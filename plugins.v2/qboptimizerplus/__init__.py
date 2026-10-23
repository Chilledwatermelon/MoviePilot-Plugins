import asyncio
import json
import math
import re
import threading
import time
from datetime import datetime, timedelta
from typing import List, Tuple, Dict, Any, Optional
from urllib.parse import urlparse

import pytz
from apscheduler.schedulers.background import BackgroundScheduler
from apscheduler.triggers.cron import CronTrigger

from app.chain.download import DownloadChain
from app.chain.media import MediaChain
from app.chain.search import SearchChain
from app.core.config import settings
from app.core.context import MediaInfo, TorrentInfo, Context
from app.core.event import eventmanager, Event
from app.core.metainfo import MetaInfo
from app.helper.downloader import DownloaderHelper
from app.db.site_oper import SiteOper
from app.log import logger
from app.plugins import _PluginBase
from app.schemas import NotificationType, ServiceInfo
from app.schemas.message import Notification
from app.schemas.types import EventType, MediaType
from app.utils.string import StringUtils

lock = threading.Lock()


class QbOptimizerPlus(_PluginBase):
    # 插件名称
    plugin_name = "QB种子优化Plus"
    # 插件描述
    plugin_desc = "基于 leG09 的QB种子优化改进：做种数复核防误删、排除过滤、精确重新下载。清理进行中无人做种任务、清理预计下载时长超过N小时且已下载N小时的慢速任务、智能综合评分优先级（下载速度+做种数+进度）、下载阈值控制（当下载中种子总大小超过阈值时优先暂停低速低进度种子，确保磁盘空间不超阈值）"
    # 插件图标
    plugin_icon = "Qbittorrent_A.png"
    # 插件版本
    plugin_version = "1.9.1"
    # 插件作者
    plugin_author = "Chilledwatermelon"
    # 作者主页
    author_url = "https://github.com/Chilledwatermelon"
    # 插件配置项ID前缀
    plugin_config_prefix = "qboptimizerplus_"
    # 加载顺序
    plugin_order = 10
    # 可使用的用户级别
    auth_level = 1

    # 私有属性
    _event = threading.Event()
    _scheduler = None
    _enabled = False
    _onlyonce = False
    _notify = False
    _downloaders = []
    _cron = None
    
    # 功能开关
    _enable_zero_seed_clean = False  # 启用进行中无人做种任务清理
    _enable_timeout_clean = False    # 启用慢速下载任务清理
    _enable_unrecognized_clean = False  # 启用识别不到媒体信息任务清理
    _enable_auto_redownload = True   # 启用自动重新下载
    
    # 配置参数
    _zero_seed_threshold = 0         # 做种数阈值

    _timeout_hours = 24              # 慢速下载时长阈值（小时）
    _max_download_slots = 5          # 最大下载槽位
    _max_zero_seed_process = 50      # 每次处理的最大无人做种种子数量
    _max_timeout_process = 50        # 每次处理的最大慢速下载种子数量
    _max_unrecognized_process = 50   # 每次处理的最大识别不到媒体信息种子数量
    _max_priority_process = 100      # 每次处理的最大优先级优化种子数量
    # 移除优先级提升倍数，改为按做种数排序
    _search_sites = []               # 重新下载时用于搜索的站点ID列表
    _seeder_metric = 'num_complete'  # 做种数度量方式：固定使用num_complete字段
    
    # 综合评分配置
    _enable_score_priority = True    # 启用综合评分优先级
    _speed_weight = 1.0             # 下载速度权重
    _seeder_weight = 0.5            # 做种数权重
    _min_score_threshold = 1.0      # 最低综合评分阈值
    
    # 磁盘空间和I/O监控配置
    _enable_disk_monitor = False     # 启用磁盘空间和I/O监控
    _disk_space_threshold = 10       # 磁盘空间不足阈值（GB）
    _io_cache_threshold = 70         # 写入缓存阈值（百分比）
    _io_queue_threshold = 8000       # 队列I/O任务阈值
    _speed_limit_mbps = 1            # 限制下载速度（MB/s）
    _monitor_duration = 30           # 持续监测时长（秒）
    _monitor_interval = 3            # 监测间隔（秒）
    
    # 下载阈值控制配置
    _enable_download_threshold = False  # 启用下载阈值控制
    _min_disk_space_threshold = 50      # 最小磁盘空间阈值（GB）

    # 过滤设置（每行一个，命中的种子不会被清理删除）
    _exclude_keywords = ""
    _exclude_categories = ""
    _exclude_labels = ""

    # 做种数据可靠性
    _seed_check_grace_minutes = 30   # 种子实际活跃满N分钟后才判定无人做种
    _probe_wait_seconds = 30         # 排队种子探测做种数的最长等待时间

    # 重新下载
    _redownload_min_seeders = 3      # 替代资源最少做种数
    _redownload_size_tolerance = 50  # 替代资源与原种子大小允许偏差（%），0为不限制
    _redownload_max_attempts = 3     # 同一资源最多自动重新下载次数

    # AI 辅助识别（可选）
    _ai_enabled = False
    _ai_model = ""
    _ai_base_url = ""
    _ai_api_key = ""
    _ai_calls_this_run = 0

    # 通知设置
    _notify_types = ['summary', 'threshold', 'limit', 'error', 'oversize']
    _notify_prefix = "QB优化Plus"
    _notify_name_length = 40
    _notify_max_items = 10
    _notify_summary_title = ""
    _notify_summary_body = ""

    # 清理已被 MP 整理移走的种子
    _enable_moved_clean = True
    _moved_clean_delay_minutes = 30

    # 错误种子处理
    _enable_error_handle = True
    _error_timeout_hours = 24        # 持续报错超过N小时删除并重新下载，0为不删除

    # qB 中表示“无限”的 ETA 值
    QB_ETA_INFINITY = 8640000
    PROBE_CACHE_TTL = 6 * 3600

    def init_plugin(self, config: dict = None):
        logger.info("【QB种子优化】开始初始化插件...")
        self._removed_hashes = set()
        self._recognized_cache = set()
        self._qb_settings_logged = set()
        self._qb_log_last_id = {}
        self._qb_error_reasons = {}
        self._events = {'replaced': [], 'kept': [], 'deleted': [], 'moved': [], 'synced': []}
        self._last_free_gb = None
        self._current_downloader = None
        logger.info(f"【QB种子优化】收到配置: {config}")
        
        if config:
            logger.info(f"【QB种子优化】收到配置: {config}")
            
            self._enabled = config.get("enabled")
            self._onlyonce = config.get("onlyonce")
            self._notify = config.get("notify")
            self._downloaders = config.get("downloaders") or []
            if not self._downloaders:
                logger.error("【QB种子优化】错误：未配置下载器，请先在插件配置中选择下载器")
                return
            self._cron = config.get("cron")
            
            # 功能开关
            self._enable_zero_seed_clean = config.get("enable_zero_seed_clean")
            self._enable_timeout_clean = config.get("enable_timeout_clean")
            self._enable_unrecognized_clean = config.get("enable_unrecognized_clean", False)
            self._enable_auto_redownload = config.get("enable_auto_redownload", True)
            self._search_sites = config.get("search_sites") or []
            self._seeder_metric = 'num_complete'  # 固定使用num_complete字段
            
            # 配置参数
            self._zero_seed_threshold = int(config.get("zero_seed_threshold") or 0)

            self._timeout_hours = int(config.get("timeout_hours") or 24)
            self._max_download_slots = int(config.get("max_download_slots") or 5)
            self._max_zero_seed_process = int(config.get("max_zero_seed_process") or 50)
            self._max_timeout_process = int(config.get("max_timeout_process") or 50)
            self._max_unrecognized_process = int(config.get("max_unrecognized_process") or 50)
            self._max_priority_process = int(config.get("max_priority_process") or 100)
            # 移除优先级提升倍数配置
            
            # 综合评分配置
            self._enable_score_priority = config.get("enable_score_priority", True)
            logger.info(f"【QB种子优化】配置加载 - enable_score_priority: {self._enable_score_priority} (原始配置值: {config.get('enable_score_priority', 'NOT_FOUND')})")
            self._speed_weight = float(config.get("speed_weight", 1.0))
            self._seeder_weight = float(config.get("seeder_weight", 0.5))
            self._min_score_threshold = float(config.get("min_score_threshold", 1.0))
            
            # 磁盘空间和I/O监控配置
            self._enable_disk_monitor = config.get("enable_disk_monitor", False)
            self._disk_space_threshold = float(config.get("disk_space_threshold", 10))
            self._io_cache_threshold = float(config.get("io_cache_threshold", 70))
            self._io_queue_threshold = int(config.get("io_queue_threshold", 8000))
            self._speed_limit_mbps = float(config.get("speed_limit_mbps", 1))
            self._monitor_duration = int(config.get("monitor_duration", 30))
            self._monitor_interval = int(config.get("monitor_interval", 3))
            
            # 下载阈值控制配置
            self._enable_download_threshold = config.get("enable_download_threshold", False)
            self._min_disk_space_threshold = float(config.get("min_disk_space_threshold", 50))

            self._exclude_keywords = config.get("exclude_keywords") or ""
            self._exclude_categories = config.get("exclude_categories") or ""
            self._exclude_labels = config.get("exclude_labels") or ""

            self._seed_check_grace_minutes = int(config.get("seed_check_grace_minutes") or 30)
            self._probe_wait_seconds = int(config.get("probe_wait_seconds") or 30)
            self._redownload_min_seeders = int(config.get("redownload_min_seeders") or 3)
            self._redownload_size_tolerance = int(config.get("redownload_size_tolerance", 50) or 0)
            self._redownload_max_attempts = int(config.get("redownload_max_attempts") or 3)

            notify_types = config.get("notify_types")
            self._notify_types = list(notify_types) if isinstance(notify_types, list) else list(self.NOTIFY_KINDS)
            self._notify_prefix = (config.get("notify_prefix") or "QB优化Plus").strip()
            self._notify_name_length = int(config.get("notify_name_length") or 40)
            self._notify_max_items = int(config.get("notify_max_items") or 10)
            self._notify_summary_title = config.get("notify_summary_title") or ""
            self._notify_summary_body = config.get("notify_summary_body") or ""

            self._enable_moved_clean = bool(config.get("enable_moved_clean", True))
            self._moved_clean_delay_minutes = int(config.get("moved_clean_delay_minutes", 30) or 0)

            self._enable_error_handle = bool(config.get("enable_error_handle", True))
            self._error_timeout_hours = int(config.get("error_timeout_hours", 24) or 0)

            self._ai_enabled = bool(config.get("ai_enabled", False))
            self._ai_model = (config.get("ai_model") or "").strip()
            self._ai_base_url = (config.get("ai_base_url") or "").strip()
            self._ai_api_key = (config.get("ai_api_key") or "").strip()

            logger.info(f"【QB种子优化】配置加载完成:")
            logger.info(f"  - 启用状态: {self._enabled}")
            logger.info(f"  - 立即运行: {self._onlyonce}")
            logger.info(f"  - 发送通知: {self._notify}")
            logger.info(f"  - 下载器: {self._downloaders}")
            logger.info(f"  - 执行周期: {self._cron}")
            logger.info(f"  - 搜索站点: {self._search_sites}")
            logger.info(f"  - 做种数度量: {self._seeder_metric}")
            logger.info(f"  - 清理做种数为0: {self._enable_zero_seed_clean}")
            logger.info(f"  - 清理超时: {self._enable_timeout_clean}")
            logger.info(f"  - 清理识别不到媒体信息: {self._enable_unrecognized_clean}")
            logger.info(f"  - 做种数阈值: {self._zero_seed_threshold}")
            logger.info(f"  - 慢速下载时长阈值: {self._timeout_hours}小时")
            logger.info(f"  - 最大无人做种处理数: {self._max_zero_seed_process}")
            logger.info(f"  - 最大慢速下载处理数: {self._max_timeout_process}")
            logger.info(f"  - 最大识别不到媒体信息处理数: {self._max_unrecognized_process}")
            logger.info(f"  - 最大优先级优化处理数: {self._max_priority_process}")
            logger.info(f"  - 优先级策略: 综合评分排序")
            logger.info(f"  - 综合评分开关: {self._enable_score_priority}")
            logger.info(f"  - 速度权重: {self._speed_weight}")
            logger.info(f"  - 做种数权重: {self._seeder_weight}")
            logger.info(f"  - 最低评分阈值: {self._min_score_threshold}")
            logger.info(f"  - 磁盘监控开关: {self._enable_disk_monitor}")
            logger.info(f"  - 磁盘空间阈值: {self._disk_space_threshold}GB")
            logger.info(f"  - I/O缓存阈值: {self._io_cache_threshold}%")
            logger.info(f"  - I/O队列阈值: {self._io_queue_threshold}")
            logger.info(f"  - 速度限制: {self._speed_limit_mbps}MB/s")
            logger.info(f"  - 监测时长: {self._monitor_duration}秒")
            logger.info(f"  - 监测间隔: {self._monitor_interval}秒")
            logger.info(f"  - 下载阈值控制开关: {self._enable_download_threshold}")
            logger.info(f"  - 最小磁盘空间阈值: {self._min_disk_space_threshold}GB")
            logger.info(f"  - 排除关键字: {self._split_lines(self._exclude_keywords)}")
            logger.info(f"  - 排除分类: {self._split_lines(self._exclude_categories)}")
            logger.info(f"  - 排除标签: {self._split_lines(self._exclude_labels)}")
        else:
            logger.warning("【QB种子优化】未收到配置，使用默认值")

        self.stop_service()

        if self.get_state() or self._onlyonce:
            logger.info(f"【QB种子优化】插件状态检查: get_state()={self.get_state()}, onlyonce={self._onlyonce}")
            
            if self._onlyonce:
                logger.info("【QB种子优化】准备立即运行一次...")
                self._scheduler = BackgroundScheduler(timezone=settings.TZ)
                logger.info(f"【QB种子优化】创建调度器，时区: {settings.TZ}")
                
                run_time = datetime.now(tz=pytz.timezone(settings.TZ)) + timedelta(seconds=3)
                logger.info(f"【QB种子优化】设置运行时间: {run_time}")
                
                self._scheduler.add_job(func=self.optimize_torrents, trigger='date',
                                        run_date=run_time)
                
                # 关闭一次性开关
                self._onlyonce = False
                logger.info("【QB种子优化】已关闭立即运行开关")
                
                # 保存设置：沿用提交的完整配置，只关闭立即运行开关，避免新增配置项被覆盖丢失
                config["onlyonce"] = False
                self.update_config(config)
                
                if self._scheduler.get_jobs():
                    logger.info("【QB种子优化】调度器任务列表:")
                    self._scheduler.print_jobs()
                    logger.info("【QB种子优化】启动调度器...")
                    self._scheduler.start()
                    logger.info("【QB种子优化】调度器启动成功")
                else:
                    logger.warning("【QB种子优化】调度器没有任务")
            else:
                logger.info("【QB种子优化】插件已启用，等待定时任务执行")

    def get_state(self) -> bool:
        state = True if self._enabled and self._cron and self._downloaders else False
        logger.debug(f"【QB种子优化】插件状态: enabled={self._enabled}, cron={self._cron}, downloaders={self._downloaders}, state={state}")
        return state

    @staticmethod
    def get_command() -> List[Dict[str, Any]]:
        """
        定义远程控制命令
        """
        return [
            {
                "cmd": "/qbp_optimize",
                "event": EventType.PluginAction,
                "desc": "执行QB种子优化Plus",
                "category": "QB优化Plus",
                "data": {"action": "qbp_optimize"},
            },
            {
                "cmd": "/qbp_status",
                "event": EventType.PluginAction,
                "desc": "查看QB优化Plus状态",
                "category": "QB优化Plus",
                "data": {"action": "qbp_status"},
            },
        ]

    def get_api(self) -> List[Dict[str, Any]]:
        pass

    def get_service(self) -> List[Dict[str, Any]]:
        """
        注册插件公共服务
        """
        if self.get_state():
            return [{
                "id": "QbOptimizerPlus",
                "name": "QB种子优化Plus服务",
                "trigger": CronTrigger.from_crontab(self._cron),
                "func": self.optimize_torrents,
                "kwargs": {}
            }]
        return []

    @property
    def service_infos(self) -> Optional[Dict[str, ServiceInfo]]:
        """
        服务信息
        """
        logger.debug(f"【QB种子优化】获取服务信息，配置的下载器: {self._downloaders}")
        
        if not self._downloaders:
            logger.warning("【QB种子优化】尚未配置下载器，请检查配置")
            return None

        logger.debug("【QB种子优化】开始获取下载器服务...")
        services = DownloaderHelper().get_services(name_filters=self._downloaders)
        logger.debug(f"【QB种子优化】获取到的服务: {list(services.keys()) if services else 'None'}")
        
        if not services:
            logger.warning("【QB种子优化】获取下载器实例失败，请检查配置")
            return None

        active_services = {}
        for service_name, service_info in services.items():
            logger.debug(f"【QB种子优化】检查下载器: {service_name}")
            
            if service_info.instance.is_inactive():
                logger.warning(f"【QB种子优化】下载器 {service_name} 未连接，请检查配置")
            elif not self.check_is_qb(service_info):
                logger.warning(f"【QB种子优化】不支持的下载器类型 {service_name}，仅支持QB，请检查配置")
            else:
                logger.info(f"【QB种子优化】下载器 {service_name} 连接正常")
                active_services[service_name] = service_info

        logger.info(f"【QB种子优化】活跃下载器数量: {len(active_services)}")
        if not active_services:
            logger.warning("【QB种子优化】没有已连接的下载器，请检查配置")
            return None

        return active_services

    @staticmethod
    def check_is_qb(service_info) -> bool:
        """
        检查下载器类型是否为 qbittorrent
        """
        is_qb = DownloaderHelper().is_downloader(service_type="qbittorrent", service=service_info)
        logger.debug(f"【QB种子优化】检查下载器类型: {service_info.name if service_info else 'None'} -> {'qbittorrent' if is_qb else '其他'}")
        return is_qb

    def __get_downloader(self, name: str):
        """
        根据名称返回下载器实例
        """
        logger.debug(f"【QB种子优化】获取下载器实例: {name}")
        service_info = self.service_infos.get(name)
        if service_info:
            logger.debug(f"【QB种子优化】找到下载器: {name}")
            return service_info.instance
        else:
            logger.error(f"【QB种子优化】未找到下载器: {name}")
            return None

    @eventmanager.register(EventType.PluginAction)
    def handle_qb_optimize(self, event: Event):
        if not self._enabled:
            return
        if event:
            event_data = event.event_data
            if not event_data or event_data.get("action") != "qbp_optimize":
                return
        self.optimize_torrents()

    @eventmanager.register(EventType.PluginAction)
    def handle_qb_status(self, event: Event):
        if not self._enabled:
            return
        if event:
            event_data = event.event_data
            if not event_data or event_data.get("action") != "qbp_status":
                return
        self.show_status()

    def _check_disk_space_before_optimize(self):
        """
        优化前检查磁盘空间
        如果磁盘空间不足：
        - 如果未限速，则限速并停止执行任务
        - 如果已限速，则跳过所有优化任务
        如果磁盘空间充足：
        - 如果已限速（可能是之前因为磁盘空间不足而限速的），则解除限速
        返回 True 表示需要跳过所有任务，False 表示可以继续执行
        """
        logger.info("【QB种子优化】优先检查磁盘空间...")
        
        try:
            # 获取第一个下载器进行磁盘空间检查
            if not self._downloaders:
                logger.warning("【QB种子优化】未配置下载器，无法检查磁盘空间")
                return False  # 无法检查时继续执行
            
            first_downloader_name = self._downloaders[0]
            downloader_obj = self.__get_downloader(first_downloader_name)
            
            if not downloader_obj:
                logger.warning(f"【QB种子优化】无法获取下载器实例，继续执行优化任务")
                return False
            
            # 获取qBittorrent客户端实例
            qb_client = downloader_obj.qbc
            if not qb_client:
                logger.warning(f"【QB种子优化】无法获取qBittorrent客户端，继续执行优化任务")
                return False
            
            # 调用qBittorrent API获取服务器状态
            try:
                response = qb_client._request(
                    http_method='POST',
                    api_namespace='sync',
                    api_method='maindata',
                    data={'rid': 0}
                )
                
                # 解析响应数据
                try:
                    response_data = response.json()
                except:
                    import json
                    response_data = json.loads(response.text)
                
                if 'server_state' not in response_data:
                    logger.warning(f"【QB种子优化】无法获取服务器状态信息，继续执行优化任务")
                    return False
                
                server_state = response_data['server_state']
                free_space_gb = server_state.get('free_space_on_disk', 0) / (1024**3)  # 转换为GB
                
                logger.info(f"【QB种子优化】磁盘空间检查结果: 剩余空间 {free_space_gb:.2f}GB, 阈值 {self._disk_space_threshold}GB")
                
                if free_space_gb < self._disk_space_threshold:
                    logger.warning(f"【QB种子优化】磁盘空间不足 ({free_space_gb:.2f}GB < {self._disk_space_threshold}GB)")
                    
                    # 检查当前是否已限速
                    try:
                        current_download_limit, current_upload_limit = downloader_obj.get_speed_limit()
                        our_limit_kbps = int(self._speed_limit_mbps * 1024)
                        is_limited = current_download_limit > 0 and current_download_limit <= our_limit_kbps
                        
                        logger.info(f"【QB种子优化】当前速度限制: {current_download_limit}KB/s, 我们的限制值: {our_limit_kbps}KB/s, 已限速: {is_limited}")
                        
                        if not is_limited:
                            # 未限速，则限速并停止执行任务
                            logger.warning(f"【QB种子优化】磁盘空间不足且未限速，开始限制下载速度: {self._speed_limit_mbps}MB/s")
                            
                            speed_limit_bytes = int(self._speed_limit_mbps * 1024 * 1024)  # 转换为字节/秒
                            success = self._set_download_speed_limit(downloader_obj, speed_limit_bytes)
                            
                            if success:
                                logger.info(f"【QB种子优化】下载速度限制成功，停止执行优化任务")
                                
                                self._send('limit', "💾 磁盘空间不足，已限速",
                                           f"剩余 {free_space_gb:.1f}G ＜ 阈值 {self._disk_space_threshold}G\n"
                                           f"下载已限速 {self._speed_limit_mbps}MB/s，本轮暂停所有清理与调度\n"
                                           f"空间恢复后会自动解除限速")
                                return True  # 已限速，停止执行任务
                            else:
                                logger.error(f"【QB种子优化】下载速度限制失败，跳过所有优化任务")
                                return True  # 限速失败，跳过任务
                        else:
                            # 已限速，跳过所有优化任务
                            logger.warning(f"【QB种子优化】磁盘空间不足且已限速，跳过所有优化任务")
                            
                            return True  # 已限速，跳过所有任务
                            
                    except Exception as e:
                        logger.error(f"【QB种子优化】检查限速状态异常: {str(e)}，跳过所有优化任务")
                        return True  # 异常时跳过任务，保守处理
                else:
                    # 磁盘空间充足，检查是否需要解除限速
                    logger.info(f"【QB种子优化】磁盘空间充足，检查是否需要解除限速...")
                    
                    try:
                        current_download_limit, current_upload_limit = downloader_obj.get_speed_limit()
                        our_limit_kbps = int(self._speed_limit_mbps * 1024)
                        is_limited = current_download_limit > 0 and current_download_limit <= our_limit_kbps
                        
                        logger.info(f"【QB种子优化】当前速度限制: {current_download_limit}KB/s, 我们的限制值: {our_limit_kbps}KB/s, 已限速: {is_limited}")
                        
                        if is_limited:
                            # 已限速，可能是之前因为磁盘空间不足而限速的，现在磁盘空间恢复了，解除限速
                            logger.info(f"【QB种子优化】磁盘空间已恢复，解除下载速度限制")
                            
                            success = self._set_download_speed_limit(downloader_obj, 0)  # 0 表示无限制
                            
                            if success:
                                logger.info(f"【QB种子优化】下载速度限制解除成功，继续执行优化任务")
                                
                                self._send('limit', "✅ 磁盘空间已恢复，已解除限速",
                                           f"剩余 {free_space_gb:.1f}G ≥ 阈值 {self._disk_space_threshold}G\n"
                                           f"下载限速 {current_download_limit}KB/s → 不限速")
                            else:
                                logger.warning(f"【QB种子优化】下载速度限制解除失败，但继续执行优化任务")
                        else:
                            logger.info(f"【QB种子优化】未检测到限速状态，继续执行优化任务")
                            
                    except Exception as e:
                        logger.warning(f"【QB种子优化】检查限速状态异常: {str(e)}，继续执行优化任务")
                    
                    return False  # 磁盘空间充足，可以继续
                    
            except Exception as e:
                logger.warning(f"【QB种子优化】获取磁盘空间信息异常: {str(e)}，继续执行优化任务")
                return False
                
        except Exception as e:
            logger.warning(f"【QB种子优化】磁盘空间检查异常: {str(e)}，继续执行优化任务")
            import traceback
            logger.debug(f"【QB种子优化】磁盘空间检查异常详情: {traceback.format_exc()}")
            return False  # 异常时继续执行，避免阻塞

    def optimize_torrents(self):
        """
        执行种子优化
        """
        logger.info("【QB种子优化】开始执行种子优化任务...")
        logger.info(f"【QB种子优化】配置的下载器: {self._downloaders}")
        
        if not self._downloaders:
            logger.error("【QB种子优化】错误：未配置下载器，无法执行优化任务")
            return
        
        # 优先检查磁盘空间，如果不足则直接跳过所有任务
        if self._check_disk_space_before_optimize():
            return  # 磁盘空间不足，跳过所有优化任务
        
        total_zero_seed_removed = 0
        total_priority_boosted = 0
        self._current_downloader = None
        self._ai_calls_this_run = 0
        self._events = {'replaced': [], 'kept': [], 'deleted': [], 'moved': [], 'synced': []}
        self._last_free_gb = None
        total_timeout_removed = 0
        total_unrecognized_removed = 0
        total_error_removed = 0
        total_moved_removed = 0
        all_failed_torrents = []  # 收集所有重新下载失败的种子
        
        for downloader_name in self._downloaders:
            logger.info(f"【QB种子优化】开始处理下载器: {downloader_name}")
            
            try:
                with lock:
                    logger.debug(f"【QB种子优化】获取下载器实例: {downloader_name}")
                    downloader_obj = self.__get_downloader(downloader_name)
                    if not downloader_obj:
                        logger.error(f"【QB种子优化】获取下载器失败: {downloader_name}")
                        continue

                    self._current_downloader = downloader_name
                    self._log_qb_add_settings(downloader_obj, downloader_name)
                    logger.info(f"【QB种子优化】开始获取种子列表: {downloader_name}")
                    # 获取所有种子
                    all_torrents, error = downloader_obj.get_torrents()
                    if error:
                        logger.error(f"【QB种子优化】获取下载器:{downloader_name}种子失败: {error}")
                        continue

                    if not all_torrents:
                        logger.info(f"【QB种子优化】下载器:{downloader_name}没有种子")
                        continue

                    logger.info(f"【QB种子优化】下载器:{downloader_name}种子总数: {len(all_torrents)}")
                    
                    # 统计种子状态
                    downloading_count = len([t for t in all_torrents if t.state_enum.is_downloading])
                    uploading_count = len([t for t in all_torrents if t.state_enum.is_uploading])
                    logger.info(f"【QB种子优化】下载中: {downloading_count}, 做种中: {uploading_count}")
                    
                    # 添加状态分布统计
                    state_distribution = {}
                    for torrent in all_torrents:
                        state = getattr(torrent, 'state', 'unknown')
                        state_distribution[state] = state_distribution.get(state, 0) + 1
                    
                    logger.info(f"【QB种子优化】状态分布: {state_distribution}")
                    
                    # 显示前几个下载中种子的详细信息
                    downloading_torrents = [t for t in all_torrents if t.state_enum.is_downloading]
                    logger.info(f"【QB种子优化】前5个下载中种子详情:")
                    for i, torrent in enumerate(downloading_torrents[:5], 1):
                        seeder_count = self._get_seeder_count(torrent)
                        logger.info(f"  {i}. {torrent.name}")
                        logger.info(f"     - 状态: {getattr(torrent, 'state', 'unknown')}")
                        logger.info(f"     - 做种数: {seeder_count}")
                        logger.info(f"     - 原始字段: num_complete={getattr(torrent, 'num_complete', 'N/A')}, num_seeds={getattr(torrent, 'num_seeds', 'N/A')}")
                    
                    # 执行各项优化
                    logger.info(f"【QB种子优化】开始执行优化操作...")
                    # 每一步都基于剔除了前面步骤已删除种子的列表，避免重复处理和空间计算错误
                    self._removed_hashes = set()
                    if self._enable_moved_clean:
                        self._sync_moved_files(downloader_obj, all_torrents)
                    self._dedupe_torrents(downloader_obj, self._alive(all_torrents))
                    zero_seed_removed, zero_seed_failed = self._clean_zero_seed_torrents(
                        downloader_obj, self._alive(all_torrents), downloader_name)
                    timeout_removed, timeout_failed = self._clean_timeout_torrents(
                        downloader_obj, self._alive(all_torrents), downloader_name)
                    unrecognized_removed = self._clean_unrecognized_torrents(
                        downloader_obj, self._alive(all_torrents), downloader_name)
                    moved_removed = self._clean_moved_torrents(
                        downloader_obj, self._alive(all_torrents), downloader_name)
                    error_removed, error_failed = self._handle_error_torrents(
                        downloader_obj, self._alive(all_torrents), downloader_name)
                    priority_boosted = self._boost_priority_torrents(
                        downloader_obj, self._alive(all_torrents), downloader_name)

                    self._last_free_gb = self._get_free_space_gb(downloader_obj)

                    # 执行磁盘空间和I/O监控
                    disk_monitor_result = self._monitor_disk_and_io(downloader_obj, downloader_name)

                    # 执行下载阈值控制（优先级调整后状态已变化，重新获取种子列表）
                    fresh_torrents, fresh_error = downloader_obj.get_torrents()
                    threshold_torrents = fresh_torrents if not fresh_error and fresh_torrents else self._alive(all_torrents)
                    download_threshold_result = self._manage_download_threshold(downloader_obj, threshold_torrents, downloader_name)
                    
                    total_zero_seed_removed += zero_seed_removed
                    total_priority_boosted += priority_boosted
                    total_timeout_removed += timeout_removed
                    total_unrecognized_removed += unrecognized_removed
                    total_error_removed += error_removed
                    total_moved_removed += moved_removed
                    
                    # 收集重新下载失败信息
                    all_failed_torrents.extend(zero_seed_failed)
                    all_failed_torrents.extend(timeout_failed)
                    all_failed_torrents.extend(error_failed)
                    
                    logger.info(f"【QB种子优化】{downloader_name} 优化完成:")
                    logger.info(f"  - 清理下载中无人做种: {zero_seed_removed}个")
                    logger.info(f"  - 综合评分优化: {priority_boosted}个")
                    logger.info(f"  - 清理慢速下载: {timeout_removed}个")
                    logger.info(f"  - 清理识别不到媒体信息: {unrecognized_removed}个")

            except Exception as e:
                logger.error(f"【QB种子优化】处理下载器 {downloader_name} 时发生异常：{str(e)}")
                import traceback
                logger.error(f"【QB种子优化】异常详情: {traceback.format_exc()}")
        
        # 输出总结信息到日志
        logger.info(f"【QB种子优化】所有下载器处理完成，总计:")
        logger.info(f"  - 清理下载中无人做种: {total_zero_seed_removed}个")
        logger.info(f"  - 综合评分优化: {total_priority_boosted}个")
        logger.info(f"  - 清理慢速下载: {total_timeout_removed}个")
        logger.info(f"  - 清理识别不到媒体信息: {total_unrecognized_removed}个")
        logger.info(f"  - 清理长期报错种子: {total_error_removed}个")
        logger.info(f"  - 清理已整理移走的种子: {total_moved_removed}个")
        logger.info(f"  - 重新下载失败: {len(all_failed_torrents)}个")
        
        self._send_run_summary()

    # ---------------- 通知 ----------------
    NOTIFY_KINDS = {
        'summary': '清理汇总（替换/保留/删除）',
        'threshold': '阈值控制暂停/恢复',
        'limit': '磁盘/IO限速与恢复',
        'error': '报错种子提醒',
        'oversize': '超出可用空间的种子',
    }
    DEFAULT_SUMMARY_TITLE = "🧹 {前缀}｜{摘要}"
    DEFAULT_SUMMARY_BODY = "🖥 下载器：{下载器}　💾 剩余：{剩余空间}\n⏰ {时间}\n{替换列表}{保留列表}{删除列表}{同步列表}{整理列表}"

    class _SafeDict(dict):
        def __missing__(self, key):
            return '{' + key + '}'

    def _short(self, name) -> str:
        name = str(name or '')
        limit = max(self._notify_name_length, 10)
        return name if len(name) <= limit else name[:limit - 1] + '…'

    def _name(self, name) -> str:
        """通知中的种子名：等宽显示，避免 TG Markdown 把 _ * [] 当成格式，点击可复制"""
        return f"`{self._short(name).replace('`', '')}`"

    @staticmethod
    def _brief(info: dict) -> str:
        """种子关键信息：大小 · 进度 · 分类/标签"""
        parts = [StringUtils.str_filesize(info.get('size') or 0)]
        if info.get('progress') is not None:
            parts.append(f"进度 {info['progress'] * 100:.0f}%")
        if info.get('category'):
            parts.append(f"分类 {info['category']}")
        return ' · '.join(parts)

    def _section(self, header: str, lines: list) -> str:
        if not lines:
            return ''
        shown = lines[:max(self._notify_max_items, 1)]
        text = f"\n{header}（{len(lines)}）\n" + "\n".join(shown)
        if len(lines) > len(shown):
            text += f"\n…另有 {len(lines) - len(shown)} 个，详见插件日志"
        return text + "\n"

    def _render(self, template: str, default: str, values: dict) -> str:
        for tpl in (template, default):
            if not tpl:
                continue
            try:
                return tpl.format_map(self._SafeDict(values)).strip()
            except Exception as e:
                logger.warning(f"【通知】模板格式有误，改用默认模板: {e}")
        return ''

    def _send(self, kind: str, title: str, text: str):
        if not self._notify or kind not in self._notify_types:
            return
        try:
            self.post_message(mtype=NotificationType.Manual, title=title, text=(text or '').strip())
        except Exception as e:
            logger.warning(f"【通知】发送失败: {e}")

    def _send_run_summary(self):
        events = self._events
        if not any(events.values()):
            logger.info("【QB种子优化】本次没有替换/保留/删除，无需发送汇总通知")
            return
        values = {
            '前缀': self._notify_prefix,
            '替换数': len(events['replaced']),
            '保留数': len(events['kept']),
            '删除数': len(events['deleted']),
            '替换列表': self._section("♻️ 已替换为新资源", events['replaced']),
            '保留列表': self._section("⚠️ 未找到替代资源，已保留原种子", events['kept']),
            '删除列表': self._section("🗑️ 已删除", events['deleted']),
            '整理数': len(events['moved']),
            '同步数': len(events['synced']),
            '同步列表': self._section("🔀 季包部分集数已整理，跳过这些文件继续下载", events['synced']),
            '摘要': ' · '.join(f"{label} {len(events[key])}" for label, key in
                               [('替换', 'replaced'), ('保留', 'kept'), ('删除', 'deleted'), ('跳过已整理文件', 'synced'), ('已整理', 'moved')] if events[key]),
            '整理列表': self._section("📤 文件已被MP整理移走，清理种子记录", events['moved']),
            '下载器': ', '.join(self._downloaders),
            '剩余空间': f"{self._last_free_gb:.1f}G" if self._last_free_gb is not None else '未知',
            '时间': datetime.now().strftime('%m-%d %H:%M'),
        }
        title = self._render(self._notify_summary_title, self.DEFAULT_SUMMARY_TITLE, values)
        body = self._render(self._notify_summary_body, self.DEFAULT_SUMMARY_BODY, values)
        self._send('summary', title, body)

    def _clean_zero_seed_torrents(self, downloader_obj, torrents, downloader_name):
        """
        清理下载中无人做种的任务并重新下载。
        qB 的 num_complete 在 tracker 尚未返回 scrape 数据时会退回为“已知 peer 列表中的做种数”，
        刚加入、刚恢复或刚出队的种子通常显示为 0，因此要经过多重校验才判定为无人做种。
        """
        prefix = "【功能1-无人做种】"
        if not self._enable_zero_seed_clean:
            logger.info(f"{prefix}功能已禁用，跳过")
            return 0, []

        logger.info(f"{prefix}检查条件: 做种数≤{self._zero_seed_threshold}, 状态=downloading/stalledDL, "
                    f"实际活跃≥{self._seed_check_grace_minutes}分钟, 并以tracker返回数据复核")

        candidates = []
        for torrent in torrents:
            state_lower = (getattr(torrent, 'state', '') or '').lower()
            if state_lower not in ('downloading', 'stalleddl'):
                continue
            if self._get_seeder_count(torrent) > self._zero_seed_threshold:
                continue
            candidates.append(torrent)
        candidates = self._filter_excluded(candidates, prefix)

        zero_seed_torrents = []
        dead_detail = {}
        reannounce_hashes = []
        for torrent in candidates:
            verdict, detail = self._verify_no_seeders(downloader_obj, torrent)
            if verdict == 'dead':
                logger.info(f"{prefix}确认无人做种（{detail}）: {torrent.name}")
                zero_seed_torrents.append(torrent)
                dead_detail[torrent.hash] = detail
            else:
                logger.info(f"{prefix}暂不清理（{detail}）: {torrent.name}")
                if verdict == 'unknown':
                    reannounce_hashes.append(torrent.hash)
        if reannounce_hashes:
            self._reannounce(downloader_obj, reannounce_hashes)
            logger.info(f"{prefix}已让{len(reannounce_hashes)}个做种数据未就绪的种子重新汇报tracker，下次运行再判断")

        logger.info(f"{prefix}检查完成: 候选{len(candidates)}个, 确认无人做种{len(zero_seed_torrents)}个")
        if len(zero_seed_torrents) > self._max_zero_seed_process:
            logger.info(f"{prefix}超过每次处理上限{self._max_zero_seed_process}，只处理前{self._max_zero_seed_process}个")
            zero_seed_torrents = zero_seed_torrents[:self._max_zero_seed_process]

        removed = 0
        redownload_failed_torrents = []
        for i, torrent in enumerate(zero_seed_torrents, 1):
            logger.info(f"{prefix}删除审计 ({i}/{len(zero_seed_torrents)}): {torrent.name} | HASH={torrent.hash} | "
                        f"进度={getattr(torrent, 'progress', 0) * 100:.1f}% | 大小={StringUtils.str_filesize(getattr(torrent, 'size', 0))} | "
                        f"分类={getattr(torrent, 'category', '')} | 标签={getattr(torrent, 'tags', '')}")
            ok, failed = self._replace_torrent(
                downloader_obj, torrent, torrents, f"无人做种（{dead_detail.get(torrent.hash, '')}）", prefix)
            removed += int(ok)
            if failed:
                redownload_failed_torrents.append(failed)
        return removed, redownload_failed_torrents

    def _boost_priority_torrents(self, downloader_obj, torrents, downloader_name):
        """
        提升做种数多的种子下载优先级
        """
        logger.info(f"【功能3-综合评分】开始综合评分优先级优化，功能开关: {self._enable_score_priority}")
        
        if not self._enable_score_priority:
            logger.info("【功能3-综合评分】综合评分优先级优化功能已禁用，跳过")
            return 0
            
        logger.info(f"【功能3-综合评分】检查条件: 最低综合评分阈值={self._min_score_threshold}")

        high_seed_torrents = []
        checked_count = 0

        # 统计信息用于调试
        state_counter = {}
        downloading_like_counter = 0
        completed_counter = 0
        queued_counter = 0
        seeds_ge_1 = 0
        seeds_ge_5 = 0
        seeds_ge_10 = 0

        # 分类种子
        downloading_torrents = []  # 正在下载的种子
        queued_torrents = []       # 排队中的种子

        for torrent in torrents:
            checked_count += 1
            state_name = getattr(torrent, 'state', '') or ''
            state_counter[state_name] = state_counter.get(state_name, 0) + 1

            # 检查是否为已完成状态
            is_completed = False
            try:
                progress = getattr(torrent, 'progress', 0)
                is_completed = progress >= 1.0  # 进度100%视为已完成
            except Exception:
                is_completed = False
            
            if is_completed:
                completed_counter += 1
                continue  # 跳过已完成的种子

            # 分类种子状态
            state_lower = (state_name or '').lower()
            is_downloading = 'downloading' in state_lower or 'metadl' in state_lower
            is_queued = 'queueddl' in state_lower or state_lower == 'queued'
            
            # 调试日志：查看前几个种子的状态分类
            if checked_count <= 10:
                logger.debug(f"【QB种子优化】状态分类调试: {torrent.name} - 原始状态: '{state_name}' - 小写: '{state_lower}' - 下载中: {is_downloading} - 排队中: {is_queued}")
            
            if is_downloading:
                downloading_like_counter += 1
                downloading_torrents.append(torrent)
            elif is_queued:
                queued_counter += 1
                queued_torrents.append(torrent)
                
        # 只保留真正排队中的种子（排除等待和进行中的）
        true_queued_torrents = []
        for torrent in queued_torrents:
            state_name = getattr(torrent, 'state', '') or ''
            state_lower = state_name.lower()
            
            # 只处理真正排队中的种子，排除其他状态
            if 'queueddl' in state_lower or state_lower == 'queued':
                true_queued_torrents.append(torrent)
            else:
                logger.debug(f"【QB种子优化】跳过非排队状态种子: {torrent.name} (状态: {state_name})")
        
        queued_torrents = true_queued_torrents
        logger.info(f"【QB种子优化】真正排队中的种子数量: {len(queued_torrents)}个")
        # 按队列顺序排序，确保优先处理排在最前的任务（例如 101、102...）
        try:
            queued_torrents.sort(key=lambda t: self._get_queue_position(t))
            logger.info(f"【QB种子优化】按队列位置排序完成，展示前20个队列位置:")
            for idx, t in enumerate(queued_torrents[:20], 1):
                queue_pos = self._get_queue_position(t)
                logger.info(f"  {idx:2d}. 队列位置: {queue_pos:3d} | {getattr(t, 'name', '')}")
        except Exception as e:
            logger.warning(f"【QB种子优化】按队列顺序排序失败，将按默认顺序处理: {str(e)}")

        # 处理正在下载的种子
        logger.info(f"【QB种子优化】处理正在下载的种子: {len(downloading_torrents)}个")
        for torrent in downloading_torrents:
            seeder_count = self._get_seeder_count(torrent)
            dlspeed = getattr(torrent, 'dlspeed', 0)
            progress = getattr(torrent, 'progress', 0) * 100
            
            # 计算综合评分：使用配置的权重
            speed_score = (dlspeed / (1024 * 1024)) * self._speed_weight  # 转换为MB/s并应用权重
            seeder_score = seeder_count * self._seeder_weight  # 做种数权重
            
            total_score = speed_score + seeder_score
            
            logger.debug(f"【QB种子优化】种子评分: {torrent.name}")
            logger.debug(f"  - 做种数: {seeder_count}, 下载速度: {StringUtils.str_filesize(dlspeed)}/s, 进度: {progress:.1f}%")
            logger.debug(f"  - 速度评分: {speed_score:.2f}, 做种评分: {seeder_score:.2f}")
            logger.debug(f"  - 综合评分: {total_score:.2f}")
            
            # 使用综合评分判断是否加入优化
            if total_score >= self._min_score_threshold:
                logger.debug(f"【QB种子优化】下载中种子符合条件: {torrent.name} (综合评分: {total_score:.2f})")
                high_seed_torrents.append({
                    'torrent': torrent,
                    'score': total_score,
                    'seeder_count': seeder_count,
                    'dlspeed': dlspeed,
                    'progress': progress
                })
            
            # 统计做种数分布
            if seeder_count >= 1:
                seeds_ge_1 += 1
            if seeder_count >= 5:
                seeds_ge_5 += 1
            if seeder_count >= 10:
                seeds_ge_10 += 1

        # 处理排队中的种子（分批启动获取做种数）
        if queued_torrents:
            logger.info(f"【QB种子优化】发现排队中的种子: {len(queued_torrents)}个")
            
            # 只处理队列最前面的任务，避免重复处理不合格的任务
            # 限制处理数量，避免负载过高
            max_process_count = min(self._max_priority_process, len(queued_torrents))
            queued_torrents = queued_torrents[:max_process_count]
            
            logger.info(f"【QB种子优化】准备处理队列最前面的{len(queued_torrents)}个种子:")
            for idx, torrent in enumerate(queued_torrents, 1):
                queue_pos = self._get_queue_position(torrent)
                logger.info(f"  处理第{idx}个: 队列位置 {queue_pos} | {torrent.name}")
            self._process_queued_torrents(downloader_obj, queued_torrents, high_seed_torrents)

        # 输出统计日志帮助定位为何为0
        logger.info(f"【QB种子优化】已完成种子数量: {completed_counter}")
        logger.info(f"【QB种子优化】正在下载的种子数量: {downloading_like_counter}")
        logger.info(f"【QB种子优化】排队中的种子数量: {queued_counter}")
        logger.info(f"【QB种子优化】做种数分布统计(仅下载中): ≥1:{seeds_ge_1} ≥5:{seeds_ge_5} ≥10:{seeds_ge_10}")
        top_states = sorted(state_counter.items(), key=lambda x: x[1], reverse=True)[:8]
        logger.info(f"【QB种子优化】状态分布Top: {top_states}")
        logger.info(f"【QB种子优化】处理策略: 直接处理下载中种子，分批启动排队种子获取做种数")
        
        logger.info(f"【QB种子优化】检查完成，发现{len(high_seed_torrents)}个高做种数的种子")
        
        if high_seed_torrents:
            # 先按评分排序再截取，保证处理的是评分最高的一批
            high_seed_torrents.sort(key=lambda x: x['score'], reverse=True)
            if len(high_seed_torrents) > self._max_priority_process:
                logger.info(f"【功能3-综合评分】种子数量({len(high_seed_torrents)})超过配置限制({self._max_priority_process})，只处理评分最高的{self._max_priority_process}个")
                high_seed_torrents = high_seed_torrents[:self._max_priority_process]

            logger.info(f"【功能3-综合评分】按综合评分排序后的种子列表:")
            for i, torrent_info in enumerate(high_seed_torrents, 1):
                logger.info(f"  {i}. 评分{torrent_info['score']:.2f} | 做种{torrent_info['seeder_count']} | "
                            f"{StringUtils.str_filesize(torrent_info['dlspeed'])}/s | 进度{torrent_info['progress']:.1f}% | {torrent_info['torrent'].name}")

            # qB 的 API 调用是同步的：从最后一名到第一名依次置顶，第1名最终排在最前，无需先移到底部或等待
            total_count = len(high_seed_torrents)
            success_count = 0
            for torrent_info in reversed(high_seed_torrents):
                if self._set_qb_torrent_priority(downloader_obj, torrent_info['torrent'].hash, 1):
                    success_count += 1
            logger.info(f"【功能3-综合评分】优先级设置完成: 成功置顶{success_count}/{total_count}个")
        else:
            # 无匹配时输出采样日志
            sample = torrents[:10]
            logger.info("【QB种子优化】未匹配到高做种种子，采样前10条做种信息：")
            for t in sample:
                logger.info(f"  - {getattr(t, 'name', '')} | state={getattr(t, 'state','')} | seeds={self._get_seeder_count(t)} | raw=[num_seeds={getattr(t,'num_seeds',None)}, seeds={getattr(t,'seeds',None)}, seeders={getattr(t,'seeders',None)}, connected_seeds={getattr(t,'connected_seeds',None)}, num_complete={getattr(t,'num_complete',None)}]")

        # 命中过滤设置的种子（如keep标签）最后置顶，保证排在队列最前
        keep_torrents = [t for t in torrents
                         if getattr(t, 'progress', 0) < 1 and not self._is_paused_state(t) and self._get_exclude_reason(t)]
        for torrent in keep_torrents:
            self._set_qb_torrent_priority(downloader_obj, torrent.hash, 1)
        if keep_torrents:
            logger.info(f"【功能3-综合评分】{len(keep_torrents)}个保持下载的种子已置顶")

        return len(high_seed_torrents)

    def _process_queued_torrents(self, downloader_obj, queued_torrents, high_seed_torrents):
        """
        排队中的种子不会向 tracker 汇报，qB 显示的做种数通常是 0。
        这里临时强制启动一小批种子并主动重新汇报，轮询到 tracker 返回数据后再取消强制启动，
        不合格的移到队尾。探测结果缓存一段时间，避免每次运行重复探测。
        """
        if not queued_torrents:
            return
        prefix = "【功能3-排队探测】"
        cache = self._load_probe_cache()
        now = int(time.time())

        to_probe = []
        for torrent in queued_torrents:
            cached = cache.get(torrent.hash)
            if cached and now - cached.get('ts', 0) < self.PROBE_CACHE_TTL:
                self._apply_queued_score(downloader_obj, torrent, cached.get('seeders', 0), 0,
                                         high_seed_torrents, prefix, from_cache=True)
            else:
                to_probe.append(torrent)

        batch_size = 10
        for start in range(0, len(to_probe), batch_size):
            batch = to_probe[start:start + batch_size]
            hashes = [t.hash for t in batch]
            logger.info(f"{prefix}探测第{start // batch_size + 1}批，共{len(batch)}个种子，最长等待{self._probe_wait_seconds}秒")
            forced = self._set_force_start(downloader_obj, hashes, True)
            speed_map = {}
            results = {}
            try:
                self._reannounce(downloader_obj, hashes)
                results = self._poll_tracker_seeders(downloader_obj, hashes)
                refreshed, error = downloader_obj.get_torrents(ids=hashes)
                if not error:
                    speed_map = {t.hash: getattr(t, 'dlspeed', 0) for t in (refreshed or [])}
            finally:
                if forced:
                    self._set_force_start(downloader_obj, hashes, False)

            for torrent in batch:
                seeders = results.get(torrent.hash)
                if seeders is None:
                    logger.info(f"{prefix}tracker未返回有效数据，保持原队列位置: {torrent.name}")
                    continue
                cache[torrent.hash] = {'seeders': seeders, 'ts': now}
                self._apply_queued_score(downloader_obj, torrent, seeders, speed_map.get(torrent.hash, 0),
                                         high_seed_torrents, prefix)

        self._save_probe_cache(cache, now)

    def _apply_queued_score(self, downloader_obj, torrent, seeders, dlspeed, high_seed_torrents, prefix, from_cache=False):
        score = (dlspeed / (1024 * 1024)) * self._speed_weight + seeders * self._seeder_weight
        source = "缓存" if from_cache else "探测"
        if score >= self._min_score_threshold:
            logger.info(f"{prefix}[{source}] 做种{seeders}，评分{score:.2f}，加入优先级排序: {torrent.name}")
            high_seed_torrents.append({
                'torrent': torrent,
                'score': score,
                'seeder_count': seeders,
                'dlspeed': dlspeed,
                'progress': getattr(torrent, 'progress', 0) * 100
            })
        elif self._get_exclude_reason(torrent):
            logger.info(f"{prefix}[{source}] 做种{seeders}，评分{score:.2f}偏低，但命中过滤设置，保持队列位置: {torrent.name}")
        else:
            logger.info(f"{prefix}[{source}] 做种{seeders}，评分{score:.2f}低于{self._min_score_threshold}，移到队尾: {torrent.name}")
            self._set_qb_torrent_priority(downloader_obj, torrent.hash, 999)

    def _poll_tracker_seeders(self, downloader_obj, hashes: List[str]) -> Dict[str, Optional[int]]:
        """轮询直到 tracker 返回做种数或超时。tracker 正常但不提供统计时，退回使用刷新后的 num_complete"""
        results: Dict[str, Optional[int]] = {h: None for h in hashes}
        working_without_stats = set()
        pending = set(hashes)
        deadline = time.time() + max(self._probe_wait_seconds, 5)
        while pending and time.time() < deadline:
            time.sleep(3)
            for torrent_hash in list(pending):
                status = self._get_tracker_seed_status(downloader_obj, torrent_hash)
                if not status:
                    continue
                if status['max_seeders'] is not None:
                    results[torrent_hash] = status['max_seeders']
                    pending.discard(torrent_hash)
                elif status['working']:
                    working_without_stats.add(torrent_hash)
                    pending.discard(torrent_hash)
        if working_without_stats:
            refreshed, error = downloader_obj.get_torrents(ids=list(working_without_stats))
            if not error:
                for torrent in refreshed or []:
                    results[torrent.hash] = self._get_seeder_count(torrent)
        return results

    def _load_probe_cache(self) -> dict:
        try:
            return dict(self.get_data('queued_probe_cache') or {})
        except Exception:
            return {}

    def _save_probe_cache(self, cache: dict, now: int):
        cache = {h: v for h, v in cache.items() if now - v.get('ts', 0) < self.PROBE_CACHE_TTL}
        try:
            self.save_data('queued_probe_cache', cache)
        except Exception as e:
            logger.debug(f"【QB种子优化】保存探测缓存失败: {e}")

    TRACKER_STATUS = {0: '禁用', 1: '未联系', 2: '工作中', 3: '更新中', 4: '出错'}

    @staticmethod
    def _tracker_field(tracker, key):
        if hasattr(tracker, 'get'):
            return tracker.get(key)
        return getattr(tracker, key, None)

    @staticmethod
    def _to_int(value, default: int) -> int:
        try:
            return int(value)
        except (TypeError, ValueError):
            return default

    def _get_tracker_seed_status(self, downloader_obj, torrent_hash: str) -> Optional[dict]:
        """
        读取种子各 tracker 的状态和做种数（tracker 返回的整个种群数据，比列表里的 num_complete 可靠）。
        返回 max_seeders（无统计为None）、working（有tracker正常工作）和便于日志的摘要。
        """
        try:
            trackers = downloader_obj.qbc.torrents_trackers(torrent_hash=torrent_hash)
        except Exception as e:
            logger.debug(f"【QB种子优化】获取tracker信息失败 {torrent_hash}: {e}")
            return None
        max_seeders = None
        working = False
        summary = []
        for tracker in trackers or []:
            url = str(self._tracker_field(tracker, 'url') or '')
            if url.startswith('** ['):
                continue
            status = self._to_int(self._tracker_field(tracker, 'status'), -1)
            seeds = self._to_int(self._tracker_field(tracker, 'num_seeds'), -1)
            if status in (2, 3):
                working = True
                if seeds >= 0:
                    max_seeders = seeds if max_seeders is None else max(max_seeders, seeds)
            msg = self._tracker_field(tracker, 'msg') or ''
            host = urlparse(url).netloc or url
            summary.append(f"{host}:{self.TRACKER_STATUS.get(status, status)}{'/' + msg if msg else ''}")
        return {
            'max_seeders': max_seeders,
            'working': working,
            'summary': ', '.join(summary) or '无tracker'
        }

    def _verify_no_seeders(self, downloader_obj, torrent) -> Tuple[str, str]:
        """
        复核候选种子是否真的无人做种。
        返回 (结论, 说明)，结论为 dead / alive / young / unknown。
        """
        active_seconds = self._first_int_attr(torrent, ['time_active'])
        if active_seconds < self._seed_check_grace_minutes * 60:
            return 'young', f"实际活跃{active_seconds // 60}分钟，未满{self._seed_check_grace_minutes}分钟"
        if getattr(torrent, 'dlspeed', 0) > 0:
            return 'alive', f"正在以{StringUtils.str_filesize(torrent.dlspeed)}/s下载"
        connected_seeds = self._first_int_attr(torrent, ['num_seeds'])
        if connected_seeds > 0:
            return 'alive', f"已连接{connected_seeds}个做种者"
        availability = getattr(torrent, 'availability', -1)
        if isinstance(availability, (int, float)) and availability >= 1:
            return 'alive', f"可用分布{availability:.2f}≥1，已连接用户拥有完整数据"

        status = self._get_tracker_seed_status(downloader_obj, torrent.hash)
        if status is None:
            return 'unknown', "获取tracker信息失败"
        if status['max_seeders'] is not None:
            if status['max_seeders'] > self._zero_seed_threshold:
                return 'alive', f"tracker报告做种数{status['max_seeders']}"
            return 'dead', f"tracker报告做种数{status['max_seeders']}，已活跃{active_seconds // 60}分钟"
        if status['working']:
            return 'dead', f"tracker正常但未提供做种统计，活跃{active_seconds // 60}分钟内未连接到做种者"
        return 'unknown', f"tracker尚未成功返回数据（{status['summary']}）"

    def _reannounce(self, downloader_obj, hashes: List[str]):
        try:
            downloader_obj.qbc.torrents_reannounce(torrent_hashes=hashes)
        except Exception as e:
            logger.debug(f"【QB种子优化】重新汇报tracker失败: {e}")

    def _set_force_start(self, downloader_obj, hashes: List[str], enable: bool) -> bool:
        try:
            downloader_obj.qbc.torrents_set_force_start(enable=enable, torrent_hashes=hashes)
            return True
        except Exception as e:
            logger.warning(f"【QB种子优化】设置强制启动={enable}失败: {e}")
            return False

    def _alive(self, torrents: list) -> list:
        return [t for t in torrents if t.hash not in self._removed_hashes]

    @staticmethod
    def _snapshot_torrent(torrent) -> dict:
        return {
            'name': torrent.name,
            'size': getattr(torrent, 'size', 0),
            'progress': getattr(torrent, 'progress', None),
            'hash': torrent.hash,
            'tracker': getattr(torrent, 'tracker', ''),
            'category': getattr(torrent, 'category', ''),
            'tags': getattr(torrent, 'tags', ''),
            'save_path': getattr(torrent, 'save_path', '') or '',
        }

    def _delete_torrent(self, downloader_obj, torrent, all_torrents, prefix) -> bool:
        """删除种子；若有其它种子共用同一份数据（辅种），只删种子保留文件"""
        torrent_hash = torrent.hash
        delete_files = True
        content_path = getattr(torrent, 'content_path', '') or ''
        if content_path:
            shared = [t for t in all_torrents
                      if t.hash != torrent_hash and (getattr(t, 'content_path', '') or '') == content_path]
            if shared:
                delete_files = False
                logger.warning(f"{prefix}有{len(shared)}个其它种子共用这份数据（辅种），只删除种子、保留文件: {torrent.name}")
        try:
            downloader_obj.qbc.torrents_delete(delete_files=delete_files, torrent_hashes=torrent_hash)
            ok = True
        except Exception as e:
            logger.warning(f"{prefix}API删除失败，改用封装方法: {torrent.name}, 错误: {e}")
            try:
                ok = bool(downloader_obj.delete_torrents(delete_file=delete_files, ids=[torrent_hash]))
            except Exception as e2:
                logger.error(f"{prefix}删除异常: {torrent.name}, 错误: {e2}")
                ok = False
        if ok:
            self._removed_hashes.add(torrent_hash)
            logger.info(f"{prefix}已删除{'种子与数据文件' if delete_files else '种子（保留文件）'}: {torrent.name}")
        else:
            logger.error(f"{prefix}删除失败: {torrent.name}")
        return ok

    # 未找到替代资源时，同一种子间隔多久再搜索
    REPLACEMENT_RETRY_SECONDS = 6 * 3600

    def _replace_torrent(self, downloader_obj, torrent, all_torrents, reason: str, prefix: str) -> Tuple[bool, Optional[dict]]:
        """
        替换一个需要清理的种子：先搜索并提交替代资源，成功后才删除原种子；
        找不到替代资源时保留原种子（进了qB的内容不丢），首次失败时返回通知记录，6小时后再搜。
        未开启自动重新下载时直接删除。返回 (是否删除了原种子, 失败记录或None)。
        """
        if not self._enable_auto_redownload or not self._search_sites:
            why = "自动重新下载已禁用" if not self._enable_auto_redownload else "未配置搜索站点"
            logger.info(f"{prefix}{why}，直接删除: {torrent.name}")
            deleted = self._delete_torrent(downloader_obj, torrent, all_torrents, prefix)
            if deleted:
                self._events['deleted'].append(
                    f"• {self._name(torrent.name)}\n  {self._brief(self._snapshot_torrent(torrent))}\n  原因：{reason}（{why}）")
            return deleted, None

        now = int(time.time())
        current = {t.hash for t in all_torrents}
        try:
            misses = {h: v for h, v in dict(self.get_data('replacement_miss') or {}).items() if h in current}
        except Exception:
            misses = {}
        miss = misses.get(torrent.hash)
        if miss and now - miss.get('ts', 0) < self.REPLACEMENT_RETRY_SECONDS:
            wait_hours = (self.REPLACEMENT_RETRY_SECONDS - (now - miss['ts'])) / 3600
            logger.info(f"{prefix}之前未找到替代资源，{wait_hours:.1f}小时后再搜，保留原种子: {torrent.name}")
            return False, None

        torrent_info = self._snapshot_torrent(torrent)
        partially_moved, remaining_eps = self._remaining_episodes(downloader_obj, torrent)
        if partially_moved and remaining_eps is not None and not remaining_eps:
            logger.info(f"{prefix}所有集数都已被MP整理，无需重新下载，只删除种子记录: {torrent.name}")
            try:
                downloader_obj.qbc.torrents_delete(delete_files=False, torrent_hashes=torrent.hash)
            except Exception as e:
                logger.warning(f"{prefix}删除种子记录失败: {torrent.name}, 错误: {e}")
                return False, None
            self._removed_hashes.add(torrent.hash)
            self._events['moved'].append(f"• {self._name(torrent.name)}\n  所有集数均已整理，删除种子记录（原因：{reason}）")
            return True, None
        if remaining_eps:
            torrent_info['episodes'] = sorted(remaining_eps)
            logger.info(f"{prefix}部分集数已整理，替代资源只下载剩余集数 {torrent_info['episodes']}: {torrent.name}")
        ok, detail = self._re_download_torrent(torrent_info)
        if ok:
            misses.pop(torrent.hash, None)
            self._save_replacement_misses(misses)
            # 重新获取种子列表：替代资源若与原种子文件同名同目录，会被识别为共用数据，删除时保留文件
            fresh, error = downloader_obj.get_torrents()
            deleted = self._delete_torrent(downloader_obj, torrent, fresh if not error and fresh else all_torrents, prefix)
            eps_note = f"\n  只下载未整理的 E{'、E'.join(str(e) for e in torrent_info['episodes'])}" if torrent_info.get('episodes') else ""
            self._events['replaced'].append(
                f"• {self._name(torrent.name)}\n  {self._brief(torrent_info)}\n  原因：{reason}\n  ↳ {detail}{eps_note}"
                + ("" if deleted else "\n  （原种子删除失败，请手动处理）"))
            return deleted, None
        fail_reason = detail

        first_miss = not miss
        misses[torrent.hash] = {'ts': now, 'count': (miss or {}).get('count', 0) + 1}
        self._save_replacement_misses(misses)
        logger.warning(f"{prefix}{fail_reason}，保留原种子: {torrent.name}")
        if not first_miss:
            return False, None
        self._events['kept'].append(
            f"• {self._name(torrent.name)}\n  {self._brief(torrent_info)}\n  原因：{reason}\n  ✗ {fail_reason}（6小时后再搜）")
        return False, {
            'name': torrent_info['name'],
            'hash': torrent_info['hash'],
            'size': StringUtils.str_filesize(torrent_info['size']),
            'category': torrent_info.get('category') or 'N/A',
            'tags': torrent_info.get('tags') or 'N/A',
            'tracker': torrent_info.get('tracker') or 'N/A',
            'reason': f"{reason}；{fail_reason}，已保留原种子"
        }

    def _save_replacement_misses(self, misses: dict):
        try:
            self.save_data('replacement_miss', misses)
        except Exception as e:
            logger.debug(f"【重新下载】保存记录失败: {e}")

    @staticmethod
    def _split_lines(text) -> List[str]:
        if not text:
            return []
        return [line.strip() for line in str(text).splitlines() if line.strip()]

    def _get_exclude_reason(self, torrent) -> Optional[str]:
        """命中排除条件时返回原因，否则返回None"""
        name = getattr(torrent, 'name', '') or ''
        name_lower = name.lower()
        for keyword in self._split_lines(self._exclude_keywords):
            if keyword.lower() in name_lower:
                return f"名称包含排除关键字「{keyword}」"

        category = (getattr(torrent, 'category', '') or '').strip()
        if category and category in self._split_lines(self._exclude_categories):
            return f"分类「{category}」在排除列表中"

        exclude_labels = self._split_lines(self._exclude_labels)
        if exclude_labels:
            tags = [t.strip() for t in (getattr(torrent, 'tags', '') or '').split(',') if t.strip()]
            for tag in tags:
                if tag in exclude_labels:
                    return f"标签「{tag}」在排除列表中"
        return None

    def _filter_excluded(self, torrents: list, log_prefix: str) -> list:
        """从待清理列表中剔除命中排除条件的种子"""
        kept = []
        for torrent in torrents:
            reason = self._get_exclude_reason(torrent)
            if reason:
                logger.info(f"{log_prefix}跳过（{reason}）: {getattr(torrent, 'name', '')}")
            else:
                kept.append(torrent)
        if len(kept) != len(torrents):
            logger.info(f"{log_prefix}过滤设置排除了{len(torrents) - len(kept)}个种子，剩余{len(kept)}个待清理")
        return kept

    def _get_seeder_count(self, torrent) -> int:
        """获取做种数，支持多种度量方式：num_complete/connected/availability/auto"""
        metric = (self._seeder_metric or 'num_complete').lower()
        # 优先使用显式度量
        if metric == 'num_complete':
            # 直接使用 num_complete 字段作为做种数
            return self._first_int_attr(torrent, ['num_complete'])
        if metric == 'connected':
            # connected peers as seeders fallback (有的客户端会提供connected种子数)
            return self._first_int_attr(torrent, ['connected_seeds', 'num_complete', 'seeds'])
        if metric == 'availability':
            # 可用性近似：可用性*10 作为粗略整数（避免浮点），仅用于排序
            avail = getattr(torrent, 'availability', None)
            try:
                if isinstance(avail, (int, float)):
                    return int(max(avail, 0) * 10)
            except Exception:
                pass
            return self._first_int_attr(torrent, ['num_seeds', 'seeds', 'seeders'])
        # auto：按照常见字段顺序尝试（包含总计字段）
        return self._first_int_attr(torrent, [
            'num_complete', 'num_seeds', 'seeds', 'seeders', 'connected_seeds'
        ])

    @staticmethod
    def _get_queue_position(torrent) -> int:
        """
        获取种子的队列位置（用于排序）。不同版本的对象可能字段名不同，做兼容。
        优先顺序：priority -> queue_position -> queue_pos -> qpos -> index。
        取不到时返回一个较大的数，避免被优先处理。
        """
        fallback = 10 ** 9
        for name in ['priority', 'queue_position', 'queue_pos', 'qpos', 'index']:
            try:
                val = getattr(torrent, name, None)
                if isinstance(val, (int, float)):
                    return int(val)
                # 字符串数字也尝试转为int
                if isinstance(val, str) and val.isdigit():
                    return int(val)
            except Exception:
                continue
        return fallback

    @staticmethod
    def _first_int_attr(obj, names: list) -> int:
        for name in names:
            try:
                val = getattr(obj, name, None)
                if isinstance(val, (int, float)) and val is not None:
                    return int(val)
            except Exception:
                continue
        return 0

    def _set_qb_torrent_priority(self, downloader_obj, torrent_hash: str, priority_rank: int) -> bool:
        """
        使用qBittorrent原生HTTP API设置种子优先级
        :param downloader_obj: 下载器对象
        :param torrent_hash: 种子哈希
        :param priority_rank: 优先级排名（1为最高）
        :return: 是否设置成功
        """
        try:
            logger.debug(f"【QB种子优化】开始设置种子优先级: hash={torrent_hash}, rank={priority_rank}")
            
            # 获取qBittorrent客户端实例
            qb_client = downloader_obj.qbc
            if not qb_client:
                logger.error("【QB种子优化】无法获取qBittorrent客户端")
                return False
            
            # 使用qBittorrentAPI客户端的_request方法直接调用API
            try:
                # 根据优先级排名选择API端点和调用策略
                if priority_rank == 1:
                    # 最高优先级：设置为顶部
                    logger.debug(f"【QB种子优化】设置种子为最高优先级: topPrio")
                    response = qb_client._request(
                        http_method='POST',
                        api_namespace='torrents',
                        api_method='topPrio',
                        data={'hashes': torrent_hash}
                    )
                    
                elif priority_rank == 2:
                    # 下移优先级
                    logger.debug(f"【QB种子优化】设置种子为下移优先级: decreasePrio")
                    response = qb_client._request(
                        http_method='POST',
                        api_namespace='torrents',
                        api_method='decreasePrio',
                        data={'hashes': torrent_hash}
                    )
                    
                elif priority_rank <= 5:
                    # 高优先级：多次上移（rank=3调用1次，rank=4调用2次，rank=5调用3次）
                    logger.debug(f"【QB种子优化】设置种子为高优先级: increasePrio, 调用次数: {priority_rank - 2}")
                    
                    # 多次调用increasePrio
                    for i in range(priority_rank - 2):
                        response = qb_client._request(
                            http_method='POST',
                            api_namespace='torrents',
                            api_method='increasePrio',
                            data={'hashes': torrent_hash}
                        )
                        logger.debug(f"【QB种子优化】第{i+1}次上移成功")
                    
                elif priority_rank == 999:
                    # 最低优先级：设置为底部
                    logger.debug(f"【QB种子优化】设置种子为最低优先级: bottomPrio")
                    response = qb_client._request(
                        http_method='POST',
                        api_namespace='torrents',
                        api_method='bottomPrio',
                        data={'hashes': torrent_hash}
                    )
                    
                else:
                    # 普通优先级：设置为底部
                    logger.debug(f"【QB种子优化】设置种子为普通优先级: bottomPrio")
                    response = qb_client._request(
                        http_method='POST',
                        api_namespace='torrents',
                        api_method='bottomPrio',
                        data={'hashes': torrent_hash}
                    )
                
                logger.info(f"【QB种子优化】优先级设置成功: {torrent_hash}")
                return True
                
            except Exception as api_error:
                logger.error(f"【QB种子优化】qBittorrent API调用失败: {str(api_error)}")
                return False
                
        except Exception as e:
            logger.error(f"【QB种子优化】设置优先级时发生异常: {str(e)}")
            import traceback
            logger.error(f"【QB种子优化】设置优先级异常详情: {traceback.format_exc()}")
            return False

    def _estimate_remaining_seconds(self, torrent) -> Optional[int]:
        """预计剩余下载时间（秒），无法估算（速度为0）时返回None"""
        eta = self._first_int_attr(torrent, ['eta'])
        if 0 < eta < self.QB_ETA_INFINITY:
            return eta
        dlspeed = getattr(torrent, 'dlspeed', 0) or 0
        if dlspeed > 0:
            amount_left = getattr(torrent, 'amount_left', None)
            if not isinstance(amount_left, (int, float)):
                amount_left = getattr(torrent, 'size', 0) * (1 - getattr(torrent, 'progress', 0))
            return int(amount_left / dlspeed)
        return None

    def _clean_timeout_torrents(self, downloader_obj, torrents, downloader_name):
        """
        清理慢速任务：实际活跃时长超过N小时，且预计剩余时间也超过N小时（或速度为0无法估算）。
        用 time_active（不含排队/暂停时间）而不是添加时间，避免排队很久的种子一开始下载就被清理；
        预计快下完的种子不会被清理。
        """
        prefix = "【功能2-慢速下载】"
        if not self._enable_timeout_clean:
            logger.info(f"{prefix}功能已禁用，跳过")
            return 0, []

        timeout_seconds = self._timeout_hours * 3600
        logger.info(f"{prefix}检查条件: 实际活跃>{self._timeout_hours}小时 且 预计剩余>{self._timeout_hours}小时, 状态=downloading/stalledDL")

        timeout_torrents = []
        for torrent in torrents:
            state_lower = (getattr(torrent, 'state', '') or '').lower()
            if state_lower not in ('downloading', 'stalleddl'):
                continue
            if self._get_seeder_count(torrent) <= self._zero_seed_threshold:
                continue  # 无人做种的交给功能1复核处理
            active_seconds = self._first_int_attr(torrent, ['time_active'])
            if active_seconds <= timeout_seconds:
                continue
            remaining = self._estimate_remaining_seconds(torrent)
            if remaining is not None and remaining <= timeout_seconds:
                logger.debug(f"{prefix}活跃已超时但预计{remaining / 3600:.1f}小时内完成，保留: {torrent.name}")
                continue
            remaining_text = "无法估算（速度为0）" if remaining is None else f"{remaining / 3600:.1f}小时"
            logger.info(f"{prefix}慢速任务: {torrent.name} | 活跃{active_seconds / 3600:.1f}小时 | 预计剩余{remaining_text} | "
                        f"进度{getattr(torrent, 'progress', 0) * 100:.1f}%")
            timeout_torrents.append((torrent, active_seconds, remaining_text))

        kept = set(t.hash for t in self._filter_excluded([t for t, _, _ in timeout_torrents], prefix))
        timeout_torrents = [item for item in timeout_torrents if item[0].hash in kept]
        logger.info(f"{prefix}检查完成，发现{len(timeout_torrents)}个慢速任务")
        if len(timeout_torrents) > self._max_timeout_process:
            logger.info(f"{prefix}超过每次处理上限{self._max_timeout_process}，只处理前{self._max_timeout_process}个")
            timeout_torrents = timeout_torrents[:self._max_timeout_process]

        removed = 0
        redownload_failed_torrents = []
        for i, (torrent, active_seconds, remaining_text) in enumerate(timeout_torrents, 1):
            logger.info(f"{prefix}删除审计 ({i}/{len(timeout_torrents)}): {torrent.name} | HASH={torrent.hash} | "
                        f"速度={StringUtils.str_filesize(getattr(torrent, 'dlspeed', 0))}/s | 大小={StringUtils.str_filesize(getattr(torrent, 'size', 0))}")
            ok, failed = self._replace_torrent(
                downloader_obj, torrent, torrents, f'慢速下载：活跃{active_seconds / 3600:.1f}小时，预计剩余{remaining_text}', prefix)
            removed += int(ok)
            if failed:
                redownload_failed_torrents.append(failed)
        return removed, redownload_failed_torrents

    def _has_recognized_history(self, torrent_hash: str) -> bool:
        """MoviePilot 添加该种子时已识别过媒体信息（下载历史里有 TMDB/豆瓣 ID）"""
        history = self._get_download_history(torrent_hash)
        return bool(history and (getattr(history, 'tmdbid', None) or getattr(history, 'doubanid', None)))

    @staticmethod
    def _get_download_history(torrent_hash: str):
        try:
            from app.db.downloadhistory_oper import DownloadHistoryOper
            return DownloadHistoryOper().get_by_hash(torrent_hash)
        except Exception as e:
            logger.debug(f"【QB种子优化】查询下载历史失败 {torrent_hash}: {e}")
            return None

    # ---------------- AI 辅助识别（可选） ----------------
    AI_MAX_CALLS_PER_RUN = 10
    AI_CACHE_TTL = 7 * 24 * 3600
    AI_TIMEOUT = 60
    AI_PROMPT = (
        "你是影视资源命名解析助手。根据给出的种子名称，推断它对应的影视作品。"
        "只输出一个JSON对象，不要输出其它内容，格式："
        '{"title": "作品中文名或最常用的名称", "original_title": "原名/英文名，没有则为空字符串", '
        '"year": 首播或上映年份整数，不确定则为null, "type": "movie" 或 "tv", "season": 季号整数，不确定则为null}。'
        "如果无法判断是什么作品，title 输出空字符串。"
    )

    def _ai_recognize(self, torrent_name: str) -> Optional[MediaInfo]:
        """
        让 AI 根据种子名推测片名、年份、类型，再交给 TMDB 识别核对。
        AI 只提供线索，必须 TMDB 识别成功才采用；结果按种子名缓存，避免重复调用。
        """
        guess = self._ai_guess(torrent_name)
        if not guess or not guess.get('title'):
            return None
        prefix = "【AI辅助识别】"
        media_chain = MediaChain()
        for title in [guess.get('title'), guess.get('original_title')]:
            if not title:
                continue
            meta = MetaInfo(title)
            if guess.get('year'):
                meta.year = str(guess['year'])
            if guess.get('type') == 'tv':
                meta.type = MediaType.TV
                if guess.get('season'):
                    meta.begin_season = guess['season']
            elif guess.get('type') == 'movie':
                meta.type = MediaType.MOVIE
            try:
                mediainfo = media_chain.recognize_by_meta(meta)
            except Exception as e:
                logger.warning(f"{prefix}TMDB核对异常: {e}")
                mediainfo = None
            if mediainfo:
                logger.info(f"{prefix}{torrent_name} -> AI推测「{title} {guess.get('year') or ''}」-> TMDB确认: {mediainfo.title_year}")
                return mediainfo
        logger.info(f"{prefix}AI推测「{guess.get('title')} {guess.get('year') or ''}」但TMDB未能确认，不采用: {torrent_name}")
        return None

    def _ai_guess(self, torrent_name: str) -> Optional[dict]:
        """AI 根据种子名推测作品信息（带缓存和每轮调用上限），未启用或失败时返回None"""
        if not self._ai_enabled or not torrent_name:
            return None
        prefix = "【AI辅助识别】"
        now = int(time.time())
        try:
            cache = dict(self.get_data('ai_guess_cache') or {})
        except Exception:
            cache = {}
        cached = cache.get(torrent_name)
        if cached and now - cached.get('ts', 0) < self.AI_CACHE_TTL:
            guess = cached.get('guess')
        else:
            if self._ai_calls_this_run >= self.AI_MAX_CALLS_PER_RUN:
                logger.info(f"{prefix}本轮调用已达上限{self.AI_MAX_CALLS_PER_RUN}次，下轮再识别: {torrent_name}")
                return None
            self._ai_calls_this_run += 1
            guess = self._ask_ai_for_media(torrent_name)
            cache[torrent_name] = {'guess': guess, 'ts': now}
            cache = {k: v for k, v in cache.items() if now - v.get('ts', 0) < self.AI_CACHE_TTL}
            try:
                self.save_data('ai_guess_cache', cache)
            except Exception as e:
                logger.debug(f"{prefix}保存缓存失败: {e}")

        if not guess or not guess.get('title'):
            logger.info(f"{prefix}AI未能判断作品: {torrent_name}")
        return guess

    def _ask_ai_for_media(self, torrent_name: str) -> Optional[dict]:
        """调用 MoviePilot 系统中配置的大模型；插件里填写了模型/地址/密钥时覆盖系统设置"""
        prefix = "【AI辅助识别】"
        try:
            from app.agent.llm.helper import LLMHelper
        except Exception as e:
            logger.warning(f"{prefix}当前 MoviePilot 版本不支持 AI 接口: {e}")
            return None

        overrides = {}
        if self._ai_model:
            overrides['model'] = self._ai_model
        if self._ai_base_url:
            overrides['base_url'] = self._ai_base_url
        if self._ai_api_key:
            overrides['api_key'] = self._ai_api_key

        async def _ask():
            llm = await LLMHelper.get_llm(streaming=False, thinking_level="off", **overrides)
            try:
                reply = await asyncio.wait_for(
                    llm.ainvoke([("system", self.AI_PROMPT), ("human", torrent_name)]), timeout=self.AI_TIMEOUT)
                return LLMHelper.extract_text_content(reply.content, fallback_to_string=True)
            finally:
                try:
                    await LLMHelper.close_llm(llm)
                except Exception:
                    pass

        try:
            try:
                asyncio.get_running_loop()
                in_loop = True
            except RuntimeError:
                in_loop = False
            if in_loop:
                from concurrent.futures import ThreadPoolExecutor
                with ThreadPoolExecutor(max_workers=1) as pool:
                    text = pool.submit(lambda: asyncio.run(_ask())).result(timeout=self.AI_TIMEOUT + 30)
            else:
                text = asyncio.run(_ask())
        except Exception as e:
            logger.warning(f"{prefix}调用AI失败: {e}")
            return None
        return self._parse_ai_json(text)

    @staticmethod
    def _parse_ai_json(text: str) -> Optional[dict]:
        if not text:
            return None
        match = re.search(r"\{.*\}", text, re.S)
        if not match:
            return None
        try:
            data = json.loads(match.group(0))
        except Exception:
            return None
        if not isinstance(data, dict):
            return None
        year = data.get('year')
        season = data.get('season')
        return {
            'title': str(data.get('title') or '').strip(),
            'original_title': str(data.get('original_title') or '').strip(),
            'year': int(year) if isinstance(year, (int, float)) or (isinstance(year, str) and year.isdigit()) else None,
            'type': data.get('type') if data.get('type') in ('movie', 'tv') else None,
            'season': int(season) if isinstance(season, (int, float)) or (isinstance(season, str) and season.isdigit()) else None,
        }

    def _clean_unrecognized_torrents(self, downloader_obj, torrents, downloader_name):
        """
        清理识别不到媒体信息的下载任务。
        为避免误删：MoviePilot 下载历史里已有识别记录的跳过；种子元数据未获取（名称仍是hash）的跳过；
        需要连续两次运行（间隔至少1小时）都识别失败才删除，避免 TMDB 偶发故障导致误删。
        """
        prefix = "【功能6-识别不到媒体信息】"
        if not self._enable_unrecognized_clean:
            logger.info(f"{prefix}功能已禁用，跳过")
            return 0

        media_chain = MediaChain()
        now = int(time.time())
        try:
            seen_before = dict(self.get_data('unrecognized_seen') or {})
        except Exception:
            seen_before = {}
        seen_now = {}
        unrecognized_torrents = []

        for torrent in torrents:
            state_lower = (getattr(torrent, 'state', '') or '').lower()
            if state_lower not in ('downloading', 'stalleddl', 'metadl'):
                continue
            torrent_name = getattr(torrent, 'name', '') or ''
            if not torrent_name or torrent_name.lower() == torrent.hash.lower():
                continue
            if self._get_exclude_reason(torrent):
                continue
            if torrent.hash in self._recognized_cache:
                continue
            if self._has_recognized_history(torrent.hash):
                self._recognized_cache.add(torrent.hash)
                continue
            try:
                mediainfo = media_chain.recognize_by_meta(MetaInfo(torrent_name))
            except Exception as e:
                logger.warning(f"{prefix}识别异常，本次跳过: {torrent_name}, 错误: {e}")
                continue
            if mediainfo or self._ai_recognize(torrent_name):
                self._recognized_cache.add(torrent.hash)
                continue

            first_seen = seen_before.get(torrent.hash, now)
            seen_now[torrent.hash] = first_seen
            if now - first_seen < 3600:
                logger.info(f"{prefix}首次识别失败，1小时后复查再决定: {torrent_name}")
                continue
            logger.info(f"{prefix}连续识别失败超过1小时: {torrent_name} | 进度{getattr(torrent, 'progress', 0) * 100:.1f}%")
            unrecognized_torrents.append(torrent)

        try:
            self.save_data('unrecognized_seen', seen_now)
        except Exception as e:
            logger.debug(f"{prefix}保存识别记录失败: {e}")

        logger.info(f"{prefix}检查完成，发现{len(unrecognized_torrents)}个识别不到媒体信息的任务")
        if len(unrecognized_torrents) > self._max_unrecognized_process:
            logger.info(f"{prefix}超过每次处理上限{self._max_unrecognized_process}，只处理前{self._max_unrecognized_process}个")
            unrecognized_torrents = unrecognized_torrents[:self._max_unrecognized_process]

        removed = 0
        for i, torrent in enumerate(unrecognized_torrents, 1):
            logger.info(f"{prefix}删除审计 ({i}/{len(unrecognized_torrents)}): {torrent.name} | HASH={torrent.hash} | "
                        f"大小={StringUtils.str_filesize(getattr(torrent, 'size', 0))} | 分类={getattr(torrent, 'category', '')} | 标签={getattr(torrent, 'tags', '')}")
            if self._delete_torrent(downloader_obj, torrent, torrents, prefix):
                removed += 1
                self._events['deleted'].append(
                    f"• {self._name(torrent.name)}\n  {self._brief(self._snapshot_torrent(torrent))}\n"
                    f"  原因：识别不到媒体信息（持续1小时以上{'，AI也未能确认' if self._ai_enabled else ''}）")
        return removed

    def _mp_download_roots(self) -> List[str]:
        """MoviePilot 目录设置中的下载目录（MP 视角的路径），用于按源路径查询整理记录"""
        try:
            from app.helper.directory import DirectoryHelper
            roots = [str(d.download_path) for d in DirectoryHelper().get_download_dirs() if d.download_path]
        except Exception as e:
            logger.debug(f"【QB种子优化】读取下载目录失败: {e}")
            roots = []
        return list(dict.fromkeys(r.replace('\\', '/').rstrip('/') for r in roots if r))

    @staticmethod
    def _record_ts(record) -> Optional[float]:
        value = getattr(record, 'date', None)
        if not value:
            return None
        try:
            return datetime.strptime(str(value)[:19], '%Y-%m-%d %H:%M:%S').timestamp()
        except Exception:
            return None

    def _get_transfer_records(self, torrent, files=None) -> list:
        """
        该种子的整理记录：按种子 hash 查询，并按文件源路径查询（同一资源从多个站点重复添加时，
        MP 只会把整理记录挂在其中一个 hash 上，其它副本的文件同样已被移走）。
        只保留种子添加之后的记录，避免同一资源删除后重新下载时被旧记录误判。
        """
        try:
            from app.db.transferhistory_oper import TransferHistoryOper
            oper = TransferHistoryOper()
        except Exception as e:
            logger.debug(f"【QB种子优化】整理记录接口不可用: {e}")
            return []
        records = {}
        try:
            for r in oper.list_by_hash(torrent.hash) or []:
                records[getattr(r, 'id', id(r))] = r
        except Exception as e:
            logger.debug(f"【QB种子优化】按hash查询整理记录失败 {torrent.name}: {e}")

        names = [(getattr(f, 'name', '') or '').replace('\\', '/') for f in (files or [])] or [torrent.name]
        tops = {n.split('/')[0] for n in names if n}
        multi = any('/' in n for n in names)
        save_path = (getattr(torrent, 'save_path', '') or '').replace('\\', '/').rstrip('/')
        roots = list(dict.fromkeys(self._mp_download_roots() + ([save_path] if save_path else [])))
        for root in roots:
            for top in tops:
                path = f"{root}/{top}"
                try:
                    if multi and hasattr(oper, 'list_success_by_src'):
                        found = oper.list_success_by_src(src=path, recursive=True) or []
                    else:
                        found = [r for r in [oper.get_by_src(path)] if r]
                except Exception as e:
                    logger.debug(f"【QB种子优化】按路径查询整理记录失败 {path}: {e}")
                    continue
                for r in found:
                    records[getattr(r, 'id', id(r))] = r

        added_on = self._first_int_attr(torrent, ['added_on'])
        result = []
        for r in records.values():
            ts = self._record_ts(r)
            if added_on and ts is not None and ts < added_on - 60:
                continue
            result.append(r)
        return result

    def _moved_by_mp(self, downloader_obj, torrent) -> bool:
        """MoviePilot 已用“移动”方式成功整理过该种子的文件（下载目录里的文件已不在）"""
        try:
            files = downloader_obj.get_files(tid=torrent.hash) or []
        except Exception:
            files = []
        return any(getattr(r, 'status', False) and (getattr(r, 'mode', '') or '') == 'move'
                   for r in self._get_transfer_records(torrent, files))

    @staticmethod
    def _file_index(file, position: int) -> int:
        value = file.get('index') if hasattr(file, 'get') else getattr(file, 'index', None)
        return int(value) if isinstance(value, (int, float)) else position

    def _moved_file_indexes(self, files, records) -> set:
        """按文件相对路径匹配 MP 移动成功记录的源路径，得到已被移走的文件序号（与 qB/MP 的路径映射无关）"""
        moved_src = [(getattr(r, 'src', '') or '').replace('\\', '/') for r in records
                     if getattr(r, 'status', False) and (getattr(r, 'mode', '') or '') == 'move']
        indexes = set()
        for position, file in enumerate(files or []):
            name = (getattr(file, 'name', '') or '').replace('\\', '/')
            if name and any(src == name or src.endswith('/' + name) for src in moved_src):
                indexes.add(self._file_index(file, position))
        return indexes

    @staticmethod
    def _file_episodes(name: str) -> set:
        meta = MetaInfo(name.replace('\\', '/').split('/')[-1])
        return set(getattr(meta, 'episode_list', None) or [])

    def _sync_moved_files(self, downloader_obj, torrents):
        """
        MP 目录监控+移动：季包下载中途已完成的单集会被移走，qB 之后读这些文件（上传或校验）就会报错。
        把已移走的文件设为不下载，并在有新移走的文件或已报错时重新校验一次，让 qB 放弃这些文件的数据，其余集数继续下载。
        """
        prefix = "【功能8-已整理移走】"
        try:
            handled = dict(self.get_data('moved_files_handled') or {})
        except Exception:
            handled = {}
        current = {t.hash for t in torrents}
        handled = {h: v for h, v in handled.items() if h in current}

        for torrent in torrents:
            if getattr(torrent, 'progress', 0) >= 1:
                continue
            try:
                files = downloader_obj.get_files(tid=torrent.hash) or []
            except Exception as e:
                logger.debug(f"{prefix}获取文件列表失败 {torrent.name}: {e}")
                continue
            records = self._get_transfer_records(torrent, files)
            if not records:
                continue
            moved = self._moved_file_indexes(files, records)
            if not moved:
                continue
            priorities = {self._file_index(f, i): getattr(f, 'priority', 1) for i, f in enumerate(files)}
            wanted_left = [i for i, p in priorities.items() if p != 0 and i not in moved]
            if not wanted_left and not self._get_exclude_reason(torrent):
                # 需要的文件已全部被 MP 整理移走：种子已无内容可下，只删除种子记录（不删除任何文件）
                try:
                    downloader_obj.qbc.torrents_delete(delete_files=False, torrent_hashes=torrent.hash)
                except Exception as e:
                    logger.warning(f"{prefix}删除种子记录失败: {torrent.name}, 错误: {e}")
                    continue
                self._removed_hashes.add(torrent.hash)
                handled.pop(torrent.hash, None)
                logger.info(f"{prefix}需要的文件已全部被MP整理移走，删除种子记录: {torrent.name}")
                self._events['moved'].append(
                    f"• {self._name(torrent.name)}\n  {StringUtils.str_filesize(getattr(torrent, 'size', 0))} · "
                    f"{len(moved)} 个文件已全部整理，删除种子记录")
                continue
            to_skip = sorted(i for i in moved if priorities.get(i, 0) != 0)
            state = (getattr(torrent, 'state', '') or '').lower()
            errored = state in ('error', 'missingfiles')
            already = set(handled.get(torrent.hash) or [])
            if not to_skip and not errored and moved <= already:
                continue
            try:
                if to_skip:
                    downloader_obj.qbc.torrents_file_priority(torrent_hash=torrent.hash, file_ids=to_skip, priority=0)
                downloader_obj.qbc.torrents_recheck(torrent_hashes=torrent.hash)
                downloader_obj.start_torrents(ids=[torrent.hash])
            except Exception as e:
                logger.warning(f"{prefix}跳过已移走文件失败: {torrent.name}, 错误: {e}")
                continue
            handled[torrent.hash] = sorted(moved)
            remaining = [f for i, f in enumerate(files) if self._file_index(f, i) not in moved and getattr(f, 'priority', 1) != 0]
            logger.info(f"{prefix}{torrent.name}: 已被MP移走{len(moved)}个文件，设为不下载并重新校验，"
                        f"剩余{len(remaining)}个文件继续下载{'（原为报错状态）' if errored else ''}")
            self._events['synced'].append(
                f"• {self._name(torrent.name)}\n  已整理 {len(moved)} 个文件，剩余 {len(remaining)} 个继续下载 · "
                f"进度 {getattr(torrent, 'progress', 0) * 100:.0f}%" + ("\n  原为报错状态，已恢复" if errored else ""))
        try:
            self.save_data('moved_files_handled', handled)
        except Exception as e:
            logger.debug(f"{prefix}保存记录失败: {e}")

    def _remaining_episodes(self, downloader_obj, torrent) -> Tuple[bool, Optional[set]]:
        """
        部分文件已被 MP 移走的未完成种子：返回 (是否有移走记录, 还没整理的集数)。
        没有移走记录或无法按集区分时集数为 None（下载整个种子）。
        """
        if getattr(torrent, 'progress', 0) >= 1:
            return False, None
        try:
            files = downloader_obj.get_files(tid=torrent.hash) or []
        except Exception:
            files = []
        records = self._get_transfer_records(torrent, files)
        if not any(getattr(r, 'status', False) and (getattr(r, 'mode', '') or '') == 'move' for r in records):
            return False, None
        if not files:
            return True, None
        moved = self._moved_file_indexes(files, records)
        all_eps, moved_eps = set(), set()
        for position, file in enumerate(files):
            eps = self._file_episodes(getattr(file, 'name', '') or '')
            all_eps |= eps
            if self._file_index(file, position) in moved:
                moved_eps |= eps
        if not all_eps:
            return True, None
        return True, all_eps - moved_eps

    def _clean_moved_torrents(self, downloader_obj, torrents, downloader_name):
        """
        MoviePilot 整理方式为“移动”时，文件移走后 qB 里的已完成种子只剩空壳（无法做种，也会占着列表）。
        对已下载完成、完成超过N分钟、且 MP 整理记录里有移动成功记录的种子，只删除种子记录、不删除任何文件。
        """
        prefix = "【功能8-已整理移走】"
        if not self._enable_moved_clean:
            logger.info(f"{prefix}功能已禁用，跳过")
            return 0
        now = int(time.time())
        delay = self._moved_clean_delay_minutes * 60
        removed = 0
        for torrent in torrents:
            if getattr(torrent, 'progress', 0) < 1:
                continue
            completed_on = self._first_int_attr(torrent, ['completion_on'])
            if completed_on > 0 and now - completed_on < delay:
                continue
            if self._get_exclude_reason(torrent):
                continue
            try:
                files = downloader_obj.get_files(tid=torrent.hash) or []
            except Exception:
                files = []
            records = self._get_transfer_records(torrent, files)
            moved = [r for r in records if getattr(r, 'status', False) and (getattr(r, 'mode', '') or '') == 'move']
            if not moved:
                continue
            failed = [r for r in records if not getattr(r, 'status', False)]
            try:
                downloader_obj.qbc.torrents_delete(delete_files=False, torrent_hashes=torrent.hash)
            except Exception as e:
                logger.warning(f"{prefix}删除种子记录失败: {torrent.name}, 错误: {e}")
                continue
            self._removed_hashes.add(torrent.hash)
            removed += 1
            dest = getattr(moved[-1], 'dest', '') or ''
            logger.info(f"{prefix}已删除种子记录（文件已移至 {dest}）: {torrent.name}")
            self._events['moved'].append(
                f"• {self._name(torrent.name)}\n  {StringUtils.str_filesize(getattr(torrent, 'size', 0))} · "
                f"已整理 {len(moved)} 个文件" + (f" · 失败 {len(failed)} 个" if failed else "")
                + (f"\n  → {self._name(dest)}" if dest else ""))
        logger.info(f"{prefix}清理{removed}个文件已被移走的已完成种子")
        return removed

    # ---------------- 重复种子去重 ----------------
    def _dedupe_torrents(self, downloader_obj, torrents):
        """
        同一保存目录下同名的种子会往同一个文件夹写同名文件，互相覆盖、出现 File exists / I/O 错误。
        每组只保留下载量最多的一个（命中过滤设置的优先保留），其余未完成的只删除种子记录、不删除文件；
        已完成的副本不处理（文件被整理移走后由清理功能处理）。
        """
        prefix = "【功能9-重复种子】"
        groups = {}
        for torrent in torrents:
            key = ((getattr(torrent, 'save_path', '') or '').replace('\\', '/').rstrip('/'), torrent.name)
            groups.setdefault(key, []).append(torrent)
        for (_, name), members in groups.items():
            if len(members) < 2:
                continue
            members.sort(key=lambda t: (bool(self._get_exclude_reason(t)), getattr(t, 'progress', 0) >= 1,
                                        self._first_int_attr(t, ['downloaded', 'completed']), getattr(t, 'progress', 0)),
                         reverse=True)
            keeper = members[0]
            for dup in members[1:]:
                if getattr(dup, 'progress', 0) >= 1 or self._get_exclude_reason(dup):
                    continue
                try:
                    downloader_obj.qbc.torrents_delete(delete_files=False, torrent_hashes=dup.hash)
                except Exception as e:
                    logger.warning(f"{prefix}删除重复种子失败: {dup.name}, 错误: {e}")
                    continue
                self._removed_hashes.add(dup.hash)
                logger.info(f"{prefix}同目录同名重复，删除种子记录（保留文件）: {dup.name} "
                            f"[{dup.hash[:8]} 进度{getattr(dup, 'progress', 0) * 100:.0f}%]，保留 [{keeper.hash[:8]} 进度{getattr(keeper, 'progress', 0) * 100:.0f}%]")
                self._events['deleted'].append(
                    f"• {self._name(dup.name)}\n  {StringUtils.str_filesize(getattr(dup, 'size', 0))} · 进度 {getattr(dup, 'progress', 0) * 100:.0f}%\n"
                    f"  原因：同目录同名重复种子，保留进度 {getattr(keeper, 'progress', 0) * 100:.0f}% 的那个（文件保留）")

    # ---------------- qB 报错原因 ----------------
    ERROR_REASON_TEXT = {
        'nospace': '写入失败：磁盘空间不足（No space left on device）',
        'missing': '文件不存在（No such file or directory）',
        'io': '读写出错（I/O error）',
        'other': '其它错误',
    }

    def _refresh_qb_error_reasons(self, downloader_obj, downloader_name) -> dict:
        """从 qB 日志解析每个种子最近一次文件错误的原因，增量读取"""
        reasons = self._qb_error_reasons.setdefault(downloader_name, {})
        try:
            entries = downloader_obj.qbc.log_main(normal=False, info=False, warning=True, critical=True,
                                                  last_known_id=self._qb_log_last_id.get(downloader_name, -1)) or []
        except Exception as e:
            logger.debug(f"【功能7-错误种子】读取qB日志失败: {e}")
            return reasons
        for entry in entries:
            get = entry.get if hasattr(entry, 'get') else (lambda k, d=None: getattr(entry, k, d))
            self._qb_log_last_id[downloader_name] = get('id', self._qb_log_last_id.get(downloader_name, -1))
            message = str(get('message', '') or '')
            name = re.search(r'Torrent[：:]\s*[“"](.+?)[”"]', message)
            if not name:
                continue
            if 'No space left' in message:
                category = 'nospace'
            elif 'No such file' in message:
                category = 'missing'
            elif 'I/O error' in message or 'Input/output error' in message:
                category = 'io'
            elif 'error' in message.lower():
                category = 'other'
            else:
                continue
            detail = re.search(r'(file_\w+)\s*\((.+?)\)\s*error:\s*([^”"]+)', message)
            reasons[name.group(1)] = {
                'category': category,
                'op': detail.group(1) if detail else '',
                'file': detail.group(2) if detail else '',
                'ts': get('timestamp', 0),
            }
        return reasons

    def _handle_error_torrents(self, downloader_obj, torrents, downloader_name):
        """
        处理报错的种子（error / missingFiles）：
        1. 每轮自动重试：error 执行继续，missingFiles 先重新校验再继续（磁盘空间不足时不重试）
        2. 连续重试3轮仍报错时通知一次
        3. 未完成的种子持续报错超过N小时：删除并搜索替代资源重新下载（N为0时不删除）
        已完成的做种种子和命中过滤设置的种子只重试、通知，不删除。
        """
        prefix = "【功能7-错误种子】"
        if not self._enable_error_handle:
            logger.info(f"{prefix}功能已禁用，跳过")
            return 0, []

        now = int(time.time())
        try:
            records = dict(self.get_data('error_torrents') or {})
        except Exception:
            records = {}

        error_torrents = [t for t in torrents
                          if (getattr(t, 'state', '') or '').lower() in ('error', 'missingfiles')]
        error_hashes = {t.hash for t in error_torrents}
        records = {h: v for h, v in records.items() if h in error_hashes}
        if not error_torrents:
            self._save_error_records(records)
            logger.info(f"{prefix}没有报错的种子")
            return 0, []

        free_gb = self._get_free_space_gb(downloader_obj)
        space_ok = free_gb is None or free_gb >= self._min_disk_space_threshold
        timeout_seconds = self._error_timeout_hours * 3600
        qb_reasons = self._refresh_qb_error_reasons(downloader_obj, downloader_name)

        to_delete, to_notify = [], []
        for torrent in error_torrents:
            state = getattr(torrent, 'state', '')
            record = records.get(torrent.hash) or {'first': now, 'retries': 0, 'notified': False}
            reason = qb_reasons.get(torrent.name) or {}
            record['reason'] = reason.get('category', '')
            hours = (now - record['first']) / 3600
            completed = getattr(torrent, 'progress', 0) >= 1
            keep_reason = self._get_exclude_reason(torrent)
            if self._moved_by_mp(downloader_obj, torrent):
                # 已在“处理被整理移走的文件”中跳过移走的文件并重新校验恢复；仍反复报错时通知，不删除
                record['retries'] += 1
                if record['retries'] >= 3 and not record.get('notified'):
                    to_notify.append((torrent, hours, completed, keep_reason or "部分文件已被MP整理移走，已跳过这些文件"))
                    record['notified'] = True
                records[torrent.hash] = record
                logger.info(f"{prefix}文件已被MP整理移走过，由同步逻辑处理，不删除: {torrent.name}")
                continue

            # 磁盘写入失败是存储问题，删掉重下同样会失败，不做超时替换
            if (timeout_seconds > 0 and now - record['first'] >= timeout_seconds
                    and not completed and not keep_reason and record['reason'] != 'nospace'):
                logger.info(f"{prefix}持续报错{hours:.1f}小时，超过{self._error_timeout_hours}小时: {torrent.name}（{state}）")
                to_delete.append((torrent, hours))
                records[torrent.hash] = record
                continue

            reason_text = self.ERROR_REASON_TEXT.get(record['reason'], '原因未知')
            if now < record.get('next_retry', 0):
                logger.info(f"{prefix}{reason_text}，{(record['next_retry'] - now) / 60:.0f}分钟后再重试: {torrent.name}")
            elif space_ok:
                if self._retry_error_torrent(downloader_obj, torrent, record['reason']):
                    record['retries'] += 1
                    # 退避重试：5、10、20…分钟，最长2小时，避免反复失败刷满日志
                    record['next_retry'] = now + min(300 * 2 ** (record['retries'] - 1), 7200)
                    logger.info(f"{prefix}第{record['retries']}次重试（{state}，{reason_text}，已报错{hours:.1f}小时）: {torrent.name}")
            else:
                logger.info(f"{prefix}磁盘剩余{free_gb:.1f}GB低于{self._min_disk_space_threshold}GB，暂不重试: {torrent.name}")

            if record['retries'] >= 3 and not record.get('notified'):
                to_notify.append((torrent, hours, completed, keep_reason))
                record['notified'] = True
            records[torrent.hash] = record

        if to_notify:
            reasons_for = {t.hash: (records.get(t.hash) or {}).get('reason', '') for t, *_ in to_notify}
            lines = []
            for torrent, hours, completed, keep_reason in to_notify:
                if reasons_for.get(torrent.hash) == 'nospace':
                    plan = (f"qB 显示剩余 {free_gb:.0f}G 但写入失败，属于存储问题（inode/合并盘/挂载/配额），"
                            f"删掉重下也会失败，只退避重试，请检查存储") if free_gb is not None else "磁盘写入失败，请检查存储"
                elif completed:
                    plan = "已下载完成，只重试不删除"
                elif keep_reason:
                    plan = f"{keep_reason}，只重试不删除"
                elif self._error_timeout_hours > 0:
                    left = max(self._error_timeout_hours - hours, 0)
                    plan = f"约 {left:.0f} 小时后删除并搜索替代资源"
                else:
                    plan = "未开启超时删除，需手动处理"
                lines.append(f"• {self._name(torrent.name)}\n  {self.ERROR_REASON_TEXT.get(reasons_for.get(torrent.hash), '原因未知')}\n  {getattr(torrent, 'state', '')} · 已报错 {hours:.1f} 小时 · "
                             f"进度 {getattr(torrent, 'progress', 0) * 100:.0f}%\n  路径：{self._name(getattr(torrent, 'save_path', ''))}\n  处理：{plan}")
            self._send('error', f"❗ {self._notify_prefix}｜{len(to_notify)} 个种子重试 3 次仍报错",
                       self._section("报错种子", lines)
                       + "\n常见原因：磁盘写满、保存路径不可写或挂载断开、文件被删除或移动")

        removed = 0
        redownload_failed = []
        for torrent, hours in to_delete[:self._max_zero_seed_process]:
            ok, failed = self._replace_torrent(
                downloader_obj, torrent, torrents, f'报错{hours:.1f}小时（{getattr(torrent, "state", "")}）', prefix)
            if ok:
                removed += 1
                records.pop(torrent.hash, None)
            if failed:
                redownload_failed.append(failed)

        self._save_error_records(records)
        logger.info(f"{prefix}报错种子{len(error_torrents)}个，删除{removed}个")
        return removed, redownload_failed

    def _retry_error_torrent(self, downloader_obj, torrent, reason: str = '') -> bool:
        try:
            # 文件丢失或读写出错：先重新校验，让 qB 找出缺失/损坏的分块重新下载；磁盘写满等其它原因直接继续
            if (getattr(torrent, 'state', '') or '').lower() == 'missingfiles' or reason in ('missing', 'io'):
                downloader_obj.qbc.torrents_recheck(torrent_hashes=torrent.hash)
            return bool(downloader_obj.start_torrents(ids=[torrent.hash]))
        except Exception as e:
            logger.warning(f"【功能7-错误种子】重试失败: {torrent.name}, 错误: {e}")
            return False

    def _save_error_records(self, records: dict):
        try:
            self.save_data('error_torrents', records)
        except Exception as e:
            logger.debug(f"【功能7-错误种子】保存记录失败: {e}")

    @staticmethod
    def _get_free_space_gb(downloader_obj) -> Optional[float]:
        try:
            response = downloader_obj.qbc._request(http_method='POST', api_namespace='sync',
                                                   api_method='maindata', data={'rid': 0})
            free = (response.json().get('server_state') or {}).get('free_space_on_disk')
            return float(free) / 1024 ** 3 if free is not None else None
        except Exception:
            return None

    def _check_system_status_once(self, qb_client, check_disk_space=True):
        """
        单次检查系统状态
        :param qb_client: qBittorrent客户端实例
        :param check_disk_space: 是否检测磁盘空间（默认True，如果前面已检测过可设为False）
        """
        try:
            # 调用qBittorrent API获取服务器状态
            response = qb_client._request(
                http_method='POST',
                api_namespace='sync',
                api_method='maindata',
                data={'rid': 0}
            )
            
            # 解析响应数据
            try:
                response_data = response.json()
            except:
                # 如果response.json()不可用，尝试用json.loads
                import json
                response_data = json.loads(response.text)
            
            if 'server_state' not in response_data:
                return None
            
            server_state = response_data['server_state']
            
            # 获取各项指标
            free_space_gb = server_state.get('free_space_on_disk', 0) / (1024**3) if check_disk_space else 0  # 转换为GB
            write_cache_overload = float(server_state.get('write_cache_overload', 0))  # 百分比，确保是数值
            queued_io_jobs = int(server_state.get('queued_io_jobs', 0))  # I/O任务数，确保是整数
            
            # 判断是否需要限制速度（如果已检测过磁盘空间，则不将其作为限速条件）
            disk_space_insufficient = (free_space_gb < self._disk_space_threshold) if check_disk_space else False
            io_cache_high = write_cache_overload > self._io_cache_threshold
            io_queue_high = queued_io_jobs > self._io_queue_threshold
            should_limit = disk_space_insufficient or io_cache_high or io_queue_high
            
            return {
                'free_space_gb': free_space_gb,
                'write_cache_overload': write_cache_overload,
                'queued_io_jobs': queued_io_jobs,
                'disk_space_insufficient': disk_space_insufficient,
                'io_cache_high': io_cache_high,
                'io_queue_high': io_queue_high,
                'should_limit': should_limit
            }
            
        except Exception as e:
            logger.debug(f"【功能4-磁盘监控】单次检查异常: {str(e)}")
            return None

    def _continuous_monitor_system(self, qb_client, monitor_duration=30, monitor_interval=3, check_disk_space=True):
        """
        持续监测系统状态，确保决策稳定性
        :param qb_client: qBittorrent客户端实例
        :param monitor_duration: 监测时长（秒）
        :param monitor_interval: 监测间隔（秒）
        :param check_disk_space: 是否检测磁盘空间（默认True，如果前面已检测过可设为False）
        """
        # 计算监测次数
        monitor_count = max(1, monitor_duration // monitor_interval)
        actual_duration = monitor_count * monitor_interval
        
        logger.info(f"【功能4-磁盘监控】开始持续监测 {actual_duration} 秒，每 {monitor_interval} 秒检查一次，共 {monitor_count} 次")
        if not check_disk_space:
            logger.info(f"【功能4-磁盘监控】跳过磁盘空间检测（已在优化前检测），仅监测I/O状态")
        
        monitor_results = []
        
        for i in range(monitor_count):
            logger.debug(f"【功能4-磁盘监控】第 {i+1}/{monitor_count} 次检查")
            
            # 单次检查
            result = self._check_system_status_once(qb_client, check_disk_space=check_disk_space)
            if result:
                monitor_results.append(result)
                if check_disk_space:
                    logger.debug(f"【功能4-磁盘监控】第 {i+1} 次检查结果: 磁盘{result['free_space_gb']:.1f}GB, I/O缓存{result['write_cache_overload']:.1f}%, I/O队列{result['queued_io_jobs']}, 需要限速: {result['should_limit']}")
                else:
                    logger.debug(f"【功能4-磁盘监控】第 {i+1} 次检查结果: I/O缓存{result['write_cache_overload']:.1f}%, I/O队列{result['queued_io_jobs']}, 需要限速: {result['should_limit']}")
            else:
                logger.warning(f"【功能4-磁盘监控】第 {i+1} 次检查失败")
            
            # 如果不是最后一次检查，等待指定间隔
            if i < monitor_count - 1:
                import time
                time.sleep(monitor_interval)
        
        if not monitor_results:
            logger.error(f"【功能4-磁盘监控】所有监测都失败，无法做出决策")
            return None, None, None
        
        # 计算平均值用于显示
        avg_free_space = sum(r['free_space_gb'] for r in monitor_results) / len(monitor_results) if check_disk_space else 0
        avg_cache_overload = sum(r['write_cache_overload'] for r in monitor_results) / len(monitor_results)
        avg_io_jobs = sum(r['queued_io_jobs'] for r in monitor_results) / len(monitor_results)
        
        logger.info(f"【功能4-磁盘监控】持续监测完成，共 {len(monitor_results)} 次有效检查")
        logger.info(f"【功能4-磁盘监控】平均状态:")
        if check_disk_space:
            logger.info(f"  - 磁盘剩余空间: {avg_free_space:.2f}GB (阈值: {self._disk_space_threshold}GB)")
        logger.info(f"  - 写入缓存过载: {avg_cache_overload:.1f}% (阈值: {self._io_cache_threshold}%)")
        logger.info(f"  - 队列I/O任务: {avg_io_jobs:.0f} (阈值: {self._io_queue_threshold})")
        
        # 决策规则：使用平均值与阈值对比（如果已检测过磁盘空间，则不将其作为限速条件）
        disk_space_insufficient_avg = (avg_free_space < self._disk_space_threshold) if check_disk_space else False
        io_cache_high_avg = avg_cache_overload > self._io_cache_threshold
        io_queue_high_avg = avg_io_jobs > self._io_queue_threshold
        final_should_limit = disk_space_insufficient_avg or io_cache_high_avg or io_queue_high_avg

        logger.info(
            f"【功能4-磁盘监控】最终决策: {'需要限速' if final_should_limit else '无需限速'}"
        )
        
        # 准备通知消息的数据
        notification_data = {
            'monitor_count': len(monitor_results),
            'avg_free_space': avg_free_space,
            'avg_cache_overload': avg_cache_overload,
            'avg_io_jobs': avg_io_jobs,
            'disk_issues': sum(1 for r in monitor_results if r['disk_space_insufficient']) if check_disk_space else 0,
            'cache_issues': sum(1 for r in monitor_results if r['io_cache_high']),
            'queue_issues': sum(1 for r in monitor_results if r['io_queue_high'])
        }
        
        return final_should_limit, notification_data, monitor_results

    def _monitor_disk_and_io(self, downloader_obj, downloader_name):
        """
        监控I/O状态，持续监测后决定是否限制下载速度
        注意：磁盘空间已在优化前检测过，此处不再重复检测
        """
        logger.info(f"【功能4-磁盘监控】开始I/O监控，功能开关: {self._enable_disk_monitor}")
        
        if not self._enable_disk_monitor:
            logger.info("【功能4-磁盘监控】I/O监控功能已禁用，跳过")
            return False
            
        try:
            # 获取qBittorrent客户端实例
            qb_client = downloader_obj.qbc
            if not qb_client:
                logger.error("【功能4-磁盘监控】无法获取qBittorrent客户端")
                return False
            
            # 获取当前的速度限制设置
            try:
                current_download_limit, current_upload_limit = downloader_obj.get_speed_limit()
                logger.info(f"【功能4-磁盘监控】当前速度限制 - 下载: {current_download_limit}KB/s, 上传: {current_upload_limit}KB/s")
            except Exception as e:
                logger.warning(f"【功能4-磁盘监控】获取当前速度限制失败: {str(e)}")
                current_download_limit, current_upload_limit = 0, 0
            
            # 计算我们的限制值（KB/s）
            our_limit_kbps = int(self._speed_limit_mbps * 1024)
            
            # 如果当前已限速，先解除限速再监测
            if current_download_limit > 0 and current_download_limit <= our_limit_kbps:
                logger.info(f"【功能4-磁盘监控】检测到当前已处于限速状态，先解除限速以获得真实系统状态")
                temp_unlimit_success = self._set_download_speed_limit(downloader_obj, 0)
                if temp_unlimit_success:
                    logger.info(f"【功能4-磁盘监控】临时解除限速成功，等待5秒后开始监测...")
                    time.sleep(5)  # 等待系统状态稳定
                else:
                    logger.warning(f"【功能4-磁盘监控】临时解除限速失败，将在限速状态下进行监测")
            
            # 持续监测系统状态（跳过磁盘空间检测，因为已在优化前检测过）
            final_should_limit, notification_data, monitor_results = self._continuous_monitor_system(
                qb_client, 
                self._monitor_duration, 
                self._monitor_interval,
                check_disk_space=False  # 跳过磁盘空间检测
            )
            
            if final_should_limit is None:
                logger.error("【功能4-磁盘监控】持续监测失败，无法做出决策")
                return False
            
            # 重新获取当前的速度限制设置（因为在监测前可能已经临时解除限速）
            try:
                current_download_limit, current_upload_limit = downloader_obj.get_speed_limit()
                logger.info(f"【功能4-磁盘监控】监测后当前速度限制 - 下载: {current_download_limit}KB/s, 上传: {current_upload_limit}KB/s")
            except Exception as e:
                logger.warning(f"【功能4-磁盘监控】重新获取当前速度限制失败: {str(e)}")
                current_download_limit, current_upload_limit = 0, 0
            
            if final_should_limit and current_download_limit == 0:
                # 需要限速且当前未限速
                logger.warning(f"【功能4-磁盘监控】持续监测确认系统资源不足，开始限制下载速度")
                
                # 限制下载速度
                speed_limit_bytes = int(self._speed_limit_mbps * 1024 * 1024)  # 转换为字节/秒
                success = self._set_download_speed_limit(downloader_obj, speed_limit_bytes)
                
                if success:
                    logger.info(f"【功能4-磁盘监控】下载速度限制成功: {self._speed_limit_mbps}MB/s")
                    
                    if notification_data:
                        n = notification_data['monitor_count']
                        self._send('limit', "🐢 磁盘 I/O 压力过高，已限速",
                                   f"写入缓存 平均 {notification_data['avg_cache_overload']:.0f}%（阈值 {self._io_cache_threshold}%，{notification_data['cache_issues']}/{n} 次超标）\n"
                                   f"I/O 队列 平均 {notification_data['avg_io_jobs']:.0f}（阈值 {self._io_queue_threshold}，{notification_data['queue_issues']}/{n} 次超标）\n"
                                   f"下载已限速 {self._speed_limit_mbps}MB/s，压力下降后自动解除")

                    return True
                else:
                    logger.error(f"【功能4-磁盘监控】下载速度限制失败")
                    return False
                    
            elif not final_should_limit and current_download_limit > 0:
                # 不需要限速但当前已限速，需要恢复
                logger.info(f"【功能4-磁盘监控】持续监测确认系统资源已恢复正常，开始恢复下载速度")
                
                # 恢复下载速度（设置为0表示无限制）
                success = self._set_download_speed_limit(downloader_obj, 0)
                
                if success:
                    logger.info(f"【功能4-磁盘监控】下载速度恢复成功，已取消限制")
                    
                    if notification_data:
                        self._send('limit', "✅ 磁盘 I/O 已恢复，已解除限速",
                                   f"写入缓存 平均 {notification_data['avg_cache_overload']:.0f}%（阈值 {self._io_cache_threshold}%）\n"
                                   f"I/O 队列 平均 {notification_data['avg_io_jobs']:.0f}（阈值 {self._io_queue_threshold}）")

                    return True
                else:
                    logger.error(f"【功能4-磁盘监控】下载速度恢复失败")
                    return False
                    
            elif final_should_limit and current_download_limit > 0:
                # 需要限速且当前已限速，无需操作
                logger.info(f"【功能4-磁盘监控】持续监测确认系统资源仍不足，已处于限速状态，无需操作")
                return True
                
            else:
                # 不需要限速且当前未限速，无需操作
                logger.info(f"【功能4-磁盘监控】持续监测确认系统资源正常，无需限制下载速度")
                return False
                
        except Exception as e:
            logger.error(f"【功能4-磁盘监控】监控过程中发生异常: {str(e)}")
            import traceback
            logger.error(f"【功能4-磁盘监控】异常详情: {traceback.format_exc()}")
            return False

    def _set_download_speed_limit(self, downloader_obj, speed_limit_bytes):
        """
        设置下载器速度限制
        """
        try:
            speed_limit_kbps = int(speed_limit_bytes / 1024)  # 转换为KB/s
            logger.info(f"【功能4-磁盘监控】设置下载速度限制: {speed_limit_bytes} bytes/s ({speed_limit_kbps}KB/s)")
            
            # 获取当前的上传速度限制
            try:
                current_download_limit, current_upload_limit = downloader_obj.get_speed_limit()
                logger.debug(f"【功能4-磁盘监控】当前速度限制 - 下载: {current_download_limit}KB/s, 上传: {current_upload_limit}KB/s")
            except Exception as e:
                logger.warning(f"【功能4-磁盘监控】获取当前速度限制失败: {str(e)}")
                current_download_limit, current_upload_limit = 0, 0
            
            # 使用下载器的set_speed_limit方法设置速度限制
            success = downloader_obj.set_speed_limit(
                download_limit=speed_limit_kbps,
                upload_limit=current_upload_limit
            )
            
            if success:
                logger.info(f"【功能4-磁盘监控】下载速度限制设置成功: {speed_limit_kbps}KB/s")
                return True
            else:
                logger.error(f"【功能4-磁盘监控】下载速度限制设置失败")
                return False
                
        except Exception as e:
            logger.error(f"【功能4-磁盘监控】设置下载速度限制失败: {str(e)}")
            import traceback
            logger.error(f"【功能4-磁盘监控】设置速度限制异常详情: {traceback.format_exc()}")
            return False

    def _manage_download_threshold(self, downloader_obj, torrents, downloader_name):
        """
        下载阈值控制：在“剩余空间 - 最小阈值”的预算内，选出总下载速度最大的一组种子同时下载
        （0/1背包：重量=剩余需下载大小，价值=平滑下载速度），其余暂停；空间富余时按同一规则恢复。
        只恢复本插件暂停过的种子。
        """
        prefix = "【功能5-下载阈值控制】"
        if not self._enable_download_threshold:
            logger.info(f"{prefix}功能已禁用，跳过")
            return False
        try:
            stored = self.get_data('threshold_paused')
        except Exception:
            stored = []
        if stored is None:
            # 首次使用暂停记录：旧版本暂停过的种子没有记录，接管当前所有未完成的暂停种子，之后精确跟踪
            stored = [t.hash for t in torrents
                      if getattr(t, 'progress', 0) < 1
                      and any(k in (getattr(t, 'state', '') or '').lower() for k in ('stopped', 'paused'))]
            logger.info(f"{prefix}首次建立暂停记录，接管{len(stored)}个当前暂停的未完成种子")
        paused_by_plugin = set(stored)
        try:
            speed_ema = dict(self.get_data('speed_ema') or {})
            wait_credit = dict(self.get_data('wait_credit') or {})
            oversize_notified = set(self.get_data('oversize_notified') or [])
        except Exception:
            speed_ema, wait_credit, oversize_notified = {}, {}, set()
        try:
            return self._manage_download_threshold_core(downloader_obj, torrents, paused_by_plugin, speed_ema,
                                                        wait_credit, oversize_notified, prefix)
        except Exception as e:
            logger.error(f"{prefix}执行异常: {e}")
            import traceback
            logger.error(f"{prefix}异常详情: {traceback.format_exc()}")
            return False
        finally:
            current = {t.hash for t in torrents}
            try:
                self.save_data('threshold_paused', [h for h in paused_by_plugin if h in current])
                self.save_data('speed_ema', {h: v for h, v in speed_ema.items() if h in current})
                self.save_data('wait_credit', {h: v for h, v in wait_credit.items() if h in current})
                self.save_data('oversize_notified', [h for h in oversize_notified if h in current])
            except Exception as e:
                logger.debug(f"{prefix}保存记录失败: {e}")

    # 正在下载的种子在选择时的加权，避免为了微小收益来回暂停/恢复
    RUNNING_BONUS = 1.2
    # 正在下载的种子额外加分（MB/s），避免两个都没速度的种子每轮互换；等待补偿约半小时后才会超过它，实现轮换试速
    RUNNING_MARGIN = 0.5
    # 被暂停的种子每等待1小时增加的价值（相当于MB/s），保证慢种子最终也能轮到并下载完
    WAIT_CREDIT_PER_HOUR = 1.0
    # 从未测到速度的种子（新添加的）按此速度估计，让新种子有机会试速，测到真实速度后以实测为准
    UNKNOWN_SPEED_PRIOR = 1.0

    @staticmethod
    def _is_downloading_state(torrent) -> bool:
        state_lower = (getattr(torrent, 'state', '') or '').lower()
        if any(k in state_lower for k in ('stopped', 'paused')):
            return False
        try:
            if torrent.state_enum.is_downloading:
                return True
        except Exception:
            pass
        return state_lower in ('downloading', 'stalleddl', 'metadl', 'queueddl', 'forceddl')

    def _never_started(self, torrent) -> bool:
        """添加后从未开始下载的停止种子（MP 或 qB 设置导致添加即停止），视为等待调度"""
        return (self._is_paused_state(torrent)
                and self._first_int_attr(torrent, ['time_active']) <= 0
                and self._first_int_attr(torrent, ['downloaded', 'completed']) <= 0)

    @staticmethod
    def _is_paused_state(torrent) -> bool:
        state_lower = (getattr(torrent, 'state', '') or '').lower()
        return any(k in state_lower for k in ('stopped', 'paused'))

    @staticmethod
    def _qb_preallocate_enabled(downloader_obj) -> bool:
        try:
            return bool((downloader_obj.qbc.app_preferences() or {}).get('preallocate_all'))
        except Exception as e:
            logger.debug(f"【功能5-下载阈值控制】读取qB预分配设置失败: {e}")
            return False

    def _remaining_download_bytes(self, downloader_obj, torrent) -> Optional[float]:
        """只统计需要下载（优先级不为0）且未完成的文件"""
        try:
            files = downloader_obj.get_files(tid=torrent.hash)
        except Exception as e:
            logger.debug(f"【功能5-下载阈值控制】获取文件列表失败 {torrent.name}: {e}")
            return None
        if not files:
            return None
        remaining = 0.0
        for file in files:
            if getattr(file, 'priority', 0) == 0:
                continue
            progress = getattr(file, 'progress', 0)
            if progress >= 1.0:
                continue
            remaining += getattr(file, 'size', 0) * (1 - progress)
        return remaining

    @staticmethod
    def _knapsack_select(items: List[Tuple[str, float, float]], budget_bytes: float) -> set:
        """
        0/1背包：items 为 (hash, 重量字节, 价值)，返回总重量不超过预算时价值最大的 hash 集合。
        重量按单位向上取整，保证选中集合的真实总大小不会超出预算。
        """
        if budget_bytes <= 0 or not items:
            return set()
        unit = max(256 * 1024 ** 2, budget_bytes / 4000)
        capacity = int(budget_bytes // unit)
        weights = [max(1, math.ceil(weight / unit)) for _, weight, _ in items]
        best = [0.0] * (capacity + 1)
        take = [bytearray(capacity + 1) for _ in items]
        for i, (_, _, value) in enumerate(items):
            w = weights[i]
            if w > capacity or value <= 0:
                continue
            for c in range(capacity, w - 1, -1):
                candidate = best[c - w] + value
                if candidate > best[c]:
                    best[c] = candidate
                    take[i][c] = 1
        chosen = set()
        c = capacity
        for i in range(len(items) - 1, -1, -1):
            if take[i][c]:
                chosen.add(items[i][0])
                c -= weights[i]
        return chosen

    def _manage_download_threshold_core(self, downloader_obj, torrents, paused_by_plugin: set, speed_ema: dict,
                                        wait_credit: dict, oversize_notified: set, prefix: str) -> bool:
        try:
            response = downloader_obj.qbc._request(http_method='POST', api_namespace='sync',
                                                   api_method='maindata', data={'rid': 0})
            server_state = response.json().get('server_state') or {}
        except Exception as e:
            logger.error(f"{prefix}获取磁盘空间失败: {e}")
            return False
        free_bytes = float(server_state.get('free_space_on_disk', 0) or 0)
        if free_bytes <= 0:
            logger.warning(f"{prefix}未获取到磁盘剩余空间，跳过")
            return False
        budget_bytes = free_bytes - self._min_disk_space_threshold * 1024 ** 3
        preallocate = self._qb_preallocate_enabled(downloader_obj)

        running, paused = [], []
        for torrent in torrents:
            if getattr(torrent, 'progress', 0) >= 1.0:
                continue
            if self._is_paused_state(torrent):
                if torrent.hash in paused_by_plugin or self._never_started(torrent):
                    paused.append(torrent)
            elif self._is_downloading_state(torrent):
                running.append(torrent)

        running_hashes = {t.hash for t in running}
        # 全局下载限速（如磁盘/IO监控触发）时速度失真，不更新平滑速度，沿用之前的记录
        try:
            download_limited = (downloader_obj.get_speed_limit() or (0, 0))[0] > 0
        except Exception:
            download_limited = False
        if download_limited:
            logger.info(f"{prefix}下载器处于全局限速状态，本轮沿用之前记录的平均速度")
        now = time.time()
        items = []
        info = {}
        oversize = []
        for torrent in running + paused:
            remaining = self._remaining_download_bytes(downloader_obj, torrent)
            if remaining is None or remaining <= 0:
                continue
            is_running = torrent.hash in running_hashes
            if is_running:
                current = (getattr(torrent, 'dlspeed', 0) or 0) / 1024 ** 2
                previous = speed_ema.get(torrent.hash)
                if download_limited:
                    speed = current if previous is None else previous
                else:
                    speed = current if previous is None else 0.6 * current + 0.4 * previous
                    speed_ema[torrent.hash] = round(speed, 3)
            else:
                speed = speed_ema.get(torrent.hash, self.UNKNOWN_SPEED_PRIOR)
            # 等待补偿：暂停期间按小时累积，恢复后保留到下载完成，避免慢种子永远轮不到
            record = wait_credit.get(torrent.hash) or {'credit': 0.0, 'ts': now}
            if not is_running:
                record['credit'] += self.WAIT_CREDIT_PER_HOUR * max(now - record.get('ts', now), 0) / 3600
            record['ts'] = now
            wait_credit[torrent.hash] = {'credit': round(record['credit'], 3), 'ts': now}
            # 没有速度数据的种子给一个很小的价值，让剩余预算可以分给它们去试速度
            value = speed + record['credit'] + 0.001 * min(self._get_seeder_count(torrent), 100) + 0.0001
            if is_running:
                value = value * self.RUNNING_BONUS + self.RUNNING_MARGIN
            # qB 开启预分配时，启动过的种子已经占好了磁盘空间，继续下载不再消耗剩余空间
            weight = 0.0 if preallocate and self._first_int_attr(torrent, ['time_active']) > 0 else remaining
            keep_reason = self._get_exclude_reason(torrent)
            if weight > max(budget_bytes, 0):
                oversize.append((torrent, remaining))
            items.append((torrent.hash, weight, value))
            info[torrent.hash] = (torrent, remaining, speed, is_running, weight, keep_reason)

        total_running = sum(info[h][4] for h in info if info[h][3])
        logger.info(f"{prefix}剩余空间 {StringUtils.str_filesize(free_bytes)}，最小阈值 {self._min_disk_space_threshold}GB，"
                    f"可用预算 {StringUtils.str_filesize(max(budget_bytes, 0))}；下载中{len(running)}个"
                    f"（还需{StringUtils.str_filesize(total_running)}），插件暂停{len(paused)}个"
                    f"{'，qB已开启预分配（已启动过的种子不再计入）' if preallocate else ''}")
        new_oversize = [(t, r) for t, r in oversize if t.hash not in oversize_notified]
        for torrent, remaining in oversize:
            logger.warning(f"{prefix}剩余{StringUtils.str_filesize(remaining)}超过可用预算，当前空间下无法下载完成: {torrent.name}")
        if new_oversize:
            self._send('oversize', f"📦 {self._notify_prefix}｜{len(new_oversize)} 个种子超出可用空间",
                       f"💾 剩余 {StringUtils.str_filesize(free_bytes)} − 阈值 {self._min_disk_space_threshold}G = 预算 {StringUtils.str_filesize(max(budget_bytes, 0))}\n"
                       + self._section("当前空间下无法下载完成", [
                           f"• {self._name(t.name)}\n  还需 {StringUtils.str_filesize(r)} · 进度 {getattr(t, 'progress', 0) * 100:.0f}%"
                           for t, r in new_oversize])
                       + "\n建议清理磁盘空间；要优先下载的种子可打上 keep 标签")
        oversize_notified.update(t.hash for t, _ in new_oversize)
        if not items:
            return False

        if total_running <= budget_bytes and not paused:
            logger.info(f"{prefix}下载中种子总需求在预算内，无需调整")
            return False

        # 必定保持下载：命中过滤设置的种子（如keep标签），以及不再占用剩余空间的种子；先扣除它们的空间，再对其余种子求最优
        keep_hashes = {h for h in info if info[h][5]}
        forced = keep_hashes | {h for h in info if info[h][4] <= 0}
        forced_weight = sum(info[h][4] for h in forced)
        for h in keep_hashes:
            logger.info(f"{prefix}保持下载（{info[h][5]}）: {info[h][0].name}，还需{StringUtils.str_filesize(info[h][1])}")
        if forced_weight > budget_bytes:
            logger.warning(f"{prefix}保持下载的种子共需{StringUtils.str_filesize(forced_weight)}，已超过可用预算，其它种子将全部暂停")

        chosen = forced | self._knapsack_select([i for i in items if i[0] not in forced], budget_bytes - forced_weight)
        to_pause = [h for h in info if info[h][3] and h not in chosen]
        to_resume = [h for h in info if not info[h][3] and h in chosen]
        chosen_size = sum(info[h][4] for h in chosen)
        chosen_speed = sum(info[h][2] for h in chosen)
        logger.info(f"{prefix}最优组合: {len(chosen)}个种子（其中保持下载{len(keep_hashes)}个），需{StringUtils.str_filesize(chosen_size)}，"
                    f"预计总速度{chosen_speed:.2f}MB/s；暂停{len(to_pause)}个，恢复{len(to_resume)}个")

        paused_names, resumed_names = [], []
        for torrent_hash in to_pause:
            torrent, remaining, speed = info[torrent_hash][:3]
            try:
                if downloader_obj.stop_torrents(ids=[torrent_hash]):
                    paused_by_plugin.add(torrent_hash)
                    paused_names.append(f"• {self._name(torrent.name)}\n  平均 {speed:.2f}MB/s · 还需 {StringUtils.str_filesize(remaining)}")
                    logger.info(f"{prefix}暂停: {torrent.name}（平均{speed:.2f}MB/s，剩余{StringUtils.str_filesize(remaining)}）")
                else:
                    logger.warning(f"{prefix}暂停失败: {torrent.name}")
            except Exception as e:
                logger.error(f"{prefix}暂停异常: {torrent.name}, 错误: {e}")
        for torrent_hash in to_resume:
            torrent, remaining, speed = info[torrent_hash][:3]
            if torrent_hash in speed_ema:
                speed_text = f"上次平均 {speed:.2f}MB/s"
            elif self._never_started(torrent):
                speed_text = "新添加，首次开始下载"
            else:
                speed_text = "速度未知，试速"

            try:
                if downloader_obj.start_torrents(ids=[torrent_hash]):
                    paused_by_plugin.discard(torrent_hash)
                    resumed_names.append(f"• {self._name(torrent.name)}\n  {speed_text} · 还需 {StringUtils.str_filesize(remaining)}")
                    logger.info(f"{prefix}恢复: {torrent.name}（{speed_text}，剩余{StringUtils.str_filesize(remaining)}）")
                else:
                    logger.warning(f"{prefix}恢复失败: {torrent.name}")
            except Exception as e:
                logger.error(f"{prefix}恢复异常: {torrent.name}, 错误: {e}")

        # 试速放在调度动作之后，且失败不影响已完成的暂停/恢复
        try:
            probed_names = self._probe_new_torrents(
                downloader_obj, [info[h][0] for h in info if not info[h][3] and h not in chosen and self._never_started(info[h][0])],
                speed_ema, paused_by_plugin, prefix)
        except Exception as e:
            logger.warning(f"{prefix}新种子试速失败: {e}")
            probed_names = []

        if paused_names or resumed_names or probed_names:
            self._send('threshold', f"⚖️ {self._notify_prefix}｜下载调度：暂停 {len(paused_names)} · 恢复 {len(resumed_names)}",
                       f"💾 剩余 {StringUtils.str_filesize(free_bytes)}｜预算 {StringUtils.str_filesize(max(budget_bytes, 0))}\n"
                       f"⬇️ 保持下载 {len(chosen)} 个 · 需 {StringUtils.str_filesize(chosen_size)} · 约 {chosen_speed:.1f}MB/s"
                       + (f"（含 keep {len(keep_hashes)} 个）" if keep_hashes else "") + "\n"
                       + self._section("⏸ 暂停", paused_names)
                       + self._section("▶️ 恢复", resumed_names)
                       + self._section("🔍 新种子试速（空间不够暂未下载）", probed_names))
        return bool(paused_names or resumed_names)

    PROBE_NEW_PER_RUN = 10
    PROBE_MIN_SECONDS = 20

    def _probe_new_torrents(self, downloader_obj, torrents, speed_ema: dict, paused_by_plugin: set, prefix: str) -> list:
        """
        空间预算暂时放不下的新种子（添加即停止、从未开始）：临时强制开始并向 tracker 汇报，
        在设定时间内拿到做种数和初始速度后停回去，结果用于后续调度排序；之后按插件暂停的种子正常轮换。
        """
        targets = [t for t in torrents if t.hash not in speed_ema][:self.PROBE_NEW_PER_RUN]
        if not targets:
            return []
        hashes = [t.hash for t in targets]
        logger.info(f"{prefix}{len(targets)}个新种子空间不够暂不下载，先试速获取做种数和速度")
        forced = self._set_force_start(downloader_obj, hashes, True)
        try:
            started_at = time.time()
            downloader_obj.start_torrents(ids=hashes)
            self._reannounce(downloader_obj, hashes)
            seeders = self._poll_tracker_seeders(downloader_obj, hashes)
            # tracker 往往几秒就返回，此时还没连上用户、速度为0；至少下载一段时间再读速度
            ramp_left = self.PROBE_MIN_SECONDS - (time.time() - started_at)
            if ramp_left > 0 and any((n or 0) > 0 for n in seeders.values()):
                time.sleep(ramp_left)
            refreshed, error = downloader_obj.get_torrents(ids=hashes)
            speeds = {t.hash: (getattr(t, 'dlspeed', 0) or 0) / 1024 ** 2 for t in (refreshed or [])} if not error else {}
        finally:
            if forced:
                self._set_force_start(downloader_obj, hashes, False)
            try:
                downloader_obj.stop_torrents(ids=hashes)
            except Exception as e:
                logger.warning(f"{prefix}试速后停止失败: {e}")
        lines = []
        for torrent in targets:
            n = seeders.get(torrent.hash)
            speed = speeds.get(torrent.hash, 0.0)
            if n == 0:
                speed_ema[torrent.hash] = 0.0
            elif speed > 0:
                speed_ema[torrent.hash] = round(speed, 3)
            paused_by_plugin.add(torrent.hash)
            seed_text = "未知" if n is None else str(n)
            logger.info(f"{prefix}试速: {torrent.name} 做种{seed_text}，初始速度{speed:.2f}MB/s")
            lines.append(f"• {self._name(torrent.name)}\n  做种 {seed_text} · 初始 {speed:.2f}MB/s"
                         + (" · ⚠️ 无人做种" if n == 0 else ""))
        return lines

    def _log_qb_add_settings(self, downloader_obj, downloader_name):
        """记录会导致新种子添加后处于停止状态的 qB 设置，便于排查"""
        if downloader_name in self._qb_settings_logged:
            return
        self._qb_settings_logged.add(downloader_name)
        try:
            prefs = downloader_obj.qbc.app_preferences() or {}
        except Exception as e:
            logger.debug(f"【QB种子优化】读取qB设置失败: {e}")
            return
        add_stopped = prefs.get('add_stopped_enabled', prefs.get('start_paused_enabled'))
        stop_condition = prefs.get('torrent_stop_condition')
        logger.info(f"【QB种子优化】{downloader_name} qB设置: 添加后不自动开始={add_stopped}，种子停止条件={stop_condition}，"
                    f"队列={prefs.get('queueing_enabled')}（最大活动下载{prefs.get('max_active_downloads')}），"
                    f"预分配={prefs.get('preallocate_all')}")
        if add_stopped or (stop_condition and str(stop_condition) not in ('None', '0')):
            logger.warning(f"【QB种子优化】{downloader_name} 的 qB 设置会让新种子添加后处于停止状态"
                           f"（添加后不自动开始={add_stopped}，停止条件={stop_condition}），插件会按空间预算自动开始或试速")

    def _re_download_torrent(self, torrent_info) -> Tuple[bool, str]:
        """
        重新下载：优先用 MoviePilot 下载历史里的 TMDB ID 精确识别，其次按种子名识别，
        识别成功后按媒体信息搜索（结果已按片名/年份匹配），识别失败才退回到按标题关键词搜索。
        候选需满足季集一致、大小相近、做种数达标，并限制同一资源的重试次数，避免反复删了又下。
        """
        prefix = "【重新下载】"
        name = torrent_info['name']
        meta = MetaInfo(name)
        attempt_key = self._redownload_key(meta, name)
        history = self._load_redownload_history()
        attempts = history.get(attempt_key, {}).get('count', 0)
        if attempts >= self._redownload_max_attempts:
            logger.warning(f"{prefix}{attempt_key} 已自动重新下载{attempts}次，不再重试: {name}")
            return False, f"已自动重新下载{attempts}次，停止重试"

        mediainfo = self._recognize_for_redownload(torrent_info['hash'], meta)
        candidates = self._search_candidates(meta, mediainfo, name)
        if not candidates:
            return False, "未搜索到候选资源"

        best, reason = self._select_best_torrent(candidates, torrent_info, meta)
        if not best:
            logger.warning(f"{prefix}没有合适的替代资源（{reason}）: {name}")
            return False, reason

        if not self._download_torrent(best, torrent_info, mediainfo):
            return False, "提交下载失败（可能下载器中已存在）"

        history[attempt_key] = {'count': attempts + 1, 'ts': int(time.time()), 'title': best.torrent_info.title}
        self._save_redownload_history(history)
        ti = best.torrent_info
        return True, (f"{self._name(ti.title)}\n  {getattr(ti, 'site_name', '') or '未知站点'} · 做种 {getattr(ti, 'seeders', 0)}"
                      f" · {StringUtils.str_filesize(getattr(ti, 'size', 0) or 0)}"
                      f"{'（第' + str(attempts + 1) + '次自动重下）' if attempts else ''}")

    @staticmethod
    def _redownload_key(meta, name: str) -> str:
        title = getattr(meta, 'name', None) or name
        year = getattr(meta, 'year', None) or ''
        season_episode = (getattr(meta, 'season_episode', '') or '').replace(' ', '')
        return f"{title}|{year}|{season_episode}"

    def _load_redownload_history(self) -> dict:
        try:
            history = dict(self.get_data('redownload_history') or {})
        except Exception:
            return {}
        expire = int(time.time()) - 30 * 24 * 3600
        return {k: v for k, v in history.items() if v.get('ts', 0) >= expire}

    def _save_redownload_history(self, history: dict):
        try:
            self.save_data('redownload_history', history)
        except Exception as e:
            logger.debug(f"【重新下载】保存重试记录失败: {e}")

    def _recognize_for_redownload(self, torrent_hash: str, meta) -> Optional[MediaInfo]:
        prefix = "【重新下载】"
        media_chain = MediaChain()
        history = self._get_download_history(torrent_hash)
        if history and getattr(history, 'tmdbid', None):
            try:
                mtype = MediaType(history.type) if getattr(history, 'type', None) else None
                mediainfo = media_chain.recognize_media(mtype=mtype, tmdbid=history.tmdbid)
                if mediainfo:
                    logger.info(f"{prefix}按下载历史TMDB ID识别: {mediainfo.title_year}")
                    return mediainfo
            except Exception as e:
                logger.warning(f"{prefix}按下载历史识别失败: {e}")
        try:
            mediainfo = media_chain.recognize_by_meta(meta)
            if mediainfo:
                logger.info(f"{prefix}按种子名识别: {mediainfo.title_year}")
                return mediainfo
        except Exception as e:
            logger.warning(f"{prefix}按种子名识别失败: {e}")
        return self._ai_recognize(getattr(meta, 'org_string', None) or meta.title)

    def _search_candidates(self, meta, mediainfo: Optional[MediaInfo], name: str) -> list:
        prefix = "【重新下载】"
        search_chain = SearchChain()
        sites = self._search_sites or None
        if mediainfo:
            try:
                results = search_chain.process(mediainfo=mediainfo, sites=sites) or []
                logger.info(f"{prefix}按媒体信息搜索 {mediainfo.title_year}，得到{len(results)}个候选")
                if results:
                    return results
            except Exception as e:
                logger.warning(f"{prefix}按媒体信息搜索失败，改用标题搜索: {e}")

        keyword = self._extract_search_keyword(name, meta)
        results = []
        for page in range(3):
            try:
                page_results = search_chain.search_by_title(title=keyword, page=page, sites=sites) or []
            except Exception as e:
                logger.error(f"{prefix}第{page + 1}页搜索失败: {e}")
                break
            results.extend(page_results)
            if not page_results:
                break
        logger.info(f"{prefix}按标题「{keyword}」搜索，得到{len(results)}个候选")
        if results:
            return results

        guess = self._ai_guess(name) or {}
        for alt in [guess.get('title'), guess.get('original_title')]:
            if not alt or alt == keyword:
                continue
            try:
                results = search_chain.search_by_title(title=alt, page=0, sites=sites) or []
            except Exception as e:
                logger.error(f"{prefix}按AI给出的名称搜索失败: {e}")
                continue
            logger.info(f"{prefix}按AI给出的名称「{alt}」搜索，得到{len(results)}个候选")
            if results:
                return results
        return results

    @staticmethod
    def _extract_search_keyword(torrent_name: str, meta=None) -> str:
        """用 MoviePilot 的元数据解析取片名，避免把剧集标题、来源、编码等带进搜索词"""
        meta = meta or MetaInfo(torrent_name)
        keyword = (getattr(meta, 'cn_name', None) or getattr(meta, 'en_name', None)
                   or getattr(meta, 'name', None) or '').strip()
        return keyword or torrent_name

    def _select_best_torrent(self, search_results, original_torrent_info, original_meta) -> Tuple[Optional[Context], str]:
        """
        过滤：做种数达标、季集与原种子一致、大小在允许偏差内；
        排序：做种数优先，其次大小与原种子越接近越好。
        """
        prefix = "【重新下载】"
        min_seeders = max(self._redownload_min_seeders, self._zero_seed_threshold + 1)
        original_size = original_torrent_info.get('size', 0) or 0
        orig_seasons = set(getattr(original_meta, 'season_list', None) or [])
        orig_episodes = set(getattr(original_meta, 'episode_list', None) or [])
        tolerance = self._redownload_size_tolerance / 100 if self._redownload_size_tolerance > 0 else None

        stats = {'seeders': 0, 'season': 0, 'size': 0}
        qualified = []
        for result in search_results:
            ti = getattr(result, 'torrent_info', None)
            if not ti:
                continue
            seeders = self._to_int(getattr(ti, 'seeders', 0), 0)
            size = getattr(ti, 'size', 0) or 0
            if seeders < min_seeders:
                stats['seeders'] += 1
                continue
            cand_meta = getattr(result, 'meta_info', None) or MetaInfo(ti.title, getattr(ti, 'description', None))
            cand_seasons = set(getattr(cand_meta, 'season_list', None) or [])
            cand_episodes = set(getattr(cand_meta, 'episode_list', None) or [])
            if (orig_seasons or orig_episodes) and (cand_seasons != orig_seasons or cand_episodes != orig_episodes):
                stats['season'] += 1
                continue
            if tolerance is not None and original_size > 0 and abs(size - original_size) / original_size > tolerance:
                stats['size'] += 1
                continue
            qualified.append((seeders, abs(size - original_size), result))

        summary = (f"候选{len(search_results)}个：做种<{min_seeders} {stats['seeders']}个，"
                   f"季集不一致 {stats['season']}个，大小偏差>{self._redownload_size_tolerance}% {stats['size']}个")
        logger.info(f"{prefix}{summary}，符合条件{len(qualified)}个")
        if not qualified:
            return None, summary

        qualified.sort(key=lambda x: (-x[0], x[1]))
        for idx, (seeders, _, result) in enumerate(qualified[:5], 1):
            ti = result.torrent_info
            logger.info(f"{prefix}  {idx}. 做种{seeders} | {StringUtils.str_filesize(ti.size)} | {getattr(ti, 'site_name', '')} | {ti.title}")
        best = qualified[0][2]
        logger.info(f"{prefix}选择: {best.torrent_info.title}")
        return best, ""

    def _download_torrent(self, search_result, original_torrent_info, mediainfo: Optional[MediaInfo] = None) -> bool:
        prefix = "【重新下载】"
        try:
            torrent_info = search_result.torrent_info
            meta_info = search_result.meta_info or MetaInfo(torrent_info.title, getattr(torrent_info, 'description', None))
            media_info = search_result.media_info or mediainfo
            if not media_info:
                media_info = MediaInfo()
                media_info.category = original_torrent_info.get('category') or '其它'
                media_info.type = MediaType.UNKNOWN
                media_info.title = meta_info.title if meta_info else torrent_info.title
                logger.info(f"{prefix}未识别到媒体信息，使用默认配置")

            context = Context(meta_info=meta_info, media_info=media_info, torrent_info=torrent_info)
            # 标记绕过下载器负载均衡，避免与负载均衡插件冲突
            setattr(context, "_bypass_downloader_balancer", True)

            save_path = original_torrent_info.get('save_path') or None
            logger.info(f"{prefix}提交下载: {torrent_info.title} | 站点={torrent_info.site_name} | "
                        f"下载器={self._current_downloader} | 目录={save_path or '默认'}")
            episodes = set(original_torrent_info.get('episodes') or []) or None
            download_id = DownloadChain().download_single(
                context=context,
                episodes=episodes,
                downloader=self._current_downloader,
                save_path=save_path,
                username=self.plugin_name,
            )
            if download_id:
                logger.info(f"{prefix}下载成功: {torrent_info.title}, 下载ID: {download_id}")
                return True
            logger.error(f"{prefix}下载失败: {torrent_info.title}")
            return False
        except Exception as e:
            logger.error(f"{prefix}下载异常: {e}")
            import traceback
            logger.error(f"{prefix}异常详情: {traceback.format_exc()}")
            return False

    def show_status(self):
        """
        显示优化状态
        """
        logger.info("【QB种子优化】开始显示状态...")
        
        for downloader_name in self._downloaders:
            logger.info(f"【QB种子优化】检查下载器状态: {downloader_name}")
            
            try:
                downloader_obj = self.__get_downloader(downloader_name)
                if not downloader_obj:
                    logger.error(f"【QB种子优化】无法获取下载器: {downloader_name}")
                    continue

                logger.info(f"【QB种子优化】获取种子列表: {downloader_name}")
                all_torrents, error = downloader_obj.get_torrents()
                if error:
                    logger.error(f"【QB种子优化】获取种子列表失败: {downloader_name}, 错误: {error}")
                    continue

                logger.info(f"【QB种子优化】种子列表获取成功: {downloader_name}, 总数: {len(all_torrents)}")

                # 统计各种状态的种子
                downloading = [t for t in all_torrents if t.state_enum.is_downloading]
                uploading = [t for t in all_torrents if t.state_enum.is_uploading]
                zero_seed = [t for t in downloading if self._get_seeder_count(t) <= self._zero_seed_threshold]
                # high_seed = [t for t in downloading if t.num_seeds >= 10]  # 已改为综合评分判断
                
                # 详细统计
                logger.info(f"【QB种子优化】{downloader_name} 详细统计:")
                logger.info(f"  - 总种子数: {len(all_torrents)}")
                logger.info(f"  - 下载中: {len(downloading)}")
                logger.info(f"  - 做种中: {len(uploading)}")
                logger.info(f"  - 做种数为0 (阈值≤{self._zero_seed_threshold}): {len(zero_seed)}")
                # logger.info(f"  - 高做种数: 已改为综合评分判断")
                
                # 显示做种数为0的种子详情
                if zero_seed:
                    logger.info(f"【QB种子优化】做种数为0的种子详情:")
                    for i, torrent in enumerate(zero_seed[:5], 1):  # 只显示前5个
                        logger.info(f"  {i}. {torrent.name} (做种数: {self._get_seeder_count(torrent)}, 进度: {torrent.progress * 100:.1f}%)")
                    if len(zero_seed) > 5:
                        logger.info(f"  ... 还有 {len(zero_seed) - 5} 个")
                
                # 显示高做种数的种子详情（已改为综合评分判断）
                # if high_seed:
                #     logger.info(f"【QB种子优化】高做种数的种子详情:")
                #     for i, torrent in enumerate(high_seed[:5], 1):  # 只显示前5个
                #         logger.info(f"  {i}. {torrent.name} (做种数: {torrent.num_seeds})")
                #     if len(high_seed) > 5:
                #         logger.info(f"  ... 还有 {len(high_seed) - 5} 个")
                
                errors = [t for t in all_torrents if (getattr(t, 'state', '') or '').lower() in ('error', 'missingfiles')]
                try:
                    paused_by_plugin = len(self.get_data('threshold_paused') or [])
                except Exception:
                    paused_by_plugin = 0
                free_gb = self._get_free_space_gb(downloader_obj)
                status_msg = (f"📊 总数 {len(all_torrents)}｜⬇️ 下载中 {len(downloading)}｜⬆️ 做种中 {len(uploading)}\n"
                              f"⏸ 插件暂停 {paused_by_plugin}｜❗ 报错 {len(errors)}｜显示无人做种（未复核）{len(zero_seed)}\n"
                              f"💾 剩余空间 {f'{free_gb:.1f}G' if free_gb is not None else '未知'}"
                              f"（阈值控制最小保留 {self._min_disk_space_threshold}G）")
                logger.info(f"【QB种子优化】状态消息: {status_msg}")
                # 状态查询是主动请求，不受通知类型开关限制
                self.post_message(mtype=NotificationType.Manual,
                                  title=f"📊 {self._notify_prefix}｜{downloader_name} 状态", text=status_msg)

            except Exception as e:
                logger.error(f"【QB种子优化】获取状态异常：{str(e)}")
                import traceback
                logger.error(f"【QB种子优化】状态异常详情: {traceback.format_exc()}")
        
        logger.info("【QB种子优化】状态显示完成")

    def get_form(self) -> Tuple[List[dict], Dict[str, Any]]:
        return [
            {
                'component': 'VForm',
                'content': [
                    # 基础配置组
                    {
                        'component': 'VRow',
                        'content': [
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12
                                },
                                'content': [
                                    {
                                        'component': 'VDivider',
                                        'props': {
                                            'text': '基础配置'
                                        }
                                    }
                                ]
                            }
                        ]
                    },
                    {
                        'component': 'VRow',
                        'content': [
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12,
                                    'md': 6
                                },
                                'content': [
                                    {
                                        'component': 'VSwitch',
                                        'props': {
                                            'model': 'enabled',
                                            'label': '启用插件',
                                        }
                                    }
                                ]
                            },
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12,
                                    'md': 6
                                },
                                'content': [
                                    {
                                        'component': 'VSwitch',
                                        'props': {
                                            'model': 'notify',
                                            'label': '发送通知',
                                        }
                                    }
                                ]
                            }
                        ]
                    },
                    {
                        'component': 'VRow',
                        'content': [
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12,
                                    'md': 6
                                },
                                'content': [
                                    {
                                        'component': 'VSelect',
                                        'props': {
                                            'multiple': True,
                                            'chips': True,
                                            'clearable': True,
                                            'model': 'downloaders',
                                            'label': '下载器',
                                            'items': [{"title": config.name, "value": config.name}
                                                      for config in DownloaderHelper().get_configs().values()]
                                        }
                                    }
                                ]
                            },
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12,
                                    'md': 6
                                },
                                'content': [
                                    {
                                        'component': 'VCronField',
                                        'props': {
                                            'model': 'cron',
                                            'label': '执行周期',
                                            'placeholder': '0 */6 * * *'
                                        }
                                    }
                                ]
                            }
                        ]
                    },
                    {
                        'component': 'VRow',
                        'content': [
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12
                                },
                                'content': [
                                    {
                                        'component': 'VSwitch',
                                        'props': {
                                            'model': 'onlyonce',
                                            'label': '立即运行一次',
                                        }
                                    }
                                ]
                            }
                        ]
                    },

                    # 过滤设置
                    {
                        'component': 'VRow',
                        'content': [
                            {
                                'component': 'VCol',
                                'props': {'cols': 12},
                                'content': [
                                    {
                                        'component': 'VAlert',
                                        'props': {
                                            'type': 'secondary',
                                            'variant': 'tonal',
                                            'title': '🔍 过滤设置',
                                            'text': '命中任一条件的种子视为“保持下载”：不会被无人做种、慢速下载、识别不到媒体信息三项清理删除；下载阈值控制不会暂停它们（优先占用空间预算）；优先级优化会把它们置顶。'
                                        }
                                    }
                                ]
                            }
                        ]
                    },
                    {
                        'component': 'VRow',
                        'content': [
                            {
                                'component': 'VCol',
                                'props': {'cols': 12, 'md': 4},
                                'content': [
                                    {
                                        'component': 'VTextarea',
                                        'props': {
                                            'model': 'exclude_keywords',
                                            'label': '🔤 排除关键字',
                                            'rows': 3,
                                            'placeholder': '种子名称包含这些关键字将被跳过（不区分大小写）\n每行一个关键字',
                                            'prepend-inner-icon': 'mdi-text-search'
                                        }
                                    }
                                ]
                            },
                            {
                                'component': 'VCol',
                                'props': {'cols': 12, 'md': 4},
                                'content': [
                                    {
                                        'component': 'VTextarea',
                                        'props': {
                                            'model': 'exclude_categories',
                                            'label': '📂 排除分类',
                                            'rows': 3,
                                            'placeholder': '这些分类的种子将被跳过\n每行一个分类名',
                                            'prepend-inner-icon': 'mdi-folder-outline'
                                        }
                                    }
                                ]
                            },
                            {
                                'component': 'VCol',
                                'props': {'cols': 12, 'md': 4},
                                'content': [
                                    {
                                        'component': 'VTextarea',
                                        'props': {
                                            'model': 'exclude_labels',
                                            'label': '🏷️ 排除标签',
                                            'rows': 3,
                                            'placeholder': '这些标签的种子将被跳过\n每行一个标签名',
                                            'prepend-inner-icon': 'mdi-tag-outline'
                                        }
                                    }
                                ]
                            }
                        ]
                    },

                    # 通知设置
                    {
                        'component': 'VRow',
                        'content': [
                            {
                                'component': 'VCol',
                                'props': {'cols': 12},
                                'content': [
                                    {
                                        'component': 'VDivider',
                                        'props': {'text': '通知设置'}
                                    }
                                ]
                            }
                        ]
                    },
                    {
                        'component': 'VRow',
                        'content': [
                            {
                                'component': 'VCol',
                                'props': {'cols': 12, 'md': 6},
                                'content': [
                                    {
                                        'component': 'VSelect',
                                        'props': {
                                            'multiple': True,
                                            'chips': True,
                                            'clearable': True,
                                            'model': 'notify_types',
                                            'label': '发送哪些通知',
                                            'items': [{"title": v, "value": k} for k, v in self.NOTIFY_KINDS.items()]
                                        }
                                    }
                                ]
                            },
                            {
                                'component': 'VCol',
                                'props': {'cols': 12, 'md': 2},
                                'content': [
                                    {
                                        'component': 'VTextField',
                                        'props': {'model': 'notify_prefix', 'label': '标题前缀', 'placeholder': 'QB优化Plus'}
                                    }
                                ]
                            },
                            {
                                'component': 'VCol',
                                'props': {'cols': 12, 'md': 2},
                                'content': [
                                    {
                                        'component': 'VTextField',
                                        'props': {'model': 'notify_name_length', 'label': '名称最多显示字数',
                                                  'placeholder': '40', 'type': 'number'}
                                    }
                                ]
                            },
                            {
                                'component': 'VCol',
                                'props': {'cols': 12, 'md': 2},
                                'content': [
                                    {
                                        'component': 'VTextField',
                                        'props': {'model': 'notify_max_items', 'label': '每组最多列出',
                                                  'placeholder': '10', 'type': 'number'}
                                    }
                                ]
                            }
                        ]
                    },
                    {
                        'component': 'VRow',
                        'content': [
                            {
                                'component': 'VCol',
                                'props': {'cols': 12, 'md': 5},
                                'content': [
                                    {
                                        'component': 'VTextField',
                                        'props': {
                                            'model': 'notify_summary_title',
                                            'label': '清理汇总标题模板（留空用默认）',
                                            'placeholder': self.DEFAULT_SUMMARY_TITLE
                                        }
                                    }
                                ]
                            },
                            {
                                'component': 'VCol',
                                'props': {'cols': 12, 'md': 7},
                                'content': [
                                    {
                                        'component': 'VTextarea',
                                        'props': {
                                            'model': 'notify_summary_body',
                                            'label': '清理汇总正文模板（留空用默认）',
                                            'rows': 3,
                                            'placeholder': self.DEFAULT_SUMMARY_BODY
                                        }
                                    }
                                ]
                            }
                        ]
                    },
                    {
                        'component': 'VRow',
                        'content': [
                            {
                                'component': 'VCol',
                                'props': {'cols': 12},
                                'content': [
                                    {
                                        'component': 'VAlert',
                                        'props': {
                                            'type': 'info',
                                            'variant': 'tonal',
                                            'density': 'compact',
                                            'text': '模板可用占位符：{前缀} {摘要}（只列出有发生的类别） {替换数} {保留数} {删除数} {整理数} {同步数} {替换列表} {保留列表} {删除列表} {同步列表} {整理列表} {下载器} {剩余空间} {时间}。'
                                                    '列表占位符已包含小标题，没有内容时为空。每条记录包含名称、大小、进度、原因，替换记录还有新资源的站点、做种数和大小。'
                                                    '每轮最多发送一条汇总，状态不变时不会重复提醒。'
                                        }
                                    }
                                ]
                            }
                        ]
                    },

                    # 无人做种任务配置组
                    {
                        'component': 'VRow',
                        'content': [
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12
                                },
                                'content': [
                                    {
                                        'component': 'VDivider',
                                        'props': {
                                            'text': '清理下载中无人做种任务'
                                        }
                                    }
                                ]
                            }
                        ]
                    },
                    {
                        'component': 'VRow',
                        'content': [
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12,
                                    'md': 4
                                },
                                'content': [
                                    {
                                        'component': 'VSwitch',
                                        'props': {
                                            'model': 'enable_zero_seed_clean',
                                            'label': '启用无人做种清理',
                                        }
                                    }
                                ]
                            },
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12,
                                    'md': 4
                                },
                                'content': [
                                    {
                                        'component': 'VTextField',
                                        'props': {
                                            'model': 'zero_seed_threshold',
                                            'label': '做种数阈值',
                                            'placeholder': '0',
                                            'type': 'number'
                                        }
                                    }
                                ]
                            },
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12,
                                    'md': 4
                                },
                                'content': [
                                    {
                                        'component': 'VTextField',
                                        'props': {
                                            'model': 'max_zero_seed_process',
                                            'label': '每次处理数量',
                                            'placeholder': '50',
                                            'type': 'number'
                                        }
                                    }
                                ]
                            }
                        ]
                    },
                    {
                        'component': 'VRow',
                        'content': [
                            {
                                'component': 'VCol',
                                'props': {'cols': 12, 'md': 4},
                                'content': [
                                    {
                                        'component': 'VTextField',
                                        'props': {
                                            'model': 'seed_check_grace_minutes',
                                            'label': '活跃满N分钟后才判定（分钟）',
                                            'placeholder': '30',
                                            'type': 'number'
                                        }
                                    }
                                ]
                            },
                            {
                                'component': 'VCol',
                                'props': {'cols': 12, 'md': 8},
                                'content': [
                                    {
                                        'component': 'VAlert',
                                        'props': {
                                            'type': 'info',
                                            'variant': 'tonal',
                                            'density': 'compact',
                                            'text': 'qB 列表中的做种数在 tracker 返回数据前会显示为 0（刚添加、刚恢复、排队中的种子都是如此）。'
                                                    '插件会再核对：实际活跃时长、当前下载速度、已连接做种者、可用分布以及 tracker 返回的做种数，'
                                                    'tracker 未返回数据的种子会触发重新汇报，下次运行再判断。'
                                        }
                                    }
                                ]
                            }
                        ]
                    },
                    
                    # 慢速下载任务配置组
                    {
                        'component': 'VRow',
                        'content': [
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12
                                },
                                'content': [
                                    {
                                        'component': 'VDivider',
                                        'props': {
                                            'text': '清理慢速下载任务'
                                        }
                                    }
                                ]
                            }
                        ]
                    },
                    {
                        'component': 'VRow',
                        'content': [
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12,
                                    'md': 4
                                },
                                'content': [
                                    {
                                        'component': 'VSwitch',
                                        'props': {
                                            'model': 'enable_timeout_clean',
                                            'label': '启用慢速下载清理',
                                        }
                                    }
                                ]
                            },
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12,
                                    'md': 4
                                },
                                'content': [
                                    {
                                        'component': 'VTextField',
                                        'props': {
                                            'model': 'timeout_hours',
                                            'label': '实际活跃&&预计剩余时长超出（小时）',
                                            'placeholder': '24',
                                            'type': 'number'
                                        }
                                    }
                                ]
                            },
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12,
                                    'md': 4
                                },
                                'content': [
                                    {
                                        'component': 'VTextField',
                                        'props': {
                                            'model': 'max_timeout_process',
                                            'label': '每次处理数量',
                                            'placeholder': '50',
                                            'type': 'number'
                                        }
                                    }
                                ]
                            }
                        ]
                    },
                    
                    # 识别不到媒体信息任务配置组
                    {
                        'component': 'VRow',
                        'content': [
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12
                                },
                                'content': [
                                    {
                                        'component': 'VDivider',
                                        'props': {
                                            'text': '清理识别不到媒体信息任务'
                                        }
                                    }
                                ]
                            }
                        ]
                    },
                    {
                        'component': 'VRow',
                        'content': [
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12,
                                    'md': 6
                                },
                                'content': [
                                    {
                                        'component': 'VSwitch',
                                        'props': {
                                            'model': 'enable_unrecognized_clean',
                                            'label': '启用识别不到媒体信息清理',
                                        }
                                    }
                                ]
                            },
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12,
                                    'md': 6
                                },
                                'content': [
                                    {
                                        'component': 'VTextField',
                                        'props': {
                                            'model': 'max_unrecognized_process',
                                            'label': '每次处理数量',
                                            'placeholder': '50',
                                            'type': 'number'
                                        }
                                    }
                                ]
                            }
                        ]
                    },

                    # 清理已整理移走的种子
                    {
                        'component': 'VRow',
                        'content': [
                            {
                                'component': 'VCol',
                                'props': {'cols': 12},
                                'content': [
                                    {
                                        'component': 'VDivider',
                                        'props': {'text': '处理被整理移走的文件（目录监控）'}
                                    }
                                ]
                            }
                        ]
                    },
                    {
                        'component': 'VRow',
                        'content': [
                            {
                                'component': 'VCol',
                                'props': {'cols': 12, 'md': 4},
                                'content': [
                                    {
                                        'component': 'VSwitch',
                                        'props': {'model': 'enable_moved_clean', 'label': '处理被MP整理移走的文件'}
                                    }
                                ]
                            },
                            {
                                'component': 'VCol',
                                'props': {'cols': 12, 'md': 4},
                                'content': [
                                    {
                                        'component': 'VTextField',
                                        'props': {
                                            'model': 'moved_clean_delay_minutes',
                                            'label': '下载完成满N分钟后清理',
                                            'placeholder': '30',
                                            'type': 'number'
                                        }
                                    }
                                ]
                            },
                            {
                                'component': 'VCol',
                                'props': {'cols': 12, 'md': 4},
                                'content': [
                                    {
                                        'component': 'VAlert',
                                        'props': {
                                            'type': 'info',
                                            'variant': 'tonal',
                                            'density': 'compact',
                                            'text': '适配 MP 目录监控+移动：下载中的季包有单集被移走时，把这些文件设为不下载并重新校验一次，'
                                                    '避免 qB 读不到文件而报错，其余集数继续下载；需要换资源时只下载还没整理的集数；'
                                                    '已完成且已移走的种子只删除种子记录，不删除任何文件。'
                                        }
                                    }
                                ]
                            }
                        ]
                    },

                    # 错误种子处理
                    {
                        'component': 'VRow',
                        'content': [
                            {
                                'component': 'VCol',
                                'props': {'cols': 12},
                                'content': [
                                    {
                                        'component': 'VDivider',
                                        'props': {'text': '处理报错的种子'}
                                    }
                                ]
                            }
                        ]
                    },
                    {
                        'component': 'VRow',
                        'content': [
                            {
                                'component': 'VCol',
                                'props': {'cols': 12, 'md': 4},
                                'content': [
                                    {
                                        'component': 'VSwitch',
                                        'props': {'model': 'enable_error_handle', 'label': '启用报错种子处理'}
                                    }
                                ]
                            },
                            {
                                'component': 'VCol',
                                'props': {'cols': 12, 'md': 4},
                                'content': [
                                    {
                                        'component': 'VTextField',
                                        'props': {
                                            'model': 'error_timeout_hours',
                                            'label': '报错超过N小时删除并重新下载（0为不删除）',
                                            'placeholder': '24',
                                            'type': 'number'
                                        }
                                    }
                                ]
                            },
                            {
                                'component': 'VCol',
                                'props': {'cols': 12, 'md': 4},
                                'content': [
                                    {
                                        'component': 'VAlert',
                                        'props': {
                                            'type': 'info',
                                            'variant': 'tonal',
                                            'density': 'compact',
                                            'text': '每轮自动重试（文件丢失的先重新校验），磁盘空间不足时不重试；重试3次仍报错会通知。'
                                                    '已完成的做种种子和命中过滤设置的种子只重试不删除。'
                                        }
                                    }
                                ]
                            }
                        ]
                    },
                    
                    # 综合评分优先级配置组
                    {
                        'component': 'VRow',
                        'content': [
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12
                                },
                                'content': [
                                    {
                                        'component': 'VDivider',
                                        'props': {
                                            'text': '优先级优化'
                                        }
                                    }
                                ]
                            }
                        ]
                    },
                    {
                        'component': 'VRow',
                        'content': [
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12,
                                    'md': 4
                                },
                                'content': [
                                    {
                                        'component': 'VSwitch',
                                        'props': {
                                            'model': 'enable_score_priority',
                                            'label': '启用优先级优化',
                                        }
                                    }
                                ]
                            },
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12,
                                    'md': 4
                                },
                                'content': [
                                    {
                                        'component': 'VTextField',
                                        'props': {
                                            'model': 'min_score_threshold',
                                            'label': '最低综合评分阈值',
                                            'placeholder': '1.0',
                                            'type': 'number',
                                            'step': 0.1
                                        }
                                    }
                                ]
                            },
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12,
                                    'md': 4
                                },
                                'content': [
                                    {
                                        'component': 'VTextField',
                                        'props': {
                                            'model': 'max_priority_process',
                                            'label': '每次处理数量',
                                            'placeholder': '100',
                                            'type': 'number'
                                        }
                                    }
                                ]
                            }
                        ]
                    },
                    {
                        'component': 'VRow',
                        'content': [
                            {
                                'component': 'VCol',
                                'props': {'cols': 12, 'md': 4},
                                'content': [
                                    {
                                        'component': 'VTextField',
                                        'props': {
                                            'model': 'probe_wait_seconds',
                                            'label': '排队种子探测最长等待（秒）',
                                            'placeholder': '30',
                                            'type': 'number'
                                        }
                                    }
                                ]
                            },
                            {
                                'component': 'VCol',
                                'props': {'cols': 12, 'md': 8},
                                'content': [
                                    {
                                        'component': 'VAlert',
                                        'props': {
                                            'type': 'info',
                                            'variant': 'tonal',
                                            'density': 'compact',
                                            'text': '排队中的种子不会向 tracker 汇报，拿不到做种数。插件会临时强制启动一小批、主动重新汇报，'
                                                    '拿到 tracker 数据后立即取消强制启动；结果缓存6小时，避免重复探测。'
                                        }
                                    }
                                ]
                            }
                        ]
                    },
                    {
                        'component': 'VRow',
                        'content': [
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12,
                                    'md': 6
                                },
                                'content': [
                                    {
                                        'component': 'VTextField',
                                        'props': {
                                            'model': 'speed_weight',
                                            'label': '下载速度权重',
                                            'placeholder': '1.0',
                                            'type': 'number',
                                            'step': 0.1
                                        }
                                    }
                                ]
                            },
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12,
                                    'md': 6
                                },
                                'content': [
                                    {
                                        'component': 'VTextField',
                                        'props': {
                                            'model': 'seeder_weight',
                                            'label': '做种数权重',
                                            'placeholder': '0.5',
                                            'type': 'number',
                                            'step': 0.1
                                        }
                                    }
                                ]
                            }
                        ]
                    },
                    
                    # 磁盘空间和I/O监控配置组
                    {
                        'component': 'VRow',
                        'content': [
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12
                                },
                                'content': [
                                    {
                                        'component': 'VDivider',
                                        'props': {
                                            'text': '磁盘空间和I/O监控'
                                        }
                                    }
                                ]
                            }
                        ]
                    },
                    {
                        'component': 'VRow',
                        'content': [
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12,
                                    'md': 4
                                },
                                'content': [
                                    {
                                        'component': 'VSwitch',
                                        'props': {
                                            'model': 'enable_disk_monitor',
                                            'label': '启用磁盘监控',
                                        }
                                    }
                                ]
                            },
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12,
                                    'md': 4
                                },
                                'content': [
                                    {
                                        'component': 'VTextField',
                                        'props': {
                                            'model': 'disk_space_threshold',
                                            'label': '磁盘空间阈值（GB）',
                                            'placeholder': '10',
                                            'type': 'number'
                                        }
                                    }
                                ]
                            },
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12,
                                    'md': 4
                                },
                                'content': [
                                    {
                                        'component': 'VTextField',
                                        'props': {
                                            'model': 'speed_limit_mbps',
                                            'label': '限制下载速度（MB/s）',
                                            'placeholder': '1',
                                            'type': 'number',
                                            'step': 0.1
                                        }
                                    }
                                ]
                            }
                        ]
                    },
                    {
                        'component': 'VRow',
                        'content': [
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12,
                                    'md': 6
                                },
                                'content': [
                                    {
                                        'component': 'VTextField',
                                        'props': {
                                            'model': 'monitor_duration',
                                            'label': '持续监测时长（秒）',
                                            'placeholder': '30',
                                            'type': 'number',
                                            'min': 10,
                                            'max': 300
                                        }
                                    }
                                ]
                            },
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12,
                                    'md': 6
                                },
                                'content': [
                                    {
                                        'component': 'VTextField',
                                        'props': {
                                            'model': 'monitor_interval',
                                            'label': '监测间隔（秒）',
                                            'placeholder': '3',
                                            'type': 'number',
                                            'min': 1,
                                            'max': 30
                                        }
                                    }
                                ]
                            }
                        ]
                    },
                    {
                        'component': 'VRow',
                        'content': [
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12,
                                    'md': 6
                                },
                                'content': [
                                    {
                                        'component': 'VTextField',
                                        'props': {
                                            'model': 'io_cache_threshold',
                                            'label': 'I/O缓存阈值（%）',
                                            'placeholder': '70',
                                            'type': 'number'
                                        }
                                    }
                                ]
                            },
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12,
                                    'md': 6
                                },
                                'content': [
                                    {
                                        'component': 'VTextField',
                                        'props': {
                                            'model': 'io_queue_threshold',
                                            'label': 'I/O队列阈值',
                                            'placeholder': '8000',
                                            'type': 'number'
                                        }
                                    }
                                ]
                            }
                        ]
                    },
                    
                    # 下载阈值控制配置组
                    {
                        'component': 'VRow',
                        'content': [
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12
                                },
                                'content': [
                                    {
                                        'component': 'VDivider',
                                        'props': {
                                            'text': '下载阈值控制'
                                        }
                                    }
                                ]
                            }
                        ]
                    },
                    {
                        'component': 'VRow',
                        'content': [
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12,
                                    'md': 6
                                },
                                'content': [
                                    {
                                        'component': 'VSwitch',
                                        'props': {
                                            'model': 'enable_download_threshold',
                                            'label': '启用下载阈值控制',
                                        }
                                    }
                                ]
                            },
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12,
                                    'md': 6
                                },
                                'content': [
                                    {
                                        'component': 'VTextField',
                                        'props': {
                                            'model': 'min_disk_space_threshold',
                                            'label': '最小磁盘空间阈值（GB）',
                                            'placeholder': '50',
                                            'type': 'number'
                                        }
                                    }
                                ]
                            }
                        ]
                    },
                    {
                        'component': 'VRow',
                        'content': [
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12,
                                },
                                'content': [
                                    {
                                        'component': 'VAlert',
                                        'props': {
                                            'type': 'info',
                                            'variant': 'tonal',
                                            'text': '📊 下载阈值控制：预算 = 磁盘剩余空间 − 最小阈值。在预算内选出总下载速度最大的一组种子同时下载（背包算法，按种子还需下载的大小计算，只算要下载的文件），其余暂停；空间释放后按同一规则恢复。被暂停的种子每等1小时加分，保证慢种子最终也能下载完；正在下载的种子有加权，避免来回切换。单个种子超过整个预算时会通知。只恢复本插件暂停的种子。'
                                        }
                                    }
                                ]
                            }
                        ]
                    },
                    
                    # 其他配置组
                    {
                        'component': 'VRow',
                        'content': [
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12
                                },
                                'content': [
                                    {
                                        'component': 'VDivider',
                                        'props': {
                                            'text': '其他配置'
                                        }
                                    }
                                ]
                            }
                        ]
                    },
                    {
                        'component': 'VRow',
                        'content': [
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12,
                                    'md': 6
                                },
                                'content': [
                                    {
                                        'component': 'VSwitch',
                                        'props': {
                                            'model': 'enable_auto_redownload',
                                            'label': '启用自动重新下载',
                                        }
                                    }
                                ]
                            }
                        ]
                    },
                    {
                        'component': 'VRow',
                        'content': [
                            {
                                'component': 'VCol',
                                'props': {'cols': 12, 'md': 4},
                                'content': [
                                    {
                                        'component': 'VTextField',
                                        'props': {
                                            'model': 'redownload_min_seeders',
                                            'label': '替代资源最少做种数',
                                            'placeholder': '3',
                                            'type': 'number'
                                        }
                                    }
                                ]
                            },
                            {
                                'component': 'VCol',
                                'props': {'cols': 12, 'md': 4},
                                'content': [
                                    {
                                        'component': 'VTextField',
                                        'props': {
                                            'model': 'redownload_size_tolerance',
                                            'label': '大小允许偏差（%，0为不限制）',
                                            'placeholder': '50',
                                            'type': 'number'
                                        }
                                    }
                                ]
                            },
                            {
                                'component': 'VCol',
                                'props': {'cols': 12, 'md': 4},
                                'content': [
                                    {
                                        'component': 'VTextField',
                                        'props': {
                                            'model': 'redownload_max_attempts',
                                            'label': '同一资源最多重新下载次数',
                                            'placeholder': '3',
                                            'type': 'number'
                                        }
                                    }
                                ]
                            }
                        ]
                    },
                    {
                        'component': 'VRow',
                        'content': [
                            {
                                'component': 'VCol',
                                'props': {'cols': 12},
                                'content': [
                                    {
                                        'component': 'VAlert',
                                        'props': {
                                            'type': 'info',
                                            'variant': 'tonal',
                                            'density': 'compact',
                                            'text': '重新下载优先用 MoviePilot 下载历史中的 TMDB ID 识别，按媒体信息精确搜索，识别失败才按片名搜索；'
                                                    '候选资源需季集一致、大小相近、做种数达标，按做种数从高到低选择，下载到原下载器和原目录；仍搜不到时用AI给出的中文名/原名再搜。'
                                                    '先成功提交替代资源再删除原种子，找不到替代资源时保留原种子并通知，6小时后再搜。'
                                        }
                                    }
                                ]
                            }
                        ]
                    },

                    # AI 辅助识别（可选）
                    {
                        'component': 'VRow',
                        'content': [
                            {
                                'component': 'VCol',
                                'props': {'cols': 12},
                                'content': [
                                    {
                                        'component': 'VDivider',
                                        'props': {'text': 'AI辅助识别（可选）'}
                                    }
                                ]
                            }
                        ]
                    },
                    {
                        'component': 'VRow',
                        'content': [
                            {
                                'component': 'VCol',
                                'props': {'cols': 12, 'md': 3},
                                'content': [
                                    {
                                        'component': 'VSwitch',
                                        'props': {'model': 'ai_enabled', 'label': '启用AI辅助识别'}
                                    }
                                ]
                            },
                            {
                                'component': 'VCol',
                                'props': {'cols': 12, 'md': 3},
                                'content': [
                                    {
                                        'component': 'VTextField',
                                        'props': {'model': 'ai_model', 'label': '模型（留空用系统设置）'}
                                    }
                                ]
                            },
                            {
                                'component': 'VCol',
                                'props': {'cols': 12, 'md': 3},
                                'content': [
                                    {
                                        'component': 'VTextField',
                                        'props': {'model': 'ai_base_url', 'label': 'API地址（留空用系统设置）'}
                                    }
                                ]
                            },
                            {
                                'component': 'VCol',
                                'props': {'cols': 12, 'md': 3},
                                'content': [
                                    {
                                        'component': 'VTextField',
                                        'props': {'model': 'ai_api_key', 'label': 'API Key（留空用系统设置）', 'type': 'password'}
                                    }
                                ]
                            }
                        ]
                    },
                    {
                        'component': 'VRow',
                        'content': [
                            {
                                'component': 'VCol',
                                'props': {'cols': 12},
                                'content': [
                                    {
                                        'component': 'VAlert',
                                        'props': {
                                            'type': 'info',
                                            'variant': 'tonal',
                                            'density': 'compact',
                                            'text': '仅在 MoviePilot 和 TMDB 都识别不出种子时调用：AI 根据种子名推测片名、年份、类型，再交给 TMDB 核对，'
                                                    '核对成功才采用（避免误删识别不到的种子、帮助重新下载时找到正确资源）。AI 不参与任何删除/暂停决定。'
                                                    '默认使用 MoviePilot 系统的 AI 设置；每轮最多调用10次，结果按种子名缓存7天。'
                                        }
                                    }
                                ]
                            }
                        ]
                    },
                    


                    
                    # 搜索站点配置组
                    {
                        'component': 'VRow',
                        'content': [
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12
                                },
                                'content': [
                                    {
                                        'component': 'VDivider',
                                        'props': {
                                            'text': '搜索站点配置'
                                        }
                                    }
                                ]
                            }
                        ]
                    },
                    {
                        'component': 'VRow',
                        'content': [
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12
                                },
                                'content': [
                                    {
                                        'component': 'VSelect',
                                        'props': {
                                            'multiple': True,
                                            'chips': True,
                                            'clearable': True,
                                            'model': 'search_sites',
                                            'label': '重新下载时用于搜索的站点',
                                            'items': [{"title": site.name, "value": site.id}
                                                      for site in SiteOper().list_order_by_pri()]
                                        }
                                    }
                                ]
                            }
                        ]
                    },
                    
                    # 功能说明
                    {
                        'component': 'VRow',
                        'content': [
                            {
                                'component': 'VCol',
                                'props': {
                                    'cols': 12,
                                },
                                'content': [
                                    {
                                        'component': 'VAlert',
                                        'props': {
                                            'type': 'info',
                                            'variant': 'tonal',
                                            'text': '📊 综合评分算法：评分 = 下载速度(MB/s) × 速度权重 + 做种数 × 做种数权重'
                                        }
                                    }
                                ]
                            }
                        ]
                    }
                ]
            }
        ], {
            "enabled": False,
            "notify": True,
            "onlyonce": False,
            "cron": "0 */6 * * *",
            "downloaders": [],
            "search_sites": [],
            "enable_zero_seed_clean": True,
            "enable_priority_boost": True,
            "enable_timeout_clean": True,
            "enable_unrecognized_clean": False,
            "enable_auto_redownload": True,
            "zero_seed_threshold": 0,
            "timeout_hours": 24,
            "max_download_slots": 5,
            "max_zero_seed_process": 50,
            "max_timeout_process": 50,
            "max_unrecognized_process": 50,
            "max_priority_process": 100,
            # 综合评分配置
            "enable_score_priority": True,
            "speed_weight": 1.0,
            "seeder_weight": 0.5,
            "min_score_threshold": 1.0,
            # 磁盘空间和I/O监控配置
            "enable_disk_monitor": False,
            "disk_space_threshold": 10,
            "io_cache_threshold": 70,
            "io_queue_threshold": 8000,
            "speed_limit_mbps": 1,
            "monitor_duration": 30,
            "monitor_interval": 3,
            # 下载阈值控制配置
            "enable_download_threshold": False,
            "min_disk_space_threshold": 50,
            # 过滤设置
            "exclude_keywords": "",
            "exclude_categories": "",
            "exclude_labels": "",
            # 做种数据复核与重新下载
            "seed_check_grace_minutes": 30,
            "probe_wait_seconds": 30,
            "redownload_min_seeders": 3,
            "redownload_size_tolerance": 50,
            "redownload_max_attempts": 3,
            # AI 辅助识别
            "ai_enabled": False,
            # 通知设置
            "notify_types": ['summary', 'threshold', 'limit', 'error', 'oversize'],
            "notify_prefix": "QB优化Plus",
            "notify_name_length": 40,
            "notify_max_items": 10,
            "notify_summary_title": "",
            "notify_summary_body": "",
            # 清理已整理移走的种子
            "enable_moved_clean": True,
            "moved_clean_delay_minutes": 30,
            # 错误种子处理
            "enable_error_handle": True,
            "error_timeout_hours": 24,
            "ai_model": "",
            "ai_base_url": "",
            "ai_api_key": "",
        }

    def get_page(self) -> List[dict]:
        pass

    def stop_service(self):
        """
        退出插件
        """
        logger.info("【QB种子优化】开始停止服务...")
        try:
            if self._scheduler:
                logger.info("【QB种子优化】移除所有调度任务")
                self._scheduler.remove_all_jobs()
                if self._scheduler.running:
                    logger.info("【QB种子优化】停止调度器")
                    self._event.set()
                    self._scheduler.shutdown()
                    self._event.clear()
                self._scheduler = None
                logger.info("【QB种子优化】调度器已停止")
            else:
                logger.info("【QB种子优化】没有运行中的调度器")
        except Exception as e:
            logger.error(f"【QB种子优化】退出插件失败：{str(e)}")
            import traceback
            logger.error(f"【QB种子优化】退出异常详情: {traceback.format_exc()}")
        logger.info("【QB种子优化】服务停止完成")
