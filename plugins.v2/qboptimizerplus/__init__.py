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
    plugin_version = "1.0"
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

    # qB 中表示“无限”的 ETA 值
    QB_ETA_INFINITY = 8640000
    PROBE_CACHE_TTL = 6 * 3600

    def init_plugin(self, config: dict = None):
        logger.info("【QB种子优化】开始初始化插件...")
        self._removed_hashes = set()
        self._recognized_cache = set()
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
                                
                                # 发送通知
                                if self._notify:
                                    notification_title = "【QB种子优化】磁盘空间不足，已限制下载速度"
                                    notification_text = f"磁盘剩余空间: {free_space_gb:.2f}GB\n"
                                    notification_text += f"空间阈值: {self._disk_space_threshold}GB\n"
                                    notification_text += f"\n已自动限制下载速度为: {self._speed_limit_mbps}MB/s\n"
                                    notification_text += f"已停止执行优化任务，避免进一步占用磁盘空间"
                                    
                                    self.post_message(
                                        mtype=NotificationType.Manual,
                                        title=notification_title,
                                        text=notification_text
                                    )
                                return True  # 已限速，停止执行任务
                            else:
                                logger.error(f"【QB种子优化】下载速度限制失败，跳过所有优化任务")
                                return True  # 限速失败，跳过任务
                        else:
                            # 已限速，跳过所有优化任务
                            logger.warning(f"【QB种子优化】磁盘空间不足且已限速，跳过所有优化任务")
                            
                            # 发送通知
                            if self._notify:
                                notification_title = "【QB种子优化】磁盘空间不足，已跳过所有优化任务"
                                notification_text = f"磁盘剩余空间: {free_space_gb:.2f}GB\n"
                                notification_text += f"空间阈值: {self._disk_space_threshold}GB\n"
                                notification_text += f"当前已处于限速状态: {current_download_limit}KB/s\n"
                                notification_text += f"\n为避免进一步占用磁盘空间，已跳过所有优化任务"
                                
                                self.post_message(
                                    mtype=NotificationType.Manual,
                                    title=notification_title,
                                    text=notification_text
                                )
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
                                
                                # 发送通知
                                if self._notify:
                                    notification_title = "【QB种子优化】磁盘空间已恢复，已解除下载速度限制"
                                    notification_text = f"磁盘剩余空间: {free_space_gb:.2f}GB\n"
                                    notification_text += f"空间阈值: {self._disk_space_threshold}GB\n"
                                    notification_text += f"之前限速值: {current_download_limit}KB/s\n"
                                    notification_text += f"\n已自动解除下载速度限制，恢复正常下载速度"
                                    
                                    self.post_message(
                                        mtype=NotificationType.Manual,
                                        title=notification_title,
                                        text=notification_text
                                    )
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
        total_timeout_removed = 0
        total_unrecognized_removed = 0
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
                    zero_seed_removed, zero_seed_failed = self._clean_zero_seed_torrents(
                        downloader_obj, self._alive(all_torrents), downloader_name)
                    timeout_removed, timeout_failed = self._clean_timeout_torrents(
                        downloader_obj, self._alive(all_torrents), downloader_name)
                    unrecognized_removed = self._clean_unrecognized_torrents(
                        downloader_obj, self._alive(all_torrents), downloader_name)
                    priority_boosted = self._boost_priority_torrents(
                        downloader_obj, self._alive(all_torrents), downloader_name)

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
                    
                    # 收集重新下载失败信息
                    all_failed_torrents.extend(zero_seed_failed)
                    all_failed_torrents.extend(timeout_failed)
                    
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
        logger.info(f"  - 重新下载失败: {len(all_failed_torrents)}个")
        
        # 输出详细总结信息
        if total_zero_seed_removed > 0 or total_timeout_removed > 0 or total_unrecognized_removed > 0:
            logger.info(f"【QB种子优化】本次清理总结:")
            logger.info(f"  清理种子总数: {total_zero_seed_removed + total_timeout_removed + total_unrecognized_removed}个")
            logger.info(f"  - 清理下载中无人做种: {total_zero_seed_removed}个")
            logger.info(f"  - 清理慢速下载: {total_timeout_removed}个")
            logger.info(f"  - 清理识别不到媒体信息: {total_unrecognized_removed}个")
            
            if all_failed_torrents:
                logger.warning(f"【QB种子优化】重新下载失败总结: 共{len(all_failed_torrents)}个种子未找到资源")
                for i, failed_torrent in enumerate(all_failed_torrents, 1):
                    logger.warning(f"  {i}. {failed_torrent['name']}")
                    logger.warning(f"     - HASH: {failed_torrent['hash']}")
                    logger.warning(f"     - 大小: {failed_torrent['size']}")
                    logger.warning(f"     - 原因: {failed_torrent['reason']}")
                
                # 发送通知
                if self._notify:
                    summary_message = f"【QB种子优化完成】\n"
                    summary_message += f"本次清理种子: {total_zero_seed_removed + total_timeout_removed + total_unrecognized_removed}个\n"
                    summary_message += f"  - 清理下载中无人做种: {total_zero_seed_removed}个\n"
                    summary_message += f"  - 清理慢速下载: {total_timeout_removed}个\n"
                    summary_message += f"  - 清理识别不到媒体信息: {total_unrecognized_removed}个\n"
                    summary_message += f"重新下载失败: {len(all_failed_torrents)}个\n\n"
                    summary_message += "失败种子列表:\n"
                    for i, failed_torrent in enumerate(all_failed_torrents, 1):
                        summary_message += f"{i}. {failed_torrent['name']}\n"
                        summary_message += f"   HASH: {failed_torrent['hash']}\n"
                        summary_message += f"   大小: {failed_torrent['size']}\n"
                        summary_message += f"   原因: {failed_torrent['reason']}\n\n"
                    
                    logger.info(f"【QB种子优化】发送总结通知: 清理{total_zero_seed_removed + total_timeout_removed + total_unrecognized_removed}个，失败{len(all_failed_torrents)}个")
                    self.post_message(
                        mtype=NotificationType.Manual,
                        title=f"【QB种子优化】清理完成 - {len(all_failed_torrents)}个种子未找到资源",
                        text=summary_message
                    )
            else:
                logger.info(f"【QB种子优化】重新下载成功总结: 清理的{total_zero_seed_removed + total_timeout_removed}个种子全部重新下载成功")
                if self._notify:
                    logger.info(f"【QB种子优化】清理{total_zero_seed_removed + total_timeout_removed + total_unrecognized_removed}个种子，全部重新下载成功，无需发送通知")
        else:
            logger.info(f"【QB种子优化】本次无清理操作，无需发送通知")

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
        reannounce_hashes = []
        for torrent in candidates:
            verdict, detail = self._verify_no_seeders(downloader_obj, torrent)
            if verdict == 'dead':
                logger.info(f"{prefix}确认无人做种（{detail}）: {torrent.name}")
                zero_seed_torrents.append(torrent)
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
            torrent_info = self._snapshot_torrent(torrent)
            if not self._delete_torrent(downloader_obj, torrent, torrents, prefix):
                continue
            removed += 1
            failed = self._maybe_redownload(torrent_info, '无人做种', prefix)
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

    def _maybe_redownload(self, torrent_info: dict, reason: str, prefix: str) -> Optional[dict]:
        """按配置重新下载，失败时返回用于通知的失败记录"""
        if not self._enable_auto_redownload:
            logger.info(f"{prefix}自动重新下载已禁用: {torrent_info['name']}")
            return None
        if not self._search_sites:
            logger.info(f"{prefix}未配置搜索站点，跳过重新下载: {torrent_info['name']}")
            return None
        ok, fail_reason = self._re_download_torrent(torrent_info)
        if ok:
            return None
        return {
            'name': torrent_info['name'],
            'hash': torrent_info['hash'],
            'size': StringUtils.str_filesize(torrent_info['size']),
            'category': torrent_info.get('category') or 'N/A',
            'tags': torrent_info.get('tags') or 'N/A',
            'tracker': torrent_info.get('tracker') or 'N/A',
            'reason': f"{reason}；{fail_reason}"
        }

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
            torrent_info = self._snapshot_torrent(torrent)
            if not self._delete_torrent(downloader_obj, torrent, torrents, prefix):
                continue
            removed += 1
            failed = self._maybe_redownload(
                torrent_info, f'慢速下载：活跃{active_seconds / 3600:.1f}小时，预计剩余{remaining_text}', prefix)
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
            if mediainfo:
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
        return removed

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
                    
                    # 发送通知（不包含磁盘空间信息，因为已在优化前检测过）
                    if self._notify and notification_data:
                        notification_title = "【QB种子优化】I/O资源不足，已限制下载速度"
                        notification_text = f"持续监测{notification_data['monitor_count']}次，发现以下I/O问题:\n"
                        if notification_data['cache_issues'] > 0:
                            notification_text += f"• I/O缓存过高: {notification_data['cache_issues']}/{notification_data['monitor_count']}次 (平均: {notification_data['avg_cache_overload']:.1f}%, 阈值: {self._io_cache_threshold}%)\n"
                        if notification_data['queue_issues'] > 0:
                            notification_text += f"• I/O队列过高: {notification_data['queue_issues']}/{notification_data['monitor_count']}次 (平均: {notification_data['avg_io_jobs']:.0f}, 阈值: {self._io_queue_threshold})\n"
                        notification_text += f"\n已自动限制下载速度为: {self._speed_limit_mbps}MB/s"
                        
                        self.post_message(
                            mtype=NotificationType.Manual,
                            title=notification_title,
                            text=notification_text
                        )
                        logger.info(f"【功能4-磁盘监控】已发送资源不足通知")
                    
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
                    
                    # 发送通知（不包含磁盘空间信息，因为已在优化前检测过）
                    if self._notify and notification_data:
                        notification_title = "【QB种子优化】I/O资源已恢复，已取消下载速度限制"
                        notification_text = f"持续监测{notification_data['monitor_count']}次，I/O资源已恢复正常:\n"
                        notification_text += f"• I/O缓存使用率: {notification_data['avg_cache_overload']:.1f}% (阈值: {self._io_cache_threshold}%) ✓\n"
                        notification_text += f"• 队列I/O任务: {notification_data['avg_io_jobs']:.0f} (阈值: {self._io_queue_threshold}) ✓\n"
                        notification_text += f"\n已自动取消下载速度限制"
                        
                        self.post_message(
                            mtype=NotificationType.Manual,
                            title=notification_title,
                            text=notification_text
                        )
                        logger.info(f"【功能4-磁盘监控】已发送资源恢复通知")
                    
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
        if not self._enable_download_threshold:
            logger.info("【功能5-下载阈值控制】下载阈值控制功能已禁用，跳过")
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
            logger.info(f"【功能5-下载阈值控制】首次建立暂停记录，接管{len(stored)}个当前暂停的未完成种子")
        paused_by_plugin = set(stored)
        try:
            return self._manage_download_threshold_core(downloader_obj, torrents, downloader_name, paused_by_plugin)
        finally:
            try:
                self.save_data('threshold_paused', list(paused_by_plugin))
            except Exception as e:
                logger.debug(f"【功能5-下载阈值控制】保存暂停记录失败: {e}")

    def _manage_download_threshold_core(self, downloader_obj, torrents, downloader_name, paused_by_plugin: set):
        """
        下载阈值控制管理：如果当前下载中的种子总大小超过阈值，直接暂停任务保持不超过阈值
        1. 计算所有下载中种子的总大小（只计算需要下载的文件，优先级不为0）
        2. 如果总大小超过阈值，优先暂停当前下载速度慢、下载进度低的种子，直到总大小不超过阈值
        3. 如果总大小未超过阈值，按下载速度从快到慢恢复暂停的种子，但不能超过阈值
        """
        logger.info(f"【功能5-下载阈值控制】开始下载阈值控制管理，功能开关: {self._enable_download_threshold}")
        
        if not self._enable_download_threshold:
            logger.info("【功能5-下载阈值控制】下载阈值控制功能已禁用，跳过")
            return False
        
        try:
            # 获取qBittorrent客户端实例
            qb_client = downloader_obj.qbc
            if not qb_client:
                logger.error("【功能5-下载阈值控制】无法获取qBittorrent客户端")
                return False
            
            # 获取当前磁盘空间
            try:
                response = qb_client._request(
                    http_method='POST',
                    api_namespace='sync',
                    api_method='maindata',
                    data={'rid': 0}
                )
                
                try:
                    response_data = response.json()
                except:
                    import json
                    response_data = json.loads(response.text)
                
                if 'server_state' not in response_data:
                    logger.warning(f"【功能5-下载阈值控制】无法获取服务器状态信息")
                    return False
                
                server_state = response_data['server_state']
                free_space_gb = server_state.get('free_space_on_disk', 0) / (1024**3)  # 转换为GB
                
                logger.info(f"【功能5-下载阈值控制】当前磁盘剩余空间: {free_space_gb:.2f}GB, 最小阈值: {self._min_disk_space_threshold}GB")
                
            except Exception as e:
                logger.error(f"【功能5-下载阈值控制】获取磁盘空间失败: {str(e)}")
                return False
            
            # 只恢复本插件暂停过的种子，不动用户手动暂停的种子；已不存在的种子从记录中清除
            paused_by_plugin.intersection_update({t.hash for t in torrents})

            # 筛选下载中的种子和暂停的种子
            downloading_torrents = []  # 正在下载的种子
            paused_torrents = []      # 本插件暂停的种子
            
            # 用于调试：统计所有状态
            state_counter = {}
            
            for torrent in torrents:
                progress = getattr(torrent, 'progress', 0)
                if progress >= 1.0:
                    continue  # 跳过已完成的种子
                
                state_name = getattr(torrent, 'state', '') or ''
                state_lower = state_name.lower()
                
                # 统计状态用于调试
                state_counter[state_name] = state_counter.get(state_name, 0) + 1
                
                # 首先检测暂停状态（优先级最高，避免被误判为下载中）
                # stoppedDL = 暂停下载, stoppedUP = 暂停上传, paused = 暂停
                is_paused = (state_lower == 'stoppeddl' or 
                           state_lower == 'stoppedup' or
                           state_lower == 'pauseddl' or
                           state_lower == 'pausedup' or
                           state_lower == 'paused' or
                           'stopped' in state_lower or
                           'paused' in state_lower)
                
                if is_paused:
                    if torrent.hash in paused_by_plugin:
                        paused_torrents.append(torrent)
                    continue
                
                # 检测下载中的种子：优先使用 state_enum（更可靠）
                is_downloading = False
                try:
                    if hasattr(torrent, 'state_enum'):
                        is_downloading = torrent.state_enum.is_downloading
                except Exception:
                    pass
                
                # 如果 state_enum 不可用，使用字符串匹配
                # 注意：排除 stoppedDL 等暂停状态
                if not is_downloading and not is_paused:
                    is_downloading = (state_lower == 'downloading' or 
                                    state_lower == 'stalleddl' or 
                                    state_lower == 'metadl' or
                                    state_lower == 'queueddl')
                
                # 检测做种中的种子
                is_uploading = False
                try:
                    if hasattr(torrent, 'state_enum'):
                        is_uploading = torrent.state_enum.is_uploading
                except Exception:
                    pass
                
                if not is_uploading and not is_paused:
                    is_uploading = (state_lower == 'uploading' or 
                                  state_lower == 'stalledup' or 
                                  state_lower == 'queuedup')
                
                # error/missingFiles/checking 等其它状态不处理，避免把异常种子当成暂停种子恢复
                if is_downloading:
                    downloading_torrents.append(torrent)
            
            # 输出状态统计用于调试
            logger.info(f"【功能5-下载阈值控制】种子状态统计: {dict(sorted(state_counter.items(), key=lambda x: x[1], reverse=True)[:10])}")
            logger.info(f"【功能5-下载阈值控制】发现 {len(downloading_torrents)} 个下载中的种子, {len(paused_torrents)} 个暂停的种子")
            
            # 如果检测到暂停的种子，输出前几个的详细信息用于调试
            if paused_torrents:
                logger.debug(f"【功能5-下载阈值控制】暂停种子详情（前5个）:")
                for i, torrent in enumerate(paused_torrents[:5], 1):
                    state_name = getattr(torrent, 'state', '') or ''
                    progress = getattr(torrent, 'progress', 0)
                    dlspeed = getattr(torrent, 'dlspeed', 0)
                    logger.debug(f"  {i}. {getattr(torrent, 'name', 'Unknown')} | 状态: {state_name} | 进度: {progress*100:.1f}% | 速度: {dlspeed}")
            
            # 收集所有下载中种子的文件信息（只计算需要下载的文件，优先级不为0）
            downloading_torrent_info = []
            
            for torrent in downloading_torrents:
                torrent_hash = getattr(torrent, 'hash', '')
                torrent_name = getattr(torrent, 'name', 'Unknown')
                
                try:
                    # 获取种子文件列表
                    files = downloader_obj.get_files(tid=torrent_hash)
                    if not files:
                        logger.debug(f"【功能5-下载阈值控制】无法获取种子文件列表: {torrent_name}")
                        continue
                    
                    # 计算该种子需要下载的文件总大小
                    torrent_remaining_size = 0
                    for file in files:
                        # 获取文件优先级，如果为0则跳过（不下载的文件）
                        file_priority = getattr(file, 'priority', 0)
                        if file_priority == 0:
                            continue  # 跳过不下载的文件
                        
                        file_progress = getattr(file, 'progress', 0)
                        if file_progress >= 1.0:
                            continue  # 跳过已完成的文件
                        
                        file_size = getattr(file, 'size', 0)
                        remaining_size = file_size * (1 - file_progress)
                        torrent_remaining_size += remaining_size
                    
                    if torrent_remaining_size > 0:
                        dlspeed = getattr(torrent, 'dlspeed', 0)
                        progress = getattr(torrent, 'progress', 0)
                        downloading_torrent_info.append({
                            'torrent': torrent,
                            'torrent_hash': torrent_hash,
                            'torrent_name': torrent_name,
                            'remaining_size': torrent_remaining_size,
                            'dlspeed': dlspeed,
                            'dlspeed_mbps': dlspeed / (1024 * 1024),  # 转换为MB/s
                            'progress': progress,
                            'progress_percent': progress * 100
                        })
                    
                except Exception as e:
                    logger.warning(f"【功能5-下载阈值控制】处理种子文件异常: {torrent_name}, 错误: {str(e)}")
                    continue
            
            # 计算所有下载中种子的总剩余大小
            if downloading_torrent_info:
                total_remaining_size = sum(t['remaining_size'] for t in downloading_torrent_info)
                total_remaining_gb = total_remaining_size / (1024**3)
                estimated_free_space = free_space_gb - total_remaining_gb
                
                logger.info(f"【功能5-下载阈值控制】下载中种子总数: {len(downloading_torrent_info)}")
                logger.info(f"【功能5-下载阈值控制】预计下载空间（仅计算需要下载的文件）: {total_remaining_gb:.2f}GB")
                logger.info(f"【功能5-下载阈值控制】预计剩余空间: {estimated_free_space:.2f}GB")
            else:
                # 没有下载中的种子，预计剩余空间就是当前剩余空间
                total_remaining_gb = 0
                estimated_free_space = free_space_gb
                
                logger.info(f"【功能5-下载阈值控制】没有下载中的种子")
                logger.info(f"【功能5-下载阈值控制】预计下载空间: 0GB")
                logger.info(f"【功能5-下载阈值控制】预计剩余空间（当前剩余空间）: {estimated_free_space:.2f}GB")
                
                # 如果没有暂停的种子，直接返回
                if not paused_torrents:
                    logger.info(f"【功能5-下载阈值控制】没有暂停的种子，无需调整")
                    return False
                
                # 如果有暂停的种子，继续执行恢复逻辑（跳过暂停逻辑，直接到恢复逻辑）
                logger.info(f"【功能5-下载阈值控制】有暂停的种子，检查是否可以恢复")
            
            # 如果预计剩余空间小于最小阈值，需要暂停部分种子
            if estimated_free_space < self._min_disk_space_threshold:
                # 如果没有下载中的种子，无法暂停，直接返回
                if not downloading_torrent_info:
                    logger.warning(f"【功能5-下载阈值控制】预计剩余空间({estimated_free_space:.2f}GB) < 最小阈值({self._min_disk_space_threshold}GB)，但没有下载中的种子可以暂停")
                    return False
                
                logger.warning(f"【功能5-下载阈值控制】预计剩余空间({estimated_free_space:.2f}GB) < 最小阈值({self._min_disk_space_threshold}GB)，开始暂停种子")
                
                # 保留优先级：当前下载速度高的优先不暂停；速度相同时，下载进度高的优先不暂停。
                # 因此暂停顺序为：速度低 -> 进度低 -> 剩余空间大。
                downloading_torrent_info.sort(
                    key=lambda x: (x['dlspeed_mbps'], x['progress'], -x['remaining_size'])
                )
                
                # 计算需要暂停的总大小
                space_shortage_gb = self._min_disk_space_threshold - estimated_free_space
                space_shortage_bytes = space_shortage_gb * (1024**3)
                
                logger.info(f"【功能5-下载阈值控制】空间不足: {space_shortage_gb:.2f}GB，需要暂停种子释放空间")
                
                paused_count = 0
                paused_size = 0
                
                # 从慢到快暂停种子，直到总大小不超过阈值
                for torrent_info in downloading_torrent_info:
                    if paused_size >= space_shortage_bytes:
                        break  # 已经暂停足够多的种子
                    
                    torrent = torrent_info['torrent']
                    torrent_hash = torrent_info['torrent_hash']
                    torrent_name = torrent_info['torrent_name']
                    remaining_size = torrent_info['remaining_size']
                    dlspeed_mbps = torrent_info['dlspeed_mbps']
                    progress_percent = torrent_info['progress_percent']
                    
                    try:
                        # 暂停种子
                        result = downloader_obj.stop_torrents(ids=[torrent_hash])
                        
                        if result:
                            logger.info(f"【功能5-下载阈值控制】暂停种子成功: {torrent_name} (速度: {dlspeed_mbps:.2f}MB/s, 进度: {progress_percent:.1f}%, 剩余: {StringUtils.str_filesize(remaining_size)})")
                            paused_by_plugin.add(torrent_hash)
                            paused_count += 1
                            paused_size += remaining_size
                        else:
                            logger.warning(f"【功能5-下载阈值控制】暂停种子失败: {torrent_name}")
                            
                    except Exception as e:
                        logger.error(f"【功能5-下载阈值控制】暂停种子异常: {torrent_name}, 错误: {str(e)}")
                
                logger.info(f"【功能5-下载阈值控制】暂停完成: 暂停 {paused_count} 个种子，释放空间: {StringUtils.str_filesize(paused_size)}")
                
                # 发送通知
                if self._notify and paused_count > 0:
                    notification_title = "【QB种子优化】下载阈值控制已暂停种子"
                    notification_text = f"当前磁盘剩余空间: {free_space_gb:.2f}GB\n"
                    notification_text += f"预计下载空间: {total_remaining_gb:.2f}GB\n"
                    notification_text += f"预计剩余空间: {estimated_free_space:.2f}GB\n"
                    notification_text += f"最小阈值: {self._min_disk_space_threshold}GB\n"
                    notification_text += f"空间不足: {space_shortage_gb:.2f}GB\n"
                    notification_text += f"\n已暂停 {paused_count} 个低速低进度的种子，释放空间: {StringUtils.str_filesize(paused_size)}\n"
                    notification_text += f"确保磁盘空间不会超过阈值"
                    
                    self.post_message(
                        mtype=NotificationType.Manual,
                        title=notification_title,
                        text=notification_text
                    )
                
                return paused_count > 0
            else:
                # 预计剩余空间 >= 最小阈值，可以尝试恢复暂停的种子
                logger.info(f"【功能5-下载阈值控制】预计剩余空间({estimated_free_space:.2f}GB) >= 最小阈值({self._min_disk_space_threshold}GB)，检查是否可以恢复暂停的种子")
                
                if not paused_torrents:
                    logger.info(f"【功能5-下载阈值控制】没有暂停的种子，无需恢复")
                    return False
                
                # 收集暂停种子的信息
                paused_torrent_info = []
                logger.info(f"【功能5-下载阈值控制】开始收集 {len(paused_torrents)} 个暂停种子的信息")
                
                for i, torrent in enumerate(paused_torrents, 1):
                    torrent_hash = getattr(torrent, 'hash', '')
                    torrent_name = getattr(torrent, 'name', 'Unknown')
                    
                    try:
                        # 获取种子文件列表
                        files = downloader_obj.get_files(tid=torrent_hash)
                        if not files:
                            logger.debug(f"【功能5-下载阈值控制】暂停种子 {i}/{len(paused_torrents)}: {torrent_name} - 无法获取文件列表")
                            continue
                        
                        # 计算该种子需要下载的文件总大小
                        torrent_remaining_size = 0
                        for file in files:
                            file_priority = getattr(file, 'priority', 0)
                            if file_priority == 0:
                                continue
                            
                            file_progress = getattr(file, 'progress', 0)
                            if file_progress >= 1.0:
                                continue
                            
                            file_size = getattr(file, 'size', 0)
                            remaining_size = file_size * (1 - file_progress)
                            torrent_remaining_size += remaining_size
                        
                        if torrent_remaining_size > 0:
                            # 获取种子之前的下载速度（如果可用）
                            dlspeed = getattr(torrent, 'dlspeed', 0)
                            paused_torrent_info.append({
                                'torrent': torrent,
                                'torrent_hash': torrent_hash,
                                'torrent_name': torrent_name,
                                'remaining_size': torrent_remaining_size,
                                'dlspeed': dlspeed,
                                'dlspeed_mbps': dlspeed / (1024 * 1024) if dlspeed > 0 else 0
                            })
                            logger.debug(f"【功能5-下载阈值控制】暂停种子 {i}/{len(paused_torrents)}: {torrent_name} - 剩余: {StringUtils.str_filesize(torrent_remaining_size)}, 速度: {dlspeed / (1024 * 1024):.2f}MB/s")
                        else:
                            logger.debug(f"【功能5-下载阈值控制】暂停种子 {i}/{len(paused_torrents)}: {torrent_name} - 没有需要下载的文件（所有文件已完成或优先级为0）")
                    
                    except Exception as e:
                        logger.warning(f"【功能5-下载阈值控制】处理暂停种子异常: {torrent_name}, 错误: {str(e)}")
                        import traceback
                        logger.debug(f"【功能5-下载阈值控制】异常详情: {traceback.format_exc()}")
                        continue
                
                logger.info(f"【功能5-下载阈值控制】收集完成: 共 {len(paused_torrent_info)} 个暂停种子有需要下载的文件")
                
                if not paused_torrent_info:
                    logger.info(f"【功能5-下载阈值控制】没有需要恢复的暂停种子（所有暂停种子的文件都已完成或优先级为0）")
                    return False
                
                # 按文件大小从小到大排序（小的先恢复），这样可以恢复更多种子
                # 因为暂停的种子速度都是0，按速度排序没有意义
                paused_torrent_info.sort(key=lambda x: x['remaining_size'])
                
                # 输出前5个待恢复的种子信息
                logger.info(f"【功能5-下载阈值控制】待恢复种子列表（前5个，按大小从小到大排序）:")
                for i, t in enumerate(paused_torrent_info[:5], 1):
                    logger.info(f"  {i}. {t['torrent_name']} | 剩余: {StringUtils.str_filesize(t['remaining_size'])} | 速度: {t['dlspeed_mbps']:.2f}MB/s")
                
                # 计算当前预计剩余空间（用于判断恢复后是否超过阈值）
                logger.info(f"【功能5-下载阈值控制】当前预计剩余空间: {estimated_free_space:.2f}GB, 最小阈值: {self._min_disk_space_threshold}GB")
                logger.info(f"【功能5-下载阈值控制】可以恢复的种子：恢复后预计剩余空间 >= {self._min_disk_space_threshold}GB")
                
                resumed_count = 0
                resumed_size = 0
                current_estimated_free_space = estimated_free_space  # 动态跟踪恢复后的预计剩余空间
                
                # 从小到大恢复种子（小的先恢复，可以恢复更多种子），但不能超过阈值
                for i, torrent_info in enumerate(paused_torrent_info, 1):
                    remaining_size = torrent_info['remaining_size']
                    torrent_name = torrent_info['torrent_name']
                    
                    # 计算恢复这个种子后的预计剩余空间
                    new_estimated_free_space = current_estimated_free_space - (remaining_size / (1024**3))  # 转换为GB
                    
                    # 如果恢复这个种子后，预计剩余空间 < 最小阈值，停止恢复
                    if new_estimated_free_space < self._min_disk_space_threshold:
                        logger.info(f"【功能5-下载阈值控制】恢复种子 {i}/{len(paused_torrent_info)}: {torrent_name} - 恢复此种子后预计剩余空间({new_estimated_free_space:.2f}GB) < 最小阈值({self._min_disk_space_threshold}GB)，停止恢复")
                        break
                    
                    torrent_hash = torrent_info['torrent_hash']
                    dlspeed_mbps = torrent_info['dlspeed_mbps']
                    
                    try:
                        logger.info(f"【功能5-下载阈值控制】恢复种子 {i}/{len(paused_torrent_info)}: {torrent_name} - 尝试恢复（速度: {dlspeed_mbps:.2f}MB/s, 剩余: {StringUtils.str_filesize(remaining_size)}）")
                        # 恢复种子
                        result = downloader_obj.start_torrents(ids=[torrent_hash])
                        
                        if result:
                            logger.info(f"【功能5-下载阈值控制】恢复种子成功: {torrent_name} (速度: {dlspeed_mbps:.2f}MB/s, 剩余: {StringUtils.str_filesize(remaining_size)})")
                            paused_by_plugin.discard(torrent_hash)
                            resumed_count += 1
                            resumed_size += remaining_size
                            # 更新当前预计剩余空间（恢复后，这个种子会变成下载中的）
                            current_estimated_free_space = new_estimated_free_space
                            logger.debug(f"【功能5-下载阈值控制】恢复后预计剩余空间更新为: {current_estimated_free_space:.2f}GB")
                        else:
                            logger.warning(f"【功能5-下载阈值控制】恢复种子失败: {torrent_name} (API返回False)")
                            
                    except Exception as e:
                        logger.error(f"【功能5-下载阈值控制】恢复种子异常: {torrent_name}, 错误: {str(e)}")
                        import traceback
                        logger.debug(f"【功能5-下载阈值控制】异常详情: {traceback.format_exc()}")
                
                logger.info(f"【功能5-下载阈值控制】恢复完成: 恢复 {resumed_count} 个种子，占用空间: {StringUtils.str_filesize(resumed_size)}")
                
                # 发送通知
                if self._notify and resumed_count > 0:
                    notification_title = "【QB种子优化】下载阈值控制已恢复种子"
                    notification_text = f"当前磁盘剩余空间: {free_space_gb:.2f}GB\n"
                    notification_text += f"恢复前预计剩余空间: {estimated_free_space:.2f}GB\n"
                    notification_text += f"恢复后预计剩余空间: {current_estimated_free_space:.2f}GB\n"
                    notification_text += f"最小阈值: {self._min_disk_space_threshold}GB\n"
                    notification_text += f"\n已恢复 {resumed_count} 个暂停的种子（按大小从小到大），占用空间: {StringUtils.str_filesize(resumed_size)}\n"
                    notification_text += f"确保磁盘空间不会超过阈值"
                    
                    self.post_message(
                        mtype=NotificationType.Manual,
                        title=notification_title,
                        text=notification_text
                    )
                
                return resumed_count > 0
                
        except Exception as e:
            logger.error(f"【功能5-下载阈值控制】下载阈值控制管理异常: {str(e)}")
            import traceback
            logger.error(f"【功能5-下载阈值控制】异常详情: {traceback.format_exc()}")
            return False

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
        return True, ""

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
            return None

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
            download_id = DownloadChain().download_single(
                context=context,
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
                
                status_msg = f"【{downloader_name}状态】\n"
                status_msg += f"总种子数: {len(all_torrents)}\n"
                status_msg += f"下载中: {len(downloading)}\n"
                status_msg += f"做种中: {len(uploading)}\n"
                status_msg += f"下载中显示无人做种（未复核）: {len(zero_seed)}\n"
                # status_msg += f"高做种数: 已改为综合评分判断\n"
                
                logger.info(f"【QB种子优化】状态消息: {status_msg}")
                if self._notify:
                    logger.info(f"【QB种子优化】发送状态通知")
                    self.post_message(
                        mtype=NotificationType.Download,
                        title=f"【QB优化状态】",
                        text=status_msg
                    )

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
                                            'text': '设置排除条件，避免误删重要文件（对无人做种、慢速下载、识别不到媒体信息三项清理生效）'
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
                                            'text': '📊 下载阈值控制：当下载中种子总大小超过阈值时，优先保留当前下载速度高的种子；速度相同时，优先保留下载进度高的种子，暂停低速低进度种子以确保磁盘空间不超阈值。当空间充足时，按下载速度从快到慢恢复暂停的种子，但不能超过阈值。只处理需要下载的文件（优先级不为0），跳过不下载的文件（优先级为0）'
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
                                                    '候选资源需季集一致、大小相近、做种数达标，按做种数从高到低选择，下载到原下载器和原目录。'
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
