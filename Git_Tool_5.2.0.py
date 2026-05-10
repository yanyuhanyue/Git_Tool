import tkinter as tk
from tkinter import ttk, filedialog, messagebox
from pathlib import Path
import subprocess
import threading
import re
import json
import copy
import uuid
import shlex
import webbrowser
import zipfile
import os
import sys


class GitGuiApp(tk.Tk):
    """
    Git 图形化自动脚本

    主要功能：
    1. 常用 Git 操作按钮
    2. 选择仓库后自动检测是否 Git 仓库、是否连接 GitHub
    3. 非 Git 仓库时弹出“连接 GitHub”窗口，包含：打开 GitHub / 克隆仓库 / 取消
    4. 智能推送：自动判断是否第一次推送
    5. 多人协作同步检查：检测本地是否领先 / 落后 / 分叉
    6. 启动时询问是否加载上一次布局，并可勾选不再提示
    7. 按钮布局可拖拽、隐藏、导入、导出、自定义
    8. 查看日志时 提交 ID 蓝色显示，Ctrl + 左键可切换版本
    """

    CONFIG_PATH = Path.home() / ".git_gui_tool_config.json"

    def __init__(self):
        super().__init__()

        self.title("Git 图形化自动脚本")
        self.geometry("1120x790")
        self.minsize(920, 630)

        self.repo_path = tk.StringVar()
        self.status_text = tk.StringVar(value="请选择一个 Git 仓库目录")
        self.simple_mode_var = tk.BooleanVar(value=True)

        self.layout_edit_mode = False
        self.drag_ghost = None
        self.insert_marker = None
        self.current_insert_index = None

        self.action_registry = self.create_action_registry()
        self.default_button_layout = self.create_default_button_layout()
        self.button_layout = copy.deepcopy(self.default_button_layout)
        self.max_cols = 5
        self.layout_modified = False

        self.drag_data = {
            "key": None,
            "item": None,
            "start_x": 0,
            "start_y": 0,
            "dragging": False,
            "widget": None,
        }

        self.button_key_by_widget = {}
        self.button_widget_by_key = {}

        # 避免同一个仓库反复弹出 LF/CRLF 自动修复提示
        self.crlf_warning_prompted_repos = set()
        self.is_running_line_ending_fix = False

        # 避免同一个仓库反复弹出“中文文件名显示为八进制”的修复提示
        self.octal_filename_prompted_repos = set()
        self.is_running_chinese_filename_fix = False

        # 避免同类 warning / error 复制提示反复刷屏
        self.last_copied_diagnostic_text = ""
        self.git_install_prompted = False

        # 避免同一批暂存文件反复提示
        self.staged_files_prompted_keys = set()

        self.app_config = self.load_app_config()

        # 启动时直接恢复上次关闭软件时的模式；没有记录时默认精简模式
        self.simple_mode_var.set(bool(self.app_config.get("simple_mode", True)))

        self.create_widgets()
        self.protocol("WM_DELETE_WINDOW", self.on_close)

        # 启动后先检测 Git，再依次询问是否打开上次路径、是否加载上次布局
        self.after(120, self.check_git_installation_on_startup)
        self.after(350, self.prompt_startup_choices)

    # ============================================================
    # 配置：上一次布局、是否不再提示
    # ============================================================

    def load_app_config(self):
        default_config = {
            "suppress_load_layout_prompt": False,
            "auto_load_last_layout": False,
            "last_layout": None,
            "last_max_cols": 5,

            "suppress_load_repo_prompt": False,
            "auto_load_last_repo_path": False,
            "last_repo_path": "",

            "custom_buttons_exported": False,

            # 直接记住上次关闭软件时的精简/标准模式
            "remember_simple_mode": True,
            "simple_mode": True,
        }

        if not self.CONFIG_PATH.exists():
            return default_config

        try:
            with open(self.CONFIG_PATH, "r", encoding="utf-8") as f:
                data = json.load(f)

            if isinstance(data, dict):
                default_config.update(data)

            return default_config

        except Exception:
            return default_config

    def save_app_config(self):
        try:
            with open(self.CONFIG_PATH, "w", encoding="utf-8") as f:
                json.dump(self.app_config, f, ensure_ascii=False, indent=4)
        except Exception:
            pass

    def save_current_layout_to_config(self):
        self.app_config["last_layout"] = copy.deepcopy(self.button_layout)
        self.app_config["last_max_cols"] = self.max_cols
        self.save_app_config()

    def mark_layout_modified(self):
        """
        手动修改布局后调用：
        1. 保存为上次布局；
        2. 标记关闭软件时需要询问是否导出；
        3. 下次启动恢复为询问是否加载布局。
        """
        self.layout_modified = True
        self.app_config["suppress_load_layout_prompt"] = False
        self.app_config["auto_load_last_layout"] = False
        self.save_current_layout_to_config()

    def save_current_repo_path_to_config(self):
        path = self.repo_path.get().strip()

        if path:
            self.app_config["last_repo_path"] = path
            self.save_app_config()

    def on_close(self):
        self.save_current_repo_path_to_config()

        # 关闭软件时自动记住当前是精简模式还是标准模式
        self.app_config["remember_simple_mode"] = True
        self.app_config["simple_mode"] = bool(self.simple_mode_var.get())
        self.save_app_config()

        if self.layout_modified:
            choice = messagebox.askyesnocancel(
                "导出布局",
                "检测到你修改过按钮布局或自定义按钮。\n\n"
                "是否在关闭软件前导出？\n\n"
                "选择“是”：打开导出选项\n"
                "选择“否”：不导出，直接关闭\n"
                "选择“取消”：返回软件"
            )

            if choice is None:
                return

            if choice:
                exported = self.export_layout(show_mode_dialog=True)
                if not exported:
                    return

        # 无论是否导出，都保存为上次布局；并确保下次启动会询问是否加载布局。
        if self.layout_modified:
            self.app_config["suppress_load_layout_prompt"] = False
            self.app_config["auto_load_last_layout"] = False

        self.save_current_layout_to_config()
        self.destroy_drag_ghost()
        self.destroy_insert_marker()
        self.destroy()

    def prompt_startup_choices(self):
        # 先询问是否打开上次仓库路径，再询问是否加载上次布局，避免两个弹窗同时出现。
        self.prompt_load_last_repo_path_if_needed()
        self.prompt_load_last_layout_if_needed()

    def prompt_load_last_repo_path_if_needed(self):
        last_repo_path = self.app_config.get("last_repo_path", "")

        if not last_repo_path:
            return

        if not Path(last_repo_path).exists():
            return

        if self.app_config.get("suppress_load_repo_prompt", False):
            if self.app_config.get("auto_load_last_repo_path", False):
                self.repo_path.set(last_repo_path)
                self.status_text.set(f"已打开上次路径：{last_repo_path}")
                self.append_output(f"\n已打开上次路径：{last_repo_path}\n")
                self.after(80, self.check_repo_after_choose)
            return

        dialog = tk.Toplevel(self)
        dialog.withdraw()
        dialog.title("打开上次路径")
        dialog.resizable(False, False)
        dialog.transient(self)
        dialog.grab_set()
        dialog.attributes("-topmost", True)

        result = {"choice": "skip"}
        remember_var = tk.BooleanVar(value=False)

        frame = ttk.Frame(dialog, padding=16)
        frame.pack(fill="both", expand=True)

        ttk.Label(
            frame,
            text=f"检测到上一次使用的仓库路径：\n\n{last_repo_path}\n\n是否打开这个路径？",
            justify="left"
        ).pack(anchor="w", pady=(0, 12))

        ttk.Checkbutton(
            frame,
            text="记住本次选择，以后不再提示",
            variable=remember_var
        ).pack(anchor="w", pady=(0, 12))

        btn_frame = ttk.Frame(frame)
        btn_frame.pack(fill="x")

        def choose_open():
            result["choice"] = "open"
            dialog.destroy()

        def choose_skip():
            result["choice"] = "skip"
            dialog.destroy()

        ttk.Button(btn_frame, text="打开", command=choose_open).pack(side="left", padx=(0, 8))
        ttk.Button(btn_frame, text="不打开", command=choose_skip).pack(side="left")

        # 点 X 等同“不打开”
        dialog.protocol("WM_DELETE_WINDOW", choose_skip)

        self.center_dialog(dialog, min_width=520, min_height=240)
        self.wait_window(dialog)

        if result["choice"] == "open":
            self.repo_path.set(last_repo_path)
            self.status_text.set(f"已打开上次路径：{last_repo_path}")
            self.append_output(f"\n已打开上次路径：{last_repo_path}\n")
            self.after(80, self.check_repo_after_choose)

        if remember_var.get():
            self.app_config["suppress_load_repo_prompt"] = True
            self.app_config["auto_load_last_repo_path"] = (result["choice"] == "open")
            self.save_app_config()

    def prompt_load_last_layout_if_needed(self):
        last_layout = self.app_config.get("last_layout")

        if not last_layout:
            return

        if self.app_config.get("suppress_load_layout_prompt", False):
            if self.app_config.get("auto_load_last_layout", False):
                self.load_layout_from_data(
                    last_layout,
                    self.app_config.get("last_max_cols", 5),
                    show_message=False
                )
            return

        dialog = tk.Toplevel(self)
        dialog.withdraw()
        dialog.title("加载上一次布局")
        dialog.resizable(False, False)
        dialog.transient(self)
        dialog.grab_set()
        dialog.attributes("-topmost", True)

        result = {"choice": "skip"}
        dont_ask_var = tk.BooleanVar(value=False)

        frame = ttk.Frame(dialog, padding=16)
        frame.pack(fill="both", expand=True)

        ttk.Label(
            frame,
            text="检测到上一次使用时保存的按钮布局。\n\n是否加载上一次的布局？",
            justify="left"
        ).pack(anchor="w", pady=(0, 12))

        ttk.Checkbutton(
            frame,
            text="以后不再提示",
            variable=dont_ask_var
        ).pack(anchor="w", pady=(0, 12))

        btn_frame = ttk.Frame(frame)
        btn_frame.pack(fill="x")

        def choose_load():
            result["choice"] = "load"
            dialog.destroy()

        def choose_skip():
            result["choice"] = "skip"
            dialog.destroy()

        ttk.Button(btn_frame, text="加载", command=choose_load).pack(side="left", padx=(0, 8))
        ttk.Button(btn_frame, text="不加载", command=choose_skip).pack(side="left")

        # 用户点 X 等同“不加载”，不再保留“取消”按钮
        dialog.protocol("WM_DELETE_WINDOW", choose_skip)

        self.center_dialog(dialog)
        self.wait_window(dialog)

        if result["choice"] == "load":
            self.load_layout_from_data(
                last_layout,
                self.app_config.get("last_max_cols", 5),
                show_message=False
            )

        if dont_ask_var.get():
            self.app_config["suppress_load_layout_prompt"] = True
            self.app_config["auto_load_last_layout"] = (result["choice"] == "load")
            self.save_app_config()

    def load_layout_from_data(self, layout, max_cols, show_message=True):
        self.button_layout = self.normalize_layout(layout)

        try:
            self.max_cols = int(max_cols)
        except Exception:
            self.max_cols = 5

        self.layout_edit_mode = False
        self.destroy_drag_ghost()
        self.destroy_insert_marker()
        self.reset_drag_data()
        self.render_buttons()

        if show_message:
            messagebox.showinfo("成功", "布局已加载")

    # ============================================================
    # 按钮注册与默认顺序
    # ============================================================

    def create_action_registry(self):
        return {
            "simple_upload": {"label": "一键上传到 GitHub", "method": "git_one_click_upload_to_github"},
            "init": {"label": "初始化仓库", "method": "git_init"},
            "clone_repo": {"label": "克隆仓库", "method": "git_clone_repo"},
            "add_remote": {"label": "添加远程 origin", "method": "git_add_remote"},
            "config_user": {"label": "配置用户名邮箱", "method": "git_config_user"},
            "edit_user": {"label": "修改用户名邮箱", "method": "git_edit_user"},
            "generate_ignore": {"label": "生成忽略文件", "method": "git_generate_ignore"},
            "edit_ignore": {"label": "修改忽略文件", "method": "git_edit_ignore"},
            "create_workflow": {"label": "一键创建工作流", "method": "git_create_workflow"},
            "edit_workflow": {"label": "编辑工作流文件", "method": "git_edit_workflow"},
            "status": {"label": "查看状态", "method": "git_status"},
            "add_all": {"label": "添加全部文件", "method": "git_add_all"},
            "add_some": {"label": "添加部分文件", "method": "git_add_some"},
            "commit": {"label": "添加说明", "method": "git_commit"},
            "push": {"label": "推送至仓库", "method": "git_smart_push"},
            "pull": {"label": "拉取", "method": "git_pull"},
            "sync_status": {"label": "检查同步", "method": "git_check_sync_status"},
            "log": {"label": "查看日志", "method": "git_log"},
            "checkout_commit": {"label": "切换到指定版本", "method": "git_checkout_commit_by_input"},
            "all_branches": {"label": "查看所有分支", "method": "git_show_all_branches"},
            "create_branch": {"label": "创建分支", "method": "git_create_branch"},
            "rename_default_branch": {"label": "修改默认分支名称", "method": "git_rename_default_branch"},
            "commit_some_to_branch": {"label": "提交部分文件到指定分支", "method": "git_commit_some_to_branch"},
            "commit_all_to_branch": {"label": "提交全部文件到指定分支", "method": "git_commit_all_to_branch"},
            "remote": {"label": "查看远程仓库", "method": "git_remote"},
            "set_remote": {"label": "修改远程仓库", "method": "git_set_remote"},
            "restore_files": {"label": "恢复指定文件到旧版本", "method": "git_restore_files"},
            "checkout_branch": {"label": "切回指定分支", "method": "git_checkout_branch"},
            "current_branch": {"label": "查看当前分支", "method": "git_current_branch"},
            "fix_line_endings": {"label": "修复换行符警告", "method": "git_fix_line_endings_windows"},
            "clear_output": {"label": "清空输出", "method": "clear_output"},
            "fix_chinese": {"label": "修复中文显示", "method": "git_fix_chinese"},
        }

    def create_default_button_layout(self):
        # 初始化仓库第一位；切换到指定版本紧跟查看日志；
        # 修复中文显示倒数第二，清空输出最后。
        order = [
            "clone_repo",
            "init",
            "add_remote",
            "config_user",
            "edit_user",
            "generate_ignore",
            "simple_upload",
            "edit_ignore",
            "status",
            "add_all",
            "add_some",
            "commit",
            "push",
            "pull",
            "sync_status",
            "log",
            "checkout_commit",
            "all_branches",
            "create_branch",
            "rename_default_branch",
            "commit_some_to_branch",
            "commit_all_to_branch",
            "remote",
            "set_remote",
            "restore_files",
            "checkout_branch",
            "current_branch",
            "fix_line_endings",
            "fix_chinese",
            "create_workflow",
            "edit_workflow",
            "clear_output",
        ]

        return [
            {"type": "builtin", "id": action_id, "visible": self.is_action_default_visible(action_id)}
            for action_id in order
        ]

    def is_action_default_visible(self, action_id):
        # 以下按钮默认隐藏，用户可通过“显示隐藏”手动显示。
        default_hidden_actions = {
            "all_branches",
            "create_branch",
            "rename_default_branch",
            "commit_some_to_branch",
            "commit_all_to_branch",
            "remote",
            "set_remote",
            "config_user",
            "edit_user",
            "fix_line_endings",
            "create_workflow",
            "edit_workflow",
        }
        return action_id not in default_hidden_actions


    # ============================================================
    # .gitignore 忽略文件模板
    # ============================================================

    def get_ignore_template_dir(self):
        """
        用户可编辑模板保存位置：
        用户目录/.git_gui_ignore_templates
        """
        template_dir = Path.home() / ".git_gui_ignore_templates"
        template_dir.mkdir(parents=True, exist_ok=True)
        return template_dir

    def safe_template_filename(self, name):
        safe_name = re.sub(r'[<>:"/\\|?*\s]+', "_", name.strip())
        safe_name = safe_name.strip("._")

        if not safe_name:
            safe_name = "Custom_Template"

        return safe_name + ".gitignore_template"

    def get_default_ignore_template_texts(self):
        """
        内置常用 .gitignore 模板。
        首次运行时会写入用户目录，之后用户可以自行修改这些模板文件。
        """
        ue5_template = """# Unreal Engine 5 / UE5
# 由 Git 图形化工具生成

# 构建产物
Binaries/
DerivedDataCache/
Intermediate/
Saved/
Build/

# IDE / 编辑器
.vs/
.vscode/.browse.VC.db*
.vscode/ipch/
.idea/

# Visual Studio 文件
*.suo
*.user
*.userosscache
*.sln.docstates
*.VC.db
*.VC.opendb

# 日志和崩溃报告
*.log
*.dmp

# 打包输出
Windows/
WindowsNoEditor/
Linux/
Mac/

# 可选的本地临时文件
*.tmp
*.bak

# 通常应该提交：
# Source/
# Content/
# Config/
# *.uproject
"""

        unity_template = """# Unity
# 由 Git 图形化工具生成

[Ll]ibrary/
[Tt]emp/
[Oo]bj/
[Bb]uild/
[Bb]uilds/
[Ll]ogs/
[Uu]ser[Ss]ettings/

# 内存捕获文件可能很大
[Mm]emoryCaptures/

# Visual Studio 文件 / Rider
.vs/
.idea/
*.csproj
*.unityproj
*.sln
*.suo
*.tmp
*.user
*.userprefs
*.pidb
*.booproj
*.svd
*.pdb
*.mdb
*.opendb
*.VC.db

# Unity 生成的崩溃报告
sysinfo.txt

# 构建和包文件
*.apk
*.aab
*.unitypackage

# 保留 .meta 文件！
# *.meta
"""

        python_template = """# Python
# 由 Git 图形化工具生成

__pycache__/
*.py[cod]
*$py.class

# 虚拟环境
.venv/
venv/
env/
ENV/

# 发布 / 打包
build/
dist/
*.egg-info/
.eggs/
*.egg
pip-wheel-metadata/

# 测试 / 覆盖率
.pytest_cache/
.coverage
.coverage.*
htmlcov/
.tox/
.nox/

# IDE
.vscode/
.idea/

# 环境变量文件
.env
.env.*
!.env.example

# Jupyter
.ipynb_checkpoints/
"""

        node_template = """# Node.js / 前端项目
# 由 Git 图形化工具生成

node_modules/
npm-debug.log*
yarn-debug.log*
yarn-error.log*
pnpm-debug.log*

# 构建输出
dist/
build/
.next/
.nuxt/
out/
coverage/

# 环境变量文件
.env
.env.*
!.env.example

# 缓存
.cache/
.parcel-cache/
.turbo/

# IDE
.vscode/
.idea/

# 系统文件
.DS_Store
Thumbs.db
"""

        cpp_vs_template = """# C / C++ / Visual Studio 项目
# 由 Git 图形化工具生成

# 构建输出
Debug/
Release/
x64/
x86/
bin/
obj/
build/
out/

# Visual Studio 文件
.vs/
*.suo
*.user
*.userosscache
*.sln.docstates
*.VC.db
*.VC.opendb
ipch/

# Compiled objects
*.o
*.obj
*.lib
*.dll
*.exe
*.pdb
*.ilk
*.idb

# CMake
CMakeFiles/
CMakeCache.txt
cmake_install.cmake
compile_commands.json

# IDE
.vscode/
.idea/
"""

        java_template = """# Java / Maven / Gradle 项目
# 由 Git 图形化工具生成

# 编译后的 class 文件
*.class

# Logs
*.log

# Maven
target/

# Gradle
.gradle/
build/

# IntelliJ IDEA
.idea/
*.iml
*.iws
*.ipr

# Eclipse
.project
.classpath
.settings/

# VS Code
.vscode/

# 打包文件
*.jar
*.war
*.ear
"""

        go_template = """# Go
# 由 Git 图形化工具生成

# 二进制文件
*.exe
*.exe~
*.dll
*.so
*.dylib
*.test
*.out

# 构建输出
bin/
dist/
build/

# 依赖目录
vendor/

# Go 工作区
go.work

# IDE
.vscode/
.idea/

# 环境变量文件
.env
"""

        web_template = """# 通用 Web 项目
# 由 Git 图形化工具生成

# 依赖目录
node_modules/
vendor/

# 构建输出
dist/
build/
public/build/
coverage/

# 环境变量文件
.env
.env.*
!.env.example

# 缓存
.cache/
.tmp/
temp/

# IDE
.vscode/
.idea/

# 系统文件
.DS_Store
Thumbs.db
"""

        general_template = """# 通用模板
# 由 Git 图形化工具生成

# 系统文件
.DS_Store
Thumbs.db
Desktop.ini

# IDE
.vscode/
.idea/
.vs/

# Logs
*.log

# 临时文件
*.tmp
*.temp
*.bak
*.swp
~$*

# 环境变量文件 / secrets
.env
.env.*
!.env.example

# 构建输出
build/
dist/
out/
bin/
obj/
"""

        return {
            "UE5_Unreal_Engine_5": ue5_template,
            "Unity": unity_template,
            "Python": python_template,
            "Node_js_Frontend": node_template,
            "C_CPP_Visual_Studio": cpp_vs_template,
            "Java_Maven_Gradle": java_template,
            "Go": go_template,
            "通用模板_Web_Project": web_template,
            "通用模板": general_template,
        }

    def ensure_ignore_template_files(self):
        template_dir = self.get_ignore_template_dir()

        for name, content in self.get_default_ignore_template_texts().items():
            path = template_dir / self.safe_template_filename(name)

            # 不覆盖用户已经修改过的模板
            if not path.exists():
                path.write_text(content, encoding="utf-8")

    def display_name_from_template_path(self, path):
        name = path.name

        if name.endswith(".gitignore_template"):
            name = name[:-len(".gitignore_template")]

        mapping = {
            "UE5_Unreal_Engine_5": "UE5 / 虚幻引擎 5",
            "Node_js_Frontend": "Node.js / 前端项目",
            "C_CPP_Visual_Studio": "C / C++ / Visual Studio 项目",
            "Java_Maven_Gradle": "Java / Maven / Gradle 项目",
            "通用模板_Web_Project": "通用 Web 项目",
        }

        return mapping.get(name, name.replace("_", " "))

    def get_ignore_templates(self):
        self.ensure_ignore_template_files()
        template_dir = self.get_ignore_template_dir()

        templates = {}

        for path in sorted(template_dir.glob("*.gitignore_template")):
            try:
                display_name = self.display_name_from_template_path(path)
                templates[display_name] = {
                    "path": path,
                    "content": path.read_text(encoding="utf-8")
                }
            except Exception:
                pass

        return templates

    def update_ignore_buttons_by_repo(self):
        repo = self.get_repo_silent()
        if not repo:
            return

        ignore_path = Path(repo) / ".gitignore"

        if ignore_path.exists():
            self.hide_builtin_if_exists("generate_ignore")
            self.show_builtin_if_exists("edit_ignore")
        else:
            self.show_builtin_if_exists("generate_ignore")
            self.hide_builtin_if_exists("edit_ignore")

    def open_template_folder(self):
        template_dir = self.get_ignore_template_dir()

        try:
            if os.name == "nt":
                os.startfile(str(template_dir))
            elif sys.platform == "darwin":
                subprocess.Popen(["open", str(template_dir)])
            else:
                subprocess.Popen(["xdg-open", str(template_dir)])
        except Exception as e:
            messagebox.showerror("错误", f"无法打开模板文件夹：\n{e}")

    def open_ignore_template_editor(self, title, template_name="", content=""):
        dialog = tk.Toplevel(self)
        dialog.withdraw()
        dialog.title(title)
        dialog.resizable(True, True)
        dialog.transient(self)
        dialog.grab_set()
        dialog.attributes("-topmost", True)

        result = {
            "saved": False,
            "name": template_name,
            "content": content
        }

        frame = ttk.Frame(dialog, padding=12)
        frame.pack(fill="both", expand=True)

        ttk.Label(frame, text="模板名称：").pack(anchor="w")

        name_var = tk.StringVar(value=template_name)
        name_entry = ttk.Entry(frame, textvariable=name_var)
        name_entry.pack(fill="x", pady=(4, 10))

        ttk.Label(frame, text="模板内容：").pack(anchor="w")

        text_frame = ttk.Frame(frame)
        text_frame.pack(fill="both", expand=True, pady=(4, 10))

        text = tk.Text(text_frame, wrap="none", font=("Consolas", 10), undo=True)
        text.grid(row=0, column=0, sticky="nsew")
        text.insert("1.0", content)

        y_scroll = ttk.Scrollbar(text_frame, orient="vertical", command=text.yview)
        y_scroll.grid(row=0, column=1, sticky="ns")

        x_scroll = ttk.Scrollbar(text_frame, orient="horizontal", command=text.xview)
        x_scroll.grid(row=1, column=0, sticky="ew")

        text.configure(yscrollcommand=y_scroll.set, xscrollcommand=x_scroll.set)

        text_frame.rowconfigure(0, weight=1)
        text_frame.columnconfigure(0, weight=1)

        btn_frame = ttk.Frame(frame)
        btn_frame.pack(fill="x")

        def save():
            name = name_var.get().strip()
            body = text.get("1.0", "end-1c")

            if not name:
                messagebox.showwarning("提示", "模板名称不能为空")
                return

            if not body.strip():
                messagebox.showwarning("提示", "模板内容不能为空")
                return

            result["saved"] = True
            result["name"] = name
            result["content"] = body
            dialog.destroy()

        def cancel():
            dialog.destroy()

        ttk.Button(btn_frame, text="保存", command=save).pack(side="left", padx=(0, 8))
        ttk.Button(btn_frame, text="取消", command=cancel).pack(side="left")

        dialog.protocol("WM_DELETE_WINDOW", cancel)
        self.center_dialog(dialog, min_width=760, min_height=560)
        self.wait_window(dialog)

        return result

    def save_ignore_template_file(self, name, content):
        template_dir = self.get_ignore_template_dir()
        path = template_dir / self.safe_template_filename(name)
        path.write_text(content, encoding="utf-8")
        return path

    def git_generate_ignore(self):
        repo = self.get_repo()
        if not repo:
            return

        ignore_path = Path(repo) / ".gitignore"

        if ignore_path.exists():
            messagebox.showinfo("提示", "当前仓库已经存在 .gitignore，将显示“修改忽略文件”按钮。")
            self.update_ignore_buttons_by_repo()
            return

        templates = self.get_ignore_templates()

        dialog = tk.Toplevel(self)
        dialog.withdraw()
        dialog.title("生成忽略文件")
        dialog.resizable(True, True)
        dialog.transient(self)
        dialog.grab_set()
        dialog.attributes("-topmost", True)

        result = {"template_name": None}

        frame = ttk.Frame(dialog, padding=16)
        frame.pack(fill="both", expand=True)

        ttk.Label(
            frame,
            text="请选择要生成的 .gitignore 忽略文件模板：",
            justify="left"
        ).pack(anchor="w", pady=(0, 8))

        # 模板选择区域和内容预览区域分开显示，避免把下拉框内容和忽略文件内容混在一起。
        select_frame = ttk.LabelFrame(frame, text="模板选择", padding=10)
        select_frame.pack(fill="x", pady=(0, 12))

        template_var = tk.StringVar()
        values = list(templates.keys())

        if "UE5 / 虚幻引擎 5" in values:
            template_var.set("UE5 / 虚幻引擎 5")
        elif values:
            template_var.set(values[0])

        combo = ttk.Combobox(
            select_frame,
            textvariable=template_var,
            values=values,
            state="readonly",
            width=42,
            font=("Microsoft YaHei UI", 10)
        )
        combo.pack(fill="x")

        preview_outer = ttk.LabelFrame(frame, text="忽略文件内容预览 / .gitignore Preview", padding=8)
        preview_outer.pack(fill="both", expand=True, pady=(0, 12))

        preview_frame = ttk.Frame(preview_outer)
        preview_frame.pack(fill="both", expand=True)

        preview = tk.Text(
            preview_frame,
            width=78,
            height=18,
            font=("Consolas", 9),
            wrap="none",
            undo=False,
            bg="#f7f7f7",
            fg="#111111",
            insertbackground="#111111",
            relief="solid",
            borderwidth=1
        )
        preview.grid(row=0, column=0, sticky="nsew")

        y_scroll = ttk.Scrollbar(preview_frame, orient="vertical", command=preview.yview)
        y_scroll.grid(row=0, column=1, sticky="ns")

        x_scroll = ttk.Scrollbar(preview_frame, orient="horizontal", command=preview.xview)
        x_scroll.grid(row=1, column=0, sticky="ew")

        preview.configure(yscrollcommand=y_scroll.set, xscrollcommand=x_scroll.set)

        preview_frame.rowconfigure(0, weight=1)
        preview_frame.columnconfigure(0, weight=1)

        def reload_templates(selected_name=None):
            nonlocal templates
            templates = self.get_ignore_templates()
            names = list(templates.keys())
            combo.configure(values=names)

            if selected_name and selected_name in names:
                template_var.set(selected_name)
            elif template_var.get() not in names:
                template_var.set(names[0] if names else "")

            refresh_preview()

        def refresh_preview(*_):
            preview.configure(state="normal")
            preview.delete("1.0", "end")

            selected = template_var.get()
            if selected in templates:
                preview.insert(
                    "1.0",
                    f"# 当前选择模板：{selected}\n"
                    f"# 下面内容将写入当前仓库的 .gitignore 文件\n"
                    f"# {'=' * 58}\n\n"
                    + templates[selected]["content"]
                )
            else:
                preview.insert("1.0", "当前没有可用模板，请点击“添加模板”。")

            preview.configure(state="disabled")

        def add_template():
            editor_result = self.open_ignore_template_editor(
                "添加忽略文件模板",
                "New_Template",
                "# Custom .gitignore template\n"
            )

            if not editor_result["saved"]:
                return

            self.save_ignore_template_file(editor_result["name"], editor_result["content"])
            reload_templates(editor_result["name"])

        def edit_template():
            selected = template_var.get()

            if selected not in templates:
                messagebox.showinfo("提示", "请先选择一个模板")
                return

            editor_result = self.open_ignore_template_editor(
                "修改忽略文件模板",
                selected,
                templates[selected]["content"]
            )

            if not editor_result["saved"]:
                return

            old_path = templates[selected]["path"]
            new_path = self.get_ignore_template_dir() / self.safe_template_filename(editor_result["name"])

            if new_path != old_path and old_path.exists():
                try:
                    old_path.unlink()
                except Exception:
                    pass

            self.save_ignore_template_file(editor_result["name"], editor_result["content"])
            reload_templates(editor_result["name"])

        def open_folder():
            self.open_template_folder()

        combo.bind("<<ComboboxSelected>>", refresh_preview)
        refresh_preview()

        manage_frame = ttk.Frame(frame)
        manage_frame.pack(fill="x", pady=(0, 10))

        ttk.Button(manage_frame, text="添加模板", command=add_template).pack(side="left", padx=(0, 8))
        ttk.Button(manage_frame, text="修改模板", command=edit_template).pack(side="left", padx=(0, 8))
        ttk.Button(manage_frame, text="打开模板文件夹", command=open_folder).pack(side="left")

        btn_frame = ttk.Frame(frame)
        btn_frame.pack(fill="x")

        def ok():
            if not template_var.get():
                messagebox.showwarning("提示", "请先选择或添加一个模板")
                return

            result["template_name"] = template_var.get()
            dialog.destroy()

        def cancel():
            result["template_name"] = None
            dialog.destroy()

        ttk.Button(btn_frame, text="生成", command=ok).pack(side="left", padx=(0, 8))
        ttk.Button(btn_frame, text="取消", command=cancel).pack(side="left")

        dialog.protocol("WM_DELETE_WINDOW", cancel)
        self.center_dialog(dialog, min_width=760, min_height=560)
        self.wait_window(dialog)

        template_name = result["template_name"]
        if not template_name:
            return

        templates = self.get_ignore_templates()

        if template_name not in templates:
            messagebox.showerror("错误", "模板不存在，请重新选择")
            return

        try:
            ignore_path.write_text(templates[template_name]["content"], encoding="utf-8")
            self.append_output(f"\n已生成忽略文件：{ignore_path}\n模板：{template_name}\n")
            self.status_text.set("已生成 .gitignore 忽略文件")
            self.update_ignore_buttons_by_repo()

        except Exception as e:
            messagebox.showerror("错误", f"生成 .gitignore 失败：\n{e}")

    def git_edit_ignore(self):
        repo = self.get_repo()
        if not repo:
            return

        ignore_path = Path(repo) / ".gitignore"

        if not ignore_path.exists():
            messagebox.showinfo("提示", "当前仓库还没有 .gitignore，将显示“生成忽略文件”按钮。")
            self.update_ignore_buttons_by_repo()
            return

        try:
            if os.name == "nt":
                os.startfile(str(ignore_path))
            elif sys.platform == "darwin":
                subprocess.Popen(["open", str(ignore_path)])
            else:
                subprocess.Popen(["xdg-open", str(ignore_path)])

            self.append_output(f"\n已打开忽略文件：{ignore_path}\n")
            self.status_text.set("已打开 .gitignore")

        except Exception:
            try:
                webbrowser.open(ignore_path.as_uri())
                self.append_output(f"\n已打开忽略文件：{ignore_path}\n")
                self.status_text.set("已打开 .gitignore")
            except Exception as e:
                messagebox.showerror("错误", f"无法打开 .gitignore：\n{e}")


    # ============================================================
    # 主界面
    # ============================================================

    def create_widgets(self):
        nav_frame = ttk.Frame(self, padding=(10, 8, 10, 0))
        nav_frame.pack(fill="x")

        self.edit_layout_button = ttk.Button(
            nav_frame,
            text="编辑布局",
            command=self.toggle_edit_layout_mode
        )
        self.edit_layout_button.pack(side="left", padx=(0, 8), pady=2)

        ttk.Button(nav_frame, text="添加按钮", command=self.add_custom_button).pack(side="left", padx=(0, 8), pady=2)
        ttk.Button(nav_frame, text="显示隐藏", command=self.show_hidden_buttons_dialog).pack(side="left", padx=(0, 8), pady=2)
        ttk.Button(nav_frame, text="管理布局", command=self.open_layout_manager).pack(side="left", padx=(0, 8), pady=2)
        ttk.Button(nav_frame, text="每行数量", command=self.set_button_columns).pack(side="left", padx=(0, 8), pady=2)
        ttk.Button(nav_frame, text="导出布局", command=self.export_layout).pack(side="left", padx=(0, 8), pady=2)
        ttk.Button(nav_frame, text="导入布局", command=self.import_layout).pack(side="left", padx=(0, 8), pady=2)
        ttk.Button(nav_frame, text="重置布局", command=self.reset_layout).pack(side="left", padx=(0, 8), pady=2)

        # 放在导航栏最右边：用于恢复所有“以后不再提示 / 记住选择”的弹窗设置
        ttk.Button(nav_frame, text="初始化弹窗选择", command=self.reset_popup_choices).pack(side="right", padx=(8, 0), pady=2)

        top_frame = ttk.Frame(self, padding=10)
        top_frame.pack(fill="x")

        ttk.Label(top_frame, text="仓库路径：").pack(side="left")

        repo_entry = ttk.Entry(top_frame, textvariable=self.repo_path)
        repo_entry.pack(side="left", fill="x", expand=True, padx=5)

        ttk.Button(top_frame, text="选择仓库", command=self.choose_repo).pack(side="left")

        self.btn_frame = ttk.LabelFrame(self, text="Git 常用操作", padding=10)
        self.btn_frame.pack(fill="x", padx=10, pady=5)
        self.btn_frame.bind("<Button-3>", self.show_frame_context_menu)

        self.render_buttons()

        output_frame = ttk.Frame(self, padding=10)
        output_frame.pack(fill="both", expand=True)

        self.output = tk.Text(output_frame, wrap="word", font=("Consolas", 11), undo=True)
        self.output.pack(side="left", fill="both", expand=True)

        scrollbar = ttk.Scrollbar(output_frame, command=self.output.yview)
        scrollbar.pack(side="right", fill="y")
        self.output.config(yscrollcommand=scrollbar.set)

        self.output.tag_config("normal_text", foreground="black", underline=False)
        self.output.tag_config("warning_text", foreground="#7a4b00", background="#fff3a3", underline=False)
        self.output.tag_config("error_text", foreground="#b00020", background="#ffd6d6", underline=False)
        self.output.tag_config("status_file_text", foreground="black", font=("Consolas", 11, "bold"), underline=False)
        self.output.tag_config("commit_link", foreground="blue", underline=True)
        self.output.tag_raise("commit_link", "normal_text")
        self.output.tag_raise("commit_link", "warning_text")
        self.output.tag_raise("error_text", "normal_text")
        self.output.tag_raise("commit_link", "warning_text")
        self.output.tag_raise("commit_link", "error_text")
        self.output.tag_raise("commit_link", "status_file_text")

        self.output.tag_bind("commit_link", "<Enter>", self.enter_commit_link)
        self.output.tag_bind("commit_link", "<Leave>", self.leave_commit_link)
        self.output.tag_bind("commit_link", "<Control-Button-1>", self.ctrl_click_commit)

        self.output_menu = tk.Menu(self, tearoff=0)
        self.output_menu.add_command(label="复制", command=self.copy_selected_text)
        self.output_menu.add_command(label="全选", command=self.select_all_output)
        self.output_menu.add_separator()
        self.output_menu.add_command(label="清空输出", command=self.clear_output)

        self.output.bind("<Button-3>", self.show_output_menu)

        bottom_frame = ttk.Frame(self, padding=10)
        bottom_frame.pack(fill="x")

        ttk.Label(bottom_frame, textvariable=self.status_text).pack(side="left", fill="x", expand=True)

        simple_controls = ttk.Frame(bottom_frame)
        simple_controls.pack(side="right")

        self.simple_upload_bottom_button = None

        ttk.Checkbutton(
            simple_controls,
            text="精简模式",
            variable=self.simple_mode_var,
            command=self.toggle_simple_mode
        ).pack(side="left")

    def render_buttons(self):
        for widget in self.btn_frame.winfo_children():
            widget.destroy()

        self.button_key_by_widget.clear()
        self.button_widget_by_key.clear()

        if self.layout_edit_mode:
            self.btn_frame.configure(text="Git 常用操作  ——  布局编辑中：拖动按钮排序，蓝色丨表示插入位置")
            self.edit_layout_button.configure(text="退出编辑布局")
        else:
            self.btn_frame.configure(text="Git 常用操作")
            self.edit_layout_button.configure(text="编辑布局")

        visible_items = [item for item in self.button_layout if item.get("visible", True)]

        if self.simple_mode_var.get():
            # 精简模式保留常用按钮：
            # - 如果当前仓库已有 .gitignore，则“修改忽略文件”放在第一位；
            # - 如果没有 .gitignore，则保留“生成忽略文件”；
            # - “一键上传到 GitHub”只保留一个。
            repo = self.get_repo_silent()
            has_ignore_file = bool(repo and (Path(repo) / ".gitignore").exists())

            has_workflow = bool(repo and self.repo_has_workflows(repo))
            workflow_simple_button = ["edit_workflow"] if has_workflow else []

            if has_ignore_file:
                simple_mode_ids = [
                    "edit_ignore",
                    "simple_upload",
                    "status",
                    "log",
                    "checkout_commit",
                    "restore_files",
                    "checkout_branch",
                    *workflow_simple_button,
                    "clear_output",
                ]
            else:
                simple_mode_ids = [
                    "generate_ignore",
                    "simple_upload",
                    "status",
                    "log",
                    "checkout_commit",
                    "restore_files",
                    "checkout_branch",
                    *workflow_simple_button,
                    "clear_output",
                ]

            picked_ids = set()
            visible_items = []

            for item in self.button_layout:
                action_id = item.get("id")
                is_default_simple_button = action_id in simple_mode_ids
                is_extra_simple_button = bool(item.get("simple_visible", False))

                if (
                    item.get("type") == "builtin"
                    and action_id not in picked_ids
                    and item.get("visible", True)
                    and (is_default_simple_button or is_extra_simple_button)
                ):
                    visible_items.append(item)
                    picked_ids.add(action_id)

            def simple_sort_key(item):
                action_id = item.get("id")
                if action_id in simple_mode_ids:
                    return (0, simple_mode_ids.index(action_id))
                return (1, self.button_layout.index(item))

            visible_items.sort(key=simple_sort_key)
        else:
            visible_items = [
                item for item in visible_items
                if not (item.get("type") == "builtin" and item.get("id") == "simple_upload")
            ]

        if not visible_items:
            ttk.Label(
                self.btn_frame,
                text="当前没有显示的按钮。可在顶部导航栏点击“添加按钮”或“显示隐藏”。"
            ).grid(row=0, column=0, sticky="w")
            return

        for index, item in enumerate(visible_items):
            row = index // self.max_cols
            col = index % self.max_cols
            label_text = self.get_layout_item_label(item)
            key = self.layout_item_key(item)

            btn = ttk.Button(self.btn_frame, text=label_text)
            btn.grid(row=row, column=col, padx=5, pady=5, sticky="ew")

            self.button_key_by_widget[btn] = key
            self.button_widget_by_key[key] = btn

            if self.layout_edit_mode:
                btn.bind("<ButtonPress-1>", lambda event, i=item: self.on_button_press(event, i))
                btn.bind("<B1-Motion>", self.on_button_motion)
                btn.bind("<ButtonRelease-1>", self.on_button_release)
            else:
                btn.configure(command=lambda i=item: self.run_layout_button(i))

            btn.bind("<Button-3>", lambda event, i=item: self.show_button_context_menu(event, i))

        for col in range(self.max_cols):
            self.btn_frame.columnconfigure(col, weight=1)

    def toggle_simple_mode(self):
        is_simple = bool(self.simple_mode_var.get())
        mode_name = "精简模式" if is_simple else "标准模式"

        # 不再弹窗询问是否记住，直接保存当前模式
        self.app_config["remember_simple_mode"] = True
        self.app_config["simple_mode"] = is_simple
        self.save_app_config()

        if is_simple:
            self.status_text.set("已切换到精简模式，并自动记住本次选择")
        else:
            self.status_text.set("已切换到标准模式，并自动记住本次选择")

        self.render_buttons()

    # ============================================================
    # 布局工具
    # ============================================================

    def layout_item_key(self, item):
        return f"{item.get('type')}:{item.get('id')}"

    def get_layout_item_label(self, item):
        if item.get("type") == "builtin":
            # 内置按钮允许用户自定义显示名称，但功能仍然保持原来的内置功能。
            if item.get("label_override"):
                return item.get("label_override")

            action_id = item.get("id")
            action = self.action_registry.get(action_id)
            return action["label"] if action else f"未知按钮：{action_id}"

        if item.get("type") == "custom":
            return item.get("label", "自定义按钮")

        return "未知按钮"

    def run_layout_button(self, item):
        if item.get("type") == "builtin":
            action_id = item.get("id")
            action = self.action_registry.get(action_id)

            if not action:
                messagebox.showerror("错误", f"未知内置按钮：{action_id}")
                return

            method = getattr(self, action["method"], None)

            if not method:
                messagebox.showerror("错误", f"按钮方法不存在：{action['method']}")
                return

            method()
            return

        if item.get("type") == "custom":
            label = item.get("label", "自定义命令")
            command_text = item.get("git_args", "").strip()

            if command_text == "":
                messagebox.showwarning("提示", "该自定义按钮还没有设置 Git 命令")
                return

            args = self.parse_git_args(command_text)
            if not args:
                return

            self.run_git(args, f"自定义命令：{label}")

    def set_builtin_visibility(self, action_id, visible):
        changed = False

        for index, item in enumerate(self.button_layout):
            if item.get("type") == "builtin" and item.get("id") == action_id:
                if visible and item.get("user_hidden"):
                    # 用户手动隐藏过的按钮，不被自动检测逻辑强行重新显示；
                    # 需要用户在“显示隐藏”里手动恢复。
                    return

                if item.get("visible", True) != visible:
                    item["visible"] = visible
                    if visible:
                        item.pop("user_hidden", None)
                    changed = True

                # “克隆仓库”只要显示，就固定移动到第一位，方便非 Git 仓库场景使用。
                if visible and action_id == "clone_repo" and index != 0:
                    moved_item = self.button_layout.pop(index)
                    self.button_layout.insert(0, moved_item)
                    changed = True

                # “添加远程 origin”自动显示时，固定放在“初始化仓库”后面。
                if visible and action_id == "add_remote":
                    current_index = self.find_layout_index_by_key("builtin:add_remote")
                    init_index = self.find_layout_index_by_key("builtin:init")

                    if current_index is not None and init_index is not None:
                        moved_item = self.button_layout.pop(current_index)

                        # 如果 add_remote 原本在 init 前面，pop 后 init 的位置会左移一位，需要重新查找。
                        init_index = self.find_layout_index_by_key("builtin:init")
                        insert_index = init_index + 1 if init_index is not None else len(self.button_layout)

                        if current_index != insert_index:
                            self.button_layout.insert(insert_index, moved_item)
                            changed = True
                        else:
                            self.button_layout.insert(current_index, moved_item)

                break

        if changed:
            self.render_buttons()
            self.save_current_layout_to_config()

    def hide_builtin_if_exists(self, action_id):
        self.set_builtin_visibility(action_id, False)

    def show_builtin_if_exists(self, action_id):
        self.set_builtin_visibility(action_id, True)

    # ============================================================
    # 编辑布局：拖拽排序
    # ============================================================

    def toggle_edit_layout_mode(self):
        self.layout_edit_mode = not self.layout_edit_mode
        self.destroy_drag_ghost()
        self.destroy_insert_marker()
        self.reset_drag_data()

        if self.layout_edit_mode:
            self.status_text.set("已进入布局编辑模式：拖动按钮时，蓝色丨表示插入位置")
        else:
            self.status_text.set("已退出布局编辑模式：左键点击按钮将执行 Git 功能")

        self.render_buttons()

    def reset_drag_data(self):
        self.drag_data = {
            "key": None,
            "item": None,
            "start_x": 0,
            "start_y": 0,
            "dragging": False,
            "widget": None,
        }
        self.current_insert_index = None

    def on_button_press(self, event, item):
        if not self.layout_edit_mode:
            return

        self.drag_data = {
            "key": self.layout_item_key(item),
            "item": item,
            "start_x": event.x_root,
            "start_y": event.y_root,
            "dragging": False,
            "widget": event.widget,
        }
        self.current_insert_index = None

    def on_button_motion(self, event):
        if not self.layout_edit_mode or not self.drag_data["key"]:
            return

        dx = abs(event.x_root - self.drag_data["start_x"])
        dy = abs(event.y_root - self.drag_data["start_y"])

        if dx > 6 or dy > 6:
            if not self.drag_data["dragging"]:
                self.drag_data["dragging"] = True
                self.create_drag_ghost(self.drag_data["item"], event.x_root, event.y_root)

                try:
                    self.drag_data["widget"].configure(cursor="fleur")
                except Exception:
                    pass

            self.move_drag_ghost(event.x_root, event.y_root)

            insert_index, marker_info = self.calculate_insert_position(event.x_root, event.y_root)
            self.current_insert_index = insert_index

            if marker_info:
                marker_x, marker_y, marker_height = marker_info
                self.show_insert_marker(marker_x, marker_y, marker_height)
            else:
                self.destroy_insert_marker()

            self.status_text.set("正在拖动按钮：蓝色丨表示松开后插入的位置")

    def on_button_release(self, event):
        if not self.layout_edit_mode or not self.drag_data["key"]:
            return

        try:
            self.drag_data["widget"].configure(cursor="")
        except Exception:
            pass

        dragged_key = self.drag_data["key"]
        was_dragging = self.drag_data["dragging"]
        insert_index = self.current_insert_index

        self.destroy_drag_ghost()
        self.destroy_insert_marker()
        self.reset_drag_data()

        if not was_dragging:
            self.status_text.set("布局编辑模式中：按住按钮并拖动可以调整位置")
            return

        if insert_index is not None:
            self.move_layout_item_to_visible_index(dragged_key, insert_index)
            self.reflow_buttons_without_recreate()
            self.mark_layout_modified()
            self.status_text.set("按钮位置已按插入方式移动")
        else:
            self.status_text.set("已取消移动按钮")

    def create_drag_ghost(self, item, x_root, y_root):
        self.destroy_drag_ghost()
        label_text = self.get_layout_item_label(item)

        ghost = tk.Toplevel(self)
        ghost.overrideredirect(True)
        ghost.attributes("-topmost", True)

        try:
            ghost.attributes("-alpha", 0.65)
        except Exception:
            pass

        frame = tk.Frame(ghost, bg="#dbeafe", bd=1, relief="solid")
        frame.pack(fill="both", expand=True)

        label = tk.Label(
            frame,
            text=label_text,
            bg="#dbeafe",
            fg="#111827",
            padx=22,
            pady=7,
            font=("Microsoft YaHei UI", 10)
        )
        label.pack()

        self.drag_ghost = ghost
        self.move_drag_ghost(x_root, y_root)

    def move_drag_ghost(self, x_root, y_root):
        if self.drag_ghost is None:
            return

        try:
            self.drag_ghost.geometry(f"+{x_root + 16}+{y_root + 14}")
        except Exception:
            pass

    def destroy_drag_ghost(self):
        if self.drag_ghost is not None:
            try:
                self.drag_ghost.destroy()
            except Exception:
                pass

        self.drag_ghost = None

    def show_insert_marker(self, x_root, y_root, height):
        if self.insert_marker is None:
            marker = tk.Toplevel(self)
            marker.overrideredirect(True)
            marker.attributes("-topmost", True)

            frame = tk.Frame(marker, bg="#2563eb")
            frame.pack(fill="both", expand=True)

            label = tk.Label(
                frame,
                text="丨",
                bg="#2563eb",
                fg="white",
                font=("Microsoft YaHei UI", 18, "bold"),
                padx=1,
                pady=0
            )
            label.pack(fill="both", expand=True)

            self.insert_marker = marker

        marker_height = max(28, height + 8)

        try:
            self.insert_marker.geometry(f"10x{marker_height}+{x_root}+{y_root - 4}")
        except Exception:
            pass

    def destroy_insert_marker(self):
        if self.insert_marker is not None:
            try:
                self.insert_marker.destroy()
            except Exception:
                pass

        self.insert_marker = None

    def calculate_insert_position(self, x_root, y_root):
        visible_items = [item for item in self.button_layout if item.get("visible", True)]
        visible_keys = [self.layout_item_key(item) for item in visible_items]

        widgets = []

        for key in visible_keys:
            widget = self.button_widget_by_key.get(key)
            if not widget:
                continue

            try:
                row = int(widget.grid_info().get("row", 0))
                col = int(widget.grid_info().get("column", 0))
                x1 = widget.winfo_rootx()
                y1 = widget.winfo_rooty()
                width = widget.winfo_width()
                height = widget.winfo_height()
                x2 = x1 + width

                widgets.append({
                    "key": key,
                    "row": row,
                    "col": col,
                    "x1": x1,
                    "x2": x2,
                    "y1": y1,
                    "height": height,
                    "mid_x": x1 + width / 2,
                    "mid_y": y1 + height / 2,
                })

            except Exception:
                pass

        if not widgets:
            frame_x = self.btn_frame.winfo_rootx() + 16
            frame_y = self.btn_frame.winfo_rooty() + 34
            return 0, (frame_x, frame_y, 32)

        rows = {}
        for info in widgets:
            rows.setdefault(info["row"], []).append(info)

        row_infos = []
        for row, items in rows.items():
            items.sort(key=lambda x: x["col"])
            y1 = min(i["y1"] for i in items)
            y2 = max(i["y1"] + i["height"] for i in items)
            row_infos.append({
                "row": row,
                "items": items,
                "mid_y": (y1 + y2) / 2,
            })

        row_infos.sort(key=lambda x: x["row"])
        selected_row = min(row_infos, key=lambda r: abs(y_root - r["mid_y"]))
        row_items = selected_row["items"]

        last_info = row_items[-1]
        insert_index = visible_keys.index(last_info["key"]) + 1
        marker_x = last_info["x2"] + 4
        marker_y = last_info["y1"]
        marker_height = last_info["height"]

        for info in row_items:
            if x_root < info["mid_x"]:
                insert_index = visible_keys.index(info["key"])
                marker_x = info["x1"] - 8
                marker_y = info["y1"]
                marker_height = info["height"]
                break

        return insert_index, (marker_x, marker_y, marker_height)

    def find_layout_index_by_key(self, key):
        for index, item in enumerate(self.button_layout):
            if self.layout_item_key(item) == key:
                return index
        return None

    def move_layout_item_to_visible_index(self, dragged_key, visible_insert_index):
        from_index = self.find_layout_index_by_key(dragged_key)
        if from_index is None:
            return

        dragged_item = self.button_layout.pop(from_index)

        visible_items_after_pop = [item for item in self.button_layout if item.get("visible", True)]

        if not visible_items_after_pop:
            self.button_layout.append(dragged_item)
            return

        if visible_insert_index <= 0:
            first_key = self.layout_item_key(visible_items_after_pop[0])
            first_real_index = self.find_layout_index_by_key(first_key)
            self.button_layout.insert(first_real_index if first_real_index is not None else 0, dragged_item)
            return

        if visible_insert_index >= len(visible_items_after_pop):
            last_key = self.layout_item_key(visible_items_after_pop[-1])
            last_real_index = self.find_layout_index_by_key(last_key)

            if last_real_index is None:
                self.button_layout.append(dragged_item)
            else:
                self.button_layout.insert(last_real_index + 1, dragged_item)
            return

        target_key = self.layout_item_key(visible_items_after_pop[visible_insert_index])
        target_real_index = self.find_layout_index_by_key(target_key)

        if target_real_index is None:
            self.button_layout.append(dragged_item)
        else:
            self.button_layout.insert(target_real_index, dragged_item)

    def reflow_buttons_without_recreate(self):
        visible_items = [item for item in self.button_layout if item.get("visible", True)]

        for index, item in enumerate(visible_items):
            key = self.layout_item_key(item)
            widget = self.button_widget_by_key.get(key)

            if widget is None or not widget.winfo_exists():
                self.render_buttons()
                return

            row = index // self.max_cols
            col = index % self.max_cols
            widget.grid_configure(row=row, column=col, padx=5, pady=5, sticky="ew")

        self.btn_frame.update_idletasks()

    # ============================================================
    # 右键菜单、添加隐藏按钮
    # ============================================================

    def show_button_context_menu(self, event, item):
        menu = tk.Menu(self, tearoff=0)

        menu.add_command(
            label="退出编辑布局" if self.layout_edit_mode else "进入编辑布局",
            command=self.toggle_edit_layout_mode
        )
        menu.add_separator()
        menu.add_command(
            label=f"编辑：{self.get_layout_item_label(item)}",
            command=lambda i=item: self.edit_layout_item(i)
        )

        if item.get("type") == "custom":
            menu.add_command(
                label=f"导出当前自定义按钮",
                command=lambda i=item: self.export_single_custom_button(i)
            )

        menu.add_command(
            label=f"隐藏：{self.get_layout_item_label(item)}",
            command=lambda i=item: self.hide_layout_item(i)
        )
        menu.add_separator()
        menu.add_command(label="添加自定义按钮", command=self.add_custom_button)
        menu.add_command(label="显示隐藏按钮", command=self.show_hidden_buttons_dialog)
        menu.add_command(label="管理布局", command=self.open_layout_manager)
        menu.add_separator()
        menu.add_command(label="导出布局文件", command=self.export_layout)
        menu.add_command(label="导入布局文件", command=self.import_layout)

        try:
            menu.tk_popup(event.x_root, event.y_root)
        finally:
            menu.grab_release()

        return "break"

    def show_frame_context_menu(self, event):
        menu = tk.Menu(self, tearoff=0)

        menu.add_command(
            label="退出编辑布局" if self.layout_edit_mode else "进入编辑布局",
            command=self.toggle_edit_layout_mode
        )
        menu.add_separator()
        menu.add_command(label="添加自定义按钮", command=self.add_custom_button)
        menu.add_command(label="显示隐藏按钮", command=self.show_hidden_buttons_dialog)
        menu.add_command(label="管理布局", command=self.open_layout_manager)
        menu.add_separator()
        menu.add_command(label="每行按钮数量", command=self.set_button_columns)
        menu.add_command(label="导出布局文件", command=self.export_layout)
        menu.add_command(label="导入布局文件", command=self.import_layout)
        menu.add_separator()
        menu.add_command(label="重置布局", command=self.reset_layout)

        try:
            menu.tk_popup(event.x_root, event.y_root)
        finally:
            menu.grab_release()

        return "break"

    def hide_layout_item(self, item):
        index = self.find_layout_index_by_key(self.layout_item_key(item))
        if index is None:
            return

        was_custom = self.button_layout[index].get("type") == "custom"
        self.button_layout[index]["visible"] = False
        self.button_layout[index]["user_hidden"] = True

        if self.simple_mode_var.get():
            self.button_layout[index]["simple_visible"] = False

        self.render_buttons()
        self.mark_layout_modified()

        if was_custom:
            self.mark_custom_buttons_dirty()

        self.status_text.set(f"已隐藏按钮：{self.get_layout_item_label(item)}。顶部导航栏可重新显示。")

    def get_custom_button_items(self):
        return [
            copy.deepcopy(item)
            for item in self.button_layout
            if item.get("type") == "custom"
        ]

    def has_custom_buttons(self):
        return any(item.get("type") == "custom" for item in self.button_layout)

    def set_custom_buttons_exported(self, exported):
        self.app_config["custom_buttons_exported"] = bool(exported)
        self.save_app_config()

    def mark_custom_buttons_dirty(self):
        if self.has_custom_buttons():
            self.app_config["custom_buttons_exported"] = False
        else:
            self.app_config["custom_buttons_exported"] = True

        self.save_app_config()

    def are_custom_buttons_exported(self):
        if not self.has_custom_buttons():
            return True

        return bool(self.app_config.get("custom_buttons_exported", False))

    def add_custom_button(self):
        """
        顶部“添加按钮”入口：
        - 添加单个自定义按钮
        - 批量导入自定义按钮
        - 批量导出自定义按钮
        """
        dialog = tk.Toplevel(self)
        dialog.withdraw()
        dialog.title("添加 / 导入自定义按钮")
        dialog.resizable(False, False)
        dialog.transient(self)
        dialog.grab_set()
        dialog.attributes("-topmost", True)

        result = {"action": None}

        frame = ttk.Frame(dialog, padding=16)
        frame.pack(fill="both", expand=True)

        ttk.Label(
            frame,
            text="请选择要执行的操作：",
            justify="left"
        ).pack(anchor="w", pady=(0, 12))

        def choose(action):
            result["action"] = action
            dialog.destroy()

        ttk.Button(frame, text="添加单个自定义按钮", command=lambda: choose("single")).pack(fill="x", pady=4)
        ttk.Button(frame, text="批量导入自定义按钮", command=lambda: choose("import")).pack(fill="x", pady=4)
        ttk.Button(frame, text="批量导出自定义按钮", command=lambda: choose("export")).pack(fill="x", pady=4)
        ttk.Button(frame, text="取消", command=lambda: choose(None)).pack(fill="x", pady=(12, 0))

        dialog.protocol("WM_DELETE_WINDOW", lambda: choose(None))
        self.center_dialog(dialog, min_width=360, min_height=260)
        self.wait_window(dialog)

        if result["action"] == "single":
            return self.add_single_custom_button()

        if result["action"] == "import":
            return self.import_custom_buttons()

        if result["action"] == "export":
            return self.select_custom_buttons_and_export()

        return False

    def add_single_custom_button(self):
        label = self.ask_text_with_menu("添加自定义按钮", "请输入按钮名称：\n例如：简洁状态")

        if label is None:
            return False

        label = label.strip()
        if label == "":
            messagebox.showwarning("提示", "按钮名称不能为空")
            return False

        command_text = self.ask_text_with_menu(
            "添加自定义按钮",
            "请输入 Git 命令参数，可省略开头的 git：\n例如：status -sb（查看简洁状态）\n例如：log --oneline -n 5（查看最近 5 条日志）"
        )

        if command_text is None:
            return False

        command_text = command_text.strip()
        if command_text == "":
            messagebox.showwarning("提示", "Git 命令不能为空")
            return False

        self.button_layout.append({
            "type": "custom",
            "id": "custom_" + uuid.uuid4().hex[:8],
            "label": label,
            "git_args": command_text,
            "visible": True
        })

        self.render_buttons()
        self.mark_layout_modified()
        self.mark_custom_buttons_dirty()
        self.status_text.set(f"已添加自定义按钮：{label}")
        return True

    def normalize_custom_button_for_import(self, item):
        if not isinstance(item, dict):
            return None

        if item.get("type") != "custom":
            return None

        label = str(item.get("label", "自定义按钮")).strip()
        git_args = str(item.get("git_args", "")).strip()

        if not label or not git_args:
            return None

        return {
            "type": "custom",
            "id": "custom_" + uuid.uuid4().hex[:8],
            "label": label,
            "git_args": git_args,
            "visible": bool(item.get("visible", True))
        }

    def extract_custom_buttons_from_data(self, data):
        source_items = []

        if isinstance(data, dict):
            if data.get("type") == "custom":
                source_items = [data]
            elif isinstance(data.get("custom_buttons"), list):
                source_items = data.get("custom_buttons", [])
            elif isinstance(data.get("layout"), list):
                source_items = [
                    item for item in data.get("layout", [])
                    if isinstance(item, dict) and item.get("type") == "custom"
                ]
        elif isinstance(data, list):
            source_items = [
                item for item in data
                if isinstance(item, dict) and item.get("type") == "custom"
            ]

        result = []

        for item in source_items:
            normalized = self.normalize_custom_button_for_import(item)

            if normalized is not None:
                result.append(normalized)

        return result

    def safe_export_filename(self, name, suffix=".json"):
        safe_name = re.sub(r'[<>:"/\\|?*\s]+', "_", str(name).strip())
        safe_name = safe_name.strip("._")

        if not safe_name:
            safe_name = "custom_button"

        return safe_name + suffix

    def make_custom_button_export_data(self, custom_buttons):
        return {
            "version": 1,
            "export_type": "custom_buttons",
            "custom_buttons": copy.deepcopy(custom_buttons)
        }

    def read_json_config_entries(self, file_path):
        """
        支持读取：
        1. 普通 JSON 配置文件；
        2. ZIP 压缩包文件，内部可包含一个或多个 JSON 配置文件。
        """
        path = Path(file_path)
        entries = []

        if path.suffix.lower() == ".zip":
            with zipfile.ZipFile(path, "r") as zf:
                for name in zf.namelist():
                    if name.endswith("/") or not name.lower().endswith(".json"):
                        continue

                    with zf.open(name, "r") as f:
                        raw = f.read()

                    text = raw.decode("utf-8-sig")
                    entries.append({
                        "name": name,
                        "data": json.loads(text)
                    })
            return entries

        with open(path, "r", encoding="utf-8-sig") as f:
            entries.append({
                "name": path.name,
                "data": json.load(f)
            })

        return entries

    def import_custom_buttons(self):
        file_path = filedialog.askopenfilename(
            title="批量导入自定义按钮",
            filetypes=[
                ("JSON / ZIP 配置文件", "*.json *.zip"),
                ("JSON 配置文件", "*.json"),
                ("ZIP 压缩包文件", "*.zip")
            ]
        )

        if not file_path:
            return False

        try:
            entries = self.read_json_config_entries(file_path)
            custom_buttons = []

            for entry in entries:
                custom_buttons.extend(self.extract_custom_buttons_from_data(entry["data"]))

            if not custom_buttons:
                messagebox.showwarning("提示", "该文件中没有可导入的自定义按钮")
                return False

            # 批量导入后，默认追加在最后。
            self.button_layout.extend(custom_buttons)

            self.render_buttons()
            self.mark_layout_modified()
            self.set_custom_buttons_exported(True)

            self.status_text.set(f"已导入 {len(custom_buttons)} 个自定义按钮")
            messagebox.showinfo("成功", f"已导入 {len(custom_buttons)} 个自定义按钮。\n导入后位置已追加到最后。")
            return True

        except Exception as e:
            messagebox.showerror("错误", f"导入自定义按钮失败：\n{e}")
            return False

    def export_custom_buttons(self, custom_buttons=None, title="批量导出自定义按钮"):
        if custom_buttons is None:
            custom_buttons = self.get_custom_button_items()
        else:
            custom_buttons = [copy.deepcopy(item) for item in custom_buttons if item.get("type") == "custom"]

        if not custom_buttons:
            messagebox.showinfo("提示", "当前没有自定义按钮可导出")
            return False

        file_path = filedialog.asksaveasfilename(
            title=title,
            defaultextension=".json",
            filetypes=[("JSON 配置文件", "*.json")]
        )

        if not file_path:
            return False

        data = self.make_custom_button_export_data(custom_buttons)

        try:
            with open(file_path, "w", encoding="utf-8") as f:
                json.dump(data, f, ensure_ascii=False, indent=4)

            self.set_custom_buttons_exported(True)
            messagebox.showinfo("成功", f"自定义按钮已导出：\n{file_path}")
            return True

        except Exception as e:
            messagebox.showerror("错误", f"导出自定义按钮失败：\n{e}")
            return False

    def export_single_custom_button(self, item):
        key = self.layout_item_key(item)
        index = self.find_layout_index_by_key(key)

        if index is None:
            messagebox.showerror("错误", "没有找到当前自定义按钮")
            return False

        real_item = self.button_layout[index]

        if real_item.get("type") != "custom":
            messagebox.showinfo("提示", "只有自定义按钮可以单独导出")
            return False

        initial_file = self.safe_export_filename(real_item.get("label", "custom_button"))

        file_path = filedialog.asksaveasfilename(
            title="导出当前自定义按钮",
            initialfile=initial_file,
            defaultextension=".json",
            filetypes=[("JSON 配置文件", "*.json")]
        )

        if not file_path:
            return False

        data = self.make_custom_button_export_data([real_item])

        try:
            with open(file_path, "w", encoding="utf-8") as f:
                json.dump(data, f, ensure_ascii=False, indent=4)

            self.set_custom_buttons_exported(True)
            messagebox.showinfo("成功", f"当前自定义按钮已导出：\n{file_path}")
            return True

        except Exception as e:
            messagebox.showerror("错误", f"导出当前自定义按钮失败：\n{e}")
            return False

    def export_custom_buttons_as_separate_files(self, custom_buttons=None):
        if custom_buttons is None:
            custom_buttons = self.get_custom_button_items()
        else:
            custom_buttons = [copy.deepcopy(item) for item in custom_buttons if item.get("type") == "custom"]

        if not custom_buttons:
            messagebox.showinfo("提示", "没有可导出的自定义按钮")
            return False

        folder = filedialog.askdirectory(title="选择导出文件夹")

        if not folder:
            return False

        folder_path = Path(folder)
        used_names = set()

        try:
            for item in custom_buttons:
                base_name = self.safe_export_filename(item.get("label", "custom_button"))
                file_name = base_name
                stem = Path(base_name).stem
                suffix = Path(base_name).suffix
                counter = 2

                while file_name.lower() in used_names or (folder_path / file_name).exists():
                    file_name = f"{stem}_{counter}{suffix}"
                    counter += 1

                used_names.add(file_name.lower())

                data = self.make_custom_button_export_data([item])

                with open(folder_path / file_name, "w", encoding="utf-8") as f:
                    json.dump(data, f, ensure_ascii=False, indent=4)

            self.set_custom_buttons_exported(True)
            messagebox.showinfo("成功", f"已分开导出 {len(custom_buttons)} 个自定义按钮到：\n{folder_path}")
            return True

        except Exception as e:
            messagebox.showerror("错误", f"分开导出自定义按钮失败：\n{e}")
            return False

    def export_custom_buttons_to_zip(self, custom_buttons=None):
        if custom_buttons is None:
            custom_buttons = self.get_custom_button_items()
        else:
            custom_buttons = [copy.deepcopy(item) for item in custom_buttons if item.get("type") == "custom"]

        if not custom_buttons:
            messagebox.showinfo("提示", "没有可导出的自定义按钮")
            return False

        file_path = filedialog.asksaveasfilename(
            title="导出自定义按钮到压缩包",
            initialfile="custom_buttons.zip",
            defaultextension=".zip",
            filetypes=[("ZIP 压缩包文件", "*.zip")]
        )

        if not file_path:
            return False

        used_names = set()

        try:
            with zipfile.ZipFile(file_path, "w", compression=zipfile.ZIP_DEFLATED) as zf:
                for item in custom_buttons:
                    base_name = self.safe_export_filename(item.get("label", "custom_button"))
                    file_name = base_name
                    stem = Path(base_name).stem
                    suffix = Path(base_name).suffix
                    counter = 2

                    while file_name.lower() in used_names:
                        file_name = f"{stem}_{counter}{suffix}"
                        counter += 1

                    used_names.add(file_name.lower())

                    data = self.make_custom_button_export_data([item])
                    zf.writestr(file_name, json.dumps(data, ensure_ascii=False, indent=4))

            self.set_custom_buttons_exported(True)
            messagebox.showinfo("成功", f"已将 {len(custom_buttons)} 个自定义按钮分开导出到压缩包：\n{file_path}")
            return True

        except Exception as e:
            messagebox.showerror("错误", f"导出压缩包失败：\n{e}")
            return False

    def select_custom_buttons_and_export(self):
        """
        批量导出自定义按钮时，先让用户选择要导出的按钮，再选择导出方式。
        """
        custom_items = [
            item for item in self.button_layout
            if item.get("type") == "custom"
        ]

        if not custom_items:
            messagebox.showinfo("提示", "当前没有自定义按钮可导出")
            return False

        dialog = tk.Toplevel(self)
        dialog.withdraw()
        dialog.title("选择要导出的自定义按钮")
        dialog.resizable(True, True)
        dialog.transient(self)
        dialog.grab_set()
        dialog.attributes("-topmost", True)

        result = {"items": None}

        frame = ttk.Frame(dialog, padding=12)
        frame.pack(fill="both", expand=True)

        ttk.Label(
            frame,
            text="请选择需要导出的自定义按钮，可按 Ctrl 或 Shift 多选：",
            justify="left"
        ).pack(anchor="w", pady=(0, 8))

        list_frame = ttk.Frame(frame)
        list_frame.pack(fill="both", expand=True, pady=(0, 10))

        listbox = tk.Listbox(
            list_frame,
            selectmode="extended",
            font=("Microsoft YaHei UI", 10)
        )
        listbox.grid(row=0, column=0, sticky="nsew")

        y_scroll = ttk.Scrollbar(list_frame, orient="vertical", command=listbox.yview)
        y_scroll.grid(row=0, column=1, sticky="ns")
        listbox.configure(yscrollcommand=y_scroll.set)

        list_frame.rowconfigure(0, weight=1)
        list_frame.columnconfigure(0, weight=1)

        for item in custom_items:
            label = item.get("label", "自定义按钮")
            git_args = item.get("git_args", "")
            listbox.insert("end", f"{label}    git {git_args}")

        # 默认全选，方便一次性全部导出
        listbox.selection_set(0, "end")

        btn_frame = ttk.Frame(frame)
        btn_frame.pack(fill="x")

        def select_all():
            listbox.selection_set(0, "end")

        def clear_selection():
            listbox.selection_clear(0, "end")

        def ok():
            selections = listbox.curselection()

            if not selections:
                messagebox.showwarning("提示", "请至少选择一个自定义按钮")
                return

            result["items"] = [
                copy.deepcopy(custom_items[index])
                for index in selections
            ]
            dialog.destroy()

        def cancel():
            result["items"] = None
            dialog.destroy()

        ttk.Button(btn_frame, text="全选", command=select_all).pack(side="left", padx=(0, 8))
        ttk.Button(btn_frame, text="清空选择", command=clear_selection).pack(side="left", padx=(0, 8))
        ttk.Button(btn_frame, text="下一步", command=ok).pack(side="left", padx=(0, 8))
        ttk.Button(btn_frame, text="取消", command=cancel).pack(side="left")

        dialog.protocol("WM_DELETE_WINDOW", cancel)
        self.center_dialog(dialog, min_width=720, min_height=440)
        self.wait_window(dialog)

        if not result["items"]:
            return False

        return self.ask_export_custom_buttons_mode(result["items"])

    def ask_export_custom_buttons_mode(self, custom_buttons):
        if not custom_buttons:
            messagebox.showinfo("提示", "没有可导出的自定义按钮")
            return False

        dialog = tk.Toplevel(self)
        dialog.withdraw()
        dialog.title("导出自定义按钮")
        dialog.resizable(False, False)
        dialog.transient(self)
        dialog.grab_set()
        dialog.attributes("-topmost", True)

        result = {"mode": None}

        frame = ttk.Frame(dialog, padding=16)
        frame.pack(fill="both", expand=True)

        ttk.Label(
            frame,
            text=f"已选择 {len(custom_buttons)} 个自定义按钮。\n\n请选择导出方式：",
            justify="left"
        ).pack(anchor="w", pady=(0, 12))

        def choose(mode):
            result["mode"] = mode
            dialog.destroy()

        ttk.Button(frame, text="合并导出为一个 JSON 配置文件", command=lambda: choose("one_json")).pack(fill="x", pady=4)
        ttk.Button(frame, text="分开导出为多个 JSON 配置文件", command=lambda: choose("separate_json")).pack(fill="x", pady=4)
        ttk.Button(frame, text="分开导出到一个 ZIP 压缩包文件文件", command=lambda: choose("zip")).pack(fill="x", pady=4)
        ttk.Button(frame, text="取消", command=lambda: choose(None)).pack(fill="x", pady=(12, 0))

        dialog.protocol("WM_DELETE_WINDOW", lambda: choose(None))
        self.center_dialog(dialog, min_width=430, min_height=300)
        self.wait_window(dialog)

        if result["mode"] == "one_json":
            return self.export_custom_buttons(custom_buttons, "导出选中的自定义按钮")

        if result["mode"] == "separate_json":
            return self.export_custom_buttons_as_separate_files(custom_buttons)

        if result["mode"] == "zip":
            return self.export_custom_buttons_to_zip(custom_buttons)

        return False

    def edit_layout_item(self, item):
        """
        所有按钮都可以编辑并保存：
        - 内置按钮：可修改显示名称，功能保持内置功能不变；
        - 自定义按钮：可修改显示名称和 Git 命令。
        """
        key = self.layout_item_key(item)
        index = self.find_layout_index_by_key(key)

        if index is None:
            messagebox.showerror("错误", "没有找到要编辑的按钮")
            return False

        real_item = self.button_layout[index]

        if real_item.get("type") == "builtin":
            old_label = self.get_layout_item_label(real_item)
            new_label = self.ask_text_with_menu(
                "编辑内置按钮",
                "请输入按钮显示名称：\n说明：内置按钮只能修改显示名称，不能修改内置功能。",
                old_label
            )

            if new_label is None:
                return False

            new_label = new_label.strip()

            if new_label == "":
                messagebox.showwarning("提示", "按钮名称不能为空")
                return False

            default_label = self.action_registry.get(real_item.get("id"), {}).get("label", "")

            if new_label == default_label:
                real_item.pop("label_override", None)
            else:
                real_item["label_override"] = new_label

            self.render_buttons()
            self.mark_layout_modified()
            self.status_text.set(f"已保存按钮名称：{new_label}")
            return True

        if real_item.get("type") == "custom":
            old_label = real_item.get("label", "自定义按钮")
            old_args = real_item.get("git_args", "")

            new_label = self.ask_text_with_menu(
                "编辑自定义按钮",
                "请输入按钮显示名称：",
                old_label
            )

            if new_label is None:
                return False

            new_label = new_label.strip()

            if new_label == "":
                messagebox.showwarning("提示", "按钮名称不能为空")
                return False

            new_args = self.ask_text_with_menu(
                "编辑自定义按钮",
                "请输入 Git 命令参数，可省略开头的 git：",
                old_args
            )

            if new_args is None:
                return False

            new_args = new_args.strip()

            if new_args == "":
                messagebox.showwarning("提示", "Git 命令不能为空")
                return False

            real_item["label"] = new_label
            real_item["git_args"] = new_args

            self.render_buttons()
            self.mark_layout_modified()
            self.mark_custom_buttons_dirty()
            self.status_text.set(f"已保存自定义按钮：{new_label}")
            return True

        messagebox.showerror("错误", "未知按钮类型")
        return False

    def get_simple_mode_default_ids(self):
        repo = self.get_repo_silent()
        has_ignore_file = bool(repo and (Path(repo) / ".gitignore").exists())
        has_workflow = bool(repo and self.repo_has_workflows(repo))

        ids = [
            "edit_ignore" if has_ignore_file else "generate_ignore",
            "simple_upload",
            "status",
            "log",
            "checkout_commit",
            "restore_files",
            "checkout_branch",
        ]

        # 精简模式默认隐藏“一键创建工作流”；
        # 如果仓库已经存在工作流，则默认显示“编辑工作流文件”。
        if has_workflow:
            ids.append("edit_workflow")

        ids.append("clear_output")
        return ids

    def get_items_available_to_show(self):
        if not self.simple_mode_var.get():
            return [item for item in self.button_layout if not item.get("visible", True)]

        simple_default_ids = set(self.get_simple_mode_default_ids())
        result = []
        seen_keys = set()

        for item in self.button_layout:
            key = self.layout_item_key(item)
            action_id = item.get("id")
            is_hidden_normally = not item.get("visible", True)
            is_hidden_in_simple = (
                item.get("type") == "builtin"
                and item.get("visible", True)
                and action_id not in simple_default_ids
                and not item.get("simple_visible", False)
            )

            if (is_hidden_normally or is_hidden_in_simple) and key not in seen_keys:
                result.append(item)
                seen_keys.add(key)

        return result

    def show_hidden_buttons_dialog(self):
        hidden_items = self.get_items_available_to_show()

        if not hidden_items:
            messagebox.showinfo("提示", "当前没有可显示的隐藏按钮")
            return

        dialog = tk.Toplevel(self)
        dialog.withdraw()
        dialog.title("显示隐藏按钮")
        dialog.geometry("560x420")
        dialog.transient(self)
        dialog.grab_set()

        frame = ttk.Frame(dialog, padding=10)
        frame.pack(fill="both", expand=True)

        if self.simple_mode_var.get():
            tip = "精简模式：可恢复隐藏按钮，也可把标准模式按钮添加到精简模式中。"
        else:
            tip = "选择要重新显示的按钮："

        ttk.Label(frame, text=tip).pack(anchor="w", pady=(0, 8))

        list_frame = ttk.Frame(frame)
        list_frame.pack(fill="both", expand=True)

        listbox = tk.Listbox(list_frame, selectmode="extended")
        listbox.pack(side="left", fill="both", expand=True)

        scrollbar = ttk.Scrollbar(list_frame, command=listbox.yview)
        scrollbar.pack(side="right", fill="y")
        listbox.config(yscrollcommand=scrollbar.set)

        simple_default_ids = set(self.get_simple_mode_default_ids()) if self.simple_mode_var.get() else set()

        for item in hidden_items:
            label = self.get_layout_item_label(item)

            if self.simple_mode_var.get() and item.get("type") == "builtin":
                action_id = item.get("id")
                if item.get("visible", True) and action_id not in simple_default_ids:
                    label += "  （标准模式按钮，添加到精简模式）"
                elif not item.get("visible", True):
                    label += "  （已隐藏）"

            listbox.insert("end", label)

        btn_frame = ttk.Frame(frame)
        btn_frame.pack(fill="x", pady=(10, 0))

        def show_items_by_keys(selected_keys):
            for key in selected_keys:
                index = self.find_layout_index_by_key(key)

                if index is not None:
                    item = self.button_layout.pop(index)
                    item["visible"] = True
                    item.pop("user_hidden", None)

                    if self.simple_mode_var.get() and item.get("type") == "builtin":
                        simple_default_ids_now = set(self.get_simple_mode_default_ids())
                        if item.get("id") not in simple_default_ids_now:
                            item["simple_visible"] = True

                    self.button_layout.append(item)

            self.render_buttons()
            self.mark_layout_modified()
            dialog.destroy()

        def show_selected():
            selections = listbox.curselection()

            if not selections:
                messagebox.showinfo("提示", "请先选择要显示的按钮")
                return

            selected_keys = [
                self.layout_item_key(hidden_items[selected])
                for selected in selections
            ]

            show_items_by_keys(selected_keys)

        def show_all():
            hidden_keys = [
                self.layout_item_key(item)
                for item in hidden_items
            ]
            show_items_by_keys(hidden_keys)

        ttk.Button(btn_frame, text="显示选中", command=show_selected).pack(side="left", padx=(0, 8))
        ttk.Button(btn_frame, text="显示全部", command=show_all).pack(side="left", padx=(0, 8))
        ttk.Button(btn_frame, text="关闭", command=dialog.destroy).pack(side="left")

        dialog.protocol("WM_DELETE_WINDOW", dialog.destroy)
        self.center_dialog(dialog, min_width=560, min_height=420)

    # ============================================================
    # 布局管理
    # ============================================================

    def open_layout_manager(self):
        manager = tk.Toplevel(self)
        manager.withdraw()
        manager.title("管理按钮布局")
        manager.geometry("760x480")
        manager.transient(self)

        main_frame = ttk.Frame(manager, padding=10)
        main_frame.pack(fill="both", expand=True)

        left_frame = ttk.Frame(main_frame)
        left_frame.pack(side="left", fill="both", expand=True)

        listbox = tk.Listbox(left_frame, font=("Microsoft YaHei UI", 10), selectmode="extended")
        listbox.pack(side="left", fill="both", expand=True)

        scrollbar = ttk.Scrollbar(left_frame, command=listbox.yview)
        scrollbar.pack(side="right", fill="y")
        listbox.config(yscrollcommand=scrollbar.set)

        right_frame = ttk.Frame(main_frame)
        right_frame.pack(side="right", fill="y", padx=(10, 0))

        def refresh_listbox():
            listbox.delete(0, "end")
            for item in self.button_layout:
                listbox.insert("end", self.format_layout_item(item))

        def get_selected_index():
            selection = listbox.curselection()
            if not selection:
                messagebox.showinfo("提示", "请先选择一个按钮")
                return None
            return selection[0]

        def move_selected(delta):
            index = get_selected_index()
            if index is None:
                return

            new_index = index + delta
            if new_index < 0 or new_index >= len(self.button_layout):
                return

            self.button_layout[index], self.button_layout[new_index] = (
                self.button_layout[new_index],
                self.button_layout[index]
            )

            refresh_listbox()
            listbox.selection_set(new_index)
            self.render_buttons()
            self.mark_layout_modified()

        def toggle_visible():
            index = get_selected_index()
            if index is None:
                return

            item = self.button_layout[index]
            item["visible"] = not item.get("visible", True)

            if item.get("visible", True):
                item.pop("user_hidden", None)
            else:
                item["user_hidden"] = True
                item["simple_visible"] = False

            refresh_listbox()
            listbox.selection_set(index)
            self.render_buttons()
            self.mark_layout_modified()

        def edit_custom_button():
            index = get_selected_index()
            if index is None:
                return

            item = self.button_layout[index]

            if self.edit_layout_item(item):
                refresh_listbox()
                listbox.selection_set(index)

        def delete_custom_button():
            index = get_selected_index()
            if index is None:
                return

            item = self.button_layout[index]
            if item.get("type") != "custom":
                messagebox.showinfo("提示", "内置按钮不能删除，如果不想显示可以点击“显示/隐藏”")
                return

            confirm = messagebox.askyesno("确认删除", f"确定要删除自定义按钮：{item.get('label', '')} 吗？")
            if not confirm:
                return

            del self.button_layout[index]
            refresh_listbox()
            self.render_buttons()
            self.mark_layout_modified()
            self.mark_custom_buttons_dirty()

        def add_custom_and_refresh():
            if self.add_custom_button():
                refresh_listbox()

        def import_and_refresh():
            self.import_layout()
            refresh_listbox()

        def export_selected_custom_buttons():
            selections = listbox.curselection()

            if not selections:
                messagebox.showinfo("提示", "请先选择一个或多个自定义按钮")
                return

            selected_custom_buttons = []

            for selected in selections:
                item = self.button_layout[selected]
                if item.get("type") == "custom":
                    selected_custom_buttons.append(copy.deepcopy(item))

            if not selected_custom_buttons:
                messagebox.showinfo("提示", "选中的项目中没有自定义按钮")
                return

            self.ask_export_custom_buttons_mode(selected_custom_buttons)

        ttk.Button(right_frame, text="上移", command=lambda: move_selected(-1)).pack(fill="x", pady=4)
        ttk.Button(right_frame, text="下移", command=lambda: move_selected(1)).pack(fill="x", pady=4)
        ttk.Button(right_frame, text="显示 / 隐藏", command=toggle_visible).pack(fill="x", pady=4)

        ttk.Separator(right_frame).pack(fill="x", pady=8)

        ttk.Button(right_frame, text="添加自定义按钮", command=add_custom_and_refresh).pack(fill="x", pady=4)
        ttk.Button(right_frame, text="编辑按钮", command=edit_custom_button).pack(fill="x", pady=4)
        ttk.Button(right_frame, text="导出选中自定义按钮", command=export_selected_custom_buttons).pack(fill="x", pady=4)
        ttk.Button(right_frame, text="删除自定义按钮", command=delete_custom_button).pack(fill="x", pady=4)

        ttk.Separator(right_frame).pack(fill="x", pady=8)

        ttk.Button(right_frame, text="导出布局", command=self.export_layout).pack(fill="x", pady=4)
        ttk.Button(right_frame, text="导入布局", command=import_and_refresh).pack(fill="x", pady=4)
        ttk.Button(right_frame, text="关闭", command=manager.destroy).pack(fill="x", pady=4)

        refresh_listbox()
        self.center_dialog(manager, min_width=760, min_height=480)

    def format_layout_item(self, item):
        visible_text = "显示" if item.get("visible", True) else "隐藏"

        if item.get("type") == "builtin":
            action_id = item.get("id")
            label = self.get_layout_item_label(item)
            return f"[{visible_text}] 内置按钮：{label}    ID={action_id}"

        if item.get("type") == "custom":
            label = item.get("label", "自定义按钮")
            command_text = item.get("git_args", "")
            return f"[{visible_text}] 自定义按钮：{label}    git {command_text}"

        return f"[{visible_text}] 未知按钮"

    def set_button_columns(self):
        value = self.ask_text_with_menu("设置每行按钮数量", "请输入每行显示几个按钮：\n建议 3、4、5、6", str(self.max_cols))

        if value is None:
            return

        value = value.strip()
        if value == "":
            messagebox.showwarning("提示", "每行按钮数量不能为空")
            return

        try:
            number = int(value)
        except ValueError:
            messagebox.showerror("错误", "请输入数字")
            return

        if number < 1 or number > 10:
            messagebox.showerror("错误", "按钮数量建议设置在 1 到 10 之间")
            return

        self.max_cols = number
        self.render_buttons()
        self.mark_layout_modified()

    def ask_layout_export_mode(self):
        if not self.has_custom_buttons():
            return "layout_only"

        dialog = tk.Toplevel(self)
        dialog.withdraw()
        dialog.title("导出布局")
        dialog.resizable(False, False)
        dialog.transient(self)
        dialog.grab_set()
        dialog.attributes("-topmost", True)

        result = {"mode": None}

        frame = ttk.Frame(dialog, padding=16)
        frame.pack(fill="both", expand=True)

        ttk.Label(
            frame,
            text="当前布局中包含自定义按钮。\n\n请选择导出方式：",
            justify="left"
        ).pack(anchor="w", pady=(0, 12))

        def choose(mode):
            result["mode"] = mode
            dialog.destroy()

        ttk.Button(frame, text="仅导出按钮布局", command=lambda: choose("layout_only")).pack(fill="x", pady=4)
        ttk.Button(frame, text="仅导出自定义按钮", command=lambda: choose("custom_only")).pack(fill="x", pady=4)
        ttk.Button(frame, text="导出布局 + 自定义按钮到同一文件", command=lambda: choose("layout_with_custom")).pack(fill="x", pady=4)
        ttk.Button(frame, text="取消", command=lambda: choose(None)).pack(fill="x", pady=(12, 0))

        dialog.protocol("WM_DELETE_WINDOW", lambda: choose(None))
        self.center_dialog(dialog, min_width=430, min_height=260)
        self.wait_window(dialog)

        return result["mode"]

    def export_layout(self, show_mode_dialog=True):
        # 导出布局时，先让用户选择：
        # 1. 仅导出按钮布局
        # 2. 仅导出自定义按钮
        # 3. 导出布局 + 自定义按钮到同一文件
        export_mode = self.ask_layout_export_mode()

        if export_mode is None:
            return False

        if export_mode == "custom_only":
            # “仅导出自定义按钮”也先让用户选择具体要导出的按钮。
            return self.select_custom_buttons_and_export()

        file_path = filedialog.asksaveasfilename(
            title="导出按钮布局",
            defaultextension=".json",
            filetypes=[("JSON 配置文件", "*.json")]
        )

        if not file_path:
            return False

        data = {
            "version": 1,
            "export_type": "layout",
            "max_cols": self.max_cols,
            "layout_edit_mode": False,
            "layout": self.button_layout
        }

        if export_mode == "layout_with_custom":
            data["export_type"] = "layout_with_custom_buttons"
            data["custom_buttons"] = self.get_custom_button_items()

        try:
            with open(file_path, "w", encoding="utf-8") as f:
                json.dump(data, f, ensure_ascii=False, indent=4)

            self.layout_modified = False

            if export_mode == "layout_with_custom":
                self.set_custom_buttons_exported(True)

            messagebox.showinfo("成功", f"布局已导出：\n{file_path}")
            return True

        except Exception as e:
            messagebox.showerror("错误", f"导出失败：\n{e}")
            return False

    def import_layout(self):
        file_path = filedialog.askopenfilename(
            title="导入按钮布局 / 自定义按钮",
            filetypes=[
                ("JSON / ZIP 配置文件", "*.json *.zip"),
                ("JSON 配置文件", "*.json"),
                ("ZIP 压缩包文件", "*.zip")
            ]
        )

        if not file_path:
            return

        try:
            entries = self.read_json_config_entries(file_path)

            layout_entries = []
            custom_buttons = []

            for entry in entries:
                data = entry["data"]

                if isinstance(data, dict) and isinstance(data.get("layout"), list):
                    layout_entries.append(data)

                custom_buttons.extend(self.extract_custom_buttons_from_data(data))

            if layout_entries:
                data = layout_entries[0]
                layout = data.get("layout", [])
                max_cols = data.get("max_cols", self.max_cols)

                self.load_layout_from_data(layout, max_cols, show_message=False)

                if custom_buttons:
                    self.set_custom_buttons_exported(True)

                self.mark_layout_modified()

                extra_text = ""
                if len(layout_entries) > 1:
                    extra_text = f"\n注意：压缩包中检测到 {len(layout_entries)} 个布局文件，仅导入第一个布局。"

                messagebox.showinfo("成功", f"布局已导入：\n{file_path}{extra_text}")
                return

            if custom_buttons:
                self.button_layout.extend(custom_buttons)
                self.render_buttons()
                self.mark_layout_modified()
                self.set_custom_buttons_exported(True)
                messagebox.showinfo("成功", f"已导入 {len(custom_buttons)} 个自定义按钮。\n导入后位置已追加到最后。")
                return

            messagebox.showwarning("提示", "该文件或压缩包中没有可导入的按钮布局或自定义按钮")

        except Exception as e:
            messagebox.showerror("错误", f"导入失败：\n{e}")

    def normalize_layout(self, layout):
        new_layout = []
        existing_builtin_ids = set()
        existing_custom_ids = set()

        for item in layout:
            if not isinstance(item, dict):
                continue

            item_type = item.get("type")

            if item_type == "builtin":
                action_id = item.get("id")

                if action_id in self.action_registry and action_id not in existing_builtin_ids:
                    existing_builtin_ids.add(action_id)
                    new_item = {
                        "type": "builtin",
                        "id": action_id,
                        "visible": bool(item.get("visible", True))
                    }

                    if item.get("label_override"):
                        new_item["label_override"] = str(item.get("label_override"))

                    if item.get("simple_visible"):
                        new_item["simple_visible"] = True

                    if item.get("user_hidden"):
                        new_item["user_hidden"] = True

                    new_layout.append(new_item)

            elif item_type == "custom":
                label = str(item.get("label", "自定义按钮"))
                git_args = str(item.get("git_args", ""))

                custom_id = item.get("id", "custom_" + uuid.uuid4().hex[:8])
                if custom_id in existing_custom_ids:
                    custom_id = "custom_" + uuid.uuid4().hex[:8]

                existing_custom_ids.add(custom_id)

                new_layout.append({
                    "type": "custom",
                    "id": custom_id,
                    "label": label,
                    "git_args": git_args,
                    "visible": bool(item.get("visible", True))
                })

        for action_id in self.action_registry.keys():
            if action_id not in existing_builtin_ids:
                existing_builtin_ids.add(action_id)
                new_layout.append({
                    "type": "builtin",
                    "id": action_id,
                    "visible": self.is_action_default_visible(action_id)
                })

        return new_layout

    def reset_layout(self):
        if self.has_custom_buttons() and not self.are_custom_buttons_exported():
            choice = messagebox.askyesnocancel(
                "导出自定义按钮",
                "检测到当前存在尚未导出的自定义按钮。\n\n"
                "重置布局会清空自定义按钮，是否先导出自定义按钮？\n\n"
                "选择“是”：先导出自定义按钮\n"
                "选择“否”：不导出并继续重置\n"
                "选择“取消”：取消重置布局"
            )

            if choice is None:
                return

            if choice:
                exported = self.export_custom_buttons()

                if not exported:
                    return

        confirm = messagebox.askyesno("重置布局", "确定要重置按钮布局吗？\n自定义按钮会被清空。")

        if not confirm:
            return

        self.layout_edit_mode = False
        self.destroy_drag_ghost()
        self.destroy_insert_marker()
        self.reset_drag_data()
        self.button_layout = copy.deepcopy(self.default_button_layout)
        self.max_cols = 5
        self.set_custom_buttons_exported(True)
        self.render_buttons()
        self.mark_layout_modified()

    def reset_popup_choices(self):
        """
        初始化所有弹窗选择：
        - 启动时是否打开上次路径
        - 启动时是否加载上次布局

        不删除上次路径和上次布局本身，只恢复为“下次启动继续询问”的默认状态。
        """
        confirm = messagebox.askyesno(
            "初始化弹窗选择",
            "确定要恢复所有弹窗选择到默认状态吗？\n\n"
            "恢复后，下次启动软件时会重新询问：\n"
            "1. 是否打开上次文件路径\n"
            "2. 是否加载上一次布局\n\n"
            "注意：不会删除已保存的上次路径和布局。"
        )

        if not confirm:
            return

        self.app_config["suppress_load_repo_prompt"] = False
        self.app_config["auto_load_last_repo_path"] = False
        self.app_config["suppress_load_layout_prompt"] = False
        self.app_config["auto_load_last_layout"] = False

        # 模式恢复到默认精简模式；之后仍会自动记住关闭软件时的模式
        self.app_config["remember_simple_mode"] = True
        self.app_config["simple_mode"] = True
        self.simple_mode_var.set(True)

        self.save_app_config()
        self.render_buttons()
        self.status_text.set("已初始化弹窗选择，模式已恢复为默认精简模式")
        messagebox.showinfo(
            "完成",
            "弹窗选择已恢复为默认状态。\n"
            "模式已恢复为默认精简模式。\n"
            "以后关闭软件时会自动记住当前模式，不再弹窗询问。"
        )

    # ============================================================
    # 自定义输入框
    # ============================================================

    def ask_text_with_menu(self, title, prompt, default_text=""):
        dialog = tk.Toplevel(self)
        dialog.withdraw()
        dialog.title(title)
        dialog.resizable(False, False)
        dialog.transient(self)
        dialog.grab_set()
        dialog.attributes("-topmost", True)

        result = {"value": None}

        frame = ttk.Frame(dialog, padding=15)
        frame.pack(fill="both", expand=True)

        ttk.Label(frame, text=prompt, justify="left").pack(anchor="w", pady=(0, 8))

        entry_var = tk.StringVar(value=default_text)
        entry = ttk.Entry(frame, textvariable=entry_var, width=56)
        entry.pack(fill="x", pady=(0, 12))
        entry.focus_set()
        entry.select_range(0, "end")

        entry_menu = tk.Menu(dialog, tearoff=0)
        entry_menu.add_command(label="剪切", command=lambda: entry.event_generate("<<Cut>>"))
        entry_menu.add_command(label="复制", command=lambda: entry.event_generate("<<Copy>>"))
        entry_menu.add_command(label="粘贴", command=lambda: entry.event_generate("<<Paste>>"))
        entry_menu.add_separator()
        entry_menu.add_command(label="全选", command=lambda: self.entry_select_all(entry))

        def show_entry_menu(event):
            try:
                entry_menu.tk_popup(event.x_root, event.y_root)
            finally:
                entry_menu.grab_release()

        entry.bind("<Button-3>", show_entry_menu)
        entry.bind("<Control-a>", lambda event: self.entry_select_all(entry))
        entry.bind("<Control-A>", lambda event: self.entry_select_all(entry))

        btn_frame = ttk.Frame(frame)
        btn_frame.pack(fill="x")

        def ok():
            result["value"] = entry_var.get()
            dialog.destroy()

        def cancel():
            result["value"] = None
            dialog.destroy()

        ttk.Button(btn_frame, text="OK", command=ok).pack(side="left", padx=(0, 10))
        ttk.Button(btn_frame, text="Cancel", command=cancel).pack(side="left")

        entry.bind("<Return>", lambda event: ok())
        entry.bind("<Escape>", lambda event: cancel())
        dialog.protocol("WM_DELETE_WINDOW", cancel)

        self.center_dialog(dialog)

        self.wait_window(dialog)
        return result["value"]

    def entry_select_all(self, entry):
        entry.select_range(0, "end")
        entry.icursor("end")
        return "break"

    # ============================================================
    # 基础工具函数
    # ============================================================

    def choose_repo(self):
        path = filedialog.askdirectory(title="选择 Git 仓库目录")

        if not path:
            return

        self.repo_path.set(path)
        self.status_text.set(f"当前仓库：{path}")
        self.append_output(f"\n已选择仓库：{path}\n")
        self.save_current_repo_path_to_config()

        # 选择文件夹后立即检测；非 Git 仓库必须弹窗，不只是输出文字
        self.after(80, self.check_repo_after_choose)

    def check_repo_after_choose(self):
        repo = self.repo_path.get().strip()

        if not repo or not Path(repo).exists():
            return

        self.status_text.set("正在检测仓库状态...")

        def task():
            inside_output = self.run_command(["git", "rev-parse", "--is-inside-work-tree"], repo).strip()

            if inside_output.lower() != "true":
                self.after(0, self.handle_non_git_repo_selected)
                return

            remote_output = self.run_command(["git", "remote", "-v"], repo)
            has_github = "github.com" in remote_output.lower()
            fix_chinese_done = self.is_fix_chinese_done(repo)

            self.after(0, lambda: self.handle_git_repo_selected(has_github, remote_output, fix_chinese_done))

        threading.Thread(target=task, daemon=True).start()

    def handle_non_git_repo_selected(self):
        self.append_output(
            "\n提示：当前目录不是 Git 仓库。\n"
            "可以点击“初始化仓库”，也可以在弹窗中点击“克隆仓库”。\n"
        )
        self.status_text.set("当前目录不是 Git 仓库")

        # 非 Git 仓库时显示：克隆仓库、初始化仓库、添加远程 origin
        # 之前如果检测过已连接 GitHub，会把“添加远程 origin”隐藏；
        # 这里重新显示，避免选择普通文件夹后看不到添加远程按钮。
        self.show_builtin_if_exists("clone_repo")
        self.show_builtin_if_exists("init")
        self.show_builtin_if_exists("add_remote")
        self.update_ignore_buttons_by_repo()
        self.update_workflow_buttons_by_repo()
        self.update_user_config_buttons_by_repo()

        self.show_connect_github_dialog_for_non_git()

    def handle_git_repo_selected(self, has_github, remote_output, fix_chinese_done):
        # 当前目录已经是 Git 仓库时，隐藏“初始化仓库”
        self.hide_builtin_if_exists("init")

        if has_github:
            self.append_output("\n已检测到 GitHub 远程仓库：\n")
            self.append_output(remote_output + "\n")
            self.status_text.set("已连接 GitHub")

            # 已连接 GitHub 后隐藏“添加远程 origin”和“克隆仓库”
            self.hide_builtin_if_exists("add_remote")
            self.hide_builtin_if_exists("clone_repo")

            # 自动检查同步
            self.after(150, lambda: self.git_check_sync_status(auto=True))
        else:
            self.append_output(
                "\n当前目录是 Git 仓库，但未检测到 GitHub 远程仓库。\n"
                "可以点击“添加远程 origin”连接 GitHub。\n"
            )
            self.status_text.set("Git 仓库未连接 GitHub")
            self.show_builtin_if_exists("add_remote")
            self.show_connect_github_dialog_for_git_no_remote()

        if fix_chinese_done:
            self.hide_builtin_if_exists("fix_chinese")
        else:
            self.show_builtin_if_exists("fix_chinese")

        self.update_ignore_buttons_by_repo()
        self.update_workflow_buttons_by_repo()
        self.update_user_config_buttons_by_repo()

        # 如果暂存区已经有文件，提醒用户可以直接添加说明并提交
        self.after(300, self.prompt_staged_files_if_needed)

    def get_staged_status_display_lines(self, staged_statuses):
        status_map = {
            "A": "新增",
            "M": "修改",
            "D": "删除",
            "R": "重命名",
            "C": "复制",
            "T": "类型变化",
            "U": "未合并",
        }

        lines = []

        for item in staged_statuses or []:
            status = str(item.get("status", ""))
            path = item.get("path", "")
            status_text = status_map.get(status[:1], status)
            lines.append(f"- {status_text}：{path}")

        return lines

    def prompt_staged_files_if_needed(self):
        repo = self.get_repo_silent()

        if not repo or not Path(repo).exists():
            return

        if not self.is_inside_git_repo(repo):
            return

        staged_statuses = self.get_staged_file_statuses(repo)

        if not staged_statuses:
            return

        key = str(Path(repo).resolve()) + "::" + "|".join(
            f"{item.get('status')}:{item.get('path')}" for item in staged_statuses
        )

        if key in self.staged_files_prompted_keys:
            return

        self.staged_files_prompted_keys.add(key)

        lines = self.get_staged_status_display_lines(staged_statuses)
        preview = "\n".join(lines[:12])
        more = "" if len(lines) <= 12 else f"\n... 还有 {len(lines) - 12} 个文件"

        message = (
            f"检测到暂存区已有 {len(staged_statuses)} 个文件等待提交：\n\n"
            f"{preview}{more}\n\n"
            "是否现在点击“添加说明”，继续提交这些暂存文件？"
        )

        should_commit = messagebox.askyesno("检测到暂存区已有文件", message)

        if should_commit:
            self.git_commit()
        else:
            self.status_text.set("暂存区已有文件：可点击“添加说明”继续提交")

    def add_remote_origin_from_connect_dialog(self):
        repo = self.get_repo()

        if not repo:
            return

        inside_output = self.run_command(
            ["git", "rev-parse", "--is-inside-work-tree"],
            repo
        ).strip()

        if inside_output.lower() != "true":
            should_init = messagebox.askyesno(
                "需要先初始化 Git 仓库",
                "当前目录还不是 Git 仓库，不能直接添加远程 origin。\n\n"
                "是否先执行 git init 初始化仓库，然后再添加远程 origin？"
            )

            if not should_init:
                return

            self.append_output("\n========== 初始化 Git 仓库 ==========\n")
            self.append_output("默认分支：main\n\n")

            code, output = self.run_git_init_main_sync(repo)
            self.append_output(output)

            if code != 0:
                messagebox.showerror("错误", "初始化 Git 仓库失败，无法继续添加远程 origin。")
                self.status_text.set("初始化 Git 仓库失败：请查看红色错误提示")
                return

            self.update_first_commit_step_status(repo, command_success=True, command_title="初始化仓库")
            self.status_text.set("初始化仓库成功。继续添加远程 origin")

        self.git_add_remote()

    def show_connect_github_dialog_for_git_no_remote(self):
        dialog = tk.Toplevel(self)
        dialog.withdraw()
        dialog.title("连接 GitHub")
        dialog.resizable(False, False)
        dialog.transient(self)
        dialog.grab_set()
        dialog.attributes("-topmost", True)

        frame = ttk.Frame(dialog, padding=18)
        frame.pack(fill="both", expand=True)

        ttk.Label(
            frame,
            text=(
                "当前仓库还没有连接 GitHub。\n\n"
                "可以打开 GitHub 新建仓库，然后回到工具点击“添加远程 origin”。"
            ),
            justify="left"
        ).pack(anchor="w", pady=(0, 16))

        btn_frame = ttk.Frame(frame)
        btn_frame.pack(fill="x")

        def open_github():
            webbrowser.open("https://github.com/new")
            dialog.destroy()

        def add_remote_origin():
            dialog.destroy()
            self.add_remote_origin_from_connect_dialog()

        ttk.Button(btn_frame, text="打开 GitHub", command=open_github).pack(side="left", padx=(0, 8))
        ttk.Button(btn_frame, text="添加远程 origin", command=add_remote_origin).pack(side="left", padx=(0, 8))
        ttk.Button(btn_frame, text="取消", command=dialog.destroy).pack(side="left")

        dialog.protocol("WM_DELETE_WINDOW", dialog.destroy)
        self.center_dialog(dialog)

    def show_connect_github_dialog_for_non_git(self):
        dialog = tk.Toplevel(self)
        dialog.withdraw()
        dialog.title("连接 GitHub")
        dialog.resizable(False, False)
        dialog.transient(self)
        dialog.grab_set()
        dialog.attributes("-topmost", True)

        frame = ttk.Frame(dialog, padding=18)
        frame.pack(fill="both", expand=True)

        ttk.Label(
            frame,
            text=(
                "当前目录不是 Git 仓库，也未检测到 GitHub 连接。\n\n"
                "可以打开 GitHub 新建仓库，也可以点击“克隆仓库”从远程仓库下载到当前目录。"
            ),
            justify="left"
        ).pack(anchor="w", pady=(0, 16))

        btn_frame = ttk.Frame(frame)
        btn_frame.pack(fill="x")

        def open_github():
            webbrowser.open("https://github.com/new")
            dialog.destroy()

        def clone_repo():
            dialog.destroy()
            self.git_clone_repo()

        def add_remote_origin():
            dialog.destroy()
            self.add_remote_origin_from_connect_dialog()

        ttk.Button(btn_frame, text="打开 GitHub", command=open_github).pack(side="left", padx=(0, 8))
        ttk.Button(btn_frame, text="克隆仓库", command=clone_repo).pack(side="left", padx=(0, 8))
        ttk.Button(btn_frame, text="添加远程 origin", command=add_remote_origin).pack(side="left", padx=(0, 8))
        ttk.Button(btn_frame, text="取消", command=dialog.destroy).pack(side="left")

        dialog.protocol("WM_DELETE_WINDOW", dialog.destroy)
        self.center_dialog(dialog)

    def center_dialog(self, dialog, min_width=320, min_height=160):
        """
        统一修复弹窗跑到左上角的问题。

        做法：
        1. 先 withdraw 隐藏弹窗，避免它先在 (0,0) 闪一下；
        2. update_idletasks 后读取真实所需尺寸；
        3. 不依赖主窗口坐标，直接按屏幕居中，最稳定；
        4. 设置 geometry 后再 deiconify 显示。
        """
        try:
            dialog.withdraw()
        except Exception:
            pass

        self.update_idletasks()
        dialog.update_idletasks()

        width = max(dialog.winfo_reqwidth(), dialog.winfo_width(), min_width)
        height = max(dialog.winfo_reqheight(), dialog.winfo_height(), min_height)

        screen_w = dialog.winfo_screenwidth()
        screen_h = dialog.winfo_screenheight()

        x = max(0, (screen_w - width) // 2)
        y = max(0, (screen_h - height) // 2)

        dialog.geometry(f"{width}x{height}+{x}+{y}")

        try:
            dialog.deiconify()
        except Exception:
            pass

        dialog.lift()
        dialog.focus_force()

        try:
            dialog.attributes("-topmost", True)
            dialog.after(500, lambda: dialog.attributes("-topmost", False))
        except Exception:
            pass

    def get_repo(self):
        path = self.repo_path.get().strip()

        if not path:
            messagebox.showwarning("提示", "请先选择 Git 仓库目录")
            return None

        if not Path(path).exists():
            messagebox.showerror("错误", "该路径不存在")
            return None

        return path

    def get_repo_silent(self):
        path = self.repo_path.get().strip()

        if not path or not Path(path).exists():
            return None

        return path

    def decode_output(self, data: bytes):
        for encoding in ("utf-8", "gbk", "mbcs"):
            try:
                return data.decode(encoding)
            except Exception:
                pass

        return data.decode("utf-8", errors="replace")

    def run_command(self, args, cwd):
        try:
            creationflags = 0
            if hasattr(subprocess, "CREATE_NO_WINDOW"):
                creationflags = subprocess.CREATE_NO_WINDOW

            result = subprocess.run(
                args,
                cwd=cwd,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                shell=False,
                creationflags=creationflags
            )

            return self.decode_output(result.stdout)

        except FileNotFoundError:
            self.after(0, lambda: self.prompt_install_git_if_missing("执行 git 命令时未找到 git.exe"))
            return (
                "错误：没有检测到 Git。\n"
                "请先安装 Git，并确保 git 命令可以在 PowerShell 或 CMD 中使用。\n"
            )
        except Exception as e:
            return f"执行出错：{e}\n"

    def check_git_available(self):
        try:
            creationflags = 0
            if hasattr(subprocess, "CREATE_NO_WINDOW"):
                creationflags = subprocess.CREATE_NO_WINDOW

            result = subprocess.run(
                ["git", "--version"],
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                shell=False,
                creationflags=creationflags
            )

            return result.returncode == 0, self.decode_output(result.stdout).strip()

        except FileNotFoundError:
            return False, "未检测到 Git"
        except Exception as e:
            return False, str(e)

    def check_git_installation_on_startup(self):
        ok, info = self.check_git_available()

        if ok:
            self.status_text.set(f"已检测到 {info}")
            return True

        self.prompt_install_git_if_missing(info)
        return False

    def prompt_install_git_if_missing(self, reason=""):
        if self.git_install_prompted:
            return

        self.git_install_prompted = True

        dialog = tk.Toplevel(self)
        dialog.withdraw()
        dialog.title("未检测到 Git")
        dialog.resizable(False, False)
        dialog.transient(self)
        dialog.grab_set()
        dialog.attributes("-topmost", True)

        frame = ttk.Frame(dialog, padding=16)
        frame.pack(fill="both", expand=True)

        ttk.Label(
            frame,
            text=(
                "没有检测到 Git，当前工具无法执行 Git 命令。\n\n"
                "请选择一种安装方式：\n"
                "1. 打开 Git 官方下载页面\n"
                "2. Windows 下尝试使用 winget 自动安装\n\n"
                f"检测信息：{reason}"
            ),
            justify="left"
        ).pack(anchor="w", pady=(0, 12))

        result = {"action": None}

        def choose(action):
            result["action"] = action
            dialog.destroy()

        btn_frame = ttk.Frame(frame)
        btn_frame.pack(fill="x")

        ttk.Button(btn_frame, text="打开下载页", command=lambda: choose("web")).pack(side="left", padx=(0, 8))
        ttk.Button(btn_frame, text="尝试自动安装", command=lambda: choose("winget")).pack(side="left", padx=(0, 8))
        ttk.Button(btn_frame, text="取消", command=lambda: choose(None)).pack(side="left")

        dialog.protocol("WM_DELETE_WINDOW", lambda: choose(None))
        self.center_dialog(dialog, min_width=520, min_height=260)
        self.wait_window(dialog)

        if result["action"] == "web":
            webbrowser.open("https://git-scm.com/download/win")
            self.status_text.set("已打开 Git 下载页面，安装完成后请重新打开本工具")
            return

        if result["action"] == "winget":
            self.install_git_with_winget()

    def install_git_with_winget(self):
        self.append_output("\n========== 尝试使用 winget 安装 Git ==========\n")
        self.append_output("winget install --id Git.Git -e --source winget\n\n")
        self.status_text.set("正在尝试使用 Windows winget 自动安装 Git...")

        def task():
            try:
                creationflags = 0
                if hasattr(subprocess, "CREATE_NO_WINDOW"):
                    creationflags = subprocess.CREATE_NO_WINDOW

                result = subprocess.run(
                    ["winget", "install", "--id", "Git.Git", "-e", "--source", "winget"],
                    stdout=subprocess.PIPE,
                    stderr=subprocess.STDOUT,
                    shell=False,
                    creationflags=creationflags
                )
                code = result.returncode
                output = self.decode_output(result.stdout)
            except FileNotFoundError:
                code = 1
                output = "未检测到 Windows winget。请手动打开 Git 下载页面安装。\n"
            except Exception as e:
                code = 1
                output = f"Windows winget 自动安装出错：{e}\n"

            self.after(0, lambda: self.append_output(output))

            if code == 0:
                self.after(0, lambda: messagebox.showinfo(
                    "安装完成",
                    "Windows winget 自动安装命令已执行完成。\n\n"
                    "如果仍然检测不到 Git，请关闭并重新打开本工具，或重启电脑后再试。"
                ))
                self.after(0, lambda: self.status_text.set("Git 安装命令执行完成，请重启工具确认"))
            else:
                self.after(0, lambda: messagebox.showwarning(
                    "安装失败",
                    "自动安装没有成功。\n\n"
                    "建议点击下载页面手动安装 Windows 版 Git。"
                ))
                self.after(0, lambda: webbrowser.open("https://git-scm.com/download/win"))
                self.after(0, lambda: self.status_text.set("Git 自动安装失败，已打开下载页面"))

        threading.Thread(target=task, daemon=True).start()

    def run_command_with_code(self, args, cwd):
        try:
            creationflags = 0
            if hasattr(subprocess, "CREATE_NO_WINDOW"):
                creationflags = subprocess.CREATE_NO_WINDOW

            result = subprocess.run(
                args,
                cwd=cwd,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                shell=False,
                creationflags=creationflags
            )

            return result.returncode, self.decode_output(result.stdout)

        except FileNotFoundError:
            self.after(0, lambda: self.prompt_install_git_if_missing("执行 git 命令时未找到 git.exe"))
            return 1, "错误：没有检测到 Git。\n请先安装 Git，并确保 git 命令可以在 PowerShell 或 CMD 中使用。\n"
        except Exception as e:
            return 1, f"执行出错：{e}\n"

    def parse_git_args(self, command_text):
        text = command_text.strip()

        if text.lower().startswith("git "):
            text = text[4:].strip()

        try:
            return shlex.split(text)
        except Exception as e:
            messagebox.showerror("错误", f"命令解析失败：\n{e}")
            return None

    def run_git(self, git_args, title="执行命令"):
        repo = self.get_repo()
        if not repo:
            return

        command_text = "git " + " ".join(git_args)

        self.append_output(f"\n========== {title} ==========\n")
        self.append_output(f"{command_text}\n\n")
        self.status_text.set("命令执行中...")

        def task():
            code, output = self.run_command_with_code(["git"] + git_args, repo)
            self.after(0, lambda: self.finish_command_with_code(output, code, repo, title))

        threading.Thread(target=task, daemon=True).start()

    def finish_command_with_code(self, output, code, repo=None, title="执行命令"):
        self.append_output(output)

        if code == 0:
            self.update_first_commit_step_status(repo, command_success=True, command_title=title)
        else:
            handled = self.handle_common_git_problem(output, title)
            if not handled:
                self.status_text.set(f"{title}失败：请查看红色错误提示，修正后重试")

    def is_inside_git_repo(self, repo):
        if not repo or not Path(repo).exists():
            return False

        output = self.run_command(["git", "rev-parse", "--is-inside-work-tree"], repo).strip()
        return output.lower() == "true"

    def repo_has_staged_changes(self, repo):
        if not self.is_inside_git_repo(repo):
            return False

        output = self.run_command(["git", "diff", "--cached", "--name-only"], repo).strip()
        return bool(output)

    def update_first_commit_step_status(self, repo=None, command_success=True, command_title="命令"):
        """
        左下角流程提示：
        新仓库第一次提交流程中，每完成一步都提示是否成功以及下一步做什么。
        """
        if repo is None:
            repo = self.get_repo_silent()

        if not command_success:
            self.status_text.set(f"{command_title}失败：请查看红色错误提示，修正后重试")
            return

        if not repo or not Path(repo).exists():
            self.status_text.set(f"{command_title}成功")
            return

        if not self.is_inside_git_repo(repo):
            self.status_text.set(f"{command_title}成功。下一步：初始化仓库或克隆仓库")
            return

        has_commits = self.repo_has_commits(repo)
        has_origin = self.repo_has_origin_remote(repo)

        if not has_commits:
            if self.repo_has_staged_changes(repo):
                self.status_text.set(f"{command_title}成功。新仓库下一步：点击“添加说明”，完成第一次提交")
            else:
                self.status_text.set(f"{command_title}成功。新仓库下一步：点击“添加全部文件”或“添加部分文件”")
            return

        if not has_origin:
            self.status_text.set(f"{command_title}成功。第一次提交已完成，下一步：点击“添加远程 origin”")
            return

        branch = self.get_current_branch_for_push(repo)
        upstream = self.run_command(
            ["git", "rev-parse", "--abbrev-ref", "--symbolic-full-name", "@{u}"],
            repo
        ).strip()

        if branch and ("fatal" in upstream.lower() or upstream == ""):
            self.status_text.set(f"{command_title}成功。下一步：点击“推送至仓库”，首次绑定远程分支")
            return

        self.status_text.set(f"{command_title}成功。当前仓库已提交并连接远程，可正常推送或拉取")

    def run_git_sequence(self, commands, title="执行多个 Git 命令"):
        repo = self.get_repo()
        if not repo:
            return

        self.append_output(f"\n========== {title} ==========\n")
        self.status_text.set("命令执行中...")

        def task():
            all_output = []
            stopped = False

            for git_args, step_title in commands:
                cmd_text = "git " + " ".join(git_args)
                all_output.append(f"\n--- {step_title} ---\n{cmd_text}\n")

                code, output = self.run_command_with_code(["git"] + git_args, repo)
                all_output.append(output)

                if code != 0:
                    all_output.append("\n命令执行失败，后续步骤已停止。\n")
                    stopped = True
                    break

            final_output = "".join(all_output)
            self.after(0, lambda: self.finish_command(final_output))

            if stopped:
                self.after(0, lambda: self.status_text.set("部分命令执行失败"))
            else:
                self.after(0, lambda: self.status_text.set("命令执行完成"))

        threading.Thread(target=task, daemon=True).start()

    def finish_command(self, output):
        self.append_output(output)
        self.update_first_commit_step_status(self.get_repo_silent(), command_success=True, command_title="命令")

    def is_error_line(self, line):
        lower_line = line.lower()
        error_patterns = [
            "error:",
            "fatal:",
            "failed:",
            "cannot ",
            "unable to ",
            "refusing to ",
            "permission denied",
            "authentication failed",
        ]

        return any(pattern in lower_line for pattern in error_patterns)

    def is_warning_line(self, line):
        lower_line = line.lower()
        warning_patterns = [
            "warning:",
            "lf will be replaced by crlf",
            "crlf will be replaced by lf",
        ]

        return any(pattern in lower_line for pattern in warning_patterns)

    def is_crlf_warning_text(self, text):
        lower_text = text.lower()
        return (
            "lf will be replaced by crlf" in lower_text
            or "crlf will be replaced by lf" in lower_text
        )

    def is_octal_escaped_filename_text(self, text):
        """
        Git 默认 core.quotepath=true 时，中文文件名可能显示为：
        "\345\246\202\344\275\225.md"
        这里检测这种连续八进制转义。
        """
        if not text:
            return False

        # 至少出现两组 \ooo，基本可判断为非 ASCII 文件名被 Git 转义了。
        return bool(re.search(r'(?:\\[0-7]{3}){2,}', text))

    def extract_warning_error_lines(self, text):
        lines = []

        for line in text.splitlines():
            if self.is_error_line(line) or self.is_warning_line(line):
                lines.append(line)

        return "\n".join(lines).strip()

    def ask_copy_resolved_warning(self, diagnostic_text, solved_message="警告已自动处理"):
        diagnostic_text = (diagnostic_text or "").strip()

        if not diagnostic_text:
            return

        should_copy = messagebox.askyesno(
            "警告已处理",
            f"{solved_message}\n\n是否仍然需要把原始警告内容复制到剪切板？"
        )

        if should_copy:
            self.copy_diagnostics_to_clipboard(diagnostic_text, "已处理的警告")
        else:
            self.status_text.set(f"{solved_message}，未复制原始警告")

    def copy_diagnostics_to_clipboard(self, diagnostic_text, level="警告/错误"):
        diagnostic_text = diagnostic_text.strip()

        if not diagnostic_text:
            return

        if diagnostic_text == self.last_copied_diagnostic_text:
            return

        self.last_copied_diagnostic_text = diagnostic_text

        try:
            self.clipboard_clear()
            self.clipboard_append(diagnostic_text)
            self.status_text.set(f"检测到 {level}，已复制到剪切板")
            messagebox.showinfo(
                "已复制提示信息",
                f"检测到 {level}，相关内容已自动复制到剪切板。\n\n"
                "可直接粘贴给他人或发给 ChatGPT 分析。"
            )
        except Exception:
            self.status_text.set(f"检测到 {level}，但复制到剪切板失败")

    def is_network_error_text(self, text):
        lower_text = text.lower()
        patterns = [
            "failed to connect",
            "could not resolve host",
            "connection timed out",
            "connection reset",
            "connection refused",
            "failed to receive",
            "recv failure",
            "schannel",
            "ssl",
            "tls",
            "proxy",
            "port 443",
            "network is unreachable",
            "unable to access",
        ]
        return any(pattern in lower_text for pattern in patterns)

    def is_auth_error_text(self, text):
        lower_text = text.lower()
        patterns = [
            "authentication failed",
            "permission denied",
            "repository not found",
            "could not read username",
            "support for password authentication was removed",
            "403",
            "401",
        ]
        return any(pattern in lower_text for pattern in patterns)

    def handle_common_git_problem(self, output, context="Git 操作"):
        if self.is_crlf_warning_text(output):
            self.after(100, self.prompt_fix_crlf_warning_if_needed)

        if self.is_octal_escaped_filename_text(output):
            self.after(150, self.prompt_fix_octal_filename_if_needed)

        if self.is_network_error_text(output):
            message = (
                f"{context} 可能因为网络连接问题失败。\n\n"
                "建议检查：\n"
                "1. 浏览器能否打开 GitHub\n"
                "2. 当前网络是否能访问 github.com:443\n"
                "3. 是否需要开启代理 / 网络加速\n"
                "4. 如果使用代理，确认 Git 也配置了代理\n\n"
                "常见命令示例：\n"
                "git config --global http.proxy http://127.0.0.1:端口\n"
                "git config --global https.proxy http://127.0.0.1:端口\n\n"
                "如果不使用代理，可清除：\n"
                "git config --global --unset http.proxy\n"
                "git config --global --unset https.proxy"
            )
            messagebox.showwarning("网络或代理问题", message)
            self.status_text.set("检测到网络问题：请检查网络或配置 Git 网络加速")
            return True

        if self.is_auth_error_text(output):
            message = (
                f"{context} 可能因为 GitHub 登录或权限问题失败。\n\n"
                "建议检查：\n"
                "1. GitHub 仓库地址是否正确\n"
                "2. 当前账号是否有该仓库权限\n"
                "3. HTTPS 推送是否已登录 Git 凭据管理器\n"
                "4. 如果提示密码认证失效，请使用 GitHub 访问令牌 或重新登录"
            )
            messagebox.showwarning("GitHub 认证或权限问题", message)
            self.status_text.set("检测到认证或权限问题：请检查 GitHub 登录和仓库权限")
            return True

        return False

    def append_output(self, text):
        has_warning = False
        has_error = False
        has_crlf_warning = self.is_crlf_warning_text(text)
        has_octal_filename = self.is_octal_escaped_filename_text(text)

        for chunk in text.splitlines(True):
            if self.is_error_line(chunk):
                self.output.insert("end-1c", chunk, ("error_text",))
                has_error = True
            elif self.is_warning_line(chunk):
                self.output.insert("end-1c", chunk, ("warning_text",))
                has_warning = True
            else:
                self.output.insert("end-1c", chunk, ("normal_text",))

        if has_error:
            self.status_text.set("检测到错误 / 严重错误，已用红色高亮显示")
        elif has_warning:
            self.status_text.set("检测到警告，已用黄色高亮显示")

        diagnostic_text = self.extract_warning_error_lines(text)
        can_auto_fix_warning = has_crlf_warning or has_octal_filename

        if diagnostic_text:
            level = "错误" if has_error else "警告"

            # 错误仍然自动复制；无法自动处理的警告也自动复制。
            # 可自动处理的警告先尝试自动修复，修复后再询问是否仍需复制原始警告。
            if has_error or not can_auto_fix_warning:
                self.after(80, lambda t=diagnostic_text, lv=level: self.copy_diagnostics_to_clipboard(t, lv))

        if has_crlf_warning:
            self.after(100, lambda t=diagnostic_text: self.prompt_fix_crlf_warning_if_needed(t))

        if has_octal_filename:
            self.after(150, lambda t=diagnostic_text: self.prompt_fix_octal_filename_if_needed(t))

        if has_error or has_warning:
            self.after(120, lambda t=text: self.handle_common_git_problem(t, "Git 操作"))

        self.output.see("end")

    def prompt_fix_octal_filename_if_needed(self, diagnostic_text=""):
        if self.is_running_chinese_filename_fix:
            return

        repo = self.get_repo_silent()
        repo_key = str(Path(repo).resolve()) if repo else "__no_repo__"

        if repo_key in self.octal_filename_prompted_repos:
            return

        self.octal_filename_prompted_repos.add(repo_key)

        message = (
            "检测到 Git 输出中的文件名显示为八进制转义，而不是中文。\n\n"
            "例如：\n"
            "\\345\\246\\202\\344\\275\\225.md\n\n"
            "这是因为 Git 的 core.quotepath 仍为 true。\n"
            "建议设置：git config --global core.quotepath false\n\n"
            "是否现在自动修复中文文件名显示？"
        )

        if messagebox.askyesno("检测到中文文件名显示异常", message):
            fixed = self.git_fix_chinese()

            if fixed:
                self.ask_copy_resolved_warning(
                    diagnostic_text,
                    "中文文件名显示问题已处理"
                )
            else:
                self.status_text.set("中文文件名显示问题自动处理失败，请查看红色错误提示")
        else:
            self.status_text.set("已忽略本次中文文件名显示提示；可点击“修复中文显示”手动处理")

    def prompt_fix_crlf_warning_if_needed(self, diagnostic_text=""):
        if self.is_running_line_ending_fix:
            return

        repo = self.get_repo_silent()
        repo_key = str(Path(repo).resolve()) if repo else "__no_repo__"

        if repo_key in self.crlf_warning_prompted_repos:
            return

        self.crlf_warning_prompted_repos.add(repo_key)

        message = (
            "检测到 Windows 换行符警告：\n\n"
            "warning: LF will be replaced by CRLF the next time Git touches it\n\n"
            "建议处理方式：\n"
            "1. 自动写入 / 更新 .gitattributes\n"
            "2. 当前仓库设置 core.autocrlf=false\n"
            "3. 由 .gitattributes 统一管理不同文件的换行符\n\n"
            "是否现在执行“修复换行符警告”？"
        )

        if messagebox.askyesno("检测到换行符警告", message):
            fixed = self.git_fix_line_endings_windows()

            if fixed:
                self.ask_copy_resolved_warning(
                    diagnostic_text,
                    "Windows 换行符警告已处理"
                )
            else:
                self.status_text.set("换行符警告自动处理失败或已取消")
        else:
            self.status_text.set("已忽略本次换行符警告；可在“显示隐藏”中打开“修复换行符警告”按钮手动处理")

    def clear_output(self):
        self.output.delete("1.0", "end")

    # ============================================================
    # 输出框右键复制
    # ============================================================

    def show_output_menu(self, event):
        try:
            self.output_menu.tk_popup(event.x_root, event.y_root)
        finally:
            self.output_menu.grab_release()

    def copy_selected_text(self):
        try:
            selected_text = self.output.get("sel.first", "sel.last")
            self.clipboard_clear()
            self.clipboard_append(selected_text)
        except tk.TclError:
            messagebox.showinfo("提示", "请先选中要复制的内容")

    def select_all_output(self):
        self.output.tag_add("sel", "1.0", "end")
        return "break"

    # ============================================================
    # 提交 ID 点击切换
    # ============================================================

    def enter_commit_link(self, event):
        self.output.config(cursor="hand2")

    def leave_commit_link(self, event):
        self.output.config(cursor="")

    def ctrl_click_commit(self, event):
        index = self.output.index(f"@{event.x},{event.y}")
        ranges = self.output.tag_ranges("commit_link")
        commit_id = None

        for i in range(0, len(ranges), 2):
            start = ranges[i]
            end = ranges[i + 1]

            if self.output.compare(start, "<=", index) and self.output.compare(index, "<", end):
                commit_id = self.output.get(start, end).strip()
                break

        if not commit_id:
            return "break"

        if not re.fullmatch(r"[0-9a-fA-F]{4,40}", commit_id):
            return "break"

        confirm = messagebox.askyesno(
            "切换版本",
            f"确定要切换到这个版本吗？\n\n"
            f"提交 ID：{commit_id}\n\n"
            f"注意：切换到旧版本后会进入 游离 HEAD 状态。\n"
            f"如果只是查看旧版本，这是正常的。\n\n"
            f"要回到最新版本，可以点击“切回指定分支”。"
        )

        if not confirm:
            return "break"

        self.run_git(["checkout", commit_id], f"切换到版本：{commit_id}")
        return "break"

    # ============================================================
    # Git 功能
    # ============================================================

    # ============================================================
    # Git 用户名和邮箱配置
    # ============================================================

    def get_git_identity(self, repo=None):
        """
        获取当前有效的 Git 用户名和邮箱。
        在 Git 仓库里会读取 local + global 的最终结果；
        在普通目录里通常读取 global 配置。
        """
        if repo is None:
            repo = self.get_repo_silent()

        cwd = repo if repo and Path(repo).exists() else str(Path.home())

        name = self.run_command(["git", "config", "--get", "user.name"], cwd).strip()
        email = self.run_command(["git", "config", "--get", "user.email"], cwd).strip()

        if "error" in name.lower() or "fatal" in name.lower():
            name = ""

        if "error" in email.lower() or "fatal" in email.lower():
            email = ""

        return name, email

    def is_git_identity_configured(self, repo=None):
        name, email = self.get_git_identity(repo)
        return bool(name.strip()) and bool(email.strip())

    def update_user_config_buttons_by_repo(self):
        repo = self.get_repo_silent()

        if self.is_git_identity_configured(repo):
            self.hide_builtin_if_exists("config_user")
        else:
            self.show_builtin_if_exists("config_user")

        # “修改用户名邮箱”只作为可选高级按钮，默认隐藏，不自动显示。
        # 用户需要时可从“显示隐藏”里手动打开。

    def ask_git_identity_dialog(self, title="配置用户名邮箱", default_global=True):
        repo = self.get_repo_silent()
        current_name, current_email = self.get_git_identity(repo)

        dialog = tk.Toplevel(self)
        dialog.withdraw()
        dialog.title(title)
        dialog.resizable(False, False)
        dialog.transient(self)
        dialog.grab_set()
        dialog.attributes("-topmost", True)

        result = {"ok": False, "name": "", "email": "", "use_global": True}

        frame = ttk.Frame(dialog, padding=16)
        frame.pack(fill="both", expand=True)

        ttk.Label(
            frame,
            text=(
                "Git 第一次提交前需要配置用户名和邮箱。\n"
                "这些信息会写入提交记录，用于标识是谁提交的。"
            ),
            justify="left"
        ).pack(anchor="w", pady=(0, 12))

        ttk.Label(frame, text="用户名 user.name：").pack(anchor="w")
        name_var = tk.StringVar(value=current_name)
        name_entry = ttk.Entry(frame, textvariable=name_var, width=48)
        name_entry.pack(fill="x", pady=(4, 10))

        ttk.Label(frame, text="邮箱 user.email：").pack(anchor="w")
        email_var = tk.StringVar(value=current_email)
        email_entry = ttk.Entry(frame, textvariable=email_var, width=48)
        email_entry.pack(fill="x", pady=(4, 10))

        use_global_var = tk.BooleanVar(value=default_global)

        ttk.Checkbutton(
            frame,
            text="保存为全局配置（推荐：以后所有仓库都可使用）",
            variable=use_global_var
        ).pack(anchor="w", pady=(0, 12))

        btn_frame = ttk.Frame(frame)
        btn_frame.pack(fill="x")

        def ok():
            name = name_var.get().strip()
            email = email_var.get().strip()

            if not name:
                messagebox.showwarning("提示", "用户名不能为空")
                return

            if not email:
                messagebox.showwarning("提示", "邮箱不能为空")
                return

            result["ok"] = True
            result["name"] = name
            result["email"] = email
            result["use_global"] = bool(use_global_var.get())
            dialog.destroy()

        def cancel():
            dialog.destroy()

        ttk.Button(btn_frame, text="保存", command=ok).pack(side="left", padx=(0, 8))
        ttk.Button(btn_frame, text="取消", command=cancel).pack(side="left")

        dialog.protocol("WM_DELETE_WINDOW", cancel)

        name_entry.focus_set()
        self.center_dialog(dialog, min_width=480, min_height=330)
        self.wait_window(dialog)

        if not result["ok"]:
            return None

        return result

    def save_git_identity(self, name, email, use_global=True):
        repo = self.get_repo_silent()
        cwd = repo if repo and Path(repo).exists() else str(Path.home())

        if use_global:
            name_args = ["config", "--global", "user.name", name]
            email_args = ["config", "--global", "user.email", email]
            title = "保存全局 Git 用户名和邮箱"
        else:
            if not repo:
                messagebox.showwarning("提示", "当前没有可用仓库，无法保存为当前仓库配置")
                return False

            name_args = ["config", "user.name", name]
            email_args = ["config", "user.email", email]
            title = "保存当前仓库 Git 用户名和邮箱"

        self.append_output(f"\n========== {title} ==========\n")

        code1, out1 = self.run_command_with_code(["git"] + name_args, cwd)
        code2, out2 = self.run_command_with_code(["git"] + email_args, cwd)

        if out1.strip():
            self.append_output(out1 + "\n")
        if out2.strip():
            self.append_output(out2 + "\n")

        if code1 == 0 and code2 == 0:
            self.append_output(f"已保存 user.name = {name}\n")
            self.append_output(f"已保存 user.email = {email}\n")
            self.status_text.set("Git 用户名和邮箱已配置")
            self.update_user_config_buttons_by_repo()
            return True

        messagebox.showerror("错误", "保存 Git 用户名和邮箱失败，请检查 Git 是否安装正常。")
        return False

    def git_config_user(self):
        result = self.ask_git_identity_dialog("配置用户名邮箱", default_global=True)

        if not result:
            return False

        return self.save_git_identity(
            result["name"],
            result["email"],
            result["use_global"]
        )

    def git_edit_user(self):
        result = self.ask_git_identity_dialog("修改用户名邮箱", default_global=True)

        if not result:
            return False

        return self.save_git_identity(
            result["name"],
            result["email"],
            result["use_global"]
        )

    def ensure_git_identity_or_prompt(self):
        repo = self.get_repo_silent()

        if self.is_git_identity_configured(repo):
            return True

        should_config = messagebox.askyesno(
            "需要配置用户名和邮箱",
            "Git 第一次提交前需要配置 user.name 和 user.email。\n\n"
            "是否现在配置？\n\n"
            "建议保存为全局配置，这样以后所有仓库都可以直接提交。"
        )

        if not should_config:
            self.show_builtin_if_exists("config_user")
            return False

        return bool(self.git_config_user())

    def run_git_init_main_sync(self, repo):
        """
        初始化仓库时默认创建 main 分支。
        优先使用：git init -b main
        如果用户的 Git 版本较旧，不支持 -b，则回退：
        git init
        git symbolic-ref HEAD refs/heads/main
        """
        output_parts = []

        output_parts.append("git init -b main\n")
        code, output = self.run_command_with_code(["git", "init", "-b", "main"], repo)
        output_parts.append(output)

        if code == 0:
            return 0, "".join(output_parts)

        output_parts.append(
            "\n当前 Git 可能不支持 git init -b main，尝试兼容方式初始化 main 分支。\n\n"
        )

        output_parts.append("git init\n")
        code2, output2 = self.run_command_with_code(["git", "init"], repo)
        output_parts.append(output2)

        if code2 != 0:
            return code2, "".join(output_parts)

        output_parts.append("git symbolic-ref HEAD refs/heads/main\n")
        code3, output3 = self.run_command_with_code(
            ["git", "symbolic-ref", "HEAD", "refs/heads/main"],
            repo
        )
        output_parts.append(output3)

        return code3, "".join(output_parts)

    def git_init(self):
        repo = self.get_repo()
        if not repo:
            return

        self.append_output("\n========== 初始化 Git 仓库 ==========\n")
        self.status_text.set("正在初始化 Git 仓库，默认分支为 main...")

        def task():
            code, output = self.run_git_init_main_sync(repo)

            if code == 0:
                output += "\n初始化完成：默认分支已设置为 main。\n"
            else:
                output += "\n初始化失败，请查看上方红色错误提示。\n"

            self.after(0, lambda: self.finish_command_with_code(output, code, repo, "初始化仓库"))
            self.after(1000, self.check_repo_after_choose)

        threading.Thread(target=task, daemon=True).start()

    def git_clone_repo(self):
        repo = self.get_repo()
        if not repo:
            return

        url = self.ask_text_with_menu(
            "克隆仓库",
            "请输入要克隆的 GitHub 仓库地址：\n例如：https://github.com/用户名/仓库名.git"
        )

        if url is None:
            return

        url = url.strip()
        if url == "":
            messagebox.showwarning("提示", "仓库地址不能为空")
            return

        repo_path = Path(repo)

        # 如果当前目录为空，则克隆到当前目录；否则克隆为子文件夹
        try:
            is_empty = not any(repo_path.iterdir())
        except Exception:
            is_empty = False

        if is_empty:
            args = ["clone", url, "."]
            title = "克隆仓库到当前目录"
            target_path = repo_path
        else:
            folder_name = self.guess_repo_folder_name(url)
            target_path = repo_path / folder_name

            if target_path.exists():
                messagebox.showerror("错误", f"目标文件夹已存在：\n{target_path}")
                return

            args = ["clone", url, folder_name]
            title = "克隆仓库到子文件夹"

        self.append_output(f"\n========== {title} ==========\n")
        self.append_output("git " + " ".join(args) + "\n\n")
        self.status_text.set("正在克隆仓库...")

        def task():
            output = self.run_command(["git"] + args, repo)
            self.after(0, lambda: self.finish_clone_repo(output, target_path))

        threading.Thread(target=task, daemon=True).start()

    def finish_clone_repo(self, output, target_path):
        self.append_output(output)
        self.status_text.set("克隆命令执行完成")

        if (target_path / ".git").exists():
            self.repo_path.set(str(target_path))
            self.save_current_repo_path_to_config()
            self.append_output(f"\n已切换当前仓库路径：{target_path}\n")
            self.after(100, self.check_repo_after_choose)

    def guess_repo_folder_name(self, url):
        text = url.rstrip("/")

        if text.endswith(".git"):
            text = text[:-4]

        name = text.split("/")[-1].strip()
        if not name:
            name = "cloned_repo"

        # Windows 文件名简单清理
        return re.sub(r'[<>:"/\\|?*]+', "_", name)

    def ensure_repo_path_for_simple_upload(self):
        repo = self.get_repo_silent()

        if repo and Path(repo).exists():
            return repo

        messagebox.showinfo("选择仓库", "请先选择要上传到 GitHub 的项目文件夹。")
        path = filedialog.askdirectory(title="选择要上传到 GitHub 的项目文件夹")

        if not path:
            return None

        self.repo_path.set(path)
        self.save_current_repo_path_to_config()
        self.append_output(f"\n已选择仓库：{path}\n")
        return path

    def ensure_git_repo_for_simple_upload(self, repo):
        if self.is_inside_git_repo(repo):
            return True

        should_init = messagebox.askyesno(
            "初始化仓库",
            "当前文件夹还不是 Git 仓库。\n\n"
            "是否自动执行初始化？\n\n"
            "工具会使用 main 作为默认分支。"
        )

        if not should_init:
            self.status_text.set("一键上传已取消：当前文件夹不是 Git 仓库")
            return False

        self.append_output("\n========== 一键上传：初始化仓库 ==========\n")
        code, output = self.run_git_init_main_sync(repo)
        self.append_output(output)

        if code != 0:
            self.status_text.set("初始化失败：请查看红色错误提示")
            messagebox.showerror("错误", "初始化 Git 仓库失败，无法继续一键上传。")
            return False

        self.status_text.set("初始化成功。下一步：连接 GitHub 远程仓库")
        return True

    def ensure_origin_for_simple_upload(self, repo):
        if self.repo_has_origin_remote(repo):
            return True

        should_add = messagebox.askyesno(
            "连接 GitHub",
            "当前仓库还没有添加远程 origin。\n\n"
            "是否现在添加 GitHub 仓库地址？"
        )

        if not should_add:
            self.status_text.set("一键上传已暂停：需要先连接 GitHub 远程仓库")
            return False

        url = self.ask_text_with_menu(
            "添加远程 origin",
            "请输入 GitHub 仓库地址：\n例如：https://github.com/用户名/仓库名.git"
        )

        if url is None:
            return False

        url = url.strip()

        if not url:
            messagebox.showwarning("提示", "远程仓库地址不能为空")
            return False

        self.append_output("\n========== 一键上传：添加远程 origin ==========\n")
        self.append_output(f"git remote add origin {url}\n\n")

        code, output = self.run_command_with_code(["git", "remote", "add", "origin", url], repo)
        self.append_output(output)

        if code != 0:
            # origin 可能已经存在但不是 GitHub，提示用户可修改远程。
            self.handle_common_git_problem(output, "添加远程 origin")
            self.status_text.set("添加远程 origin 失败：请检查地址或使用“修改远程仓库”")
            messagebox.showerror("错误", "添加远程 origin 失败，请查看输出区域。")
            return False

        self.status_text.set("添加远程 origin 成功。下一步：选择要添加的文件")
        return True

    def ask_simple_upload_add_mode(self):
        dialog = tk.Toplevel(self)
        dialog.withdraw()
        dialog.title("选择添加文件方式")
        dialog.resizable(False, False)
        dialog.transient(self)
        dialog.grab_set()
        dialog.attributes("-topmost", True)

        result = {"mode": None}

        frame = ttk.Frame(dialog, padding=16)
        frame.pack(fill="both", expand=True)

        ttk.Label(
            frame,
            text="请选择本次要上传的文件范围：",
            justify="left"
        ).pack(anchor="w", pady=(0, 12))

        def choose(mode):
            result["mode"] = mode
            dialog.destroy()

        ttk.Button(frame, text="添加全部文件", command=lambda: choose("all")).pack(fill="x", pady=4)
        ttk.Button(frame, text="选择部分文件", command=lambda: choose("some")).pack(fill="x", pady=4)
        ttk.Button(frame, text="取消", command=lambda: choose(None)).pack(fill="x", pady=(12, 0))

        dialog.protocol("WM_DELETE_WINDOW", lambda: choose(None))
        self.center_dialog(dialog, min_width=360, min_height=220)
        self.wait_window(dialog)

        return result["mode"]

    def get_deleted_files_for_add(self, repo):
        """
        获取工作区 / 暂存区中被删除的文件。
        这些文件已经不存在于磁盘中，无法通过文件选择窗口选中，
        所以需要单独列出来让用户选择是否提交删除记录。
        """
        code, output = self.run_command_with_code(
            ["git", "status", "--porcelain", "-z"],
            repo
        )

        if code != 0:
            self.append_output(output)
            return []

        deleted_files = []
        entries = output.split("\0")

        for entry in entries:
            if not entry or len(entry) < 4:
                continue

            status = entry[:2]
            path = entry[3:]

            if "D" in status and path:
                deleted_files.append(path)

        # 去重并保持顺序
        return list(dict.fromkeys(deleted_files))

    def ask_select_deleted_files_for_add(self, deleted_files):
        """
        选择是否把删除文件也加入本次提交。
        返回：
        - list[str]：选择的删除文件
        - []：不添加删除文件
        - None：取消整个操作
        """
        if not deleted_files:
            return []

        dialog = tk.Toplevel(self)
        dialog.withdraw()
        dialog.title("检测到已删除文件")
        dialog.resizable(True, True)
        dialog.transient(self)
        dialog.grab_set()
        dialog.attributes("-topmost", True)

        result = {"files": None, "cancelled": False}

        frame = ttk.Frame(dialog, padding=16)
        frame.pack(fill="both", expand=True)

        ttk.Label(
            frame,
            text=(
                "检测到仓库中有文件被删除。\n\n"
                "删除文件无法在普通文件选择窗口中选中。\n"
                "如果希望 GitHub 也删除这些旧文件，请把它们加入本次提交。"
            ),
            justify="left"
        ).pack(anchor="w", pady=(0, 10))

        list_frame = ttk.LabelFrame(frame, text="被删除的文件", padding=8)
        list_frame.pack(fill="both", expand=True, pady=(0, 12))

        listbox = tk.Listbox(list_frame, selectmode="extended", font=("Consolas", 9), height=9)
        listbox.grid(row=0, column=0, sticky="nsew")

        y_scroll = ttk.Scrollbar(list_frame, orient="vertical", command=listbox.yview)
        y_scroll.grid(row=0, column=1, sticky="ns")
        listbox.configure(yscrollcommand=y_scroll.set)

        list_frame.rowconfigure(0, weight=1)
        list_frame.columnconfigure(0, weight=1)

        for file_path in deleted_files:
            listbox.insert("end", file_path)

        # 默认全选，因为多数情况下用户希望远程同步删除。
        listbox.selection_set(0, "end")

        btn_frame = ttk.Frame(frame)
        btn_frame.pack(fill="x")

        def add_selected():
            selections = listbox.curselection()

            result["files"] = [
                deleted_files[index]
                for index in selections
            ]
            dialog.destroy()

        def skip_deleted():
            result["files"] = []
            dialog.destroy()

        def cancel_all():
            result["cancelled"] = True
            result["files"] = None
            dialog.destroy()

        ttk.Button(btn_frame, text="加入选中的删除文件", command=add_selected).pack(side="left", padx=(0, 8))
        ttk.Button(btn_frame, text="不加入删除文件", command=skip_deleted).pack(side="left", padx=(0, 8))
        ttk.Button(btn_frame, text="取消上传", command=cancel_all).pack(side="left")

        dialog.protocol("WM_DELETE_WINDOW", cancel_all)
        self.center_dialog(dialog, min_width=680, min_height=420)
        self.wait_window(dialog)

        if result["cancelled"]:
            return None

        return result["files"] if result["files"] is not None else []

    def choose_simple_upload_files(self, repo):
        mode = self.ask_simple_upload_add_mode()

        if mode is None:
            return None

        if mode == "all":
            # git add . 在某些情况下不会把删除记录纳入提交；
            # git add -A 会同时处理新增、修改、删除，更适合“一键上传”。
            return ["add", "-A"], "添加全部文件（包含删除文件）"

        file_paths = filedialog.askopenfilenames(
            title="选择要上传到 GitHub 的文件",
            initialdir=repo
        )

        if not file_paths:
            return None

        relative_paths = []

        for file_path in file_paths:
            try:
                relative_path = Path(file_path).resolve().relative_to(Path(repo).resolve())
                relative_paths.append(relative_path.as_posix())
            except ValueError:
                messagebox.showerror("错误", "只能选择当前仓库目录里面的文件")
                return None

        deleted_files = self.get_deleted_files_for_add(repo)
        selected_deleted_files = self.ask_select_deleted_files_for_add(deleted_files)

        if selected_deleted_files is None:
            return None

        relative_paths.extend(selected_deleted_files)
        relative_paths = list(dict.fromkeys(relative_paths))

        if not relative_paths:
            return None

        return ["add", "--"] + relative_paths, "添加部分文件（可包含删除文件）"

    def git_one_click_upload_to_github(self):
        ok, info = self.check_git_available()
        if not ok:
            self.prompt_install_git_if_missing(info)
            return

        repo = self.ensure_repo_path_for_simple_upload()
        if not repo:
            return

        if not self.ensure_git_repo_for_simple_upload(repo):
            return

        if not self.ensure_git_identity_or_prompt():
            return

        if not self.ensure_origin_for_simple_upload(repo):
            return

        tag_plan = self.ask_workflow_tag_plan(repo)

        if tag_plan.get("cancel"):
            self.status_text.set("一键上传已取消")
            return

        add_result = self.choose_simple_upload_files(repo)
        if not add_result:
            self.status_text.set("一键上传已取消：未选择要添加的文件")
            return

        add_args, add_title = add_result

        self.append_output("\n========== 一键上传到 GitHub ==========\n")
        self.append_output(f"\n--- {add_title} ---\n")
        self.append_output("git " + " ".join(add_args) + "\n")
        self.status_text.set("一键上传执行中：正在添加文件...")

        def task_add():
            add_code, add_output = self.run_command_with_code(["git"] + add_args, repo)
            self.after(
                0,
                lambda: self.finish_one_click_add_and_choose_commit_mode(
                    repo,
                    add_title,
                    add_code,
                    add_output
                )
            )

        threading.Thread(target=task_add, daemon=True).start()

    def finish_one_click_add_and_choose_commit_mode(self, repo, add_title, add_code, add_output):
        self.append_output(add_output)

        if add_code != 0:
            self.handle_common_git_problem(add_output, add_title)
            self.status_text.set(f"一键上传失败：{add_title}失败")
            return

        self.status_text.set("添加文件成功。请选择提交说明方式")

        staged_statuses = self.get_staged_file_statuses(repo)

        if staged_statuses is None:
            self.status_text.set("一键上传暂停：获取暂存区文件失败")
            return

        if not staged_statuses:
            messagebox.showinfo(
                "没有可提交的文件",
                "文件添加完成，但暂存区没有可提交内容。\n\n"
                "可能是当前文件没有变化，或文件被 .gitignore 忽略。"
            )
            self.status_text.set("一键上传暂停：没有可提交内容")
            return

        mode = self.ask_commit_message_mode(staged_statuses)

        if mode is None:
            self.status_text.set("一键上传已取消：未选择提交说明方式")
            return

        commit_commands = []

        if mode == "single":
            msg = self.ask_text_with_menu(
                "统一添加说明",
                "请输入本次上传说明：\n例如：首次上传项目"
            )

            if msg is None:
                self.status_text.set("一键上传已取消：未填写提交说明")
                return

            msg = msg.strip()

            if not msg:
                messagebox.showwarning("提示", "提交说明不能为空")
                return

            commit_commands.append((
                ["commit", "-m", msg],
                "统一添加说明并提交"
            ))

        elif mode == "separate":
            commit_commands = self.build_separate_commit_commands(
                staged_statuses,
                "一键上传已取消：未完成每个文件的提交说明"
            )

            if commit_commands is None:
                return

        if not commit_commands:
            self.status_text.set("一键上传已取消：没有可执行的提交")
            return

        self.run_one_click_commit_and_push(repo, commit_commands, tag_plan)

    def run_one_click_commit_and_push(self, repo, commit_commands, tag_plan=None):
        self.status_text.set("一键上传执行中：正在提交...")

        def task_commit_push():
            all_output = []

            for git_args, step_title in commit_commands:
                all_output.append(f"\n--- {step_title} ---\n")
                all_output.append("git " + " ".join(git_args) + "\n")

                code, output = self.run_command_with_code(["git"] + git_args, repo)
                all_output.append(output)

                if code != 0:
                    self.after(0, lambda text="".join(all_output): self.append_output(text))
                    self.after(0, lambda out=output: self.handle_common_git_problem(out, "添加说明并提交"))
                    self.after(0, lambda: self.status_text.set("一键上传失败：提交失败，可能没有文件变化或存在错误"))
                    return

            self.after(0, lambda: self.status_text.set("提交成功。下一步：推送至 GitHub"))

            branch = self.get_current_branch_for_push(repo)
            if not branch:
                branch = "main"

            upstream = self.run_command(
                ["git", "rev-parse", "--abbrev-ref", "--symbolic-full-name", "@{u}"],
                repo
            ).strip()

            if "fatal" in upstream.lower() or upstream == "":
                push_args = ["push", "-u", "origin", branch]
                push_title = f"首次推送并绑定远程分支：{branch}"
            else:
                push_args = ["push"]
                push_title = "推送至仓库"

            all_output.append(f"\n--- {push_title} ---\n")
            all_output.append("git " + " ".join(push_args) + "\n")

            push_code, push_output = self.run_command_with_code(["git"] + push_args, repo)
            all_output.append(push_output)

            if push_code == 0:
                tag_ok = self.append_tag_push_after_successful_branch_push(repo, all_output, tag_plan)

                self.after(0, lambda text="".join(all_output): self.append_output(text))

                if tag_ok:
                    if tag_plan and tag_plan.get("create_tag"):
                        self.after(0, lambda: self.status_text.set("一键上传成功：代码和版本标签已推送到 GitHub"))
                        self.after(0, lambda: messagebox.showinfo("上传完成", "一键上传已完成，代码和版本标签都已推送到 GitHub。"))
                    else:
                        self.after(0, lambda: self.status_text.set("一键上传成功：文件已推送到 GitHub"))
                        self.after(0, lambda: messagebox.showinfo("上传完成", "一键上传到 GitHub 已完成。"))
                else:
                    self.after(0, lambda: self.status_text.set("代码已推送，但版本标签创建或推送失败"))
                    self.after(0, lambda: messagebox.showwarning("标签推送失败", "代码已推送成功，但版本标签创建或推送失败，请查看输出区域。"))
            else:
                self.after(0, lambda text="".join(all_output): self.append_output(text))
                self.after(0, lambda out=push_output, br=branch: self.handle_push_failure(repo, br, out))

        threading.Thread(target=task_commit_push, daemon=True).start()

    def git_status(self):
        repo = self.get_repo()
        if not repo:
            return

        self.append_output("\n========== 查看仓库状态 ==========\n")
        self.append_output("git status\n\n")
        self.status_text.set("正在查看仓库状态...")

        def task():
            code, output = self.run_command_with_code(["git", "status"], repo)
            self.after(0, lambda: self.show_status_output_with_highlight(output, code, repo))

        threading.Thread(target=task, daemon=True).start()

    def is_git_status_file_line(self, line):
        stripped = line.strip()

        if not stripped:
            return False

        if stripped.startswith("("):
            return False

        if stripped.startswith("use "):
            return False

        status_prefixes = (
            "modified:",
            "new file:",
            "deleted:",
            "renamed:",
            "copied:",
            "typechange:",
            "both modified:",
            "both added:",
            "both deleted:",
            "unmerged:",
            "已修改：",
            "新文件：",
            "已删除：",
            "已重命名：",
            "已复制：",
            "类型变化：",
            "双方都修改：",
            "双方都添加：",
            "双方都删除：",
            "未合并：",
        )

        if stripped.startswith(status_prefixes):
            return True

        # git status 中未跟踪文件一般是缩进后只显示文件名
        if (line.startswith("\t") or line.startswith("        ")) and not stripped.startswith(("(", "（")):
            return True

        # 兼容简短状态输出格式
        if re.match(r"^\s*[MADRCU?]{1,2}\s+.+", line):
            return True

        return False

    def translate_git_status_line(self, line):
        """
        将 git status 常见英文输出汉化。
        注意：文件名、分支名、远程名仍然原样保留，避免影响用户复制命令或识别文件。
        """
        newline = "\n" if line.endswith("\n") else ""
        raw = line[:-1] if newline else line
        stripped = raw.strip()
        indent = raw[:len(raw) - len(raw.lstrip())]

        exact_map = {
            "Changes to be committed:": "已暂存，等待提交的更改：",
            '  (use "git restore --staged <file>..." to unstage)': '  （可使用 git restore --staged <文件>... 取消暂存）',
            "Changes not staged for commit:": "已修改但尚未暂存的更改：",
            '  (use "git add/rm <file>..." to update what will be committed)': '  （可使用 git add/rm <文件>... 更新要提交的内容）',
            '  (use "git restore <file>..." to discard changes in working directory)': '  （可使用 git restore <文件>... 放弃工作区更改）',
            "Untracked files:": "未跟踪文件：",
            '  (use "git add <file>..." to include in what will be committed)': '  （可使用 git add <文件>... 纳入提交）',
            "nothing to commit, working tree clean": "没有需要提交的内容，工作区干净。",
            "no changes added to commit (use \"git add\" and/or \"git commit -a\")": "没有把更改加入暂存区。可使用“添加全部文件 / 添加部分文件”后再提交。",
            "No commits yet": "当前分支还没有提交记录。",
            "Initial commit": "初始提交。",
        }

        if raw in exact_map:
            return exact_map[raw] + newline

        if stripped in exact_map:
            return indent + exact_map[stripped] + newline

        match = re.match(r"^On branch (.+)$", stripped)
        if match:
            return f"{indent}当前分支：{match.group(1)}{newline}"

        match = re.match(r"^Your branch is up to date with '(.+)'\.$", stripped)
        if match:
            return f"{indent}当前分支已与远程分支 '{match.group(1)}' 保持同步。{newline}"

        match = re.match(r"^Your branch is ahead of '(.+)' by (\d+) commit[s]?\.$", stripped)
        if match:
            return f"{indent}当前分支领先远程分支 '{match.group(1)}' {match.group(2)} 个提交。{newline}"

        match = re.match(r"^Your branch is behind '(.+)' by (\d+) commit[s]?, and can be fast-forwarded\.$", stripped)
        if match:
            return f"{indent}当前分支落后远程分支 '{match.group(1)}' {match.group(2)} 个提交，可以快进合并。{newline}"

        match = re.match(r"^Your branch and '(.+)' have diverged,$", stripped)
        if match:
            return f"{indent}当前分支与远程分支 '{match.group(1)}' 已经分叉，{newline}"

        match = re.match(r"^and have (\d+) and (\d+) different commits each, respectively\.$", stripped)
        if match:
            return f"{indent}本地有 {match.group(1)} 个独有提交，远程有 {match.group(2)} 个独有提交。{newline}"

        match = re.match(r"^  \(use \"git pull\" to update your local branch\)$", raw)
        if match:
            return "  （可使用“拉取”更新本地分支）" + newline

        prefix_map = {
            "modified:": "已修改：",
            "new file:": "新文件：",
            "deleted:": "已删除：",
            "renamed:": "已重命名：",
            "copied:": "已复制：",
            "typechange:": "类型变化：",
            "both modified:": "双方都修改：",
            "both added:": "双方都添加：",
            "both deleted:": "双方都删除：",
            "unmerged:": "未合并：",
        }

        for old_prefix, new_prefix in prefix_map.items():
            if stripped.startswith(old_prefix):
                rest = stripped[len(old_prefix):].strip()
                return f"{indent}{new_prefix}   {rest}{newline}"

        return line

    def show_status_output_with_highlight(self, output, code, repo):
        has_warning = False
        has_error = False
        has_crlf_warning = self.is_crlf_warning_text(output)
        has_octal_filename = self.is_octal_escaped_filename_text(output)

        for line in output.splitlines(True):
            display_line = self.translate_git_status_line(line)

            if self.is_error_line(line):
                self.output.insert("end-1c", display_line, ("error_text",))
                has_error = True
            elif self.is_warning_line(line):
                self.output.insert("end-1c", display_line, ("warning_text",))
                has_warning = True
            elif self.is_git_status_file_line(display_line):
                self.output.insert("end-1c", display_line, ("status_file_text",))
            else:
                self.output.insert("end-1c", display_line, ("normal_text",))

        self.output.see("end")

        if code == 0:
            self.update_first_commit_step_status(repo, True, "查看状态")
        else:
            self.status_text.set("查看状态失败：请查看红色错误提示")

        if has_error:
            self.status_text.set("查看状态时检测到错误 / 严重错误，已用红色高亮显示")
        elif has_warning:
            self.status_text.set("查看状态时检测到警告，已用黄色高亮显示")

        diagnostic_text = self.extract_warning_error_lines(output)
        can_auto_fix_warning = has_crlf_warning or has_octal_filename

        if diagnostic_text:
            level = "错误" if has_error else "警告"

            if has_error or not can_auto_fix_warning:
                self.after(80, lambda t=diagnostic_text, lv=level: self.copy_diagnostics_to_clipboard(t, lv))

        if has_crlf_warning:
            self.after(100, lambda t=diagnostic_text: self.prompt_fix_crlf_warning_if_needed(t))

        if has_octal_filename:
            self.after(150, lambda t=diagnostic_text: self.prompt_fix_octal_filename_if_needed(t))

        if has_error or has_warning:
            self.after(120, lambda t=output: self.handle_common_git_problem(t, "查看状态"))

    def git_add_all(self):
        self.run_git(["add", "-A"], "添加全部文件（包含删除文件）")

    def git_add_some(self):
        repo = self.get_repo()
        if not repo:
            return

        file_paths = filedialog.askopenfilenames(
            title="选择要添加到暂存区的文件",
            initialdir=repo
        )

        relative_paths = []

        for file_path in file_paths:
            try:
                relative_path = Path(file_path).resolve().relative_to(Path(repo).resolve())
                relative_paths.append(relative_path.as_posix())
            except ValueError:
                messagebox.showerror("错误", "只能选择当前仓库目录里面的文件")
                return

        deleted_files = self.get_deleted_files_for_add(repo)
        selected_deleted_files = self.ask_select_deleted_files_for_add(deleted_files)

        if selected_deleted_files is None:
            return

        relative_paths.extend(selected_deleted_files)
        relative_paths = list(dict.fromkeys(relative_paths))

        if not relative_paths:
            self.status_text.set("未选择任何文件")
            return

        self.run_git(["add", "--"] + relative_paths, "添加部分文件（可包含删除文件）")

    def get_staged_file_statuses(self, repo):
        """
        获取暂存区文件及状态。
        返回示例：
        [
            {"status": "A", "path": "new.py", "is_deleted": False},
            {"status": "D", "path": "old.py", "is_deleted": True},
            {"status": "R100", "path": "old.py -> new.py", "commit_path": "new.py", "is_deleted": False},
        ]
        """
        code, output = self.run_command_with_code(
            ["git", "diff", "--cached", "--name-status"],
            repo
        )

        if code != 0:
            messagebox.showerror("错误", "获取暂存区文件状态失败，请查看输出区域。")
            self.append_output(output)
            return None

        result = []

        for raw_line in output.splitlines():
            if not raw_line.strip():
                continue

            parts = raw_line.split("\t")
            status = parts[0].strip()

            if status.startswith(("R", "C")) and len(parts) >= 3:
                display_path = f"{parts[1]} -> {parts[2]}"
                commit_path = parts[2]
            elif len(parts) >= 2:
                display_path = parts[1]
                commit_path = parts[1]
            else:
                continue

            result.append({
                "status": status,
                "path": display_path,
                "commit_path": commit_path,
                "is_deleted": status.startswith("D")
            })

        return result

    def split_staged_files_by_delete(self, staged_statuses):
        normal_files = []
        deleted_files = []

        for item in staged_statuses or []:
            commit_path = item.get("commit_path") or item.get("path")

            if item.get("is_deleted"):
                deleted_files.append(commit_path)
            else:
                normal_files.append(commit_path)

        return normal_files, deleted_files

    def build_separate_commit_commands(self, staged_statuses, cancel_status_text):
        """
        每个文件单独添加说明时：
        - 新增 / 修改 / 重命名文件：逐个询问说明；
        - 已删除文件：不再逐个询问说明，自动使用“删除 {文件名}”作为说明。
        """
        normal_files, deleted_files = self.split_staged_files_by_delete(staged_statuses)
        commands = []

        for file_path in normal_files:
            default_msg = f"更新 {Path(file_path).name}"

            msg = self.ask_text_with_menu(
                "每个文件单独添加说明",
                f"文件：{file_path}\n\n请输入该文件的提交说明：",
                default_msg
            )

            if msg is None:
                self.status_text.set(cancel_status_text)
                return None

            msg = msg.strip()

            if not msg:
                messagebox.showwarning("提示", f"文件 {file_path} 的提交说明不能为空")
                return None

            commands.append((
                ["commit", "-m", msg, "--", file_path],
                f"提交文件：{file_path}"
            ))

        if deleted_files:
            # 删除文件不再要求用户逐个填写说明，但提交说明要包含具体文件名。
            for file_path in deleted_files:
                delete_msg = f"删除 {Path(file_path).name}"
                commands.append((
                    ["commit", "-m", delete_msg, "--", file_path],
                    f"提交删除文件：{file_path}"
                ))

        return commands

    def get_staged_files(self, repo):
        """
        获取已经添加到暂存区、等待提交的文件。
        """
        code, output = self.run_command_with_code(
            ["git", "diff", "--cached", "--name-only"],
            repo
        )

        if code != 0:
            messagebox.showerror("错误", "获取暂存区文件失败，请查看输出区域。")
            self.append_output(output)
            return None

        files = [
            line.strip()
            for line in output.splitlines()
            if line.strip()
        ]

        return files

    def ask_commit_message_mode(self, staged_files):
        """
        选择提交说明方式：
        1. 所有文件统一添加一个提交说明；
        2. 每个文件单独添加提交说明并分别提交。
        """
        dialog = tk.Toplevel(self)
        dialog.withdraw()
        dialog.title("选择添加说明方式")
        dialog.resizable(True, True)
        dialog.transient(self)
        dialog.grab_set()
        dialog.attributes("-topmost", True)

        result = {"mode": None}

        frame = ttk.Frame(dialog, padding=16)
        frame.pack(fill="both", expand=True)

        delete_count = 0
        normal_count = len(staged_files)

        for item in staged_files:
            if isinstance(item, dict):
                if item.get("is_deleted"):
                    delete_count += 1
            elif str(item).startswith("[已删除]"):
                delete_count += 1

        if delete_count:
            normal_count = len(staged_files) - delete_count
            tip_text = (
                f"当前暂存区共有 {len(staged_files)} 个文件等待提交。\n"
                f"其中已删除文件 {delete_count} 个。\n\n"
                "说明：选择“每个文件单独添加说明”时，已删除文件不会逐个询问说明，\n"
                "会自动使用“删除 {文件名}”作为提交说明。\n\n"
                "请选择添加说明方式："
            )
        else:
            tip_text = (
                f"当前暂存区共有 {len(staged_files)} 个文件等待提交。\n\n"
                "请选择添加说明方式："
            )

        ttk.Label(
            frame,
            text=tip_text,
            justify="left"
        ).pack(anchor="w", pady=(0, 10))

        file_preview_frame = ttk.LabelFrame(frame, text="等待提交的文件", padding=8)
        file_preview_frame.pack(fill="both", expand=True, pady=(0, 12))

        listbox = tk.Listbox(file_preview_frame, height=8, font=("Consolas", 9))
        listbox.grid(row=0, column=0, sticky="nsew")

        y_scroll = ttk.Scrollbar(file_preview_frame, orient="vertical", command=listbox.yview)
        y_scroll.grid(row=0, column=1, sticky="ns")
        listbox.configure(yscrollcommand=y_scroll.set)

        file_preview_frame.rowconfigure(0, weight=1)
        file_preview_frame.columnconfigure(0, weight=1)

        for file_item in staged_files:
            if isinstance(file_item, dict):
                if file_item.get("is_deleted"):
                    listbox.insert("end", f"[已删除 / 自动说明] {file_item.get('path')}")
                else:
                    status = file_item.get("status", "")
                    listbox.insert("end", f"[{status}] {file_item.get('path')}")
            else:
                listbox.insert("end", str(file_item))

        btn_frame = ttk.Frame(frame)
        btn_frame.pack(fill="x")

        def choose(mode):
            result["mode"] = mode
            dialog.destroy()

        ttk.Button(
            btn_frame,
            text="统一添加说明",
            command=lambda: choose("single")
        ).pack(side="left", padx=(0, 8))

        ttk.Button(
            btn_frame,
            text="每个文件单独添加说明",
            command=lambda: choose("separate")
        ).pack(side="left", padx=(0, 8))

        ttk.Button(
            btn_frame,
            text="取消",
            command=lambda: choose(None)
        ).pack(side="left")

        dialog.protocol("WM_DELETE_WINDOW", lambda: choose(None))
        self.center_dialog(dialog, min_width=620, min_height=380)
        self.wait_window(dialog)

        return result["mode"]

    def git_commit(self):
        repo = self.get_repo()
        if not repo:
            return

        if not self.ensure_git_identity_or_prompt():
            return

        staged_statuses = self.get_staged_file_statuses(repo)

        if staged_statuses is None:
            return

        if not staged_statuses:
            messagebox.showinfo(
                "没有可提交的文件",
                "当前暂存区没有文件，无法添加说明并提交。\n\n"
                "请先点击“添加全部文件”或“添加部分文件”，再点击“添加说明”。"
            )
            self.status_text.set("没有可提交的暂存文件：请先添加文件")
            return

        mode = self.ask_commit_message_mode(staged_statuses)

        if mode is None:
            return

        if mode == "single":
            msg = self.ask_text_with_menu(
                "统一添加说明",
                "请输入本次提交说明："
            )

            if msg is None:
                return

            msg = msg.strip()
            if msg == "":
                messagebox.showwarning("提示", "提交说明不能为空")
                return

            self.run_git(["commit", "-m", msg], "统一添加说明并提交")
            return

        if mode == "separate":
            commands = self.build_separate_commit_commands(
                staged_statuses,
                "已取消按文件分别提交"
            )

            if commands is None:
                return

            if not commands:
                return

            self.run_git_sequence(commands, "每个文件单独添加说明并提交")

    def repo_has_commits(self, repo):
        code, _ = self.run_command_with_code(
            ["git", "rev-parse", "--verify", "HEAD"],
            repo
        )
        return code == 0

    def repo_has_origin_remote(self, repo):
        remote_output = self.run_command(["git", "remote"], repo).strip()
        return "origin" in remote_output.split()

    def get_current_branch_for_push(self, repo):
        branch = self.run_command(["git", "symbolic-ref", "--short", "HEAD"], repo).strip()

        if branch and "fatal" not in branch.lower():
            return branch

        branch = self.run_command(["git", "rev-parse", "--abbrev-ref", "HEAD"], repo).strip()

        if branch and "fatal" not in branch.lower() and branch != "HEAD":
            return branch

        return ""

    def build_new_repo_push_guide(self, has_origin):
        if has_origin:
            remote_step = "4. 点击“推送至仓库”，工具会自动执行首次推送并绑定远程分支"
        else:
            remote_step = "4. 点击“添加远程 origin”，粘贴 GitHub 仓库地址\n5. 点击“推送至仓库”，工具会自动执行首次推送并绑定远程分支"

        return (
            "检测到当前仓库还没有任何提交记录，因此不能直接推送。\n"
            "请按需生成忽略文件，随后点击“添加全部文件”或“添加部分文件”。\n\n"
            "新仓库标准操作步骤：\n"
            "1. 先确认是否需要“生成忽略文件”，例如 UE5 / Unity 项目建议先生成 .gitignore\n"
            "2. 点击“添加全部文件”或“添加部分文件”\n"
            "3. 点击“添加说明”，填写本次提交说明并完成第一次提交\n"
            f"{remote_step}\n\n"
            "说明：GitHub 只能接收已经提交过的内容，空仓库直接推送会报错。"
        )

    def show_new_repo_push_guide(self, has_origin):
        message = self.build_new_repo_push_guide(has_origin)

        self.append_output("\n========== 新仓库推送提示 ==========\n")
        self.append_output(message + "\n")
        self.status_text.set("新仓库需要先提交一次再推送")
        messagebox.showinfo("新仓库推送提示", message)

    def show_existing_repo_no_origin_guide(self):
        message = (
            "检测到当前仓库已经有提交记录，但还没有添加远程 origin。\n\n"
            "标准操作步骤：\n"
            "1. 点击“添加远程 origin”\n"
            "2. 粘贴 GitHub 仓库地址，例如：https://github.com/用户名/仓库名.git\n"
            "3. 再点击“推送至仓库”\n\n"
            "工具会自动判断是否是第一次推送，并在首次推送时自动绑定远程上游分支。"
        )

        self.append_output("\n========== 缺少远程 origin ==========\n")
        self.append_output(message + "\n")
        self.status_text.set("缺少远程 origin")
        messagebox.showinfo("缺少远程 origin", message)

    def is_push_rejected_fetch_first(self, output):
        lower_output = output.lower()

        patterns = [
            "[rejected]",
            "fetch first",
            "failed to push some refs",
            "updates were rejected because the remote contains work that you do not",
            "have locally",
            "use 'git pull' before pushing again",
            "use \"git pull\" before pushing again",
        ]

        return (
            ("fetch first" in lower_output or "failed to push some refs" in lower_output)
            and any(pattern in lower_output for pattern in patterns)
        )

    def handle_push_rejected_fetch_first(self, repo, branch, output):
        message = (
            "推送被 GitHub 拒绝：远程仓库包含本地没有的提交。\\n\\n"
            "这通常出现在：\\n"
            "1. GitHub 仓库创建时勾选了 README / .gitignore / License\\n"
            "2. 其他电脑或其他成员已经先推送过内容\\n"
            "3. 远程 main 分支比本地 main 分支更新\\n\\n"
            "标准处理步骤：\\n"
            "1. 先点击“拉取”，把 GitHub 上的内容拉到本地\\n"
            "2. 如果出现冲突，先解决冲突，再执行“添加全部文件”→“添加说明”\\n"
            "3. 再点击“推送至仓库”\\n\\n"
            "推荐命令：git pull --rebase origin "
            f"{branch}\\n"
        )

        self.append_output("\\n========== 推送被拒绝：需要先拉取 ==========\n")
        self.append_output(message + "\\n")
        self.status_text.set("推送失败：远程有本地没有的提交，下一步先点击“拉取”")

        should_pull = messagebox.askyesno(
            "推送被拒绝：需要先拉取",
            message + "\\n是否现在自动执行“拉取并变基”命令？"
        )

        if should_pull:
            self.run_git(["pull", "--rebase", "origin", branch], "拉取远程更新并变基")

    def handle_push_failure(self, repo, branch, output):
        if self.is_push_rejected_fetch_first(output):
            self.handle_push_rejected_fetch_first(repo, branch, output)
            return

        if self.handle_common_git_problem(output, "推送至仓库"):
            return

        self.status_text.set("推送至仓库失败：请查看红色错误提示，修正后重试")

    # ============================================================
    # GitHub Actions 工作流模板
    # ============================================================

    def get_workflow_template_dir(self):
        """
        用户可编辑模板保存位置：
        用户目录/.git_gui_workflow_templates
        """
        template_dir = Path.home() / ".git_gui_workflow_templates"
        template_dir.mkdir(parents=True, exist_ok=True)
        return template_dir

    def safe_workflow_template_filename(self, name):
        safe_name = re.sub(r'[<>:"/\\|?*\s]+', "_", str(name).strip())
        safe_name = safe_name.strip("._")

        if not safe_name:
            safe_name = "Workflow_Template"

        return safe_name + ".workflow_template.yml"

    def safe_workflow_file_name(self, name):
        safe_name = re.sub(r'[<>:"/\\|?*\s]+', "-", str(name).strip())
        safe_name = safe_name.strip(".-_/")

        if not safe_name:
            safe_name = "workflow"

        if not safe_name.lower().endswith((".yml", ".yaml")):
            safe_name += ".yml"

        return safe_name

    def get_default_workflow_template_texts(self):
        python_ci = """name: Python CI

on:
  push:
    branches: [ main ]
  pull_request:
    branches: [ main ]
  workflow_dispatch:

jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - name: 拉取代码
        uses: actions/checkout@v4

      - name: 设置 Python
        uses: actions/setup-python@v5
        with:
          python-version: '3.11'

      - name: 安装依赖
        run: |
          python -m pip install --upgrade pip
          if [ -f requirements.txt ]; then pip install -r requirements.txt; fi

      - name: 运行基础检查
        run: |
          python --version
"""

        node_ci = """name: Node.js CI

on:
  push:
    branches: [ main ]
  pull_request:
    branches: [ main ]
  workflow_dispatch:

jobs:
  build:
    runs-on: ubuntu-latest
    steps:
      - name: 拉取代码
        uses: actions/checkout@v4

      - name: 设置 Node.js
        uses: actions/setup-node@v4
        with:
          node-version: '20'

      - name: 安装依赖
        run: |
          if [ -f package-lock.json ]; then npm ci; else npm install; fi

      - name: 构建项目
        run: |
          npm run build --if-present
"""

        tag_release = """name: Tag Release

on:
  push:
    tags:
      - 'v*.*.*'
  workflow_dispatch:

jobs:
  release:
    runs-on: ubuntu-latest
    steps:
      - name: 拉取代码
        uses: actions/checkout@v4

      - name: 创建 GitHub Release
        uses: softprops/action-gh-release@v2
        with:
          generate_release_notes: true
"""

        windows_python_exe = """name: Build Windows EXE

on:
  push:
    tags:
      - 'v*.*.*'
  workflow_dispatch:

jobs:
  build:
    runs-on: windows-latest
    steps:
      - name: 拉取代码
        uses: actions/checkout@v4

      - name: 设置 Python
        uses: actions/setup-python@v5
        with:
          python-version: '3.11'

      - name: 安装 PyInstaller
        run: |
          python -m pip install --upgrade pip
          pip install pyinstaller
          if (Test-Path requirements.txt) { pip install -r requirements.txt }

      - name: 打包 EXE
        run: |
          pyinstaller --onefile *.py

      - name: 上传构建产物
        uses: actions/upload-artifact@v4
        with:
          name: windows-exe
          path: dist/*
"""

        ue5_placeholder = """name: UE5 Placeholder Workflow

on:
  workflow_dispatch:

jobs:
  note:
    runs-on: ubuntu-latest
    steps:
      - name: 提示
        run: |
          echo "UE5 项目通常需要自托管 Runner 或专门配置的构建环境。"
          echo "你可以在此基础上改成自己的 UE5 自动构建流程。"
"""

        return {
            "Python_CI": python_ci,
            "Node_js_CI": node_ci,
            "Tag_Release": tag_release,
            "Build_Windows_EXE": windows_python_exe,
            "UE5_Placeholder": ue5_placeholder,
        }

    def ensure_workflow_template_files(self):
        template_dir = self.get_workflow_template_dir()

        for name, content in self.get_default_workflow_template_texts().items():
            path = template_dir / self.safe_workflow_template_filename(name)

            # 不覆盖用户已经修改过的模板
            if not path.exists():
                path.write_text(content, encoding="utf-8")

    def display_name_from_workflow_template_path(self, path):
        name = path.name

        if name.endswith(".workflow_template.yml"):
            name = name[:-len(".workflow_template.yml")]
        elif name.endswith(".workflow_template.yaml"):
            name = name[:-len(".workflow_template.yaml")]

        mapping = {
            "Python_CI": "Python 持续集成",
            "Node_js_CI": "Node.js 持续集成",
            "Tag_Release": "标签触发 Release",
            "Build_Windows_EXE": "Python 打包 Windows EXE",
            "UE5_Placeholder": "UE5 占位工作流",
        }

        return mapping.get(name, name.replace("_", " "))

    def get_workflow_templates(self):
        self.ensure_workflow_template_files()

        templates = {}
        template_dir = self.get_workflow_template_dir()

        for path in sorted(template_dir.glob("*.workflow_template.yml")) + sorted(template_dir.glob("*.workflow_template.yaml")):
            try:
                display_name = self.display_name_from_workflow_template_path(path)
                templates[display_name] = {
                    "path": path,
                    "content": path.read_text(encoding="utf-8", errors="replace")
                }
            except Exception:
                pass

        return templates

    def save_workflow_template_file(self, name, content):
        template_dir = self.get_workflow_template_dir()
        path = template_dir / self.safe_workflow_template_filename(name)
        path.write_text(content, encoding="utf-8")
        return path

    def import_workflow_template_file(self):
        file_path = filedialog.askopenfilename(
            title="导入工作流模板",
            filetypes=[
                ("YAML / 文本文件", "*.yml *.yaml *.txt"),
                ("YAML 文件", "*.yml *.yaml"),
                ("所有文件", "*.*"),
            ]
        )

        if not file_path:
            return None

        path = Path(file_path)

        try:
            content = path.read_text(encoding="utf-8", errors="replace")
        except Exception as e:
            messagebox.showerror("错误", f"导入模板失败：\n{e}")
            return None

        name = path.stem.replace(".workflow_template", "")
        self.save_workflow_template_file(name, content)
        return self.display_name_from_workflow_template_path(self.get_workflow_template_dir() / self.safe_workflow_template_filename(name))

    def export_workflow_template_file(self, template_name, template_data):
        if not template_name or not template_data:
            messagebox.showinfo("提示", "请先选择一个模板")
            return False

        default_file = self.safe_workflow_file_name(template_name)

        file_path = filedialog.asksaveasfilename(
            title="导出工作流模板",
            initialfile=default_file,
            defaultextension=".yml",
            filetypes=[("YAML 文件", "*.yml *.yaml"), ("所有文件", "*.*")]
        )

        if not file_path:
            return False

        try:
            Path(file_path).write_text(template_data["content"], encoding="utf-8")
            messagebox.showinfo("成功", f"工作流模板已导出：\n{file_path}")
            return True
        except Exception as e:
            messagebox.showerror("错误", f"导出模板失败：\n{e}")
            return False

    def git_create_workflow(self):
        repo = self.get_repo()
        if not repo:
            return

        workflow_files = self.get_workflow_files(repo)

        if workflow_files:
            messagebox.showinfo("提示", "当前仓库已经存在工作流，将显示“编辑工作流文件”按钮。")
            self.update_workflow_buttons_by_repo()
            return

        templates = self.get_workflow_templates()

        dialog = tk.Toplevel(self)
        dialog.withdraw()
        dialog.title("一键创建 GitHub Actions 工作流")
        dialog.resizable(True, True)
        dialog.transient(self)
        dialog.grab_set()
        dialog.attributes("-topmost", True)

        frame = ttk.Frame(dialog, padding=16)
        frame.pack(fill="both", expand=True)

        ttk.Label(
            frame,
            text=(
                "当前仓库没有检测到 GitHub Actions 工作流。\n"
                "请选择模板生成 .github/workflows/*.yml 文件。"
            ),
            justify="left"
        ).pack(anchor="w", pady=(0, 8))

        select_frame = ttk.LabelFrame(frame, text="工作流模板", padding=10)
        select_frame.pack(fill="x", pady=(0, 12))

        template_var = tk.StringVar()
        values = list(templates.keys())
        template_var.set(values[0] if values else "")

        combo = ttk.Combobox(
            select_frame,
            textvariable=template_var,
            values=values,
            state="readonly",
            width=42,
            font=("Microsoft YaHei UI", 10)
        )
        combo.pack(fill="x")

        preview_outer = ttk.LabelFrame(frame, text="工作流内容预览", padding=8)
        preview_outer.pack(fill="both", expand=True, pady=(0, 12))

        preview_frame = ttk.Frame(preview_outer)
        preview_frame.pack(fill="both", expand=True)

        preview = tk.Text(
            preview_frame,
            width=86,
            height=20,
            font=("Consolas", 9),
            wrap="none",
            undo=False,
            bg="#f7f7f7",
            fg="#111111",
            insertbackground="#111111",
            relief="solid",
            borderwidth=1
        )
        preview.grid(row=0, column=0, sticky="nsew")

        y_scroll = ttk.Scrollbar(preview_frame, orient="vertical", command=preview.yview)
        y_scroll.grid(row=0, column=1, sticky="ns")

        x_scroll = ttk.Scrollbar(preview_frame, orient="horizontal", command=preview.xview)
        x_scroll.grid(row=1, column=0, sticky="ew")

        preview.configure(yscrollcommand=y_scroll.set, xscrollcommand=x_scroll.set)

        preview_frame.rowconfigure(0, weight=1)
        preview_frame.columnconfigure(0, weight=1)

        def reload_templates(selected_name=None):
            nonlocal templates
            templates = self.get_workflow_templates()
            names = list(templates.keys())
            combo.configure(values=names)

            if selected_name and selected_name in names:
                template_var.set(selected_name)
            elif template_var.get() not in names:
                template_var.set(names[0] if names else "")

            refresh_preview()

        def refresh_preview(*_):
            preview.configure(state="normal")
            preview.delete("1.0", "end")

            selected = template_var.get()
            if selected in templates:
                preview.insert(
                    "1.0",
                    f"# 当前选择模板：{selected}\n"
                    f"# 下面内容将写入当前仓库的 .github/workflows/ 目录\n"
                    f"# {'=' * 70}\n\n"
                    + templates[selected]["content"]
                )
            else:
                preview.insert("1.0", "当前没有可用模板，请点击“添加模板”或“导入模板”。")

            preview.configure(state="disabled")

        def add_template():
            editor_result = self.open_ignore_template_editor(
                "添加工作流模板",
                "New_Workflow",
                "name: Custom Workflow\n\non:\n  workflow_dispatch:\n\njobs:\n  build:\n    runs-on: ubuntu-latest\n    steps:\n      - uses: actions/checkout@v4\n"
            )

            if not editor_result["saved"]:
                return

            self.save_workflow_template_file(editor_result["name"], editor_result["content"])
            reload_templates(editor_result["name"])

        def edit_template():
            selected = template_var.get()

            if selected not in templates:
                messagebox.showinfo("提示", "请先选择一个模板")
                return

            editor_result = self.open_ignore_template_editor(
                "编辑工作流模板",
                selected,
                templates[selected]["content"]
            )

            if not editor_result["saved"]:
                return

            old_path = templates[selected]["path"]
            new_path = self.get_workflow_template_dir() / self.safe_workflow_template_filename(editor_result["name"])

            if new_path != old_path and old_path.exists():
                try:
                    old_path.unlink()
                except Exception:
                    pass

            self.save_workflow_template_file(editor_result["name"], editor_result["content"])
            reload_templates(editor_result["name"])

        def import_template():
            imported_name = self.import_workflow_template_file()
            if imported_name:
                reload_templates(imported_name)

        def export_template():
            selected = template_var.get()
            if selected not in templates:
                messagebox.showinfo("提示", "请先选择一个模板")
                return
            self.export_workflow_template_file(selected, templates[selected])

        def create_workflow_file():
            selected = template_var.get()

            if selected not in templates:
                messagebox.showwarning("提示", "请先选择一个工作流模板")
                return

            default_file = self.safe_workflow_file_name(selected)
            workflow_file_name = self.ask_text_with_menu(
                "工作流文件名",
                "请输入要创建的工作流文件名：\n例如：ci.yml、release.yml",
                default_file
            )

            if workflow_file_name is None:
                return

            workflow_file_name = self.safe_workflow_file_name(workflow_file_name)
            workflow_dir = Path(repo) / ".github" / "workflows"
            workflow_dir.mkdir(parents=True, exist_ok=True)

            workflow_path = workflow_dir / workflow_file_name

            if workflow_path.exists():
                overwrite = messagebox.askyesno(
                    "文件已存在",
                    f"工作流文件已存在：\n{workflow_path}\n\n是否覆盖？"
                )

                if not overwrite:
                    return

            try:
                workflow_path.write_text(templates[selected]["content"], encoding="utf-8")
            except Exception as e:
                messagebox.showerror("错误", f"创建工作流失败：\n{e}")
                return

            self.append_output(f"\n已创建工作流文件：{workflow_path}\n")
            self.status_text.set("工作流文件已创建")
            self.update_workflow_buttons_by_repo()
            messagebox.showinfo(
                "创建完成",
                f"已创建工作流文件：\n{workflow_path}\n\n"
                "后续可点击“添加全部文件 / 一键上传到 GitHub”提交并推送。"
            )
            dialog.destroy()

        combo.bind("<<ComboboxSelected>>", refresh_preview)

        btn_frame = ttk.Frame(frame)
        btn_frame.pack(fill="x")

        ttk.Button(btn_frame, text="添加模板", command=add_template).pack(side="left", padx=(0, 8))
        ttk.Button(btn_frame, text="编辑当前模板", command=edit_template).pack(side="left", padx=(0, 8))
        ttk.Button(btn_frame, text="导入模板", command=import_template).pack(side="left", padx=(0, 8))
        ttk.Button(btn_frame, text="导出模板", command=export_template).pack(side="left", padx=(0, 8))
        ttk.Button(btn_frame, text="创建工作流", command=create_workflow_file).pack(side="left", padx=(0, 8))
        ttk.Button(btn_frame, text="关闭", command=dialog.destroy).pack(side="left")

        dialog.protocol("WM_DELETE_WINDOW", dialog.destroy)
        refresh_preview()
        self.center_dialog(dialog, min_width=860, min_height=660)
        self.wait_window(dialog)

    def open_file_with_system(self, path, title="文件"):
        try:
            if os.name == "nt":
                os.startfile(str(path))
            elif sys.platform == "darwin":
                subprocess.Popen(["open", str(path)])
            else:
                subprocess.Popen(["xdg-open", str(path)])

            self.append_output(f"\n已打开{title}：{path}\n")
            return True

        except Exception:
            try:
                webbrowser.open(Path(path).as_uri())
                self.append_output(f"\n已打开{title}：{path}\n")
                return True
            except Exception as e:
                messagebox.showerror("错误", f"无法打开{title}：\n{e}")
                return False

    def git_edit_workflow(self):
        repo = self.get_repo()
        if not repo:
            return

        workflow_files = self.get_workflow_files(repo)

        if not workflow_files:
            messagebox.showinfo("提示", "当前仓库还没有工作流，将显示“一键创建工作流”按钮。")
            self.update_workflow_buttons_by_repo()
            return

        if len(workflow_files) == 1:
            if self.open_file_with_system(workflow_files[0], "工作流文件"):
                self.status_text.set("已打开工作流文件")
            return

        dialog = tk.Toplevel(self)
        dialog.withdraw()
        dialog.title("选择要编辑的工作流文件")
        dialog.resizable(True, True)
        dialog.transient(self)
        dialog.grab_set()
        dialog.attributes("-topmost", True)

        frame = ttk.Frame(dialog, padding=16)
        frame.pack(fill="both", expand=True)

        ttk.Label(frame, text="检测到多个工作流文件，请选择要编辑的文件：").pack(anchor="w", pady=(0, 8))

        listbox = tk.Listbox(frame, height=10, font=("Consolas", 9))
        listbox.pack(fill="both", expand=True, pady=(0, 12))

        for file_path in workflow_files:
            try:
                rel_path = file_path.relative_to(Path(repo))
            except ValueError:
                rel_path = file_path
            listbox.insert("end", str(rel_path).replace("\\", "/"))

        def open_selected():
            selection = listbox.curselection()

            if not selection:
                messagebox.showinfo("提示", "请先选择一个工作流文件")
                return

            file_path = workflow_files[selection[0]]
            dialog.destroy()

            if self.open_file_with_system(file_path, "工作流文件"):
                self.status_text.set("已打开工作流文件")

        btn_frame = ttk.Frame(frame)
        btn_frame.pack(fill="x")

        ttk.Button(btn_frame, text="打开选中", command=open_selected).pack(side="left", padx=(0, 8))
        ttk.Button(btn_frame, text="关闭", command=dialog.destroy).pack(side="left")

        dialog.protocol("WM_DELETE_WINDOW", dialog.destroy)
        self.center_dialog(dialog, min_width=680, min_height=420)
        self.wait_window(dialog)

    def update_workflow_buttons_by_repo(self):
        repo = self.get_repo_silent()

        if not repo or not Path(repo).exists():
            self.hide_builtin_if_exists("create_workflow")
            self.hide_builtin_if_exists("edit_workflow")
            return

        if self.repo_has_workflows(repo):
            self.hide_builtin_if_exists("create_workflow")
            self.show_builtin_if_exists("edit_workflow")
        else:
            self.show_builtin_if_exists("create_workflow")
            self.hide_builtin_if_exists("edit_workflow")

    def get_workflow_files(self, repo):
        """
        检测仓库是否存在 GitHub Actions 工作流。
        默认识别：.github/workflows/*.yml 和 *.yaml
        """
        workflow_dir = Path(repo) / ".github" / "workflows"

        if not workflow_dir.exists() or not workflow_dir.is_dir():
            return []

        files = []
        for pattern in ("*.yml", "*.yaml"):
            files.extend(workflow_dir.glob(pattern))

        return sorted(files)

    def repo_has_workflows(self, repo):
        return bool(self.get_workflow_files(repo))

    def suggest_next_version_tag(self, repo):
        """
        根据已有 v1.2.3 形式的标签，自动建议下一个补丁版本。
        没有标签时默认 v1.0.0。
        """
        code, output = self.run_command_with_code(["git", "tag", "--list", "v*"], repo)

        if code != 0:
            return "v1.0.0"

        versions = []

        for line in output.splitlines():
            tag = line.strip()
            match = re.fullmatch(r"v(\d+)\.(\d+)\.(\d+)", tag)

            if match:
                versions.append(tuple(int(x) for x in match.groups()))

        if not versions:
            return "v1.0.0"

        major, minor, patch = max(versions)
        return f"v{major}.{minor}.{patch + 1}"

    def git_tag_exists(self, repo, tag_name):
        code, _ = self.run_command_with_code(
            ["git", "rev-parse", "-q", "--verify", f"refs/tags/{tag_name}"],
            repo
        )
        return code == 0

    def ask_workflow_tag_plan(self, repo):
        """
        如果仓库存在 GitHub Actions 工作流，则让用户选择：
        1. 创建版本标签并推送；
        2. 只推送，不创建标签；
        3. 取消本次推送。
        """
        workflow_files = self.get_workflow_files(repo)

        if not workflow_files:
            return {
                "cancel": False,
                "create_tag": False,
                "tag_name": "",
            }

        dialog = tk.Toplevel(self)
        dialog.withdraw()
        dialog.title("检测到 GitHub 工作流")
        dialog.resizable(True, True)
        dialog.transient(self)
        dialog.grab_set()
        dialog.attributes("-topmost", True)

        result = {
            "cancel": True,
            "create_tag": False,
            "tag_name": "",
        }

        frame = ttk.Frame(dialog, padding=16)
        frame.pack(fill="both", expand=True)

        ttk.Label(
            frame,
            text=(
                "检测到当前仓库存在 GitHub Actions 工作流文件。\n\n"
                "如果你的工作流依赖版本标签触发发布，可以选择“创建版本标签并推送”。\n"
                "如果只是普通上传代码，可以选择“只推送，不创建标签”。"
            ),
            justify="left"
        ).pack(anchor="w", pady=(0, 10))

        workflow_box = ttk.LabelFrame(frame, text="检测到的工作流文件", padding=8)
        workflow_box.pack(fill="both", expand=True, pady=(0, 12))

        listbox = tk.Listbox(workflow_box, height=5, font=("Consolas", 9))
        listbox.grid(row=0, column=0, sticky="nsew")

        y_scroll = ttk.Scrollbar(workflow_box, orient="vertical", command=listbox.yview)
        y_scroll.grid(row=0, column=1, sticky="ns")
        listbox.configure(yscrollcommand=y_scroll.set)

        workflow_box.rowconfigure(0, weight=1)
        workflow_box.columnconfigure(0, weight=1)

        for file_path in workflow_files:
            try:
                rel_path = file_path.relative_to(Path(repo))
            except ValueError:
                rel_path = file_path
            listbox.insert("end", str(rel_path).replace("\\", "/"))

        tag_frame = ttk.LabelFrame(frame, text="版本标签", padding=8)
        tag_frame.pack(fill="x", pady=(0, 12))

        ttk.Label(
            tag_frame,
            text="标签名称："
        ).pack(side="left")

        tag_var = tk.StringVar(value=self.suggest_next_version_tag(repo))
        tag_entry = ttk.Entry(tag_frame, textvariable=tag_var, width=24)
        tag_entry.pack(side="left", padx=(8, 0))

        btn_frame = ttk.Frame(frame)
        btn_frame.pack(fill="x")

        def choose_tag():
            tag_name = tag_var.get().strip()

            if not tag_name:
                messagebox.showwarning("提示", "版本标签不能为空")
                return

            if " " in tag_name:
                messagebox.showwarning("提示", "版本标签不能包含空格")
                return

            if self.git_tag_exists(repo, tag_name):
                messagebox.showwarning(
                    "标签已存在",
                    f"标签 {tag_name} 已存在，请换一个版本号。"
                )
                return

            result["cancel"] = False
            result["create_tag"] = True
            result["tag_name"] = tag_name
            dialog.destroy()

        def choose_push_only():
            result["cancel"] = False
            result["create_tag"] = False
            result["tag_name"] = ""
            dialog.destroy()

        def cancel():
            result["cancel"] = True
            dialog.destroy()

        ttk.Button(btn_frame, text="创建版本标签并推送", command=choose_tag).pack(side="left", padx=(0, 8))
        ttk.Button(btn_frame, text="只推送，不创建标签", command=choose_push_only).pack(side="left", padx=(0, 8))
        ttk.Button(btn_frame, text="取消推送", command=cancel).pack(side="left")

        dialog.protocol("WM_DELETE_WINDOW", cancel)
        tag_entry.focus_set()
        tag_entry.select_range(0, "end")
        self.center_dialog(dialog, min_width=680, min_height=420)
        self.wait_window(dialog)

        return result

    def append_tag_push_after_successful_branch_push(self, repo, all_output, tag_plan):
        """
        分支推送成功后，如果用户选择创建版本标签，则创建本地标签并推送到 origin。
        返回 True / False 表示标签步骤是否成功。
        """
        if not tag_plan or not tag_plan.get("create_tag"):
            return True

        tag_name = tag_plan.get("tag_name", "").strip()

        if not tag_name:
            return True

        all_output.append(f"\n--- 创建版本标签：{tag_name} ---\n")
        all_output.append(f"git tag -a {tag_name} -m 发布 {tag_name}\n")

        tag_code, tag_output = self.run_command_with_code(
            ["git", "tag", "-a", tag_name, "-m", f"发布 {tag_name}"],
            repo
        )
        all_output.append(tag_output)

        if tag_code != 0:
            return False

        all_output.append(f"\n--- 推送版本标签：{tag_name} ---\n")
        all_output.append(f"git push origin {tag_name}\n")

        push_tag_code, push_tag_output = self.run_command_with_code(
            ["git", "push", "origin", tag_name],
            repo
        )
        all_output.append(push_tag_output)

        return push_tag_code == 0

    def git_smart_push(self):
        repo = self.get_repo()
        if not repo:
            return

        self.append_output("\n========== 推送至仓库 ==========\n")
        self.status_text.set("正在判断仓库状态...")

        inside_output = self.run_command(
            ["git", "rev-parse", "--is-inside-work-tree"],
            repo
        ).strip()

        if inside_output.lower() != "true":
            messagebox.showerror("错误", "当前目录不是 Git 仓库，请先初始化仓库或克隆仓库。")
            self.status_text.set("当前目录不是 Git 仓库")
            return

        has_commits = self.repo_has_commits(repo)
        has_origin = self.repo_has_origin_remote(repo)

        # 新仓库：没有任何提交，直接 push 一定会失败，因此只给标准操作步骤。
        if not has_commits:
            self.show_new_repo_push_guide(has_origin)
            return

        # 有提交但没有远程 origin：提示先添加远程。
        if not has_origin:
            self.show_existing_repo_no_origin_guide()
            return

        branch = self.get_current_branch_for_push(repo)

        if not branch:
            messagebox.showerror("错误", "无法获取当前分支名，请确认这是正常的 Git 分支。")
            self.status_text.set("无法获取当前分支")
            return

        # 检测到 .github/workflows 后，先让用户选择是否创建版本标签。
        tag_plan = self.ask_workflow_tag_plan(repo)

        if tag_plan.get("cancel"):
            self.status_text.set("推送已取消")
            return

        def task():
            upstream = self.run_command(
                ["git", "rev-parse", "--abbrev-ref", "--symbolic-full-name", "@{u}"],
                repo
            ).strip()

            if "fatal" in upstream.lower() or upstream == "":
                args = ["push", "-u", "origin", branch]
                title = f"首次推送并绑定远程分支：{branch}"
                message = (
                    f"检测到当前分支“{branch}”已有提交，但还没有绑定远程上游分支。\n\n"
                    f"将执行首次推送：git push -u origin {branch}\n\n"
                    "之后再点击“推送至仓库”时，就会自动使用普通推送命令。"
                )
                self.after(0, lambda: self.append_output(message + "\n\n"))
            else:
                args = ["push"]
                title = "推送到已绑定远程分支"

            all_output = []
            all_output.append(f"--- {title} ---\n")
            all_output.append(f"git {' '.join(args)}\n\n")

            code, output = self.run_command_with_code(["git"] + args, repo)
            all_output.append(output)

            if code == 0:
                tag_ok = self.append_tag_push_after_successful_branch_push(repo, all_output, tag_plan)

                self.after(0, lambda text="".join(all_output): self.append_output(text))

                if tag_ok:
                    if tag_plan.get("create_tag"):
                        self.after(0, lambda: self.status_text.set("推送完成：代码和版本标签已推送到 GitHub"))
                        self.after(0, lambda: messagebox.showinfo("推送完成", "代码已推送，版本标签也已推送到 GitHub。"))
                    else:
                        self.after(0, lambda: self.update_first_commit_step_status(repo, True, "推送至仓库"))
                else:
                    self.after(0, lambda: self.status_text.set("代码已推送，但版本标签创建或推送失败"))
                    self.after(0, lambda: messagebox.showwarning("标签推送失败", "代码已推送成功，但版本标签创建或推送失败，请查看输出区域。"))
            else:
                self.after(0, lambda text="".join(all_output): self.append_output(text))
                self.after(0, lambda: self.handle_push_failure(repo, branch, output))

        threading.Thread(target=task, daemon=True).start()

    def git_pull(self):
        self.run_git(["pull"], "拉取")

    def format_remote_changed_files_detail(self, name_status_output):
        """
        将 git diff --name-status HEAD..@{u} 输出汉化。
        用于本地落后 GitHub 时显示：远程版本到底改了哪些文件。
        """
        if not name_status_output or not name_status_output.strip():
            return "未检测到具体文件差异。"

        status_map = {
            "A": "远程新增",
            "M": "远程修改",
            "D": "远程删除",
            "R": "远程重命名",
            "C": "远程复制",
            "T": "类型变化",
            "U": "未合并",
        }

        lines = []

        for raw_line in name_status_output.splitlines():
            raw_line = raw_line.strip()

            if not raw_line:
                continue

            parts = raw_line.split("\t")
            status = parts[0].strip()

            # R100 / R092 / C100 这类状态只取首字母判断。
            status_key = status[:1]
            status_text = status_map.get(status_key, status)

            if status_key == "R" and len(parts) >= 3:
                lines.append(f"- {status_text}：{parts[1]}  →  {parts[2]}")
            elif status_key == "C" and len(parts) >= 3:
                lines.append(f"- {status_text}：{parts[1]}  →  {parts[2]}")
            elif len(parts) >= 2:
                lines.append(f"- {status_text}：{parts[1]}")
            else:
                lines.append(f"- {raw_line}")

        return "\n".join(lines) if lines else "未检测到具体文件差异。"

    def get_remote_changed_files_detail(self, repo):
        """
        查看本地 HEAD 到远程上游 @{u} 之间变化的文件。
        注意：调用前应先 git fetch。
        """
        code, output = self.run_command_with_code(
            ["git", "diff", "--name-status", "HEAD..@{u}"],
            repo
        )

        if code != 0:
            return "获取远程变化文件失败：\n" + output.strip()

        return self.format_remote_changed_files_detail(output)

    def git_check_sync_status(self, auto=False):
        repo = self.get_repo_silent() if auto else self.get_repo()
        if not repo:
            return

        if not auto:
            self.append_output("\n========== 检查本地与 GitHub 同步状态 ==========\n")

        self.status_text.set("正在检查本地是否落后于 GitHub...")

        def task():
            inside_output = self.run_command(["git", "rev-parse", "--is-inside-work-tree"], repo).strip()

            if inside_output.lower() != "true":
                self.after(0, lambda: self.handle_sync_result(
                    auto=auto,
                    ok=False,
                    message="当前目录不是 Git 仓库。",
                    upstream="",
                    ahead=0,
                    behind=0,
                    detail=""
                ))
                return

            has_commits = self.repo_has_commits(repo)
            has_origin = self.repo_has_origin_remote(repo)

            if not has_commits:
                message = self.build_new_repo_push_guide(has_origin)
                self.after(0, lambda: self.handle_sync_result(
                    auto=auto,
                    ok=False,
                    message=message,
                    upstream="",
                    ahead=0,
                    behind=0,
                    detail=""
                ))
                return

            upstream_output = self.run_command(
                ["git", "rev-parse", "--abbrev-ref", "--symbolic-full-name", "@{u}"],
                repo
            ).strip()

            if "fatal" in upstream_output.lower() or upstream_output == "":
                if has_origin:
                    message = (
                        "当前分支已有提交，但还没有绑定远程上游分支。\n\n"
                        "标准操作步骤：\n"
                        "1. 点击“推送至仓库”\n"
                        "2. 工具会自动执行首次推送并绑定远程分支\n"
                        "3. 之后再次推送会自动使用普通推送命令"
                    )
                else:
                    message = (
                        "当前分支已有提交，但还没有添加远程 origin。\n\n"
                        "标准操作步骤：\n"
                        "1. 点击“添加远程 origin”并粘贴 GitHub 仓库地址\n"
                        "2. 点击“推送至仓库”\n"
                        "3. 工具会自动执行首次推送并绑定远程分支"
                    )

                self.after(0, lambda: self.handle_sync_result(
                    auto=auto,
                    ok=False,
                    message=message,
                    upstream="",
                    ahead=0,
                    behind=0,
                    detail=""
                ))
                return

            fetch_code, fetch_output = self.run_command_with_code(["git", "fetch", "--prune"], repo)

            if fetch_code != 0:
                self.after(0, lambda: self.handle_sync_result(
                    auto=auto,
                    ok=False,
                    message="拉取远程信息失败，请检查网络、GitHub 连接或代理设置。",
                    upstream=upstream_output,
                    ahead=0,
                    behind=0,
                    detail=fetch_output
                ))
                return

            count_output = self.run_command(
                ["git", "rev-list", "--left-right", "--count", "HEAD...@{u}"],
                repo
            ).strip()

            try:
                parts = count_output.split()
                ahead = int(parts[0])
                behind = int(parts[1])
            except Exception:
                self.after(0, lambda: self.handle_sync_result(
                    auto=auto,
                    ok=False,
                    message=f"无法解析同步状态：{count_output}",
                    upstream=upstream_output,
                    ahead=0,
                    behind=0,
                    detail=""
                ))
                return

            remote_files_detail = ""
            if behind > 0:
                remote_files_detail = self.get_remote_changed_files_detail(repo)

            self.after(0, lambda: self.handle_sync_result(
                auto=auto,
                ok=True,
                message="",
                upstream=upstream_output,
                ahead=ahead,
                behind=behind,
                detail=remote_files_detail
            ))

        threading.Thread(target=task, daemon=True).start()

    def handle_sync_result(self, auto, ok, message, upstream, ahead, behind, detail):
        if not ok:
            first_line = message.split("\n", 1)[0] if message else "检查同步失败"
            self.status_text.set(first_line)

            if not auto:
                self.append_output(message + "\n")
                if detail:
                    self.append_output(detail + "\n")

                # 对新仓库 / 未绑定远程等流程类提示，弹窗显示步骤更清晰。
                if "标准操作步骤" in message or "新仓库标准操作步骤" in message:
                    messagebox.showinfo("操作提示", message)

            return

        info = f"远程上游：{upstream}\n本地领先：{ahead} 个提交\n本地落后：{behind} 个提交\n"

        if behind > 0 and detail:
            info += "\nGitHub 上比本地更新的文件：\n"
            info += detail + "\n"

        if not auto:
            self.append_output(info)

        if ahead == 0 and behind == 0:
            self.status_text.set("本地与 GitHub 已同步")
            if not auto:
                messagebox.showinfo("同步状态", "本地与 GitHub 已同步。")
            return

        if ahead == 0 and behind > 0:
            self.status_text.set(f"本地落后 GitHub {behind} 个提交，已显示远程变更文件")

            file_text = detail if detail else "未获取到具体文件差异。"
            should_pull = messagebox.askyesno(
                "本地版本落后",
                f"检测到 GitHub 上有 {behind} 个新提交，本地版本落后。\n\n"
                f"GitHub 上比本地更新的文件：\n{file_text}\n\n"
                f"是否现在执行 git pull 拉取更新？"
            )
            if should_pull:
                self.run_git(["pull"], "拉取 GitHub 更新")
            return

        if ahead > 0 and behind == 0:
            self.status_text.set(f"本地领先 GitHub {ahead} 个提交")
            should_push = messagebox.askyesno(
                "本地版本领先",
                f"检测到本地有 {ahead} 个提交还没有推送到 GitHub。\n\n是否现在执行推送？"
            )
            if should_push:
                self.git_smart_push()
            return

        self.status_text.set(f"本地和 GitHub 已分叉：领先 {ahead}，落后 {behind}，已显示远程变更文件")
        file_text = detail if detail else "未获取到具体文件差异。"
        messagebox.showwarning(
            "分支已分叉",
            f"本地和 GitHub 都有新的提交：\n\n"
            f"本地领先：{ahead} 个提交\n"
            f"本地落后：{behind} 个提交\n\n"
            f"GitHub 上比本地更新的文件：\n{file_text}\n\n"
            f"建议先手动处理冲突风险，再执行拉取或合并操作。"
        )

    def git_log(self):
        repo = self.get_repo()
        if not repo:
            return

        self.append_output("\n========== 查看最近 20 条提交记录 ==========\n")
        self.append_output("git log --oneline --decorate -n 20\n\n")
        self.status_text.set("正在读取提交记录...")

        def task():
            output = self.run_command(["git", "log", "--oneline", "--decorate", "-n", "20"], repo)
            self.after(0, lambda: self.show_log_with_clickable_commit(output))

        threading.Thread(target=task, daemon=True).start()

    def show_log_with_clickable_commit(self, log_text):
        for line in log_text.splitlines():
            match = re.match(r"^([0-9a-fA-F]{4,40})(.*)$", line)

            if match:
                commit_id = match.group(1)
                line_start = self.output.index("end-1c")
                self.output.insert("end-1c", line + "\n", ("normal_text",))
                id_end = f"{line_start}+{len(commit_id)}c"
                self.output.tag_add("commit_link", line_start, id_end)
                self.output.tag_raise("commit_link")
            else:
                self.output.insert("end-1c", line + "\n", ("normal_text",))

        self.output.insert(
            "end-1c",
            "\n提示：按住 Ctrl，然后左键点击蓝色 提交 ID，可以切换到该版本。\n",
            ("normal_text",)
        )

        self.output.see("end")
        self.status_text.set("提交记录读取完成")

    def git_show_all_branches(self):
        self.run_git(["branch", "-a"], "查看所有分支")

    def git_create_branch(self):
        repo = self.get_repo()
        if not repo:
            return

        branch_name = self.ask_text_with_menu(
            "创建分支",
            "请输入新分支名称：\n例如：feature/input-ui"
        )

        if branch_name is None:
            return

        branch_name = branch_name.strip()

        if branch_name == "":
            messagebox.showwarning("提示", "分支名称不能为空")
            return

        switch_now = messagebox.askyesno(
            "创建分支",
            f"是否创建并立即切换到分支：{branch_name}？\n\n"
            f"选择“是”：执行 git checkout -b {branch_name}\n"
            f"选择“否”：只创建分支，不切换"
        )

        if switch_now:
            self.run_git(["checkout", "-b", branch_name], f"创建并切换分支：{branch_name}")
        else:
            self.run_git(["branch", branch_name], f"创建分支：{branch_name}")

    def git_rename_default_branch(self):
        repo = self.get_repo()
        if not repo:
            return

        if not self.is_inside_git_repo(repo):
            messagebox.showwarning("提示", "当前目录不是 Git 仓库，请先初始化仓库。")
            return

        current_branch = self.get_current_branch_for_push(repo)
        if not current_branch:
            current_branch = "main"

        new_branch = self.ask_text_with_menu(
            "修改默认分支名称",
            "请输入新的默认分支名称：\n建议使用 main",
            current_branch
        )

        if new_branch is None:
            return

        new_branch = new_branch.strip()

        if new_branch == "":
            messagebox.showwarning("提示", "分支名称不能为空")
            return

        if " " in new_branch:
            messagebox.showwarning("提示", "分支名称不能包含空格")
            return

        confirm = messagebox.askyesno(
            "确认修改默认分支名称",
            f"确定要把当前分支名称修改为：{new_branch} 吗？\n\n"
            f"将执行：git branch -M {new_branch}\n\n"
            f"如果远程 GitHub 默认分支还不是 {new_branch}，"
            f"推送后还需要到 GitHub 仓库设置里确认默认分支。"
        )

        if not confirm:
            return

        self.run_git(["branch", "-M", new_branch], f"修改默认分支名称为 {new_branch}")

    def git_commit_some_to_branch(self):
        repo = self.get_repo()
        if not repo:
            return

        if not self.ensure_git_identity_or_prompt():
            return

        branch_name = self.ask_text_with_menu(
            "提交部分文件到指定分支",
            "请输入目标分支名称：\n例如：main 或 feature/input-ui"
        )

        if branch_name is None:
            return

        branch_name = branch_name.strip()

        if branch_name == "":
            messagebox.showwarning("提示", "目标分支名称不能为空")
            return

        file_paths = filedialog.askopenfilenames(
            title="选择要提交到指定分支的文件",
            initialdir=repo
        )

        if not file_paths:
            return

        relative_paths = []

        for file_path in file_paths:
            try:
                relative_path = Path(file_path).resolve().relative_to(Path(repo).resolve())
                relative_paths.append(relative_path.as_posix())
            except ValueError:
                messagebox.showerror("错误", "只能选择当前仓库目录里面的文件")
                return

        msg = self.ask_text_with_menu(
            "提交部分文件到指定分支",
            "请输入提交说明："
        )

        if msg is None:
            return

        msg = msg.strip()

        if msg == "":
            messagebox.showwarning("提示", "提交说明不能为空")
            return

        files_text = "\n".join(relative_paths)
        confirm = messagebox.askyesno(
            "确认提交",
            f"将执行以下操作：\n\n"
            f"1. 切换到分支：{branch_name}\n"
            f"2. 添加这些文件：\n{files_text}\n"
            f"3. 提交说明：{msg}\n\n"
            f"是否继续？"
        )

        if not confirm:
            return

        self.run_git_sequence(
            [
                (["checkout", branch_name], f"切换到指定分支：{branch_name}"),
                (["add", "--"] + relative_paths, "添加部分文件"),
                (["commit", "-m", msg], "提交说明")
            ],
            f"提交部分文件到指定分支：{branch_name}"
        )

    def git_commit_all_to_branch(self):
        repo = self.get_repo()
        if not repo:
            return

        if not self.ensure_git_identity_or_prompt():
            return

        branch_name = self.ask_text_with_menu(
            "提交全部文件到指定分支",
            "请输入目标分支名称：\n例如：main 或 feature/input-ui"
        )

        if branch_name is None:
            return

        branch_name = branch_name.strip()

        if branch_name == "":
            messagebox.showwarning("提示", "目标分支名称不能为空")
            return

        msg = self.ask_text_with_menu(
            "提交全部文件到指定分支",
            "请输入提交说明："
        )

        if msg is None:
            return

        msg = msg.strip()

        if msg == "":
            messagebox.showwarning("提示", "提交说明不能为空")
            return

        confirm = messagebox.askyesno(
            "确认提交",
            f"将执行以下操作：\n\n"
            f"1. 切换到分支：{branch_name}\n"
            f"2. 添加全部文件：git add .\n"
            f"3. 提交说明：{msg}\n\n"
            f"是否继续？"
        )

        if not confirm:
            return

        self.run_git_sequence(
            [
                (["checkout", branch_name], f"切换到指定分支：{branch_name}"),
                (["add", "."], "添加全部文件"),
                (["commit", "-m", msg], "提交说明")
            ],
            f"提交全部文件到指定分支：{branch_name}"
        )

    def git_remote(self):
        self.run_git(["remote", "-v"], "查看远程仓库")

    def git_add_remote(self):
        url = self.ask_text_with_menu(
            "添加远程仓库",
            "请输入 GitHub 仓库地址：\n例如：https://github.com/用户名/仓库名.git"
        )

        if url is None:
            return

        url = url.strip()
        if url == "":
            messagebox.showwarning("提示", "远程仓库地址不能为空")
            return

        self.run_git(["remote", "add", "origin", url], "添加远程仓库 origin")
        self.after(1200, self.check_repo_after_choose)

    def git_set_remote(self):
        url = self.ask_text_with_menu(
            "修改远程仓库",
            "请输入新的 GitHub 仓库地址：\n例如：https://github.com/用户名/仓库名.git"
        )

        if url is None:
            return

        url = url.strip()
        if url == "":
            messagebox.showwarning("提示", "远程仓库地址不能为空")
            return

        self.run_git(["remote", "set-url", "origin", url], "修改远程仓库 origin")
        self.after(1200, self.check_repo_after_choose)

    def git_fix_line_endings_windows(self):
        repo = self.get_repo()
        if not repo:
            return False

        if not Path(repo).exists():
            messagebox.showerror("错误", "当前仓库路径不存在")
            return False

        self.is_running_line_ending_fix = True

        message = (
            "该功能用于修复 Windows 下常见提示：\n\n"
            "warning: LF will be replaced by CRLF the next time Git touches it\n\n"
            "处理方式：\n"
            "1. 在当前仓库写入 / 更新 .gitattributes\n"
            "2. 将 Python、C/C++、UE/Unity 常见文本文件统一按 LF 保存\n"
            "3. 将 .bat、.cmd、.ps1、.sln 等 Windows 文件按 CRLF 保存\n"
            "4. 当前仓库设置 core.autocrlf=false，由 .gitattributes 接管换行符规则\n\n"
            "是否继续？"
        )

        if not messagebox.askyesno("修复 Windows 换行符警告", message):
            self.is_running_line_ending_fix = False
            return False

        gitattributes_path = Path(repo) / ".gitattributes"

        block = """\n# ===== Git GUI Tool line ending rules BEGIN =====\n# Cross-platform line ending rules for Windows development\n* text=auto\n\n# Source code / scripts usually keep LF\n*.py text eol=lf\n*.c text eol=lf\n*.h text eol=lf\n*.cpp text eol=lf\n*.hpp text eol=lf\n*.cs text eol=lf\n*.java text eol=lf\n*.js text eol=lf\n*.ts text eol=lf\n*.json text eol=lf\n*.uproject text eol=lf\n*.uplugin text eol=lf\n*.ini text eol=lf\n*.md text eol=lf\n*.txt text eol=lf\n\n# Windows command/project files keep CRLF\n*.bat text eol=crlf\n*.cmd text eol=crlf\n*.ps1 text eol=crlf\n*.sln text eol=crlf\n*.vcxproj text eol=crlf\n*.vcxproj.filters text eol=crlf\n\n# Binary files\n*.png binary\n*.jpg binary\n*.jpeg binary\n*.gif binary\n*.ico binary\n*.uasset binary\n*.umap binary\n*.fbx binary\n*.wav binary\n*.mp3 binary\n*.mp4 binary\n*.zip binary\n*.7z binary\n*.rar binary\n# ===== Git GUI Tool line ending rules END =====\n"""

        try:
            if gitattributes_path.exists():
                old_text = gitattributes_path.read_text(encoding="utf-8", errors="replace")

                if "# ===== Git GUI Tool line ending rules BEGIN =====" not in old_text:
                    new_text = old_text.rstrip() + "\n" + block
                    gitattributes_path.write_text(new_text, encoding="utf-8")
            else:
                gitattributes_path.write_text(block.lstrip(), encoding="utf-8")

        except Exception as e:
            self.is_running_line_ending_fix = False
            messagebox.showerror("错误", f"写入 .gitattributes 失败：\n{e}")
            return False

        self.append_output("\n========== 修复 Windows 换行符警告 ==========\n")
        self.append_output(f"已更新：{gitattributes_path}\n")

        # 当前仓库使用 .gitattributes 接管换行符，避免 Git 自动按全局 autocrlf 反复提示。
        code1, output1 = self.run_command_with_code(["git", "config", "core.autocrlf", "false"], repo)
        code2, output2 = self.run_command_with_code(["git", "config", "core.safecrlf", "false"], repo)

        self.append_output("git config core.autocrlf false\n")
        if output1.strip():
            self.append_output(output1 + "\n")

        self.append_output("git config core.safecrlf false\n")
        if output2.strip():
            self.append_output(output2 + "\n")

        if code1 != 0 or code2 != 0:
            self.is_running_line_ending_fix = False
            messagebox.showwarning(
                "提示",
                "换行符规则文件已写入，但 Git 配置命令可能没有全部执行成功。\n请查看输出区域。"
            )
            return False

        do_renormalize = messagebox.askyesno(
            "是否重新规范化已跟踪文件",
            "是否现在执行：git add --renormalize . ？\n\n"
            "建议：\n"
            "1. 如果你准备马上提交本次换行符修复，选择“是”\n"
            "2. 如果你只想先写入规则，稍后再处理，选择“否”\n\n"
            "执行后可继续点击“添加说明”提交。"
        )

        if do_renormalize:
            self.run_git(["add", "--renormalize", "."], "重新规范化换行符")
        else:
            self.append_output(
                "\n已完成基础修复。\n"
                "后续标准操作：\n"
                "1. 点击“添加全部文件”\n"
                "2. 点击“添加说明”\n"
                "3. 点击“推送至仓库”\n"
            )

        self.is_running_line_ending_fix = False
        self.status_text.set("Windows 换行符警告修复已完成")
        return True

    def git_fix_chinese(self):
        repo = self.get_repo_silent()
        cwd = repo if repo and Path(repo).exists() else str(Path.home())

        self.is_running_chinese_filename_fix = True
        self.append_output("\n========== 修复中文文件名显示 ==========" + "\n")
        self.append_output("git config --global core.quotepath false\n\n")

        code, output = self.run_command_with_code(
            ["git", "config", "--global", "core.quotepath", "false"],
            cwd
        )

        if output.strip():
            self.append_output(output + "\n")

        self.is_running_chinese_filename_fix = False

        if code == 0:
            self.hide_builtin_if_exists("fix_chinese")
            self.status_text.set("中文文件名显示已修复。下一次查看状态时会显示中文文件名")
            messagebox.showinfo(
                "修复完成",
                "已执行：git config --global core.quotepath false\n\n"
                "之后 Git 输出会尽量显示中文文件名，而不是八进制转义。\n"
                "可重新点击“查看状态”确认。"
            )
            return True
        else:
            self.status_text.set("修复中文显示失败：请查看红色错误提示")
            messagebox.showerror("错误", "修复中文文件名显示失败，请查看输出区域。")
            return False

    def is_fix_chinese_done(self, repo):
        output = self.run_command(["git", "config", "--global", "--get", "core.quotepath"], repo).strip().lower()
        return output == "false"

    def git_current_branch(self):
        self.run_git(["rev-parse", "--abbrev-ref", "HEAD"], "查看当前分支")

    def git_checkout_branch(self):
        branch = self.ask_text_with_menu(
            "切回指定分支",
            "请输入要切回的分支名：\n通常是 main，也可能是 master",
            "main"
        )

        if branch is None:
            return

        branch = branch.strip()
        if branch == "":
            messagebox.showwarning("提示", "分支名不能为空")
            return

        self.run_git(["checkout", branch], f"切回指定分支：{branch}")

    def git_checkout_commit_by_input(self):
        commit_id = self.ask_text_with_menu(
            "切换到指定版本",
            "请输入要切换到的 提交 ID：\n例如：e5e5fc8"
        )

        if commit_id is None:
            return

        commit_id = commit_id.strip()
        if commit_id == "":
            messagebox.showwarning("提示", "提交 ID 不能为空")
            return

        confirm = messagebox.askyesno(
            "确认切换版本",
            f"确定要切换到这个版本吗？\n\n提交 ID：{commit_id}\n\n注意：这会切换整个项目版本。"
        )

        if not confirm:
            return

        self.run_git(["checkout", commit_id], f"切换到版本：{commit_id}")

    def git_restore_files(self):
        repo = self.get_repo()
        if not repo:
            return

        commit_id = self.ask_text_with_menu(
            "恢复指定文件到旧版本",
            "请输入要恢复到的旧版本 提交 ID：\n例如：e5e5fc8"
        )

        if commit_id is None:
            return

        commit_id = commit_id.strip()
        if commit_id == "":
            messagebox.showwarning("提示", "提交 ID 不能为空")
            return

        file_paths = filedialog.askopenfilenames(
            title="选择要恢复的一个或多个文件",
            initialdir=repo
        )

        if not file_paths:
            return

        relative_paths = []
        for file_path in file_paths:
            try:
                relative_path = Path(file_path).resolve().relative_to(Path(repo).resolve())
                relative_paths.append(relative_path.as_posix())
            except ValueError:
                messagebox.showerror("错误", "只能选择当前仓库目录里面的文件")
                return

        files_text = "\n".join(relative_paths)
        confirm = messagebox.askyesno(
            "确认恢复",
            f"确定要把这些文件恢复到旧版本吗？\n\n旧版本：{commit_id}\n\n文件：\n{files_text}\n\n恢复后还需要执行：\n添加全部文件 → 添加说明 → 推送至仓库"
        )

        if not confirm:
            return

        self.run_git(["restore", "--source", commit_id, "--"] + relative_paths, "恢复指定文件到旧版本")


if __name__ == "__main__":
    app = GitGuiApp()
    app.mainloop()
