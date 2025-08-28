import sys
import sqlite3
import os
import shutil
import subprocess
import time
from typing import Any
import requests
import math
import threading
import urllib.parse
import webbrowser
import random
import ctypes
import html

# Hide console window immediately on Windows
if os.name == 'nt':  # Windows
    try:
        ctypes.windll.user32.ShowWindow(ctypes.windll.kernel32.GetConsoleWindow(), 0)
    except:
        pass
from PySide6.QtWidgets import (
    QApplication, QWidget, QVBoxLayout, QHBoxLayout, QListWidget, QListWidgetItem, QPushButton,
    QLineEdit, QLabel, QCheckBox, QGroupBox, QSpacerItem, QSizePolicy, QFrame, QTabWidget,
    QInputDialog, QMessageBox, QAbstractItemView, QDialog, QListWidget as QListWidgetDialog,
    QGraphicsDropShadowEffect, QTreeWidget, QTreeWidgetItem, QStyledItemDelegate
)
from PySide6.QtGui import QFont, QPixmap, QIcon, QPainter, QPen, QCursor, QColor, QLinearGradient
from PySide6.QtCore import Qt, QSize, QEvent, QTimer, QPoint
from PySide6.QtWidgets import QListView
from playwright.sync_api import sync_playwright, TimeoutError as PWTimeoutError
from cryptography.fernet import Fernet

DB_FILE = "accounts.db"
PROFILE_DIR = "profiles"

# --- Simple at-rest encryption using Fernet ---
_FERNET: Fernet | None = None
# Old (insecure) location: next to DB
_KEY_FILE_OLD = os.path.join(os.path.dirname(os.path.abspath(DB_FILE)), ".ramn_key")
# New (protected) location under user's Local AppData
_KEY_DIR_NEW = os.path.join(os.getenv("LOCALAPPDATA", os.path.expanduser("~")), "RAMN")
_KEY_FILE = os.path.join(_KEY_DIR_NEW, ".ramn_key")

# Windows DPAPI helpers (user scope)
class _DATA_BLOB(ctypes.Structure):
    _fields_ = [("cbData", ctypes.c_ulong), ("pbData", ctypes.c_void_p)]

def _win_protect(data: bytes) -> bytes | None:
    try:
        CryptProtectData = ctypes.windll.crypt32.CryptProtectData
        LocalFree = ctypes.windll.kernel32.LocalFree
    except Exception:
        return None
    in_blob = _DATA_BLOB(len(data), ctypes.cast(ctypes.create_string_buffer(data), ctypes.c_void_p))
    out_blob = _DATA_BLOB()
    if CryptProtectData(ctypes.byref(in_blob), None, None, None, None, 0, ctypes.byref(out_blob)):
        try:
            buf = ctypes.string_at(out_blob.pbData, out_blob.cbData)
            return bytes(buf)
        finally:
            LocalFree(out_blob.pbData)
    return None

def _win_unprotect(data: bytes) -> bytes | None:
    try:
        CryptUnprotectData = ctypes.windll.crypt32.CryptUnprotectData
        LocalFree = ctypes.windll.kernel32.LocalFree
    except Exception:
        return None
    in_blob = _DATA_BLOB(len(data), ctypes.cast(ctypes.create_string_buffer(data), ctypes.c_void_p))
    out_blob = _DATA_BLOB()
    if CryptUnprotectData(ctypes.byref(in_blob), None, None, None, None, 0, ctypes.byref(out_blob)):
        try:
            buf = ctypes.string_at(out_blob.pbData, out_blob.cbData)
            return bytes(buf)
        finally:
            LocalFree(out_blob.pbData)
    return None

def _get_fernet() -> Fernet:
    global _FERNET
    if _FERNET is not None:
        return _FERNET
    # Ensure key file exists and is DPAPI-protected at the new location; migrate if needed
    try:
        os.makedirs(_KEY_DIR_NEW, exist_ok=True)

        key_bytes: bytes | None = None

        # 1) Migration: if old plaintext key exists next to DB, move and DPAPI-wrap it
        if os.path.exists(_KEY_FILE_OLD) and not os.path.exists(_KEY_FILE):
            try:
                with open(_KEY_FILE_OLD, "rb") as f:
                    old_key = f.read()
                protected = _win_protect(old_key) or old_key  # if DPAPI fails, still move
                with open(_KEY_FILE, "wb") as nf:
                    nf.write(protected)
                try:
                    os.remove(_KEY_FILE_OLD)
                except Exception:
                    pass
            except Exception:
                pass

        if os.path.exists(_KEY_FILE):
            with open(_KEY_FILE, "rb") as f:
                stored = f.read()
            # Try DPAPI-unprotect first; if it fails, assume plaintext key, then wrap and rewrite
            unprotected = _win_unprotect(stored)
            if unprotected:
                key_bytes = unprotected
            else:
                # Probably a legacy plaintext Fernet key; try to use it, then DPAPI-wrap it
                try:
                    Fernet(stored)  # validate
                    key_bytes = stored
                    protected = _win_protect(stored)
                    if protected:
                        with open(_KEY_FILE, "wb") as f:
                            f.write(protected)
                except Exception:
                    # Corrupt key file → regenerate
                    key_bytes = None

        if not key_bytes:
            # Generate fresh Fernet key and DPAPI-wrap it
            key_bytes = Fernet.generate_key()
            protected = _win_protect(key_bytes)
            with open(_KEY_FILE, "wb") as f:
                f.write(protected if protected else key_bytes)
        
        _FERNET = Fernet(key_bytes)
    except Exception:
        # Fallback to an in-memory key (data will be unreadable next run but prevents crash)
        _FERNET = Fernet(Fernet.generate_key())
    return _FERNET

def _is_enc(val: str | None) -> bool:
    if not val:
        return False
    # Fernet tokens are URL-safe base64 and often start with 'gAAAA'. Heuristic check.
    return isinstance(val, str) and val.startswith("gAAAA")

def _enc(val: str | None) -> str | None:
    if val is None:
        return None
    f = _get_fernet()
    try:
        return f.encrypt(val.encode("utf-8")).decode("utf-8")
    except Exception:
        return val

def _dec(val: str | None) -> str | None:
    if val is None:
        return None
    f = _get_fernet()
    try:
        # Try decrypt; if it's not encrypted, return as-is
        if _is_enc(val):
            return f.decrypt(val.encode("utf-8")).decode("utf-8")
        return val
    except Exception:
        return val

def apply_glow(widget, radius=36, color=QColor(64, 120, 255, 110), x_offset=0, y_offset=8):
    """Apply a soft glow/drop-shadow behind a widget.
    Defaults align with the app's dark theme and rounded corners.
    Returns the created effect for optional animation.
    """
    # Qt clamps blur radius internally (usually around 64). Clamp to safe max to avoid odd stops.
    safe_radius = min(max(0, radius), 64)
    effect = QGraphicsDropShadowEffect(widget)
    effect.setBlurRadius(safe_radius)
    effect.setColor(color)
    effect.setOffset(x_offset, y_offset)
    widget.setGraphicsEffect(effect)
    return effect

def start_glow_animation(effect: QGraphicsDropShadowEffect, period_ms: int = 2400,
                         radius_ampl: int = 3, alpha_ampl: int = 18, y_ampl: int = 1):
    """Subtle breathing animation for a QGraphicsDropShadowEffect.
    Keeps a reference to the timer on the effect's parent widget to avoid GC.
    """
    widget = effect.parent()
    if widget is None:
        return

    base_radius = effect.blurRadius()
    base_color = QColor(effect.color())
    base_alpha = base_color.alpha()
    base_offset = effect.offset()
    base_y = base_offset.y()

    start_t = time.monotonic()
    timer = QTimer(widget)
    timer.setInterval(16)  # ~60 FPS

    def tick():
        t = (time.monotonic() - start_t) * 1000.0
        phase = (t % period_ms) / period_ms * 2 * math.pi
        # Ease in/out sine for subtle effect
        s = (1 - math.cos(phase)) * 0.5  # 0..1

        # Animate radius and alpha very slightly
        new_radius = min(64, max(0, base_radius + radius_ampl * (s - 0.5) * 2))
        new_alpha = int(max(0, min(255, base_alpha + alpha_ampl * (s - 0.5) * 2)))
        c = QColor(base_color)
        c.setAlpha(new_alpha)

        # Slight vertical breathing
        new_y = base_y + y_ampl * (s - 0.5) * 2

        effect.setBlurRadius(new_radius)
        effect.setColor(c)
        effect.setOffset(base_offset.x(), new_y)

    timer.timeout.connect(tick)
    timer.start()
    # Keep reference so it isn't garbage-collected
    setattr(widget, "_glow_timer", timer)

class ModernInputDialog(QDialog):
    """Custom input dialog with modern styling."""
    def __init__(self, parent=None, title="Input", label="Input:", text=""):
        super().__init__(None)  # No parent to avoid clipping
        self.parent_widget = parent  # Store parent reference separately
        self.setWindowFlags(Qt.FramelessWindowHint | Qt.WindowStaysOnTopHint)
        self.setAttribute(Qt.WA_TranslucentBackground)
        self.setModal(True)
        
        # Install event filter to handle clicks outside
        if parent:
            QApplication.instance().installEventFilter(self)
        self.resize(350, 180)
        self.dragging = False
        self.drag_start_position = QPoint()
        
        # Main container
        container = QVBoxLayout(self)
        container.setSpacing(0)
        # Add margins so glow around the dialog isn't clipped
        container.setContentsMargins(14, 14, 14, 14)
        
        # Frame container to hold title bar + content (glow under entire dialog)
        frame_container = QWidget()
        frame_container.setStyleSheet(
            """
            QWidget {
                background-color: #0a0d14;
                border-radius: 10px;
            }
            """
        )
        frame_layout = QVBoxLayout(frame_container)
        frame_layout.setContentsMargins(0, 0, 0, 0)
        frame_layout.setSpacing(0)
        container.addWidget(frame_container)

        # Custom title bar
        title_bar = QFrame()
        title_bar.setFixedHeight(30)
        title_bar.setStyleSheet("""
            QFrame {
                background: qlineargradient(spread:pad, x1:0, y1:0, x2:0, y2:1, 
                    stop:0 rgba(20, 25, 35, 0.95), stop:1 rgba(15, 19, 28, 0.98));
                border-top-left-radius: 10px;
                border-top-right-radius: 10px;
                border: none;
            }
        """)
        
        title_layout = QHBoxLayout(title_bar)
        title_layout.setContentsMargins(8, 6, 8, 6)
        
        # Close button
        close_btn = QPushButton("")
        close_btn.setStyleSheet("""
            QPushButton {
                background-color: #ff5f57;
                border: none;
                border-radius: 6px;
                width: 12px;
                height: 12px;
            }
            QPushButton:hover { background-color: #ff3b30; }
        """)
        close_btn.setFixedSize(12, 12)
        close_btn.clicked.connect(self.reject)
        title_layout.addWidget(close_btn)
        
        # Title
        title_label = QLabel(title)
        title_label.setStyleSheet("""
            QLabel {
                color: #f0f0f0;
                font-size: 12px;
                font-weight: 600;
                background: transparent;
            }
        """)
        title_label.setAlignment(Qt.AlignCenter)
        title_layout.addWidget(title_label, 1)
        title_layout.addSpacerItem(QSpacerItem(18, 8, QSizePolicy.Fixed, QSizePolicy.Minimum))
        
        frame_layout.addWidget(title_bar)
        
        # Content
        content = QWidget()
        content.setStyleSheet("""
            QWidget {
                background-color: #0a0d14;
                border-bottom-left-radius: 10px;
                border-bottom-right-radius: 10px;
            }
            QLabel { color: #d0d0d0; font-size: 12px; }
            QLineEdit { 
                background-color: #13171f; 
                border: 1px solid #1e2329; 
                padding: 10px; 
                border-radius: 8px;
                color: #f0f0f0;
            }
            QLineEdit:focus { border: 2px solid rgba(64, 120, 255, 0.5); }
            QPushButton {
                background: qlineargradient(spread:pad, x1:0, y1:0, x2:0, y2:1, 
                    stop:0 rgba(35, 42, 52, 1), stop:1 rgba(25, 30, 38, 1));
                border: 1px solid rgba(255, 255, 255, 0.1);
                padding: 8px 16px;
                border-radius: 8px;
                font-weight: 600;
                color: #f0f0f0;
            }
            QPushButton:hover {
                background: qlineargradient(spread:pad, x1:0, y1:0, x2:0, y2:1, 
                    stop:0 rgba(64, 120, 255, 0.3), stop:1 rgba(44, 90, 200, 0.2));
                border: 1px solid rgba(64, 120, 255, 0.4);
            }
        """)
        content_layout = QVBoxLayout(content)
        content_layout.setContentsMargins(15, 15, 15, 15)
        content_layout.setSpacing(12)
        
        # Label and input
        input_label = QLabel(label)
        content_layout.addWidget(input_label)
        
        self.line_edit = QLineEdit(text)
        content_layout.addWidget(self.line_edit)
        
        # Buttons
        button_layout = QHBoxLayout()
        button_layout.addSpacerItem(QSpacerItem(40, 20, QSizePolicy.Expanding, QSizePolicy.Minimum))
        
        cancel_btn = QPushButton("Cancel")
        cancel_btn.clicked.connect(self.reject)
        button_layout.addWidget(cancel_btn)
        
        ok_btn = QPushButton("OK")
        ok_btn.clicked.connect(self.accept)
        # Make OK the default action for Enter/Return
        ok_btn.setDefault(True)
        ok_btn.setAutoDefault(True)
        button_layout.addWidget(ok_btn)
        
        content_layout.addLayout(button_layout)
        frame_layout.addWidget(content)

        # Dialog frame glow (under everything in this dialog)
        dlg_eff = apply_glow(frame_container, radius=32, color=QColor(64, 120, 255, 96), x_offset=0, y_offset=-2)
        start_glow_animation(dlg_eff, period_ms=2600, radius_ampl=3, alpha_ampl=14, y_ampl=1)
        
        # Set focus to input
        self.line_edit.setFocus()
        # Pressing Enter in the line edit accepts the dialog
        self.line_edit.returnPressed.connect(self.accept)
    
    def get_text(self):
        return self.line_edit.text()
    
    def exec(self):
        """Override exec to center dialog before showing."""
        if self.parent_widget:
            # Get parent's global position and size
            parent_pos = self.parent_widget.mapToGlobal(QPoint(0, 0))
            parent_size = self.parent_widget.size()
            
            # Calculate center position in global coordinates
            center_x = parent_pos.x() + parent_size.width() // 2
            center_y = parent_pos.y() + parent_size.height() // 2
            
            # Position dialog centered on parent
            dialog_size = self.size()
            x = center_x - dialog_size.width() // 2
            y = center_y - dialog_size.height() // 2
            self.move(x, y)
        
        return super().exec()
    
    def eventFilter(self, obj, event):
        """Filter events to handle clicks outside dialog."""
        if event.type() == QEvent.MouseButtonPress and self.isVisible():
            # Get global position of the click
            if hasattr(event, 'globalPosition'):
                global_pos = event.globalPosition().toPoint()
            else:
                global_pos = event.globalPos()
            
            # Check if click is outside our dialog
            dialog_rect = self.geometry()
            if not dialog_rect.contains(global_pos):
                # Don't auto-close input dialogs on outside clicks
                # This prevents accidental closure while typing
                pass
        return super().eventFilter(obj, event)
    
    def hideEvent(self, event):
        """Remove event filter when hiding."""
        if self.parent_widget:
            QApplication.instance().removeEventFilter(self)
        super().hideEvent(event)
    
    # Remove all mouse event handlers to disable dragging
    def mousePressEvent(self, event):
        """Disabled - dialog is not draggable."""
        pass

    def mouseMoveEvent(self, event):
        """Disabled - dialog is not draggable."""
        pass

    def mouseReleaseEvent(self, event):
        """Disabled - dialog is not draggable."""
        pass

class ModernMessageBox(QDialog):
    """Custom message box with modern styling."""
    def __init__(self, parent=None, title="Message", text="", icon_type="info"):
        super().__init__(None)  # No parent to avoid clipping
        self.parent_widget = parent  # Store parent reference separately
        self.setWindowFlags(Qt.FramelessWindowHint | Qt.WindowStaysOnTopHint)
        self.setAttribute(Qt.WA_TranslucentBackground)
        self.setModal(True)
        self.resize(400, 200)
        
        # Main container
        container = QVBoxLayout(self)
        container.setSpacing(0)
        container.setContentsMargins(16, 16, 16, 16)
        
        # Frame container
        frame_container = QWidget()
        frame_container.setStyleSheet("""
            QWidget {
                background-color: #0a0d14;
                border-radius: 12px;
            }
        """)
        frame_layout = QVBoxLayout(frame_container)
        frame_layout.setContentsMargins(0, 0, 0, 0)
        frame_layout.setSpacing(0)
        container.addWidget(frame_container)

        # Title bar
        title_bar = QFrame()
        title_bar.setFixedHeight(35)
        title_bar.setStyleSheet("""
            QFrame {
                background: qlineargradient(spread:pad, x1:0, y1:0, x2:0, y2:1, 
                    stop:0 rgba(20, 25, 35, 0.95), stop:1 rgba(15, 19, 28, 0.98));
                border-top-left-radius: 12px;
                border-top-right-radius: 12px;
                border: none;
            }
        """)
        
        title_layout = QHBoxLayout(title_bar)
        title_layout.setContentsMargins(12, 8, 12, 8)
        
        # Icon based on type
        icon_label = QLabel()
        if icon_type == "warning":
            icon_label.setText("⚠")
            icon_label.setStyleSheet("color: #ff9500; font-size: 16px;")
        elif icon_type == "error":
            icon_label.setText("✕")
            icon_label.setStyleSheet("color: #ff3b30; font-size: 16px;")
        else:
            icon_label.setText("ℹ")
            icon_label.setStyleSheet("color: #4078ff; font-size: 16px;")
        title_layout.addWidget(icon_label)
        
        # Title
        title_label = QLabel(title)
        title_label.setStyleSheet("""
            QLabel {
                color: #f0f0f0;
                font-size: 13px;
                font-weight: 600;
                background: transparent;
                margin-left: 8px;
            }
        """)
        title_layout.addWidget(title_label, 1)
        
        # Close button
        close_btn = QPushButton("×")
        close_btn.setStyleSheet("""
            QPushButton {
                background-color: #ff5f57;
                border: none;
                border-radius: 10px;
                color: #ffffff;
                font-size: 14px;
                font-weight: bold;
                width: 20px;
                height: 20px;
            }
            QPushButton:hover { background-color: #ff3b30; }
        """)
        close_btn.setFixedSize(20, 20)
        close_btn.clicked.connect(self.reject)
        title_layout.addWidget(close_btn)
        
        frame_layout.addWidget(title_bar)
        
        # Content
        content = QWidget()
        content.setStyleSheet("""
            QWidget {
                background-color: #0a0d14;
                border-bottom-left-radius: 12px;
                border-bottom-right-radius: 12px;
            }
            QLabel { color: #d0d0d0; font-size: 13px; line-height: 1.4; }
            QPushButton {
                background: qlineargradient(spread:pad, x1:0, y1:0, x2:0, y2:1, 
                    stop:0 rgba(35, 42, 52, 1), stop:1 rgba(25, 30, 38, 1));
                border: 1px solid rgba(255, 255, 255, 0.1);
                padding: 10px 20px;
                border-radius: 8px;
                font-weight: 600;
                color: #f0f0f0;
                min-width: 80px;
            }
            QPushButton:hover {
                background: qlineargradient(spread:pad, x1:0, y1:0, x2:0, y2:1, 
                    stop:0 rgba(64, 120, 255, 0.3), stop:1 rgba(44, 90, 200, 0.2));
                border: 1px solid rgba(64, 120, 255, 0.4);
            }
        """)
        content_layout = QVBoxLayout(content)
        content_layout.setContentsMargins(20, 20, 20, 20)
        content_layout.setSpacing(20)
        
        # Message text
        text_label = QLabel(text)
        text_label.setWordWrap(True)
        content_layout.addWidget(text_label)
        
        # Buttons
        button_layout = QHBoxLayout()
        button_layout.addStretch()
        
        ok_btn = QPushButton("OK")
        ok_btn.clicked.connect(self.accept)
        ok_btn.setDefault(True)
        button_layout.addWidget(ok_btn)
        
        content_layout.addLayout(button_layout)
        frame_layout.addWidget(content)

        # Apply glow effect
        apply_glow(frame_container, radius=32, color=QColor(64, 120, 255, 96), x_offset=0, y_offset=-2)
    
    def exec(self):
        """Override exec to center dialog before showing."""
        if self.parent_widget:
            parent_pos = self.parent_widget.mapToGlobal(QPoint(0, 0))
            parent_size = self.parent_widget.size()
            center_x = parent_pos.x() + parent_size.width() // 2
            center_y = parent_pos.y() + parent_size.height() // 2
            dialog_size = self.size()
            x = center_x - dialog_size.width() // 2
            y = center_y - dialog_size.height() // 2
            self.move(x, y)
        return super().exec()
    
    @staticmethod
    def information(parent, title, text):
        dialog = ModernMessageBox(parent, title, text, "info")
        return dialog.exec()
    
    @staticmethod
    def warning(parent, title, text):
        dialog = ModernMessageBox(parent, title, text, "warning")
        return dialog.exec()
    
    @staticmethod
    def critical(parent, title, text):
        dialog = ModernMessageBox(parent, title, text, "error")
        return dialog.exec()

class ModernMenu(QWidget):
    """Custom context menu with modern styling."""
    def __init__(self, parent=None):
        super().__init__(None, Qt.FramelessWindowHint | Qt.WindowStaysOnTopHint)
        self.parent_widget = parent
        self.setAttribute(Qt.WA_TranslucentBackground)
        self.setWindowFlags(Qt.FramelessWindowHint | Qt.WindowStaysOnTopHint | Qt.Tool)
        
        # Install event filter on application to catch clicks outside
        if parent:
            QApplication.instance().installEventFilter(self)
        
        self.actions = []
        self.separators = []
        
        # Main layout
        layout = QVBoxLayout(self)
        layout.setContentsMargins(8, 8, 8, 8)
        layout.setSpacing(0)
        
        # Menu container
        self.menu_container = QWidget()
        self.menu_container.setStyleSheet("""
            QWidget {
                background-color: #171c24;
                border: 1px solid #2a3139;
                border-radius: 10px;
            }
        """)
        self.menu_layout = QVBoxLayout(self.menu_container)
        self.menu_layout.setContentsMargins(6, 6, 6, 6)
        self.menu_layout.setSpacing(2)
        layout.addWidget(self.menu_container)
        
        # Apply glow effect
        apply_glow(self.menu_container, radius=20, color=QColor(0, 0, 0, 120), x_offset=0, y_offset=4)
    
    def addAction(self, text, callback=None):
        """Add an action to the menu."""
        action_btn = QPushButton(text)
        action_btn.setStyleSheet("""
            QPushButton {
                background: transparent;
                border: none;
                padding: 8px 16px;
                border-radius: 6px;
                color: #f0f0f0;
                font-size: 13px;
                text-align: left;
            }
            QPushButton:hover {
                background: qlineargradient(spread:pad, x1:0, y1:0, x2:1, y2:0, 
                    stop:0 rgba(64, 120, 255, 0.2), stop:1 rgba(104, 140, 255, 0.15));
                color: #ffffff;
            }
        """)
        if callback:
            action_btn.clicked.connect(lambda: (self.hide(), callback()))
        else:
            action_btn.clicked.connect(self.hide)
        
        self.menu_layout.addWidget(action_btn)
        self.actions.append(action_btn)
        return action_btn
    
    def addSeparator(self):
        """Add a separator line."""
        separator = QFrame()
        separator.setFrameShape(QFrame.HLine)
        separator.setStyleSheet("""
            QFrame {
                background: rgba(255, 255, 255, 0.1);
                border: none;
                height: 1px;
                margin: 6px 8px;
            }
        """)
        self.menu_layout.addWidget(separator)
        self.separators.append(separator)
    
    def addMenu(self, text):
        """Add a submenu (simplified - returns a button that can have actions added)."""
        submenu_btn = QPushButton(f"{text} ►")
        submenu_btn.setStyleSheet("""
            QPushButton {
                background: transparent;
                border: none;
                padding: 8px 16px;
                border-radius: 6px;
                color: #f0f0f0;
                font-size: 13px;
                text-align: left;
            }
            QPushButton:hover {
                background: qlineargradient(spread:pad, x1:0, y1:0, x2:1, y2:0, 
                    stop:0 rgba(64, 120, 255, 0.2), stop:1 rgba(104, 140, 255, 0.15));
                color: #ffffff;
            }
        """)
        self.menu_layout.addWidget(submenu_btn)
        return submenu_btn
    
    def exec(self, pos):
        """Show the menu at the specified position."""
        self.move(pos)
        self.show()
        self.adjustSize()
    
    def isEmpty(self):
        """Check if menu has no actions."""
        return len(self.actions) == 0
    
    def eventFilter(self, obj, event):
        """Filter events to hide menu when clicking outside."""
        if event.type() == QEvent.MouseButtonPress and self.isVisible():
            # Get global position of the click
            if hasattr(event, 'globalPosition'):
                global_pos = event.globalPosition().toPoint()
            else:
                global_pos = event.globalPos()
            
            # Check if click is outside our menu
            menu_rect = self.geometry()
            if not menu_rect.contains(global_pos):
                self.hide()
                return True
        return super().eventFilter(obj, event)
    
    def mousePressEvent(self, event):
        """Handle mouse press within menu."""
        super().mousePressEvent(event)
    
    def hideEvent(self, event):
        """Remove event filter when hiding."""
        if self.parent_widget:
            QApplication.instance().removeEventFilter(self)
        super().hideEvent(event)

class ModernDialog(QDialog):
    """Custom frameless dialog with modern styling."""
    def __init__(self, parent=None, title="Dialog"):
        super().__init__(None)  # No parent to avoid clipping
        self.parent_widget = parent  # Store parent reference separately
        self.setWindowFlags(Qt.FramelessWindowHint | Qt.WindowStaysOnTopHint)
        self.setAttribute(Qt.WA_TranslucentBackground)
        self.dragging = False
        self.drag_start_position = QPoint()
        
        # Main container
        container = QVBoxLayout(self)
        container.setSpacing(0)
        container.setContentsMargins(16, 16, 16, 16)
        
        # Frame container to hold title bar + content (glow under entire dialog)
        frame_container = QWidget()
        frame_container.setStyleSheet(
            """
            QWidget {
                background-color: #0a0d14;
                border-radius: 12px;
            }
            """
        )
        frame_layout = QVBoxLayout(frame_container)
        frame_layout.setContentsMargins(0, 0, 0, 0)
        frame_layout.setSpacing(0)
        container.addWidget(frame_container)

        # Custom title bar for dialog
        title_bar = QFrame()
        title_bar.setFixedHeight(35)
        title_bar.setStyleSheet("""
            QFrame {
                background: qlineargradient(spread:pad, x1:0, y1:0, x2:0, y2:1, 
                    stop:0 rgba(20, 25, 35, 0.95), stop:1 rgba(15, 19, 28, 0.98));
                border: none;
                border-top-left-radius: 12px;
                border-top-right-radius: 12px;
            }
            QPushButton {
                border: none;
                border-radius: 10px;
                font-size: 14px;
                font-weight: bold;
                width: 20px;
                height: 20px;
            }
            QPushButton#dialog_close_btn {
                background-color: #ff5f57;
                color: #ffffff;
            }
            QPushButton#dialog_close_btn:hover {
                background-color: #ff3b30;
            }
        """)
        
        title_layout = QHBoxLayout(title_bar)
        title_layout.setContentsMargins(10, 6, 10, 6)
        
        # Close button
        close_btn = QPushButton("")
        close_btn.setObjectName("dialog_close_btn")
        close_btn.setFixedSize(20, 20)
        close_btn.clicked.connect(self.close)
        title_layout.addWidget(close_btn)
        
        # Title
        title_label = QLabel(title)
        title_label.setStyleSheet("""
            QLabel {
                color: #f0f0f0;
                font-size: 13px;
                font-weight: 600;
                background: transparent;
            }
        """)
        title_label.setAlignment(Qt.AlignCenter)
        title_layout.addWidget(title_label, 1)
        
        # Spacer to balance
        title_layout.addSpacerItem(QSpacerItem(20, 10, QSizePolicy.Fixed, QSizePolicy.Minimum))
        
        frame_layout.addWidget(title_bar)
        
        # Content area
        self.content_widget = QWidget()
        self.content_widget.setStyleSheet("""
            QWidget { 
                background-color: #0a0d14; 
                border-bottom-left-radius: 12px;
                border-bottom-right-radius: 12px;
            }
        """)
        frame_layout.addWidget(self.content_widget)

        # Dialog frame glow (under everything in this dialog)
        dlg_eff = apply_glow(frame_container, radius=34, color=QColor(64, 120, 255, 100), x_offset=0, y_offset=-2)
        start_glow_animation(dlg_eff, period_ms=2600, radius_ampl=3, alpha_ampl=14, y_ampl=1)
        
        # Create content layout for easy access
        self.content_layout = QVBoxLayout(self.content_widget)
        
    def exec(self):
        """Override exec to center dialog before showing."""
        if self.parent_widget:
            # Get parent's global position and size
            parent_pos = self.parent_widget.mapToGlobal(QPoint(0, 0))
            parent_size = self.parent_widget.size()
            
            # Calculate center position in global coordinates
            center_x = parent_pos.x() + parent_size.width() // 2
            center_y = parent_pos.y() + parent_size.height() // 2
            
            # Position dialog centered on parent
            dialog_size = self.size()
            x = center_x - dialog_size.width() // 2
            y = center_y - dialog_size.height() // 2
            self.move(x, y)
        
        return super().exec()
    
    def showEvent(self, event):
        """Set content margins when shown."""
        super().showEvent(event)
        self.content_layout.setContentsMargins(15, 15, 15, 15)
    
    # Remove all mouse event handlers to disable dragging
    def mousePressEvent(self, event):
        """Disabled - dialog is not draggable."""
        pass

    def mouseMoveEvent(self, event):
        """Disabled - dialog is not draggable."""
        pass

    def mouseReleaseEvent(self, event):
        """Disabled - dialog is not draggable."""
        pass

class RobloxAccountManager(QWidget):
    def __init__(self):
        super().__init__()
        # Keep references to Playwright and browser contexts so they remain alive
        self._playwright = None
        self._open_contexts: list[Any] = []
        
        # Remove default window frame and enable resize
        self.setWindowFlags(Qt.FramelessWindowHint | Qt.WindowSystemMenuHint | Qt.WindowMinMaxButtonsHint)
        self.setWindowTitle("Roblox Account Manager")
        self.resize(1260, 640)
        self.setAttribute(Qt.WA_TranslucentBackground)
        

        
        # Track username hiding state
        self.usernames_hidden = False
        self.original_account_data = []  # Store original display data
        
        # Variables for window dragging and resizing
        self.dragging = False
        self.resizing = False
        self.drag_start_position = QPoint()
        self.resize_direction = None
        self.resize_margin = 10

        os.makedirs(PROFILE_DIR, exist_ok=True)

        # Ensure Playwright browsers are installed (best-effort, non-fatal)
        try:
            subprocess.run([sys.executable, "-m", "playwright", "install", "chromium"], check=False, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        except Exception:
            pass

        self.conn = sqlite3.connect(DB_FILE)
        self.create_table()
        self.migrate_table()
        self._load_settings()

        # Create main layout
        outer_layout = QVBoxLayout(self)
        # Extra margin so glows around title/content aren't clipped by window bounds
        outer_layout.setContentsMargins(24, 24, 24, 24)
        outer_layout.setSpacing(0)

        # Frame container wraps title bar and main content so glow sits beneath the whole frame
        self.frame_container = QWidget()
        self.frame_container.setStyleSheet("""
            QWidget {
                background: qlineargradient(spread:pad, x1:0, y1:0, x3:1, y2:1, 
                    stop:0 rgba(10,13,20,1), stop:1 rgba(15,19,28,1));
                border-radius: 12px;
                border: 0px solid rgba(255, 255, 255, 0.1);
            }
        """)
        outer_layout.addWidget(self.frame_container)

        frame_layout = QVBoxLayout(self.frame_container)
        frame_layout.setContentsMargins(0, 0, 0, 0)
        frame_layout.setSpacing(0)

        # Custom title bar
        self.title_bar = self.create_title_bar()
        frame_layout.addWidget(self.title_bar)

        # Main content container (transparent, inherits frame background)
        self.content_container = QWidget()
        self.content_container.setStyleSheet("QWidget { background: transparent; border: none; }")
        frame_layout.addWidget(self.content_container)

        # Glow under entire frame (raised and slightly stronger to show under top bar)
        frame_effect = apply_glow(
            self.frame_container,
            radius=40,
            color=QColor(64, 120, 255, 100),
            x_offset=0,
            y_offset=-2,
        )
        start_glow_animation(frame_effect, period_ms=2600, radius_ampl=4, alpha_ampl=18, y_ampl=1)
        
        # Content layout
        container_layout = QVBoxLayout(self.content_container)
        container_layout.setContentsMargins(0, 0, 0, 0)
        
        # Content area  
        content_widget = QWidget()
        content_widget.setObjectName("content_root")
        content_widget.setStyleSheet(self.modern_dark_theme())
        main_layout = QHBoxLayout(content_widget)
        main_layout.setSpacing(15)
        main_layout.setContentsMargins(15, 15, 15, 15)
        container_layout.addWidget(content_widget)

        # Accounts tree with groups as folders
        class AccountTree(QTreeWidget):
            def __init__(self, parent_mgr):
                super().__init__()
                self._mgr = parent_mgr
            def dropEvent(self, event):
                super().dropEvent(event)
                # After items are moved, sync DB to reflect new parentage
                try:
                    # Ensure accounts are not left at top-level; move to Ungrouped
                    ungrouped = None
                    for i in range(self.topLevelItemCount()):
                        gi = self.topLevelItem(i)
                        if gi and gi.data(0, Qt.UserRole) == "group" and gi.data(0, Qt.UserRole + 1) is None:
                            ungrouped = gi
                            break
                    if ungrouped is None and self.topLevelItemCount() > 0:
                        # fallback: first top-level "Ungrouped" by text
                        for i in range(self.topLevelItemCount()):
                            gi = self.topLevelItem(i)
                            if gi and gi.data(0, Qt.UserRole) == "group" and "Ungrouped" in gi.text(0):
                                ungrouped = gi
                                break
                    # Collect orphan accounts at top-level
                    orphan_indices = []
                    for i in range(self.topLevelItemCount()):
                        ti = self.topLevelItem(i)
                        if ti and ti.data(0, Qt.UserRole) == "account":
                            orphan_indices.append(i)
                    # Move orphans under ungrouped (from last to first to keep indices valid)
                    if orphan_indices and ungrouped is not None:
                        for idx in reversed(orphan_indices):
                            itm = self.takeTopLevelItem(idx)
                            if itm is not None:
                                ungrouped.addChild(itm)
                        ungrouped.setExpanded(True)

                    self._mgr._sync_groups_from_tree()
                    # Update labels/counts in-place to preserve expansion state
                    self._mgr._refresh_account_labels_from_tree()
                    self._mgr._refresh_group_counts()
                except Exception:
                    pass
            def keyPressEvent(self, event):
                from PySide6.QtCore import Qt as _Qt
                if event.key() in (_Qt.Key_Delete, _Qt.Key_Backspace):
                    it = self.currentItem()
                    if it and it.data(0, Qt.UserRole) == "group" and it.data(0, Qt.UserRole + 1) is not None:
                        # Delete selected group (not Ungrouped)
                        self._mgr._delete_group(it)
                        return
                super().keyPressEvent(event)

        # Glowing separators between top-level group items
        class AccountsDelegate(QStyledItemDelegate):
            def __init__(self, tree):
                super().__init__(tree)
                self._tree = tree
            def paint(self, painter: QPainter, option, index):
                # Default painting
                super().paint(painter, option, index)
                # Only draw for top-level group rows on column 0
                if index.column() != 0 or index.parent().isValid():
                    return
                item = self._tree.itemFromIndex(index)
                if not item or item.data(0, Qt.UserRole) != "group":
                    return
                # Skip separator after the last top-level item
                row = index.row()
                if row >= self._tree.topLevelItemCount() - 1:
                    return
                # Draw a subtle glowing blue line across the row bottom
                r = option.rect
                y = r.bottom() - 1
                left = r.left() + 8
                right = r.right() - 8
                grad = QLinearGradient(left, y, right, y)
                # Match frame glow color: rgba(64, 120, 255, ~)
                grad.setColorAt(0.0, QColor(64, 120, 255, 0))
                grad.setColorAt(0.5, QColor(64, 120, 255, 110))
                grad.setColorAt(1.0, QColor(64, 120, 255, 0))
                pen = QPen()
                pen.setBrush(grad)
                pen.setWidth(2)
                painter.save()
                painter.setRenderHint(QPainter.Antialiasing, True)
                painter.setPen(pen)
                painter.drawLine(left, y, right, y)
                painter.restore()

        self.account_list = AccountTree(self)
        self.account_list.setHeaderHidden(True)
        self.account_list.setFont(QFont("Segoe UI", 11))
        self.account_list.setSelectionMode(QAbstractItemView.SingleSelection)
        self.account_list.setDragDropMode(QAbstractItemView.InternalMove)
        self.account_list.setDefaultDropAction(Qt.MoveAction)
        self.account_list.setIndentation(18)
        self.account_list.setAnimated(True)
        self.account_list.setAlternatingRowColors(False)
        self.account_list.setObjectName("accounts_tree")
        self.account_list.setItemDelegate(AccountsDelegate(self.account_list))

        # Wrap accounts tree in a container similar to Last Played
        self.accounts_container = QFrame()
        self.accounts_container.setObjectName("accounts_container")
        accounts_layout = QVBoxLayout(self.accounts_container)
        accounts_layout.setContentsMargins(0, 0, 0, 0)
        accounts_layout.addWidget(self.account_list)
        main_layout.addWidget(self.accounts_container, 3)

        # Last played list
        self.last_played_list = QListWidget()
        self.last_played_list.setObjectName("last_played_list")
        self.last_played_list.setStyleSheet("""
            QListWidget#last_played_list {
                border: none;
                outline: none;
                background-color: #13171f;
                border-radius: 12px;
                padding: 12px;
            }
        """)
        # Use emoji-capable font so game titles with emojis render correctly
        self.last_played_list.setFont(QFont("Segoe UI Emoji", 10))
        self.last_played_list.itemDoubleClicked.connect(self._select_last_played)
        # allow Ctrl/Shift multi-selection and Delete key removal
        self.last_played_list.setSelectionMode(QAbstractItemView.ExtendedSelection)
        self.last_played_list.installEventFilter(self)
        # Display as a list with icons on the left and full text visible
        self.last_played_list.setViewMode(QListView.ListMode)
        self.last_played_list.setIconSize(QSize(64, 64))
        self.last_played_list.setResizeMode(QListView.Adjust)
        self.last_played_list.setMovement(QListView.Static)
        self.last_played_list.setSpacing(8)
        self.last_played_list.setWordWrap(True)
        # Prevent horizontal scrolling when vertical scrollbar appears
        self.last_played_list.setHorizontalScrollBarPolicy(Qt.ScrollBarAlwaysOff)
        self.last_played_list.setTextElideMode(Qt.ElideRight)
        self.last_played_list.setUniformItemSizes(False)
        # Context menu for deleting selected last played entries
        self.last_played_list.setContextMenuPolicy(Qt.CustomContextMenu)
        self.last_played_list.customContextMenuRequested.connect(self.show_last_played_menu)

        # Load last played when account selection changes (tree)
        self.account_list.itemSelectionChanged.connect(self._refresh_last_played)

        right_panel = QVBoxLayout()
        right_panel.setSpacing(12)

        self.place_id_input = QLineEdit()
        self.place_id_input.setPlaceholderText("Enter Place ID")
        self.join_button = QPushButton("▶ Join Server")
        self.join_button.setMinimumHeight(42)
        self.join_button.clicked.connect(self.join_server)
        # Removed redundant "Join Game" label header to avoid duplicate text with outline
        right_panel.addWidget(self.place_id_input)
        right_panel.addWidget(self.join_button)

        action_frame = QFrame()
        action_layout = QHBoxLayout(action_frame)
        action_layout.setSpacing(10)
        self.add_account_btn = QPushButton("＋ Add Account (Login)")
        self.add_account_btn.clicked.connect(self.add_account)

        # context menu for account list
        self.account_list.setContextMenuPolicy(Qt.CustomContextMenu)
        self.account_list.customContextMenuRequested.connect(self.show_account_menu)
        self.remove_account_btn = QPushButton("🗑 Remove")
        self.remove_account_btn.clicked.connect(self.remove_account)
        self.hide_usernames_chk = QCheckBox("Hide Usernames")
        self.hide_usernames_chk.setChecked(self.usernames_hidden)
        self.hide_usernames_chk.stateChanged.connect(self.toggle_hide_usernames)
        action_layout.addWidget(self.add_account_btn)
        action_layout.addWidget(self.remove_account_btn)
        action_layout.addWidget(self.hide_usernames_chk)
        right_panel.addWidget(action_frame)

        utilities_group = QGroupBox("Utilities")
        util_layout = QVBoxLayout()
        util_layout.setSpacing(8)
        browser_btn = QPushButton("🌐 Open Browser")
        browser_btn.clicked.connect(self.open_browser_for_account)
        util_layout.addWidget(browser_btn)
        utilities_group.setLayout(util_layout)
        right_panel.addWidget(utilities_group)

        # Settings button
        settings_btn = QPushButton("⚙ Settings")
        settings_btn.clicked.connect(self.open_settings)
        # start mutex patcher thread if enabled
        if self.multi_instance_enabled and not getattr(self, "_patcher_started", False):
            threading.Thread(target=self._mutex_patcher_loop, daemon=True).start()
            self._patcher_started = True
        right_panel.addWidget(settings_btn)

        right_panel.addSpacerItem(QSpacerItem(20, 40, QSizePolicy.Minimum, QSizePolicy.Expanding))

        main_layout.addLayout(right_panel, 2)

        self.load_accounts()

        # Create a vertical layout for Last Played section with title and container
        last_played_section = QVBoxLayout()
        last_played_section.setSpacing(10)  # Gap between title and container
        # Add margins so the container's glow isn't clipped by its parent
        last_played_section.setContentsMargins(8, 8, 8, 8)
        
        # Last Played title label
        last_played_title = QLabel("Last Played")
        last_played_title.setStyleSheet("""
            QLabel {
                color: #f0f0f0;
                font-size: 14px;
                font-weight: 600;
                background: transparent;
                padding: 16px 12px;
                border: none;
                border-radius: 8px;
                background: qlineargradient(spread:pad, x1:0, y1:0, x2:0, y2:1, 
                    stop:0 rgba(30, 35, 45, 0.95), stop:1 rgba(20, 25, 35, 0.98));
            }
        """)
        last_played_title.setAlignment(Qt.AlignCenter)
        last_played_section.addWidget(last_played_title)
        
        # Last Played container (just the list, no tab)
        last_played_container = QFrame()
        last_played_container.setObjectName("last_played_container")
        last_played_container.setAttribute(Qt.WA_StyledBackground, True)
        last_played_container.setStyleSheet("""
            QFrame#last_played_container {
                background-color: #0a0d14;
                border: none;
                border-radius: 12px;
            }
        """)
        lp_layout = QVBoxLayout(last_played_container)
        last_played_container.setMinimumWidth(330)  # Set minimum width
        last_played_container.setMaximumWidth(330)  # Set maximum width
        lp_layout.setContentsMargins(0, 0, 0, 0)
        lp_layout.setSpacing(0)
        lp_layout.addWidget(self.last_played_list)
        last_played_section.addWidget(last_played_container)
        
        # Removed glow around Last Played container per request
        
        # Create a widget to hold the section and add it to main layout
        last_played_widget = QWidget()
        last_played_widget.setLayout(last_played_section)
        main_layout.addWidget(last_played_widget, 2)
    
    def create_title_bar(self):
        """Create modern title bar with window controls on the left."""
        title_bar = QFrame()
        title_bar.setFixedHeight(40)
        title_bar.setStyleSheet("""
            QFrame {
                background: qlineargradient(spread:pad, x1:0, y1:0, x2:0, y2:1, 
                    stop:0 rgba(30, 35, 45, 0.95), stop:1 rgba(20, 25, 35, 0.98));
                border: 1px solid rgba(255, 255, 255, 0.1);
                border-radius: 10px;
                border-bottom-left-radius: 0px;
                border-bottom-right-radius: 0px;
                border-bottom: none;
            }
            QLabel#title_label {
                background: transparent;
                border: none;
                border-radius: 0;
                padding: 0;
                margin: 0;
            }
            QPushButton {
                border: none;
                border-radius: 10px; /* default circle fallback */
                width: 20px;
                height: 20px;
                margin: 0px;
                padding: 0;
            }
            /* Explicit per-button rules to guarantee perfect circles and override any inherited styles */
            QPushButton#close_btn,
            QPushButton#minimize_btn,
            QPushButton#maximize_btn {
                border: none;
                border-radius: 10px; /* 20/2 = 10 for a perfect circle */
                width: 20px;
                height: 20px;
                padding: 0;
            }
            QPushButton#close_btn {
                background-color: #ff5f57;
            }
            QPushButton#close_btn:hover {
                background-color: #ff3b30;
            }
            QPushButton#minimize_btn {
                background-color: #ffbd2e;
            }
            QPushButton#minimize_btn:hover {
                background-color: #ff9500;
            }
            QPushButton#maximize_btn {
                background-color: #28ca42;
            }
            QPushButton#maximize_btn:hover {
                background-color: #30d158;
            }
        """)
        
        layout = QHBoxLayout(title_bar)
        layout.setContentsMargins(12, 8, 15, 8)
        layout.setSpacing(8)
        
        # Window controls on the left
        controls_layout = QHBoxLayout()
        controls_layout.setSpacing(6)
        
        # Close button
        self.close_btn = QPushButton("")
        self.close_btn.setObjectName("close_btn")
        self.close_btn.setFixedSize(20, 20)
        self.close_btn.setStyleSheet("border-radius: 10px;")
        self.close_btn.clicked.connect(self.close)
        controls_layout.addWidget(self.close_btn)
        
        # Minimize button  
        self.minimize_btn = QPushButton("")
        self.minimize_btn.setObjectName("minimize_btn")
        self.minimize_btn.setFixedSize(20, 20)
        self.minimize_btn.setStyleSheet("border-radius: 10px;")
        self.minimize_btn.clicked.connect(self.showMinimized)
        controls_layout.addWidget(self.minimize_btn)
        
        # Maximize button
        self.maximize_btn = QPushButton("")
        self.maximize_btn.setObjectName("maximize_btn") 
        self.maximize_btn.setFixedSize(20, 20)
        self.maximize_btn.setStyleSheet("border-radius: 10px;")
        self.maximize_btn.clicked.connect(self.toggle_maximize)
        controls_layout.addWidget(self.maximize_btn)
        
        layout.addLayout(controls_layout)
        
        # Title in center
        title_label = QLabel("Roblox Account Manager")
        title_label.setObjectName("title_label")
        title_label.setStyleSheet("""
            QLabel {
                color: #f0f0f0;
                font-size: 14px;
                font-weight: 700;
                background: transparent;
            }
        """)
        title_label.setAlignment(Qt.AlignCenter)
        layout.addWidget(title_label, 1)
        
        # Spacer to balance the layout
        layout.addSpacerItem(QSpacerItem(80, 20, QSizePolicy.Fixed, QSizePolicy.Minimum))
        # No direct glow on title bar; frame_container glow renders under entire frame

        return title_bar
    
    def toggle_maximize(self):
        """Toggle between maximized and normal window state."""
        if self.isMaximized():
            self.showNormal()
        else:
            self.showMaximized()
            
    def _get_resize_direction(self, pos):
        """Determine resize direction based on mouse position."""
        rect = self.rect()
        margin = self.resize_margin
        
        # Check corners first
        if pos.x() <= margin and pos.y() <= margin:
            return "top_left"
        elif pos.x() >= rect.width() - margin and pos.y() <= margin:
            return "top_right"
        elif pos.x() <= margin and pos.y() >= rect.height() - margin:
            return "bottom_left"
        elif pos.x() >= rect.width() - margin and pos.y() >= rect.height() - margin:
            return "bottom_right"
        # Check edges
        elif pos.x() <= margin:
            return "left"
        elif pos.x() >= rect.width() - margin:
            return "right"
        elif pos.y() <= margin:
            return "top"
        elif pos.y() >= rect.height() - margin:
            return "bottom"
        
        return None
        
    def _resize_window(self, global_pos):
        """Resize window based on drag direction."""
        rect = self.geometry()
        
        if "right" in self.resize_direction:
            rect.setRight(global_pos.x())
        elif "left" in self.resize_direction:
            rect.setLeft(global_pos.x())
            
        if "bottom" in self.resize_direction:
            rect.setBottom(global_pos.y())
        elif "top" in self.resize_direction:
            rect.setTop(global_pos.y())
            
        # Enforce minimum size
        if rect.width() < 800:
            if "left" in self.resize_direction:
                rect.setLeft(rect.right() - 800)
            else:
                rect.setRight(rect.left() + 800)
                
        if rect.height() < 500:
            if "top" in self.resize_direction:
                rect.setTop(rect.bottom() - 500)
            else:
                rect.setBottom(rect.top() + 500)
                
        self.setGeometry(rect)

    # ---------- DB ----------
    def create_table(self):
        with self.conn:
            self.conn.execute(
                """
                CREATE TABLE IF NOT EXISTS accounts (
                    username TEXT PRIMARY KEY,
                    alias TEXT,
                    profile_path TEXT
                )
                """
            )

            # last_played table
            self.conn.execute(
                """
                CREATE TABLE IF NOT EXISTS last_played (
                    username TEXT,
                    place_id TEXT,
                    name TEXT,
                    icon_url TEXT,
                    played_at INTEGER,
                    PRIMARY KEY(username, place_id)
                )
                """
            )
            # groups table
            self.conn.execute(
                """
                CREATE TABLE IF NOT EXISTS groups (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    name TEXT UNIQUE
                )
                """
            )

    def migrate_table(self):
        # Add roblosecurity column if not exists
        cur = self.conn.cursor()
        cur.execute("PRAGMA table_info(accounts)")
        cols = [row[1] for row in cur.fetchall()]
        if "roblosecurity" not in cols:
            with self.conn:
                self.conn.execute("ALTER TABLE accounts ADD COLUMN roblosecurity TEXT")
        # Add group_id column if not exists
        cur.execute("PRAGMA table_info(accounts)")
        cols = [row[1] for row in cur.fetchall()]
        if "group_id" not in cols:
            with self.conn:
                self.conn.execute("ALTER TABLE accounts ADD COLUMN group_id INTEGER REFERENCES groups(id)")
        # Ensure groups table has an id column; if not, recreate with correct schema
        try:
            gcur = self.conn.cursor()
            gcur.execute("PRAGMA table_info(groups)")
            gcols = [row[1] for row in gcur.fetchall()]
            if gcols and "id" not in gcols:
                # migrate existing groups(name) -> groups(id, name)
                with self.conn:
                    self.conn.execute(
                        "CREATE TABLE IF NOT EXISTS groups_new (id INTEGER PRIMARY KEY AUTOINCREMENT, name TEXT UNIQUE)"
                    )
                    # Copy distinct names
                    self.conn.execute("INSERT OR IGNORE INTO groups_new(name) SELECT DISTINCT name FROM groups")
                    self.conn.execute("DROP TABLE groups")
                    self.conn.execute("ALTER TABLE groups_new RENAME TO groups")
        except sqlite3.OperationalError:
            # If groups table does not exist yet, create_table() will handle it.
            pass
        
        # Encrypt existing plaintext aliases and cookies at rest (idempotent)
        try:
            rows = self.conn.execute("SELECT username, alias, roblosecurity FROM accounts").fetchall()
            to_update = []
            for username, alias, cookie in rows:
                # Only encrypt cookies, leave aliases as plain text
                new_alias = alias  # Keep alias as-is (no encryption)
                new_cookie = _enc(cookie) if cookie and not _is_enc(cookie) else cookie
                if new_alias != alias or new_cookie != cookie:
                    to_update.append((new_alias, new_cookie, username))
            if to_update:
                with self.conn:
                    for a, c, u in to_update:
                        self.conn.execute("UPDATE accounts SET alias=?, roblosecurity=? WHERE username=?", (a, c, u))
        except Exception:
            # Non-fatal: if anything goes wrong, leave data as-is
            pass

    def load_accounts(self):
        # Build tree: top-level = groups (including "Ungrouped"), children = accounts
        self.account_list.clear()
        self.original_account_data = []

        # Fetch groups and accounts
        group_rows = self.conn.execute("SELECT id, name FROM groups ORDER BY name").fetchall()
        accounts = self.conn.execute("SELECT username, alias, group_id FROM accounts ORDER BY username").fetchall()

        # Helper to create a group node
        def make_group_item(name: str, group_id: int | None) -> QTreeWidgetItem:
            it = QTreeWidgetItem([name])
            it.setData(0, Qt.UserRole, "group")
            it.setData(0, Qt.UserRole + 1, group_id)
            it.setData(0, Qt.UserRole + 5, name)  # base name without count
            it.setFlags(it.flags() | Qt.ItemIsDropEnabled | Qt.ItemIsEnabled | Qt.ItemIsSelectable)
            it.setExpanded(True)
            f = it.font(0)
            f.setBold(True)
            it.setFont(0, f)
            return it

        # Create top-level group nodes
        group_items: dict[int | None, QTreeWidgetItem] = {}
        # Ungrouped bucket (None)
        ungrouped = make_group_item("Ungrouped", None)
        self.account_list.addTopLevelItem(ungrouped)
        group_items[None] = ungrouped
        for gid, gname in group_rows:
            gi = make_group_item(gname, gid)
            self.account_list.addTopLevelItem(gi)
            group_items[gid] = gi

        # Helper to format account label per current hide setting
        def account_label(username: str, alias: str | None, group_name: str | None) -> str:
            if self.usernames_hidden:
                parts = ["[hidden]"]
                if alias:
                    parts.append(f"[alias: {alias}]")
                if group_name:
                    parts.append(f"[group: {group_name}]")
                return " ".join(parts)
            parts = [username]
            if alias:
                parts.append(f"[alias: {alias}]")
            if group_name:
                parts.append(f"[group: {group_name}]")
            return " ".join(parts)

        # Add accounts as children under their group
        group_name_map = {gid: gname for gid, gname in group_rows}
        for username, alias, group_id in accounts:
            # Use alias as-is (no decryption needed for aliases)
            alias = alias or ""
            gname = group_name_map.get(group_id) if group_id else None
            label = account_label(username, alias, gname)
            parent_item = group_items.get(group_id, ungrouped)
            child = QTreeWidgetItem([label])
            child.setData(0, Qt.UserRole, "account")
            child.setData(0, Qt.UserRole + 1, username)
            child.setData(0, Qt.UserRole + 2, alias)
            child.setData(0, Qt.UserRole + 3, group_id)
            child.setData(0, Qt.UserRole + 4, gname)
            child.setFlags(child.flags() | Qt.ItemIsDragEnabled | Qt.ItemIsEnabled | Qt.ItemIsSelectable)
            parent_item.addChild(child)

        # Update group counts in labels
        self._refresh_group_counts()

    # ---------- UI Actions ----------
    def add_account(self):
        """Start login flow without asking for username/alias. Username is resolved after login."""
        tmp_dir = str(int(time.time()))
        profile_path = os.path.join(PROFILE_DIR, tmp_dir)
        os.makedirs(profile_path, exist_ok=True)

        try:
            roblosec = self.login_and_capture_cookie(profile_path)
        except PWTimeoutError:
            ModernMessageBox.warning(self, "Login timeout", "Timed out waiting for Roblox login to complete.")
            shutil.rmtree(profile_path, ignore_errors=True)
            return
        except Exception as e:
            ModernMessageBox.critical(self, "Chromium error", f"Failed to launch or capture cookie: {e}")
            shutil.rmtree(profile_path, ignore_errors=True)
            return

        if not roblosec:
            ModernMessageBox.warning(self, "No cookie", "Couldn't find .ROBLOSECURITY after login.")
            shutil.rmtree(profile_path, ignore_errors=True)
            return

        # Resolve username via Roblox API
        username = self._resolve_username(roblosec)
        if not username:
            ModernMessageBox.warning(self, "Error", "Could not determine username after login.")
            shutil.rmtree(profile_path, ignore_errors=True)
            return

        final_profile_path = os.path.join(PROFILE_DIR, username)
        if os.path.exists(final_profile_path):
            shutil.rmtree(final_profile_path)
        os.rename(profile_path, final_profile_path)

        with self.conn:
            self.conn.execute(
                "INSERT OR REPLACE INTO accounts (username, alias, profile_path, roblosecurity) VALUES (?, ?, ?, ?)",
                (username, "", final_profile_path, _enc(roblosec)),
            )
        ModernMessageBox.information(self, "Account Added", f"Logged in as {username} and stored credentials.")
        # Update UI in-place to preserve expanded/collapsed groups
        # Find Ungrouped group item (group_id is None)
        ungrouped = None
        for i in range(self.account_list.topLevelItemCount()):
            gi = self.account_list.topLevelItem(i)
            if gi and gi.data(0, Qt.UserRole) == "group" and gi.data(0, Qt.UserRole + 1) is None:
                ungrouped = gi
                break
        if ungrouped is None:
            # Fallback create if not present
            ungrouped = QTreeWidgetItem(["Ungrouped"])
            ungrouped.setData(0, Qt.UserRole, "group")
            ungrouped.setData(0, Qt.UserRole + 1, None)
            ungrouped.setData(0, Qt.UserRole + 5, "Ungrouped")
            f = ungrouped.font(0); f.setBold(True); ungrouped.setFont(0, f)
            self.account_list.addTopLevelItem(ungrouped)
        # Compose label based on current hide setting
        if self.usernames_hidden:
            label = "[hidden]"
        else:
            label = username
        child = QTreeWidgetItem([label])
        child.setData(0, Qt.UserRole, "account")
        child.setData(0, Qt.UserRole + 1, username)
        child.setData(0, Qt.UserRole + 2, "")
        child.setData(0, Qt.UserRole + 3, None)
        child.setData(0, Qt.UserRole + 4, None)
        child.setFlags(child.flags() | Qt.ItemIsDragEnabled | Qt.ItemIsEnabled | Qt.ItemIsSelectable)
        ungrouped.addChild(child)
        ungrouped.setExpanded(True)
        # Refresh counts and labels to reflect alias/group tags
        self._refresh_account_labels_from_tree()
        self._refresh_group_counts()

    def remove_account(self):
        selected = self.account_list.currentItem()
        if not selected:
            return
        username = self._get_selected_username()
        with self.conn:
            self.conn.execute("DELETE FROM accounts WHERE username=?", (username,))
        profile_path = os.path.join(PROFILE_DIR, username)
        if os.path.exists(profile_path):
            shutil.rmtree(profile_path)
        self.load_accounts()

    # ---------- Context Menu ----------
    def show_account_menu(self, pos):
        item = self.account_list.itemAt(pos)
        menu = ModernMenu(self)

        if item:
            # Ensure actions target the item under the cursor
            self.account_list.setCurrentItem(item)
            itype = item.data(0, Qt.UserRole)
            if itype == "account":
                # Actions for a specific account
                menu.addAction("Edit Alias…", lambda: self._prompt_set_alias(item))
                menu.addAction("Remove Account", lambda: self._remove_account_from_menu(item))

                # Group actions (simplified - no submenu for now)
                groups = self.conn.execute("SELECT id, name FROM groups ORDER BY name").fetchall()
                if groups:
                    menu.addSeparator()
                    for gid, gname in groups:
                        menu.addAction(f"Move to {gname}", lambda group_id=gid: self._move_selected_to_group(group_id))
                
                menu.addSeparator()
                menu.addAction("Create New Group…", self._create_group_from_menu)
                menu.addAction("Remove from Group", self._remove_selected_from_group)
                
            elif itype == "group":
                # Group actions
                menu.addAction("Create Group…", self._create_group_from_menu)

                group_id = item.data(0, Qt.UserRole + 1)
                if group_id is not None:
                    menu.addAction("Rename Group…", lambda: self._rename_group(item))
                    menu.addAction("Delete Group", lambda: self._delete_group(item))
        else:
            # Background menu on account tree
            menu.addAction("Create Group…", self._create_group_from_menu)

        if not menu.isEmpty():
            menu.exec(self.account_list.mapToGlobal(pos))

    def _create_group_from_menu(self):
        # Create and show the input dialog
        dialog = ModernInputDialog(self, "Create Group", "Enter group name:", "")
        
        # Process the dialog result
        try:
            result = dialog.exec()
            if result == QDialog.Accepted:
                name = dialog.get_text().strip()
                if name:
                    try:
                        with self.conn:
                            self.conn.execute("INSERT INTO groups(name) VALUES(?)", (name,))
                        self.load_accounts()
                    except sqlite3.IntegrityError:
                        ModernMessageBox.warning(self, "Group Exists", f"A group named '{name}' already exists.")
        finally:
            # Ensure dialog is properly cleaned up
            dialog.close()
            dialog.deleteLater()

    def _move_selected_to_group(self, group_id: int):
        username = self._get_selected_username()
        if not username:
            return
        with self.conn:
            self.conn.execute("UPDATE accounts SET group_id=? WHERE username=?", (group_id, username))
        self.load_accounts()

    def _remove_selected_from_group(self):
        username = self._get_selected_username()
        if not username:
            return
        with self.conn:
            self.conn.execute("UPDATE accounts SET group_id=NULL WHERE username=?", (username,))
        self.load_accounts()

    def _remove_account_from_menu(self, item):
        """Remove account from context menu action."""
        if item is None or item.data(0, Qt.UserRole) != "account":
            return
        username = item.data(0, Qt.UserRole + 1)
        if not username:
            return
        
        # Store expanded state before removal
        expanded_groups = {}
        for i in range(self.account_list.topLevelItemCount()):
            group_item = self.account_list.topLevelItem(i)
            if group_item and group_item.data(0, Qt.UserRole) == "group":
                group_id = group_item.data(0, Qt.UserRole + 1)
                expanded_groups[group_id] = group_item.isExpanded()
        
        # Confirm deletion
        result = ModernMessageBox.warning(self, "Remove Account", 
                                        f"Are you sure you want to remove account '{username}'?\n\nThis will delete all associated data including the browser profile.")
        if result == QDialog.Accepted:
            # Remove from database
            with self.conn:
                self.conn.execute("DELETE FROM accounts WHERE username=?", (username,))
            # Remove profile directory
            profile_path = os.path.join(PROFILE_DIR, username)
            if os.path.exists(profile_path):
                shutil.rmtree(profile_path)
            # Refresh the account list
            self.load_accounts()
            
            # Restore expanded state
            for i in range(self.account_list.topLevelItemCount()):
                group_item = self.account_list.topLevelItem(i)
                if group_item and group_item.data(0, Qt.UserRole) == "group":
                    group_id = group_item.data(0, Qt.UserRole + 1)
                    if group_id in expanded_groups and expanded_groups[group_id]:
                        group_item.setExpanded(True)

    def _rename_group(self, group_item: QTreeWidgetItem):
        group_id = group_item.data(0, Qt.UserRole + 1)
        if group_id is None:
            return  # Don't rename Ungrouped
        current_name = group_item.text(0)
        dialog = ModernInputDialog(self, "Rename Group", "New group name:", current_name)
        result = dialog.exec()
        dialog.hide()  # Explicitly hide the dialog
        dialog.deleteLater()  # Schedule for deletion
        
        if result == QDialog.Accepted:
            name = dialog.get_text().strip()
            if not name:
                return
            try:
                with self.conn:
                    self.conn.execute("UPDATE groups SET name=? WHERE id=?", (name, group_id))
            except sqlite3.IntegrityError:
                ModernMessageBox.warning(self, "Group Exists", f"A group named '{name}' already exists.")
            # Update base name and refresh label/counts without full reload
            group_item.setData(0, Qt.UserRole + 5, name)
            self._refresh_group_counts()
            # Also refresh labels of children to reflect new group tag
            for i in range(group_item.childCount()):
                child = group_item.child(i)
                if child.data(0, Qt.UserRole) == "account":
                    username = child.data(0, Qt.UserRole + 1)
                    alias = child.data(0, Qt.UserRole + 2)
                    gname = name
                    if self.usernames_hidden:
                        parts = ["[hidden]"]
                        if alias:
                            parts.append(f"[alias: {alias}]")
                        parts.append(f"[group: {gname}]")
                        child.setText(0, " ".join(parts))
            # Ensure visible-username case is refreshed too
            self._refresh_account_labels_from_tree()

    def _delete_group(self, group_item: QTreeWidgetItem):
        """Delete a group: move its accounts to Ungrouped, remove group from DB and UI."""
        group_id = group_item.data(0, Qt.UserRole + 1)
        if group_id is None:
            return  # do not delete Ungrouped
        # Find or create the Ungrouped node
        ungrouped = None
        for i in range(self.account_list.topLevelItemCount()):
            gi = self.account_list.topLevelItem(i)
            if gi and gi.data(0, Qt.UserRole) == "group" and gi.data(0, Qt.UserRole + 1) is None:
                ungrouped = gi
                break
        if ungrouped is None:
            # Should not happen because we always create it; fallback create
            ungrouped = QTreeWidgetItem(["Ungrouped"])
            ungrouped.setData(0, Qt.UserRole, "group")
            ungrouped.setData(0, Qt.UserRole + 1, None)
            ungrouped.setData(0, Qt.UserRole + 5, "Ungrouped")
            f = ungrouped.font(0); f.setBold(True); ungrouped.setFont(0, f)
            self.account_list.addTopLevelItem(ungrouped)
        # Move children visually first to preserve state
        while group_item.childCount() > 0:
            ch = group_item.takeChild(0)
            ungrouped.addChild(ch)
        ungrouped.setExpanded(True)
        # DB updates: move accounts to NULL group and delete group row
        with self.conn:
            self.conn.execute("UPDATE accounts SET group_id=NULL WHERE group_id=?", (group_id,))
            self.conn.execute("DELETE FROM groups WHERE id=?", (group_id,))
        # Remove the group node from UI
        idx = self.account_list.indexOfTopLevelItem(group_item)
        if idx >= 0:
            self.account_list.takeTopLevelItem(idx)
        # Refresh labels and counts
        self._refresh_account_labels_from_tree()
        self._refresh_group_counts()

    def _sync_groups_from_tree(self):
        # After drag/drop, ensure account children under a group reflect group_id in DB
        updates: list[tuple[int | None, str]] = []  # (group_id, username)
        top_n = self.account_list.topLevelItemCount()
        for t in range(top_n):
            group_item = self.account_list.topLevelItem(t)
            group_id = group_item.data(0, Qt.UserRole + 1)
            for i in range(group_item.childCount()):
                child = group_item.child(i)
                if child.data(0, Qt.UserRole) == "account":
                    username = child.data(0, Qt.UserRole + 1)
                    updates.append((group_id, username))
        if not updates:
            return
        with self.conn:
            for gid, uname in updates:
                if gid is None:
                    self.conn.execute("UPDATE accounts SET group_id=NULL WHERE username=?", (uname,))
                else:
                    self.conn.execute("UPDATE accounts SET group_id=? WHERE username=?", (gid, uname))
        # Refresh labels/counts after drop
        self._refresh_group_counts()

    def _prompt_set_alias(self, item):
        # With tree view, fetch username from the item's data
        if item is None or item.data(0, Qt.UserRole) != "account":
            return
        username = item.data(0, Qt.UserRole + 1)
        if not username:
            return
        # Get current alias from database (aliases are stored as plain text)
        row = self.conn.execute("SELECT alias FROM accounts WHERE username=?", (username,)).fetchone()
        current_alias = row[0] if row and row[0] else ""
        
        dialog = ModernInputDialog(self, "Edit Alias", "Enter alias for account:", current_alias)
        result = dialog.exec()
        dialog.hide()  # Explicitly hide the dialog
        dialog.deleteLater()  # Schedule for deletion
        
        if result == QDialog.Accepted:
            alias = dialog.get_text().strip()
            with self.conn:
                self.conn.execute("UPDATE accounts SET alias=? WHERE username=?", (alias, username))
            item.setData(0, Qt.UserRole + 2, alias)
            self._refresh_account_labels_from_tree()

    # ---------- UI Actions ----------
    def toggle_hide_usernames(self, state):
        self.usernames_hidden = bool(state)
        
        # Save the setting
        with self.conn:
            self.conn.execute("INSERT OR REPLACE INTO settings(key,value) VALUES('hide_usernames',?)", 
                            (1 if self.usernames_hidden else 0,))
        
        # Update display across tree items
        def update_tree_labels():
            top_count = self.account_list.topLevelItemCount()
            for t in range(top_count):
                group_item = self.account_list.topLevelItem(t)
                # group label unchanged here
                for i in range(group_item.childCount()):
                    child = group_item.child(i)
                    if child.data(0, Qt.UserRole) == "account":
                        username = child.data(0, Qt.UserRole + 1)
                        alias = child.data(0, Qt.UserRole + 2)
                        group_id = group_item.data(0, Qt.UserRole + 1)
                        gname = group_item.text(0) if group_id is not None else None
                        # store latest
                        child.setData(0, Qt.UserRole + 3, group_id)
                        child.setData(0, Qt.UserRole + 4, gname)
                        # set label
                        if self.usernames_hidden:
                            parts = ["[hidden]"]
                            if alias:
                                parts.append(f"[alias: {alias}]")
                            if gname:
                                parts.append(f"[group: {gname}]")
                            child.setText(0, " ".join(parts))
                        else:
                            parts = [username]
                            if alias:
                                parts.append(f"[alias: {alias}]")
                            if gname:
                                parts.append(f"[group: {gname}]")
                            child.setText(0, " ".join(parts))
        update_tree_labels()

    def open_browser_for_account(self):
        selected = self.account_list.currentItem()
        if not selected:
            QMessageBox.warning(self, "Error", "Please select an account")
            return
        username = self._get_selected_username()
        profile_path, roblosec = self._get_account(username)
        self.launch_chromium(profile_path, "https://www.roblox.com/home", roblosec)

    def join_server(self):
        place_id = self.place_id_input.text().strip()
        selected = self.account_list.currentItem()
        if not selected:
            QMessageBox.warning(self, "Error", "Please select an account")
            return
        if not place_id:
            ModernMessageBox.warning(self, "Error", "Please enter a Place ID")
            return
        username = self._get_selected_username()
        _, roblosec = self._get_account(username)
        try:
            ticket = self._get_auth_ticket(roblosec, place_id)
        except Exception as e:
            ModernMessageBox.critical(self, "Error", f"Failed to get auth ticket: {e}")
            return
        launch_uri = self._build_roblox_player_uri(ticket, place_id)
        try:
            # Proactively keep clearing the Roblox mutex during startup window
            if self.multi_instance_enabled:
                self._clear_mutex_burst(duration=8.0, interval=0.2)
            # Open via default handler (Roblox Player).
            webbrowser.open(launch_uri)
            # record last played on success
            self._record_last_played(username, place_id)
        except Exception as e:
            ModernMessageBox.critical(self, "Error", f"Failed to launch Roblox player: {e}")

    # ---------- Chromium helpers ----------
    def _login_and_capture_cookie_worker(self, profile_path: str, timeout_ms: int, result_holder: dict):
        """Worker executed in a separate thread to avoid Playwright sync API conflict with running asyncio loop."""
        with sync_playwright() as p:
            ctx = p.chromium.launch_persistent_context(
                profile_path,
                headless=False,
                args=["--disable-session-crashed-bubble --app=https://www.roblox.com --window-size=700,800"],
            )
            try:
                page = ctx.pages[0] if ctx.pages else ctx.new_page()
                page.goto("https://www.roblox.com/Login")
                page.wait_for_url("https://www.roblox.com/home*", timeout=timeout_ms)
                time.sleep(0.5)
                cookies = ctx.cookies()
                for c in cookies:
                    if c.get("name") == ".ROBLOSECURITY":
                        result_holder["cookie"] = c.get("value")
                        break
            finally:
                try:
                    ctx.close()
                except Exception:
                    pass

    def login_and_capture_cookie(self, profile_path: str, timeout_ms: int = 600_000):
        """Run Playwright sync API in a dedicated thread so it is not executed inside an existing asyncio loop."""
        result: dict[str, str | None] = {"cookie": None}
        t = threading.Thread(target=self._login_and_capture_cookie_worker, args=(profile_path, timeout_ms, result), daemon=True)
        t.start()
        t.join()
        return result["cookie"]

    def launch_chromium(self, profile_path: str, url: str, roblosec: str | None = None, auto_play: bool = False):
        """Launch persistent Chromium for this account, ensure cookie is present if provided, then navigate.

        We intentionally keep a reference to both the Playwright driver and the browser context
        so that the browser window stays open after this function returns. They will be
        cleaned-up when the Qt window closes.
        """
        # Lazily start Playwright once and keep it alive
        if self._playwright is None:
            self._playwright = sync_playwright().start()

        ctx = self._playwright.chromium.launch_persistent_context(
            profile_path,
            headless=False,
            args=["--disable-session-crashed-bubble --app=https://www.roblox.com --window-size=700,800"],
        )
        # Track context so that we can close it later on application exit
        self._open_contexts.append(ctx)

        page = ctx.pages[0] if ctx.pages else ctx.new_page()

        # If we have a saved cookie but the context doesn't, inject it
        if roblosec:
            has_cookie = any(c.get("name") == ".ROBLOSECURITY" for c in ctx.cookies())
            if not has_cookie:
                ctx.add_cookies([
                    {
                        "name": ".ROBLOSECURITY",
                        "value": roblosec,
                        "domain": ".roblox.com",
                        "path": "/",
                        "httpOnly": True,
                        "secure": True,
                        "sameSite": "Lax",
                    }
                ])
        page.goto(url)

        # Optionally auto-click the Play button on a game details page to initiate joining.
        if auto_play:
            try:
                page.wait_for_selector('button[data-testid="game-detail-play-button"], button[data-test-play-button], .btn-play', timeout=10000)
                page.click('button[data-testid="game-detail-play-button"], button[data-test-play-button], .btn-play')
            except Exception:
                pass  # ignore if not found
        # Do NOT close context; keep it open for user interaction.


    def _get_selected_username(self):
        """Return username if an account item is selected in the tree; otherwise None."""
        item = self.account_list.currentItem()
        if not item:
            return None
        if item.data(0, Qt.UserRole) != "account":
            return None
        return item.data(0, Qt.UserRole + 1)

    def _refresh_group_counts(self):
        """Update group node labels to include the number of accounts in each group."""
        top_n = self.account_list.topLevelItemCount()
        for t in range(top_n):
            group_item = self.account_list.topLevelItem(t)
            base = group_item.data(0, Qt.UserRole + 5) or group_item.text(0)
            count = group_item.childCount()
            group_item.setText(0, f"{base} ({count})")

    def _refresh_account_labels_from_tree(self):
        """Update each account child label based on current group parent and username-hidden setting."""
        top_n = self.account_list.topLevelItemCount()
        for t in range(top_n):
            group_item = self.account_list.topLevelItem(t)
            if not group_item or group_item.data(0, Qt.UserRole) != "group":
                continue
            group_id = group_item.data(0, Qt.UserRole + 1)
            # Prefer stored base name without count
            gname = group_item.data(0, Qt.UserRole + 5)
            if group_id is None:
                gname = None
            elif not gname:
                # Fallback: strip trailing count if present
                txt = group_item.text(0)
                if txt.endswith(')') and '(' in txt:
                    gname = txt[: txt.rfind('(')].rstrip()
                else:
                    gname = txt
            for i in range(group_item.childCount()):
                child = group_item.child(i)
                if child.data(0, Qt.UserRole) != "account":
                    continue
                username = child.data(0, Qt.UserRole + 1)
                alias = child.data(0, Qt.UserRole + 2)
                # Update child's stored group info
                child.setData(0, Qt.UserRole + 3, group_id)
                child.setData(0, Qt.UserRole + 4, gname)
                if self.usernames_hidden:
                    parts = ["[hidden]"]
                    if alias:
                        parts.append(f"[alias: {alias}]")
                    if gname:
                        parts.append(f"[group: {gname}]")
                    child.setText(0, " ".join(parts))
                else:
                    parts = [username]
                    if alias:
                        parts.append(f"[alias: {alias}]")
                    if gname:
                        parts.append(f"[group: {gname}]")
                    child.setText(0, " ".join(parts))

    def _get_account(self, username: str):
        row = self.conn.execute(
            "SELECT profile_path, roblosecurity FROM accounts WHERE username=?", (username,)
        ).fetchone()
        if not row:
            raise RuntimeError("Account not found")
        profile_path = row[0]
        cookie = _dec(row[1]) if row[1] else None
        return profile_path, cookie

    # -------- Last played helpers --------
    def _record_last_played(self, username: str, place_id: str):
        """Fetch game info and store/update last played entry."""
        try:
            name, icon_url = self._fetch_game_info(place_id)
        except Exception:
            name, icon_url = "Unknown", ""
        with self.conn:
            self.conn.execute(
                "INSERT OR REPLACE INTO last_played (username, place_id, name, icon_url, played_at) VALUES (?, ?, ?, ?, strftime('%s','now'))",
                (username, place_id, name, icon_url),
            )
        self._refresh_last_played()

    def _fetch_game_info(self, place_id: str):
        """Return (game_name, icon_url) for a given Roblox ``place_id``.

        This helper now:
        1. Extracts the first digit-sequence from *any* user-supplied text (URL, jobId, etc.).
        2. Calls Roblox public game metadata APIs with a real browser-like *User-Agent* so the
           request is not blocked.
        3. Falls back to scraping the HTML for the `data-place-name` / `data-universe-id`
           attributes when the API is rate-limited or unavailable.
        4. Always returns a best-effort tuple instead of throwing – callers already blanket-catch
           the error and substitute "Unknown" so we keep behaviour stable.
        """
        import re

        # 1. Sanitise input → numeric placeId string
        m = re.search(r"\d+", str(place_id))
        if not m:
            raise RuntimeError("Invalid place id")
        pid = m.group(0)

        headers = {
            "User-Agent": (
                "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                "AppleWebKit/537.36 (KHTML, like Gecko) "
                "Chrome/120.0.0.0 Safari/537.36"
            ),
            "Accept": "application/json",
        }

        name: str = "Unknown"
        universe_id: str | None = None

        # 2. Preferred endpoint – multiget
        try:
            resp = requests.get(
                "https://games.roblox.com/v1/games/multiget-place-details",
                params={"placeIds": pid},
                headers=headers,
                timeout=10,
            )
            if resp.ok:
                info = resp.json()
                if isinstance(info, list) and info:
                    name = info[0].get("name", name)
                    universe_id = str(info[0].get("universeId")) if info[0].get("universeId") else None
        except Exception:
            pass  # ignore and try fallbacks

        # 3. Fallback endpoint – single get
        if universe_id is None:
            try:
                resp = requests.get(
                    "https://games.roblox.com/v1/games",
                    params={"placeIds": pid},
                    headers=headers,
                    timeout=10,
                )
                if resp.ok:
                    data = resp.json().get("data", [])
                    if data:
                        game = data[0]
                        name = game.get("name", name)
                        universe_id = str(game.get("universeId")) if game.get("universeId") else None
            except Exception:
                pass

        # 4. Last-resort – scrape the HTML metadata
        if name == "Unknown":
            try:
                resp = requests.get(f"https://www.roblox.com/games/{pid}", headers=headers, timeout=10)
                if resp.ok:
                    html = resp.text
                    m_name = re.search(r'data-place-name="([^"]+)"', html)
                    if m_name:
                        name = m_name.group(1)
                    if universe_id is None:
                        m_uni = re.search(r'data-universe-id="(\d+)"', html)
                        if m_uni:
                            universe_id = m_uni.group(1)
            except Exception:
                pass

        # 5. Retrieve icon thumbnail
        icon_url = ""
        if universe_id:
            try:
                resp = requests.get(
                    "https://thumbnails.roblox.com/v1/games/icons",
                    params={
                        "universeIds": universe_id,
                        "size": "150x150",
                        "format": "Png",
                        "isCircular": "false",
                    },
                    headers=headers,
                    timeout=10,
                )
                if resp.ok:
                    icon_data = resp.json().get("data", [])
                    if icon_data:
                        icon_url = icon_data[0].get("imageUrl", "")
            except Exception:
                pass

        return name, icon_url
        info = requests.get(f"https://games.roblox.com/v1/games?placeIds={place_id}").json()
        data = info.get("data", [])
        if not data:
            raise RuntimeError("No game data")
        game = data[0]
        name = game.get("name", "Unknown")
        universe_id = game.get("universeId")
        icon_url = ""
        if universe_id:
            icon_json = requests.get(
                f"https://thumbnails.roblox.com/v1/games/icons?universeIds={universe_id}&size=150x150&format=Png&isCircular=false"
            ).json()
            icon_data = icon_json.get("data", [])
            if icon_data:
                icon_url = icon_data[0].get("imageUrl", "")
        return name, icon_url

    def _refresh_last_played(self):
        selected = self.account_list.currentItem()
        if not selected or selected.data(0, Qt.UserRole) != "account":
            self.last_played_list.clear()
            return
        username = self._get_selected_username()
        rows = self.conn.execute(
            "SELECT place_id, name, icon_url FROM last_played WHERE username = ? ORDER BY played_at DESC LIMIT 20",
            (username,),
        ).fetchall()
        self.last_played_list.clear()
        update_needed = False
        for place_id, name, icon_url in rows:
            # Normalize/display name: decode HTML entities so emojis and symbols show correctly
            display_name = html.unescape(name or "Unknown")
            # Show full name in the list; put place_id in tooltip and user data
            item = QListWidgetItem(display_name)
            item.setData(Qt.UserRole, place_id)
            item.setToolTip(f"{display_name}\nPlace ID: {place_id}")
            if icon_url:
                try:
                    img_data = requests.get(icon_url, timeout=5).content
                    pix = QPixmap()
                    if pix.loadFromData(img_data) and not pix.isNull():
                        item.setIcon(QIcon(pix))
                except Exception:
                    pass
            self.last_played_list.addItem(item)
            # Heuristics: if the stored name likely came from page title or contains entities/marketing text, schedule update
            if (name and ('&#' in name or '&amp;' in name or 'NEW!' in name or 'UPDATE' in name)):
                update_needed = True

        if update_needed:
            def _bg_fix_names(username: str, items_snapshot: list[tuple[str, int]], rows_snapshot: list[tuple[str, str, str]]):
                updates: list[tuple[str, str, str]] = []  # (place_id, new_name, new_icon)
                for pid, idx in items_snapshot:
                    try:
                        new_name, new_icon = self._fetch_game_info(pid)
                    except Exception:
                        continue
                    if not new_name:
                        continue
                    old_name, old_icon = rows_snapshot[idx][1], rows_snapshot[idx][2]
                    if new_name != old_name or (new_icon and new_icon != old_icon):
                        updates.append((pid, new_name, new_icon or old_icon))
                # Apply updates on the main thread
                QTimer.singleShot(0, lambda: self._apply_last_played_updates(username, updates))

            items_snapshot = [(self.last_played_list.item(i).data(Qt.UserRole), i) for i in range(self.last_played_list.count())]
            rows_snapshot = list(rows)
            threading.Thread(target=_bg_fix_names, args=(username, items_snapshot, rows_snapshot), daemon=True).start()

    def _select_last_played(self, item):
        place_id = item.data(Qt.UserRole)
        if place_id:
            self.place_id_input.setText(str(place_id))

    def _apply_last_played_updates(self, username: str, updates: list[tuple[str, str, str]]):
        """Apply background-fetched name/icon updates on the main thread."""
        if not updates:
            return
        with self.conn:
            for pid, new_name, new_icon in updates:
                self.conn.execute(
                    "UPDATE last_played SET name=?, icon_url=? WHERE username=? AND place_id=?",
                    (new_name, new_icon, username, pid),
                )
        # refresh list
        self._refresh_last_played()

    # ----- Last Played deletion helpers -----
    def _delete_selected_last_played(self):
        """Remove selected last-played entries from DB and refresh list."""
        items = self.last_played_list.selectedItems()
        if not items:
            return
        username = self._get_selected_username()
        if not username:
            return
        with self.conn:
            for it in items:
                pid = it.data(Qt.UserRole)
                if pid is not None:
                    self.conn.execute(
                        "DELETE FROM last_played WHERE username=? AND place_id=?",
                        (username, str(pid)),
                    )
        self._refresh_last_played()

    def show_last_played_menu(self, pos):
        item = self.last_played_list.itemAt(pos)
        if not item:
            return
        menu = ModernMenu(self)
        menu.addAction("Delete selected", self._delete_selected_last_played)
        menu.exec(self.last_played_list.mapToGlobal(pos))

    def mousePressEvent(self, event):
        """Handle mouse press for window dragging/resizing."""
        if event.button() == Qt.LeftButton:
            local_pos = event.position().toPoint()
            # If over the title bar (or any of its descendants), start dragging
            over_bar = False
            w = self.childAt(local_pos)
            while w is not None:
                if w is self.title_bar:
                    over_bar = True
                    break
                w = w.parentWidget()
            if over_bar:
                self.dragging = True
                self.drag_start_position = event.globalPosition().toPoint() - self.frameGeometry().topLeft()
                event.accept()
                return
            # Otherwise, check for window resize on edges
            direction = self._get_resize_direction(local_pos)
            if direction:
                self.resizing = True
                self.resize_direction = direction
                event.accept()
                return

    def mouseMoveEvent(self, event):
        """Handle mouse move for window dragging/resizing and cursor feedback."""
        if not event.buttons():
            pt = event.position().toPoint()
            # Do not show resize cursors while hovering over the title bar (or descendants)
            over_bar = False
            w = self.childAt(pt)
            while w is not None:
                if w is self.title_bar:
                    over_bar = True
                    break
                w = w.parentWidget()
            if over_bar:
                self.unsetCursor()
                return
            direction = self._get_resize_direction(pt)
            if direction in ("top_left", "bottom_right"):
                self.setCursor(Qt.SizeFDiagCursor)
            elif direction in ("top_right", "bottom_left"):
                self.setCursor(Qt.SizeBDiagCursor)
            elif direction in ("left", "right"):
                self.setCursor(Qt.SizeHorCursor)
            elif direction in ("top", "bottom"):
                self.setCursor(Qt.SizeVerCursor)
            else:
                self.unsetCursor()

        if event.buttons() == Qt.LeftButton:
            if self.resizing and self.resize_direction:
                self._resize_window(event.globalPosition().toPoint())
                event.accept()
                return
            if self.dragging:
                self.move(event.globalPosition().toPoint() - self.drag_start_position)
                event.accept()

    def mouseReleaseEvent(self, event):
        """Handle mouse release to stop dragging/resizing."""
        self.dragging = False
        self.resizing = False
        self.resize_direction = None
        event.accept()

    def eventFilter(self, obj, event):
        if obj is self.last_played_list and event.type() == QEvent.KeyPress and event.key() == Qt.Key_Delete:
            self._delete_selected_last_played()
            return True
        return super().eventFilter(obj, event)

    def _get_auth_ticket(self, roblosec: str, place_id: str) -> str:
        """Exchange .ROBLOSECURITY for a one-time authentication ticket."""
        sess = requests.Session()
        sess.cookies[".ROBLOSECURITY"] = roblosec
        referer = f"https://www.roblox.com/games/{place_id}"
        headers = {"Referer": referer, "Content-Type": "application/json"}
        # Initial request to grab CSRF
        r1 = sess.post("https://auth.roblox.com/v1/authentication-ticket/", headers=headers, json={})
        token = r1.headers.get("x-csrf-token")
        if not token:
            raise RuntimeError("Failed to obtain CSRF token")
        headers["X-CSRF-TOKEN"] = token
        r2 = sess.post("https://auth.roblox.com/v1/authentication-ticket/", headers=headers, json={})
        ticket = r2.headers.get("rbx-authentication-ticket")
        if not ticket:
            raise RuntimeError("Authentication ticket header missing")
        return ticket

        # ---- END last_played helpers ----

        r1 = sess.post("https://auth.roblox.com/v1/authentication-ticket/", headers=headers, json={})
        token = r1.headers.get("x-csrf-token")
        if not token:
            raise RuntimeError("Failed to obtain CSRF token")
        headers["X-CSRF-TOKEN"] = token
        r2 = sess.post("https://auth.roblox.com/v1/authentication-ticket/", headers=headers, json={})
        ticket = r2.headers.get("rbx-authentication-ticket")
        if not ticket:
            raise RuntimeError("Authentication ticket header missing")
        return ticket

    def _build_roblox_player_uri(self, ticket: str, place_id: str) -> str:
        """Construct roblox-player URI that launches directly into the game."""
        launch_time = str(int(time.time() * 1000))
        browser_tracker = str(random.randint(100000, 999999))
        place_launcher_url = (
            f"https://assetgame.roblox.com/game/PlaceLauncher.ashx?request=RequestGame&placeId={place_id}"
        )
        params = {
            "launchmode": "play",
            "gameinfo": ticket,
            "launchtime": launch_time,
            "placelauncherurl": urllib.parse.quote_plus(place_launcher_url),
            "browsertrackerid": browser_tracker,
            "robloxLocale": "en_us",
            "gameLocale": "en_us",
            "channel": "",
            "LaunchExp": "InApp",
        }
        parts = ["1"] + [f"{k}:{v}" for k, v in params.items()]
        return "roblox-player:" + "+".join(parts)

    def _resolve_username(self, roblosec: str) -> str | None:
        """Use Roblox Web API to get the authenticated username from the cookie."""
        try:
            resp = requests.get(
                "https://users.roblox.com/v1/users/authenticated",
                headers={"Cookie": f".ROBLOSECURITY={roblosec};"},
                timeout=10,
            )
            if resp.status_code == 200:
                data = resp.json()
                return data.get("name")
        except Exception:
            pass
        return None

    # ---------- Theme ----------
    # ---------- Settings & Multi-Instance ----------
    def _load_settings(self):
        """Load persistent settings from DB and set flags."""
        with self.conn:
            self.conn.execute("CREATE TABLE IF NOT EXISTS settings (key TEXT PRIMARY KEY, value TEXT)")
        
        # Load multi-instance setting
        row = self.conn.execute("SELECT value FROM settings WHERE key='multi_instance'").fetchone()
        self.multi_instance_enabled = bool(int(row[0])) if row else False
        self._patcher_started = False
        
        # Load hide usernames setting
        row = self.conn.execute("SELECT value FROM settings WHERE key='hide_usernames'").fetchone()
        self.usernames_hidden = bool(int(row[0])) if row else False

    def _mutex_patcher_loop(self):
        """Continuously clear Roblox singleton mutex to allow multi-instance."""
        name = "ROBLOX_singletonMutex"
        kernel32 = ctypes.windll.kernel32
        OpenMutexW = kernel32.OpenMutexW
        CloseHandle = kernel32.CloseHandle
        MUTEX_ALL_ACCESS = 0x1F0001
        while True:
            try:
                handle = OpenMutexW(MUTEX_ALL_ACCESS, False, name)
                if handle:
                    CloseHandle(handle)
            except Exception:
                pass
            time.sleep(1)

    def _clear_mutex_burst(self, duration: float = 8.0, interval: float = 0.2):
        """Clear the Roblox mutex repeatedly for a short time window to avoid instance-kill races."""
        if not self.multi_instance_enabled:
            return
        def _worker():
            name = "ROBLOX_singletonMutex"
            kernel32 = ctypes.windll.kernel32
            OpenMutexW = kernel32.OpenMutexW
            CloseHandle = kernel32.CloseHandle
            MUTEX_ALL_ACCESS = 0x1F0001
            end = time.time() + max(0.5, duration)
            while time.time() < end:
                try:
                    handle = OpenMutexW(MUTEX_ALL_ACCESS, False, name)
                    if handle:
                        CloseHandle(handle)
                except Exception:
                    pass
                time.sleep(max(0.05, interval))
        threading.Thread(target=_worker, daemon=True).start()

    # ---------- Settings & Multi-Instance ----------
    def open_settings(self):
        """Open settings dialog containing Multi Launch tool."""
        dlg = ModernDialog(self, "Settings")
        dlg.resize(400, 500)
        dlg.content_widget.setStyleSheet(self.modern_dark_theme())
        lay = dlg.content_layout
        lay.setSpacing(10)

        info_lbl = QLabel("Select accounts to launch and enter the Place ID to join")
        lay.addWidget(info_lbl)

        # multi-instance toggle
        mi_chk = QCheckBox("Enable Multi-Instance Roblox")
        mi_chk.setChecked(self.multi_instance_enabled)
        lay.addWidget(mi_chk)

        # Hide usernames toggle (synced with main window)
        hide_usernames_chk = QCheckBox("Hide Usernames")
        hide_usernames_chk.setChecked(self.usernames_hidden)
        lay.addWidget(hide_usernames_chk)

        acc_list = QListWidgetDialog()
        acc_list.setSelectionMode(QAbstractItemView.ExtendedSelection)
        
        # Function to update account list display (read directly from DB)
        def update_account_display():
            acc_list.clear()
            rows = self.conn.execute("SELECT username, alias FROM accounts ORDER BY username").fetchall()
            for username, alias in rows:
                # Use alias as-is (no decryption needed for aliases)
                alias = alias or ""
                if hide_usernames_chk.isChecked():
                    text = f"[hidden] [alias: {alias}]" if alias else "[hidden]"
                else:
                    text = username if not alias else f"{username} [alias: {alias}]"
                item = QListWidgetItem(text)
                item.setData(Qt.UserRole, username)
                acc_list.addItem(item)
        
        # Initial population
        update_account_display()
        lay.addWidget(acc_list)

        place_input = QLineEdit()
        place_input.setPlaceholderText("Place ID (leave blank to use each account's current input)")
        lay.addWidget(place_input)

        launch_btn = QPushButton("🚀 Launch Selected")
        lay.addWidget(launch_btn)

        def on_multi_instance_toggle(state:int):
            self.multi_instance_enabled = bool(state)
            # Start patcher immediately if toggled on
            if self.multi_instance_enabled and not self._patcher_started:
                threading.Thread(target=self._mutex_patcher_loop, daemon=True).start()
                self._patcher_started = True
        mi_chk.stateChanged.connect(on_multi_instance_toggle)

        def on_hide_usernames_toggle(state:int):
            # Update main window setting
            self.usernames_hidden = bool(state)
            self.hide_usernames_chk.setChecked(self.usernames_hidden)
            
            # Save the setting
            with self.conn:
                self.conn.execute("INSERT OR REPLACE INTO settings(key,value) VALUES('hide_usernames',?)", 
                                (1 if self.usernames_hidden else 0,))
            
            # Update main window display
            self.toggle_hide_usernames(state)
            
            # Update settings dialog display
            update_account_display()
        
        hide_usernames_chk.stateChanged.connect(on_hide_usernames_toggle)

        def do_launch():
            selected_items = acc_list.selectedItems()
            if not selected_items:
                ModernMessageBox.warning(dlg, "No accounts", "Please select at least one account")
                return
            
            # Get actual usernames from selected items
            selected_usernames = [item.data(Qt.UserRole) for item in selected_items if item.data(Qt.UserRole)]
            
            pid = place_input.text().strip() or self.place_id_input.text().strip()
            if not pid:
                ModernMessageBox.warning(dlg, "Missing Place ID", "Please enter a Place ID")
                return
            # Launch sequentially with small stagger and mutex-burst to avoid instance kill
            for idx, uname in enumerate(selected_usernames):
                try:
                    if self.multi_instance_enabled:
                        self._clear_mutex_burst(duration=8.0, interval=0.2)
                    self._launch_game_for_account(uname, pid)
                    # Stagger a bit so each instance boots without killing the previous
                    if idx < len(selected_usernames) - 1:
                        time.sleep(1.5)
                except Exception as e:
                    ModernMessageBox.warning(dlg, "Launch error", f"{uname}: {e}")
            dlg.accept()
        launch_btn.clicked.connect(do_launch)
        
        def on_close():
            # save setting
            with self.conn:
                self.conn.execute("INSERT OR REPLACE INTO settings(key,value) VALUES('multi_instance',?)", (1 if self.multi_instance_enabled else 0,))
            if self.multi_instance_enabled and not self._patcher_started:
                threading.Thread(target=self._mutex_patcher_loop, daemon=True).start()
                self._patcher_started = True
        dlg.finished.connect(lambda _: on_close())
        dlg.exec()

    def _launch_game_for_account(self, username: str, place_id: str):
        """Launch a game for a specific account without altering UI selection."""
        profile_path, roblosec = self._get_account(username)
        if not roblosec:
            raise RuntimeError("Missing .ROBLOSECURITY for account")
        ticket = self._get_auth_ticket(roblosec, place_id)
        launch_uri = self._build_roblox_player_uri(ticket, place_id)
        if self.multi_instance_enabled:
            self._clear_mutex_burst(duration=8.0, interval=0.2)
        webbrowser.open(launch_uri)
        # Do not record here; main join flow records after user-initiated joins
        time.sleep(1)  # slight delay to avoid race

    # ---------- Theme ----------
    def modern_dark_theme(self):
        return """
        /* Base widget reset for theme area (avoid unintended rounded outlines) */
        QWidget { 
            background-color: #0a0d14; 
            color: #f0f0f0; 
            font-family: 'Segoe UI Variable Display', 'Segoe UI', system-ui, sans-serif; 
            font-size: 13px; 
            font-weight: 400;
            /* no global border radius here */
        }

        /* Ensure the root content uses squared top corners to align with title bar */
        #content_root {
            border-radius: 12px;
            border-top-left-radius: 0px;
            border-top-right-radius: 0px;
            border-top: none;
            outline: 0;
        }


        
        /* List Widgets */
        QListWidget { 
            background-color: #13171f; 
            border: none; 
            padding: 12px; 
            border-radius: 12px; 
            outline: 0;
            selection-background-color: transparent;
        }
        QListWidget::viewport { 
            background: transparent; 
            border: 0; 
        }
        
        /* Accounts Tree (styled like the old container) */
        QTreeWidget#accounts_tree {
            background: transparent; /* let viewport paint the background */
            border: none;
            outline: none;
            border-radius: 12px;
            padding: 8px 8px; /* inner padding to match list */
            color: #f0f0f0;
        }
        QTreeWidget#accounts_tree::viewport {
            background-color: #13171f; /* fix white background */
            border: none;
            border-radius: 12px;
        }
        QTreeWidget#accounts_tree::item {
            padding: 8px 12px; 
            border: 0;
            border-radius: 8px;
            margin: 2px 4px; /* small gaps */
            background-color: rgba(255, 255, 255, 0.02);
            border: 1px solid rgba(255, 255, 255, 0.05); /* subtle edge like old list */
            color: #f0f0f0;
        }
        QTreeWidget#accounts_tree::item:selected {
            background: qlineargradient(spread:pad, x1:0, y1:0, x2:1, y2:0,
                stop:0 rgba(64, 120, 255, 0.15), stop:1 rgba(104, 140, 255, 0.1));
            border: 1px solid rgba(64, 120, 255, 0.3);
            color: #ffffff;
        }
        QTreeWidget#accounts_tree::item:hover:!selected {
            background-color: rgba(255, 255, 255, 0.04);
            border: 1px solid rgba(255, 255, 255, 0.1);
        }
        QTreeWidget#accounts_tree::item:selected:hover {
            background: qlineargradient(spread:pad, x1:0, y1:0, x2:1, y2:0, 
                stop:0 rgba(64, 120, 255, 0.15), stop:1 rgba(104, 140, 255, 0.1));
            border: 1px solid rgba(64, 120, 255, 0.3);
            color: #ffffff;
        }
        /* Alternating rows subtle tint */
        QTreeWidget#accounts_tree::item:alternate {
            background-color: rgba(255, 255, 255, 0.015);
        }
        /* Branch (expand/collapse) indicators */
        QTreeView::branch {
            background: transparent;
        }
        QTreeView::branch:has-children:!has-siblings:closed,
        QTreeView::branch:closed:has-children:has-siblings {
            border-image: none;
            image: url(none);
        }
        QTreeView::branch:open:has-children:!has-siblings,
        QTreeView::branch:open:has-children:has-siblings {
            border-image: none;
            image: url(none);
        }
        
        /* List Items */
        QListWidget::item { 
            padding: 12px 16px; 
            border: 0;
            border-radius: 8px;
            margin-bottom: 4px;
            background-color: rgba(255, 255, 255, 0.02);
            border: 1px solid rgba(255, 255, 255, 0.05);
        }
        QListWidget::item:selected { 
            background: qlineargradient(spread:pad, x1:0, y1:0, x2:1, y2:0, 
                stop:0 rgba(64, 120, 255, 0.15), stop:1 rgba(104, 140, 255, 0.1));
            border: 1px solid rgba(64, 120, 255, 0.3);
            color: #ffffff;
        }
        /* Keep hover from overriding selection */
        QListWidget::item:hover:!selected { 
            background-color: rgba(255, 255, 255, 0.04);
            border: 1px solid rgba(255, 255, 255, 0.1);
        }
        /* When selected and hovered, keep the selected visuals */
        QListWidget::item:selected:hover {
            background: qlineargradient(spread:pad, x1:0, y1:0, x2:1, y2:0, 
                stop:0 rgba(64, 120, 255, 0.15), stop:1 rgba(104, 140, 255, 0.1));
            border: 1px solid rgba(64, 120, 255, 0.3);
            color: #ffffff;
        }
        
        /* Tab Widget */
        QTabWidget { 
            background: transparent; 
            border: none; 
        }
        QTabWidget::pane { 
            border: none; 
            background: transparent; 
            margin-top: 6px; /* subtle gap below tab bar */
        }
        QTabWidget::tab-bar {
            alignment: center; /* center the single tab label */
        }
        /* Rounded container around Last Played content (no outline) */
        #last_played_container {
            background-color: #0a0d14; /* match main content background */
            border: none; /* remove outline entirely so it doesn't surround the tab title */
            border-radius: 12px;
            border-top-left-radius: 12px;
            border-top-right-radius: 12px;
        }
        /* Also round the pane inside the tab widget so content respects the radius */
        QTabWidget#last_played_tab::pane {
            border-top-left-radius: 12px;
            border-top-right-radius: 12px;
            background: transparent;
            border: none;
            margin: 0; padding: 0;
        }
        QTabBar { 
            background: transparent; 
            border: none; 
        }
        QTabBar::tab { 
            background: transparent; 
            border: none; 
            border-radius: 0;
            padding: 6px 12px; 
            margin-right: 8px;
            font-weight: 600;
            color: #cfd3da;
        }
        QTabBar::tab:selected { 
            background: transparent;
            border: none;
            border-bottom: 2px solid #4078ff; /* underline only, no outline */
            color: #ffffff;
        }
        QTabBar::tab:hover:!selected {
            background: transparent;
            border: none;
            color: #e8ebf0;
        }
        QTabBar::tab:focus {
            outline: 0;
        }
        QTabWidget:focus {
            outline: 0;
            border: none;
            background: transparent;
        }
        
        /* Context Menus */
        QMenu { 
            background-color: #171c24; 
            color: #f0f0f0; 
            border: 1px solid #2a3139; 
            padding: 8px; 
            border-radius: 10px;
            font-size: 13px;
        }
        QMenu::separator { 
            height: 1px; 
            background: rgba(255, 255, 255, 0.1); 
            margin: 6px 8px; 
        }
        QMenu::item { 
            padding: 8px 16px; 
            border-radius: 6px;
            background: transparent;
        }
        QMenu::item:selected { 
            background: qlineargradient(spread:pad, x1:0, y1:0, x2:1, y2:0, 
                stop:0 rgba(64, 120, 255, 0.2), stop:1 rgba(104, 140, 255, 0.15));
            color: #ffffff; 
        }
        
        /* Buttons */
        QPushButton { 
            background: qlineargradient(spread:pad, x1:0, y1:0, x2:0, y2:1, 
                stop:0 rgba(35, 42, 52, 1), stop:1 rgba(25, 30, 38, 1));
            border: 1px solid rgba(255, 255, 255, 0.1); 
            padding: 12px 18px; 
            border-radius: 10px; 
            font-weight: 600;
            color: #f0f0f0;
        }
        QPushButton:hover { 
            background: qlineargradient(spread:pad, x1:0, y1:0, x2:0, y2:1, 
                stop:0 rgba(64, 120, 255, 0.3), stop:1 rgba(44, 90, 200, 0.2));
            border: 1px solid rgba(64, 120, 255, 0.4);
        }
        QPushButton:pressed {
            background: qlineargradient(spread:pad, x1:0, y1:0, x2:0, y2:1, 
                stop:0 rgba(44, 90, 200, 0.4), stop:1 rgba(34, 70, 160, 0.3));
        }
        
        /* Input Fields */
        QLineEdit { 
            background-color: #13171f; 
            border: 1px solid #1e2329; 
            padding: 12px 16px; 
            border-radius: 10px;
            font-size: 13px;
            color: #f0f0f0;
        }
        QLineEdit:focus {
            border: 2px solid rgba(64, 120, 255, 0.5);
            background-color: #171c24;
        }
        
        /* Group Box */
        QGroupBox { 
            border: 1px solid #1e2329; 
            margin-top: 12px; 
            border-radius: 12px; 
            font-weight: 600; 
            padding-top: 18px;
            background-color: rgba(255, 255, 255, 0.01);
        }
        QGroupBox::title {
            subcontrol-origin: margin;
            left: 12px;
            padding: 0 8px 0 8px;
            color: #d0d0d0;
        }
        
        /* Checkbox */
        QCheckBox { 
            padding: 8px;
            font-weight: 500;
        }
        QCheckBox::indicator {
            width: 18px;
            height: 18px;
            border-radius: 4px;
            border: 2px solid #2a3139;
            background: #13171f;
        }
        QCheckBox::indicator:checked {
            background: qlineargradient(spread:pad, x1:0, y1:0, x2:1, y2:1, 
                stop:0 rgba(64, 120, 255, 1), stop:1 rgba(84, 140, 255, 1));
            border: 2px solid #4078ff;
        }
        QCheckBox::indicator:hover {
            border: 2px solid rgba(64, 120, 255, 0.6);
        }
        
        /* Scrollbars */
        QScrollBar:vertical {
            border: none;
            background: #171c24;
            width: 8px;
            margin: 0;
            border-radius: 4px;
        }
        QScrollBar::handle:vertical {
            background: #2a3139;
            border-radius: 4px;
            min-height: 20px;
        }
        QScrollBar::handle:vertical:hover {
            background: #3a4149;
        }
        QScrollBar::add-line:vertical, QScrollBar::sub-line:vertical {
            border: none;
            background: none;
        }
        """

    def closeEvent(self, event):
        """Ensure all Playwright resources are released on application exit."""
        for ctx in self._open_contexts:
            try:
                ctx.close()
            except Exception:
                pass
        if self._playwright is not None:
            try:
                self._playwright.stop()
            except Exception:
                pass
        super().closeEvent(event)


if __name__ == "__main__":
    app = QApplication(sys.argv)
    win = RobloxAccountManager()

    win.show()
    sys.exit(app.exec())
