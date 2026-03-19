"""
FPGA UART Loader — Frontend Base
Autor: (tu nombre aquí)
Descripción: Interfaz de control para cargar programas y controlar
             periféricos en una FPGA vía UART desde Python/Arduino.
"""

import sys
import random
from datetime import datetime
from PyQt5.QtWidgets import (
    QApplication, QMainWindow, QWidget, QVBoxLayout, QHBoxLayout,
    QGridLayout, QPushButton, QLabel, QComboBox, QTextEdit,
    QProgressBar, QFrame, QSizePolicy, QScrollArea, QGroupBox,
    QSplitter
)
from PyQt5.QtCore import Qt, QTimer, QThread, pyqtSignal, QPropertyAnimation, QEasingCurve
from PyQt5.QtGui import QFont, QColor, QPalette, QFontDatabase, QIcon, QPainter, QBrush, QPen


# ─────────────────────────────────────────────
#  PALETA DE COLORES
# ─────────────────────────────────────────────
COLORS = {
    "bg_dark":      "#0D0F14",
    "bg_panel":     "#13161D",
    "bg_card":      "#1A1E28",
    "bg_hover":     "#222736",
    "accent":       "#00D4FF",
    "accent_dim":   "#0099BB",
    "accent_glow":  "rgba(0, 212, 255, 0.15)",
    "green":        "#00FF88",
    "green_dim":    "#00BB66",
    "yellow":       "#FFD600",
    "red":          "#FF4455",
    "text_primary": "#E8EAF0",
    "text_secondary":"#7A8299",
    "text_dim":     "#4A5068",
    "border":       "#252A38",
    "border_accent":"#00D4FF",
}

STYLESHEET = f"""
QMainWindow, QWidget {{
    background-color: {COLORS['bg_dark']};
    color: {COLORS['text_primary']};
    font-family: 'Courier New', monospace;
}}

/* ── PANEL LATERAL ── */
#sidebar {{
    background-color: {COLORS['bg_panel']};
    border-right: 1px solid {COLORS['border']};
}}

/* ── TARJETAS DE PROGRAMA ── */
QPushButton.program-btn {{
    background-color: {COLORS['bg_card']};
    color: {COLORS['text_primary']};
    border: 1px solid {COLORS['border']};
    border-left: 3px solid {COLORS['accent_dim']};
    border-radius: 4px;
    padding: 10px 14px;
    text-align: left;
    font-family: 'Courier New', monospace;
    font-size: 12px;
}}
QPushButton.program-btn:hover {{
    background-color: {COLORS['bg_hover']};
    border-left-color: {COLORS['accent']};
    color: {COLORS['accent']};
}}
QPushButton.program-btn:pressed {{
    background-color: {COLORS['accent_glow']};
}}
QPushButton.program-btn:checked {{
    background-color: {COLORS['bg_hover']};
    border-left: 3px solid {COLORS['accent']};
    color: {COLORS['accent']};
}}

/* ── BOTONES DE PERIFÉRICO ── */
QPushButton.periph-btn {{
    background-color: {COLORS['bg_card']};
    color: {COLORS['text_secondary']};
    border: 1px solid {COLORS['border']};
    border-radius: 4px;
    padding: 8px 12px;
    font-size: 11px;
    font-family: 'Courier New', monospace;
}}
QPushButton.periph-btn:hover {{
    background-color: {COLORS['bg_hover']};
    color: {COLORS['green']};
    border-color: {COLORS['green_dim']};
}}
QPushButton.periph-btn:checked {{
    background-color: rgba(0, 255, 136, 0.1);
    color: {COLORS['green']};
    border-color: {COLORS['green']};
}}

/* ── BOTÓN PRINCIPAL ENVIAR ── */
QPushButton#btn-upload {{
    background-color: {COLORS['accent']};
    color: {COLORS['bg_dark']};
    border: none;
    border-radius: 4px;
    padding: 12px 24px;
    font-weight: bold;
    font-size: 13px;
    font-family: 'Courier New', monospace;
    letter-spacing: 2px;
}}
QPushButton#btn-upload:hover {{
    background-color: #33DDFF;
}}
QPushButton#btn-upload:pressed {{
    background-color: {COLORS['accent_dim']};
}}
QPushButton#btn-upload:disabled {{
    background-color: {COLORS['text_dim']};
    color: {COLORS['bg_panel']};
}}

/* ── BOTÓN RESET ── */
QPushButton#btn-reset {{
    background-color: transparent;
    color: {COLORS['red']};
    border: 1px solid {COLORS['red']};
    border-radius: 4px;
    padding: 10px 18px;
    font-size: 12px;
    font-family: 'Courier New', monospace;
    letter-spacing: 1px;
}}
QPushButton#btn-reset:hover {{
    background-color: rgba(255, 68, 85, 0.12);
}}

/* ── BARRA DE PROGRESO ── */
QProgressBar {{
    background-color: {COLORS['bg_card']};
    border: 1px solid {COLORS['border']};
    border-radius: 2px;
    height: 8px;
    text-align: center;
    font-size: 10px;
    color: {COLORS['text_secondary']};
}}
QProgressBar::chunk {{
    background-color: {COLORS['accent']};
    border-radius: 2px;
}}

/* ── LOG / CONSOLA ── */
QTextEdit#log-area {{
    background-color: {COLORS['bg_dark']};
    color: #88FF99;
    border: 1px solid {COLORS['border']};
    border-radius: 4px;
    font-family: 'Courier New', monospace;
    font-size: 11px;
    padding: 8px;
    selection-background-color: {COLORS['accent_dim']};
}}

/* ── COMBO (Puerto serial) ── */
QComboBox {{
    background-color: {COLORS['bg_card']};
    color: {COLORS['text_primary']};
    border: 1px solid {COLORS['border']};
    border-radius: 4px;
    padding: 6px 10px;
    font-family: 'Courier New', monospace;
    font-size: 12px;
    min-width: 120px;
}}
QComboBox:hover {{
    border-color: {COLORS['accent_dim']};
}}
QComboBox::drop-down {{
    border: none;
    padding-right: 8px;
}}
QComboBox QAbstractItemView {{
    background-color: {COLORS['bg_card']};
    color: {COLORS['text_primary']};
    border: 1px solid {COLORS['border']};
    selection-background-color: {COLORS['bg_hover']};
}}

/* ── LABELS ── */
QLabel#section-title {{
    color: {COLORS['text_dim']};
    font-size: 9px;
    letter-spacing: 3px;
    font-family: 'Courier New', monospace;
}}
QLabel#header-title {{
    color: {COLORS['accent']};
    font-size: 16px;
    font-weight: bold;
    font-family: 'Courier New', monospace;
    letter-spacing: 3px;
}}
QLabel#status-val {{
    font-size: 11px;
    font-family: 'Courier New', monospace;
}}

/* ── SEPARADORES ── */
QFrame[frameShape="4"],
QFrame[frameShape="5"] {{
    color: {COLORS['border']};
}}

QScrollArea {{
    border: none;
    background-color: transparent;
}}
QScrollBar:vertical {{
    background-color: {COLORS['bg_panel']};
    width: 6px;
    border: none;
}}
QScrollBar::handle:vertical {{
    background-color: {COLORS['border']};
    border-radius: 3px;
    min-height: 20px;
}}
QScrollBar::handle:vertical:hover {{
    background-color: {COLORS['text_dim']};
}}
QScrollBar::add-line:vertical, QScrollBar::sub-line:vertical {{
    height: 0;
}}
"""


# ─────────────────────────────────────────────
#  INDICADOR LED  (widget custom)
# ─────────────────────────────────────────────
class LedIndicator(QWidget):
    def __init__(self, color_on="#00FF88", color_off="#1A2A20", size=10):
        super().__init__()
        self._on = False
        self._color_on  = QColor(color_on)
        self._color_off = QColor(color_off)
        self._size = size
        self.setFixedSize(size + 4, size + 4)

    def set_state(self, on: bool):
        self._on = on
        self.update()

    def paintEvent(self, event):
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing)
        color = self._color_on if self._on else self._color_off
        p.setBrush(QBrush(color))
        p.setPen(QPen(color.darker(150), 1))
        offset = 2
        p.drawEllipse(offset, offset, self._size, self._size)


# ─────────────────────────────────────────────
#  VENTANA PRINCIPAL
# ─────────────────────────────────────────────
class FPGALoader(QMainWindow):

    # ── Catálogo de programas de ejemplo (reemplaza con los tuyos) ──
    PROGRAMS = [
        {"id": "prog_blink",    "name": "Blink LED",         "desc": "Blinker 1 Hz en GPIO[0]",       "size": 128},
        {"id": "prog_counter",  "name": "Counter 8-bit",     "desc": "Contador binario en GPIO[7:0]",  "size": 256},
        {"id": "prog_pwm",      "name": "PWM Dimmer",        "desc": "Control PWM de LED RGB",         "size": 512},
        {"id": "prog_uart_echo","name": "UART Echo",         "desc": "Loopback UART 115200 baud",      "size": 320},
        {"id": "prog_alu",      "name": "ALU Demo",          "desc": "Demo de unidad aritmética",      "size": 640},
        {"id": "prog_fsm",      "name": "FSM Semáforo",      "desc": "Máquina de estados semáforo",    "size": 480},
    ]

    # ── Catálogo de periféricos ──
    PERIPHERALS = [
        {"id": "per_led",     "name": "LEDs",          "icon": "◈"},
        {"id": "per_motor",   "name": "Motor DC",      "icon": "⟳"},
        {"id": "per_servo",   "name": "Servo",         "icon": "⤢"},
        {"id": "per_display", "name": "Display 7-seg", "icon": "▦"},
        {"id": "per_sensor",  "name": "Sensor Temp",   "icon": "⊕"},
        {"id": "per_btn",     "name": "Botones",       "icon": "⊞"},
    ]

    def __init__(self):
        super().__init__()
        self.setWindowTitle("FPGA UART Loader  //  v0.1-frontend")
        self.resize(1060, 700)
        self.setMinimumSize(900, 580)

        self.selected_program = None
        self.selected_periph  = None
        self._upload_progress = 0
        self._connected = False

        self._build_ui()
        self._apply_styles()

        # Timer de parpadeo del LED de conexión
        self._led_blink_timer = QTimer()
        self._led_blink_timer.timeout.connect(self._blink_led)
        self._blink_state = False

    # ─────────────────────
    #  CONSTRUCCIÓN DE UI
    # ─────────────────────
    def _build_ui(self):
        central = QWidget()
        self.setCentralWidget(central)
        root = QHBoxLayout(central)
        root.setContentsMargins(0, 0, 0, 0)
        root.setSpacing(0)

        # ── Sidebar ──────────────────────────────────────────────────
        sidebar = QWidget()
        sidebar.setObjectName("sidebar")
        sidebar.setFixedWidth(260)
        sidebar_layout = QVBoxLayout(sidebar)
        sidebar_layout.setContentsMargins(16, 20, 16, 16)
        sidebar_layout.setSpacing(0)

        # Logo / título
        logo = QLabel("FPGA\nLOADER")
        logo.setObjectName("header-title")
        logo.setAlignment(Qt.AlignLeft)
        sidebar_layout.addWidget(logo)

        sub = QLabel("UART INSTRUCTION UPLOADER")
        sub.setObjectName("section-title")
        sub.setContentsMargins(0, 2, 0, 20)
        sidebar_layout.addWidget(sub)

        sidebar_layout.addWidget(self._make_separator())

        # ── Sección: PROGRAMAS ────────────────────────────────────────
        sidebar_layout.addSpacing(16)
        sidebar_layout.addWidget(self._section_label("PROGRAMAS"))
        sidebar_layout.addSpacing(8)

        self.prog_buttons = []
        for prog in self.PROGRAMS:
            btn = QPushButton(f"{prog['name']}\n{prog['desc']}")
            btn.setProperty("class", "program-btn")
            btn.setCheckable(True)
            btn.setAutoExclusive(False)
            btn.clicked.connect(lambda checked, p=prog, b=btn: self._select_program(p, b))
            sidebar_layout.addWidget(btn)
            sidebar_layout.addSpacing(4)
            self.prog_buttons.append(btn)

        sidebar_layout.addSpacing(16)
        sidebar_layout.addWidget(self._make_separator())

        # ── Sección: PERIFÉRICOS ──────────────────────────────────────
        sidebar_layout.addSpacing(16)
        sidebar_layout.addWidget(self._section_label("PERIFÉRICOS"))
        sidebar_layout.addSpacing(8)

        periph_grid = QGridLayout()
        periph_grid.setSpacing(4)
        self.periph_buttons = []
        for i, per in enumerate(self.PERIPHERALS):
            btn = QPushButton(f"{per['icon']}  {per['name']}")
            btn.setProperty("class", "periph-btn")
            btn.setCheckable(True)
            btn.setAutoExclusive(False)
            btn.clicked.connect(lambda checked, p=per, b=btn: self._select_periph(p, b))
            periph_grid.addWidget(btn, i // 2, i % 2)
            self.periph_buttons.append(btn)
        sidebar_layout.addLayout(periph_grid)

        sidebar_layout.addStretch()
        root.addWidget(sidebar)

        # ── Panel derecho ─────────────────────────────────────────────
        right = QWidget()
        right_layout = QVBoxLayout(right)
        right_layout.setContentsMargins(24, 20, 24, 20)
        right_layout.setSpacing(12)

        # ── Barra superior: conexión serial ───────────────────────────
        top_bar = QHBoxLayout()
        top_bar.setSpacing(10)

        # LED de estado
        self.led_conn = LedIndicator(color_on=COLORS["green"], size=10)
        top_bar.addWidget(self.led_conn, alignment=Qt.AlignVCenter)

        self.lbl_conn_status = QLabel("DESCONECTADO")
        self.lbl_conn_status.setObjectName("status-val")
        self.lbl_conn_status.setStyleSheet(f"color: {COLORS['red']}; letter-spacing: 1px;")
        top_bar.addWidget(self.lbl_conn_status)

        top_bar.addSpacing(12)

        lbl_port = QLabel("PUERTO:")
        lbl_port.setObjectName("section-title")
        lbl_port.setContentsMargins(0, 0, 4, 0)
        top_bar.addWidget(lbl_port)

        self.combo_port = QComboBox()
        self.combo_port.addItems(["COM3", "COM4", "/dev/ttyUSB0", "/dev/ttyUSB1", "/dev/ttyACM0"])
        top_bar.addWidget(self.combo_port)

        lbl_baud = QLabel("BAUD:")
        lbl_baud.setObjectName("section-title")
        lbl_baud.setContentsMargins(8, 0, 4, 0)
        top_bar.addWidget(lbl_baud)

        self.combo_baud = QComboBox()
        self.combo_baud.addItems(["9600", "19200", "57600", "115200", "230400"])
        self.combo_baud.setCurrentText("115200")
        self.combo_baud.setFixedWidth(90)
        top_bar.addWidget(self.combo_baud)

        self.btn_connect = QPushButton("CONECTAR")
        self.btn_connect.setObjectName("btn-upload")
        self.btn_connect.setFixedWidth(110)
        self.btn_connect.clicked.connect(self._toggle_connection)
        top_bar.addWidget(self.btn_connect)

        top_bar.addStretch()

        right_layout.addLayout(top_bar)
        right_layout.addWidget(self._make_separator())

        # ── Área de detalle / selección activa ────────────────────────
        detail_bar = QHBoxLayout()
        detail_bar.setSpacing(20)

        self.lbl_selected_title = QLabel("SELECCIÓN ACTIVA")
        self.lbl_selected_title.setObjectName("section-title")
        detail_bar.addWidget(self.lbl_selected_title)

        self.lbl_selected_val = QLabel("— ninguna —")
        self.lbl_selected_val.setObjectName("status-val")
        self.lbl_selected_val.setStyleSheet(f"color: {COLORS['text_secondary']};")
        detail_bar.addWidget(self.lbl_selected_val)

        detail_bar.addStretch()

        self.lbl_bytes_title = QLabel("INSTRUCCIONES:")
        self.lbl_bytes_title.setObjectName("section-title")
        detail_bar.addWidget(self.lbl_bytes_title)

        self.lbl_bytes_val = QLabel("—")
        self.lbl_bytes_val.setObjectName("status-val")
        self.lbl_bytes_val.setStyleSheet(f"color: {COLORS['text_secondary']};")
        detail_bar.addWidget(self.lbl_bytes_val)

        right_layout.addLayout(detail_bar)

        # ── Progress bar ──────────────────────────────────────────────
        progress_row = QHBoxLayout()
        lbl_tx = QLabel("TX:")
        lbl_tx.setObjectName("section-title")
        lbl_tx.setFixedWidth(24)
        progress_row.addWidget(lbl_tx)

        self.progress_bar = QProgressBar()
        self.progress_bar.setValue(0)
        self.progress_bar.setFormat("%p%  —  %v / %m bytes")
        self.progress_bar.setFixedHeight(18)
        progress_row.addWidget(self.progress_bar)

        self.lbl_progress_status = QLabel("IDLE")
        self.lbl_progress_status.setObjectName("section-title")
        self.lbl_progress_status.setFixedWidth(80)
        self.lbl_progress_status.setAlignment(Qt.AlignRight)
        progress_row.addWidget(self.lbl_progress_status)

        right_layout.addLayout(progress_row)
        right_layout.addWidget(self._make_separator())

        # ── LOG / Consola ─────────────────────────────────────────────
        log_label = self._section_label("LOG  //  UART TRANSMISSION")
        right_layout.addWidget(log_label)

        self.log_area = QTextEdit()
        self.log_area.setObjectName("log-area")
        self.log_area.setReadOnly(True)
        self.log_area.setMinimumHeight(180)
        right_layout.addWidget(self.log_area)

        # ── Botones de acción ─────────────────────────────────────────
        action_row = QHBoxLayout()
        action_row.setSpacing(10)

        self.btn_upload = QPushButton("▶  CARGAR PROGRAMA")
        self.btn_upload.setObjectName("btn-upload")
        self.btn_upload.setEnabled(False)
        self.btn_upload.clicked.connect(self._upload_program)
        action_row.addWidget(self.btn_upload)

        self.btn_reset = QPushButton("⟳  RESET FPGA")
        self.btn_reset.setObjectName("btn-reset")
        self.btn_reset.clicked.connect(self._reset_fpga)
        action_row.addWidget(self.btn_reset)

        action_row.addStretch()

        self.btn_clear_log = QPushButton("LIMPIAR LOG")
        self.btn_clear_log.setObjectName("btn-reset")
        self.btn_clear_log.setStyleSheet(
            f"color: {COLORS['text_dim']}; border-color: {COLORS['border']};"
        )
        self.btn_clear_log.clicked.connect(self.log_area.clear)
        action_row.addWidget(self.btn_clear_log)

        right_layout.addLayout(action_row)
        root.addWidget(right)

        # ── Log inicial ────────────────────────────────────────────────
        self._log("SISTEMA INICIALIZADO", level="info")
        self._log("Selecciona un programa o periférico y conecta el puerto serial.", level="info")

    # ─────────────────────
    #  ESTILOS
    # ─────────────────────
    def _apply_styles(self):
        self.setStyleSheet(STYLESHEET)
        # Forzar clases CSS en botones (PyQt no soporta class selector nativamente,
        # reapplicamos el estilo manualmente a cada botón)
        for btn in self.prog_buttons:
            btn.setStyleSheet(f"""
                QPushButton {{
                    background-color: {COLORS['bg_card']};
                    color: {COLORS['text_primary']};
                    border: 1px solid {COLORS['border']};
                    border-left: 3px solid {COLORS['accent_dim']};
                    border-radius: 4px;
                    padding: 8px 12px;
                    text-align: left;
                    font-family: 'Courier New', monospace;
                    font-size: 11px;
                }}
                QPushButton:hover {{
                    background-color: {COLORS['bg_hover']};
                    border-left-color: {COLORS['accent']};
                    color: {COLORS['accent']};
                }}
                QPushButton:checked {{
                    background-color: {COLORS['bg_hover']};
                    border-left: 3px solid {COLORS['accent']};
                    color: {COLORS['accent']};
                }}
            """)

        for btn in self.periph_buttons:
            btn.setStyleSheet(f"""
                QPushButton {{
                    background-color: {COLORS['bg_card']};
                    color: {COLORS['text_secondary']};
                    border: 1px solid {COLORS['border']};
                    border-radius: 4px;
                    padding: 7px 10px;
                    font-size: 11px;
                    font-family: 'Courier New', monospace;
                }}
                QPushButton:hover {{
                    background-color: {COLORS['bg_hover']};
                    color: {COLORS['green']};
                    border-color: {COLORS['green_dim']};
                }}
                QPushButton:checked {{
                    background-color: rgba(0, 255, 136, 0.08);
                    color: {COLORS['green']};
                    border-color: {COLORS['green']};
                }}
            """)

    # ─────────────────────
    #  HELPERS
    # ─────────────────────
    def _make_separator(self):
        line = QFrame()
        line.setFrameShape(QFrame.HLine)
        line.setStyleSheet(f"color: {COLORS['border']};")
        return line

    def _section_label(self, text):
        lbl = QLabel(text)
        lbl.setObjectName("section-title")
        lbl.setStyleSheet(
            f"color: {COLORS['text_dim']}; font-size: 9px; "
            f"letter-spacing: 3px; font-family: 'Courier New', monospace;"
        )
        return lbl

    def _log(self, msg: str, level: str = "data"):
        ts = datetime.now().strftime("%H:%M:%S.%f")[:-3]
        colors_map = {
            "info":    COLORS["text_secondary"],
            "ok":      COLORS["green"],
            "warn":    COLORS["yellow"],
            "error":   COLORS["red"],
            "data":    "#88FF99",
            "tx":      COLORS["accent"],
        }
        prefixes = {
            "info":  "  INFO",
            "ok":    "    OK",
            "warn":  "  WARN",
            "error": " ERROR",
            "data":  "  DATA",
            "tx":    "    TX",
        }
        color   = colors_map.get(level, "#88FF99")
        prefix  = prefixes.get(level, "  DATA")
        html = (
            f'<span style="color:{COLORS["text_dim"]};">[{ts}]</span> '
            f'<span style="color:{color}; font-weight:bold;">{prefix}</span> '
            f'<span style="color:{color};">{msg}</span>'
        )
        self.log_area.append(html)
        # Auto-scroll
        sb = self.log_area.verticalScrollBar()
        sb.setValue(sb.maximum())

    # ─────────────────────
    #  HANDLERS
    # ─────────────────────
    def _select_program(self, prog: dict, clicked_btn: QPushButton):
        # Deseleccionar otros programas
        for btn in self.prog_buttons:
            if btn is not clicked_btn:
                btn.setChecked(False)
        # Deseleccionar periféricos
        for btn in self.periph_buttons:
            btn.setChecked(False)
        self.selected_periph = None

        if clicked_btn.isChecked():
            self.selected_program = prog
            self.lbl_selected_val.setText(prog["name"])
            self.lbl_selected_val.setStyleSheet(f"color: {COLORS['accent']};")
            self.lbl_bytes_val.setText(f"{prog['size']} instr.")
            self.lbl_bytes_val.setStyleSheet(f"color: {COLORS['accent']};")
            self.progress_bar.setMaximum(prog["size"])
            self.progress_bar.setValue(0)
            self._update_upload_btn()
            self._log(f"Programa seleccionado: {prog['name']}  [{prog['size']} instrucciones]", level="info")
        else:
            self.selected_program = None
            self._clear_selection_display()

    def _select_periph(self, per: dict, clicked_btn: QPushButton):
        # Deseleccionar otros periféricos
        for btn in self.periph_buttons:
            if btn is not clicked_btn:
                btn.setChecked(False)
        # Deseleccionar programas
        for btn in self.prog_buttons:
            btn.setChecked(False)
        self.selected_program = None

        if clicked_btn.isChecked():
            self.selected_periph = per
            self.lbl_selected_val.setText(f"{per['icon']}  {per['name']}")
            self.lbl_selected_val.setStyleSheet(f"color: {COLORS['green']};")
            self.lbl_bytes_val.setText("periférico")
            self.lbl_bytes_val.setStyleSheet(f"color: {COLORS['green']};")
            self._update_upload_btn()
            self._log(f"Periférico seleccionado: {per['name']}", level="info")
        else:
            self.selected_periph = None
            self._clear_selection_display()

    def _clear_selection_display(self):
        self.lbl_selected_val.setText("— ninguna —")
        self.lbl_selected_val.setStyleSheet(f"color: {COLORS['text_secondary']};")
        self.lbl_bytes_val.setText("—")
        self.lbl_bytes_val.setStyleSheet(f"color: {COLORS['text_secondary']};")
        self.btn_upload.setEnabled(False)

    def _update_upload_btn(self):
        has_selection = (self.selected_program or self.selected_periph) is not None
        self.btn_upload.setEnabled(has_selection and self._connected)

    def _toggle_connection(self):
        """
        Stub de conexión serial — aquí conectarás tu lógica de pyserial.
        """
        if not self._connected:
            port = self.combo_port.currentText()
            baud = self.combo_baud.currentText()
            # ── TODO: abrir puerto serial ──
            # self.serial = serial.Serial(port, int(baud), timeout=1)
            self._connected = True
            self.lbl_conn_status.setText(f"CONECTADO  {port}")
            self.lbl_conn_status.setStyleSheet(f"color: {COLORS['green']}; letter-spacing: 1px;")
            self.btn_connect.setText("DESCONECTAR")
            self.btn_connect.setStyleSheet(
                f"background-color: transparent; color: {COLORS['red']};"
                f"border: 1px solid {COLORS['red']}; border-radius: 4px;"
                f"padding: 12px 24px; font-size: 12px; letter-spacing: 2px;"
            )
            self.combo_port.setEnabled(False)
            self.combo_baud.setEnabled(False)
            self._led_blink_timer.start(600)
            self._update_upload_btn()
            self._log(f"Puerto abierto: {port} @ {baud} baud", level="ok")
        else:
            # ── TODO: cerrar puerto serial ──
            # self.serial.close()
            self._connected = False
            self.lbl_conn_status.setText("DESCONECTADO")
            self.lbl_conn_status.setStyleSheet(f"color: {COLORS['red']}; letter-spacing: 1px;")
            self.btn_connect.setText("CONECTAR")
            self.btn_connect.setStyleSheet("")   # restaurar stylesheet global
            self.combo_port.setEnabled(True)
            self.combo_baud.setEnabled(True)
            self._led_blink_timer.stop()
            self.led_conn.set_state(False)
            self.btn_upload.setEnabled(False)
            self._log("Puerto serial cerrado.", level="warn")

    def _blink_led(self):
        self._blink_state = not self._blink_state
        self.led_conn.set_state(self._blink_state)

    def _upload_program(self):
        """
        Stub de carga — aquí colocará tu lógica de envío UART.
        """
        if self.selected_program:
            name = self.selected_program["name"]
            total = self.selected_program["size"]
            self._log(f"Iniciando carga: {name}  ({total} instrucciones)", level="tx")
        elif self.selected_periph:
            name = self.selected_periph["name"]
            total = 64  # placeholder
            self._log(f"Enviando configuración periférico: {name}", level="tx")
        else:
            return

        self.progress_bar.setMaximum(total)
        self.progress_bar.setValue(0)
        self.lbl_progress_status.setText("TX...")
        self.btn_upload.setEnabled(False)

        # ── Simulación de progreso (reemplaza con tu hilo de envío UART) ──
        self._sim_progress = 0
        self._sim_total    = total
        self._sim_timer    = QTimer()
        self._sim_timer.timeout.connect(self._sim_step)
        self._sim_timer.start(30)

    def _sim_step(self):
        """Simulación de envío — REEMPLAZAR con lógica real de UART."""
        step = max(1, self._sim_total // 40)
        self._sim_progress = min(self._sim_progress + step, self._sim_total)
        self.progress_bar.setValue(self._sim_progress)

        # Log periódico simulado
        if self._sim_progress % (self._sim_total // 8 or 1) < step:
            pct = int(self._sim_progress / self._sim_total * 100)
            self._log(
                f"0x{self._sim_progress:04X}  →  FPGA MEM  [{pct:3d}%]",
                level="tx"
            )

        if self._sim_progress >= self._sim_total:
            self._sim_timer.stop()
            self.lbl_progress_status.setText("OK")
            self._log("Carga completada. FPGA lista para ejecutar.", level="ok")
            self.progress_bar.setStyleSheet(
                f"QProgressBar::chunk {{ background-color: {COLORS['green']}; }}"
            )
            self._update_upload_btn()

    def _reset_fpga(self):
        """Stub de reset — envía señal de reset a la FPGA."""
        # ── TODO: serial.write(RESET_CMD) ──
        self.progress_bar.setValue(0)
        self.progress_bar.setStyleSheet("")
        self.lbl_progress_status.setText("IDLE")
        self._log("RESET enviado a FPGA.", level="warn")


# ─────────────────────────────────────────────
#  ENTRY POINT
# ─────────────────────────────────────────────
if __name__ == "__main__":
    app = QApplication(sys.argv)
    app.setStyle("Fusion")

    # Paleta oscura base para que Fusion no sobreescriba
    palette = QPalette()
    palette.setColor(QPalette.Window,          QColor(COLORS["bg_dark"]))
    palette.setColor(QPalette.WindowText,      QColor(COLORS["text_primary"]))
    palette.setColor(QPalette.Base,            QColor(COLORS["bg_card"]))
    palette.setColor(QPalette.AlternateBase,   QColor(COLORS["bg_panel"]))
    palette.setColor(QPalette.Text,            QColor(COLORS["text_primary"]))
    palette.setColor(QPalette.Button,          QColor(COLORS["bg_card"]))
    palette.setColor(QPalette.ButtonText,      QColor(COLORS["text_primary"]))
    palette.setColor(QPalette.Highlight,       QColor(COLORS["accent"]))
    palette.setColor(QPalette.HighlightedText, QColor(COLORS["bg_dark"]))
    app.setPalette(palette)

    win = FPGALoader()
    win.show()
    sys.exit(app.exec_())
