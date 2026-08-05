from __future__ import annotations

import json
import logging
import math
import os
import queue
import re
import shutil
import socket
import subprocess
import sys
import threading
import time
import traceback
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable
from urllib.parse import unquote, urlsplit, urlunsplit

import numpy as np
import requests
import rasterio
from PIL import Image, ImageDraw, ImageTk
from pyproj import Geod
from rasterio.enums import Resampling
from rasterio.transform import from_origin
from rasterio.vrt import WarpedVRT
from rasterio.warp import transform_bounds
from rasterio.windows import Window
import tkinter as tk
from tkinter import filedialog, messagebox, ttk
from tkinter.scrolledtext import ScrolledText
from tkintermapview import TkinterMapView


APP_NAME = "CanElevation Terrain Exporter"
APP_VERSION = "1.0.8"
BUILD_MARKER = "display-friendly-heightmap-outputs-2026-08-05"
STAC_API = "https://datacube.services.geo.ca/stac/api/"
DEFAULT_BOUNDS = (-119.255, 53.070, -118.965, 53.165)
DEFAULT_CENTER = (53.1175, -119.1100)
DEFAULT_FILENAME = "mount_robson_dtm"
OUTPUT_NODATA = -9999.0
BLOCK_SIZE = 1024
COVERAGE_GRID_SIZE = 320
REQUEST_TIMEOUT = (20, 120)
DEFAULT_PROXY_URL = "http://127.0.0.1:3128"
PROXY_MODE_AUTO = "auto"
PROXY_MODE_MANUAL = "manual"
PROXY_MODE_DIRECT = "direct"
PROXY_MODE_LABELS = {
    PROXY_MODE_AUTO: "Auto / system settings",
    PROXY_MODE_MANUAL: "Manual proxy",
    PROXY_MODE_DIRECT: "Direct connection (no proxy)",
}
PROXY_LABEL_TO_MODE = {label: mode for mode, label in PROXY_MODE_LABELS.items()}
PROXY_ENV_KEYS = (
    "HTTP_PROXY",
    "HTTPS_PROXY",
    "ALL_PROXY",
    "http_proxy",
    "https_proxy",
    "all_proxy",
    "NO_PROXY",
    "no_proxy",
)


@dataclass(frozen=True)
class ProxySettings:
    mode: str = PROXY_MODE_AUTO
    proxy_url: str = ""
    allow_untrusted_gdal_ssl: bool = False

    def validated(self) -> "ProxySettings":
        if self.mode not in PROXY_MODE_LABELS:
            raise ValueError(f"Unknown proxy mode: {self.mode}")
        allow_untrusted = bool(self.allow_untrusted_gdal_ssl)
        if self.mode != PROXY_MODE_MANUAL:
            return ProxySettings(self.mode, "", allow_untrusted)

        raw = self.proxy_url.strip()
        if not raw:
            raise ValueError("Enter a proxy URL, for example http://127.0.0.1:3128")
        if "://" not in raw:
            raw = "http://" + raw
        parsed = urlsplit(raw)
        if parsed.scheme.lower() not in {"http", "https"}:
            raise ValueError("The proxy URL must start with http:// or https://")
        if not parsed.hostname:
            raise ValueError("The proxy URL does not contain a valid hostname.")
        try:
            _ = parsed.port
        except ValueError as error:
            raise ValueError("The proxy URL contains an invalid port.") from error
        normalized = urlunsplit(
            (
                parsed.scheme.lower(),
                parsed.netloc,
                parsed.path.rstrip("/"),
                "",
                "",
            )
        )
        return ProxySettings(self.mode, normalized, allow_untrusted)

    def requests_proxies(self) -> dict[str, str] | None:
        settings = self.validated()
        if settings.mode != PROXY_MODE_MANUAL:
            return None
        return {"http": settings.proxy_url, "https": settings.proxy_url}

    def redacted_display(self) -> str:
        settings = self.validated()
        if settings.mode == PROXY_MODE_AUTO:
            display = "Auto / system proxy"
        elif settings.mode == PROXY_MODE_DIRECT:
            display = "Direct connection"
        else:
            try:
                parsed = urlsplit(settings.proxy_url)
            except ValueError:
                return "Manual proxy (invalid URL)"
            hostname = parsed.hostname or ""
            if ":" in hostname and not hostname.startswith("["):
                hostname = f"[{hostname}]"
            host_port = hostname + (f":{parsed.port}" if parsed.port else "")
            display = f"Manual proxy: {parsed.scheme}://{host_port}"
        if settings.allow_untrusted_gdal_ssl:
            display += " · GDAL cert workaround on"
        return display

    def apply_process_environment(self, original_environment: dict[str, str | None]) -> None:
        # Restore the environment captured at program startup first. This makes
        # switching back to Auto predictable and prevents stale manual settings.
        for key in PROXY_ENV_KEYS:
            original_value = original_environment.get(key)
            if original_value is None:
                os.environ.pop(key, None)
            else:
                os.environ[key] = original_value

        settings = self.validated()
        if settings.mode == PROXY_MODE_MANUAL:
            for key in (
                "HTTP_PROXY",
                "HTTPS_PROXY",
                "ALL_PROXY",
                "http_proxy",
                "https_proxy",
                "all_proxy",
            ):
                os.environ[key] = settings.proxy_url
            for key in ("NO_PROXY", "no_proxy"):
                os.environ[key] = "localhost,127.0.0.1,::1"
        elif settings.mode == PROXY_MODE_DIRECT:
            for key in (
                "HTTP_PROXY",
                "HTTPS_PROXY",
                "ALL_PROXY",
                "http_proxy",
                "https_proxy",
                "all_proxy",
            ):
                os.environ.pop(key, None)
            # Requests and urllib also consult Windows proxy settings. A wildcard
            # bypass prevents those system settings from being used in Direct mode.
            os.environ["NO_PROXY"] = "*"
            os.environ["no_proxy"] = "*"

    def gdal_options(self) -> dict[str, str]:
        settings = self.validated()
        options: dict[str, str] = {
            "GDAL_HTTP_UNSAFESSL": "YES" if settings.allow_untrusted_gdal_ssl else "NO",
        }
        if settings.mode == PROXY_MODE_AUTO:
            return options
        if settings.mode == PROXY_MODE_DIRECT:
            options.update(
                {
                    "GDAL_HTTP_PROXY": "",
                    "GDAL_HTTPS_PROXY": "",
                    "GDAL_HTTP_PROXYUSERPWD": "",
                    "GDAL_PROXYAUTH": "",
                }
            )
            return options

        parsed = urlsplit(settings.proxy_url)
        hostname = parsed.hostname or ""
        if ":" in hostname and not hostname.startswith("["):
            hostname = f"[{hostname}]"
        proxy_address = hostname + (f":{parsed.port}" if parsed.port else "")
        options.update(
            {
                "GDAL_HTTP_PROXY": proxy_address,
                "GDAL_HTTPS_PROXY": proxy_address,
            }
        )
        if parsed.username is not None:
            username = unquote(parsed.username)
            password = unquote(parsed.password or "")
            options["GDAL_HTTP_PROXYUSERPWD"] = f"{username}:{password}"
            options["GDAL_PROXYAUTH"] = "ANY"
        return options



def create_requests_session(proxy_settings: ProxySettings) -> tuple[requests.Session, dict[str, str] | None]:
    settings = proxy_settings.validated()
    session = requests.Session()
    session.trust_env = settings.mode == PROXY_MODE_AUTO
    proxies = settings.requests_proxies()
    return session, proxies


def is_gdal_certificate_error(error: Exception) -> bool:
    lower = str(error).lower()
    return any(
        token in lower
        for token in (
            "untrusted root",
            "certificate chain",
            "certificate verify failed",
            "unable to get local issuer certificate",
            "self-signed certificate",
            "schannel",
        )
    )


def friendly_network_error(error: Exception, proxy_settings: ProxySettings) -> str:
    text = str(error)
    lower = text.lower()
    if is_gdal_certificate_error(error):
        return (
            "GDAL/Rasterio rejected the HTTPS certificate presented through the network proxy. "
            "Open Network settings and enable ‘GDAL certificate workaround’, then retry. "
            "This disables certificate verification only for GDAL terrain-file requests. "
            "Use it only on a trusted network and with the official CanElevation source.\n\n"
            f"Technical details:\n{text}"
        )
    if "407" in lower or "proxy authentication required" in lower:
        return (
            "The configured/system proxy rejected the connection with HTTP 407. "
            "Open Network settings, select Manual proxy, and use the local Px address "
            f"({DEFAULT_PROXY_URL}) while Px is running.\n\nTechnical details:\n{text}"
        )
    if "proxyerror" in lower or "unable to connect to proxy" in lower:
        return (
            f"Could not connect through {proxy_settings.redacted_display()}. "
            "Check that the proxy application is running and that its address is correct."
            f"\n\nTechnical details:\n{text}"
        )
    return text


class ProxyDialog(tk.Toplevel):
    TEST_URLS = (
        ("CanElevation STAC", STAC_API),
        ("OpenStreetMap tile", "https://a.tile.openstreetmap.org/0/0/0.png"),
    )

    def __init__(self, master: tk.Misc, settings: ProxySettings, apply_callback) -> None:
        super().__init__(master)
        self.title(f"{APP_NAME} — Network settings")
        self.resizable(False, False)
        self.transient(master)
        self.apply_callback = apply_callback
        self.testing = False
        self.test_result_queue: queue.Queue[str] = queue.Queue()

        body = ttk.Frame(self, padding=14)
        body.grid(row=0, column=0, sticky="nsew")
        body.columnconfigure(1, weight=1)

        ttk.Label(body, text="Connection mode").grid(row=0, column=0, sticky="w", padx=(0, 10))
        self.mode_var = tk.StringVar(value=PROXY_MODE_LABELS[settings.mode])
        self.mode_combo = ttk.Combobox(
            body,
            state="readonly",
            width=31,
            textvariable=self.mode_var,
            values=list(PROXY_LABEL_TO_MODE.keys()),
        )
        self.mode_combo.grid(row=0, column=1, sticky="ew")
        self.mode_combo.bind("<<ComboboxSelected>>", self._update_controls)

        ttk.Label(body, text="Proxy URL").grid(row=1, column=0, sticky="w", padx=(0, 10), pady=(10, 0))
        self.url_var = tk.StringVar(value=settings.proxy_url or DEFAULT_PROXY_URL)
        self.url_entry = ttk.Entry(body, width=40, textvariable=self.url_var)
        self.url_entry.grid(row=1, column=1, sticky="ew", pady=(10, 0))

        ttk.Label(
            body,
            text=(
                "For the corporate network, run Px and use http://127.0.0.1:3128. "
                "Outside that network, choose Auto or Direct."
            ),
            wraplength=430,
        ).grid(row=2, column=0, columnspan=2, sticky="ew", pady=(8, 0))

        self.insecure_gdal_ssl_var = tk.BooleanVar(value=settings.allow_untrusted_gdal_ssl)
        ttk.Checkbutton(
            body,
            text="GDAL certificate workaround (skip verification for terrain files)",
            variable=self.insecure_gdal_ssl_var,
        ).grid(row=3, column=0, columnspan=2, sticky="w", pady=(10, 0))
        ttk.Label(
            body,
            text=(
                "Enable this only when Rasterio reports a Schannel/untrusted-root error through "
                "your trusted corporate proxy. API and map requests still use normal verification."
            ),
            wraplength=430,
        ).grid(row=4, column=0, columnspan=2, sticky="ew", pady=(4, 0))

        px_button = ttk.Button(body, text="Use local Px", command=self._use_px)
        px_button.grid(row=5, column=0, sticky="ew", pady=(12, 0), padx=(0, 5))
        self.test_button = ttk.Button(body, text="Test connection", command=self._start_test)
        self.test_button.grid(row=5, column=1, sticky="ew", pady=(12, 0))

        self.status_var = tk.StringVar(value="")
        ttk.Label(body, textvariable=self.status_var, wraplength=430).grid(
            row=6,
            column=0,
            columnspan=2,
            sticky="ew",
            pady=(10, 0),
        )

        buttons = ttk.Frame(body)
        buttons.grid(row=7, column=0, columnspan=2, sticky="e", pady=(14, 0))
        ttk.Button(buttons, text="Apply", command=self._apply).pack(side="left")
        ttk.Button(buttons, text="Close", command=self.destroy).pack(side="left", padx=(8, 0))

        self._update_controls()
        self.protocol("WM_DELETE_WINDOW", self.destroy)
        self.after(10, self._centre_on_parent)
        self.after(100, self._poll_test_result)

    def _centre_on_parent(self) -> None:
        try:
            self.update_idletasks()
            parent = self.master
            x = parent.winfo_rootx() + max(0, (parent.winfo_width() - self.winfo_width()) // 2)
            y = parent.winfo_rooty() + max(0, (parent.winfo_height() - self.winfo_height()) // 2)
            self.geometry(f"+{x}+{y}")
        except Exception:
            pass

    def _settings_from_controls(self) -> ProxySettings:
        mode = PROXY_LABEL_TO_MODE[self.mode_var.get()]
        return ProxySettings(
            mode,
            self.url_var.get(),
            bool(self.insecure_gdal_ssl_var.get()),
        ).validated()

    def _update_controls(self, _event=None) -> None:
        mode = PROXY_LABEL_TO_MODE.get(self.mode_var.get(), PROXY_MODE_AUTO)
        self.url_entry.configure(state="normal" if mode == PROXY_MODE_MANUAL else "disabled")

    def _use_px(self) -> None:
        self.mode_var.set(PROXY_MODE_LABELS[PROXY_MODE_MANUAL])
        self.url_var.set(DEFAULT_PROXY_URL)
        self.insecure_gdal_ssl_var.set(True)
        self._update_controls()

    def _apply(self) -> None:
        try:
            settings = self._settings_from_controls()
            self.apply_callback(settings)
        except ValueError as error:
            messagebox.showerror("Invalid network settings", str(error), parent=self)
            return
        self.status_var.set(f"Applied: {settings.redacted_display()}")

    def _start_test(self) -> None:
        if self.testing:
            return
        try:
            settings = self._settings_from_controls()
        except ValueError as error:
            messagebox.showerror("Invalid network settings", str(error), parent=self)
            return
        self.testing = True
        self.test_button.configure(state="disabled")
        self.status_var.set(f"Testing {settings.redacted_display()}…")
        threading.Thread(target=self._test_worker, args=(settings,), daemon=True).start()

    def _test_worker(self, settings: ProxySettings) -> None:
        session, proxies = create_requests_session(settings)
        lines: list[str] = []
        try:
            session.headers.update({"User-Agent": f"{APP_NAME}/{APP_VERSION}"})
            for label, url in self.TEST_URLS:
                started = time.monotonic()
                response = session.get(url, timeout=(5, 20), proxies=proxies)
                response.raise_for_status()
                elapsed = time.monotonic() - started
                lines.append(f"{label}: OK ({response.status_code}, {elapsed:.1f} s)")
        except Exception as error:
            lines.append(friendly_network_error(error, settings))
        finally:
            session.close()
        self.test_result_queue.put("\n".join(lines))

    def _poll_test_result(self) -> None:
        try:
            result = self.test_result_queue.get_nowait()
        except queue.Empty:
            result = None
        if result is not None:
            self._finish_test(result)
        try:
            self.after(100, self._poll_test_result)
        except tk.TclError:
            pass

    def _finish_test(self, result: str) -> None:
        self.testing = False
        self.test_button.configure(state="normal")
        self.status_var.set(result)


@dataclass(frozen=True)
class DatasetChoice:
    label: str
    collection: str | None
    nominal_resolution_m: float
    preferred_asset: str
    description: str


DATASET_CHOICES: tuple[DatasetChoice, ...] = (
    DatasetChoice(
        "Auto: highest-resolution complete DTM",
        None,
        1.0,
        "dtm",
        "Tests 1 m, then 2 m, then 30 m and selects the first dataset with nearly complete valid coverage.",
    ),
    DatasetChoice(
        "HRDEM Mosaic 1 m — DTM",
        "hrdem-mosaic-1m",
        1.0,
        "dtm",
        "LiDAR-derived 1 m bare-earth terrain mosaic where available.",
    ),
    DatasetChoice(
        "HRDEM Mosaic 2 m — DTM",
        "hrdem-mosaic-2m",
        2.0,
        "dtm",
        "2 m bare-earth terrain where LiDAR-derived DTM coverage exists.",
    ),
    DatasetChoice(
        "MRDEM 30 m — DTM",
        "mrdem-30",
        30.0,
        "dtm",
        "Canada-wide 30 m terrain model fallback when HRDEM coverage is unavailable.",
    ),
)

AUTO_PRIORITY: tuple[DatasetChoice, ...] = DATASET_CHOICES[1:]

TILE_SERVERS: dict[str, tuple[str, int, str]] = {
    "OpenTopoMap": (
        "https://a.tile.opentopomap.org/{z}/{x}/{y}.png",
        17,
        "Map: OpenTopoMap / OpenStreetMap contributors",
    ),
    "OpenStreetMap": (
        "https://a.tile.openstreetmap.org/{z}/{x}/{y}.png",
        19,
        "Map: OpenStreetMap contributors",
    ),
    "Esri World Imagery": (
        "https://server.arcgisonline.com/ArcGIS/rest/services/World_Imagery/MapServer/tile/{z}/{y}/{x}",
        19,
        "Map: Esri World Imagery",
    ),
}


class CancelledError(RuntimeError):
    pass


class QueueLogHandler(logging.Handler):
    def __init__(self, event_queue: queue.Queue[tuple[Any, ...]]) -> None:
        super().__init__()
        self.event_queue = event_queue

    def emit(self, record: logging.LogRecord) -> None:
        try:
            self.event_queue.put(("log", self.format(record)))
        except Exception:
            pass


class LogDialog(tk.Toplevel):
    def __init__(self, master: tk.Misc, lines: list[str]) -> None:
        super().__init__(master)
        self.title(f"{APP_NAME} — Log")
        self.geometry("900x520")
        self.minsize(620, 340)
        self.protocol("WM_DELETE_WINDOW", self.withdraw)

        toolbar = ttk.Frame(self, padding=(8, 8, 8, 4))
        toolbar.pack(fill="x")
        ttk.Button(toolbar, text="Save log…", command=self._save_log).pack(side="left")
        ttk.Button(toolbar, text="Clear", command=self._clear).pack(side="left", padx=(6, 0))
        ttk.Button(toolbar, text="Close", command=self.withdraw).pack(side="right")

        self.text = ScrolledText(self, wrap="none", font=("Consolas", 9))
        self.text.pack(fill="both", expand=True, padx=8, pady=(0, 8))
        self.text.configure(state="normal")
        if lines:
            self.text.insert("end", "\n".join(lines) + "\n")
        self.text.configure(state="disabled")
        self.text.see("end")

    def append(self, line: str) -> None:
        self.text.configure(state="normal")
        self.text.insert("end", line + "\n")
        self.text.configure(state="disabled")
        self.text.see("end")

    def _clear(self) -> None:
        self.text.configure(state="normal")
        self.text.delete("1.0", "end")
        self.text.configure(state="disabled")

    def _save_log(self) -> None:
        path = filedialog.asksaveasfilename(
            parent=self,
            title="Save log",
            defaultextension=".log",
            filetypes=[("Log files", "*.log"), ("Text files", "*.txt"), ("All files", "*.*")],
        )
        if not path:
            return
        Path(path).write_text(self.text.get("1.0", "end-1c"), encoding="utf-8")


class StacClient:
    def __init__(
        self,
        logger: logging.Logger,
        cancel_event: threading.Event,
        proxy_settings: ProxySettings,
    ) -> None:
        self.logger = logger
        self.cancel_event = cancel_event
        self.proxy_settings = proxy_settings.validated()
        self.session, self.proxies = create_requests_session(self.proxy_settings)
        self.session.headers.update(
            {
                "User-Agent": f"{APP_NAME}/{APP_VERSION}",
                "Accept": "application/geo+json, application/json",
            }
        )

    def close(self) -> None:
        self.session.close()

    def search(self, collection: str, bbox: tuple[float, float, float, float]) -> list[dict[str, Any]]:
        self._check_cancelled()
        url = STAC_API.rstrip("/") + "/search"
        params: dict[str, Any] | None = {
            "collections": collection,
            "bbox": ",".join(f"{value:.10f}" for value in bbox),
            "limit": 100,
        }
        features: list[dict[str, Any]] = []
        page = 0

        while url:
            self._check_cancelled()
            page += 1
            self.logger.info("STAC query %s, page %d", collection, page)
            response = self.session.get(
                url,
                params=params,
                timeout=REQUEST_TIMEOUT,
                proxies=self.proxies,
            )
            response.raise_for_status()
            payload = response.json()
            page_features = payload.get("features", [])
            features.extend(page_features)

            next_link = next(
                (link for link in payload.get("links", []) if link.get("rel") == "next"),
                None,
            )
            if not next_link:
                break

            method = str(next_link.get("method", "GET")).upper()
            if method != "GET":
                raise RuntimeError(
                    "The STAC server returned POST pagination, which this exporter does not yet support."
                )
            url = next_link.get("href")
            params = None

        self.logger.info("Found %d STAC item(s) in %s", len(features), collection)
        return features

    def _check_cancelled(self) -> None:
        if self.cancel_event.is_set():
            raise CancelledError("Operation cancelled.")


@dataclass
class DatasetInspection:
    choice: DatasetChoice
    items: list[dict[str, Any]]
    assets: list[tuple[dict[str, Any], str, str]]
    valid_coverage: float
    crs_text: str | None = None
    resolution: tuple[float, float] | None = None


@dataclass
class ExportResult:
    geotiff: Path
    metadata: Path
    normalized_heightmap_tiff: Path | None
    heightmap_preview_16bit: Path | None
    heightmap_preview_8bit: Path | None
    hillshade_preview: Path | None
    collection: str
    valid_coverage: float
    min_elevation: float | None
    max_elevation: float | None
    output_width: int
    output_height: int
    resolution: tuple[float, float]
    crs_text: str


class TerrainExporter:
    def __init__(
        self,
        logger: logging.Logger,
        cancel_event: threading.Event,
        progress_callback,
        proxy_settings: ProxySettings,
    ) -> None:
        self.logger = logger
        self.cancel_event = cancel_event
        self.progress_callback = progress_callback
        self.proxy_settings = proxy_settings.validated()
        self.runtime_allow_untrusted_gdal_ssl = self.proxy_settings.allow_untrusted_gdal_ssl

    def _gdal_options(self) -> dict[str, str]:
        options = self.proxy_settings.gdal_options()
        if self.runtime_allow_untrusted_gdal_ssl:
            options["GDAL_HTTP_UNSAFESSL"] = "YES"
        return options

    def _enable_runtime_certificate_workaround(self, error: Exception) -> bool:
        if self.runtime_allow_untrusted_gdal_ssl or not is_gdal_certificate_error(error):
            return False
        self.runtime_allow_untrusted_gdal_ssl = True
        self.logger.warning(
            "GDAL rejected the proxy certificate (%s). Retrying with GDAL_HTTP_UNSAFESSL=YES. "
            "This affects only GDAL terrain-file requests for the current operation.",
            error,
        )
        return True

    def inspect_choice(
        self,
        stac: StacClient,
        choice: DatasetChoice,
        bbox: tuple[float, float, float, float],
    ) -> DatasetInspection:
        assert choice.collection is not None
        self._check_cancelled()
        items = stac.search(choice.collection, bbox)
        assets = self._collect_assets(items, choice.preferred_asset)
        if not assets:
            self.logger.warning(
                "%s returned no usable %s GeoTIFF asset for this area.",
                choice.collection,
                choice.preferred_asset,
            )
            return DatasetInspection(choice, items, assets, 0.0)

        coverage, crs_text, resolution = self._estimate_valid_coverage(assets, bbox)
        self.logger.info(
            "%s estimated valid coverage: %.2f%% (%d usable asset(s))",
            choice.collection,
            coverage * 100.0,
            len(assets),
        )
        return DatasetInspection(choice, items, assets, coverage, crs_text, resolution)

    def inspect_all(
        self,
        bbox: tuple[float, float, float, float],
    ) -> list[DatasetInspection]:
        results: list[DatasetInspection] = []
        stac = StacClient(self.logger, self.cancel_event, self.proxy_settings)
        try:
            total = len(AUTO_PRIORITY)
            for index, choice in enumerate(AUTO_PRIORITY):
                self._check_cancelled()
                self.progress_callback(
                    5 + int(index / total * 85),
                    f"Inspecting {choice.collection}…",
                )
                results.append(self.inspect_choice(stac, choice, bbox))
            self.progress_callback(100, "Coverage inspection complete.")
            return results
        finally:
            stac.close()

    def export(
        self,
        bbox: tuple[float, float, float, float],
        requested_choice: DatasetChoice,
        output_path: Path,
        create_previews: bool,
        build_overviews: bool,
    ) -> ExportResult:
        output_path = output_path.with_suffix(".tif")
        output_path.parent.mkdir(parents=True, exist_ok=True)
        partial_path = output_path.with_name(output_path.stem + ".partial.tif")
        metadata_path = output_path.with_suffix(".json")
        normalized_tiff_path = output_path.with_name(output_path.stem + "_heightmap_normalized_16bit.tif")
        preview_16bit_path = output_path.with_name(output_path.stem + "_heightmap_preview_16bit.png")
        preview_8bit_path = output_path.with_name(output_path.stem + "_heightmap_preview_8bit.png")
        hillshade_path = output_path.with_name(output_path.stem + "_hillshade_preview.png")

        for stale in (partial_path,):
            if stale.exists():
                stale.unlink()

        stac = StacClient(self.logger, self.cancel_event, self.proxy_settings)
        sources: list[rasterio.io.DatasetReader] = []
        vrts: list[WarpedVRT] = []

        try:
            self.progress_callback(2, "Querying CanElevation STAC…")
            inspection = self._select_dataset(stac, requested_choice, bbox)
            if not inspection.assets:
                raise RuntimeError(
                    f"No usable elevation assets were found in {inspection.choice.collection} for the selected area."
                )

            self.logger.info(
                "Selected collection %s with %.2f%% estimated valid coverage.",
                inspection.choice.collection,
                inspection.valid_coverage * 100.0,
            )
            if inspection.valid_coverage < 0.995:
                self.logger.warning(
                    "The selected dataset does not appear to cover the entire box. The output may contain nodata gaps."
                )

            self.progress_callback(12, "Opening remote Cloud Optimized GeoTIFFs…")
            env_options = {
                "GDAL_DISABLE_READDIR_ON_OPEN": "EMPTY_DIR",
                "CPL_VSIL_CURL_ALLOWED_EXTENSIONS": ".tif,.tiff,.TIF,.TIFF",
                "GDAL_HTTP_MULTIPLEX": "YES",
                "GDAL_HTTP_VERSION": "2",
                "GDAL_HTTP_MAX_RETRY": "4",
                "GDAL_HTTP_RETRY_DELAY": "2",
                "VSI_CACHE": "TRUE",
                "VSI_CACHE_SIZE": str(64 * 1024 * 1024),
                "GDAL_CACHEMAX": 512,
                **self._gdal_options(),
            }

            with rasterio.Env(**env_options):
                for item, asset_key, href in inspection.assets:
                    self._check_cancelled()
                    item_id = str(item.get("id", "<unknown>"))
                    self.logger.info("Opening %s / %s", item_id, asset_key)
                    source = rasterio.open(href)
                    self._validate_elevation_source(source, asset_key, item_id)
                    self.logger.info(
                        "Source raster: dtype=%s, size=%d x %d, resolution=%s, CRS=%s",
                        source.dtypes[0],
                        source.width,
                        source.height,
                        source.res,
                        source.crs,
                    )
                    sources.append(source)

                first = sources[0]

                destination_crs = first.crs
                destination_transform, width, height, resolution = self._create_aligned_grid(
                    first,
                    bbox,
                )
                crs_text = destination_crs.to_string()
                pixel_count = width * height
                raw_gib = pixel_count * 4 / (1024**3)
                self.logger.info(
                    "Output grid: %d × %d pixels, %.3f × %.3f m, %s, %.2f GiB raw float32",
                    width,
                    height,
                    resolution[0],
                    resolution[1],
                    crs_text,
                    raw_gib,
                )

                if pixel_count <= 0:
                    raise RuntimeError("The selected bounds produced an empty output grid.")
                if pixel_count > 1_500_000_000:
                    raise RuntimeError(
                        "The requested output exceeds 1.5 billion pixels. Select a smaller box or a lower-resolution dataset."
                    )

                for source in sources:
                    vrts.append(
                        WarpedVRT(
                            source,
                            crs=destination_crs,
                            transform=destination_transform,
                            width=width,
                            height=height,
                            resampling=Resampling.bilinear,
                            nodata=OUTPUT_NODATA,
                        )
                    )

                profile = {
                    "driver": "GTiff",
                    "width": width,
                    "height": height,
                    "count": 1,
                    "dtype": "float32",
                    "crs": destination_crs,
                    "transform": destination_transform,
                    "nodata": OUTPUT_NODATA,
                    "compress": "DEFLATE",
                    "predictor": 3,
                    "zlevel": 6,
                    "tiled": True,
                    "blockxsize": 512,
                    "blockysize": 512,
                    "BIGTIFF": "IF_SAFER",
                    "interleave": "band",
                }

                windows = list(self._iter_windows(width, height, BLOCK_SIZE))
                total_windows = len(windows)
                valid_pixels = 0
                minimum = math.inf
                maximum = -math.inf

                self.progress_callback(18, "Writing elevation GeoTIFF…")
                with rasterio.open(partial_path, "w", **profile) as destination:
                    destination.update_tags(
                        AREA_OR_POINT="Area",
                        SOURCE="Natural Resources Canada CanElevation",
                        COLLECTION=inspection.choice.collection or "",
                        PRODUCT="DTM" if inspection.choice.preferred_asset == "dtm" else "DEM",
                        SOURCE_ASSET_KEYS=",".join(asset_key for _item, asset_key, _href in inspection.assets),
                        SELECTED_WGS84_BOUNDS=",".join(str(v) for v in bbox),
                    )

                    for index, window in enumerate(windows, start=1):
                        self._check_cancelled()
                        rows = int(window.height)
                        cols = int(window.width)
                        block = np.full((rows, cols), OUTPUT_NODATA, dtype=np.float32)
                        block_valid = np.zeros((rows, cols), dtype=bool)

                        for vrt in vrts:
                            data = vrt.read(
                                1,
                                window=window,
                                out_dtype="float32",
                                masked=True,
                                boundless=False,
                            )
                            array = np.asarray(data.filled(OUTPUT_NODATA), dtype=np.float32)
                            valid = (~np.ma.getmaskarray(data)) & np.isfinite(array) & (array != OUTPUT_NODATA)
                            fill = valid & ~block_valid
                            if np.any(fill):
                                block[fill] = array[fill]
                                block_valid[fill] = True

                        if np.any(block_valid):
                            values = block[block_valid]
                            valid_pixels += int(values.size)
                            minimum = min(minimum, float(values.min()))
                            maximum = max(maximum, float(values.max()))

                        destination.write(block, 1, window=window)

                        percent = 18 + int(index / total_windows * 72)
                        self.progress_callback(
                            percent,
                            f"Writing elevation data: {index:,}/{total_windows:,} blocks",
                        )

                    destination.update_tags(
                        VALID_MIN_ELEVATION_M=("" if not math.isfinite(minimum) else f"{minimum:.6f}"),
                        VALID_MAX_ELEVATION_M=("" if not math.isfinite(maximum) else f"{maximum:.6f}"),
                    )

                    if math.isfinite(minimum) and math.isfinite(maximum) and maximum <= 255.0 and minimum >= 0.0:
                        raise RuntimeError(
                            "The selected source produced only values in the 0..255 display range. "
                            "This indicates a rendered visualization asset rather than real metre-valued "
                            "elevation data, so the invalid export was stopped."
                        )

                self._check_cancelled()
                if build_overviews:
                    self.progress_callback(92, "Building GeoTIFF overviews…")
                    self._build_overviews(partial_path, width, height)

            self._check_cancelled()
            if output_path.exists():
                output_path.unlink()
            partial_path.replace(output_path)

            normalized_tiff_result: Path | None = None
            preview_16bit_result: Path | None = None
            preview_8bit_result: Path | None = None
            hillshade_result: Path | None = None
            if create_previews:
                if not math.isfinite(minimum) or not math.isfinite(maximum):
                    raise RuntimeError("Cannot create normalized heightmaps because no valid elevation range was found.")
                self.progress_callback(95, "Creating display/CAM-friendly 16-bit heightmap TIFF…")
                normalized_tiff_result = self._write_normalized_heightmap_tiff(
                    output_path,
                    normalized_tiff_path,
                    minimum,
                    maximum,
                )
                self.progress_callback(98, "Creating preview images…")
                preview_16bit_result, preview_8bit_result, hillshade_result = self._make_previews(
                    output_path,
                    preview_16bit_path,
                    preview_8bit_path,
                    hillshade_path,
                )

            valid_fraction = valid_pixels / pixel_count if pixel_count else 0.0
            min_value = None if not math.isfinite(minimum) else minimum
            max_value = None if not math.isfinite(maximum) else maximum

            metadata = {
                "application": APP_NAME,
                "application_version": APP_VERSION,
                "created_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
                "source": "Natural Resources Canada CanElevation",
                "stac_api": STAC_API,
                "collection": inspection.choice.collection,
                "requested_product": inspection.choice.preferred_asset,
                "selection_wgs84": {
                    "west": bbox[0],
                    "south": bbox[1],
                    "east": bbox[2],
                    "north": bbox[3],
                },
                "estimated_source_valid_coverage_fraction": inspection.valid_coverage,
                "output_valid_fraction": valid_fraction,
                "output": {
                    "geotiff": output_path.name,
                    "crs": crs_text,
                    "width_pixels": width,
                    "height_pixels": height,
                    "resolution_x": resolution[0],
                    "resolution_y": resolution[1],
                    "nodata": OUTPUT_NODATA,
                    "minimum_elevation_m": min_value,
                    "maximum_elevation_m": max_value,
                    "normalized_heightmap_tiff": normalized_tiff_result.name if normalized_tiff_result else None,
                    "heightmap_preview_16bit": preview_16bit_result.name if preview_16bit_result else None,
                    "heightmap_preview_8bit": preview_8bit_result.name if preview_8bit_result else None,
                    "hillshade_preview": hillshade_result.name if hillshade_result else None,
                    "heightmap_normalization": (
                        "uint16 = round((elevation_m - minimum_elevation_m) / "
                        "(maximum_elevation_m - minimum_elevation_m) * 65535)"
                    ) if normalized_tiff_result else None,
                },
                "source_items": [
                    {
                        "item_id": item.get("id"),
                        "asset_key": asset_key,
                        "href": href,
                    }
                    for item, asset_key, href in inspection.assets
                ],
            }
            metadata_path.write_text(json.dumps(metadata, indent=2), encoding="utf-8")

            self.progress_callback(100, "Export complete.")
            self.logger.info("GeoTIFF written: %s", output_path)
            self.logger.info("Metadata written: %s", metadata_path)
            if normalized_tiff_result:
                self.logger.info("Normalized 16-bit heightmap TIFF written: %s", normalized_tiff_result)
            if preview_16bit_result:
                self.logger.info("16-bit heightmap preview written: %s", preview_16bit_result)
            if preview_8bit_result:
                self.logger.info("8-bit display preview written: %s", preview_8bit_result)
            if hillshade_result:
                self.logger.info("Hillshade preview written: %s", hillshade_result)

            return ExportResult(
                geotiff=output_path,
                metadata=metadata_path,
                normalized_heightmap_tiff=normalized_tiff_result,
                heightmap_preview_16bit=preview_16bit_result,
                heightmap_preview_8bit=preview_8bit_result,
                hillshade_preview=hillshade_result,
                collection=inspection.choice.collection or "",
                valid_coverage=valid_fraction,
                min_elevation=min_value,
                max_elevation=max_value,
                output_width=width,
                output_height=height,
                resolution=resolution,
                crs_text=crs_text,
            )
        except Exception:
            if partial_path.exists():
                try:
                    partial_path.unlink()
                except OSError:
                    pass
            raise
        finally:
            for vrt in vrts:
                try:
                    vrt.close()
                except Exception:
                    pass
            for source in sources:
                try:
                    source.close()
                except Exception:
                    pass
            stac.close()

    def _select_dataset(
        self,
        stac: StacClient,
        requested_choice: DatasetChoice,
        bbox: tuple[float, float, float, float],
    ) -> DatasetInspection:
        if requested_choice.collection is not None:
            return self.inspect_choice(stac, requested_choice, bbox)

        best_partial: DatasetInspection | None = None
        for index, choice in enumerate(AUTO_PRIORITY):
            self._check_cancelled()
            self.progress_callback(
                3 + index * 3,
                f"Testing {choice.collection} coverage…",
            )
            result = self.inspect_choice(stac, choice, bbox)
            if best_partial is None or result.valid_coverage > best_partial.valid_coverage:
                best_partial = result
            if result.valid_coverage >= 0.995:
                return result

        if best_partial and best_partial.assets:
            self.logger.warning(
                "No dataset reached 99.5%% valid coverage. Using %s at %.2f%%.",
                best_partial.choice.collection,
                best_partial.valid_coverage * 100.0,
            )
            return best_partial
        raise RuntimeError("No CanElevation dataset returned usable data for the selected box.")

    def _collect_assets(
        self,
        items: Iterable[dict[str, Any]],
        preferred_asset: str,
    ) -> list[tuple[dict[str, Any], str, str]]:
        collected: list[tuple[dict[str, Any], str, str]] = []
        for item in items:
            assets = item.get("assets", {})
            selection = self._choose_asset(assets, preferred_asset)
            if selection is None:
                available = ", ".join(sorted(assets.keys())) or "<none>"
                self.logger.debug(
                    "Item %s has no suitable %s asset. Available keys: %s",
                    item.get("id", "<unknown>"),
                    preferred_asset,
                    available,
                )
                continue
            key, href = selection
            collected.append((item, key, href))

        # Newest data first where timestamps are available; first valid pixel wins.
        collected.sort(
            key=lambda entry: str(entry[0].get("properties", {}).get("datetime", "")),
            reverse=True,
        )
        return collected

    @staticmethod
    def _choose_asset(
        assets: dict[str, dict[str, Any]],
        preferred_asset: str,
    ) -> tuple[str, str] | None:
        """Choose an actual elevation raster, never a rendered/preview GeoTIFF.

        CanElevation uses the asset key ``dtm`` for the elevation COG in the
        HRDEM *and* MRDEM collections.  Earlier builds requested ``dem`` for
        MRDEM and then used a permissive fallback; that could select a rendered
        8-bit visualization whose values are only 0..255.
        """
        exact = assets.get(preferred_asset)
        if exact is not None:
            href = str(exact.get("href", ""))
            if href.lower().split("?")[0].endswith((".tif", ".tiff")):
                return preferred_asset, href

        preferred_tokens = (
            ("dtm", "terrain", "bare earth", "bare-earth", "mnt")
            if preferred_asset == "dtm"
            else ("dem", "elevation", "mne")
        )
        reject_tokens = (
            "thumbnail",
            "preview",
            "visual",
            "rendered",
            "browse",
            "hillshade",
            "shaded relief",
            "color relief",
            "colour relief",
            "slope",
            "aspect",
            "mask",
            "coverage",
        )

        ranked: list[tuple[int, str, str]] = []
        for key, asset in assets.items():
            href = str(asset.get("href", ""))
            if not href.lower().split("?")[0].endswith((".tif", ".tiff")):
                continue

            roles = [str(role).lower() for role in (asset.get("roles", []) or [])]
            text = " ".join(
                [
                    key,
                    str(asset.get("title", "")),
                    str(asset.get("description", "")),
                    " ".join(roles),
                ]
            ).lower()

            if any(token in text for token in reject_tokens):
                continue
            if any(role in {"thumbnail", "overview", "visual"} for role in roles):
                continue
            if preferred_asset == "dtm" and any(token in text for token in ("dsm", "surface model", "mns")):
                continue

            # Reject explicitly advertised 8-bit rasters.  Elevation COGs may be
            # integer or floating point, but a uint8 asset is almost certainly a
            # display product rather than metre-valued terrain data.
            band_metadata = asset.get("raster:bands", []) or []
            data_types = {
                str(band.get("data_type", "")).lower()
                for band in band_metadata
                if isinstance(band, dict)
            }
            if data_types & {"uint8", "int8", "byte"}:
                continue

            score = 0
            key_lower = key.lower()
            if any(token == key_lower for token in preferred_tokens):
                score += 120
            if any(token in text for token in preferred_tokens):
                score += 50
            if "data" in roles:
                score += 80
            media_type = str(asset.get("type", "")).lower()
            if "cloud-optimized" in media_type or "geotiff" in media_type:
                score += 20
            ranked.append((score, key, href))

        if not ranked:
            return None
        ranked.sort(reverse=True)
        best_score, key, href = ranked[0]
        if best_score < 50:
            return None
        return key, href

    @staticmethod
    def _validate_elevation_source(
        source: rasterio.io.DatasetReader,
        asset_key: str,
        item_id: str,
    ) -> None:
        if source.count < 1:
            raise RuntimeError(f"{item_id} / {asset_key} contains no raster band.")
        dtype = str(source.dtypes[0]).lower()
        if dtype in {"uint8", "int8", "byte"}:
            raise RuntimeError(
                f"{item_id} / {asset_key} is an 8-bit raster ({dtype}), not a metre-valued "
                "elevation COG. Refusing to export a rendered preview as terrain data."
            )
        if source.crs is None:
            raise RuntimeError(f"{item_id} / {asset_key} has no coordinate reference system.")

    def _estimate_valid_coverage(
        self,
        assets: list[tuple[dict[str, Any], str, str]],
        bbox: tuple[float, float, float, float],
    ) -> tuple[float, str | None, tuple[float, float] | None]:
        try:
            return self._estimate_valid_coverage_once(assets, bbox)
        except Exception as error:
            if self._enable_runtime_certificate_workaround(error):
                return self._estimate_valid_coverage_once(assets, bbox)
            raise

    def _estimate_valid_coverage_once(
        self,
        assets: list[tuple[dict[str, Any], str, str]],
        bbox: tuple[float, float, float, float],
    ) -> tuple[float, str | None, tuple[float, float] | None]:
        self._check_cancelled()
        sources: list[rasterio.io.DatasetReader] = []
        vrts: list[WarpedVRT] = []
        env_options = {
            "GDAL_DISABLE_READDIR_ON_OPEN": "EMPTY_DIR",
            "CPL_VSIL_CURL_ALLOWED_EXTENSIONS": ".tif,.tiff,.TIF,.TIFF",
            "GDAL_HTTP_MULTIPLEX": "YES",
            "GDAL_HTTP_VERSION": "2",
            "GDAL_HTTP_MAX_RETRY": "3",
            "GDAL_HTTP_RETRY_DELAY": "2",
            "GDAL_CACHEMAX": 256,
            **self._gdal_options(),
        }
        try:
            with rasterio.Env(**env_options):
                for item, asset_key, href in assets:
                    self._check_cancelled()
                    source = rasterio.open(href)
                    self._validate_elevation_source(
                        source,
                        asset_key,
                        str(item.get("id", "<unknown>")),
                    )
                    sources.append(source)

                first = sources[0]
                projected_bounds = transform_bounds(
                    "EPSG:4326",
                    first.crs,
                    *bbox,
                    densify_pts=21,
                )
                left, bottom, right, top = projected_bounds
                preview_width = COVERAGE_GRID_SIZE
                aspect = max((right - left) / max(top - bottom, 1e-9), 0.05)
                preview_height = max(32, min(1024, int(round(preview_width / aspect))))
                preview_transform = rasterio.transform.from_bounds(
                    left,
                    bottom,
                    right,
                    top,
                    preview_width,
                    preview_height,
                )
                valid_union = np.zeros((preview_height, preview_width), dtype=bool)

                for source in sources:
                    self._check_cancelled()
                    vrt = WarpedVRT(
                        source,
                        crs=first.crs,
                        transform=preview_transform,
                        width=preview_width,
                        height=preview_height,
                        resampling=Resampling.nearest,
                        nodata=OUTPUT_NODATA,
                    )
                    vrts.append(vrt)
                    data = vrt.read(1, masked=True, out_dtype="float32")
                    array = np.asarray(data.filled(OUTPUT_NODATA), dtype=np.float32)
                    valid = (~np.ma.getmaskarray(data)) & np.isfinite(array) & (array != OUTPUT_NODATA)
                    valid_union |= valid

                return (
                    float(valid_union.mean()),
                    first.crs.to_string(),
                    (abs(float(first.res[0])), abs(float(first.res[1]))),
                )
        finally:
            for vrt in vrts:
                try:
                    vrt.close()
                except Exception:
                    pass
            for source in sources:
                try:
                    source.close()
                except Exception:
                    pass

    @staticmethod
    def _create_aligned_grid(
        source: rasterio.io.DatasetReader,
        bbox: tuple[float, float, float, float],
    ) -> tuple[Any, int, int, tuple[float, float]]:
        assert source.crs is not None
        left, bottom, right, top = transform_bounds(
            "EPSG:4326",
            source.crs,
            *bbox,
            densify_pts=21,
        )
        res_x = abs(float(source.res[0]))
        res_y = abs(float(source.res[1]))
        origin_x = float(source.transform.c)
        origin_y = float(source.transform.f)

        aligned_left = origin_x + math.floor((left - origin_x) / res_x) * res_x
        aligned_right = origin_x + math.ceil((right - origin_x) / res_x) * res_x
        aligned_bottom = origin_y + math.floor((bottom - origin_y) / res_y) * res_y
        aligned_top = origin_y + math.ceil((top - origin_y) / res_y) * res_y

        width = int(round((aligned_right - aligned_left) / res_x))
        height = int(round((aligned_top - aligned_bottom) / res_y))
        transform = from_origin(aligned_left, aligned_top, res_x, res_y)
        return transform, width, height, (res_x, res_y)

    @staticmethod
    def _iter_windows(width: int, height: int, block_size: int) -> Iterable[Window]:
        for row_off in range(0, height, block_size):
            rows = min(block_size, height - row_off)
            for col_off in range(0, width, block_size):
                cols = min(block_size, width - col_off)
                yield Window(col_off, row_off, cols, rows)

    def _build_overviews(self, path: Path, width: int, height: int) -> None:
        factors = [factor for factor in (2, 4, 8, 16, 32) if min(width, height) / factor >= 256]
        if not factors:
            self.logger.info("Output is small enough that internal overviews are unnecessary.")
            return
        with rasterio.open(path, "r+") as dataset:
            dataset.build_overviews(factors, Resampling.average)
            dataset.update_tags(ns="rio_overview", resampling="average")
        self.logger.info("Built internal overviews: %s", factors)

    def _write_normalized_heightmap_tiff(
        self,
        geotiff_path: Path,
        heightmap_path: Path,
        minimum: float,
        maximum: float,
    ) -> Path:
        span = maximum - minimum
        if span <= 0:
            raise RuntimeError("Cannot normalize a zero-range elevation raster.")

        with rasterio.open(geotiff_path) as source:
            profile = source.profile.copy()
            profile.update(
                dtype="uint16",
                nodata=None,
                compress="deflate",
                predictor=2,
                BIGTIFF="IF_SAFER",
            )
            if heightmap_path.exists():
                heightmap_path.unlink()
            with rasterio.open(heightmap_path, "w", **profile) as destination:
                destination.update_tags(
                    SOURCE_ELEVATION_FILE=geotiff_path.name,
                    ORIGINAL_MIN_ELEVATION_M=f"{minimum:.9f}",
                    ORIGINAL_MAX_ELEVATION_M=f"{maximum:.9f}",
                    ELEVATION_UNITS="metre",
                    NORMALIZATION=(
                        "uint16 = round((elevation_m - min_m) / "
                        "(max_m - min_m) * 65535)"
                    ),
                    PURPOSE="Display/CAM heightmap; float32 GeoTIFF remains the metre-valued master",
                )
                for _, window in source.block_windows(1):
                    self._check_cancelled()
                    data = source.read(1, window=window, masked=True)
                    mask = np.ma.getmaskarray(data)
                    array = np.asarray(data.filled(np.nan), dtype=np.float32)
                    valid = (~mask) & np.isfinite(array)
                    normalized = np.zeros(array.shape, dtype=np.uint16)
                    if np.any(valid):
                        normalized_float = np.clip((array[valid] - minimum) / span, 0.0, 1.0)
                        normalized[valid] = np.round(normalized_float * 65535.0).astype(np.uint16)
                    destination.write(normalized, 1, window=window)
                    destination.write_mask(valid.astype(np.uint8) * 255, window=window)
        return heightmap_path

    def _make_previews(
        self,
        geotiff_path: Path,
        heightmap_16bit_path: Path,
        heightmap_8bit_path: Path,
        hillshade_path: Path,
        max_dimension: int = 1800,
    ) -> tuple[Path | None, Path | None, Path | None]:
        with rasterio.open(geotiff_path) as source:
            scale = min(max_dimension / source.width, max_dimension / source.height, 1.0)
            width = max(1, int(round(source.width * scale)))
            height = max(1, int(round(source.height * scale)))
            data = source.read(
                1,
                out_shape=(height, width),
                masked=True,
                resampling=Resampling.bilinear,
                out_dtype="float32",
            )

        mask = np.ma.getmaskarray(data)
        array = np.asarray(data.filled(np.nan), dtype=np.float32)
        valid = (~mask) & np.isfinite(array)
        if not np.any(valid):
            self.logger.warning("No valid pixels were available for preview generation.")
            return None, None, None

        minimum = float(array[valid].min())
        maximum = float(array[valid].max())
        span = maximum - minimum
        if span <= 0:
            normalized = np.zeros(array.shape, dtype=np.uint16)
        else:
            normalized_float = np.clip((array - minimum) / span, 0.0, 1.0)
            normalized = np.round(normalized_float * 65535.0).astype(np.uint16)
        normalized[~valid] = 0
        Image.fromarray(normalized, mode="I;16").save(heightmap_16bit_path)
        display_8bit = np.round(normalized.astype(np.float32) / 257.0).astype(np.uint8)
        display_8bit[~valid] = 0
        Image.fromarray(display_8bit, mode="L").save(heightmap_8bit_path)

        # A visual-only hillshade preview; the source GeoTIFF remains the accurate elevation master.
        filled = array.copy()
        filled[~valid] = minimum
        gradient_y, gradient_x = np.gradient(filled)
        slope = np.pi / 2.0 - np.arctan(np.sqrt(gradient_x**2 + gradient_y**2))
        aspect = np.arctan2(-gradient_x, gradient_y)
        azimuth = np.deg2rad(315.0)
        altitude = np.deg2rad(45.0)
        shaded = (
            np.sin(altitude) * np.sin(slope)
            + np.cos(altitude) * np.cos(slope) * np.cos(azimuth - aspect)
        )
        shaded = np.clip((shaded + 1.0) * 127.5, 0, 255).astype(np.uint8)
        shaded[~valid] = 0
        Image.fromarray(shaded, mode="L").save(hillshade_path)
        return heightmap_16bit_path, heightmap_8bit_path, hillshade_path

    def _check_cancelled(self) -> None:
        if self.cancel_event.is_set():
            raise CancelledError("Operation cancelled.")


class App:
    def __init__(self, root: tk.Tk) -> None:
        self.root = root
        self.root.title(f"{APP_NAME} {APP_VERSION}")
        self.root.geometry("1380x850")
        self.root.minsize(1100, 700)
        self.root.protocol("WM_DELETE_WINDOW", self._on_close)

        self.event_queue: queue.Queue[tuple[Any, ...]] = queue.Queue()
        self.cancel_event = threading.Event()
        self.worker_thread: threading.Thread | None = None
        self.log_lines: list[str] = []
        self.log_dialog: LogDialog | None = None
        self.selection_polygon = None
        self.selection_handles: dict[str, Any] = {}
        self.selection_handle_icon: ImageTk.PhotoImage | None = None
        self.drag_corner: str | None = None
        self.drag_has_moved = False
        self.corner_markers: list[Any] = []
        self.draw_mode = False
        self.first_corner: tuple[float, float] | None = None
        self.last_result: ExportResult | None = None
        self.proxy_dialog: ProxyDialog | None = None
        self.original_proxy_environment = {key: os.environ.get(key) for key in PROXY_ENV_KEYS}

        # Initialize variables used by UI callbacks before building any widgets.
        # This keeps startup safe even if a callback is invoked during widget setup.
        self.attribution_var = tk.StringVar(
            master=self.root,
            value=TILE_SERVERS["OpenTopoMap"][2],
        )

        self.logger = logging.getLogger("canelevation_exporter")
        self.logger.setLevel(logging.DEBUG)
        self.logger.handlers.clear()
        handler = QueueLogHandler(self.event_queue)
        handler.setFormatter(logging.Formatter("%(asctime)s  %(levelname)-7s  %(message)s", "%H:%M:%S"))
        self.logger.addHandler(handler)
        self.logger.propagate = False

        self.proxy_settings = self._detect_startup_proxy_settings()
        self.proxy_settings.apply_process_environment(self.original_proxy_environment)

        self._build_ui()
        self._set_default_bounds()
        self.root.after(100, self._process_events)
        self.logger.info("%s %s started", APP_NAME, APP_VERSION)
        self.logger.info("Network mode: %s", self.proxy_settings.redacted_display())

    def _build_ui(self) -> None:
        self.root.columnconfigure(0, weight=0)
        self.root.columnconfigure(1, weight=1)
        self.root.rowconfigure(0, weight=1)

        controls = ttk.Frame(self.root, padding=12)
        controls.grid(row=0, column=0, sticky="nsew")
        controls.columnconfigure(0, weight=1)

        map_frame = ttk.Frame(self.root, padding=(0, 12, 12, 12))
        self.map_frame = map_frame
        map_frame.grid(row=0, column=1, sticky="nsew")
        map_frame.columnconfigure(0, weight=1)
        map_frame.rowconfigure(1, weight=1)

        heading = ttk.Label(controls, text="CanElevation terrain export", font=("Segoe UI", 15, "bold"))
        heading.grid(row=0, column=0, sticky="w")
        ttk.Label(
            controls,
            text="Draw a box on the map or enter WGS84 longitude/latitude corners.",
            wraplength=335,
        ).grid(row=1, column=0, sticky="ew", pady=(2, 10))

        bounds_group = ttk.LabelFrame(controls, text="Selection bounds (WGS84)", padding=10)
        bounds_group.grid(row=2, column=0, sticky="ew")
        for column in (1, 3):
            bounds_group.columnconfigure(column, weight=1)

        self.west_var = tk.StringVar()
        self.south_var = tk.StringVar()
        self.east_var = tk.StringVar()
        self.north_var = tk.StringVar()
        entries = (
            ("West", self.west_var, 0, 0),
            ("North", self.north_var, 0, 2),
            ("East", self.east_var, 1, 0),
            ("South", self.south_var, 1, 2),
        )
        for label, variable, row, column in entries:
            ttk.Label(bounds_group, text=label).grid(row=row, column=column, sticky="w", padx=(0, 5), pady=3)
            entry = ttk.Entry(bounds_group, textvariable=variable, width=14)
            entry.grid(row=row, column=column + 1, sticky="ew", pady=3)
            entry.bind("<Return>", lambda _event: self._apply_coordinate_entries())
            entry.bind("<FocusOut>", lambda _event: self._update_size_estimate())

        bounds_buttons = ttk.Frame(bounds_group)
        bounds_buttons.grid(row=2, column=0, columnspan=4, sticky="ew", pady=(8, 0))
        for column in (0, 1):
            bounds_buttons.columnconfigure(column, weight=1)
        self.draw_button = ttk.Button(
            bounds_buttons,
            text="Draw box — click 2 corners",
            command=self._begin_draw_box,
        )
        self.draw_button.grid(row=0, column=0, sticky="ew", padx=(0, 4))
        ttk.Button(
            bounds_buttons,
            text="Apply coordinates",
            command=self._apply_coordinate_entries,
        ).grid(row=0, column=1, sticky="ew", padx=(4, 0))
        ttk.Button(
            bounds_buttons,
            text="Fit map to selection",
            command=self._fit_selection,
        ).grid(row=1, column=0, sticky="ew", padx=(0, 4), pady=(6, 0))
        ttk.Button(
            bounds_buttons,
            text="Clear selection",
            command=self._clear_selection,
        ).grid(row=1, column=1, sticky="ew", padx=(4, 0), pady=(6, 0))

        self.size_var = tk.StringVar(value="")
        ttk.Label(bounds_group, textvariable=self.size_var, wraplength=320).grid(
            row=3,
            column=0,
            columnspan=4,
            sticky="ew",
            pady=(8, 0),
        )

        data_group = ttk.LabelFrame(controls, text="Elevation dataset", padding=10)
        data_group.grid(row=3, column=0, sticky="ew", pady=(10, 0))
        data_group.columnconfigure(0, weight=1)
        self.dataset_var = tk.StringVar(value=DATASET_CHOICES[0].label)
        self.dataset_combo = ttk.Combobox(
            data_group,
            state="readonly",
            textvariable=self.dataset_var,
            values=[choice.label for choice in DATASET_CHOICES],
        )
        self.dataset_combo.grid(row=0, column=0, sticky="ew")
        self.dataset_combo.bind("<<ComboboxSelected>>", self._on_dataset_changed)
        self.dataset_description_var = tk.StringVar(value=DATASET_CHOICES[0].description)
        ttk.Label(
            data_group,
            textvariable=self.dataset_description_var,
            wraplength=320,
        ).grid(row=1, column=0, sticky="ew", pady=(6, 0))
        self.inspect_button = ttk.Button(
            data_group,
            text="Inspect coverage for this box",
            command=self._start_inspection,
        )
        self.inspect_button.grid(row=2, column=0, sticky="ew", pady=(8, 0))

        output_group = ttk.LabelFrame(controls, text="Output", padding=10)
        output_group.grid(row=4, column=0, sticky="ew", pady=(10, 0))
        output_group.columnconfigure(0, weight=1)

        self.output_folder_var = tk.StringVar(value=str(Path.home() / "Downloads"))
        folder_row = ttk.Frame(output_group)
        folder_row.grid(row=0, column=0, sticky="ew")
        folder_row.columnconfigure(0, weight=1)
        ttk.Entry(folder_row, textvariable=self.output_folder_var).grid(row=0, column=0, sticky="ew")
        ttk.Button(folder_row, text="Browse…", command=self._browse_output).grid(row=0, column=1, padx=(6, 0))

        ttk.Label(output_group, text="Base filename").grid(row=1, column=0, sticky="w", pady=(8, 2))
        self.filename_var = tk.StringVar(value=DEFAULT_FILENAME)
        ttk.Entry(output_group, textvariable=self.filename_var).grid(row=2, column=0, sticky="ew")

        self.preview_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(
            output_group,
            text="Create normalized 16-bit heightmap TIFF and previews",
            variable=self.preview_var,
        ).grid(row=3, column=0, sticky="w", pady=(8, 0))
        self.overview_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(
            output_group,
            text="Build internal GeoTIFF overviews",
            variable=self.overview_var,
        ).grid(row=4, column=0, sticky="w", pady=(4, 0))

        action_group = ttk.LabelFrame(controls, text="Export progress", padding=10)
        action_group.grid(row=5, column=0, sticky="ew", pady=(10, 0))
        action_group.columnconfigure(0, weight=1)
        self.progress_var = tk.DoubleVar(value=0)
        self.progress_bar = ttk.Progressbar(
            action_group,
            variable=self.progress_var,
            maximum=100,
            mode="determinate",
        )
        self.progress_bar.grid(row=0, column=0, columnspan=2, sticky="ew")
        self.status_var = tk.StringVar(value="Ready.")
        ttk.Label(action_group, textvariable=self.status_var, wraplength=320).grid(
            row=1,
            column=0,
            columnspan=2,
            sticky="ew",
            pady=(6, 8),
        )

        self.export_button = ttk.Button(
            action_group,
            text="Export selected terrain",
            command=self._start_export,
        )
        self.export_button.grid(row=2, column=0, sticky="ew", padx=(0, 4))
        self.cancel_button = ttk.Button(
            action_group,
            text="Cancel",
            command=self._cancel_worker,
            state="disabled",
        )
        self.cancel_button.grid(row=2, column=1, sticky="ew", padx=(4, 0))
        for column in (0, 1):
            action_group.columnconfigure(column, weight=1)

        utility_row = ttk.Frame(controls)
        utility_row.grid(row=6, column=0, sticky="ew", pady=(10, 0))
        for column in (0, 1):
            utility_row.columnconfigure(column, weight=1)
        ttk.Button(utility_row, text="Show log", command=self._show_log).grid(
            row=0, column=0, sticky="ew", padx=(0, 4)
        )
        self.open_folder_button = ttk.Button(
            utility_row,
            text="Open output folder",
            command=self._open_output_folder,
        )
        self.open_folder_button.grid(row=0, column=1, sticky="ew", padx=(4, 0))

        ttk.Label(
            controls,
            text="The GeoTIFF is the accurate elevation master. Preview PNGs are visualization copies only.",
            wraplength=335,
        ).grid(row=7, column=0, sticky="ew", pady=(10, 0))

        map_toolbar = ttk.Frame(map_frame)
        map_toolbar.grid(row=0, column=0, sticky="ew", pady=(0, 6))
        ttk.Label(map_toolbar, text="Map style:").pack(side="left")
        self.tile_server_var = tk.StringVar(value="OpenTopoMap")
        tile_combo = ttk.Combobox(
            map_toolbar,
            state="readonly",
            width=22,
            textvariable=self.tile_server_var,
            values=list(TILE_SERVERS.keys()),
        )
        tile_combo.pack(side="left", padx=(6, 0))
        tile_combo.bind("<<ComboboxSelected>>", self._change_tile_server)
        self.map_instruction_var = tk.StringVar(value="Pan/zoom normally, or drag a red corner handle to resize the box.")
        ttk.Label(map_toolbar, textvariable=self.map_instruction_var).pack(side="left", padx=(14, 0))
        ttk.Button(map_toolbar, text="Network…", command=self._show_proxy_settings).pack(side="right")
        self.network_status_var = tk.StringVar(value=self.proxy_settings.redacted_display())
        ttk.Label(map_toolbar, textvariable=self.network_status_var).pack(side="right", padx=(8, 10))

        self._create_map_widget(DEFAULT_CENTER, 11)

        ttk.Label(map_frame, textvariable=self.attribution_var, anchor="e").grid(
            row=2,
            column=0,
            sticky="ew",
            pady=(4, 0),
        )

    def _detect_startup_proxy_settings(self) -> ProxySettings:
        # Prefer a running local Px instance. Otherwise leave the existing system
        # proxy configuration untouched.
        try:
            with socket.create_connection(("127.0.0.1", 3128), timeout=0.20):
                return ProxySettings(PROXY_MODE_MANUAL, DEFAULT_PROXY_URL, True)
        except OSError:
            return ProxySettings(PROXY_MODE_AUTO, "")

    def _create_map_widget(
        self,
        position: tuple[float, float] = DEFAULT_CENTER,
        zoom: int = 11,
    ) -> None:
        self.map_widget = TkinterMapView(self.map_frame, corner_radius=0)
        self.map_widget.grid(row=1, column=0, sticky="nsew")
        self.map_widget.set_position(*position)
        self.map_widget.set_zoom(int(zoom))
        self.map_widget.add_left_click_map_command(self._map_left_click)
        self._install_map_canvas_bindings()
        self._change_tile_server()

    def _show_proxy_settings(self) -> None:
        if self.proxy_dialog is not None and self.proxy_dialog.winfo_exists():
            self.proxy_dialog.deiconify()
            self.proxy_dialog.lift()
            self.proxy_dialog.focus_force()
            return
        self.proxy_dialog = ProxyDialog(self.root, self.proxy_settings, self._apply_proxy_settings)

    def _apply_proxy_settings(self, settings: ProxySettings) -> None:
        if self._worker_running():
            raise ValueError("Wait for the current inspection/export to finish before changing network settings.")
        settings = settings.validated()
        settings.apply_process_environment(self.original_proxy_environment)
        self.proxy_settings = settings
        if hasattr(self, "network_status_var"):
            self.network_status_var.set(settings.redacted_display())
        self.logger.info("Network mode changed to %s", settings.redacted_display())
        self._reload_map_for_network_change()

    def _reload_map_for_network_change(self) -> None:
        map_widget = getattr(self, "map_widget", None)
        position = DEFAULT_CENTER
        zoom = 11
        if map_widget is not None:
            try:
                position = tuple(map_widget.get_position())  # type: ignore[assignment]
            except Exception:
                pass
            try:
                zoom = int(getattr(map_widget, "zoom", zoom))
            except (TypeError, ValueError):
                pass
            try:
                map_widget.destroy()
            except Exception:
                pass

        self.selection_polygon = None
        self.selection_handles.clear()
        self.drag_corner = None
        self.corner_markers.clear()
        self._create_map_widget(position, zoom)
        try:
            bounds = self._read_bounds()
        except ValueError:
            return
        self._draw_selection(bounds)
        self.logger.info("Map tile widget reloaded with the new network settings.")

    def _set_default_bounds(self) -> None:
        self._write_bounds_to_entries(DEFAULT_BOUNDS)
        self._draw_selection(DEFAULT_BOUNDS)
        self._fit_selection()
        self._update_size_estimate()

    def _change_tile_server(self, _event=None) -> None:
        # Be defensive here because Tk callbacks can occasionally fire while the
        # surrounding UI is still being constructed.
        tile_server_var = getattr(self, "tile_server_var", None)
        name = tile_server_var.get() if tile_server_var is not None else "OpenTopoMap"
        url, max_zoom, attribution = TILE_SERVERS.get(
            name,
            TILE_SERVERS["OpenTopoMap"],
        )

        map_widget = getattr(self, "map_widget", None)
        if map_widget is not None:
            map_widget.set_tile_server(url, max_zoom=max_zoom)

        attribution_var = getattr(self, "attribution_var", None)
        if attribution_var is None:
            self.attribution_var = tk.StringVar(
                master=self.root,
                value=attribution,
            )
        else:
            attribution_var.set(attribution)

    def _begin_draw_box(self) -> None:
        if self._worker_running():
            return
        self.draw_mode = True
        self.first_corner = None
        self.drag_corner = None
        self._delete_selection_handles()
        self._delete_corner_markers()
        self.draw_button.configure(text="Cancel box drawing")
        self.draw_button.configure(command=self._cancel_draw_box)
        self.map_instruction_var.set("Click the first corner of the export box.")
        self.status_var.set("Box drawing active: click the first corner.")

    def _cancel_draw_box(self) -> None:
        self.draw_mode = False
        self.first_corner = None
        self._delete_corner_markers()
        self.draw_button.configure(text="Draw box — click 2 corners", command=self._begin_draw_box)
        self.map_instruction_var.set("Pan/zoom normally, or drag a red corner handle to resize the box.")
        try:
            self._draw_selection_handles(self._read_bounds())
        except ValueError:
            pass
        self.status_var.set("Box drawing cancelled.")

    def _map_left_click(self, coordinates: tuple[float, float]) -> None:
        if not self.draw_mode:
            return
        lat, lon = coordinates
        if self.first_corner is None:
            self.first_corner = (lat, lon)
            self.corner_markers.append(self.map_widget.set_marker(lat, lon, text="Corner 1"))
            self.map_instruction_var.set("Click the opposite corner of the export box.")
            self.status_var.set("First corner set. Click the opposite corner.")
            return

        first_lat, first_lon = self.first_corner
        west = min(first_lon, lon)
        east = max(first_lon, lon)
        south = min(first_lat, lat)
        north = max(first_lat, lat)
        bounds = (west, south, east, north)
        self.corner_markers.append(self.map_widget.set_marker(lat, lon, text="Corner 2"))
        self._write_bounds_to_entries(bounds)
        self._draw_selection(bounds)
        self._cancel_draw_box()
        self._update_size_estimate()
        self.status_var.set("Selection updated from map clicks.")

    def _apply_coordinate_entries(self) -> None:
        try:
            bounds = self._read_bounds()
        except ValueError as error:
            messagebox.showerror("Invalid coordinates", str(error), parent=self.root)
            return
        self._draw_selection(bounds)
        self._fit_selection()
        self._update_size_estimate()
        self.status_var.set("Selection updated from coordinate entries.")

    def _draw_selection(self, bounds: tuple[float, float, float, float]) -> None:
        west, south, east, north = bounds
        if self.selection_polygon is not None:
            try:
                self.selection_polygon.delete()
            except Exception:
                pass
            self.selection_polygon = None
        self.selection_polygon = self.map_widget.set_polygon(
            [
                (north, west),
                (north, east),
                (south, east),
                (south, west),
            ],
            fill_color=None,
            outline_color="#e03030",
            border_width=4,
            name="export_bounds",
        )
        self._draw_selection_handles(bounds)

    def _make_selection_handle_icon(self) -> ImageTk.PhotoImage:
        image = Image.new("RGBA", (22, 22), (0, 0, 0, 0))
        draw = ImageDraw.Draw(image)
        draw.rectangle((2, 2, 19, 19), fill=(255, 255, 255, 245), outline=(80, 20, 20, 255), width=1)
        draw.rectangle((3, 3, 18, 18), outline=(224, 48, 48, 255), width=3)
        draw.rectangle((8, 8, 13, 13), fill=(224, 48, 48, 255))
        return ImageTk.PhotoImage(image, master=self.root)

    def _draw_selection_handles(self, bounds: tuple[float, float, float, float]) -> None:
        if self.draw_mode:
            return

        if self.selection_handle_icon is None:
            self.selection_handle_icon = self._make_selection_handle_icon()

        west, south, east, north = bounds
        positions = {
            "nw": (north, west),
            "ne": (north, east),
            "se": (south, east),
            "sw": (south, west),
        }

        for corner, (latitude, longitude) in positions.items():
            marker = self.selection_handles.get(corner)
            if marker is None or getattr(marker, "deleted", False):
                marker = self.map_widget.set_marker(
                    latitude,
                    longitude,
                    icon=self.selection_handle_icon,
                    icon_anchor="center",
                    command=lambda _marker, selected_corner=corner: self._activate_corner_drag(selected_corner),
                    data={"selection_corner": corner},
                )
                self.selection_handles[corner] = marker
            else:
                marker.set_position(latitude, longitude)

    def _delete_selection_handles(self) -> None:
        for marker in self.selection_handles.values():
            try:
                marker.delete()
            except Exception:
                pass
        self.selection_handles.clear()
        self.drag_corner = None
        map_widget = getattr(self, "map_widget", None)
        if map_widget is not None:
            try:
                map_widget.canvas.configure(cursor="arrow")
            except Exception:
                pass

    def _activate_corner_drag(self, corner: str) -> None:
        if self.draw_mode or self._worker_running():
            return
        self.drag_corner = corner
        self.drag_has_moved = False
        self.map_widget.fading_possible = False
        self.map_widget.move_velocity = (0, 0)
        self.map_widget.canvas.configure(cursor="fleur")
        self.map_instruction_var.set("Drag the selected corner; release to finish resizing.")
        self.status_var.set(f"Dragging {corner.upper()} selection corner…")

    def _install_map_canvas_bindings(self) -> None:
        # TkinterMapView normally owns these bindings for map panning. Route them
        # through the app so a selection handle can temporarily consume the drag
        # while normal clicks and map panning continue to behave as before.
        canvas = self.map_widget.canvas
        canvas.bind("<Button-1>", self._map_canvas_press)
        canvas.bind("<B1-Motion>", self._map_canvas_drag)
        canvas.bind("<ButtonRelease-1>", self._map_canvas_release)

    def _map_canvas_press(self, event: tk.Event) -> str | None:
        if self.drag_corner is not None:
            self.map_widget.fading_possible = False
            self.map_widget.move_velocity = (0, 0)
            return "break"
        self.map_widget.mouse_click(event)
        return None

    def _map_canvas_drag(self, event: tk.Event) -> str | None:
        if self.drag_corner is None:
            self.map_widget.mouse_move(event)
            return None

        latitude, longitude = self.map_widget.convert_canvas_coords_to_decimal_coords(event.x, event.y)
        try:
            current_bounds = self._read_bounds()
        except ValueError:
            return "break"

        bounds = self._bounds_with_dragged_corner(
            current_bounds,
            self.drag_corner,
            float(latitude),
            float(longitude),
        )
        self._write_bounds_to_entries(bounds)
        self._draw_selection(bounds)
        self._update_size_estimate()
        self.drag_has_moved = True
        return "break"

    def _map_canvas_release(self, event: tk.Event) -> str | None:
        if self.drag_corner is None:
            self.map_widget.mouse_release(event)
            return None

        corner = self.drag_corner
        self.drag_corner = None
        self.map_widget.fading_possible = True
        self.map_widget.move_velocity = (0, 0)
        self.map_widget.canvas.configure(cursor="arrow")
        self.map_instruction_var.set("Pan/zoom normally, or drag a red corner handle to resize the box.")
        self._update_size_estimate()
        if self.drag_has_moved:
            self.status_var.set(f"Selection resized from the {corner.upper()} corner.")
        else:
            self.status_var.set("Selection corner unchanged.")
        self.drag_has_moved = False
        return "break"

    @staticmethod
    def _bounds_with_dragged_corner(
        bounds: tuple[float, float, float, float],
        corner: str,
        latitude: float,
        longitude: float,
    ) -> tuple[float, float, float, float]:
        west, south, east, north = bounds
        latitude = max(-85.0, min(85.0, latitude))
        longitude = max(-180.0, min(180.0, longitude))
        minimum_gap = 1e-7

        if corner == "nw":
            west = min(longitude, east - minimum_gap)
            north = max(latitude, south + minimum_gap)
        elif corner == "ne":
            east = max(longitude, west + minimum_gap)
            north = max(latitude, south + minimum_gap)
        elif corner == "se":
            east = max(longitude, west + minimum_gap)
            south = min(latitude, north - minimum_gap)
        elif corner == "sw":
            west = min(longitude, east - minimum_gap)
            south = min(latitude, north - minimum_gap)
        else:
            raise ValueError(f"Unknown selection corner: {corner}")

        return west, south, east, north

    def _fit_selection(self) -> None:
        try:
            west, south, east, north = self._read_bounds()
        except ValueError:
            return
        self.map_widget.fit_bounding_box((north, west), (south, east))

    def _clear_selection(self) -> None:
        if self.selection_polygon is not None:
            try:
                self.selection_polygon.delete()
            except Exception:
                pass
            self.selection_polygon = None
        self._delete_selection_handles()
        self._delete_corner_markers()
        for variable in (self.west_var, self.south_var, self.east_var, self.north_var):
            variable.set("")
        self.size_var.set("")
        self.status_var.set("Selection cleared.")

    def _delete_corner_markers(self) -> None:
        for marker in self.corner_markers:
            try:
                marker.delete()
            except Exception:
                pass
        self.corner_markers.clear()

    def _write_bounds_to_entries(self, bounds: tuple[float, float, float, float]) -> None:
        west, south, east, north = bounds
        self.west_var.set(f"{west:.8f}")
        self.south_var.set(f"{south:.8f}")
        self.east_var.set(f"{east:.8f}")
        self.north_var.set(f"{north:.8f}")

    def _read_bounds(self) -> tuple[float, float, float, float]:
        try:
            west = float(self.west_var.get().strip())
            south = float(self.south_var.get().strip())
            east = float(self.east_var.get().strip())
            north = float(self.north_var.get().strip())
        except ValueError as error:
            raise ValueError("All four bounds must be decimal numbers.") from error

        values = (west, south, east, north)
        if not all(math.isfinite(value) for value in values):
            raise ValueError("Coordinates must be finite numbers.")
        if not (-180 <= west <= 180 and -180 <= east <= 180):
            raise ValueError("West/east longitude must be between -180 and 180.")
        if not (-90 <= south <= 90 and -90 <= north <= 90):
            raise ValueError("South/north latitude must be between -90 and 90.")
        if west >= east:
            raise ValueError("West longitude must be smaller than east longitude.")
        if south >= north:
            raise ValueError("South latitude must be smaller than north latitude.")
        return values

    def _selected_choice(self) -> DatasetChoice:
        label = self.dataset_var.get()
        return next(choice for choice in DATASET_CHOICES if choice.label == label)

    def _on_dataset_changed(self, _event=None) -> None:
        choice = self._selected_choice()
        self.dataset_description_var.set(choice.description)
        self._update_size_estimate()

    def _update_size_estimate(self) -> None:
        try:
            west, south, east, north = self._read_bounds()
        except ValueError:
            self.size_var.set("")
            return
        geod = Geod(ellps="WGS84")
        mid_lat = (south + north) / 2.0
        mid_lon = (west + east) / 2.0
        _, _, width_m = geod.inv(west, mid_lat, east, mid_lat)
        _, _, height_m = geod.inv(mid_lon, south, mid_lon, north)
        choice = self._selected_choice()
        resolution = choice.nominal_resolution_m
        pixels = max(0, int(width_m / resolution) * int(height_m / resolution))
        raw_gib = pixels * 4 / (1024**3)
        prefix = "Up to " if choice.collection is None else ""
        self.size_var.set(
            f"Approx. {width_m / 1000:.1f} × {height_m / 1000:.1f} km. "
            f"{prefix}{pixels / 1_000_000:.1f} million cells at {resolution:g} m "
            f"({raw_gib:.2f} GiB raw float32 before compression)."
        )

    def _browse_output(self) -> None:
        folder = filedialog.askdirectory(
            parent=self.root,
            title="Choose output folder",
            initialdir=self.output_folder_var.get() or str(Path.home()),
        )
        if folder:
            self.output_folder_var.set(folder)

    def _output_path(self) -> Path:
        folder_text = self.output_folder_var.get().strip()
        if not folder_text:
            raise ValueError("Choose an output folder.")
        folder = Path(folder_text).expanduser()
        filename = self.filename_var.get().strip()
        filename = re.sub(r"[<>:\"/\\|?*\x00-\x1F]", "_", filename)
        filename = filename.strip(" .")
        if not filename:
            raise ValueError("Enter a valid output filename.")
        if filename.lower().endswith((".tif", ".tiff")):
            filename = Path(filename).stem
        return folder / f"{filename}.tif"

    def _start_inspection(self) -> None:
        if self._worker_running():
            return
        try:
            bounds = self._read_bounds()
        except ValueError as error:
            messagebox.showerror("Invalid selection", str(error), parent=self.root)
            return
        self.cancel_event.clear()
        self._set_busy(True)
        self.progress_var.set(0)
        self.status_var.set("Starting coverage inspection…")
        self.worker_thread = threading.Thread(
            target=self._inspection_worker,
            args=(bounds,),
            daemon=True,
        )
        self.worker_thread.start()

    def _inspection_worker(self, bounds: tuple[float, float, float, float]) -> None:
        try:
            exporter = TerrainExporter(
                self.logger,
                self.cancel_event,
                self._post_progress,
                self.proxy_settings,
            )
            results = exporter.inspect_all(bounds)
            self.event_queue.put(("inspection_complete", results))
        except CancelledError:
            self.event_queue.put(("cancelled",))
        except Exception as error:
            self.logger.error("Coverage inspection failed: %s", error)
            self.logger.debug(traceback.format_exc())
            self.event_queue.put((
                "error",
                "Coverage inspection failed",
                friendly_network_error(error, self.proxy_settings),
            ))

    def _start_export(self) -> None:
        if self._worker_running():
            return
        try:
            bounds = self._read_bounds()
            output_path = self._output_path()
        except ValueError as error:
            messagebox.showerror("Cannot export", str(error), parent=self.root)
            return

        choice = self._selected_choice()
        geod = Geod(ellps="WGS84")
        west, south, east, north = bounds
        mid_lat = (south + north) / 2.0
        mid_lon = (west + east) / 2.0
        _, _, width_m = geod.inv(west, mid_lat, east, mid_lat)
        _, _, height_m = geod.inv(mid_lon, south, mid_lon, north)
        estimated_pixels = width_m * height_m / (choice.nominal_resolution_m**2)
        if estimated_pixels > 350_000_000:
            proceed = messagebox.askyesno(
                "Large export",
                "This selection may exceed 350 million pixels at the requested resolution. "
                "It can take a long time and require several gigabytes of temporary disk space.\n\nContinue?",
                parent=self.root,
            )
            if not proceed:
                return

        if output_path.exists():
            overwrite = messagebox.askyesno(
                "Overwrite existing file?",
                f"The file already exists:\n{output_path}\n\nOverwrite it?",
                parent=self.root,
            )
            if not overwrite:
                return

        self.cancel_event.clear()
        self.last_result = None
        self._set_busy(True)
        self.progress_var.set(0)
        self.status_var.set("Starting terrain export…")
        self.logger.info("Export requested for WGS84 bounds %s", bounds)
        self.logger.info("Requested dataset: %s", choice.label)
        self.logger.info("Output path: %s", output_path)

        self.worker_thread = threading.Thread(
            target=self._export_worker,
            args=(
                bounds,
                choice,
                output_path,
                self.preview_var.get(),
                self.overview_var.get(),
            ),
            daemon=True,
        )
        self.worker_thread.start()

    def _export_worker(
        self,
        bounds: tuple[float, float, float, float],
        choice: DatasetChoice,
        output_path: Path,
        create_previews: bool,
        build_overviews: bool,
    ) -> None:
        try:
            exporter = TerrainExporter(
                self.logger,
                self.cancel_event,
                self._post_progress,
                self.proxy_settings,
            )
            result = exporter.export(
                bounds,
                choice,
                output_path,
                create_previews,
                build_overviews,
            )
            self.event_queue.put(("export_complete", result))
        except CancelledError:
            self.logger.warning("Operation cancelled by user.")
            self.event_queue.put(("cancelled",))
        except Exception as error:
            self.logger.error("Export failed: %s", error)
            self.logger.debug(traceback.format_exc())
            self.event_queue.put((
                "error",
                "Terrain export failed",
                friendly_network_error(error, self.proxy_settings),
            ))

    def _post_progress(self, percent: int, status: str) -> None:
        self.event_queue.put(("progress", max(0, min(100, percent)), status))

    def _cancel_worker(self) -> None:
        if not self._worker_running():
            return
        self.cancel_event.set()
        self.status_var.set("Cancelling after the current data block…")
        self.cancel_button.configure(state="disabled")
        self.logger.warning("Cancellation requested.")

    def _set_busy(self, busy: bool) -> None:
        normal = "disabled" if busy else "normal"
        readonly = "disabled" if busy else "readonly"
        self.export_button.configure(state=normal)
        self.inspect_button.configure(state=normal)
        self.dataset_combo.configure(state=readonly)
        self.draw_button.configure(state=normal)
        self.cancel_button.configure(state="normal" if busy else "disabled")

    def _worker_running(self) -> bool:
        return self.worker_thread is not None and self.worker_thread.is_alive()

    def _process_events(self) -> None:
        try:
            while True:
                event = self.event_queue.get_nowait()
                kind = event[0]
                if kind == "log":
                    line = str(event[1])
                    self.log_lines.append(line)
                    if self.log_dialog is not None and self.log_dialog.winfo_exists():
                        self.log_dialog.append(line)
                elif kind == "progress":
                    self.progress_var.set(float(event[1]))
                    self.status_var.set(str(event[2]))
                elif kind == "inspection_complete":
                    self._handle_inspection_complete(event[1])
                elif kind == "export_complete":
                    self._handle_export_complete(event[1])
                elif kind == "cancelled":
                    self.progress_var.set(0)
                    self.status_var.set("Cancelled.")
                    self._set_busy(False)
                elif kind == "error":
                    self.status_var.set(str(event[1]))
                    self._set_busy(False)
                    messagebox.showerror(str(event[1]), str(event[2]), parent=self.root)
        except queue.Empty:
            pass
        self.root.after(100, self._process_events)

    def _handle_inspection_complete(self, results: list[DatasetInspection]) -> None:
        self._set_busy(False)
        lines = []
        for result in results:
            resolution_text = (
                f"{result.resolution[0]:g} m" if result.resolution is not None else "unavailable"
            )
            lines.append(
                f"{result.choice.collection}: {result.valid_coverage * 100:.2f}% valid coverage, "
                f"{len(result.assets)} asset(s), source resolution {resolution_text}"
            )
        complete = next((r for r in results if r.valid_coverage >= 0.995), None)
        if complete:
            recommendation = f"Recommended: {complete.choice.label}"
        else:
            best = max(results, key=lambda result: result.valid_coverage, default=None)
            recommendation = (
                f"No dataset appears complete. Best result: {best.choice.label}"
                if best
                else "No usable coverage found."
            )
        self.status_var.set(recommendation)
        messagebox.showinfo(
            "CanElevation coverage",
            "\n".join(lines + ["", recommendation]),
            parent=self.root,
        )

    def _handle_export_complete(self, result: ExportResult) -> None:
        self.last_result = result
        self._set_busy(False)
        self.progress_var.set(100)
        elevation_text = ""
        if result.min_elevation is not None and result.max_elevation is not None:
            elevation_text = (
                f"\nElevation range: {result.min_elevation:.2f} to {result.max_elevation:.2f} m"
            )
        self.status_var.set(f"Complete: {result.geotiff.name}")
        extra_outputs = ""
        if result.normalized_heightmap_tiff is not None:
            extra_outputs += f"\n\nDisplay/CAM heightmap:\n{result.normalized_heightmap_tiff}"
        if result.heightmap_preview_8bit is not None:
            extra_outputs += f"\n\nViewable preview:\n{result.heightmap_preview_8bit}"
        messagebox.showinfo(
            "Terrain export complete",
            f"Metre-valued Float32 GeoTIFF master:\n{result.geotiff}\n\n"
            f"Dataset: {result.collection}\n"
            f"Grid: {result.output_width:,} × {result.output_height:,} pixels\n"
            f"Resolution: {result.resolution[0]:g} × {result.resolution[1]:g} m\n"
            f"Valid output coverage: {result.valid_coverage * 100:.2f}%"
            f"{elevation_text}"
            f"{extra_outputs}",
            parent=self.root,
        )

    def _show_log(self) -> None:
        if self.log_dialog is None or not self.log_dialog.winfo_exists():
            self.log_dialog = LogDialog(self.root, self.log_lines)
        else:
            self.log_dialog.deiconify()
            self.log_dialog.lift()
            self.log_dialog.focus_force()

    def _open_output_folder(self) -> None:
        folder = Path(self.output_folder_var.get().strip() or str(Path.home())).expanduser()
        folder.mkdir(parents=True, exist_ok=True)
        try:
            if sys.platform.startswith("win"):
                os.startfile(folder)  # type: ignore[attr-defined]
            elif sys.platform == "darwin":
                subprocess.Popen(["open", str(folder)])
            else:
                subprocess.Popen(["xdg-open", str(folder)])
        except Exception as error:
            messagebox.showerror("Could not open folder", str(error), parent=self.root)

    def _on_close(self) -> None:
        if self._worker_running():
            close = messagebox.askyesno(
                "Export in progress",
                "An operation is still running. Cancel it and close the application?",
                parent=self.root,
            )
            if not close:
                return
            self.cancel_event.set()
        self.root.destroy()


def main() -> int:
    root = tk.Tk()
    try:
        style = ttk.Style(root)
        if sys.platform.startswith("win"):
            for theme in ("vista", "xpnative"):
                if theme in style.theme_names():
                    style.theme_use(theme)
                    break
        app = App(root)
        root.mainloop()
        return 0
    except Exception as error:
        traceback.print_exc()
        try:
            messagebox.showerror(APP_NAME, f"The application could not start:\n\n{error}")
        except Exception:
            pass
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
