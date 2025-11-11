import importlib.util
import sys
from pathlib import Path

MODULE_PATH = Path(__file__).resolve().parents[1] / "النهائي .py"
SPEC = importlib.util.spec_from_file_location("final_module", MODULE_PATH)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC is not None and SPEC.loader is not None
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)

Box = MODULE.Box
SmartMoneyAlgoProE5 = MODULE.SmartMoneyAlgoProE5


def _seed_series(algo: SmartMoneyAlgoProE5, candles):
    for candle in candles:
        algo.series.append(candle)
        algo._update_displacement_metrics(
            candle["open"],
            candle["high"],
            candle["low"],
            candle["close"],
        )


def _make_box(text: str, top: float, bottom: float, *, left: int = 0, right: int = 0) -> Box:
    return Box(
        left=left,
        right=right,
        top=top,
        bottom=bottom,
        bgcolor="#1e90ff66",
        border_color="#1e90ff",
        text=text,
    )


def _base_algo() -> SmartMoneyAlgoProE5:
    algo = SmartMoneyAlgoProE5()
    algo.initialised = True
    algo.retracement_recent_bars = 100
    return algo


def test_bos_retracement_accepts_zone_below_break():
    algo = _base_algo()
    _seed_series(
        algo,
        [
            {"time": 900, "open": 99, "high": 101, "low": 98, "close": 100, "volume": 0},
            {"time": 1000, "open": 100, "high": 104, "low": 99, "close": 103, "volume": 0},
            {"time": 1010, "open": 104, "high": 105, "low": 99, "close": 100, "volume": 0},
        ],
    )
    algo._last_bos_timestamp = 1000
    algo._last_bos_direction = "bullish"
    algo._last_bos_price = 100.0
    box = _make_box("EXT OB", top=99.6, bottom=98.6, left=900, right=1000)
    algo._register_box_event(box, status="new", event_time=900)
    box.set_right(1010)
    algo._register_box_event(box, status="touched", event_time=1010)
    assert any("BOS Retracement" in alert for _, alert in algo.alerts)


def test_bos_retracement_rejects_zone_above_break():
    algo = _base_algo()
    _seed_series(
        algo,
        [
            {"time": 900, "open": 99, "high": 101, "low": 98, "close": 100, "volume": 0},
            {"time": 1000, "open": 100, "high": 104, "low": 99, "close": 103, "volume": 0},
            {"time": 1010, "open": 104, "high": 105, "low": 102, "close": 104, "volume": 0},
        ],
    )
    algo._last_bos_timestamp = 1000
    algo._last_bos_direction = "bullish"
    algo._last_bos_price = 100.0
    box = _make_box("EXT OB", top=101.5, bottom=100.5, left=900, right=1000)
    algo._register_box_event(box, status="new", event_time=900)
    box.set_right(1010)
    algo._register_box_event(box, status="touched", event_time=1010)
    assert not any("Retracement" in alert for _, alert in algo.alerts)


def test_choch_bearish_prefers_zones_above_break():
    algo = _base_algo()
    _seed_series(
        algo,
        [
            {"time": 2000, "open": 252, "high": 255, "low": 249, "close": 251, "volume": 0},
            {"time": 2010, "open": 251, "high": 257, "low": 244, "close": 246, "volume": 0},
        ],
    )
    algo._last_choch_timestamp = 2000
    algo._last_choch_direction = "bearish"
    algo._last_choch_price = 250.0
    idm_box = _make_box("IDM OB", top=256, bottom=254, left=1980, right=2000)
    algo._register_box_event(idm_box, status="new", event_time=1980)
    idm_box.set_right(2010)
    algo._register_box_event(idm_box, status="touched", event_time=2010)
    assert any("CHOCH Retracement" in alert for _, alert in algo.alerts)

    golden = _make_box("Golden zone", top=247, bottom=245, left=1985, right=2000)
    algo._register_box_event(golden, status="new", event_time=1985)
    golden.set_right(2010)
    algo._register_box_event(golden, status="touched", event_time=2010)
    choch_alerts = [alert for _, alert in algo.alerts if "CHOCH Retracement" in alert]
    assert len(choch_alerts) == 1


def test_disabled_zone_type_suppresses_alerts():
    algo = _base_algo()
    algo.structure_settings.zones["GOLDEN_ZONE"].enabled = False
    _seed_series(
        algo,
        [
            {"time": 3000, "open": 100, "high": 102, "low": 99, "close": 101, "volume": 0},
            {"time": 3010, "open": 101, "high": 103, "low": 97, "close": 98, "volume": 0},
        ],
    )
    algo._last_bos_timestamp = 3000
    algo._last_bos_direction = "bullish"
    algo._last_bos_price = 101.0
    golden = _make_box("Golden zone", top=100.8, bottom=99.2, left=2980, right=3000)
    algo._register_box_event(golden, status="new", event_time=2980)
    golden.set_right(3010)
    algo._register_box_event(golden, status="touched", event_time=3010)
    assert not any("Retracement" in alert for _, alert in algo.alerts)


def test_first_touch_only_blocks_retests():
    algo = _base_algo()
    _seed_series(
        algo,
        [
            {"time": 4000, "open": 50, "high": 52, "low": 49, "close": 51, "volume": 0},
            {"time": 4010, "open": 51, "high": 53, "low": 48, "close": 49, "volume": 0},
            {"time": 4020, "open": 49, "high": 52, "low": 48.5, "close": 50, "volume": 0},
        ],
    )
    algo._last_bos_timestamp = 4000
    algo._last_bos_direction = "bullish"
    algo._last_bos_price = 50.5
    zone = _make_box("EXT OB", top=50.3, bottom=49.3, left=3980, right=4000)
    algo._register_box_event(zone, status="new", event_time=3980)
    zone.set_right(4010)
    algo._register_box_event(zone, status="touched", event_time=4010)
    zone.set_right(4020)
    algo._register_box_event(zone, status="retest", event_time=4020)
    bos_alerts = [alert for _, alert in algo.alerts if "BOS Retracement" in alert]
    assert len(bos_alerts) == 1


def test_expired_validity_window_blocks_alert():
    algo = _base_algo()
    algo.structure_settings.zones["EXT_OB"].validity_bars = 1
    _seed_series(
        algo,
        [
            {"time": 5000, "open": 120, "high": 122, "low": 118, "close": 121, "volume": 0},
            {"time": 5010, "open": 121, "high": 124, "low": 119, "close": 123, "volume": 0},
            {"time": 5020, "open": 123, "high": 126, "low": 120, "close": 125, "volume": 0},
            {"time": 5030, "open": 125, "high": 128, "low": 122, "close": 124, "volume": 0},
        ],
    )
    algo._last_bos_timestamp = 5000
    algo._last_bos_direction = "bullish"
    algo._last_bos_price = 121.0
    zone = _make_box("EXT OB", top=120.8, bottom=119.8, left=4980, right=5000)
    algo._register_box_event(zone, status="new", event_time=4980)
    zone.set_right(5030)
    algo._register_box_event(zone, status="touched", event_time=5030)
    assert not any("Retracement" in alert for _, alert in algo.alerts)


def test_use_wicks_false_requires_body_touch():
    algo = _base_algo()
    algo.structure_settings.zones["EXT_OB"].use_wicks = False
    _seed_series(
        algo,
        [
            {"time": 6000, "open": 70, "high": 72, "low": 69, "close": 71, "volume": 0},
            {"time": 6010, "open": 71, "high": 71.2, "low": 69.1, "close": 71.1, "volume": 0},
        ],
    )
    algo._last_bos_timestamp = 6000
    algo._last_bos_direction = "bullish"
    algo._last_bos_price = 71.0
    zone = _make_box("EXT OB", top=70.2, bottom=69.4, left=5980, right=6000)
    algo._register_box_event(zone, status="new", event_time=5980)
    zone.set_right(6010)
    algo._register_box_event(zone, status="touched", event_time=6010)
    assert not any("Retracement" in alert for _, alert in algo.alerts)
