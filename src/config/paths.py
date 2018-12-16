from pathlib import Path

CONFIG_ROOT = Path(__file__).parent.resolve()
SRC_ROOT = CONFIG_ROOT.parent
REPO_ROOT = SRC_ROOT.parent
DATA_DIR = REPO_ROOT / 'dataset'
TMP_DIR = REPO_ROOT / 'tmp'
RESULTS_DIR = REPO_ROOT / 'results'

if not RESULTS_DIR.exists():
    RESULTS_DIR.mkdir()
if not TMP_DIR.exists():
    TMP_DIR.mkdir()
if not RESULTS_DIR.exists():
    RESULTS_DIR.mkdir()

LOG_DIR = TMP_DIR / 'logs'
MODEL_DIR = TMP_DIR / 'models'
PRED_DIR = TMP_DIR / 'predictions'

RUN_STATS_DIR = RESULTS_DIR / 'stats'

if not LOG_DIR.exists():
    LOG_DIR.mkdir()
if not MODEL_DIR.exists():
    MODEL_DIR.mkdir()
if not PRED_DIR.exists():
    PRED_DIR.mkdir()
if not RUN_STATS_DIR.exists():
    RUN_STATS_DIR.mkdir()
