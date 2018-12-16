from config.paths import *
from config.default_args import *


def get_problems_filename(p_size, data_set):
    filename = 'T=%d_%s.json' % (p_size, data_set)
    filepath = DATA_DIR / filename
    if not filepath.exists():
        err_msg = 'Please download data or generate using Deepcoder'
        raise ValueError(build_error_message(file_not_found, filename, err_msg))
    return str(filepath)


def get_model_filename(p_size):
    filename = 'T=%d.h5' % p_size
    filepath = MODEL_DIR / filename
    if not filepath.exists():
        gen_script = 'python -m deepcoder.scripts.train-nn'
        args = dict(infile=DATA_DIR / ('T=%d_train.json' % p_size),
                    outfile=str(filepath),
                    epochs=DEFAULT_TRAIN_EPOCHS)
        gen_command = '%s %s' % (gen_script, build_args(args))
        msg = 'Please run %s' % gen_command
        raise ValueError(build_error_message(file_not_found, filename, msg))
    return str(filepath)


def get_prediction_filename(p_size, data_set, create=False):
    filename = 'predictions_T=%d_%s.json' % (p_size, data_set)
    filepath = PRED_DIR / filename
    if not create and not filepath.exists():
        gen_script = 'python -m utils.prepare_predictions'
        args = dict(program_size=p_size,
                    data_set=data_set)
        gen_command = '%s %s' % (gen_script, build_args(args))
        msg = 'Please run %s' % gen_command
        raise ValueError(build_error_message(file_not_found, filename, msg))
    else:
        return str(filepath)


def get_results_filename(synthesizer, p_size):
    filename = 'results_%s_T=%d.json' % (synthesizer, p_size)
    filepath = RUN_STATS_DIR / filename
    return str(filepath)


def get_log_filename(filename):
    filepath = LOG_DIR / filename
    return str(filepath)


def build_args(args):
    out = list()
    for k, v in args.items():
        out.append('--%s=%s' % (k, v))
    return ' '.join(out)


def file_not_found(filename, *args):
    msg = '%s does not exist.' % filename
    return '%s %s' % (msg, ' '.join(args))


def build_error_message(err_gen, *args):
    return err_gen(*args)
