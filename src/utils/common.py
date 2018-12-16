import json
import keras
from config.path_utils import get_model_filename, get_problems_filename, get_prediction_filename, \
    get_results_filename


def get_problems(p_size, data_set):
    filename = get_problems_filename(p_size, data_set)
    return json.loads(open(filename).read())


def get_predictor(p_size):
    filename = get_model_filename(p_size)
    return keras.models.load_model(filename)


def get_annotated_problems(p_size, data_set):
    filename = get_prediction_filename(p_size, data_set)
    return json.loads(open(filename).read())


def save_run_statistics(statistics, synthesizer, p_size):
    filename = get_results_filename(synthesizer, p_size)
    save_to_json(filename, statistics)


def parse_program(deepcoder_program_str):
    component_strs = deepcoder_program_str.split('|')
    brokedown_list = list()
    for component_str in component_strs:
        breakdown = component_str.split(',')
        component = breakdown[0]
        params = breakdown[1:]
        brokedown_list.append((component, params))
    root = brokedown_list[-1]
    return construct_program_string(brokedown_list, root, len(brokedown_list) - 1)


def construct_program_string(comp_list, root, index):
    LAMBDAS = ['+1', '-1', '*2', '/2', '*-1', '**2', '*3', '/3', '*4', '/4', '>0', '<0', 'EVEN',
               'ODD', '+', '-', '*', 'min', 'max']
    prog = root[0]
    if prog == 'INT' or prog == 'LIST':
        return 'x%d' % index
    params = root[1]
    constructed_params = list()
    for param in params:
        if param not in LAMBDAS:
            idx = int(param)
            constructed_params.append(construct_program_string(comp_list, comp_list[idx], idx))
        else:
            constructed_params.append(param)
    return '%s(' % prog + ','.join(constructed_params) + ')'


def save_to_json(filename, data):
    with open(filename, 'w') as fp:
        json.dump(data, fp)
