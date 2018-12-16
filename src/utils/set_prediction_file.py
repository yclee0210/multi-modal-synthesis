import argparse
import random

from deepcoder.nn import model
from config.default_args import DEFAULT_P_SIZE, DEFAULT_TEST_SIZE, DEFAULT_TEST_DATA_SET
from utils.common import get_problems, get_predictor, get_prediction_filename, save_to_json


def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument('--program-size', dest='p_size', default=DEFAULT_P_SIZE, type=int)
    parser.add_argument('--model', dest='model', type=int)
    parser.add_argument('--data-set', dest='set', default=DEFAULT_TEST_DATA_SET, type=str)
    parser.add_argument('--test-size', dest='test_size', default=DEFAULT_TEST_SIZE, type=int)
    return parser.parse_args()


def get_predictions(predictor, problems):
    max_nb_inputs = model.get_max_nb_inputs(predictor)
    x, _ = model.get_XY(problems, max_nb_inputs)
    return predictor.predict(x)


def annotate_problems_with_predictions(problems, predictions):
    for problem, prediction in zip(problems, predictions):
        problem['prediction'] = prediction.tolist()
    return problems


def set_annotated_problems(p_size, model_p_size, data_set, test_size):
    problems = get_problems(p_size, data_set)
    problems = [problem for problem in problems if None not in [example['output'] for example in problem['examples']]]
    if len(problems) < test_size:
        raise ValueError('Requested test set size %d is larger than the available data' % test_size)
    int_problems = [problem for problem in problems if type(problem['examples'][0]['output']) == int]
    list_problems = [problem for problem in problems if type(problem['examples'][0]['output']) == list]
    int_size = int(test_size / 2)
    if len(int_problems) < int_size:
        int_size = len(int_problems)
    list_size = test_size - int_size

    random.shuffle(int_problems)
    random.shuffle(list_problems)
    problems = int_problems[:int_size] + list_problems[:list_size]
    predictor = get_predictor(model_p_size)

    predictions = get_predictions(predictor, problems)
    return annotate_problems_with_predictions(problems, predictions)


if __name__ == "__main__":
    FLAGS = parse_args()
    if FLAGS.model is None:
        FLAGS.model = FLAGS.p_size
    result = set_annotated_problems(FLAGS.p_size, FLAGS.model, FLAGS.set, FLAGS.test_size)
    save_file = get_prediction_filename(FLAGS.p_size, FLAGS.set, create=True)
    save_to_json(save_file, result)

