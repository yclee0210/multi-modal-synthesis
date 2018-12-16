import argparse
import utils.logger as logger
from neo.neo import Neo
from neo.neo_a import NeoA
from neo.neo_ah import NeoAH
from neo.dsl import Dsl
from neo.deepcoder import Base

from config.default_args import DEFAULT_P_SIZE, DEFAULT_TEST_DATA_SET, DEFAULT_SYNTHESIZER
from config.path_utils import get_log_filename
from utils.common import get_annotated_problems, save_run_statistics, parse_program
from utils.timed_solver import TimedSolver


def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument('--program-size', dest='p_size', default=DEFAULT_P_SIZE, type=int)
    parser.add_argument('--data-set', dest='set', default=DEFAULT_TEST_DATA_SET, type=str)
    parser.add_argument('--synthesizer', dest='synthesizer', default=DEFAULT_SYNTHESIZER, type=str)
    parser.add_argument('--logfile', dest='logfile', type=str)
    return parser.parse_args()


def get_examples(problem):
    return [(example['inputs'], example['output']) for example in problem['examples']]


def get_outputs(examples):
    return [example[1] for example in examples]


def solve_problems(dsl, problems, runner):
    KNOWN_TIMEOUT_PS = [
    ]
    synth_model = Neo
    print(FLAGS.synthesizer)
    if FLAGS.synthesizer == 'deepcoder':
        synth_model = Base
    elif FLAGS.synthesizer == 'neo':
        synth_model = Neo
    elif FLAGS.synthesizer == 'neo_a':
        synth_model = NeoA
    elif FLAGS.synthesizer == 'neo_ah':
        synth_model = NeoAH
    for problem in problems:
        examples = get_examples(problem)
        outputs = get_outputs(examples)
        if None in outputs:
            continue
        dsl.set_variables(problem)
        synth = synth_model(dsl, FLAGS.p_size)
        model_answer = parse_program(problem['program'])
        if model_answer in KNOWN_TIMEOUT_PS:
            runner.timed_out.append(model_answer)
            runner.timed_out_count += 1
            continue
        print(model_answer)
        synth.set_specs(examples)
        # synth.synthesize(examples, problem['prediction'])
        # runner.solve(synth, examples, problem['prediction'], model_answer)
    # return runner.statistics()
    return dict()


def run(p_size, data_set):
    runner = TimedSolver()
    annotated_problems = get_annotated_problems(p_size, data_set)
    dsl = Dsl()
    return solve_problems(dsl, annotated_problems, runner)


if __name__ == "__main__":
    FLAGS = parse_args()
    logger.logger = logger.initialize()
    if FLAGS.logfile:
        logger.logger = logger.set_logfile(get_log_filename(FLAGS.logfile))
        logger.logger.debug(
            'Starting script python -m run --program-size=%s --data-set=%s --synthesizer=%s' % (
                FLAGS.p_size, FLAGS.set, FLAGS.synthesizer))

    statistics = run(FLAGS.p_size, FLAGS.set)
    # save_run_statistics(statistics, synthesizer=FLAGS.synthesizer, p_size=FLAGS.p_size)
