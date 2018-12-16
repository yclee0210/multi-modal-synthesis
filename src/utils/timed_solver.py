import time
from timeout_decorator.timeout_decorator import TimeoutError
from utils.logger import logger

ERASE_LINE = '\x1b[2K'


class TimedSolver(object):
    def __init__(self):
        self.total_time = 0
        self.problems_solved = 0
        self.unexpected = 0
        self.timed_out_count = 0
        self.unsolved = list()
        self.timed_out = list()
        self.time_taken = list()

    def solve(self, solver, examples, prediction_model, model_answer):
        try:
            start = time.time()
            solved, solution = solver.synthesize(examples, prediction_model)
            end = time.time()
            time_taken = (end - start) * 1000
            if solved:
                if str(solution) != model_answer:
                    logger.debug('Expected: %s, Got: %s' % (model_answer, solution))
                    self.unexpected += 1
                else:
                    logger.debug('Got expected: %s' % solution)
                self.total_time += time_taken
                self.problems_solved += 1
                self.time_taken.append(time_taken)
            else:
                logger.debug('Expected: %s, but not found' % model_answer)
                self.unsolved.append(model_answer)
        except TimeoutError as e:
            logger.debug('Expected: %s, but timed out' % model_answer)
            self.timed_out_count += 1
            self.timed_out.append(model_answer)

    def statistics(self):
        return dict(total_time=self.total_time,
                    problems_solved=self.problems_solved,
                    unexpected=self.unexpected,
                    timed_out_count=self.timed_out_count,
                    unsolved=self.unsolved,
                    timed_out=self.timed_out,
                    time_taken=self.time_taken)