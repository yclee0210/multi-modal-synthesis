import matplotlib.pyplot as plt
import json


def get_series(filename):
    data = json.load(open(filename))
    time_taken = data['time_plot']
    time_taken.sort()

    def _scan1l(f, xs):
        ys = [0] * len(xs)
        for i, x in enumerate(xs):
            if i:
                ys[i] = f(ys[i - 1], x)
            else:
                ys[i] = x
        return ys

    cum_time_taken = _scan1l(lambda x, y: x + y, time_taken)
    return [0] + cum_time_taken


MODES = [
    # 'deepcoder',
    'neo',
    'neo_with_specs_and_heuristics',
    # 'neo_with_specs'
]


fig = plt.figure()
ax = fig.add_subplot(111)

label = dict(neo_with_specs_and_heuristics='Neo w/ Extension',
             neo='Neo',)

for mode in MODES:
    filename = '../results/%s_result.json' % mode
    ys = get_series(filename)
    xs = [x for x in range(len(ys))]
    ax.scatter(xs, ys, marker='x', label=label[mode])

plt.legend(loc='upper left')
plt.show()