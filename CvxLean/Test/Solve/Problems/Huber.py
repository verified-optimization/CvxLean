import cvxpy as cp
import numpy as np

def hub(x):
    v = cp.Variable((1))
    w = cp.Variable((1))
    p = cp.Problem(
        cp.Minimize(2 * v + w ** 2), [
            cp.abs(x) <= v + w,
            v >= 0,
            w <= 1,
        ]
    )
    p.solve()
    return (v.value, w.value, 2 * v.value + w.value ** 2)

xs = np.linspace(-3.0, 3.0, num=50)
hubs = [hub(x) for x in xs]
vs = np.array([x[0] for x in hubs])
ws = np.array([x[1] for x in hubs])
ys = np.array([x[2] for x in hubs])
zs = np.array([x**2 for x in xs])


import matplotlib.pyplot as plt
plt.plot(xs, ys)
plt.plot(xs, vs)
plt.plot(xs, ws)
plt.show()

