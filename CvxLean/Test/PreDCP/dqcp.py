import cvxpy as cp
import numpy as np

def dqcp1():
    x = cp.Variable(pos=True)
    y = cp.Variable(nonneg=True)

    p = cp.Problem(
        cp.Minimize(-y), [
            1 <= x,
            x <= 2,
            cp.sqrt((2 * y) / (x + y)) <= 1
        ])

    assert(p.is_dqcp())
    assert(not p.is_dgp())
    assert(not p.is_dcp())

    p.solve(qcp=True)

def dqcp2():
    a = .05
    b = .65

    x = cp.Variable(pos=True)

    p = cp.Problem(
        cp.Minimize(cp.sqrt(cp.inv_pos(cp.square(x)) - 1)), [
            a * cp.inv_pos(x) - (1 - b) * cp.sqrt(1 - cp.square(x)) <= 0
        ])

    assert(p.is_dqcp())
    assert(not p.is_dgp())
    assert(not p.is_dcp())

    p.solve(qcp=True)

def dqcp3():
    x = cp.Variable()
    y = cp.Variable(nonneg=True)
    p = cp.Problem(
        cp.Minimize(0), [
            x / y <= 3,
            x == 12, 
            y <= 6
        ])

    assert(p.is_dqcp())
    assert(not p.is_dgp())
    assert(not p.is_dcp())

    p.solve(qcp=True)

def dqcp4():
    x = cp.Variable()
    p = cp.Problem(
        cp.Minimize(-x), [
            cp.dist_ratio(cp.vstack([x, 1.0]), np.array([-1, -1]), np.array([0.0, -10.0])) <= 1,
            10 <= x
        ])

    assert(p.is_dqcp())
    assert(not p.is_dgp())
    assert(not p.is_dcp())

    p.solve(qcp=True)

if __name__ == "__main__":
    dqcp1()
    dqcp2()
    dqcp3()
    dqcp4()
