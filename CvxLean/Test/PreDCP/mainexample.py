import cvxpy as cp

x = cp.Variable(pos=True)

p = cp.Problem(
    cp.Minimize(x), [
        1 / cp.sqrt(x) <= cp.exp(x)
    ])

assert(not p.is_dgp())
assert(not p.is_dqcp())
assert(not p.is_dcp())

p = cp.Problem(
    cp.Minimize(x), [
        cp.exp(-x) <= cp.sqrt(x)
    ])

assert(not p.is_dgp())
assert(p.is_dqcp())
assert(p.is_dcp())

p.solve(verbose=True)
