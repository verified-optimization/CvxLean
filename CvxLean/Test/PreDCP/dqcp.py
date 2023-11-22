import cvxpy as cp

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

print(p.value)
