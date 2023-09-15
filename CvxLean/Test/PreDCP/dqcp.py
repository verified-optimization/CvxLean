import cvxpy as cp

x = cp.Variable(pos=True)

p = cp.Problem(
    cp.Minimize(x), [
        cp.sqrt(x / (x + 1)) <= 1
    ])

assert(p.is_dqcp())
assert(not p.is_dgp())
assert(not p.is_dcp())

p.solve(qcp=True)

print(p.value)
