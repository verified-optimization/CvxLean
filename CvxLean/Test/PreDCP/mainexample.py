import cvxpy as cp

x = cp.Variable(pos=True)

p = cp.Problem(
    cp.Minimize(x), [
        -x <= cp.log(cp.sqrt(x))
    ])

p.solve(verbose=True)
