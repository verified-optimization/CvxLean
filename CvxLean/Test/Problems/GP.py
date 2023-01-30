import cvxpy as cp

x = cp.Variable(pos=True, name="x")
y = cp.Variable(pos=True, name="y")
z = cp.Variable(pos=True, name="z")

w = cp.Variable(pos=True, name="w")

objective_fn = x * y * z
constraints = [
    x * y * z + 2 * x * z <= 10, 
    x <= 2 * y, 
    y <= 2 * x, 
    z >= 1]

# 

# print("DGP check")
# assert w.is_log_log_affine()
# assert (cp.Constant(1)).is_log_log_affine()
# assert (w + 1).is_log_log_convex()
# assert (w + 1).is_log_log_concave()
# assert (w + 1).is_log_log_affine()
# assert (x + 1).is_dgp()

# assert objective_fn.is_log_log_concave()
# assert all(constraint.is_dgp() for constraint in constraints)

problem = cp.Problem(cp.Maximize(objective_fn), constraints)

print(problem)
print("Is this problem DGP?", problem.is_dgp())

problem.solve(gp=True, verbose=True)

print(f"problem.status   : {problem.status}.")
print(f"problem.value    : {problem.value}." )
print(f"problem.solution : {x.value}, {y.value}, {z.value}, {w.value}.")
