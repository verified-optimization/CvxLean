import cvxpy as cp

x1 = cp.Variable((1))
y1 = cp.Variable((1))

so1 = cp.Problem(
    cp.Maximize(cp.sqrt(x1 - y1)), [
    y1 == 2 * x1 - 3,
    x1 ** 2 <= 2
])
so1.solve()

print(f"so1.status   : {so1.status}."             ) # optimal
print(f"so1.value    : {so1.value}."              ) # 2.101002988589552
print(f"so1.solution : ({x1.value}, {y1.value})." ) # ([-1.41421356], [-5.82842712])
