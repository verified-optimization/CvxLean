import cvxpy as cp

x1 = cp.Variable((1))

log1 = cp.Problem(
    cp.Minimize(x1), [
    10 <= cp.log(x1)
])
log1.solve()

print(f"log1.status   : {log1.status}.") # optimal
print(f"log1.value    : {log1.value}." ) # 22026.465740288553
print(f"log1.solution : {x1.value}."   ) # [22026.46574029]

x2 = cp.Variable((1))

log2 = cp.Problem(
    cp.Maximize(cp.log(x2)), [
    x2 <= 10
])
log2.solve()

print(f"log2.status   : {log2.status}.") # optimal
print(f"log2.value    : {log2.value}." ) # 2.302585092994046
print(f"log2.solution : {x2.value}."   ) # [10.]
