import cvxpy as cp

x1 = cp.Variable((1))

exp1 = cp.Problem(
    cp.Maximize(x1), [
    cp.exp(x1) <= 10
])
exp1.solve()

print(f"exp1.status   : {exp1.status}.") # optimal
print(f"exp1.value    : {exp1.value}." ) # 2.302585090971631
print(f"exp1.solution : {x1.value}."   ) # [2.30258509]

x2 = cp.Variable((1))

exp2 = cp.Problem(
    cp.Minimize(cp.exp(x2)), [
    10 <= x2
])
exp2.solve()

print(f"exp2.status   : {exp2.status}.") # optimal
print(f"exp2.value    : {exp2.value}." ) # 22026.465794806718
print(f"exp2.solution : {x2.value}."   ) # [10.]
