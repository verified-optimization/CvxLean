import cvxpy as cp

x3 = cp.Variable(pos=True)
y3 = cp.Variable(pos=True)
z3 = cp.Variable(pos=True)

exp3 = cp.Problem(
    cp.Maximize(x3 / y3), [
    2 <= x3,
    x3 <= 3,
    x3 ** 2 + 3 * (y3 / z3) <= y3 ** 0.5,
])
exp3.solve(gp=True)

print(f"exp3.status   : {exp3.status}.") # optimal
print(f"exp3.value    : {exp3.value}." ) # 4.641588833612779
print(f"exp3.solution : {x3.value}."   ) # 2.154434690031884

x4 =cp.Variable((1))
y4 =cp.Variable((1))
z4 =cp.Variable((1))

# exp4 = cp.Problem(
#     cp.Minimize(cp.exp(-2 * x4)), [
#     #cp.log(cp.exp(2 * x4) + cp.exp(x4)) <= cp.log(11)
#     cp.log(x4) >= 10
# ])

exp4 = cp.Problem(
    cp.Maximize(x4 - y4), [
    cp.log(2) <= x4, 
    x4 <= cp.log(3),
    cp.log_sum_exp(cp.hstack([2 * x4 + (-0.5) * y4, 3 * 0.5 * y4 + (-1) * z4])) <= 0,
])
exp4.solve()

print(f"exp4.status   : {exp4.status}.") # optimal
print(f"exp4.value    : {exp4.value}." ) # 4.641588833612779
print(f"exp4.solution : {x4.value}."   ) # [0.5]
