import cvxpy as cp

x3 = cp.Variable(pos=True)
y3 = cp.Variable(pos=True)
z3 = cp.Variable(pos=True)

# exp3 = cp.Problem(
#     cp.Maximize(x3 / y3), [
#     2 <= x3,
#     x3 <= 3,
#     x3 ** 2 + 3 * (y3 / z3) <= y3 ** 0.5,
# ])
# exp3.solve(gp=True)

exp3 = cp.Problem(
    cp.Maximize(x3 / y3), [
    2 <= x3,
    x3 <= 3,
    x3 ** 2 + 3 * y3 / z3 <= y3 ** 0.5,
    x3 * y3 == z3,
])
exp3.solve(gp=True)

print(f"exp3.status   : {exp3.status}.") 
print(f"exp3.value    : {exp3.value}." ) 
print(f"exp3.solution : {x3.value}."   ) 

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
    #x4 <= cp.log(3),
    #cp.log_sum_exp(cp.hstack([2 * x4 + (-0.5) * y4, 3 * 0.5 * y4 + (-1) * z4])) <= 0,
    cp.exp(2 * x4 + (-0.5) * y4) + cp.exp(3 * 0.5 * y4 + (-1) * z4) <= 1,
    x4 <= 3,
])
exp4.solve()

print(f"exp4.status   : {exp4.status}.") 
print(f"exp4.value    : {exp4.value}." ) 
print(f"exp4.solution : {x4.value}."   ) 

x5 = cp.Variable(pos=True)
y5 = cp.Variable(pos=True)

exp5 = cp.Problem(
    cp.Minimize(x5 * y5), [
    cp.exp(y5 / x5) <= cp.log(y5)
    ])
exp5.solve(gp=True)

print(f"exp5.status   : {exp5.status}.") 
print(f"exp5.value    : {exp5.value}." )
print(f"exp5.solution : {x5.value}."   )

x6 = cp.Variable()

test6 = cp.Problem(
    cp.Minimize(x6-cp.log(cp.log(x6 + 1))), [
    x6 <= 100,

    ])
test6.solve()

print(f"test6.status   : {test6.status}.")
print(f"test6.value    : {test6.value}." )
print(f"test6.solution : {x6.value}."   )

