import cvxpy as cp
import numpy as np

x1 = cp.Variable((1))

linear1 = cp.Problem(
    cp.Maximize(7 * x1 + 1), [
    2 * x1 <= 3
])
linear1.solve()

print(f"linear1.status   : {linear1.status}.") # optimal
print(f"linear1.value    : {linear1.value}." ) # 11.5
print(f"linear1.solution : {x1.value}."      ) # [1.5]


x2 = cp.Variable((1))
y2 = cp.Variable((1))

linear2 = cp.Problem(
    cp.Maximize(40 * x2 + 30 * y2), [
    x2 + y2 <= 12,
    2 * x2 + y2 <= 16,
    0 <= x2, 
    0 <= y2
])
linear2.solve()

print(f"linear2.status   : {linear2.status}."        ) # optimal
print(f"linear2.value    : {linear2.value}."         ) # 399.99999984761
print(f"linear2.solution : ({x2.value}, {y2.value}).") # ([4.], [8.])


x3 = cp.Variable((2))

linear3 = cp.Problem(
    cp.Minimize(5 * x3[0] - 4 * x3[1]), [
    3 <= x3[0] + x3[1],
    x3[1] <= 7 + x3[0]
])
linear3.solve()

print(f"linear3.status   : {linear3.status}.") # optimal
print(f"linear3.value    : {linear3.value}." ) # -30.0
print(f"linear3.solution : {x3.value}."      ) # [-2.  5.]


x4 = cp.Variable((5))
y4 = cp.Variable((1))
z4 = cp.Variable((1))

linear4 = cp.Problem(
    cp.Minimize(cp.sum(x4) + 10 * (y4 + z4)), [
    4.0 <= y4, 
    2.5 <= z4,
    y4 + z4 <= cp.sum(x4) 
])
linear4.solve()

print(f"linear4.status   : {linear4.status}."                    ) # optimal
print(f"linear4.value    : {linear4.value}."                     ) # 71.5
print(f"linear4.solution : ({x4.value}, {y4.value}, {z4.value}).") # ([-0.  -0.  -0.  -0.   6.5], [4.], [2.5])

A5 = [ [ 0.51417013, -1.40067196,  0.71943208,  0.58510080]
     , [-0.53401066,  1.65680551,  0.13519183,  0.29269704]
     , [ 0.39224659, -0.61942485,  1.73666095,  2.46240110]
     , [ 1.76713469,  0.61389781,  0.80559111, -0.12640489]]
A5 = np.array(A5)

b5 = np.array([ 10.56567387,  21.07609985,  23.43361457,  15.14706378])

c5 = np.array([ 0.14794342, -0.19493149,  0.31361829,  1.13959857])

x5 = cp.Variable((4))

linear5 = cp.Problem(
    cp.Maximize(c5.T @ x5), [
    A5 @ x5 <= b5,
    0 <= x5
])
linear5.solve()

print(f"linear5.status   : {linear5.status}.") # optimal
print(f"linear5.value    : {linear5.value}." ) # 11.81473957497231
print(f"linear5.solution : {x5.value}."      ) # [3.00606165e-12 1.05699632e+01 7.35158184e-13 1.21754788e+01]
