import cvxpy as cp
import numpy as np

K = -1
V = -1
A = 1
k = -1
v = -2
a = 1

x1 = cp.Variable((1))
t1 = 2.0 # Picked by hand
p1 = cp.Problem(
    cp.Minimize(t1), [
    1 <= t1,
    K * x1 <= k,
    V * x1 <= v * t1, 
    A * x1 <= a * (t1 ** 2),
])
p1.solve()
print(p1.status)
print(x1.value, t1)

x2 = cp.Variable((1))
y2 = cp.Variable((1))
t2 = cp.Variable((1))
p2 = cp.Problem(
    cp.Minimize(y2 - t2), [
    1 <= t2,
    K * x2 <= k,
    V * x2 <= v * t2,
    A * x2 <= a * y2,
    t2 ** 2 <= y2,
])
p2.solve()
print(x2.value, t2.value, y2.value)

# SDP relaxation

x3 = cp.Variable((1))
t3 = cp.Variable((1))
#v3 = np.array([[1], [x3], [t3]])
k = 3
X3 = cp.Variable((k, k), PSD=True)
Z3 = cp.Variable((k + 1, k + 1), PSD=True)
#Z3 = [[1, v3.T], [v3, X3]]
A3 = np.array([
    [    0, A / 2,      0],
    [A / 2,     0,      0],
    [    0,     0, -a / 2]
])

p3 = cp.Problem(
    cp.Minimize(t3), [
    1 <= t3,
    K * x3 <= k,
    V * x3 <= v * t3, 

    # A * x3 <= a * t3 ** 2,
    cp.trace(X3 @ A3) <= 0,
    Z3[0, 0] == 1,
    Z3[0, 1] == 1,
    Z3[0, 2] == x3,
    Z3[0, 3] == t3,
    Z3[1, 0] == 1,
    Z3[1, 1] == X3[0, 0],
    Z3[1, 2] == X3[0, 1],
    Z3[1, 3] == X3[0, 2],
    Z3[2, 0] == x3,
    Z3[2, 1] == X3[1, 0],
    Z3[2, 2] == X3[1, 1],
    Z3[2, 3] == X3[1, 2],
    Z3[3, 0] == t3,
    Z3[3, 1] == X3[2, 0],
    Z3[3, 2] == X3[2, 1],
    Z3[3, 3] == X3[2, 2],
    Z3 >> 0,
])
p3.solve()
print(p3.status)
print(x3.value, t3.value, X3.value)