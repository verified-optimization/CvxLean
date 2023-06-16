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

# x3 = cp.Variable((1), complex=True)
# t3 = cp.Variable((1), complex=True)
# k = 3
# X3 = cp.Variable((k, k))
# Z3 = cp.Variable((k + 1, k + 1))
# A3 = np.array([
#     [    0, A / 2,      0],
#     [A / 2,     0,      0],
#     [    0,     0,     -a]
# ])

# p3 = cp.Problem(
#     cp.Minimize(cp.real(t3)), [
#     1 <= cp.real(t3),
#     K * cp.real(x3) <= k,
#     V * cp.real(x3) <= v * cp.real(t3), 

#     # A * x3 <= a * t3 ** 2,
#     cp.trace(X3 @ A3) <= 0,
#     X3[0, 0] == 1,
#     Z3[0, 0] == 1,
#     Z3[0, 1] == 1,
#     Z3[0, 2] == x3,
#     Z3[0, 3] == t3,
#     Z3[1, 0] == 1,
#     Z3[1, 1] == X3[0, 0],
#     Z3[1, 2] == X3[0, 1],
#     Z3[1, 3] == X3[0, 2],
#     Z3[2, 0] == x3,
#     Z3[2, 1] == X3[1, 0],
#     Z3[2, 2] == X3[1, 1],
#     Z3[2, 3] == X3[1, 2],
#     Z3[3, 0] == t3,
#     Z3[3, 1] == X3[2, 0],
#     Z3[3, 2] == X3[2, 1],
#     Z3[3, 3] == X3[2, 2],
#     X3 >> 0,
#     Z3 >> 0,
#     # cp.lambda_max(X3) <= 10
# ])
# p3.solve()
# print(p3.status)
# print(x3.value, t3.value)
# print(X3.value)
# print(K * x3.value, k, K * x3.value <= k) 
# print(V * x3.value, v * t3.value, V * x3.value <= v * t3.value)
# print(A * x3.value, a * t3.value ** 2, A * x3.value <= a * t3.value ** 2)
# print(np.linalg.eigvals(X3.value))

x3 = cp.Variable((1))
t3 = cp.Variable((1))
v3 = cp.vstack([x3, t3])
X3 = cp.Variable((2, 2), PSD=True)
Z3 = cp.Variable((3, 3), PSD=True)
A3 = np.array([[0, 0], [0, a]])
a3 = np.array([A, 0])

k3 = cp.Variable((1))

# X = [[x^2, xt], [xt, t^2]]

# X11 - t^2 = (sqrt(X11) - t) * (sqrt(X11) + t)
# t - t^2 = t * (1 - t)
# log(t - t^2) = log(t) + log(1 - t)

p3 = cp.Problem(
    cp.Minimize(cp.norm(X3)), [
    1 <= t3,
    K * x3 <= k,
    V * x3 <= v * t3,

    # A * x3 <= a * t3 ** 2,

    # RLT
    x3 <= X3[0,1],
    t3 <= X3[1,1],

    K * X3[0,0] <= k * x3,
    K * X3[0,1] <= k * t3,

    V * X3[0,0] <= k * X3[0,1],
    V * X3[0,1] <= k * X3[1,1],

    A * x3 <= a * X3[1,1],
    
    # SDP Shor
    a3.T @ v3 <= cp.trace(A3 @ X3),
    Z3[0, 0] == X3[0, 0],
    Z3[0, 1] == X3[0, 1],
    Z3[0, 2] == x3,
    Z3[1, 0] == X3[1, 0],
    Z3[1, 1] == X3[1, 1],
    Z3[1, 2] == t3,
    Z3[2, 0] == x3,
    Z3[2, 1] == t3,
    Z3[2, 2] == 1,
    Z3 >> 0,
])
p3.solve()
print(p3.status)
print(p3.value)
print(x3.value, t3.value)
print(v3.value)
print(X3.value)
print(v3.value @ v3.value.T)
print(K * x3.value, k, K * x3.value <= k) 
print(V * x3.value, v * t3.value, V * x3.value <= v * t3.value)
print(A * x3.value, a * t3.value ** 2, A * x3.value <= a * t3.value ** 2)
print(np.linalg.eigvals(v3.value @ v3.value.T))
print(np.linalg.eigvals(X3.value))
print(np.linalg.matrix_rank(X3.value))
