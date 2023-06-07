import cvxpy as cp

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
print(x1.value)

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
