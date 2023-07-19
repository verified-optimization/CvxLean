import cvxpy as cp
import numpy as np

sigma = 0.1
F1 = 10
F2 = 10
hmin = 1
hmax = 100
wmin = 1
wmax = 100
Rmax = 20

h = cp.Variable(pos=True)
w = cp.Variable(pos=True)
A = cp.Variable(pos=True)
r = cp.Variable(pos=True)

p = cp.Problem(
    cp.Minimize(2 * A * cp.sqrt(w ** 2 + h ** 2)), [
        F1 * cp.sqrt(w ** 2 + h ** 2) / (2 * h) <= sigma * A,
        F2 * cp.sqrt(w ** 2 + h ** 2) / (2 * w) <= sigma * A,
        wmin <= w,
        w <= wmax,
        hmin <= h,
        h <= hmax,
        #1.1 * r <= cp.sqrt(A / (2 * np.pi) + r ** 2),
        0.21 * r ** 2 <= A / (2 * np.pi),
        cp.sqrt(A / (2 * np.pi) + r ** 2) <= Rmax
    ])
p.solve(gp=True, solver='MOSEK')

print("Optimal value: ", p.value)
print("Optimal var: ", w.value, h.value, A.value, r.value)
print("R = ", np.sqrt(A.value / (2 * np.pi) + r.value ** 2))
