import cvxpy as cp 
import numpy as np

hmin = 1
hmax = 100
wmin = 1
wmax = 100
Rmax = 10
sigma = 0.5
f1 = 10
f2 = 20

h = cp.Variable(pos=True)
w = cp.Variable(pos=True)
r = cp.Variable(pos=True)
A = cp.Variable(pos=True)

p = cp.Problem(
    cp.Minimize(2 * A * cp.sqrt(cp.square(w) + cp.square(h))), [
        f1 * cp.sqrt(cp.square(w) + cp.square(h)) / (2 * h) <= sigma * A,
        f2 * cp.sqrt(cp.square(w) + cp.square(h)) / (2 * w) <= sigma * A,
        hmin <= h,
        h <= hmax,
        wmin <= w,
        w <= wmax,
        0.21 * cp.square(r) <= A / (2 * np.pi),
        cp.sqrt(A / (2 * np.pi) + cp.square(r)) <= Rmax
    ])

p.solve(gp=True, verbose=True)

h_opt = h.value
w_opt = w.value
r_opt = r.value
R_opt = np.sqrt(A.value / (2 * np.pi) + r_opt ** 2)

print('h* = ', h_opt)
print('w* = ', w_opt)
print('r* = ', r_opt)
print('R* = ', R_opt)

value = 2 * A.value * np.sqrt(w_opt ** 2 + h_opt ** 2)

print('val = ', value)
