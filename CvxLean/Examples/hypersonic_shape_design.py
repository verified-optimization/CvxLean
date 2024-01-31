import cvxpy as cp 
import numpy as np

a = .05

b = .65

x = cp.Variable(pos=True)

obj = cp.sqrt(cp.inv_pos(cp.square(x)) - 1)

p = cp.Problem(
    cp.Minimize(obj), [
        a * cp.inv_pos(x) - (1 - b) * cp.sqrt(1 - cp.square(x)) <= 0
    ])

p.solve(qcp=True, verbose=True)

print('QCP w* = ', x.value)
print('QCP h* = ', np.sqrt(1 - x.value ** 2))
print('QCP L/D Ratio = ', 1 / obj.value)

x = cp.Variable(pos=True)

obj = cp.power(x, -2) - 1

p = cp.Problem(
    cp.Minimize(obj), [
        a * cp.inv_pos(x) - (1 - b) * cp.sqrt(1 - cp.square(x)) <= 0
    ])

p.solve(verbose=True)

print('DCP w* = ', x.value)
print('DCP h* = ', np.sqrt(1 - x.value ** 2))
print('DCP L/D Ratio = ', 1 / np.sqrt(obj.value))
