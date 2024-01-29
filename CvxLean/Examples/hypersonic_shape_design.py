import cvxpy as cp 
import numpy as np

a = .05 # height of rectangle

b = .65 # width of rectangle

x = cp.Variable(pos=True)

obj = cp.sqrt(cp.inv_pos(cp.square(x)) - 1)

p = cp.Problem(
    cp.Minimize(obj), [
        a * cp.inv_pos(x) - (1 - b) * cp.sqrt(1 - cp.square(x)) <= 0
    ])

p.solve(qcp=True, verbose=True)

print('QCP Final L/D Ratio = ', 1 / obj.value)
print('QCP Final width of wedge = ', x.value)
print('QCP Final height of wedge = ', np.sqrt(1 - x.value ** 2))

x = cp.Variable(pos=True)

obj = cp.power(x, -2) - 1

p = cp.Problem(
    cp.Minimize(obj), [
        a * cp.inv_pos(x) - (1 - b) * cp.sqrt(1 - cp.square(x)) <= 0
    ])

p.solve(verbose=True)

print('DCP Final L/D Ratio = ', 1 / np.sqrt(obj.value))
print('DCP Final width of wedge = ', x.value)
print('DCP Final height of wedge = ', np.sqrt(1 - x.value ** 2))


