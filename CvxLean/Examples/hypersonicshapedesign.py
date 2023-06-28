import cvxpy as cp
import math

x = cp.Variable(pos=True)

a = 0.05 
b = 0.65 

obj = cp.sqrt(cp.inv_pos(cp.square(x)) - 1)
p = cp.Problem(
    cp.Minimize(obj), [
        a * cp.inv_pos(x) - (1 - b) * cp.sqrt(1 - cp.square(x)) <= 0
    ])
p.solve(qcp=True, solver='MOSEK')

print(p.value)
print(x.value)

print('Final L/D Ratio = ', 1/obj.value)
print('Final width of wedge = ', x.value)
print('Final height of wedge = ', math.sqrt(1 - (x.value ** 2)))

x2 = cp.Variable(pos=True)

obj2 = (x2 ** (-2)) - 1
p2 = cp.Problem(
    cp.Minimize(obj2), [
        x2 <= 1,
        (a ** 2) * (x2 ** (-2)) + (1 - b) ** 2 * (x2 ** 2) <= (1 - b) ** 2
    ])
p2.solve(solver='MOSEK')

print(p2.value)
print(x2.value)
print('Final L/D Ratio = ', 1/math.sqrt(obj2.value))
print('Final width of wedge = ', x2.value)
print('Final height of wedge = ', math.sqrt(1 - (x2.value ** 2)))

