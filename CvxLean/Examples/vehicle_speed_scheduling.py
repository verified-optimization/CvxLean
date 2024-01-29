import numpy as np
import cvxpy as cp

n = 10

d = np.array(
    [1.9501, 1.2311, 1.6068, 1.4860, 1.8913, 1.7621, 1.4565, 1.0185, 1.8214, 1.4447])

tau_min = np.array(
    [1.0809, 2.7265, 3.5118, 5.3038, 5.4516, 7.1648, 9.2674, 12.1543, 14.4058, 16.6258])

tau_max = np.array(
    [4.6528, 6.5147, 7.5178, 9.7478, 9.0641, 10.3891, 13.1540, 16.0878, 17.4352, 20.9539])

smin = np.array(
    [0.7828, 0.6235, 0.7155, 0.5340, 0.6329, 0.4259, 0.7798, 0.9604, 0.7298, 0.8405])

smax = np.array(
    [1.9624, 1.6036, 1.6439, 1.5641, 1.7194, 1.9090, 1.3193, 1.3366, 1.9470, 2.8803])

a = 1
b = 6 
c = 10

t = cp.Variable(shape=(n))

p = cp.Problem(
    cp.Minimize(cp.sum(a * (d ** 2) * cp.inv_pos(t) + b * d + c * t)), (
        [t <= d / smin] + 
        [t >= d / smax] + 
        [tau_min[i] <= cp.sum(t[0:i+1]) for i in range(n)] +
        [tau_max[i] >= cp.sum(t[0:i+1]) for i in range(n)]))

p.solve(verbose=True)

s = d / t.value

print("t* = ", t.value)
print("s* = ", s)
