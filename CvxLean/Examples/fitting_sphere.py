import numpy as np
import cvxpy as cp
import matplotlib.pyplot as plt

n = 2

m = 10

x = np.array([[
    1.824183228637652032e+00, 1.349093690455489103e+00, 6.966316403935147727e-01,
    7.599387854623529392e-01, 2.388321695850912363e+00, 8.651370608981923116e-01,
    1.863922545015865406e+00, 7.099743941474848663e-01, 6.005484882320809570e-01,
    4.561429569892232472e-01], [
    -9.644136284187876385e-01, 1.069547315003422927e+00, 6.733229334437943470e-01,
    7.788072961810316164e-01, -9.467465278344706636e-01, -8.591303443863639311e-01,
    1.279527420871080956e+00, 5.314829019311283487e-01, 6.975676079749143499e-02,
    -4.641873429414754559e-01]]).T

c = cp.Variable((n))
t = cp.Variable(1)

p = cp.Problem(
    cp.Minimize(
            cp.sum([((cp.norm(x[i]) ** 2) - 2 * (x[i] @ c) - t) ** 2 for i in range(m)])
        ), [])
p.solve(solver=cp.MOSEK, verbose=True)

# Backward map from change of variables.
r = np.sqrt(t.value + (np.linalg.norm(c.value) ** 2))

print("t* = ", t.value)
print("c* = ", c.value)
print("r* = ", r)

def plot_circle_and_points(center, radius, points):
    theta = np.linspace(0, 2 * np.pi, 100)
    x_circle = center[0] + radius * np.cos(theta)
    y_circle = center[1] + radius * np.sin(theta)

    plt.plot(x_circle, y_circle, label='Circle')

    plt.scatter(points[:, 0], points[:, 1], color='red')

    plt.axis('equal')
    
    plt.show()
    plt.savefig('plots/fitting_sphere.png')

plot_circle_and_points(c.value, r, x)
