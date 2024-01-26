import numpy as np
import cvxpy as cp

n = 2

N = 4

alpha = 1

Y = np.array([[0, 2], [2, 0], [-2, 0], [0, -2]])

R = cp.Variable(shape=(n, n), PSD=True)

def covMat(X):
    # TODO: Different from np.cov(X, rowvar=False) ?
    (N, n) = X.shape
    res = np.zeros((n, n))
    for i in range(n):
        for j in range(n):
            res[i, j] = np.sum([X[k, i] * X[k, j] for k in range(N)]) / N
    return res

p = cp.Problem(
    cp.Minimize(
            -(-(N * np.log(np.sqrt((2 * np.pi) ** n)) + (N * (-cp.log_det(R) / 2))) +
            -(N * cp.trace(covMat(Y) * cp.transpose(R)) / 2))
        ), [
        cp.sum(cp.abs(R)) <= alpha
    ])
p.solve(solver=cp.MOSEK, verbose=True)

print("R* = ", R.value)
