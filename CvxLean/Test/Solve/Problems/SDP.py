import cvxpy as cp
import numpy as np

A1 = [ [23.90853599,  0.40930502]
     , [ 0.79090389, 21.30303590] ]
A1 = np.array(A1)

b1 = 8.0
b1 = np.array(b1)

C1 = [ [0.31561605, 0.97905625]
     , [0.84321261, 0.06878862] ]
C1 = np.array(C1)

X1 = cp.Variable((2, 2), symmetric=True)

sdp1 = cp.Problem(
    cp.Minimize(cp.trace(C1 @ X1)), [
    cp.trace(A1 @ X1) <= b1,
    X1 >> 0
])
sdp1.solve()

print(f"sdp1.status   : {sdp1.status}.") # optimal
print(f"sdp1.value    : {sdp1.value}." ) # -0.2667541199350546
print(f"sdp1.solution : {X1.value}."   ) # [[ 0.15121766 -0.18073041] [-0.18073041  0.21600308]]
