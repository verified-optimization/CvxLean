import cvxpy as cp

X1 = cp.Variable((2,2), symmetric=True)

logDet1 = cp.Problem(
    cp.Minimize(cp.trace(X1)), [
    10 <= cp.log_det(X1),
    X1 >> 0
])
logDet1.solve()

print(f"logDet1.status   : {logDet1.status}.") # optimal
print(f"logDet1.value    : {logDet1.value}." ) # 296.82631237843924.
print(f"logDet1.solution : {X1.value}."      ) # [[ 1.48416184e+02 -3.19252032e-13] [-3.19252032e-13  1.48410129e+02]]

X2 = cp.Variable((2,2), symmetric=True)

logDet2 = cp.Problem(
    cp.Maximize(cp.log_det(X2)), [
    X2[0, 0] + X2[0, 1] + X2[1, 1] <= 50,
    X2 >> 0
])
logDet2.solve()

print(f"logDet2.status   : {logDet2.status}.") # optimal
print(f"logDet2.value    : {logDet2.value}." ) # 6.7254336786986855
print(f"logDet2.solution : {X2.value}."      ) # [[ 33.33222217 -16.66539609 ] [-16.66539609  33.33317288 ]]
