import cvxpy as cp
import numpy as np

def dgp1():
    x = cp.Variable(pos=True)

    gp1 = cp.Problem(
        cp.Minimize(x), [
            x ** 2 <= 10.123,
        ])

    dcp1 = cp.Dgp2Dcp(gp1).reduce()

    print(dcp1)

def dgp2():
    x = cp.Variable(pos=True)
    y = cp.Variable(pos=True)

    gp2 = cp.Problem(
        cp.Minimize(x), [
            x * y <= 5.382,
        ])

    dcp2 = cp.Dgp2Dcp(gp2).reduce()

    print(dcp2)

def dgp3():
    x = cp.Variable(pos=True)
    y = cp.Variable(pos=True)

    gp3 = cp.Problem(
        cp.Minimize(x), [
            cp.sqrt (x * x + y) <= 1,
        ])

    dcp3 = cp.Dgp2Dcp(gp3).reduce()

    print(dcp3)

def dgp4():
    # x, y, z = cvxpy.Variable((3,), pos=True)
    #     constraints = [2*x*y + 2*x*z + 2*y*z <= 1.0, x >= 2*y]
    #     problem = cvxpy.Problem(cvxpy.Minimize(1/(x*y*z)), constraints)
    x4 = cp.Variable(pos=True)
    y4 = cp.Variable(pos=True)
    z4 = cp.Variable(pos=True)

    gp4 = cp.Problem(
        cp.Maximize(x4 / y4), [
            2 <= x4, 
            x4 <= 3,
            x4 ** 2 + 6 * y4 / z4 <= cp.sqrt(x4),
            x4 * y4 == z4,
        ])

    dcp4 = cp.Dgp2Dcp(gp4).reduce()

    print(dcp4)

def dgp5():
    pass 

def dgp6():
    pass 

def dgp7():
    pass 

def dgp8():
    pass

def dgp9():
    pass

def dgp10():
    pass

def dgp11():
    pass

def dgp12():
    pass

def dgp13():
    pass

def dgp14():
    pass

def dgp15():
    pass

def dgp16():
    pass

def dgp17():
    pass

def dgp18():
    pass

def dgp19():
    pass

def dgp20():
    pass


# prod1 = x * y**0.5
# prod2 = 3.0 * x * y**0.5
# obj = cvxpy.Minimize(cvxpy.max(cvxpy.hstack([prod1, prod2])))
# constr = [x == 1.0, y == 4.0]
# dgp = cvxpy.Problem(obj, constr)

# x = cvxpy.Variable(pos=True)
#         y = cvxpy.Variable(pos=True)
#         p = cvxpy.Problem(cvxpy.Minimize(x * y),
#                           [y/3 <= x, y >= 1])
#         self.assertAlmostEqual(p.solve(SOLVER, gp=True), 1.0 / 3.0)

# x = cvxpy.Variable(pos=True)
#         obj = cvxpy.Maximize(x)
#         constr = [cvxpy.one_minus_pos(x) >= 0.4]
#         problem = cvxpy.Problem(obj, constr)
#         problem.solve(SOLVER, gp=True)
#         self.assertAlmostEqual(problem.value, 0.6)
#         self.assertAlmostEqual(x.value, 0.6)

def dgpBox():
    A_wall = 100
    A_flr = 10
    alpha = 0.5
    beta = 2
    gamma = 0.5
    delta = 2

    h = cp.Variable(pos=True)
    w = cp.Variable(pos=True)
    d = cp.Variable(pos=True)

    gpBox = cp.Problem(
        cp.Maximize(h * w * d), [ 
            2 * (h * w + h * d) <= A_wall,
            w * d <= A_flr,
            alpha <= h / w,
            h / w <= beta,
            gamma <= d / w,
            d / w <= delta,
        ])

    dcpBox = cp.Dgp2Dcp(gpBox).reduce()

    print(dcpBox)

def dgpTut1():
    x = cp.Variable(pos=True)
    y = cp.Variable(pos=True)
    z = cp.Variable(pos=True)

    gpTut1 = cp.Problem(
        cp.Minimize(x / y), [
            2 <= x, 
            x <= 3,
            x ** 2 + 6 * y / z <= cp.sqrt(x),
            x * y == z,
        ])

    dcpTut1 = cp.Dgp2Dcp(gpTut1).reduce()

    print(dcpTut1)

def dgpTut2():
    x = cp.Variable(pos=True)
    y = cp.Variable(pos=True)
    z = cp.Variable(pos=True)

    gpTut2 = cp.Problem(
        cp.Minimize((x ** (-1)) * (y ** (1 / 2)) * (z ** (-1)) + 2.3 * x * z + 4 * x * y * z), [
            (1 / 3) * (x ** (-2)) * (y ** (-2)) + (4 / 3) * (y ** (1 / 2)) * (z ** (-1)) <= 1,
            x + 2 * y + 3 * z <= 1,
            (1 / 2) * x * y == 1,
        ])

    dcpTut2 = cp.Dgp2Dcp(gpTut2).reduce()

    print(dcpTut2)


if __name__ == "__main__":
    dgp1()
    dgp2()
    dgp3()
    dgp4()
    dgp5()
    dgp6()
    dgp7()
