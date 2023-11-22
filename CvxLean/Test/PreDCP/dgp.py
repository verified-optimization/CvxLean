import cvxpy as cp

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
    x5 = cp.Variable(pos=True)
    y5 = cp.Variable(pos=True)
    z5 = cp.Variable(pos=True)

    gp5 = cp.Problem(
        cp.Maximize(x5 / y5), [
            2 <= x5, 
            x5 <= 3,
            x5 ** 2 + 6 * y5 / z5 <= cp.sqrt(x5),
            x5 * y5 == z5 ** 2,
        ])

    dcp5 = cp.Dgp2Dcp(gp5).reduce()

    print(dcp5)

def dgp6():
    A_wall = 100
    A_flr = 10
    alpha = 0.5
    beta = 2
    gamma = 0.5
    delta = 2

    h = cp.Variable(pos=True)
    w = cp.Variable(pos=True)
    d = cp.Variable(pos=True)

    gp6 = cp.Problem(
        cp.Maximize(h * w * d), [ 
            2 * (h * w + h * d) <= A_wall,
            w * d <= A_flr,
            alpha <= h / w,
            h / w <= beta,
            gamma <= d / w,
            d / w <= delta,
        ])

    dcp6 = cp.Dgp2Dcp(gp6).reduce()

    print(dcp6)

def dgp7():
    x = cp.Variable(pos=True)
    y = cp.Variable(pos=True)
    z = cp.Variable(pos=True)

    gp6 = cp.Problem(
        cp.Minimize((x ** (-1)) * (y ** (1 / 2)) * (z ** (-1)) + 2.3 * x * z + 4 * x * y * z), [
            (1 / 3) * (x ** (-2)) * (y ** (-2)) + (4 / 3) * (y ** (1 / 2)) * (z ** (-1)) <= 1,
            x + 2 * y + 3 * z <= 1,
            (1 / 2) * x * y == 1,
        ])

    dcp6 = cp.Dgp2Dcp(gp6).reduce()

    print(dcp6)


if __name__ == "__main__":
    dgp1()
    dgp2()
    dgp3()
    dgp4()
    dgp5()
    dgp6()
    dgp7()
