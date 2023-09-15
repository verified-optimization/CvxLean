import cvxpy as cp

def almostdgp1():
    x1 = cp.Variable(pos=True)

    agp1 = cp.Problem(
        cp.Minimize(x1), [
            x1 ** 2 - 10.123 <= 0,
        ])

    print("agp1.is_dgp():")
    print(agp1.is_dgp())
    # False

    print("agp1.is_dcp():")
    print(agp1.is_dcp())
    # True

def almostdgp2():
    x2 = cp.Variable(pos=True)
    y2 = cp.Variable(pos=True)

    agp2 = cp.Problem(
        cp.Minimize(x2), [
            x2 * y2 - 5.382 <= 0,
        ])

    print("agp2.is_dgp():")
    print(agp2.is_dgp())
    # False

    print("agp2.is_dcp():")
    print(agp2.is_dcp())
    # False

def almostdgp3():
    x3 = cp.Variable(pos=True)
    y3 = cp.Variable(pos=True)
    z3 = cp.Variable(pos=True)

    agp3 = cp.Problem(
        cp.Minimize(x3 + y3 + z3), [
            2 <= x3, 
            x3 <= 3,
            cp.sqrt(x3) <= x3 ** 2 - 6 * y3 / z3,
            x3 * y3 == z3,
        ])

    print("agp3.is_dgp():")
    print(agp3.is_dgp())
    # False

    print("agp3.is_dcp():")
    print(agp3.is_dcp())    
    # False

def almostdgp4():
    x4 = cp.Variable(pos=True)
    y4 = cp.Variable(pos=True)

    agp4 = cp.Problem(
        cp.Minimize(1 / (x4 * y4)), [
            x4 * y4 <= 2 - x4 - y4,
        ])

    print("agp4.is_dgp():")
    print(agp4.is_dgp())
    # False

    print("agp4.is_dcp():")
    print(agp4.is_dcp())
    # False

def almostdgp5():
    x5 = cp.Variable(pos=True)
    y5 = cp.Variable(pos=True)

    agp5 = cp.Problem(
        cp.Minimize(x5 * y5), [
            x5 * y5 <= 2 + x5 - y5,
        ])

    print("agp5.is_dgp():")
    print(agp5.is_dgp())
    # False

    print("agp5.is_dcp():")
    print(agp5.is_dcp())
    # False

def almostdgp6():
    x6 = cp.Variable(pos=True)
    y6 = cp.Variable(pos=True)

    agp6 = cp.Problem(
        cp.Minimize(x6), [
            cp.sqrt (x6 * x6 - y6) <= 1,
        ])

    print("agp6.is_dgp():")
    print(agp6.is_dgp())
    # False

    print("agp6.is_dcp():")
    print(agp6.is_dcp())
    # False


if __name__ == "__main__":
    almostdgp1()
    almostdgp2()
    almostdgp3()
    almostdgp4()
    almostdgp5()
    almostdgp6()
