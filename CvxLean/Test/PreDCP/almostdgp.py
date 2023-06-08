import cvxpy as cp

def almostdgp1():
    x1 = cp.Variable(pos=True)

    agp1 = cp.Problem(
        cp.Minimize(x1), [
            x1 ** 2 <= -10.123,
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
            x2 * y2 <= -5.382,
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
        cp.Minimize(x3 / y3), [
            2 <= x3, 
            x3 <= 3,
            x3 ** 2 <= cp.sqrt(x3) - 6 * y3 / z3,
            x3 * y3 == z3,
        ])

    print("agp3.is_dgp():")
    print(agp3.is_dgp())
    # False

    print("agp3.is_dcp():")
    print(agp3.is_dcp())
    # False

if __name__ == "__main__":
    almostdgp1()
    almostdgp2()
    almostdgp3()
