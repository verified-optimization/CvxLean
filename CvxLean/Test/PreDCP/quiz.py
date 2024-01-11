import cvxpy as cp

def quiz1():
    x = cp.Variable(pos=True)

    quiz1 = cp.inv_pos(cp.inv_pos(x))

    assert(not quiz1.is_dcp())

def quiz2():
    x = cp.Variable(pos=True)
    y = cp.Variable(pos=True)

    quiz2 = cp.inv_pos(cp.inv_pos(x) + cp.inv_pos(y))

    assert(not quiz2.is_dcp())

def quiz3():
    x = cp.Variable(pos=True)

    quiz3 = cp.power(cp.sqrt(x), 2)

    assert(not quiz3.is_dcp())

def quiz4():
    x = cp.Variable(pos=True)

    quiz4 = -cp.abs(cp.sqrt(cp.abs(x)))

    assert(not quiz4.is_dcp())

def quiz5():
    x = cp.Variable()
    
    quiz5 = 1 / cp.exp(x)

    assert(not quiz5.is_dcp())

def quiz6():
    x = cp.Variable(pos=True)

    quiz6 = -cp.log(cp.power(364 * x, 2))

    assert(not quiz6.is_dcp())

def quiz7():
    x = cp.Variable(pos=True)

    quiz7 = cp.power(cp.geo_mean(cp.vstack([x + 2, 1 / x])), 2)

    assert(not quiz7.is_dcp())

def quiz8():
    x = cp.Variable(pos=True)

    quiz8 = -cp.log(cp.abs(x))

    assert(not quiz8.is_dcp())

def quiz9():
    x = cp.Variable(pos=True)
    y = cp.Variable(pos=True)

    quiz9 = 1 / cp.quad_over_lin(1 / x, 1 / y)

    assert(not quiz9.is_dcp())

def quiz10():
    x = cp.Variable()

    quiz10 = cp.power(cp.log(cp.exp(x)), 2)

    assert(not quiz10.is_dcp())

if __name__ == "__main__":
    quiz1()
    quiz2()
    quiz3()
    quiz4()
    quiz5()
    quiz6()
    quiz7()
    quiz8()
    quiz9()
    quiz10()
