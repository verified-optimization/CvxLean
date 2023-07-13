import cvxpy as cp
import numpy as np

def dgp1():
    x1 = cp.Variable(pos=True)

    gp1 = cp.Problem(
        cp.Minimize(x1), [
            x1 ** 2 <= 10.123,
        ])

    dcp1 = cp.Dgp2Dcp(gp1).reduce()

    print(dcp1)
    # minimize var1
    # subject to 2.0 @ var1 <= 2.3148100626166146

def dgp2():
    x2 = cp.Variable(pos=True)
    y2 = cp.Variable(pos=True)

    gp2 = cp.Problem(
        cp.Minimize(x2), [
            x2 * y2 <= 5.382,
        ])

    dcp2 = cp.Dgp2Dcp(gp2).reduce()

    print(dcp2)
    # minimize var11
    # subject to var11 + var12 <= 1.6830600523047141

def dgp3():
    x3 = cp.Variable(pos=True)
    y3 = cp.Variable(pos=True)
    z3 = cp.Variable(pos=True)

    gp3 = cp.Problem(
        cp.Minimize(x3 / y3), [
            2 <= x3, 
            x3 <= 3,
            x3 ** 2 + 6 * y3 / z3 <= cp.sqrt(x3),
            x3 * y3 == z3,
        ])

    dcp3 = cp.Dgp2Dcp(gp3).reduce()

    print(dcp3)
    # minimize var22 + -var23
    # subject to 0.6931471805599453 <= var22
    #            var22 <= 1.0986122886681098
    #            log_sum_exp(Hstack(reshape(2.0 @ var22, (1,), F), reshape(1.791759469228055 + var23 + -var24, (1,), F)), None, False) <= 0.5 @ var22
    #            var22 + var23 == var24

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
    # maximize var72 + -var73
    # subject to 0.6931471805599453 <= var72
    #            var72 <= 1.0986122886681098
    #            log_sum_exp(Hstack(reshape(2.0 @ var72, (1,), F), reshape(1.791759469228055 + var73 + -var74, (1,), F)), None, False) <= 0.5 @ var72
    #            var72 + var73 == var74

def dgp5():
    A_wall = 100
    A_flr = 10
    alpha = 0.5
    beta = 2
    gamma = 0.5
    delta = 2

    h = cp.Variable(pos=True)
    w = cp.Variable(pos=True)
    d = cp.Variable(pos=True)

    gp5 = cp.Problem(
        cp.Maximize(h * w * d), [ 
            2 * (h * w + h * d) <= A_wall,
            w * d <= A_flr,
            alpha <= h / w,
            h / w <= beta,
            gamma <= d / w,
            d / w <= delta,
        ])

    dcp5 = cp.Dgp2Dcp(gp5).reduce()

    print(dcp5)
    # maximize var122 + var123 + var124
    # subject to 0.6931471805599453 + log_sum_exp(Hstack(reshape(var122 + var123, (1,), F), reshape(var122 + var124, (1,), F)), None, False) <= 4.605170185988092
    #            var123 + var124 <= 2.302585092994046
    #            -0.6931471805599453 <= var122 + -var123
    #            var122 + -var123 <= 0.6931471805599453
    #            -0.6931471805599453 <= var124 + -var123
    #            var124 + -var123 <= 0.6931471805599453

def dgp6():
    x6 = cp.Variable(pos=True)
    y6 = cp.Variable(pos=True)
    z6 = cp.Variable(pos=True)

    gp6 = cp.Problem(
        cp.Minimize((x6 ** (-1)) * (y6 ** (1 / 2)) * (z6 ** (-1)) + 2.3 * x6 * z6 + 4 * x6 * y6 * z6), [
            (1 / 3) * (x6 ** (-2)) * (y6 ** (-2)) + (4 / 3) * (y6 ** (1 / 2)) * (z6 ** (-1)) <= 1,
            x6 + 2 * y6 + 3 * z6 <= 1,
            (1 / 2) * x6 * y6 == 1,
        ])

    dcp6 = cp.Dgp2Dcp(gp6).reduce()

    print(dcp6)
    # minimize log_sum_exp(Hstack(reshape(-1.0 @ var196 + 0.5 @ var197 + -1.0 @ var198, (1,), F), reshape(0.8329091229351039 + var196 + var198, (1,), F), reshape(1.3862943611198906 + var196 + var197 + var198, (1,), F)), None, False)
    # subject to log_sum_exp(Hstack(reshape(-1.0986122886681098 + -2.0 @ var196 + -2.0 @ var197, (1,), F), reshape(0.28768207245178085 + 0.5 @ var197 + -1.0 @ var198, (1,), F)), None, False) <= 0.0
    #            log_sum_exp(Hstack(reshape(var196, (1,), F), reshape(0.6931471805599453 + var197, (1,), F), reshape(1.0986122886681098 + var198, (1,), F)), None, False) <= 0.0
    #            -0.6931471805599453 + var196 + var197 == 0.0

def dgp7():
    n = 5
    sigma = 0.5 * np.ones(n)
    p_min = 0.1 * np.ones(n)
    p_max = 5 * np.ones(n)
    sinr_min = 0.2
    G = np.array(
       [[1.0, 0.1, 0.2, 0.1, 0.05],
        [0.1, 1.0, 0.1, 0.1, 0.05],
        [0.2, 0.1, 1.0, 0.2, 0.2],
        [0.1, 0.1, 0.2, 1.0, 0.1],
        [0.05, 0.05, 0.2, 0.1, 1.0]])
    
    p = cp.Variable(shape=(n,), pos=True)
    
    objective = cp.Minimize(cp.sum(p))

    S_p = []
    for i in range(n):
        S_p.append(cp.sum(cp.hstack(G[i, k]*p[k] for k in range(n) if i != k)))
    S = sigma + cp.hstack(S_p)
    signal_power = cp.multiply(cp.diag(G), p)
    inverse_sinr = S/signal_power
    constraints = [
        p >= p_min,
        p <= p_max,
        inverse_sinr <= (1/sinr_min),
    ]

    gp7 = cp.Problem(objective, constraints)

    dcp7 = cp.Dgp2Dcp(gp7).reduce()

    print(dcp7)
    # minimize reshape(log_sum_exp(Hstack(reshape(reshape(var283, (5,), F)[0], (1,), F), reshape(reshape(var283, (5,), F)[1:5][0], (1,), F), reshape(reshape(var283, (5,), F)[1:5][1], (1,), F), reshape(reshape(var283, (5,), F)[1:5][2], (1,), F), reshape(reshape(var283, (5,), F)[1:5][3], (1,), F)), None, False), (), F)
    # subject to [-2.30258509 -2.30258509 -2.30258509 -2.30258509 -2.30258509] <= var283
    #            var283 <= [1.60943791 1.60943791 1.60943791 1.60943791 1.60943791]
    #            reshape(Vstack(Hstack(reshape(log_sum_exp(Hstack(reshape([-0.69314718 -0.69314718 -0.69314718 -0.69314718 -0.69314718][0], (1,), F), reshape(Hstack(reshape(reshape(log_sum_exp(Hstack(reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F), reshape(-2.995732273553991 + var283[4], (1,), F)), (4,), F)[0], (1,), F), reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F), reshape(-2.995732273553991 + var283[4], (1,), F)), (4,), F)[1:4][0], (1,), F), reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F), reshape(-2.995732273553991 + var283[4], (1,), F)), (4,), F)[1:4][1], (1,), F), reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F), reshape(-2.995732273553991 + var283[4], (1,), F)), (4,), F)[1:4][2], (1,), F)), None, False), (), F), (1,), F), reshape(reshape(log_sum_exp(Hstack(reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F), reshape(-2.995732273553991 + var283[4], (1,), F)), (4,), F)[0], (1,), F), reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F), reshape(-2.995732273553991 + var283[4], (1,), F)), (4,), F)[1:4][0], (1,), F), reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F), reshape(-2.995732273553991 + var283[4], (1,), F)), (4,), F)[1:4][1], (1,), F), reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F), reshape(-2.995732273553991 + var283[4], (1,), F)), (4,), F)[1:4][2], (1,), F)), None, False), (), F), (1,), F), reshape(reshape(log_sum_exp(Hstack(reshape(reshape(Hstack(reshape(-1.6094379124341003 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[3], (1,), F), reshape(-1.6094379124341003 + var283[4], (1,), F)), (4,), F)[0], (1,), F), reshape(reshape(Hstack(reshape(-1.6094379124341003 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[3], (1,), F), reshape(-1.6094379124341003 + var283[4], (1,), F)), (4,), F)[1:4][0], (1,), F), reshape(reshape(Hstack(reshape(-1.6094379124341003 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[3], (1,), F), reshape(-1.6094379124341003 + var283[4], (1,), F)), (4,), F)[1:4][1], (1,), F), reshape(reshape(Hstack(reshape(-1.6094379124341003 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[3], (1,), F), reshape(-1.6094379124341003 + var283[4], (1,), F)), (4,), F)[1:4][2], (1,), F)), None, False), (), F), (1,), F), reshape(reshape(log_sum_exp(Hstack(reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[4], (1,), F)), (4,), F)[0], (1,), F), reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[4], (1,), F)), (4,), F)[1:4][0], (1,), F), reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[4], (1,), F)), (4,), F)[1:4][1], (1,), F), reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[4], (1,), F)), (4,), F)[1:4][2], (1,), F)), None, False), (), F), (1,), F), reshape(reshape(log_sum_exp(Hstack(reshape(reshape(Hstack(reshape(-2.995732273553991 + var283[0], (1,), F), reshape(-2.995732273553991 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F)), (4,), F)[0], (1,), F), reshape(reshape(Hstack(reshape(-2.995732273553991 + var283[0], (1,), F), reshape(-2.995732273553991 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F)), (4,), F)[1:4][0], (1,), F), reshape(reshape(Hstack(reshape(-2.995732273553991 + var283[0], (1,), F), reshape(-2.995732273553991 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F)), (4,), F)[1:4][1], (1,), F), reshape(reshape(Hstack(reshape(-2.995732273553991 + var283[0], (1,), F), reshape(-2.995732273553991 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F)), (4,), F)[1:4][2], (1,), F)), None, False), (), F), (1,), F))[0], (1,), F)), None, False), (1,), F)), Hstack(reshape(log_sum_exp(Hstack(reshape([-0.69314718 -0.69314718 -0.69314718 -0.69314718 -0.69314718][1], (1,), F), reshape(Hstack(reshape(reshape(log_sum_exp(Hstack(reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F), reshape(-2.995732273553991 + var283[4], (1,), F)), (4,), F)[0], (1,), F), reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F), reshape(-2.995732273553991 + var283[4], (1,), F)), (4,), F)[1:4][0], (1,), F), reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F), reshape(-2.995732273553991 + var283[4], (1,), F)), (4,), F)[1:4][1], (1,), F), reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F), reshape(-2.995732273553991 + var283[4], (1,), F)), (4,), F)[1:4][2], (1,), F)), None, False), (), F), (1,), F), reshape(reshape(log_sum_exp(Hstack(reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F), reshape(-2.995732273553991 + var283[4], (1,), F)), (4,), F)[0], (1,), F), reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F), reshape(-2.995732273553991 + var283[4], (1,), F)), (4,), F)[1:4][0], (1,), F), reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F), reshape(-2.995732273553991 + var283[4], (1,), F)), (4,), F)[1:4][1], (1,), F), reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F), reshape(-2.995732273553991 + var283[4], (1,), F)), (4,), F)[1:4][2], (1,), F)), None, False), (), F), (1,), F), reshape(reshape(log_sum_exp(Hstack(reshape(reshape(Hstack(reshape(-1.6094379124341003 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[3], (1,), F), reshape(-1.6094379124341003 + var283[4], (1,), F)), (4,), F)[0], (1,), F), reshape(reshape(Hstack(reshape(-1.6094379124341003 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[3], (1,), F), reshape(-1.6094379124341003 + var283[4], (1,), F)), (4,), F)[1:4][0], (1,), F), reshape(reshape(Hstack(reshape(-1.6094379124341003 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[3], (1,), F), reshape(-1.6094379124341003 + var283[4], (1,), F)), (4,), F)[1:4][1], (1,), F), reshape(reshape(Hstack(reshape(-1.6094379124341003 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[3], (1,), F), reshape(-1.6094379124341003 + var283[4], (1,), F)), (4,), F)[1:4][2], (1,), F)), None, False), (), F), (1,), F), reshape(reshape(log_sum_exp(Hstack(reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[4], (1,), F)), (4,), F)[0], (1,), F), reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[4], (1,), F)), (4,), F)[1:4][0], (1,), F), reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[4], (1,), F)), (4,), F)[1:4][1], (1,), F), reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[4], (1,), F)), (4,), F)[1:4][2], (1,), F)), None, False), (), F), (1,), F), reshape(reshape(log_sum_exp(Hstack(reshape(reshape(Hstack(reshape(-2.995732273553991 + var283[0], (1,), F), reshape(-2.995732273553991 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F)), (4,), F)[0], (1,), F), reshape(reshape(Hstack(reshape(-2.995732273553991 + var283[0], (1,), F), reshape(-2.995732273553991 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F)), (4,), F)[1:4][0], (1,), F), reshape(reshape(Hstack(reshape(-2.995732273553991 + var283[0], (1,), F), reshape(-2.995732273553991 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F)), (4,), F)[1:4][1], (1,), F), reshape(reshape(Hstack(reshape(-2.995732273553991 + var283[0], (1,), F), reshape(-2.995732273553991 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F)), (4,), F)[1:4][2], (1,), F)), None, False), (), F), (1,), F))[1], (1,), F)), None, False), (1,), F)), Hstack(reshape(log_sum_exp(Hstack(reshape([-0.69314718 -0.69314718 -0.69314718 -0.69314718 -0.69314718][2], (1,), F), reshape(Hstack(reshape(reshape(log_sum_exp(Hstack(reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F), reshape(-2.995732273553991 + var283[4], (1,), F)), (4,), F)[0], (1,), F), reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F), reshape(-2.995732273553991 + var283[4], (1,), F)), (4,), F)[1:4][0], (1,), F), reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F), reshape(-2.995732273553991 + var283[4], (1,), F)), (4,), F)[1:4][1], (1,), F), reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F), reshape(-2.995732273553991 + var283[4], (1,), F)), (4,), F)[1:4][2], (1,), F)), None, False), (), F), (1,), F), reshape(reshape(log_sum_exp(Hstack(reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F), reshape(-2.995732273553991 + var283[4], (1,), F)), (4,), F)[0], (1,), F), reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F), reshape(-2.995732273553991 + var283[4], (1,), F)), (4,), F)[1:4][0], (1,), F), reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F), reshape(-2.995732273553991 + var283[4], (1,), F)), (4,), F)[1:4][1], (1,), F), reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F), reshape(-2.995732273553991 + var283[4], (1,), F)), (4,), F)[1:4][2], (1,), F)), None, False), (), F), (1,), F), reshape(reshape(log_sum_exp(Hstack(reshape(reshape(Hstack(reshape(-1.6094379124341003 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[3], (1,), F), reshape(-1.6094379124341003 + var283[4], (1,), F)), (4,), F)[0], (1,), F), reshape(reshape(Hstack(reshape(-1.6094379124341003 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[3], (1,), F), reshape(-1.6094379124341003 + var283[4], (1,), F)), (4,), F)[1:4][0], (1,), F), reshape(reshape(Hstack(reshape(-1.6094379124341003 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[3], (1,), F), reshape(-1.6094379124341003 + var283[4], (1,), F)), (4,), F)[1:4][1], (1,), F), reshape(reshape(Hstack(reshape(-1.6094379124341003 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[3], (1,), F), reshape(-1.6094379124341003 + var283[4], (1,), F)), (4,), F)[1:4][2], (1,), F)), None, False), (), F), (1,), F), reshape(reshape(log_sum_exp(Hstack(reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[4], (1,), F)), (4,), F)[0], (1,), F), reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[4], (1,), F)), (4,), F)[1:4][0], (1,), F), reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[4], (1,), F)), (4,), F)[1:4][1], (1,), F), reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[4], (1,), F)), (4,), F)[1:4][2], (1,), F)), None, False), (), F), (1,), F), reshape(reshape(log_sum_exp(Hstack(reshape(reshape(Hstack(reshape(-2.995732273553991 + var283[0], (1,), F), reshape(-2.995732273553991 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F)), (4,), F)[0], (1,), F), reshape(reshape(Hstack(reshape(-2.995732273553991 + var283[0], (1,), F), reshape(-2.995732273553991 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F)), (4,), F)[1:4][0], (1,), F), reshape(reshape(Hstack(reshape(-2.995732273553991 + var283[0], (1,), F), reshape(-2.995732273553991 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F)), (4,), F)[1:4][1], (1,), F), reshape(reshape(Hstack(reshape(-2.995732273553991 + var283[0], (1,), F), reshape(-2.995732273553991 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F)), (4,), F)[1:4][2], (1,), F)), None, False), (), F), (1,), F))[2], (1,), F)), None, False), (1,), F)), Hstack(reshape(log_sum_exp(Hstack(reshape([-0.69314718 -0.69314718 -0.69314718 -0.69314718 -0.69314718][3], (1,), F), reshape(Hstack(reshape(reshape(log_sum_exp(Hstack(reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F), reshape(-2.995732273553991 + var283[4], (1,), F)), (4,), F)[0], (1,), F), reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F), reshape(-2.995732273553991 + var283[4], (1,), F)), (4,), F)[1:4][0], (1,), F), reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F), reshape(-2.995732273553991 + var283[4], (1,), F)), (4,), F)[1:4][1], (1,), F), reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F), reshape(-2.995732273553991 + var283[4], (1,), F)), (4,), F)[1:4][2], (1,), F)), None, False), (), F), (1,), F), reshape(reshape(log_sum_exp(Hstack(reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F), reshape(-2.995732273553991 + var283[4], (1,), F)), (4,), F)[0], (1,), F), reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F), reshape(-2.995732273553991 + var283[4], (1,), F)), (4,), F)[1:4][0], (1,), F), reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F), reshape(-2.995732273553991 + var283[4], (1,), F)), (4,), F)[1:4][1], (1,), F), reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F), reshape(-2.995732273553991 + var283[4], (1,), F)), (4,), F)[1:4][2], (1,), F)), None, False), (), F), (1,), F), reshape(reshape(log_sum_exp(Hstack(reshape(reshape(Hstack(reshape(-1.6094379124341003 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[3], (1,), F), reshape(-1.6094379124341003 + var283[4], (1,), F)), (4,), F)[0], (1,), F), reshape(reshape(Hstack(reshape(-1.6094379124341003 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[3], (1,), F), reshape(-1.6094379124341003 + var283[4], (1,), F)), (4,), F)[1:4][0], (1,), F), reshape(reshape(Hstack(reshape(-1.6094379124341003 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[3], (1,), F), reshape(-1.6094379124341003 + var283[4], (1,), F)), (4,), F)[1:4][1], (1,), F), reshape(reshape(Hstack(reshape(-1.6094379124341003 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[3], (1,), F), reshape(-1.6094379124341003 + var283[4], (1,), F)), (4,), F)[1:4][2], (1,), F)), None, False), (), F), (1,), F), reshape(reshape(log_sum_exp(Hstack(reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[4], (1,), F)), (4,), F)[0], (1,), F), reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[4], (1,), F)), (4,), F)[1:4][0], (1,), F), reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[4], (1,), F)), (4,), F)[1:4][1], (1,), F), reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[4], (1,), F)), (4,), F)[1:4][2], (1,), F)), None, False), (), F), (1,), F), reshape(reshape(log_sum_exp(Hstack(reshape(reshape(Hstack(reshape(-2.995732273553991 + var283[0], (1,), F), reshape(-2.995732273553991 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F)), (4,), F)[0], (1,), F), reshape(reshape(Hstack(reshape(-2.995732273553991 + var283[0], (1,), F), reshape(-2.995732273553991 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F)), (4,), F)[1:4][0], (1,), F), reshape(reshape(Hstack(reshape(-2.995732273553991 + var283[0], (1,), F), reshape(-2.995732273553991 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F)), (4,), F)[1:4][1], (1,), F), reshape(reshape(Hstack(reshape(-2.995732273553991 + var283[0], (1,), F), reshape(-2.995732273553991 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F)), (4,), F)[1:4][2], (1,), F)), None, False), (), F), (1,), F))[3], (1,), F)), None, False), (1,), F)), Hstack(reshape(log_sum_exp(Hstack(reshape([-0.69314718 -0.69314718 -0.69314718 -0.69314718 -0.69314718][4], (1,), F), reshape(Hstack(reshape(reshape(log_sum_exp(Hstack(reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F), reshape(-2.995732273553991 + var283[4], (1,), F)), (4,), F)[0], (1,), F), reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F), reshape(-2.995732273553991 + var283[4], (1,), F)), (4,), F)[1:4][0], (1,), F), reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F), reshape(-2.995732273553991 + var283[4], (1,), F)), (4,), F)[1:4][1], (1,), F), reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F), reshape(-2.995732273553991 + var283[4], (1,), F)), (4,), F)[1:4][2], (1,), F)), None, False), (), F), (1,), F), reshape(reshape(log_sum_exp(Hstack(reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F), reshape(-2.995732273553991 + var283[4], (1,), F)), (4,), F)[0], (1,), F), reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F), reshape(-2.995732273553991 + var283[4], (1,), F)), (4,), F)[1:4][0], (1,), F), reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F), reshape(-2.995732273553991 + var283[4], (1,), F)), (4,), F)[1:4][1], (1,), F), reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F), reshape(-2.995732273553991 + var283[4], (1,), F)), (4,), F)[1:4][2], (1,), F)), None, False), (), F), (1,), F), reshape(reshape(log_sum_exp(Hstack(reshape(reshape(Hstack(reshape(-1.6094379124341003 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[3], (1,), F), reshape(-1.6094379124341003 + var283[4], (1,), F)), (4,), F)[0], (1,), F), reshape(reshape(Hstack(reshape(-1.6094379124341003 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[3], (1,), F), reshape(-1.6094379124341003 + var283[4], (1,), F)), (4,), F)[1:4][0], (1,), F), reshape(reshape(Hstack(reshape(-1.6094379124341003 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[3], (1,), F), reshape(-1.6094379124341003 + var283[4], (1,), F)), (4,), F)[1:4][1], (1,), F), reshape(reshape(Hstack(reshape(-1.6094379124341003 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[3], (1,), F), reshape(-1.6094379124341003 + var283[4], (1,), F)), (4,), F)[1:4][2], (1,), F)), None, False), (), F), (1,), F), reshape(reshape(log_sum_exp(Hstack(reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[4], (1,), F)), (4,), F)[0], (1,), F), reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[4], (1,), F)), (4,), F)[1:4][0], (1,), F), reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[4], (1,), F)), (4,), F)[1:4][1], (1,), F), reshape(reshape(Hstack(reshape(-2.3025850929940455 + var283[0], (1,), F), reshape(-2.3025850929940455 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[4], (1,), F)), (4,), F)[1:4][2], (1,), F)), None, False), (), F), (1,), F), reshape(reshape(log_sum_exp(Hstack(reshape(reshape(Hstack(reshape(-2.995732273553991 + var283[0], (1,), F), reshape(-2.995732273553991 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F)), (4,), F)[0], (1,), F), reshape(reshape(Hstack(reshape(-2.995732273553991 + var283[0], (1,), F), reshape(-2.995732273553991 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F)), (4,), F)[1:4][0], (1,), F), reshape(reshape(Hstack(reshape(-2.995732273553991 + var283[0], (1,), F), reshape(-2.995732273553991 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F)), (4,), F)[1:4][1], (1,), F), reshape(reshape(Hstack(reshape(-2.995732273553991 + var283[0], (1,), F), reshape(-2.995732273553991 + var283[1], (1,), F), reshape(-1.6094379124341003 + var283[2], (1,), F), reshape(-2.3025850929940455 + var283[3], (1,), F)), (4,), F)[1:4][2], (1,), F)), None, False), (), F), (1,), F))[4], (1,), F)), None, False), (1,), F))), (5,), F) + -diag_mat([[ 0.         -2.30258509 -1.60943791 -2.30258509 -2.99573227]
    #                 [-2.30258509  0.         -2.30258509 -2.30258509 -2.99573227]
    #                 [-1.60943791 -2.30258509  0.         -1.60943791 -1.60943791]
    #                 [-2.30258509 -2.30258509 -1.60943791  0.         -2.30258509]
    #                 [-2.99573227 -2.99573227 -1.60943791 -2.30258509  0.        ]]) + var283 <= 1.6094379124341003

def dgp8():
    h_min = 1
    h_max = 10
    w_min = 1
    w_max = 10
    R_max = 2
    F_1 = 10
    F_2 = 10 
    sigma = 0.01

    A8 = cp.Variable(pos=True)
    h8 = cp.Variable(pos=True)
    w8 = cp.Variable(pos=True)
    r8 = cp.Variable(pos=True)

    dgp8 = cp.Problem(
        cp.Minimize(2 * A8 * cp.sqrt(w8 ** 2 + h8 ** 2)), [
            F_1 * cp.sqrt(w8 ** 2 + h8 ** 2) / 2 * h8 <= sigma * A8,
            F_2 * cp.sqrt(w8 ** 2 + h8 ** 2) / 2 * w8 <= sigma * A8,
            h_min <= h8,
            h8 <= h_max,
            w_min <= w8,
            w8 <= w_max,
            0.21 * r8 ** 2 <= A8 / (2 * np.pi),
            cp.sqrt(A8 / (2 * np.pi) + r8 ** 2) <= R_max,
        ])

    dcp8 = cp.Dgp2Dcp(dgp8).reduce()

    print(dcp8)


if __name__ == "__main__":
    # dgp1()
    # dgp2()
    # dgp3()
    # dgp4()
    # dgp5()
    # dgp6()
    # dgp7()
    dgp8()
