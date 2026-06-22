#!/usr/bin/env python3
"""Numerical sanity check for Layer-3 Phase D option 3 (forward-invariance of the
orthogonal-mode manifold) and the balanced solution `a = b = sqrt(uf)`. Pure stdlib
(no NumPy), matching scripts/check_svd_reduction.py.

Two checks:

1. `isABFlow_sqrt_uf`: the balanced pair `a(t) = b(t) = sqrt(uf(s,tau,u0,t))` solves
   Saxe Eq. ab_dyn, i.e. `tau a'(t) = b(t) (s - a(t) b(t))`. Verified by comparing a
   finite-difference derivative of `sqrt(uf)` to the closed-form RHS.

2. `manifold_forward_invariant`: integrate the decoupled flow wbo_dyn
       tau d/dt Wba = Wbb^T (S - Wbb Wba),   tau d/dt Wbb = (S - Wbb Wba) Wba^T,
   S = diag(sigma), from the balanced orthogonal-mode initial condition
       column alpha of Wba(0) = sqrt(u0[alpha]) * r^alpha,
       row    alpha of Wbb(0) = sqrt(u0[alpha]) * r^alpha,
   with {r^alpha} orthonormal. Confirm that for all later t and every mode alpha:
     (a) column alpha of Wba(t) stays PARALLEL to r^alpha (orthogonal residual ~ 0),
     (b) its scalar overlap  (column . r^alpha)  tracks  sqrt(uf(sigma[alpha],tau,u0[alpha],t)).
"""
import math
import random

random.seed(0)


# --- tiny matrix library (lists of rows) ---------------------------------
def mat(r, c, fill=0.0):
    return [[fill] * c for _ in range(r)]


def transpose(A):
    return [list(col) for col in zip(*A)] if A else []


def matmul(A, B):
    n, m, p = len(A), len(B), len(B[0])
    C = mat(n, p)
    for i in range(n):
        Ai, Ci = A[i], C[i]
        for k in range(m):
            a, Bk = Ai[k], B[k]
            for j in range(p):
                Ci[j] += a * Bk[j]
    return C


def sub(A, B):
    return [[A[i][j] - B[i][j] for j in range(len(A[0]))] for i in range(len(A))]


def axpy(A, c, B):
    """A + c*B for matrices."""
    return [[A[i][j] + c * B[i][j] for j in range(len(A[0]))] for i in range(len(A))]


def dot(u, v):
    return sum(x * y for x, y in zip(u, v))


def random_orthogonal(n):
    cols = []
    for _ in range(n):
        v = [random.gauss(0, 1) for _ in range(n)]
        for q in cols:
            c = dot(v, q)
            v = [vi - c * qi for vi, qi in zip(v, q)]
        norm = math.sqrt(dot(v, v))
        cols.append([vi / norm for vi in v])
    return transpose(cols)


def uf(s, tau, u0, t):
    e = math.exp(2 * s * t / tau)
    return s * e / (e - 1 + s / u0)


# --- check 1: the balanced sqrt(uf) solves ab_dyn ------------------------
def check_sqrt_uf(trials=2000):
    worst = 0.0
    h = 1e-6
    for _ in range(trials):
        s = random.uniform(0.5, 3.0)
        tau = random.uniform(0.5, 2.0)
        u0 = random.uniform(0.01, 0.4) * s        # 0 < u0 < s
        t = random.uniform(-1.0, 3.0)
        a = math.sqrt(uf(s, tau, u0, t))
        # finite-difference derivative of sqrt(uf)
        ap = (math.sqrt(uf(s, tau, u0, t + h)) - math.sqrt(uf(s, tau, u0, t - h))) / (2 * h)
        rhs = a * (s - a * a) / tau               # b (s - a b) / tau, with b = a
        worst = max(worst, abs(tau * ap - tau * rhs))
    return worst


# --- check 2: forward-invariance of the manifold under wbo_dyn -----------
def flow(S, Wba, Wbb, tau):
    D = sub(S, matmul(Wbb, Wba))
    dWba = matmul(transpose(Wbb), D)
    dWbb = matmul(D, transpose(Wba))
    return [[x / tau for x in row] for row in dWba], [[x / tau for x in row] for row in dWbb]


def rk4_step(S, Wba, Wbb, tau, dt):
    k1a, k1b = flow(S, Wba, Wbb, tau)
    k2a, k2b = flow(S, axpy(Wba, dt / 2, k1a), axpy(Wbb, dt / 2, k1b), tau)
    k3a, k3b = flow(S, axpy(Wba, dt / 2, k2a), axpy(Wbb, dt / 2, k2b), tau)
    k4a, k4b = flow(S, axpy(Wba, dt, k3a), axpy(Wbb, dt, k3b), tau)
    Wba2 = Wba
    Wbb2 = Wbb
    for k, c in ((k1a, 1), (k2a, 2), (k3a, 2), (k4a, 1)):
        Wba2 = axpy(Wba2, c * dt / 6, k)
    for k, c in ((k1b, 1), (k2b, 2), (k3b, 2), (k4b, 1)):
        Wbb2 = axpy(Wbb2, c * dt / 6, k)
    return Wba2, Wbb2


def check_forward_invariance(trials=200):
    worst_par = 0.0   # parallelism residual
    worst_mag = 0.0   # overlap vs sqrt(uf)
    for _ in range(trials):
        N = random.randint(1, 3)        # modes (square case N3 = N1 = N)
        N2 = random.randint(N, N + 3)   # hidden width >= N
        tau = random.uniform(0.7, 1.5)
        sigma = [random.uniform(0.6, 2.5) for _ in range(N)]
        u0 = [random.uniform(0.02, 0.5) * sigma[a] for a in range(N)]  # 0 < u0 < sigma
        S = [[sigma[i] if i == j else 0.0 for j in range(N)] for i in range(N)]
        Q = random_orthogonal(N2)
        r = [Q[a] for a in range(N)]    # N orthonormal vectors in R^{N2} (rows of Q)
        # balanced orthogonal-mode init
        Wba = [[math.sqrt(u0[a]) * r[a][i] for a in range(N)] for i in range(N2)]
        Wbb = [[math.sqrt(u0[a]) * r[a][i] for i in range(N2)] for a in range(N)]
        dt = 1e-3
        t = 0.0
        for step in range(1500):        # integrate to t = 1.5
            Wba, Wbb = rk4_step(S, Wba, Wbb, tau, dt)
            t += dt
            if step % 300 != 299:
                continue
            for a in range(N):
                col = [Wba[i][a] for i in range(N2)]          # column alpha of Wba(t)
                coeff = dot(col, r[a])
                resid = [col[i] - coeff * r[a][i] for i in range(N2)]
                worst_par = max(worst_par, math.sqrt(dot(resid, resid)))
                worst_mag = max(worst_mag, abs(coeff - math.sqrt(uf(sigma[a], tau, u0[a], t))))
    return worst_par, worst_mag


if __name__ == "__main__":
    w1 = check_sqrt_uf()
    wpar, wmag = check_forward_invariance()
    print(f"sqrt(uf) solves ab_dyn        max residual: {w1:.2e}")
    print(f"manifold parallelism          max residual: {wpar:.2e}")
    print(f"overlap vs sqrt(uf)           max residual: {wmag:.2e}")
    assert w1 < 1e-6, w1
    assert wpar < 1e-6, wpar     # pure RK4 integration error (parallelism is exact)
    assert wmag < 1e-6, wmag
    print("OK")
