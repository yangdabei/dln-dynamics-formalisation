#!/usr/bin/env python3
"""Numerical sanity check for Layer-3 Phase B/C (SVD change of variables + mode
extraction), before formalizing in Lean. Pure stdlib (no NumPy), matching
scripts/check_closed_form.py.

Phase B (change of variables): with an SVD Sigma = U S V^T (U,V orthogonal) and
barred coords  Wba = Wa V,  Wbb = U^T Wb, the wb_avg flow values transform as
    Wb^T (Sigma - Wb Wa) V   ==   Wbb^T (S - Wbb Wba)        [a-equation]
    U^T (Sigma - Wb Wa) Wa^T ==   (S - Wbb Wba) Wba^T        [b-equation]
(holds for arbitrary S with Sigma = U S V^T; needs only U,V orthogonal.)

Phase C (mode extraction, square case S = diag(sigma)): column alpha of the
a-flow value equals the competition form
    (s_a - b_a . a_a) b_a  -  sum_{g != a} (b_g . a_a) b_g
with a_a = column alpha of Wba, b_a = row alpha of Wbb.
"""
import math
import random

random.seed(0)


# --- tiny matrix library (lists of rows) ---------------------------------
def mat(r, c, fill=0.0):
    return [[fill] * c for _ in range(r)]


def randmat(r, c):
    return [[random.gauss(0, 1) for _ in range(c)] for _ in range(r)]


def transpose(A):
    return [list(col) for col in zip(*A)] if A else []


def matmul(A, B):
    n, m, p = len(A), len(B), len(B[0])
    C = mat(n, p)
    for i in range(n):
        Ai = A[i]
        for k in range(m):
            a = Ai[k]
            Bk = B[k]
            Ci = C[i]
            for j in range(p):
                Ci[j] += a * Bk[j]
    return C


def sub(A, B):
    return [[A[i][j] - B[i][j] for j in range(len(A[0]))] for i in range(len(A))]


def max_abs_diff(A, B):
    return max(abs(A[i][j] - B[i][j])
               for i in range(len(A)) for j in range(len(A[0]))) if A and A[0] else 0.0


def dot(u, v):
    return sum(x * y for x, y in zip(u, v))


def random_orthogonal(n):
    """Gram-Schmidt on random columns -> orthonormal columns (orthogonal matrix)."""
    cols = []
    for _ in range(n):
        v = [random.gauss(0, 1) for _ in range(n)]
        for q in cols:
            c = dot(v, q)
            v = [vi - c * qi for vi, qi in zip(v, q)]
        norm = math.sqrt(dot(v, v))
        cols.append([vi / norm for vi in v])
    # cols are orthonormal columns; build matrix with these as columns
    return transpose(cols)


# --- checks ---------------------------------------------------------------
def check_change_of_vars(trials=3000):
    worst = 0.0
    for _ in range(trials):
        N1, N2, N3 = random.randint(1, 4), random.randint(1, 4), random.randint(1, 4)
        U = random_orthogonal(N3)
        V = random_orthogonal(N1)
        S = randmat(N3, N1)
        Sigma = matmul(matmul(U, S), transpose(V))
        Wa = randmat(N2, N1)
        Wb = randmat(N3, N2)
        Wba = matmul(Wa, V)            # bar W^a
        Wbb = matmul(transpose(U), Wb)  # bar W^b
        D = sub(Sigma, matmul(Wb, Wa))
        Dbar = sub(S, matmul(Wbb, Wba))
        lhs_a = matmul(matmul(transpose(Wb), D), V)
        rhs_a = matmul(transpose(Wbb), Dbar)
        lhs_b = matmul(matmul(transpose(U), D), transpose(Wa))
        rhs_b = matmul(Dbar, transpose(Wba))
        worst = max(worst, max_abs_diff(lhs_a, rhs_a), max_abs_diff(lhs_b, rhs_b))
    return worst


def check_a_dyn(trials=3000):
    worst = 0.0
    for _ in range(trials):
        N = random.randint(1, 4)     # square modes: N3 = N1 = N
        N2 = random.randint(1, 5)    # hidden width, arbitrary
        sigma = [random.gauss(0, 1) for _ in range(N)]
        S = [[sigma[i] if i == j else 0.0 for j in range(N)] for i in range(N)]
        Wba = randmat(N2, N)         # bar W^a : N2 x N
        Wbb = randmat(N, N2)         # bar W^b : N x N2
        flow = matmul(transpose(Wbb), sub(S, matmul(Wbb, Wba)))  # N2 x N
        for a in range(N):
            a_a = [Wba[i][a] for i in range(N2)]   # column alpha, in R^N2
            b_a = Wbb[a]                           # row alpha, in R^N2
            comp = [(sigma[a] - dot(b_a, a_a)) * x for x in b_a]
            for g in range(N):
                if g != a:
                    coef = dot(Wbb[g], a_a)
                    comp = [c - coef * x for c, x in zip(comp, Wbb[g])]
            flow_col_a = [flow[i][a] for i in range(N2)]
            worst = max(worst, max(abs(c - f) for c, f in zip(comp, flow_col_a)))
    return worst


if __name__ == "__main__":
    w1 = check_change_of_vars()
    w2 = check_a_dyn()
    print(f"change of variables  max residual: {w1:.2e}")
    print(f"a_dyn competition    max residual: {w2:.2e}")
    assert w1 < 1e-9, w1
    assert w2 < 1e-9, w2
    print("OK")
