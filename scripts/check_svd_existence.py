#!/usr/bin/env python3
"""Numerical sanity check for Layer-3 Phase E (SVD existence, square full-rank case),
before formalizing in Lean. Pure stdlib (no NumPy), matching scripts/check_svd_reduction.py.

Construction (square, invertible Sg), mirroring the planned Lean proof:
    G  = Sg^T Sg                              (symmetric positive definite)
    G  = V diag(d) V^T                        (spectral theorem; V orthogonal)
    sigma_i = sqrt(d_i)  > 0
    U  = Sg V diag(sigma)^{-1}                (no basis extension; full rank)
then the SVD identities
    U^T U = 1,   V^T V = 1,   U diag(sigma) V^T = Sg
follow by pure matrix algebra:
    U^T U = sigma^{-1} V^T (Sg^T Sg) V sigma^{-1}
          = sigma^{-1} V^T (V D V^T) V sigma^{-1} = sigma^{-1} D sigma^{-1} = 1   (D = sigma^2)
    U diag(sigma) V^T = Sg V sigma^{-1} sigma V^T = Sg V V^T = Sg.
The eigendecomposition of the symmetric G is computed here by the cyclic Jacobi method.
"""
import math
import random

random.seed(0)


# --- tiny matrix library (lists of rows) ---------------------------------
def mat(r, c, fill=0.0):
    return [[fill] * c for _ in range(r)]


def ident(n):
    return [[1.0 if i == j else 0.0 for j in range(n)] for i in range(n)]


def randmat(r, c):
    return [[random.gauss(0, 1) for _ in range(c)] for _ in range(r)]


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


def diag(d):
    n = len(d)
    return [[d[i] if i == j else 0.0 for j in range(n)] for i in range(n)]


def max_abs_diff(A, B):
    return max(abs(A[i][j] - B[i][j])
               for i in range(len(A)) for j in range(len(A[0]))) if A and A[0] else 0.0


def det(A):
    """Determinant via Gaussian elimination with partial pivoting (small n)."""
    n = len(A)
    M = [row[:] for row in A]
    d = 1.0
    for col in range(n):
        piv = max(range(col, n), key=lambda r: abs(M[r][col]))
        if abs(M[piv][col]) < 1e-12:
            return 0.0
        if piv != col:
            M[col], M[piv] = M[piv], M[col]
            d = -d
        d *= M[col][col]
        for r in range(col + 1, n):
            f = M[r][col] / M[col][col]
            for c in range(col, n):
                M[r][c] -= f * M[col][c]
    return d


# --- symmetric eigendecomposition: cyclic Jacobi -------------------------
def jacobi_eig(A, sweeps=200, tol=1e-28):
    """Return (d, V) with A = V diag(d) V^T, V orthogonal (columns = eigenvectors).
    A must be symmetric."""
    n = len(A)
    M = [row[:] for row in A]
    V = ident(n)
    for _ in range(sweeps):
        off = sum(M[p][q] ** 2 for p in range(n) for q in range(p + 1, n))
        if off < tol:
            break
        for p in range(n):
            for q in range(p + 1, n):
                if abs(M[p][q]) < 1e-300:
                    continue
                theta = (M[q][q] - M[p][p]) / (2.0 * M[p][q])
                t = math.copysign(1.0, theta) / (abs(theta) + math.sqrt(theta * theta + 1.0))
                c = 1.0 / math.sqrt(t * t + 1.0)
                s = t * c
                # rotate rows/cols p,q of M
                for k in range(n):
                    Mkp, Mkq = M[k][p], M[k][q]
                    M[k][p] = c * Mkp - s * Mkq
                    M[k][q] = s * Mkp + c * Mkq
                for k in range(n):
                    Mpk, Mqk = M[p][k], M[q][k]
                    M[p][k] = c * Mpk - s * Mqk
                    M[q][k] = s * Mpk + c * Mqk
                # accumulate eigenvectors (columns of V)
                for k in range(n):
                    Vkp, Vkq = V[k][p], V[k][q]
                    V[k][p] = c * Vkp - s * Vkq
                    V[k][q] = s * Vkp + c * Vkq
    d = [M[i][i] for i in range(n)]
    return d, V


# --- the check -----------------------------------------------------------
def check_svd_existence(trials=2000):
    worst_uu = 0.0   # U^T U vs 1
    worst_vv = 0.0   # V^T V vs 1
    worst_fac = 0.0  # U diag(sigma) V^T vs Sg
    worst_spec = 0.0 # V D V^T vs G (Jacobi residual)
    min_sigma = math.inf
    for _ in range(trials):
        n = random.randint(1, 5)
        # invertible Sg: resample until determinant is comfortably nonzero
        while True:
            Sg = randmat(n, n)
            if abs(det(Sg)) > 5e-2:   # keep conditioning sane (UᵀU error ~ jacobi_err / σ²)
                break
        G = matmul(transpose(Sg), Sg)              # symmetric PD
        d, V = jacobi_eig(G)
        # spectral residual: G = V diag(d) V^T
        worst_spec = max(worst_spec, max_abs_diff(matmul(matmul(V, diag(d)), transpose(V)), G))
        sigma = [math.sqrt(max(di, 0.0)) for di in d]
        min_sigma = min(min_sigma, min(sigma))
        sinv = [1.0 / si for si in sigma]
        U = matmul(matmul(Sg, V), diag(sinv))      # U = Sg V diag(sigma)^{-1}
        n_ = n
        worst_uu = max(worst_uu, max_abs_diff(matmul(transpose(U), U), ident(n_)))
        worst_vv = max(worst_vv, max_abs_diff(matmul(transpose(V), V), ident(n_)))
        recon = matmul(matmul(U, diag(sigma)), transpose(V))
        worst_fac = max(worst_fac, max_abs_diff(recon, Sg))
    return worst_uu, worst_vv, worst_fac, worst_spec, min_sigma


if __name__ == "__main__":
    wuu, wvv, wfac, wspec, smin = check_svd_existence()
    print(f"spectral residual G = V D V^T   max: {wspec:.2e}")
    print(f"U^T U = 1                       max: {wuu:.2e}")
    print(f"V^T V = 1                       max: {wvv:.2e}")
    print(f"U diag(sigma) V^T = Sg          max: {wfac:.2e}")
    print(f"min singular value over trials     : {smin:.2e}  (>0 confirms full rank)")
    assert wspec < 1e-10, wspec
    assert wuu < 1e-7, wuu      # conditioned by min singular value; jacobi-limited
    assert wvv < 1e-10, wvv
    assert wfac < 1e-10, wfac
    assert smin > 0.0, smin
    print("OK")
