#!/usr/bin/env python3
"""Numerical sanity test of the Pauli sector bound, a flat qubit count (a variant of Corollary 4.3 [cor:count-flat]); not a proof.
 log2 D >= sum_i [1 - b_i^2/(2 ln2) - h2(min(a_i^2/2, 1/2))]
 with a_i^2 = E_g ||f(g+e_i) - f(g) Z_i||^2, b_i^2 = E_g ||(-1)^{g_i} X_i f(g) - f(g) X_i||^2 (normalized HS norm),
 plus (i) a_i^2 <= sum_{j>i} ||[Z_i,Z_j]||^2, (ii) b_i^2 <= ||{X_i,Z_i}||^2 + sum_{j!=i} ||[X_i,Z_j]||^2.
Adversarial families: (A) M pairs squeezed into 2^(M-1) dims (one pair reuses another qubit), perturbed;
(B) random Hermitian unitaries; (C) small perturbations of exact Paulis; (D) exact Paulis (tightness).
"""
import itertools, math, sys
import numpy as np

rng = np.random.default_rng(20261021)
I2 = np.eye(2); X = np.array([[0, 1], [1, 0]], complex); Zp = np.array([[1, 0], [0, -1]], complex)

def kron_at(op, k, n):
    out = np.array([[1]], complex)
    for j in range(n):
        out = np.kron(out, op if j == k else I2)
    return out

def nhs2(A):
    return float(np.real(np.trace(A.conj().T @ A))) / A.shape[0]

def h2(x):
    return 0.0 if x <= 0 or x >= 1 else -x * math.log2(x) - (1 - x) * math.log2(1 - x)

def rand_herm_unitary_near(U, eps):
    """return a Hermitian unitary close to the Hermitian unitary U (perturb then take sign)."""
    D = U.shape[0]
    H = rng.normal(size=(D, D)) + 1j * rng.normal(size=(D, D)); H = (H + H.conj().T) / 2
    A = U + eps * H
    w, V = np.linalg.eigh((A + A.conj().T) / 2)
    return V @ np.diag(np.where(w >= 0, 1.0, -1.0)) @ V.conj().T

def rand_herm_unitary(D):
    H = rng.normal(size=(D, D)) + 1j * rng.normal(size=(D, D)); H = (H + H.conj().T) / 2
    w, V = np.linalg.eigh(H)
    return V @ np.diag(np.where(w >= 0, 1.0, -1.0)) @ V.conj().T

def check(Xs, Zs):
    M = len(Xs); D = Xs[0].shape[0]
    def f(g):
        out = np.eye(D, dtype=complex)
        for k in range(M):
            if g[k]: out = out @ Zs[k]
        return out
    gs = list(itertools.product((0, 1), repeat=M))
    F = {g: f(g) for g in gs}
    bound = 0.0; okii = True
    for i in range(M):
        a2 = np.mean([nhs2(F[tuple((g[k] + (k == i)) % 2 for k in range(M))] - F[g] @ Zs[i]) for g in gs])
        b2 = np.mean([nhs2((-1) ** g[i] * Xs[i] @ F[g] - F[g] @ Xs[i]) for g in gs])
        ra = sum(nhs2(Zs[i] @ Zs[j] - Zs[j] @ Zs[i]) for j in range(i + 1, M))
        rb = nhs2(Xs[i] @ Zs[i] + Zs[i] @ Xs[i]) + sum(nhs2(Xs[i] @ Zs[j] - Zs[j] @ Xs[i]) for j in range(M) if j != i)
        okii &= (a2 <= ra + 1e-9) and (b2 <= rb + 1e-9)
        bound += 1 - b2 / (2 * math.log(2)) - h2(min(a2 / 2, 0.5))
    return math.log2(D), bound, okii

worst = 1e9; fails = 0; n = 0
# (D) exact Paulis
for M in (1, 2, 3, 4):
    Xs = [kron_at(X, k, M) for k in range(M)]; Zs = [kron_at(Zp, k, M) for k in range(M)]
    lg, b, o = check(Xs, Zs)
    print('exact Pauli M=%d: log D = %.6f, bound = %.6f' % (M, lg, b))
    fails += (b > lg + 1e-9) or not o
for trial in range(300):
    fam = trial % 3
    M = int(rng.integers(2, 5))
    if fam == 0:      # squeezed: M pairs in 2^(M-1) dims, last pair = perturbed copy of pair 0 or a mixture
        nq = M - 1
        Xs = [kron_at(X, k, nq) for k in range(nq)]; Zs = [kron_at(Zp, k, nq) for k in range(nq)]
        Xs.append(kron_at(X, 0, nq) @ kron_at(Zp, 1 % nq, nq) if nq > 1 else kron_at(X, 0, nq))
        Zs.append(kron_at(Zp, 0, nq) @ kron_at(X, 1 % nq, nq) if nq > 1 else kron_at(Zp, 0, nq))
        eps = float(rng.uniform(0, 0.3))
        Xs = [rand_herm_unitary_near(A, eps) for A in Xs]; Zs = [rand_herm_unitary_near(A, eps) for A in Zs]
    elif fam == 1:
        D = int(rng.integers(2, 9))
        Xs = [rand_herm_unitary(D) for _ in range(M)]; Zs = [rand_herm_unitary(D) for _ in range(M)]
    else:
        Xs = [kron_at(X, k, M) for k in range(M)]; Zs = [kron_at(Zp, k, M) for k in range(M)]
        eps = float(rng.uniform(0, 0.5))
        Xs = [rand_herm_unitary_near(A, eps) for A in Xs]; Zs = [rand_herm_unitary_near(A, eps) for A in Zs]
    lg, b, o = check(Xs, Zs)
    n += 1; worst = min(worst, lg - b)
    if b > lg + 1e-9 or not o:
        fails += 1; print('VIOLATION', fam, M, lg, b, o)
print('instances %d, min slack log D - bound = %.4f, violations %d' % (n, worst, fails))
# scalar inequality 1 - h2(x) <= (1 - 2 sqrt(x(1-x)))/ln 2, exact-ish on a fine grid
gmin = min((1 - 2 * math.sqrt(x * (1 - x))) / math.log(2) - (1 - h2(x)) for x in [k / 20000 for k in range(1, 20000)])
print('scalar inequality min slack on grid: %.3e' % gmin)
print('bracket at b^2 = a^2 = 1/10: %.4f' % (1 - 0.1 / (2 * math.log(2)) - h2(0.05)))
sys.exit(1 if fails or gmin < -1e-12 else 0)
