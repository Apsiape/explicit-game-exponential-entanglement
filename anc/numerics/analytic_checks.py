#!/usr/bin/env python3
"""Numerical attacks on the analytic inequalities of the paper.

No proof in the paper depends on this program. It evaluates both sides of four
statements on random and on optimised instances, with flat, full-rank, low-rank
and pure states, and reports the smallest slack found. A negative slack would be
a counterexample. Run:  python3 -I analytic_checks.py [count|rounding|return|K|all]

  count     the qubit count in a state (thm:count), parts (i), (ii), (iii)
  rounding  rounding a unitary to an involution in a state (lem:rounding)
  return    sequential measurements (lem:sequential) and the return direction
            (thm:return) on perturbed models of the magic square game
  K         the profile of c in the Slofstra-Vidick group K in a state
            (thm:K-profile): d >= 1/(29 e)

The names in parentheses are the LaTeX labels of the statements in the paper.
Requires numpy and scipy. Deterministic: every random draw is seeded.
"""
import itertools
import math
import sys

import numpy as np
from scipy.linalg import expm, sqrtm
from scipy.optimize import minimize

RNG = np.random.default_rng(20261026)
LN2 = math.log(2.0)

# ----------------------------------------------------------------------------- helpers

def hs(A):
    """Unnormalised Hilbert-Schmidt norm."""
    return float(np.linalg.norm(A, 'fro'))


def rand_herm(d, rng=RNG):
    G = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
    H = (G + G.conj().T) / 2
    return H / np.linalg.norm(H, 2)


def rand_unitary_near(d, t, rng=RNG):
    return expm(1j * t * rand_herm(d, rng))


def psd_sqrt(rho):
    w, V = np.linalg.eigh((rho + rho.conj().T) / 2)
    w = np.clip(w, 0, None)
    return (V * np.sqrt(w)) @ V.conj().T


def entropy_bits(rho):
    w = np.linalg.eigvalsh((rho + rho.conj().T) / 2)
    w = w[w > 1e-15]
    return float(-(w * np.log2(w)).sum())


def h2(p):
    if p <= 0 or p >= 1:
        return 0.0
    return -p * math.log2(p) - (1 - p) * math.log2(1 - p)


def random_state(d, kind, rng=RNG):
    if kind == 'flat':
        return np.eye(d) / d
    if kind == 'full':
        G = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
        rho = G @ G.conj().T
    elif kind == 'lowrank':
        r = max(1, d // 3)
        G = rng.normal(size=(d, r)) + 1j * rng.normal(size=(d, r))
        rho = G @ G.conj().T
    elif kind == 'pure':
        v = rng.normal(size=d) + 1j * rng.normal(size=d)
        rho = np.outer(v, v.conj())
    elif kind == 'skewed':  # geometric spectrum in a random basis
        w = 0.5 ** np.arange(d)
        U = rand_unitary_near(d, math.pi, rng)
        rho = (U * w) @ U.conj().T
    else:
        raise ValueError(kind)
    return rho / np.trace(rho).real


def state_from_params(theta, d):
    G = (theta[:d * d] + 1j * theta[d * d:2 * d * d]).reshape(d, d)
    rho = G @ G.conj().T + 1e-12 * np.eye(d)
    return rho / np.trace(rho).real


def herm_from_params(theta, d):
    G = (theta[:d * d] + 1j * theta[d * d:2 * d * d]).reshape(d, d)
    return (G + G.conj().T) / 2


class Tally:
    def __init__(self, name):
        self.name, self.n, self.worst, self.where = name, 0, math.inf, None

    def add(self, slack, where):
        self.n += 1
        if slack < self.worst:
            self.worst, self.where = slack, where

    def report(self):
        status = 'OK' if self.worst >= -1e-9 else 'VIOLATED'
        print(f'  {self.name:<46s} instances={self.n:6d}  min slack={self.worst: .3e}  [{status}]  worst at: {self.where}')
        return self.worst >= -1e-9

# ----------------------------------------------------------------------------- Paulis

SX = np.array([[0, 1], [1, 0]], dtype=complex)
SZ = np.array([[1, 0], [0, -1]], dtype=complex)
SY = np.array([[0, -1j], [1j, 0]], dtype=complex)
I2 = np.eye(2, dtype=complex)


def kron_list(ops):
    out = np.array([[1.0 + 0j]])
    for o in ops:
        out = np.kron(out, o)
    return out


def pauli_pairs(M, anc):
    Xs, Zs = [], []
    for i in range(M):
        ops = [I2] * M
        ops[i] = SX
        Xs.append(np.kron(kron_list(ops), np.eye(anc)))
        ops[i] = SZ
        Zs.append(np.kron(kron_list(ops), np.eye(anc)))
    return Xs, Zs

# ============================================================================= qubit count (thm:count)

def count_quantities(Xs, Zs, rho):
    M, d = len(Xs), rho.shape[0]
    xi = psd_sqrt(rho)
    cZ = [hs(Z @ xi - xi @ Z) for Z in Zs]
    cX = [hs(X @ xi - xi @ X) for X in Xs]
    fs = {}
    for g in itertools.product((0, 1), repeat=M):
        F = np.eye(d, dtype=complex)
        for i, gi in enumerate(g):
            if gi:
                F = F @ Zs[i]
        fs[g] = F
    a2, b2 = [], []
    for i in range(M):
        sa = sb = 0.0
        for g, F in fs.items():
            gp = list(g); gp[i] ^= 1
            sa += hs((fs[tuple(gp)] - F @ Zs[i]) @ xi) ** 2
            sb += hs((((-1) ** g[i]) * Xs[i] @ F - F @ Xs[i]) @ xi) ** 2
        a2.append(sa / len(fs)); b2.append(sb / len(fs))
    comm = lambda A, B: A @ B - B @ A
    rhs_i, rhs_ii = [], []
    for i in range(M):
        r = sum(2 * (hs(comm(Zs[i], Zs[j]) @ xi) + cZ[j]) ** 2 + 2 * cZ[j] ** 2 for j in range(i + 1, M))
        rhs_i.append(r)
        r = 2 * (hs((Xs[i] @ Zs[i] + Zs[i] @ Xs[i]) @ xi) + cZ[i]) ** 2
        r += sum(2 * (hs(comm(Xs[i], Zs[j]) @ xi) + cZ[j]) ** 2 for j in range(M) if j != i)
        r += 2 * sum(c ** 2 for c in cZ)
        rhs_ii.append(r)
    bound = 0.0
    for i in range(M):
        ai, bi = math.sqrt(a2[i]), math.sqrt(b2[i])
        bound += 1 - (bi + cX[i]) ** 2 / (2 * LN2) - h2(min((ai + cZ[i]) ** 2 / 4, 0.5))
    S = entropy_bits(rho)
    return a2, b2, rhs_i, rhs_ii, S, bound


def perturbed_pairs(M, anc, t, rng=RNG):
    Xs, Zs = pauli_pairs(M, anc)
    d = Xs[0].shape[0]
    Xs = [(V := rand_unitary_near(d, t, rng)) @ X @ V.conj().T for X in Xs]
    Zs = [(V := rand_unitary_near(d, t, rng)) @ Z @ V.conj().T for Z in Zs]
    return Xs, Zs


def run_count():
    print('Qubit count in a state (thm:count)')
    T1, T2, T3 = Tally('(i)  a_i^2 <= RHS'), Tally('(ii) b_i^2 <= RHS'), Tally('(iii) S(rho) >= sum of terms')
    for M, anc in [(2, 1), (2, 2), (3, 1), (3, 2), (4, 1)]:
        d = 2 ** M * anc
        for t in [0.0, 0.02, 0.1, 0.3, 1.0, 3.0]:
            for kind in ['flat', 'full', 'lowrank', 'pure', 'skewed', 'product']:
                for rep in range(3):
                    Xs, Zs = perturbed_pairs(M, anc, t)
                    if kind == 'product':
                        sig = random_state(anc, 'full') if anc > 1 else np.eye(1)
                        rho = np.kron(np.eye(2 ** M) / 2 ** M, sig)
                        V = rand_unitary_near(d, t / 3)
                        rho = V @ rho @ V.conj().T
                    else:
                        rho = random_state(d, kind)
                    a2, b2, r1, r2, S, bd = count_quantities(Xs, Zs, rho)
                    tag = f'M={M},anc={anc},t={t},{kind}'
                    for i in range(M):
                        T1.add(r1[i] - a2[i], tag); T2.add(r2[i] - b2[i], tag)
                    T3.add(S - bd, tag)
    # optimiser: minimise S(rho) - bound over perturbations of exact Paulis and the state
    for M, anc, seed in [(2, 1, 1), (2, 1, 2), (2, 1, 3)]:
        rng = np.random.default_rng(seed)
        X0, Z0 = pauli_pairs(M, anc)
        d = X0[0].shape[0]
        nH = 2 * d * d

        def unpack(th):
            ops = []
            for k, P in enumerate(X0 + Z0):
                H = herm_from_params(th[k * nH:(k + 1) * nH], d)
                V = expm(1j * H)
                ops.append(V @ P @ V.conj().T)
            rho = state_from_params(th[2 * M * nH:], d)
            return ops[:M], ops[M:], rho

        def obj(th):
            Xs, Zs, rho = unpack(th)
            _, _, _, _, S, bd = count_quantities(Xs, Zs, rho)
            return S - bd

        best = None
        for start in range(2):
            th0 = 0.05 * rng.normal(size=2 * M * nH + 2 * d * d)
            th0[2 * M * nH:2 * M * nH + d * d] += np.eye(d).ravel()
            res = minimize(obj, th0, method='L-BFGS-B', options={'maxiter': 300})
            if best is None or res.fun < best:
                best = res.fun
            Xs, Zs, rho = unpack(res.x)
            T3.add(res.fun, f'optimiser M={M},anc={anc},start={start}')
            print(f'  optimiser M={M}, anc={anc}, start={start}: S(rho)-bound={res.fun:.4e}, S(rho)={entropy_bits(rho):.3f}')
    ok = all(T.report() for T in (T1, T2, T3))
    return ok

# ============================================================================= rounding (lem:rounding)

def rounding(U):
    w, V = np.linalg.eig(U)
    # U is normal; re-orthonormalise eigenvectors through a Schur form for safety
    from scipy.linalg import schur
    Tm, Q = schur(U, output='complex')
    lam = np.diag(Tm)
    s = np.where(lam.real >= 0, 1.0, -1.0)
    return (Q * s) @ Q.conj().T


def run_rounding():
    print('Rounding (lem:rounding)')
    T1, T2 = Tally('||(r(U)-U)xi|| <= ||(U^2-I)xi||'), Tally('||[r(U),xi]|| <= ||[U,xi]||+2||(U^2-I)xi||')
    for d in [2, 3, 5, 8]:
        for t in [0.01, 0.1, 0.5, 1.5, 3.0]:
            for kind in ['flat', 'full', 'lowrank', 'pure', 'skewed']:
                for rep in range(10):
                    P = np.diag(RNG.choice([-1.0, 1.0], size=d)).astype(complex)
                    W = rand_unitary_near(d, math.pi)
                    U = rand_unitary_near(d, t) @ W @ P @ W.conj().T
                    rho = random_state(d, kind)
                    xi = psd_sqrt(rho)
                    R = rounding(U)
                    I = np.eye(d)
                    lhs1, rhs1 = hs((R - U) @ xi), hs((U @ U - I) @ xi)
                    lhs2 = hs(R @ xi - xi @ R)
                    rhs2 = hs(U @ xi - xi @ U) + 2 * rhs1
                    tag = f'd={d},t={t},{kind}'
                    T1.add(rhs1 - lhs1, tag); T2.add(rhs2 - lhs2, tag)
    return all(T.report() for T in (T1, T2))

# ============================================================================= return direction (lem:sequential, thm:return)

def magic_square():
    XI, IX, XX = np.kron(SX, I2), np.kron(I2, SX), np.kron(SX, SX)
    IZ, ZI, ZZ = np.kron(I2, SZ), np.kron(SZ, I2), np.kron(SZ, SZ)
    XZ, ZX, YY = np.kron(SX, SZ), np.kron(SZ, SX), np.kron(SY, SY)
    ops = [XI, IX, XX, IZ, ZI, ZZ, -XZ, -ZX, YY]
    eqs = [[0, 1, 2], [3, 4, 5], [6, 7, 8], [0, 3, 6], [1, 4, 7], [2, 5, 8]]
    b = []
    for V in eqs:
        P = ops[V[0]] @ ops[V[1]] @ ops[V[2]]
        if np.allclose(P, np.eye(4)):
            b.append(0)
        elif np.allclose(P, -np.eye(4)):
            b.append(1)
        else:
            raise RuntimeError('not a solution')
    return ops, eqs, b


def C_s(s):
    beta = lambda l: 3 * (1 + (l - 1) * (l - 2) / 2) + 13 * (l - 1) / math.sqrt(2)
    return 0.25 * (beta(s) ** 2 + (s * s + 2 + sum(beta(l) for l in range(1, s + 1))) ** 2)


def model_precision(U, UJ, eqs, b, xi):
    """The precision e of (S1)-(S3) for the presentation of Definition 2.8(a)."""
    d = xi.shape[0]
    I = np.eye(d)
    Ui = lambda A: A.conj().T
    defects = []
    for A in U:
        defects.append(hs((A @ A - I) @ xi))
        defects.append(hs((A @ UJ @ Ui(A) @ Ui(UJ) - I) @ xi))
    defects.append(hs((UJ @ UJ - I) @ xi))
    for V in eqs:
        for j in V:
            for k in V:
                if j != k:
                    defects.append(hs((U[j] @ U[k] @ Ui(U[j]) @ Ui(U[k]) - I) @ xi))
    for V, bi in zip(eqs, b):
        P = np.linalg.matrix_power(UJ, bi) @ U[V[0]] @ U[V[1]] @ U[V[2]]
        defects.append(hs((P - I) @ xi))
    comms = [hs(A @ xi - xi @ A) for A in U + [UJ]]
    s3 = hs((UJ + I) @ xi)
    return max(defects + comms + [s3])


def loss_probabilities(B, eqs, b, xi):
    """Exact losing probability of every pair (i, j), j in V_i, for the strategy of Theorem 5.4."""
    d = xi.shape[0]
    I = np.eye(d)
    Mpsi = xi.T  # psi_rho as a matrix: psi[a, b] = xi[b, a]
    out = []
    for i, V in enumerate(eqs):
        r = len(V)
        target = (-1) ** b[i]
        for pos, j in enumerate(V):
            Qc = {c: (I + c * B[j]) / 2 for c in (1, -1)}
            lose = 0.0
            for a in itertools.product((1, -1), repeat=r):
                K = np.eye(d, dtype=complex)
                for l in range(r):
                    K = ((I + a[l] * B[V[l]].T) / 2) @ K
                ans = list(a)
                if np.prod(ans) != target:
                    ans[-1] = -ans[-1]
                for c in (1, -1):
                    if ans[pos] != c:
                        lose += hs(K @ Mpsi @ Qc[c].T) ** 2
            out.append(((i, j), lose))
    return out


def run_return():
    print('Sequential measurements and the return direction (lem:sequential, thm:return), magic square game')
    ops, eqs, b = magic_square()
    Cs = C_s(3)
    print(f'  C_3 = {Cs:.2f} (paper: C_3 < 788.2)')
    T = Tally('loss(i,j) <= C_3 e^2 for every pair')
    Tseq = Tally('lem:sequential(a): Pr[a_j != b_j] <= d_j^2/4')
    smallest_e = math.inf
    worst_ratio, worst_ratio_at = 0.0, None
    for anc in [1, 2, 3]:
        d = 4 * anc
        base = [np.kron(P, np.eye(anc)) for P in ops]
        for t in [0.0, 0.003, 0.01, 0.03, 0.1, 0.3]:
            for kind in ['flat', 'product', 'full', 'lowrank', 'skewed', 'pure']:
                for rep in range(3):
                    U = [rand_unitary_near(d, t) @ A @ rand_unitary_near(d, t) for A in base]
                    UJ = -rand_unitary_near(d, t / 2)
                    if kind == 'product':
                        sig = random_state(anc, 'skewed') if anc > 1 else np.eye(1)
                        rho = np.kron(np.eye(4) / 4, sig)
                        Vr = rand_unitary_near(d, t)
                        rho = Vr @ rho @ Vr.conj().T
                    else:
                        rho = random_state(d, kind)
                    xi = psd_sqrt(rho)
                    e = model_precision(U, UJ, eqs, b, xi)
                    smallest_e = min(smallest_e, e)
                    B = [rounding(A) for A in U]
                    tag = f'anc={anc},t={t},{kind}'
                    for (ij, p) in loss_probabilities(B, eqs, b, xi):
                        T.add(Cs * e * e - p, tag + f',pair={ij}')
                        if e > 1e-9 and p / (e * e) > worst_ratio:
                            worst_ratio, worst_ratio_at = p / (e * e), tag + f',pair={ij},e={e:.2e}'
                    # Lemma 5.3(a) for the first equation, k = 3
                    V = eqs[0]
                    c = [hs(B[j] @ xi - xi @ B[j]) for j in V]
                    kap = {(j, l): hs((B[V[j]] @ B[V[l]] - B[V[l]] @ B[V[j]]) @ xi) for j in range(3) for l in range(3)}
                    I = np.eye(d)
                    for jj in range(3):
                        dj = c[jj] + sum(kap[(jj, l)] / math.sqrt(2) + sum(c[tt] for tt in range(l)) for l in range(jj))
                        p = 0.0
                        for a in itertools.product((1, -1), repeat=3):
                            K = np.eye(d, dtype=complex)
                            for l in range(3):
                                K = ((I + a[l] * B[V[l]].T) / 2) @ K
                            for cc in (1, -1):
                                if a[jj] != cc:
                                    p += hs(K @ xi.T @ ((I + cc * B[V[jj]]) / 2).T) ** 2
                        Tseq.add(dj * dj / 4 - p, tag + f',j={jj}')
    # optimiser: maximise (worst pair loss)/e^2 near the exact model, with the state free
    for seed in (21, 22):
        rng = np.random.default_rng(seed)
        d = 4
        nH = 2 * d * d

        def unpack(th):
            U = [expm(1j * herm_from_params(th[k * nH:(k + 1) * nH], d)) @ A for k, A in enumerate(ops)]
            UJ = -expm(1j * herm_from_params(th[9 * nH:10 * nH], d))
            rho = state_from_params(th[10 * nH:], d)
            return U, UJ, psd_sqrt(rho)

        def obj(th):
            U, UJ, xi = unpack(th)
            e = model_precision(U, UJ, eqs, b, xi)
            B = [rounding(A) for A in U]
            p = max(q for _, q in loss_probabilities(B, eqs, b, xi))
            return -p / max(e * e, 1e-12)

        th0 = 0.01 * rng.normal(size=10 * nH + 2 * d * d)
        th0[10 * nH:10 * nH + d * d] += np.eye(d).ravel()
        res = minimize(obj, th0, method='L-BFGS-B', options={'maxiter': 60})
        U, UJ, xi = unpack(res.x)
        e = model_precision(U, UJ, eqs, b, xi)
        r = -res.fun
        T.add(Cs - r, f'optimiser seed={seed}, e={e:.2e}, loss/e^2={r:.3f}')
        if r > worst_ratio:
            worst_ratio, worst_ratio_at = r, f'optimiser seed={seed}, e={e:.2e}'
    print(f'  largest loss/e^2 over instances with e>0: {worst_ratio:.3f} (bound C_3 = {Cs:.1f}) at {worst_ratio_at}')
    ok = T.report() and Tseq.report()
    # negative control: drop (S2) from the precision; the loss is then not O(e'^2)
    rng = np.random.default_rng(7)
    d = 8
    base = [np.kron(P, np.eye(2)) for P in ops]
    # a nearly pure state: the relations hold exactly, only (S2) fails
    v = np.zeros(d, dtype=complex); v[0] = 1
    rho = 0.98 * np.outer(v, v) + 0.02 * np.eye(d) / d
    xi = psd_sqrt(rho)
    U = base
    UJ = -np.eye(d)
    I = np.eye(d)
    e_full = model_precision(U, UJ, eqs, b, xi)
    B = [rounding(A) for A in U]
    worst = max(p for _, p in loss_probabilities(B, eqs, b, xi))
    print(f'  negative control (exact operators, state not commuting with them): (S1),(S3) defects 0, '
          f'(S2)-precision e={e_full:.3f}, worst pair loss={worst:.3f}')
    print('    The relations hold exactly, yet a pair is lost with constant probability: the state commutators of (S2)')
    print('    cannot be dropped from the precision in thm:return.')
    return ok and worst > 0.05

# ============================================================================= profile of c in K (thm:K-profile)

def K_model(m):
    d = 2 * m
    z = np.exp(2j * np.pi * np.arange(d) / d)
    Y = np.diag(z)
    A = np.zeros((d, d), dtype=complex)
    for j in range(d):
        A[(j + m) % d, j] = 1
    B = -A
    C = -np.eye(d, dtype=complex)
    varpi = [2 * (j % m) + j // m for j in range(d)]
    X = np.zeros((d, d), dtype=complex)
    for j in range(d):
        X[j, varpi[j]] = 1  # X e_{varpi(j)} = e_j
    return A, B, C, X, Y


def K_precision(A, B, C, X, Y, xi):
    d = xi.shape[0]
    I = np.eye(d)
    inv = np.linalg.inv
    rels = [X @ Y @ inv(X) @ inv(Y) @ inv(Y), X @ C @ inv(X) @ inv(C), Y @ A @ inv(Y) @ inv(B), Y @ B @ inv(Y) @ inv(A),
            inv(C) @ A @ B, A @ A, B @ B, C @ C]
    vals = [hs((R - I) @ xi) for R in rels]
    vals += [hs(S @ xi - xi @ S) for S in (A, B, C, X, Y)]
    vals.append(hs((C + I) @ xi))
    return max(vals)


def run_K():
    print('Profile of c in K in a state (thm:K-profile): d >= 1/(29 e)')
    T = Tally('29 e d - 1 >= 0')
    for m in [1, 2, 3, 4, 6, 8, 12]:
        d = 2 * m
        A0, B0, C0, X0, Y0 = K_model(m)
        e_flat = K_precision(A0, B0, C0, X0, Y0, np.eye(d) / math.sqrt(d))
        T.add(29 * e_flat * d - 1, f'exact model m={m}, flat')
        for t in [0.0, 0.01, 0.05, 0.2, 1.0]:
            for kind in ['flat', 'full', 'lowrank', 'pure', 'skewed']:
                for rep in range(3):
                    ops = [rand_unitary_near(d, t) @ P @ rand_unitary_near(d, t) for P in (A0, B0, C0, X0, Y0)]
                    rho = random_state(d, kind)
                    e = K_precision(*ops, psd_sqrt(rho))
                    T.add(29 * e * d - 1, f'm={m},t={t},{kind}')
    # optimiser over unitaries near the exact model and the state, minimising 29 e d
    for m, seed in [(1, 11), (2, 12), (3, 13)]:
        rng = np.random.default_rng(seed)
        d = 2 * m
        base = K_model(m)
        nH = 2 * d * d

        def obj(th):
            ops = [expm(1j * herm_from_params(th[k * nH:(k + 1) * nH], d)) @ P for k, P in enumerate(base)]
            rho = state_from_params(th[5 * nH:], d)
            return K_precision(*ops, psd_sqrt(rho))

        for start in range(2):
            th0 = 0.05 * rng.normal(size=5 * nH + 2 * d * d)
            th0[5 * nH:5 * nH + d * d] += np.eye(d).ravel()
            res = minimize(obj, th0, method='L-BFGS-B', options={'maxiter': 200})
            T.add(29 * res.fun * d - 1, f'optimiser m={m},start={start}, e={res.fun:.3e}')
    return T.report()

# =============================================================================

def main():
    which = sys.argv[1] if len(sys.argv) > 1 else 'all'
    runs = {'count': run_count, 'rounding': run_rounding, 'return': run_return, 'K': run_K}
    names = list(runs) if which == 'all' else [which]
    ok = True
    for n in names:
        ok = runs[n]() and ok
        print()
    print('ALL CHECKS PASSED' if ok else 'SOME CHECK FAILED')
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
