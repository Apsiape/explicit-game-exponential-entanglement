#!/usr/bin/env python3
"""The balanced lift behind the upper bound for the Slofstra-Vidick game (Lemma 11.13 [lem:sv-lift]), with the rank
obstruction for the literal lifts as a negative control.

Imports nothing from the other programs of anc/; needs numpy. All checks are floating-point evaluations of small explicit
matrices, with tolerance 1e-9. No proof depends on this program: Lemma 11.13 is proved in the paper.

The group K of (21) [eq:K] has the involutive generators a, b, c, the linear set {a, b, c} (with its commutations, as
Slofstra and Vidick add them), and the non-involutive generators y < x, with x y x^-1 = y^2. The model of Example 11.11
[ex:K-model] lives on C^d, d = 2m: Y diagonal, A, B = -A, C = -I, and X a permutation matrix. Only the relator
x y x^-1 y^-2 is inexact, with defect e_m = sqrt(2) sin(pi/(2m)).

  Part 1  the model: every relator of K, and the defect e_m.
  Part 2  negative control. The literal lifts of Slofstra's Proposition 4.8, applied to y and then to x, double the
          dimension twice; they are approximate representations of the eliminated presentations, but the marked
          involution becomes W = (-I_d) + I_3d. For every unitary T, ||T W T^* + W||_f^2 >= 2; the program tests the
          exchange of the two halves, all 24 permutations of the four blocks, and random unitaries, and confirms that 2
          is attained. So the relation t c t = c J, with J = -I, fails by at least sqrt(2) at every precision.
  Part 3  the balanced lift of Lemma 11.13. Step 1 eliminates y as in Slofstra's Proposition 4.8 (dimension 2d,
          c -> (-I_d) + I_d). Step 2 eliminates x without doubling: an involutive permutation tau with tau X tau = X^-1
          (each cycle of X reflected) gives f' = tau + tau and v' = tau X + tau X, involutions with f' v' = X + X.
          Every relator of the presentations reached keeps at most the defect e_m. Step 3 adjoins t, J and u (the
          linear set {c, u} with right-hand side J, and t c t = u); every new relator holds exactly.
  Part 4  Step 4 builds, as in Slofstra's Lemma 4.4 and Proposition 4.2, the solution group of the resulting
          linear-plus-conjugacy presentation and the lift of Slofstra's Remark 4.5 to dimension 8d. It evaluates every
          relator of the solution group (squares, commutators with J, commutators inside equations, and the product of
          each equation in every order of its variables), checks J -> -I, and compares the largest defect with
          75 e_m, the constant of that remark.
  Part 5  the resulting strategies (Theorem 5.4 [thm:return], flat state, s = 3): local dimension 16 m and losing
          probability at most C_3 delta_m^2, with delta_m the largest defect of Part 4; m delta_m stays bounded.

Usage:  python3 -I sv_balanced_lift.py        exit status 0 exactly when every check passes
"""
import itertools
import math
import sys

import numpy as np

TOL = 1e-9
FAILS = []
MS = range(1, 9)


def check(cond, msg):
    print(('PASS  ' if cond else 'FAIL  ') + msg, flush=True)
    if not cond:
        FAILS.append(msg)


def fnorm(a):
    """Normalized Hilbert-Schmidt norm ||a||_f = (Tr a^* a / dim)^(1/2)."""
    return float(np.linalg.norm(a) / math.sqrt(a.shape[0]))


def defect(a):
    return fnorm(a - np.eye(a.shape[0]))


def dsum(a, b):
    return np.block([[a, np.zeros((a.shape[0], b.shape[1]))], [np.zeros((b.shape[0], a.shape[1])), b]])


def adiag(a, b):
    """[[0, a], [b, 0]] for square blocks of one size."""
    z = np.zeros_like(a)
    return np.block([[z, a], [b, z]])


def omega(n):
    """The exchange of the two summands of C^n + C^n."""
    i = np.eye(n)
    return adiag(i, i)


def inv(u):
    return u.conj().T


def word(rep, letters):
    """Product of rep[g] (or its inverse, for a name ending in '-') in the order written."""
    n = next(iter(rep.values())).shape[0]
    out = np.eye(n, dtype=complex)
    for g in letters:
        out = out @ (inv(rep[g[:-1]]) if g.endswith('-') else rep[g])
    return out


def is_involution(u):
    n = u.shape[0]
    return float(np.abs(u @ u - np.eye(n)).max()) < TOL and float(np.abs(u - inv(u)).max()) < TOL


# ------------------------------------------------------------------------------------------- the model and K
def k_model(m):
    d = 2 * m
    Y = np.diag(np.exp(2j * np.pi * np.arange(d) / d))
    A = np.zeros((d, d), dtype=complex)
    for j in range(d):
        A[(j + m) % d, j] = 1
    X = np.zeros((d, d), dtype=complex)
    for j in range(d):
        X[j, 2 * (j % m) + j // m] = 1          # X e_varpi(j) = e_j, varpi(j) = 2 (j mod m) + floor(j/m)
    return {'a': A, 'b': -A, 'c': -np.eye(d, dtype=complex), 'x': X, 'y': Y}


# relators of K, (21) [eq:K], with the commutations of the linear set {a, b, c} that Slofstra and Vidick add
K_REL = [('x', 'y', 'x-', 'y-', 'y-'), ('x', 'c', 'x-', 'c-'), ('y', 'a', 'y-', 'b-'), ('y', 'b', 'y-', 'a-'),
         ('c-', 'a', 'b'), ('a', 'a'), ('b', 'b'), ('c', 'c'),
         ('a', 'b', 'a-', 'b-'), ('a', 'c', 'a-', 'c-'), ('b', 'c', 'b-', 'c-')]


def reversal(X):
    """An involutive permutation matrix tau with tau X tau = X^-1, for a permutation matrix X: reflect each cycle."""
    n = X.shape[0]
    sigma = [int(np.argmax(np.abs(X[:, i]))) for i in range(n)]      # X e_i = e_sigma(i)
    tau, seen = list(range(n)), [False] * n
    for start in range(n):
        if seen[start]:
            continue
        cyc, i = [], start
        while not seen[i]:
            seen[i] = True
            cyc.append(i)
            i = sigma[i]
        for s, ci in enumerate(cyc):
            tau[ci] = cyc[(-s) % len(cyc)]
    T = np.zeros((n, n), dtype=complex)
    for i in range(n):
        T[tau[i], i] = 1
    return T


# ------------------------------------------------------------------------------------------- presentations
# A presentation is (involutive generators, linear sets [(members, b)], conjugacy triples [(i, j, k)] meaning
# i j i = k, other relators [letter tuples]). Every relator is evaluated by relators().
def relators(pres, rep, with_J):
    gens, lin, conj, other = pres
    out = []
    for g in gens:
        out.append(('square ' + g, (g, g)))
    for (V, b) in lin:
        for order in itertools.permutations(V):
            out.append(('product %s%s' % ('J ' * b, ' '.join(order)), ('J',) * b + tuple(order)))
        for u, v in itertools.combinations(V, 2):
            out.append(('commutator %s %s' % (u, v), (u, v, u + '-', v + '-')))
    for (i, j, k) in conj:
        out.append(('conjugacy %s %s %s = %s' % (i, j, i, k), (i, j, i, k + '-')))
    for r in other:
        out.append((' '.join(r), r))
    if with_J:
        out.append(('square J', ('J', 'J')))
        for g in gens:
            out.append(('commutator %s J' % g, (g, 'J', g + '-', 'J-')))
    return [(name, defect(word(rep, r))) for name, r in out]


def step1(phi):
    """Slofstra's Proposition 4.8 for y: f, v with y = f v, f x = x f; y a y^-1 = b and y b y^-1 = a become
    v a v = Za, f Za f = b, v b v = Zb, f Zb f = a; x y x^-1 = y^2 becomes v f v = W, x v x^-1 = W."""
    d = phi['a'].shape[0]
    I = np.eye(d, dtype=complex)
    g = {s: dsum(phi[s], I) for s in 'abc'}
    g['f'] = omega(d)
    g['v'] = adiag(inv(phi['y']), phi['y'])
    g['x'] = dsum(phi['x'], phi['x'])
    g['Za'] = g['v'] @ g['a'] @ g['v']
    g['Zb'] = g['v'] @ g['b'] @ g['v']
    g['W'] = g['v'] @ g['f'] @ g['v']
    pres = (['a', 'b', 'c', 'f', 'v', 'Za', 'Zb', 'W'], [(('a', 'b', 'c'), 0)],
            [('v', 'a', 'Za'), ('f', 'Za', 'b'), ('v', 'b', 'Zb'), ('f', 'Zb', 'a'), ('v', 'f', 'W')],
            [('x', 'c', 'x-', 'c-'), ('x', 'f', 'x-', 'f-'), ('x', 'v', 'x-', 'W-')])
    return pres, g


def step2(pres1, g1, F, V):
    """Slofstra's Proposition 4.8 for x (the last non-involutive generator): f', v' with x = f' v'; each relation
    x s x^-1 = s' becomes v' s v' = Z's, f' Z's f' = s'. The images F, V of f', v' are given; nothing is doubled."""
    gens, lin, conj, other = pres1
    g = {k: M for k, M in g1.items() if k != 'x'}
    g["f'"], g["v'"] = F, V
    new_gens, new_conj = list(gens) + ["f'", "v'"], list(conj)
    for (s, t) in (('c', 'c'), ('f', 'f'), ('v', 'W')):
        z = "Z'" + s
        g[z] = V @ g[s] @ V
        new_gens.append(z)
        new_conj += [("v'", s, z), ("f'", z, t)]
    return (new_gens, list(lin), new_conj, []), g


def literal_step2(pres1, g1):
    """The literal second lift of Slofstra's Proposition 4.8: every involutive generator becomes rho(s) + I, f' the
    exchange, v' = [[0, rho(x)^*], [rho(x), 0]]."""
    D = g1['a'].shape[0]
    I = np.eye(D, dtype=complex)
    g = {k: dsum(M, I) for k, M in g1.items() if k != 'x'}
    g['x'] = g1['x']                                   # dropped by step2; x is now read as f' v'
    return step2(pres1, g, omega(D), adiag(inv(g1['x']), g1['x']))


def step3(pres2, g2):
    """Adjoin t, J and u: the linear set {c, u} with right-hand side J, and the conjugacy t c t = u."""
    D = g2['c'].shape[0]
    g = dict(g2)
    g['t'] = omega(D // 2)
    g['J'] = -np.eye(D, dtype=complex)
    g['u'] = -g2['c']
    gens, lin, conj, other = pres2
    return (list(gens) + ['t', 'u'], list(lin) + [(('c', 'u'), 1)], list(conj) + [('t', 'c', 'u')], []), g


# ------------------------------------------------------------------------------------------- Step 4
def slofstra_nice(pres, g):
    """Slofstra's Lemma 4.4: generators y_j, z_j, w_j for every generator x_j, and f*, with the linear sets
    {x_j, y_j, z_j}, {x_j, f*, w_j}, {g_jk, y_j, z_k} and the nice conjugacies f* y_j f* = z_j, w_i y_j w_i = z_k.
    The lift doubles: x_j -> g(x_j) + g(x_j), J -> g(J) + g(J), y_j -> g(x_j) + I, z_j -> I + g(x_j),
    w_j -> [[0, g(x_j)], [g(x_j), 0]], f* -> the exchange, g_jk -> g(x_j) + g(x_k)."""
    gens, lin, conj, _ = pres
    D = g['J'].shape[0]
    I = np.eye(D, dtype=complex)
    h = {x: dsum(g[x], g[x]) for x in gens}
    h['J'] = dsum(g['J'], g['J'])
    h['f*'] = omega(D)
    new_gens, new_lin, new_conj = list(gens) + ['f*'], list(lin), []
    for x in gens:
        y, z, w = 'y[%s]' % x, 'z[%s]' % x, 'w[%s]' % x
        h[y], h[z], h[w] = dsum(g[x], I), dsum(I, g[x]), adiag(g[x], g[x])
        new_gens += [y, z, w]
        new_lin += [((x, y, z), 0), ((x, 'f*', w), 0)]
        new_conj.append(('f*', y, z))
    for (i, j, k) in conj:
        gg = 'g[%s,%s]' % (j, k)
        if gg not in h:
            h[gg] = dsum(g[j], g[k])
            new_gens.append(gg)
            new_lin.append(((gg, 'y[%s]' % j, 'z[%s]' % k), 0))
        new_conj.append(('w[%s]' % i, 'y[%s]' % j, 'z[%s]' % k))
    return (new_gens, new_lin, new_conj, []), h


def slofstra_gadgets(pres, g):
    """Slofstra's Proposition 4.2: each nice conjugacy i j i = k is replaced by seven variables and the six equations
    x_i y1 y2 = x_j y2 y3 = y3 y4 y5 = x_i y5 y6 = x_k y6 y7 = y1 y4 y7 = e, with the lift of its proof."""
    gens, lin, conj, _ = pres
    D = g['J'].shape[0]
    I = np.eye(D, dtype=complex)
    h = {x: dsum(g[x], g[x]) for x in gens}
    h['J'] = dsum(g['J'], g['J'])
    new_gens, new_lin = list(gens), list(lin)
    for n, (i, j, k) in enumerate(conj):
        Ui, Uj, Uk = g[i], g[j], g[k]
        y = ['y%d#%d' % (q, n) for q in range(1, 8)]
        vals = [adiag(Ui, Ui), omega(D), adiag(Uj, Uj), adiag(Uj @ Ui, Ui @ Uj), dsum(Uj @ Ui @ Uj, Ui),
                dsum(Uj @ Uk, I), dsum(Uj, Uk)]
        for name, M in zip(y, vals):
            h[name] = M
        new_gens += y
        new_lin += [((i, y[0], y[1]), 0), ((j, y[1], y[2]), 0), ((y[2], y[3], y[4]), 0), ((i, y[4], y[5]), 0),
                    ((k, y[5], y[6]), 0), ((y[0], y[3], y[6]), 0)]
    return (new_gens, new_lin, [], []), h


# ------------------------------------------------------------------------------------------- the checks
def main():
    print('Part 1. The model of Example 11.11 [ex:K-model] on C^d, d = 2m, and the relators of K')
    worst_model = 0.0
    for m in MS:
        phi = k_model(m)
        e_m = math.sqrt(2) * math.sin(math.pi / (2 * m))
        dfs = [defect(word(phi, r)) for r in K_REL]
        worst_model = max(worst_model, abs(dfs[0] - e_m), max(dfs[1:]))
    check(worst_model < TOL, 'm = 1..8: x y x^-1 y^-2 has defect sqrt(2) sin(pi/(2m)), every other relator of K defect 0 '
          '(largest deviation %.1e)' % worst_model)

    print('\nPart 2. Negative control: the literal lifts of Slofstra\'s Proposition 4.8 for y and then x')
    g_rng = np.random.default_rng(20261026)
    min_ratio, attained, mult_ok, literal_ok, trace_ok = math.inf, math.inf, True, True, True
    for m in MS:
        phi = k_model(m)
        d = 2 * m
        e_m = math.sqrt(2) * math.sin(math.pi / (2 * m))
        p1, g1 = step1(phi)
        p2, g2 = literal_step2(p1, g1)
        Wm = g2['c']
        signs = np.real(np.diag(Wm))
        mult_ok &= int((signs < 0).sum()) == d and int((signs > 0).sum()) == 3 * d
        literal_ok &= max(v for _, v in relators(p2, g2, False)) <= e_m + TOL
        n4 = 4 * d
        cands = [omega(2 * d)]
        for perm in itertools.permutations(range(4)):
            P = np.zeros((n4, n4), dtype=complex)
            for i, pi in enumerate(perm):
                P[pi * d:(pi + 1) * d, i * d:(i + 1) * d] = np.eye(d)
            cands.append(P)
        for _ in range(100):
            q, r = np.linalg.qr(g_rng.normal(size=(n4, n4)) + 1j * g_rng.normal(size=(n4, n4)))
            cands.append(q * (np.diag(r) / np.abs(np.diag(r))))
        vals = [fnorm(T @ Wm @ inv(T) + Wm) ** 2 for T in cands]
        min_ratio = min(min_ratio, min(vals) / 2)
        attained = min(attained, abs(min(vals) - 2))
        trace_ok &= abs(np.real(np.trace(Wm)) / n4 - 0.5) < TOL
    check(mult_ok, 'm = 1..8: the literal marker W = g(c) has the eigenvalue -1 with multiplicity d and +1 with 3d')
    check(trace_ok, 'm = 1..8: tr W = 1/2, so W is not conjugate to -W')
    check(literal_ok, 'm = 1..8: the literal lifts are approximate representations of the eliminated presentation '
          '(every relator defect at most e_m): the failure is only one of balance')
    check(min_ratio >= 1 - TOL, 'rank obstruction: min over the exchange of halves, the 24 block permutations and 100 '
          'random unitaries of ||T W T^* + W||_f^2 / 2 is %.9f (>= 1)' % min_ratio)
    check(attained < TOL, 'the bound ||T W T^* + W||_f^2 >= 2 is attained by a block permutation (gap %.1e)' % attained)
    lit_tct = []
    for m in MS:
        p1, g1 = step1(k_model(m))
        p2, g2 = literal_step2(p1, g1)
        p3, g3 = step3(p2, g2)
        lit_tct.append(defect(word(g3, ('t', 'c', 't', 'u-'))))
    check(all(abs(v - math.sqrt(2)) < TOL for v in lit_tct), 'with t the exchange of halves, the relator t c t u^-1 '
          '(u = J c) of the literal lift has defect sqrt(2) for every m, whatever the precision of the model')

    print('\nPart 3. The balanced lift of Lemma 11.13 [lem:sv-lift]')
    rev_ok, step1_ok, step2_ok, step3_ok, bal_ok = True, True, True, True, True
    worst1 = worst2 = worst3 = 0.0
    for m in MS:
        phi = k_model(m)
        d = 2 * m
        e_m = math.sqrt(2) * math.sin(math.pi / (2 * m))
        X = phi['x']
        tau = reversal(X)
        F, V = dsum(tau, tau), dsum(tau @ X, tau @ X)
        rev_ok &= is_involution(tau) and float(np.abs(tau @ X @ tau - inv(X)).max()) < TOL
        rev_ok &= is_involution(F) and is_involution(V) and float(np.abs(F @ V - dsum(X, X)).max()) < TOL
        p1, g1 = step1(phi)
        r1 = relators(p1, g1, False)
        worst1 = max(worst1, max(v for _, v in r1) - e_m)
        step1_ok &= float(np.abs(g1['f'] @ g1['v'] - dsum(phi['y'], inv(phi['y']))).max()) < TOL
        step1_ok &= float(np.abs(g1['c'] - dsum(-np.eye(d), np.eye(d))).max()) < TOL
        p2, g2 = step2(p1, g1, F, V)
        r2 = relators(p2, g2, False)
        worst2 = max(worst2, max(v for _, v in r2) - e_m)
        step2_ok &= all(is_involution(g2[s]) for s in p2[0])
        p3, g3 = step3(p2, g2)
        new = [v for name, v in relators(p3, g3, True) if name not in dict(r2)]
        worst3 = max(worst3, max(new))
        bal_ok &= abs(float(np.real(np.trace(g3['c'])))) < TOL
        bal_ok &= float(np.abs(g3['t'] @ g3['c'] @ g3['t'] + g3['c']).max()) < TOL
    check(rev_ok, 'm = 1..8: tau is an involutive permutation with tau X tau = X^-1; f\' = tau + tau and v\' = tau X + tau X '
          'are involutions with f\' v\' = X + X')
    check(step1_ok and worst1 <= TOL, 'Step 1 (y, doubled): f v = Y + Y^*, c -> (-I_d) + I_d, and every relator of the '
          'presentation reached has defect at most e_m (largest excess %.1e)' % worst1)
    check(step2_ok and worst2 <= TOL, 'Step 2 (x, not doubled): every generator is an involution, and every relator of the '
          'all-involutive presentation reached has defect at most e_m (largest excess %.1e)' % worst2)
    check(worst3 < TOL, 'Step 3: t^2, u^2, J^2, [s, J], the row J c u, [c, u] and t c t u^-1 hold exactly (largest '
          'defect %.1e)' % worst3)
    check(bal_ok, 'the marker is balanced: tr g(c) = 0 and t c t = -c exactly, for t the exchange of the two copies of C^d')

    print('\nPart 4. Step 4: the solution group (Slofstra\'s Lemma 4.4 and Proposition 4.2) and the lift of his Remark 4.5')
    deltas, ratio_ok, J_ok, dims_ok, sizes = {}, True, True, True, None
    for m in MS:
        phi = k_model(m)
        d = 2 * m
        e_m = math.sqrt(2) * math.sin(math.pi / (2 * m))
        tau = reversal(phi['x'])
        p1, g1 = step1(phi)
        p2, g2 = step2(p1, g1, dsum(tau, tau), dsum(tau @ phi['x'], tau @ phi['x']))
        p3, g3 = step3(p2, g2)
        pn, gn = slofstra_nice(p3, g3)
        pG, gG = slofstra_gadgets(pn, gn)
        dims_ok &= gG['J'].shape[0] == 8 * d
        J_ok &= float(np.abs(gG['J'] + np.eye(8 * d)).max()) < TOL
        rG = relators(pG, gG, True)
        delta = max(v for _, v in rG)
        deltas[m] = (delta, e_m)
        ratio_ok &= delta <= 75 * e_m + TOL
        sizes = (len(pG[0]), len(pG[1]), max(len(V) for V, _ in pG[1]), len(rG))
    check(dims_ok and J_ok, 'm = 1..8: the lift of the solution group lives on C^(8d) = C^(16m), with J -> -I exactly')
    worst_ratio = max(dl / e for dl, e in deltas.values())
    check(ratio_ok, 'm = 1..8: every relator of the solution group has defect at most 75 e_m (largest ratio defect/e_m '
          '= %.4f)' % worst_ratio)
    print('INFO  solution group as built here: %d variables, %d equations of at most %d variables, %d relators checked '
          '(products in every order); Slofstra and Vidick leave the encoding of t c t = c J implicit, and the one used '
          'here is that of Step 2 of Lemma B.1 [lem:gadget]' % sizes)

    print('\nPart 5. Strategies (Theorem 5.4 [thm:return], flat state, s = 3)')
    nu = lambda l: 3 * (1 + (l - 1) * (l - 2) / 2) + 13 * (l - 1) / math.sqrt(2)    # noqa: E731
    C3 = 0.25 * (nu(3) ** 2 + (3 ** 2 + 2 + sum(nu(l) for l in range(1, 4))) ** 2)
    print('      m   local dim 16m   largest defect delta_m   m delta_m   loss bound C_3 delta_m^2')
    for m, (dl, e) in deltas.items():
        print('    %3d   %13d   %22.6e   %9.6f   %24.6e' % (m, 16 * m, dl, m * dl, C3 * dl * dl))
    md = [m * dl for m, (dl, e) in deltas.items()]
    check(max(md) <= 75 * math.pi / math.sqrt(2), 'm delta_m <= 75 pi / sqrt(2) for m = 1..8 (largest %.4f), so the '
          'losing probability is O(1/m^2) at local dimension 16m: dimension O(eps^-1/2)' % max(md))

    print('\n%s' % ('ALL CHECKS PASSED' if not FAILS else 'FAILURES: %d' % len(FAILS)))
    return 1 if FAILS else 0


if __name__ == '__main__':
    sys.exit(main())
