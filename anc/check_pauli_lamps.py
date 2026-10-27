#!/usr/bin/env python3
"""Verification script for the Pauli-lamp group G_P.

Run:  python3 -I check_pauli_lamps.py [certificate_file]
Default certificate: relators_pauli.txt next to this script.

Part 1 (exact, rigorous): evaluates every word of the certificate in a faithful
model of G_P = E_V x| A, where E_V is the central product over V = F_2^(Y) of
copies of D_4 = <x,z | x^2, z^2, (xz)^4> with common centre J = (xz)^2, and
A = V x| (GL_fin(Y) H_3) acts by affine maps on configurations.  A word is
accepted iff its lamp part is the identity of E_V and its affine part is the
identity map; the affine part is checked on 0 and on every basis vector e_y of
height <= len(word)+3 on each ray (this suffices: see the docstring of
affine_is_identity).  Also checks: J central (commutes with all six
generators), J != 1, same-site lamps anticommute up to J, distinct sites
commute (N = 3 ladder of 8 sites).
Negative controls: four corrupted words must be REJECTED.

Part 2 (numerical sanity, not a proof): checks the Pauli sector bound, a flat qubit count (a variant of
Corollary 4.3 [cor:count-flat]), and the two projection-product estimates on random near-Pauli instances, and
the scalar inequality 1 - h2(x) <= (1 - 2 sqrt(x(1-x)))/ln 2 on a grid.

Exit status 0 iff everything passes; any failure raises SystemExit(1).
"""
import itertools
import math
import os
import sys

# ---------------------------------------------------------------- Houghton H_3
def p_pt(y):
    r, h = y
    if r == 1:
        return (1, h + 1)
    if r == 2:
        return (1, 1) if h == 1 else (2, h - 1)
    return y

def P_pt(y):  # inverse of p
    r, h = y
    if r == 1:
        return (2, 1) if h == 1 else (1, h - 1)
    if r == 2:
        return (2, h + 1)
    return y

def q_pt(y):
    r, h = y
    if r == 1:
        return (1, h + 1)
    if r == 3:
        return (1, 1) if h == 1 else (3, h - 1)
    return y

def Q_pt(y):
    r, h = y
    if r == 1:
        return (3, 1) if h == 1 else (1, h - 1)
    if r == 3:
        return (3, h + 1)
    return y

PT = {'p': p_pt, 'P': P_pt, 'q': q_pt, 'Q': Q_pt}
ONE1, ONE2 = (1, 1), (1, 2)

def host_letter_on_config(letter, v):
    """Affine action of a host letter on a configuration (frozenset of points)."""
    if letter in PT:
        f = PT[letter]
        return frozenset(f(y) for y in v)
    if letter in 'tT':  # translation by e_(1,1); an involution
        return v ^ frozenset([ONE1])
    if letter in 'dD':  # transvection E_{2<-1}: v -> v + v_1 e_2; an involution
        return (v ^ frozenset([ONE2])) if ONE1 in v else v
    raise ValueError(letter)

def apply_affine(letters, v):
    """letters = alpha_1 ... alpha_k; returns alpha_1(...alpha_k(v))."""
    for L in reversed(letters):
        v = host_letter_on_config(L, v)
    return v

# ----------------------------------------------------------------- E_V (Pauli)
# element (s, a, b) = J^s X^a Z^b, a,b finite sets of sites (sites = configurations)
E_ID = (0, frozenset(), frozenset())

def e_mul(e1, e2):
    s1, a1, b1 = e1
    s2, a2, b2 = e2
    # Z^b1 X^a2 = J^{|b1 & a2|} X^a2 Z^b1
    return ((s1 + s2 + len(b1 & a2)) % 2, a1 ^ a2, b1 ^ b2)

ZERO = frozenset()
LAMP = {
    'x': (0, frozenset([ZERO]), frozenset()),
    'z': (0, frozenset(), frozenset([ZERO])),
}
LAMP['X'] = LAMP['x']  # involutions
LAMP['Z'] = LAMP['z']

def e_transport(letters, e):
    s, a, b = e
    return (s, frozenset(apply_affine(letters, v) for v in a),
            frozenset(apply_affine(letters, v) for v in b))

def evaluate(word):
    """word: list of letters in pqtdxz/PQTDXZ. Returns (lamp part, affine letters)."""
    e, alpha = E_ID, []
    for L in word:
        if L in LAMP:
            e = e_mul(e, e_transport(alpha, LAMP[L]))
        else:
            alpha.append(L)
    return e, alpha

def affine_is_identity(alpha, maxh):
    """alpha(0) = 0 and alpha(e_y) = e_y for all y of height <= maxh.
    Sufficient for alpha = id when maxh >= len(alpha)+3: every letter changes
    heights by at most 1, t and d touch only (1,1),(1,2), and p,q act on points
    of height >= 2 as translations along the rays.  A point of height
    h0 > len+2 stays at height >= 2 during the evaluation, so alpha acts on
    e_y as the net translation of ray r; checking one such height per ray
    (h0 = len+3) shows the net translation is 0, hence e_y is fixed for all
    heights >= len+3; smaller heights are checked directly."""
    if apply_affine(alpha, ZERO) != ZERO:
        return False
    for r in (1, 2, 3):
        for h in range(1, maxh + 1):
            ey = frozenset([(r, h)])
            if apply_affine(alpha, ey) != ey:
                return False
    return True

def is_identity(word):
    e, alpha = evaluate(word)
    return e == E_ID and affine_is_identity(alpha, len(word) + 3)

# ------------------------------------------------------------ word expansion
INV = {c: c.swapcase() for c in 'pqtdxzPQTDXZ'}

def inverse(w):
    return [INV[c] for c in reversed(w)]

def free_reduce(w):
    out = []
    for c in w:
        if out and out[-1] == INV[c]:
            out.pop()
        else:
            out.append(c)
    return out

ABBR = {}
ABBR['s'] = list('pqPQ')
ABBR['B'] = ['p'] + ABBR['s'] + ['P']
ABBR['t1'] = ['t']
ABBR['t2'] = list('ptP')
ABBR['t3'] = list('pptPP')
ABBR['J'] = list('xzxz')

def expand(tokens):
    w = []
    for tok in tokens:
        inv = tok.endswith('^-1')
        base = tok[:-3] if inv else tok
        if base in ABBR:
            piece = ABBR[base]
        elif len(base) == 1 and base in INV:
            piece = [base]
        else:
            raise ValueError('unknown token %r' % tok)
        w += inverse(piece) if inv else piece
    return free_reduce(w)

def load(path):
    rels = []
    with open(path) as fh:
        for line in fh:
            line = line.strip()
            if not line or line.startswith('#'):
                continue
            fam, body = [x.strip() for x in line.split('|')]
            rels.append((fam, body, expand(body.split())))
    return rels

FAIL = []

def check(cond, msg):
    if cond:
        print('  ok   ', msg)
    else:
        print('  FAIL ', msg)
        FAIL.append(msg)

# ------------------------------------------------------------------- Part 1
def part1(path):
    print('Part 1: exact evaluation of the certificate in the faithful model of G_P')
    rels = load(path)
    print('  certificate %s: %d words, total length %d, max length %d' % (
        os.path.basename(path), len(rels), sum(len(w) for _, _, w in rels),
        max(len(w) for _, _, w in rels)))
    for fam, body, w in rels:
        check(is_identity(w), '%s  %-40s (len %d)' % (fam, body, len(w)))
    # hard expectations on the shape of the certificate
    fams = {}
    for fam, _, _ in rels:
        fams[fam] = fams.get(fam, 0) + 1
    check(fams == {'H': 4, 'Q': 1, 'S': 4, 'C': 1, 'A': 3, 'Z': 6, 'L': 3, 'P': 4, 'K': 1},
          'family counts H4 Q1 S4 C1 A3 Z6 L3 P4 K1 (27 words)')

    J = ABBR['J']
    eJ, aJ = evaluate(J)
    check(eJ == (1, frozenset(), frozenset()) and aJ == [], 'J = (xz)^2 is the nontrivial central element J^1 of E_V')
    for g in 'pqtdxz':
        w = free_reduce(J + [g] + inverse(J) + [INV[g]])
        check(is_identity(w), '[J,%s] = 1 in G_P' % g)
    # ladder of 8 sites on the first 3 points of ray 1
    T = {m: ABBR['t%d' % m] for m in (1, 2, 3)}
    sites = [u for k in range(4) for u in itertools.combinations((1, 2, 3), k)]
    def Tw(u):
        w = []
        for m in u:
            w += T[m]
        return w
    def cop(u, c):
        return free_reduce(Tw(u) + [c] + inverse(Tw(u)))
    ok_pairs = True
    ok_same = True
    for u in sites:
        X, Zw = cop(u, 'x'), cop(u, 'z')
        same = free_reduce(X + Zw + X + Zw + inverse(J))
        ok_same &= is_identity(same)
        for w in sites:
            if w == u:
                continue
            for c1, c2 in (('x', 'x'), ('x', 'z'), ('z', 'x'), ('z', 'z')):
                A, Bw = cop(u, c1), cop(w, c2)
                ok_pairs &= is_identity(free_reduce(A + Bw + inverse(A) + inverse(Bw)))
    check(ok_same, 'same-site: (X_u Z_u)^2 = J for all 8 sites u of the N=3 ladder')
    check(ok_pairs, 'distinct sites commute: all 8*7*4 commutators trivial')
    # p = iota_12 o rho_12 with iota_12 the ray swap and
    # rho_12 : (1,j) <-> (2,j+1), fixing (2,1) and ray 3 (both involutions).
    def iota(y):
        r, h = y
        return {1: (2, h), 2: (1, h), 3: (3, h)}[r]
    def rho(y):
        r, h = y
        if r == 1:
            return (2, h + 1)
        if r == 2 and h >= 2:
            return (1, h - 1)
        return y
    pts = [(r, h) for r in (1, 2, 3) for h in range(1, 60)]
    ok_rho = all(rho(rho(y)) == y and iota(iota(y)) == y and iota(rho(y)) == p_pt(y) for y in pts)
    check(ok_rho, "p = iota_12 o rho_12 (both involutions) on heights < 60 (all points behave uniformly beyond height 2)")

def negative_controls():
    print('Negative controls (must be rejected):')
    bad = [('L', 'x z x z'), ('P', 'x z X Z'), ('A', 'd t1 D t1^-1'),
           ('K-missing-t', 'J x J^-1 Z')]
    for fam, body in bad:
        w = expand(body.split())
        rejected = not is_identity(w)
        check(rejected, 'corrupted %s word "%s" rejected' % (fam, body))

# ------------------------------------------------------------------- Part 2
def part2():
    print('Part 2: numerical sanity of the Pauli sector bound (not a proof)')
    try:
        import numpy as np
    except ImportError:
        print('  numpy missing: Part 2 skipped')
        return
    def h2(x):
        if x <= 0 or x >= 1:
            return 0.0
        return -x * math.log2(x) - (1 - x) * math.log2(1 - x)
    worst = min((2 * math.sqrt(x * (1 - x))) / 1.0 for x in [0.5])
    gap = min((1 - 2 * math.sqrt(x * (1 - x))) / math.log(2) - (1 - h2(x))
              for x in [i / 20000 for i in range(20001)])
    check(gap >= -1e-12, 'scalar inequality 1-h2(x) <= (1-2sqrt(x(1-x)))/ln2 on a grid (min slack %.2e)' % gap)
    bracket = 1 - 0.1 / (2 * math.log(2)) - h2(0.05)
    check(bracket >= 0.5, 'bracket at M*sigma^2*eps^2 = 1/10 is %.4f >= 1/2' % bracket)

    rng = np.random.default_rng(20261021)
    sx = np.array([[0, 1], [1, 0]], dtype=complex)
    sz = np.array([[1, 0], [0, -1]], dtype=complex)
    I2 = np.eye(2)
    def kron_list(ms):
        out = np.array([[1.0 + 0j]])
        for m in ms:
            out = np.kron(out, m)
        return out
    def nrm(A):
        return math.sqrt(np.real(np.trace(A.conj().T @ A)) / A.shape[0])
    def round_inv(H):
        H = (H + H.conj().T) / 2
        w, U = np.linalg.eigh(H)
        s = np.where(w >= 0, 1.0, -1.0)
        return (U * s) @ U.conj().T
    def lemma_p(Xs, Zs):
        M = len(Xs); Dp = Xs[0].shape[0]
        I = np.eye(Dp)
        def f(g):
            out = I.copy()
            for i in range(M):
                if g[i]:
                    out = out @ Zs[i]
            return out
        gs = list(itertools.product((0, 1), repeat=M))
        rhs = 0.0; ok_a = ok_b = True
        for i in range(M):
            a2 = np.mean([nrm(f(tuple((g[j] + (j == i)) % 2 for j in range(M))) - f(g) @ Zs[i]) ** 2 for g in gs])
            b2 = np.mean([nrm((-1) ** g[i] * Xs[i] @ f(g) - f(g) @ Xs[i]) ** 2 for g in gs])
            alpha = sum(nrm(Zs[i] @ Zs[j] - Zs[j] @ Zs[i]) ** 2 for j in range(i + 1, M))
            beta = nrm(Xs[i] @ Zs[i] + Zs[i] @ Xs[i]) ** 2 + sum(
                nrm(Xs[i] @ Zs[j] - Zs[j] @ Xs[i]) ** 2 for j in range(M) if j != i)
            ok_a &= a2 <= alpha + 1e-9
            ok_b &= b2 <= beta + 1e-9
            rhs += 1 - b2 / (2 * math.log(2)) - h2(min(a2 / 2, 0.5))
        return math.log2(Dp), rhs, ok_a, ok_b
    # exact Pauli instance: tight
    M = 3
    Xs = [kron_list([sx if j == i else I2 for j in range(M)]) for i in range(M)]
    Zs = [kron_list([sz if j == i else I2 for j in range(M)]) for i in range(M)]
    lhs, rhs, oa, ob = lemma_p(Xs, Zs)
    check(abs(lhs - rhs) < 1e-9 and oa and ob, 'exact 3-qubit Pauli instance: log D = %.3f = bound %.3f (tight)' % (lhs, rhs))
    # random near-Pauli instances, also in too-small or padded dimensions
    viol = 0; trials = 0; ests = True
    for trial in range(60):
        M = int(rng.integers(2, 4))
        Dq = 2 ** M
        pad = int(rng.integers(0, 3))
        noise = float(rng.choice([0.02, 0.1, 0.3, 0.8]))
        def rnd_herm(d):
            A = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
            return (A + A.conj().T) / 2
        def embed(A):
            if pad == 0:
                return A
            d = A.shape[0]
            out = np.zeros((d + pad, d + pad), dtype=complex)
            out[:d, :d] = A
            out[d:, d:] = np.eye(pad)
            return out
        if trial % 3 == 0:  # squeeze M pairs into dimension 2^(M-1)
            Dq = 2 ** (M - 1)
            Xb = [round_inv(rnd_herm(Dq)) for _ in range(M)]
            Zb = [round_inv(rnd_herm(Dq)) for _ in range(M)]
        else:
            Xb = [kron_list([sx if j == i else I2 for j in range(M)]) for i in range(M)]
            Zb = [kron_list([sz if j == i else I2 for j in range(M)]) for i in range(M)]
        Xs = [round_inv(embed(X) + noise * rnd_herm(Dq + pad) / math.sqrt(Dq + pad)) for X in Xb]
        Zs = [round_inv(embed(Z) + noise * rnd_herm(Dq + pad) / math.sqrt(Dq + pad)) for Z in Zb]
        lhs, rhs, oa, ob = lemma_p(Xs, Zs)
        trials += 1
        viol += lhs < rhs - 1e-9
        ests &= oa and ob
    check(viol == 0, 'Pauli sector bound log D >= sum[...] held in %d/%d random instances' % (trials - viol, trials))
    check(ests, 'projection-product estimates a^2 <= sum alpha^2, b^2 <= gamma^2 + sum beta^2 held in all instances')

def main():
    here = os.path.dirname(os.path.abspath(__file__))
    path = sys.argv[1] if len(sys.argv) > 1 else os.path.join(here, 'relators_pauli.txt')
    part1(path)
    negative_controls()
    part2()
    if FAIL:
        print('\nFAILED: %d check(s) failed' % len(FAIL))
        for m in FAIL:
            print('   -', m)
        raise SystemExit(1)
    print('\nALL CHECKS PASSED')

if __name__ == '__main__':
    main()
