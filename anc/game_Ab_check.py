"""Independent check of game_Ab.json, the linear system (A, b) of the game of Theorem A.

Imports none of the other scripts. Reads egamma0_P.json and game_Ab.json as data and checks:

  1. format: n = 1993 variables, m = 1687 equations, at most s = 3 distinct variables per equation, b in {0, 1},
     the digest of egamma0_P.json;
  2. structure: the multiset of equations, each read as a set of variable roles with its right-hand side, equals the one
     obtained by re-deriving Steps 1-4 of Lemma B.1 [lem:gadget] from egamma0_P.json (an own derivation on nested role tuples);
  3. a model: an own exact model of G_P^+ (Definition 6.5 [def:GP] and the ray swap of Lemma 6.9 [lem:GPp]), in which the
     relations of P are re-checked, and the representations gamma, gamma_1, gamma_2 of the proof of Lemma B.1, built from the defining
     words of P with the central involution J in place of -1, send every variable to an 8 x 8 block-monomial matrix
     over G_P^+. Every relator of the solution group Gamma(A, b) is evaluated exactly: x^2, the commutators of the
     variables of each equation, the product relator J^{b_i} x_{j_1} ... x_{j_r}, and [x, J]. All must give I. This is
     a homomorphism Gamma(A, b) -> G_P^+ wr Sym(8) with J -> J I_8 != I, so J != 1 in Gamma(A, b);
  4. over F_2 the system A x = b has no solution, as it must: J is a commutator in Gamma(A, b), so no deterministic
     strategy wins with certainty;
  5. negative controls: corrupted systems are rejected.

Usage (inside anc/):   python3 -I game_Ab_check.py .      exit status 0 iff every check passes
"""
import hashlib
import json
import os
import sys

DIR = sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(os.path.abspath(__file__))
FAILS = []


def ok(cond, msg):
    print(('PASS  ' if cond else 'FAIL  ') + msg, flush=True)
    if not cond:
        FAILS.append(msg)


rawP = open(os.path.join(DIR, 'egamma0_P.json'), 'rb').read()
P = json.loads(rawP)
G = json.load(open(os.path.join(DIR, 'game_Ab.json'), encoding='utf-8'))

# ===================================================================== 1. format
PRINTED = 'ad0fd91d9378bc956a78e65c813b94fbb93a0e7090b3068b4d76ac6cbc1590f0'   # the digest printed in Section C.4 [cert:rerun]
ok(hashlib.sha256(rawP).hexdigest() == PRINTED, 'egamma0_P.json has the SHA-256 digest printed in Section C.4 [cert:rerun]')
ok(G['source_sha256'] == PRINTED, 'game_Ab.json was generated from that file')
VARS, EQS = G['variables'], G['equations']
n, m = len(VARS), len(EQS)
ok(n == G['n'] == 1993, 'n = %d variables besides J' % n)
ok(m == G['m'] == 1687, 'm = %d equations' % m)
good = all(1 <= len(e['vars']) <= 3 and len(set(e['vars'])) == len(e['vars']) and
           all(isinstance(j, int) and 0 <= j < n for j in e['vars']) and e['b'] in (0, 1) for e in EQS)
smax = max(len(e['vars']) for e in EQS)
ok(good and smax == G['s'] == 3, 'every equation has 1 to 3 distinct variables (s = %d) and b in {0,1}' % smax)
ok(len({v['name'] for v in VARS}) == n, 'variable names are distinct')
used = set(j for e in EQS for j in e['vars'])
ok(len(used) == n, 'every variable occurs in some equation')
deg = {}
for e in EQS:
    deg[len(e['vars'])] = deg.get(len(e['vars']), 0) + 1
print('      equations by number of variables: %s; equations with b = 1: %d' %
      (deg, sum(e['b'] for e in EQS)))

# ===================================================================== 2. structure (own derivation, nested roles)
name_to_role = {v['name']: v['role'] for v in VARS}


def nest(role):
    """Resolve the names inside a role record into nested role tuples."""
    head = role[0]
    if head == 'gen':
        return ('gen', role[1])
    if head in ('f', 'v', 't*', 'u', 'g*'):
        return (head,)
    if head == 'Z':
        return ('Z', ('gen', role[1]), ('gen', role[2]))
    if head in ('prime', 'dprime', 'bar'):
        return (head, nest(name_to_role[role[1]]))
    if head in ('s', "s'"):
        return (head,) + tuple(nest(name_to_role[x]) for x in role[1:4])
    if head == 'y':
        return ('y', role[1]) + tuple(nest(name_to_role[x]) for x in role[2:5])
    raise ValueError(role)


ROLES = [nest(v['role']) for v in VARS]
ok(len(set(ROLES)) == n, 'variable roles are distinct')


def derive(Pd):
    """Steps 1-4 of Lemma B.1 [lem:gadget] on nested roles: returns the list of (frozenset of roles, b)."""
    gen = lambda a: ('gen', a)
    wr = gen(Pd['w'])
    # Step 1 (p = f v) and Step 2 (J = [t*, w]): the generators and conjugacy triples of the presentation of Step 2
    gens = [gen(a) for a in Pd['S0']] + [('f',), ('v',)]
    triples = [(gen(a), gen(b), gen(c)) for a, b, c in Pd['C0']]
    for b, c in Pd['C1']:
        zr = ('Z', gen(b), gen(c))
        gens.append(zr)
        triples += [(('v',), gen(b), zr), (('f',), zr, gen(c))]
    gens += [('t*',), ('u',)]
    triples.append((('t*',), wr, ('u',)))
    eqs = [(frozenset(gen(a) for a in V), 0) for V in Pd['LIN']]
    eqs.append((frozenset([wr, ('u',)]), 1))
    # Step 3
    nice = []
    for a in gens:
        eqs.append((frozenset([a, ('prime', a), ('dprime', a)]), 0))
        eqs.append((frozenset([a, ('g*',), ('bar', a)]), 0))
        nice.append((('g*',), ('prime', a), ('dprime', a)))
    for a, b, c in triples:
        nice.append((('bar', a), ('prime', b), ('dprime', c)))
        nice.append((('bar', a), ('dprime', b), ('prime', c)))
        eqs.append((frozenset([('prime', b), ('dprime', c), ('s', a, b, c)]), 0))
        eqs.append((frozenset([('prime', c), ('dprime', b), ("s'", a, b, c)]), 0))
    # Step 4
    for a, b, c in nice:
        y = [('y', k, a, b, c) for k in range(1, 8)]
        for trip in ((a, y[0], y[1]), (b, y[1], y[2]), (y[2], y[3], y[4]), (a, y[4], y[5]), (c, y[5], y[6]),
                     (y[0], y[3], y[6])):
            eqs.append((frozenset(trip), 0))
    return eqs, len(gens), len(triples), len(nice)


exp_eqs, n_gens, n_trip, n_nice = derive(P)
print('      own derivation: %d generators after Step 2, %d conjugacy triples, %d nice relations, %d equations'
      % (n_gens, n_trip, n_nice, len(exp_eqs)))


def multiset(items):
    d = {}
    for it in items:
        d[it] = d.get(it, 0) + 1
    return d


file_eqs = [(frozenset(ROLES[j] for j in e['vars']), e['b']) for e in EQS]
ok(multiset(file_eqs) == multiset(exp_eqs), 'the equations are exactly those of Steps 1-4 of Lemma B.1 [lem:gadget] applied to P')
exp_vars = set(r for eq, _ in exp_eqs for r in eq)
ok(exp_vars == set(ROLES), 'the variables are exactly those of Steps 1-4 of Lemma B.1 [lem:gadget]')

# ===================================================================== 3. an exact model of G_P^+
# Points (r, h) of the three rays, h >= 1; a configuration is a frozenset of points; V = F_2^(Y).
# A linear map L of V that is eventually a ray permutation with translations is stored as
#   (rho, mm, N, imgs): L(e_(r,h)) = imgs[(r,h)] for h <= N and e_(rho[r], h + mm[r]) for h > N,
# normalized so that N is minimal; this is a canonical form.
E0 = frozenset()


class Lin:
    __slots__ = ('rho', 'mm', 'N', 'imgs', 'key')

    def __init__(self, rho, mm, N, imgs):
        self.rho, self.mm, self.N, self.imgs = rho, mm, N, dict(imgs)
        while self.N >= 1:
            h = self.N
            if all(h + self.mm[r] >= 1 and self.imgs[(r, h)] == frozenset([(self.rho[r], h + self.mm[r])])
                   for r in (1, 2, 3)):
                for r in (1, 2, 3):
                    del self.imgs[(r, h)]
                self.N -= 1
            else:
                break
        assert all(self.N + self.mm[r] >= 0 for r in (1, 2, 3))
        self.key = (tuple(self.rho[r] for r in (1, 2, 3)), tuple(self.mm[r] for r in (1, 2, 3)), self.N,
                    tuple(sorted((k, tuple(sorted(v))) for k, v in self.imgs.items())))

    def basis(self, y):
        r, h = y
        if h <= self.N:
            return self.imgs[y]
        return frozenset([(self.rho[r], h + self.mm[r])])

    def vec(self, v):
        out = set()
        for y in v:
            out ^= self.basis(y)
        return frozenset(out)

    def compose(self, other):
        """self o other."""
        rho = {r: self.rho[other.rho[r]] for r in (1, 2, 3)}
        mm = {r: other.mm[r] + self.mm[other.rho[r]] for r in (1, 2, 3)}
        N = max([other.N, 0] + [self.N - other.mm[r] for r in (1, 2, 3)])
        imgs = {(r, h): self.vec(other.basis((r, h))) for r in (1, 2, 3) for h in range(1, N + 1)}
        return Lin(rho, mm, N, imgs)


ID_RAYS = {1: 1, 2: 2, 3: 3}
ZERO_M = {1: 0, 2: 0, 3: 0}
LIN_ID = Lin(ID_RAYS, ZERO_M, 0, {})

INTERN = {}
PRODUCTS = {}


class Elt:
    """(s, a, b, L, u): the element J^s X^a Z^b of E_V followed by the affine map v -> L v + u."""
    __slots__ = ('s', 'a', 'b', 'L', 'u', 'key')

    def __init__(self, s, a, b, L, u):
        self.s, self.a, self.b, self.L, self.u = s, a, b, L, u
        self.key = (s, tuple(sorted(tuple(sorted(c)) for c in a)), tuple(sorted(tuple(sorted(c)) for c in b)),
                    L.key, tuple(sorted(u)))

    def site(self, v):
        return frozenset(self.L.vec(v) ^ self.u)

    def __mul__(self, other):
        k = (id(self), id(other))
        if k in PRODUCTS:
            return PRODUCTS[k]
        a2 = frozenset(self.site(v) for v in other.a)
        b2 = frozenset(self.site(v) for v in other.b)
        s = (self.s + other.s + len(self.b & a2)) % 2
        L = self.L.compose(other.L)
        u = frozenset(self.L.vec(other.u) ^ self.u)
        res = intern(Elt(s, self.a ^ a2, self.b ^ b2, L, u))
        PRODUCTS[k] = res
        return res


def intern(e):
    return INTERN.setdefault(e.key, e)


ONE = intern(Elt(0, frozenset(), frozenset(), LIN_ID, E0))
JJ = intern(Elt(1, frozenset(), frozenset(), LIN_ID, E0))
LET = {
    'p': intern(Elt(0, frozenset(), frozenset(),
                    Lin(ID_RAYS, {1: 1, 2: -1, 3: 0}, 1, {(1, 1): frozenset([(1, 2)]), (2, 1): frozenset([(1, 1)]),
                                                          (3, 1): frozenset([(3, 1)])}), E0)),
    'P': intern(Elt(0, frozenset(), frozenset(),
                    Lin(ID_RAYS, {1: -1, 2: 1, 3: 0}, 1, {(1, 1): frozenset([(2, 1)]), (2, 1): frozenset([(2, 2)]),
                                                          (3, 1): frozenset([(3, 1)])}), E0)),
    'i': intern(Elt(0, frozenset(), frozenset(), Lin({1: 1, 2: 3, 3: 2}, ZERO_M, 0, {}), E0)),
    't': intern(Elt(0, frozenset(), frozenset(), LIN_ID, frozenset([(1, 1)]))),
    'd': intern(Elt(0, frozenset(), frozenset(),
                    Lin(ID_RAYS, ZERO_M, 1, {(1, 1): frozenset([(1, 1), (1, 2)]), (2, 1): frozenset([(2, 1)]),
                                             (3, 1): frozenset([(3, 1)])}), E0)),
    'x': intern(Elt(0, frozenset([E0]), frozenset(), LIN_ID, E0)),
    'z': intern(Elt(0, frozenset(), frozenset([E0]), LIN_ID, E0)),
}
for c in 'ITDXZ':                           # iota, t, d, x, z are involutions
    LET[c] = LET[c.lower()]


def word(w):
    e = ONE
    for c in w:
        e = e * LET[c]
    return e


# sanity checks of the model against the definitions
q = word('ipi')
ok(word('pP') is ONE and word('Pp') is ONE, 'model: p P = P p = 1')
ok(all(word(c + c) is ONE for c in 'itdxz'), 'model: iota, t, d, x, z are involutions')
sig = LET['p'] * q * LET['P'] * word('iPi')
tr = intern(Elt(0, frozenset(), frozenset(),
                Lin(ID_RAYS, ZERO_M, 2, {(1, 1): frozenset([(1, 2)]), (1, 2): frozenset([(1, 1)]), (2, 1): frozenset([(2, 1)]),
                                         (2, 2): frozenset([(2, 2)]), (3, 1): frozenset([(3, 1)]), (3, 2): frozenset([(3, 2)])}),
                E0))
ok(sig is tr, 'model: [p, iota p iota] is the transposition of (1,1) and (1,2)')
ok(word('xzxz') is JJ and JJ is not ONE, 'model: (xz)^2 = J != 1')
ok(all(JJ * LET[c] is LET[c] * JJ for c in 'pitdxz'), 'model: J commutes with p, iota, t, d, x, z')
ok(word('tptPtpTP') is ONE, 'model: the translations t and p t p^-1 commute')
ok(word('xtxtxtxt') is ONE and word('xtztxtzt') is ONE, 'model: the lamps at 0 and e_1 commute')
ok(word('dtdptPt') is ONE, 'model: d t d^-1 = t (p t p^-1)')
ok(word('xpXP') is ONE and word('xdxd') is ONE and word('xixi') is ONE, 'model: p, d, iota fix the lamp at 0')
ok(word('xtxt') is not ONE and word('xz') is not ONE and word('dt') is not word('td') and word('xtx') is not word('txt'),
   'model: negative tests (xtxt, xz, [d,t] and xtx (txt)^-1 are nontrivial)')

PHI = {a: word(wd) for a, wd in P['S0'].items()}
ok(all(PHI[a] * PHI[a] is ONE for a in PHI), 'model: all 26 defining words are involutions in G_P^+')
ok(PHI[P['w']] is JJ, 'model: w -> J')
ok(all(PHI[a] * PHI[b] * PHI[a] is PHI[c] for a, b, c in P['C0']), 'model: the 76 relations of C0 hold')
ok(all(LET['p'] * PHI[b] * LET['P'] is PHI[c] for b, c in P['C1']), 'model: the 10 relations of C1 hold')


def prod(xs):
    e = ONE
    for x in xs:
        e = e * x
    return e


ok(all(prod(PHI[a] for a in V) is ONE for V in P['LIN']), 'model: the 8 linear relations hold')


# block-monomial matrices over G_P^+: column k has one nonzero block, in row perm[k], with entry ents[k]
class BM:
    __slots__ = ('perm', 'ents')

    def __init__(self, perm, ents):
        self.perm, self.ents = tuple(perm), tuple(ents)

    def __mul__(self, o):
        return BM([self.perm[o.perm[k]] for k in range(len(o.perm))],
                  [self.ents[o.perm[k]] * o.ents[k] for k in range(len(o.perm))])

    def same(self, o):
        return self.perm == o.perm and all(a is b for a, b in zip(self.ents, o.ents))


def scal(e):
    return BM([0], [e])


def dsum(U, V):
    D = len(U.perm)
    return BM(list(U.perm) + [D + k for k in V.perm], list(U.ents) + list(V.ents))


def adiag(U, V):
    """The block matrix [[0, U], [V, 0]]."""
    D = len(U.perm)
    return BM([D + k for k in V.perm] + list(U.perm), list(V.ents) + list(U.ents))


def ident(D):
    return BM(range(D), [ONE] * D)


def scalar_mat(e, D):
    return BM(range(D), [e] * D)


I1, I2, I4, I8 = ident(1), ident(2), ident(4), ident(8)
J8 = scalar_mat(JJ, 8)
# Step 1 and Step 2: gamma on C^d + C^d, with J in place of -1
GAMMA = {}


def gamma(r):
    if r in GAMMA:
        return GAMMA[r]
    h = r[0]
    if h == 'gen':
        M = dsum(scal(PHI[r[1]]), I1)
    elif h == 'f':
        M = adiag(I1, I1)
    elif h == 'v':
        M = adiag(scal(LET['P']), scal(LET['p']))
    elif h == 'Z':
        M = dsum(I1, scal(LET['p'] * PHI[r[1][1]] * LET['P']))
    elif h == 't*':
        M = adiag(I1, I1)
    elif h == 'u':
        M = dsum(I1, scal(JJ))
    else:
        raise ValueError(r)
    GAMMA[r] = M
    return M


GAMMA1 = {}


def gamma1(r):
    if r in GAMMA1:
        return GAMMA1[r]
    h = r[0]
    if h == 'g*':
        M = adiag(I2, I2)
    elif h == 'bar':
        M = adiag(gamma(r[1]), gamma(r[1]))
    elif h == 'prime':
        M = dsum(gamma(r[1]), I2)
    elif h == 'dprime':
        M = dsum(I2, gamma(r[1]))
    elif h == 's':
        M = dsum(gamma(r[2]), gamma(r[3]))
    elif h == "s'":
        M = dsum(gamma(r[3]), gamma(r[2]))
    else:
        M = dsum(gamma(r), gamma(r))
    GAMMA1[r] = M
    return M


def gamma2(r):
    if r[0] != 'y':
        return dsum(gamma1(r), gamma1(r))
    k, A, B, C = r[1], gamma1(r[2]), gamma1(r[3]), gamma1(r[4])
    return {1: lambda: adiag(A, A), 2: lambda: adiag(I4, I4), 3: lambda: adiag(B, B), 4: lambda: adiag(B * A, A * B),
            5: lambda: dsum(B * A * B, A), 6: lambda: dsum(B * C, I4), 7: lambda: dsum(B, C)}[k]()


IMG = [gamma2(r) for r in ROLES]


def check_relators(eqs, imgs):
    """Return the number of relators of Gamma(A, b) that fail in the model."""
    bad = 0
    for X in imgs:
        if not (X * X).same(I8) or not (X * J8).same(J8 * X):
            bad += 1
    for e in eqs:
        Xs = [imgs[j] for j in e['vars']]
        for i1 in range(len(Xs)):
            for i2 in range(i1 + 1, len(Xs)):
                if not (Xs[i1] * Xs[i2]).same(Xs[i2] * Xs[i1]):
                    bad += 1
        Y = J8 if e['b'] else I8
        for X in Xs:
            Y = Y * X
        if not Y.same(I8):
            bad += 1
    return bad


n_comm = sum(len(e['vars']) * (len(e['vars']) - 1) // 2 for e in EQS)
bad = check_relators(EQS, IMG)
ok(bad == 0, 'model: the %d squares x^2, the %d commutators [x,J], the %d commutators within equations and the %d product '
             'relators of Gamma(A,b) hold for the 8x8 block-monomial images, with J -> J I_8 != I' % (n, n, n_comm, m))
print('      model: %d distinct elements of G_P^+ were formed' % len(INTERN))


# ===================================================================== 4. A x = b has no solution over F_2
def solvable(eqs, nvars):
    """Gaussian elimination over F_2; returns (A x = b is solvable, rank of A)."""
    mask = (1 << nvars) - 1
    pivots = {}
    consistent = True
    for e in eqs:
        r = 0
        for j in e['vars']:
            r ^= 1 << j
        r |= e['b'] << nvars
        while r & mask:
            top = (r & mask).bit_length() - 1
            if top in pivots:
                r ^= pivots[top]
            else:
                pivots[top] = r
                break
        else:
            if r:
                consistent = False
    return consistent, len(pivots)


sol, rk = solvable(EQS, n)
ok(not sol, 'over F_2 the system A x = b is inconsistent (A has rank %d), so no deterministic strategy wins with '
            'certainty' % rk)

# ===================================================================== 5. negative controls
import copy


def corrupt(f):
    eqs = copy.deepcopy(EQS)
    f(eqs)
    return eqs


wu = next(i for i, e in enumerate(EQS) if e['b'] == 1)
gadget = next(i for i, e in enumerate(EQS) if e['source'].startswith('Step 4'))
other = next(j for j in range(n) if j not in EQS[gadget]['vars'])


def c1(eqs):
    eqs[gadget]['b'] = 1


def c2(eqs):
    eqs[gadget]['vars'][0] = other


def c3(eqs):
    del eqs[gadget]


def c4(eqs):
    eqs[wu]['b'] = 0


ok(check_relators(corrupt(c1), IMG) > 0, 'negative control: a gadget equation with b = 1 fails in the model')
ok(check_relators(corrupt(c2), IMG) > 0, 'negative control: a gadget equation with a wrong variable fails in the model')
e3 = corrupt(c3)
ok(multiset([(frozenset(ROLES[j] for j in e['vars']), e['b']) for e in e3]) != multiset(exp_eqs),
   'negative control: a deleted equation is detected by the structure check')
ok(solvable(corrupt(c4), n)[0], 'negative control: with b = 0 in the equation x_w + x_u = 1 the system becomes solvable')

print()
if FAILS:
    print('%d CHECK(S) FAILED' % len(FAILS))
    sys.exit(1)
print('ALL CHECKS PASSED')
