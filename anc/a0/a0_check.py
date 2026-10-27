"""Explicit area certificates for the constant A_0 of the gadget lemma (Lemma B.1 [lem:gadget], (G1) and (G2)).

Reads egamma0_P.json (the presentation P) and game_Ab.json (the linear system (A, b), with the role of every variable)
from the directory given as the first argument. Imports nothing from the other programs of anc/.

For every relator r of P, and for the word [x_w, x_{t*}] J of (G2), the program builds a van Kampen certificate:
a list of factors (u, r_Gamma, e) with u a word, r_Gamma a relator of the solution group Gamma(A, b) in the
presentation of Definition 2.7 [def:lcs], and e = +1 or -1, such that the product of the conjugates u r_Gamma^e u^-1
is freely equal to Psi(r). The number of factors bounds the area of Psi(r). The relators of Gamma(A, b) are built from
game_Ab.json alone:

    x_j^2,  J^2,  [x_j, J],  [x_j, x_k] for j != k in a common equation,  J^{b_i} x_{j_1} ... x_{j_r} (j_1 < ... < j_r).

The relators r of P are those of Definition 10.1 [def:EG0]: g^2 for g in S_0, the product of each linear set in its
listed order, x y x z^-1 for (x, y, z) in C_0 (the commutations of the linear sets among them), and p b p^-1 c^-1 for
(b, c) in C_1; there are no relations (E5), since S_1 = {p}.

The certificates come from a few templates, one per type of word, written in role letters (A, B, C, y1, ..., y7 for a
gadget, a, b, c, bar(a), g*, b', b'', c', c'' for a conjugacy relation, and so on). Each template is a sequence of
cells: a cell replaces a subword P of the current cyclic word by Q, where P Q^-1 is a cyclic permutation of a relator,
of its inverse, or of an already certified word (a lemma). A small engine replays the cells on the actual variables,
which it finds through the roles recorded in game_Ab.json, and records one conjugate per relator used. Nothing depends
on the numbering of the variables: the relator of an equation is formed in increasing index order, as in def:lcs, and
if a template's cell meets an equation whose product order differs from the order the template expects, the engine
inserts the commutator cells that reorder it (and the extra cells are counted).

The final verification is independent of the engine: for each word it recomputes every factor from its key, checks
that the key names a genuine relator of Gamma(A, b) (an equation of the file, a commutator of two variables of one
equation, a square, ...), multiplies the conjugates, reduces freely, and compares with Psi(r) computed directly from
egamma0_P.json (Psi(g) = x_g for g in S_0 and Psi(p) = x_f x_v).

The program then requires every certificate to have at most A_0 = 42 factors, and reports the replay and this cap
separately.

Usage:   python3 -I a0_check.py <dir>                exit status 0 iff every certificate verifies and has at most 42 factors
         python3 -I a0_check.py <dir> --negctl       negative controls; exit status 0 iff every corruption is rejected
         python3 -I a0_check.py <dir> --dump <file>  as the first form, and also writes all certificates as JSON
"""
import hashlib
import json
import os
import sys

CAP = 42          # the constant A_0 of Remark B.2 [rem:A0]: no certificate may have more factors


# ===================================================================== free group words
# A word is a tuple of nonzero ints: variable j (0-based) is the letter j+1, its inverse -(j+1); J is the letter n+1.

def inv(w):
    return tuple(-x for x in reversed(w))


def red(w):
    out = []
    for x in w:
        if out and out[-1] == -x:
            out.pop()
        else:
            out.append(x)
    return tuple(out)


def cyc(w):
    """w (reduced) = h c h^-1 with c cyclically reduced; returns (h, c)."""
    i, j = 0, len(w) - 1
    while i < j and w[i] == -w[j]:
        i += 1
        j -= 1
    return tuple(w[:i]), tuple(w[i:j + 1])


class CertError(Exception):
    pass


# ===================================================================== the solution group Gamma(A, b)
class Gamma:
    def __init__(self, G):
        self.vars = G['variables']
        self.eqs = [(list(e['vars']), e['b']) for e in G['equations']]
        self.src = [e.get('source', '?') for e in G['equations']]
        self.n = len(self.vars)
        self.J = self.n + 1
        self.name = [v['name'] for v in self.vars]
        self.role = {}
        for j, v in enumerate(self.vars):
            key = tuple(v['role'])
            if key in self.role:
                raise CertError('two variables with role %r' % (key,))
            self.role[key] = j
        self.pairs = set()
        self.by_set = {}
        for i, (vs, b) in enumerate(self.eqs):
            if len(set(vs)) != len(vs) or not all(0 <= j < self.n for j in vs) or b not in (0, 1):
                raise CertError('malformed equation %d' % i)
            self.by_set.setdefault(frozenset(vs), []).append(i)
            for j in vs:
                for k in vs:
                    if j != k:
                        self.pairs.add(frozenset((j, k)))

    def relator(self, key):
        """The word of a relator of Gamma(A, b), or CertError if key names none."""
        kind = key[0]
        if kind == 'sq':
            j = key[1]
            if not 0 <= j < self.n:
                raise CertError('bad square %r' % (key,))
            return (j + 1, j + 1)
        if kind == 'J2':
            return (self.J, self.J)
        if kind == 'Jc':
            j = key[1]
            if not 0 <= j < self.n:
                raise CertError('bad [x,J] %r' % (key,))
            return (j + 1, self.J, -(j + 1), -self.J)
        if kind == 'com':
            j, k = key[1], key[2]
            if j == k or frozenset((j, k)) not in self.pairs:
                raise CertError('[x_%d, x_%d] is not a relator: no common equation' % (j, k))
            return (j + 1, k + 1, -(j + 1), -(k + 1))
        if kind == 'eq':
            i = key[1]
            if not 0 <= i < len(self.eqs):
                raise CertError('bad equation %r' % (key,))
            vs, b = self.eqs[i]
            return (self.J,) * b + tuple(j + 1 for j in sorted(vs))
        raise CertError('unknown relator kind %r' % (key,))

    def lookup(self, role):
        if role not in self.role:
            raise CertError('no variable with role %r' % (role,))
        return self.role[role]

    def equations(self, idxs):
        s = frozenset(idxs)
        if len(s) != len(idxs) or s not in self.by_set:
            raise CertError('no equation with variables %s' % sorted(self.name[j] for j in idxs))
        return self.by_set[s]


def verify(gam, target, factors):
    """Independent check: every factor is a conjugate of a relator of Gamma and the product is freely Psi(r)."""
    prod = []
    for (u, key, e) in factors:
        r = gam.relator(key)
        if e not in (1, -1):
            raise CertError('bad sign')
        if any(not (1 <= abs(x) <= gam.n + 1) for x in u):
            raise CertError('bad conjugator')
        prod.extend(u)
        prod.extend(r if e == 1 else inv(r))
        prod.extend(inv(u))
        prod = list(red(prod))
    return tuple(prod) == red(target)


# ===================================================================== templates
# Letters: names; a trailing '-' marks an inverse. Cell references:
#   ('sq', a) square; ('com', a, b) commutator of two variables of one equation; ('eq', a1, ..., ak) the equation with
#   these variables, whose product the template expects in this order (with J^b in front); a lemma ('N', A, B, C),
#   ('K3', a, b, c) refers to the certified word of that template.
# A cell is (P, Q, reference) or (P, Q, reference, k): replace the k-th occurrence (default 0) of P in the cyclic word.

TEMPLATES = {}

# --- Step 4 gadget of a nice relation A B A = C, equations A y1 y2, B y2 y3, y3 y4 y5, A y5 y6, C y6 y7, y1 y4 y7.
# The six triangles alone form a pair of pants with boundary A C, B, A; the two commutator cells glue the loops B
# and A to the first one. Certified word: A C A^-1 B^-1, a cyclic permutation of (A^-1 B A C^-1)^-1. 8 cells.
TEMPLATES['N'] = dict(
    target='A C A- B-',
    moves=[
        ('A-', 'y6 A- y6-', ('com', 'A', 'y6')),
        ('B-', 'y3 B- y3-', ('com', 'B', 'y3')),
        ('A-', 'y5 y6', ('eq', 'A', 'y5', 'y6')),
        ('B-', 'y2 y3', ('eq', 'B', 'y2', 'y3')),
        ('y5 y3', 'y4-', ('eq', 'y3', 'y4', 'y5')),
        ('y2 A', 'y1-', ('eq', 'A', 'y1', 'y2')),
        ('C y6', 'y7-', ('eq', 'C', 'y6', 'y7')),
        ('y1- y7- y4-', '', ('eq', 'y1', 'y4', 'y7')),
    ])

# --- a conjugacy relation a b a = c of the presentation of Step 2, through Step 3: a = bar(a)^-1 g*^-1 by the linear
# set {a, g*, bar a}; g* commutes with b, because {b, g*, bar b} is an equation; b = b''^-1 b'^-1; the gadgets of the
# nice relations bar(a) b'' bar(a) = c' and bar(a) b' bar(a) = c''; c = c''^-1 c'^-1. Certified word a b a^-1 c^-1.
# 1 + 1 + 1 + 1 + 8 + 8 + 1 + 1 = 22 cells.
TEMPLATES['K3'] = dict(
    target='a b a- c-',
    moves=[
        ('a', 'ab- gs-', ('eq', 'a', 'gs', 'ab')),
        ('a-', 'gs ab', ('eq', 'a', 'gs', 'ab')),
        ('gs- b gs', 'b', ('com', 'b', 'gs')),
        ('b', 'b2- b1-', ('eq', 'b', 'b1', 'b2')),
        ('ab- b2-', 'c1- ab-', ('N', 'ab', 'b2', 'c1')),
        ('ab- b1- ab', 'c2-', ('N', 'ab', 'b1', 'c2')),
        ('c1- c2-', 'c2- c1-', ('com', 'c1', 'c2')),
        ('c2- c1- c-', '', ('eq', 'c', 'c1', 'c2')),
    ])

# --- relators of P -------------------------------------------------------------------------------------------------
TEMPLATES['square'] = dict(target='g g', moves=[('g g', '', ('sq', 'g'))])

TEMPLATES['linear'] = dict(target='v1 v2 v3', moves=[('v1 v2 v3', '', ('eq', 'v1', 'v2', 'v3'))])

# (x, y, y) in C0 with x, y in one linear set of P: x y x y^-1 = [x, y] after one square. 2 cells.
TEMPLATES['C0-linear-commutation'] = dict(
    target='x y x y-',
    moves=[
        ('x', 'x-', ('sq', 'x'), 1),
        ('x y x- y-', '', ('com', 'x', 'y')),
    ])

# (a, b, c) in C0: a b a c^-1; one square turns it into the word of K3. 1 + 22 = 23 cells.
TEMPLATES['C0-conjugacy'] = dict(
    target='a b a c-',
    moves=[
        ('a', 'a-', ('sq', 'a'), 1),
        ('a b a- c-', '', ('K3', 'a', 'b', 'c')),
    ])

# (b, c) in C1: Psi(p b p^-1 c^-1) = x_f x_v x_b x_v^-1 x_f^-1 x_c^-1, through the conjugacy relations v b v = Z and
# f Z f = c of Step 1, Z = Z[b,c]. The g* of v and f are removed first (g* commutes with b and bar v), then four
# gadgets: bar(v) b'' bar(v) = Z', bar(v) b' bar(v) = Z'', bar(f) Z' bar(f) = c'', bar(f) Z'' bar(f) = c'.
# 2 + 1 + 2 + 3 + 1 + 4 x 8 + 1 = 42 cells.
TEMPLATES['C1'] = dict(
    target='f v b v- f- c-',
    moves=[
        ('v', 'vb- gs-', ('eq', 'v', 'gs', 'vb')),
        ('v-', 'gs vb', ('eq', 'v', 'gs', 'vb')),
        ('gs- b gs', 'b', ('com', 'b', 'gs')),
        ('f', 'fb- gs-', ('eq', 'f', 'gs', 'fb')),
        ('f-', 'gs fb', ('eq', 'f', 'gs', 'fb')),
        ('gs- vb-', 'vb- gs-', ('com', 'vb', 'gs')),
        ('gs- b', 'b gs-', ('com', 'b', 'gs')),
        ('gs- vb gs', 'vb', ('com', 'vb', 'gs')),
        ('b', 'b2- b1-', ('eq', 'b', 'b1', 'b2')),
        ('vb- b2-', 'Z1- vb-', ('N', 'vb', 'b2', 'Z1')),
        ('vb- b1- vb', 'Z2-', ('N', 'vb', 'b1', 'Z2')),
        ('fb- Z1-', 'c2- fb-', ('N', 'fb', 'Z1', 'c2')),
        ('fb- Z2- fb', 'c1-', ('N', 'fb', 'Z2', 'c1')),
        ('c2- c1- c-', '', ('eq', 'c', 'c1', 'c2')),
    ])

# (G2): [x_w, x_{t*}] J, through the conjugacy relation t* w t* = u of Step 2 and the equation J w u.
# 2 + 1 + 1 + 8 + 8 + 1 + 1 + 1 + 1 = 24 cells.
TEMPLATES['G2'] = dict(
    target='w ts w- ts- J',
    moves=[
        ('ts', 'tsb- gs-', ('eq', 'ts', 'gs', 'tsb')),
        ('ts-', 'gs tsb', ('eq', 'ts', 'gs', 'tsb')),
        ('gs- w- gs', 'w-', ('com', 'w', 'gs')),
        ('w-', 'w1 w2', ('eq', 'w', 'w1', 'w2')),
        ('tsb- w1', 'u2 tsb-', ('N', 'tsb', 'w1', 'u2')),
        ('tsb- w2 tsb', 'u1', ('N', 'tsb', 'w2', 'u1')),
        ('u2 u1', 'u1 u2', ('com', 'u1', 'u2')),
        ('u1 u2', 'u-', ('eq', 'u', 'u1', 'u2')),
        ('u-', 'u', ('sq', 'u')),
        ('J w u', '', ('eq', 'w', 'u')),
    ])


# ===================================================================== the engine
class Engine:
    def __init__(self, gam):
        self.gam = gam
        self.cache = {}
        self.adapted = 0          # cells added because an equation's product order differed from the template's

    # ---- letters of a template instance, from the roles of game_Ab.json
    def env_N(self, A, B, C):
        g = self.gam
        env = {'A': A, 'B': B, 'C': C}
        for k in range(1, 8):
            env['y%d' % k] = g.lookup(('y', k, g.name[A], g.name[B], g.name[C]))
        return env

    def env_K3(self, a, b, c):
        g = self.gam
        return {'a': a, 'b': b, 'c': c,
                'ab': g.lookup(('bar', g.name[a])), 'gs': g.lookup(('g*',)),
                'b1': g.lookup(('prime', g.name[b])), 'b2': g.lookup(('dprime', g.name[b])),
                'c1': g.lookup(('prime', g.name[c])), 'c2': g.lookup(('dprime', g.name[c]))}

    def lemma(self, name, args):
        key = (name,) + tuple(args)
        if key not in self.cache:
            env = self.env_N(*args) if name == 'N' else self.env_K3(*args)
            self.cache[key] = self.run(name, env)
        return self.cache[key]

    def word(self, s, env):
        w = []
        for tok in s.split():
            neg = tok.endswith('-')
            t = tok[:-1] if neg else tok
            x = self.gam.J if t == 'J' else env[t] + 1
            w.append(-x if neg else x)
        return tuple(w)

    # ---- the certified word and factors behind a cell reference
    def resolve(self, ref, env, M):
        g = self.gam
        kind = ref[0]
        if kind == 'sq':
            k = ('sq', env[ref[1]])
            return g.relator(k), [((), k, 1)]
        if kind == 'com':
            k = ('com', env[ref[1]], env[ref[2]])
            return g.relator(k), [((), k, 1)]
        if kind == 'eq':
            idx = [env[t] for t in ref[1:]]
            cand = g.equations(idx)
            for i in cand:
                R = g.relator(('eq', i))
                if rotation(M, R) is not None:
                    return R, [((), ('eq', i), 1)]
            # the template expects the product in the listed order: reorder by commutator cells
            for i in cand:
                want = (g.J,) * g.eqs[i][1] + tuple(j + 1 for j in idx)
                if rotation(M, want) is not None:
                    F = self.reorder(want, g.relator(('eq', i)), ('eq', i))
                    self.adapted += len(F) - 1
                    return want, F
            raise CertError('cell does not match the equation of %s' % [g.name[j] for j in idx])
        if kind in ('N', 'K3'):
            return self.lemma(kind, [env[t] for t in ref[1:]])
        raise CertError('bad reference %r' % (ref,))

    def reorder(self, want, R, key):
        """Factors for the word `want`, a permutation of the letters of the relator R = relator(key): sort `want` by
        adjacent swaps into the cyclic permutation R_k = X^-1 R X (X = R[:k]) that needs the fewest swaps. A swap is
        X p q Y = (X [p,q] X^-1) X q p Y, one commutator cell ([x, J] if one letter is J); then R_k, one cell."""
        g = self.gam
        best = None
        for k in range(len(R)):
            Rk = R[k:] + R[:k]
            cur = list(want)
            F = []
            order = {x: i for i, x in enumerate(Rk)}
            for _ in range(len(cur)):
                for i in range(len(cur) - 1):
                    p, q = cur[i], cur[i + 1]
                    if order[p] > order[q]:
                        if p == g.J or q == g.J:        # [v, J] = v J v^-1 J^-1 is the relator; [J, v] its inverse
                            v = q if p == g.J else p
                            kk, e = ('Jc', v - 1), (1 if q == g.J else -1)
                        else:
                            kk, e = ('com', p - 1, q - 1), 1
                        F.append((tuple(cur[:i]), kk, e))
                        cur[i], cur[i + 1] = q, p
            if tuple(cur) != Rk:
                raise CertError('reorder failed')
            F.append((inv(R[:k]), key, 1))
            if best is None or len(F) < len(best):
                best = F
        return best

    # ---- replay a template
    def run(self, name, env):
        T = TEMPLATES[name]
        target = red(self.word(T['target'], env))
        h, W = cyc(target)
        gconj = h
        F = []
        for mv in T['moves']:
            P, Q, ref = mv[0], mv[1], mv[2]
            occ = mv[3] if len(mv) > 3 else 0
            P, Q = self.word(P, env), self.word(Q, env)
            L = len(W)
            hits = [i for i in range(L) if (W[i:] + W[:i])[:len(P)] == P] if len(P) <= L else []
            if len(hits) <= occ:
                raise CertError('%s: subword %s not found' % (name, mv[0]))
            i = hits[occ]
            gconj, W = gconj + W[:i], W[i:] + W[:i]
            M = red(P + inv(Q))
            R, RF = self.resolve(ref, env, M)
            rot = rotation(M, R)
            if rot is None:
                raise CertError('%s: cell %s -> %s is not a relator %r' % (name, mv[0], mv[1], ref))
            X, e = rot                                  # M = X^-1 R^e X
            u = red(gconj + inv(X))
            for (c, k, s) in (RF if e == 1 else [(c, k, -s) for (c, k, s) in reversed(RF)]):
                F.append((red(u + c), k, s))
            nw = red(Q + W[len(P):])
            h, W = cyc(nw)
            gconj = red(gconj + h)
        if W:
            raise CertError('%s: word not reduced to e (left %r)' % (name, W))
        return target, F


def rotation(M, R):
    """If M is a cyclic permutation of R^e, return (X, e) with R^e = X Y and M = Y X, else None."""
    for e, S in ((1, tuple(R)), (-1, inv(R))):
        if len(S) != len(M):
            continue
        for k in range(len(S)):
            if S[k:] + S[:k] == M:
                return S[:k], e
    return None


# ===================================================================== the words of (G1) and (G2)
def build(P, gam, eng):
    """Returns a list of (type, label, Psi(r), factors). Psi(r) is computed from P directly."""
    S0 = list(P['S0'])
    if list(P['S1']) != ['p']:
        raise CertError('S1 must be {p}')
    gen = {a: gam.lookup(('gen', a)) for a in S0}
    xf, xv = gam.lookup(('f',)), gam.lookup(('v',))

    def psi(letters):                                  # letters: list of (generator of P, +-1)
        w = []
        for a, e in letters:
            if a == 'p':
                pw = (xf + 1, xv + 1)
                w.extend(pw if e == 1 else inv(pw))
            else:
                w.append((gen[a] + 1) * e)
        return red(w)

    out = []
    for a in S0:
        _, F = eng.run('square', {'g': gen[a]})
        out.append(('square g^2', a, psi([(a, 1), (a, 1)]), F))
    for V in P['LIN']:
        env = {'v%d' % (k + 1): gen[a] for k, a in enumerate(V)}
        if len(V) != 3:
            raise CertError('linear sets of P have three elements')
        _, F = eng.run('linear', env)
        out.append(('linear relation', ' '.join(V), psi([(a, 1) for a in V]), F))
    W = P['w']
    for (x, y, z) in P['C0']:
        word = psi([(x, 1), (y, 1), (x, 1), (z, -1)])
        if y == z and frozenset((gen[x], gen[y])) in gam.pairs:
            _, F = eng.run('C0-linear-commutation', {'x': gen[x], 'y': gen[y]})
            t = 'C0 commutation in a linear set'
        else:
            _, F = eng.run('C0-conjugacy', eng.env_K3(gen[x], gen[y], gen[z]))
            t = ('C0 centrality (g,w,w)' if y == z == W else
                 'C0 other commutation (x,y,y)' if y == z else 'C0 conjugacy (x,y,z), z != y')
        out.append((t, '(%s,%s,%s)' % (x, y, z), word, F))
    for (b, c) in P['C1']:
        word = psi([('p', 1), (b, 1), ('p', -1), (c, -1)])
        Z = gam.lookup(('Z', b, c))
        env = eng.env_K3(xv, gen[b], Z)
        env2 = eng.env_K3(xf, Z, gen[c])
        e = {'f': xf, 'v': xv, 'b': gen[b], 'c': gen[c], 'gs': env['gs'], 'vb': env['ab'], 'fb': env2['ab'],
             'b1': env['b1'], 'b2': env['b2'], 'Z1': env['c1'], 'Z2': env['c2'], 'c1': env2['c1'], 'c2': env2['c2']}
        _, F = eng.run('C1', e)
        t = ('C1 centrality (w,w)' if b == c == W else 'C1 commutation (x,x)' if b == c else 'C1 conjugacy (b,c), c != b')
        out.append((t, '(p,%s,%s)' % (b, c), word, F))
    # (G2)
    xw, xt, xu = gen[W], gam.lookup(('t*',)), gam.lookup(('u',))
    k1 = eng.env_K3(xt, xw, xu)
    e = {'w': xw, 'ts': xt, 'u': xu, 'tsb': k1['ab'], 'gs': k1['gs'], 'w1': k1['b1'], 'w2': k1['b2'],
         'u1': k1['c1'], 'u2': k1['c2']}
    _, F = eng.run('G2', e)
    word = red((xw + 1, xt + 1, -(xw + 1), -(xt + 1), gam.J))
    out.append(('(G2) [x_w, x_t*] J', '[%s,t*]J' % W, word, F))
    return out


TYPE_ORDER = ['square g^2', 'linear relation', 'C0 commutation in a linear set', 'C0 centrality (g,w,w)',
              'C0 other commutation (x,y,y)', 'C0 conjugacy (x,y,z), z != y', 'C1 centrality (w,w)',
              'C1 commutation (x,x)', 'C1 conjugacy (b,c), c != b', '(G2) [x_w, x_t*] J']


def print_templates():
    print('templates, with their nominal cell counts (every equation in the order the template expects; role letters;')
    print('X- is X^-1; each cell replaces P by Q, P Q^-1 a cyclic permutation of the relator')
    print('or lemma named, or of its inverse; free reductions and cyclic permutations cost nothing)')
    for name in ('N', 'K3', 'square', 'linear', 'C0-linear-commutation', 'C0-conjugacy', 'C1', 'G2'):
        T = TEMPLATES[name]
        cost = 0
        lines = []
        for mv in T['moves']:
            ref = mv[2]
            c = 8 if ref[0] == 'N' else 22 if ref[0] == 'K3' else 1
            cost += c
            occ = '  (occurrence %d)' % (mv[3] + 1) if len(mv) > 3 else ''
            lines.append('      %-14s -> %-12s by %-22s %2d%s' % (mv[0], mv[1] or 'e', ' '.join(ref), c, occ))
        print('  %s: word %s, %d cells' % (name, T['target'], cost))
        for ln in lines:
            print(ln)
    print('  letters: in N, A B C are the variables of a nice relation A B A = C and y1..y7 its gadget variables;')
    print("  in K3, ab = bar(a), gs = g*, b1 = b', b2 = b'', c1 = c', c2 = c''; in C1, vb = bar(v), fb = bar(f),")
    print("  Z = Z[b,c], Z1 = Z', Z2 = Z''; in G2, ts = t*, tsb = bar(t*), w1 = w', w2 = w'', u1 = u', u2 = u''.")
    print()


def fmt(gam, w):
    s = []
    for x in w:
        nm = 'J' if abs(x) == gam.J else gam.name[abs(x) - 1]
        s.append(nm + ('^-1' if x < 0 else ''))
    return ' '.join(s)


def sources(gam, F):
    cnt = {}
    for (_, k, _) in F:
        if k[0] == 'eq':
            lab = 'equation (%s)' % gam.src[k[1]]
        elif k[0] == 'com':
            lab = 'commutator'
        elif k[0] == 'sq':
            lab = 'square'
        else:
            lab = k[0]
        cnt[lab] = cnt.get(lab, 0) + 1
    return cnt


def check_dir(d, quiet=False, mutate=None):
    """Build and verify all certificates for the files in d (mutate, if given, alters the data first, for the
    negative controls). Returns (Gamma, engine, results, failed words)."""
    rawP = open(os.path.join(d, 'egamma0_P.json'), 'rb').read()
    rawG = open(os.path.join(d, 'game_Ab.json'), 'rb').read()
    P = json.loads(rawP)
    G = json.loads(rawG)
    if mutate is not None:
        mutate(P, G)
    if not quiet:
        print('input  egamma0_P.json  sha256 %s' % hashlib.sha256(rawP).hexdigest())
        print('input  game_Ab.json    sha256 %s' % hashlib.sha256(rawG).hexdigest())
    gam = Gamma(G)
    eng = Engine(gam)
    res = build(P, gam, eng)
    bad = [(t, lab) for (t, lab, w, F) in res if not verify(gam, w, F)]
    return gam, eng, res, bad


def report(gam, eng, res, bad, P_counts=None):
    print('P: |S0| = %d, |C0| = %d, |C1| = %d, %d linear sets; Gamma(A,b): n = %d variables, m = %d equations'
          % (P_counts + (gam.n, len(gam.eqs))))
    nR = P_counts[0] + P_counts[1] + P_counts[2] + P_counts[3]
    print('words certified: %d relators of P (|S0| + |C0| + |C1| + |LIN| = %d) and the word of (G2)' % (len(res) - 1, nR))
    if len(res) - 1 != nR:
        bad.append(('coverage', 'not every relator of P has a certificate'))
    print()
    print('%-34s %6s %6s %6s' % ('type', 'words', 'min', 'max'))
    by = {}
    for (t, lab, w, F) in res:
        by.setdefault(t, []).append((len(F), lab, w, F))
    for t in TYPE_ORDER:
        if t in by:
            a = [x[0] for x in by[t]]
            print('%-34s %6d %6d %6d' % (t, len(a), min(a), max(a)))
    for t in by:
        if t not in TYPE_ORDER:
            print('unexpected type', t)
    print()
    print('one instance of each type: Psi(r), and the relators of Gamma(A,b) used, by kind and source')
    for t in TYPE_ORDER:
        if t not in by:
            continue
        ar, lab, w, F = max(by[t], key=lambda x: x[0])
        print('  %s  %s:  Psi(r) = %s' % (t, lab, fmt(gam, w)))
        cnt = sources(gam, F)
        print('      area <= %d:  %s' % (ar, ', '.join('%s x%d' % (k, v) for k, v in sorted(cnt.items()))))
    lens = [len(u) for (t, lab, w, F) in res for (u, k, e) in F]
    print()
    print('longest conjugator in any certificate: %d letters' % max(lens))
    print('cells added to reorder equations whose product order differs from the templates: %d' % eng.adapted)
    A0 = max(len(F) for (t, lab, w, F) in res)
    G1 = max(len(F) for (t, lab, w, F) in res if not t.startswith('(G2)'))
    print()
    if bad:
        for b in bad:
            print('FAIL  %s %s: the certificate does not reduce to Psi(r)' % b if b[0] != 'coverage' else 'FAIL  ' + b[1])
    else:
        print('PASS  all %d certificates verify: each factor is a conjugate of a relator of Gamma(A,b) and their product'
              ' is freely equal to the word' % len(res))
    print('(G1): every Psi(r), r in R, has area at most %d;  (G2): area at most %d' %
          (G1, [len(F) for (t, lab, w, F) in res if t.startswith('(G2)')][0]))
    print('A_0 = %d' % A0)
    return A0


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(2)
    d = sys.argv[1]
    if len(sys.argv) > 2 and sys.argv[2] == '--negctl':
        sys.exit(negctl(d))
    try:
        gam, eng, res, bad = check_dir(d)
    except CertError as ex:
        print('FAIL  %s' % ex)
        sys.exit(1)
    print()
    print_templates()
    P = json.load(open(os.path.join(d, 'egamma0_P.json')))
    A0 = report(gam, eng, res, bad, (len(P['S0']), len(P['C0']), len(P['C1']), len(P['LIN'])))
    if A0 <= CAP:
        print('PASS  cap: every certificate has at most %d factors (largest %d)' % (CAP, A0))
    else:
        print('FAIL  cap: a certificate has %d factors, more than %d' % (A0, CAP))
        bad.append(('cap', 'more than %d factors' % CAP))
    if len(sys.argv) > 3 and sys.argv[2] == '--dump':
        out = [{'type': t, 'word': lab, 'Psi': list(w), 'area': len(F),
                'factors': [{'conj': list(u), 'relator': list(k), 'sign': e, 'word': list(gam.relator(k))}
                            for (u, k, e) in F]} for (t, lab, w, F) in res]
        with open(sys.argv[3], 'w') as fh:
            json.dump({'letters': 'variable j (0-based) is j+1, its inverse -(j+1); J is n+1 = %d' % gam.J,
                       'certificates': out}, fh)
        print('wrote %s' % sys.argv[3])
    sys.exit(1 if bad else 0)


# ===================================================================== negative controls
def negctl(d):
    print('negative controls: each corruption must be rejected')
    allok = True

    def expect_fail(label, fn):
        nonlocal allok
        try:
            rejected = fn()
        except CertError as ex:
            rejected = True
            label += '  [%s]' % ex
        print(('PASS  rejected: ' if rejected else 'FAIL  accepted: ') + label)
        allok &= rejected

    try:
        gam, eng, res, bad = check_dir(d, quiet=True)
    except CertError as ex:
        bad = [str(ex)]
    if bad:
        print('FAIL  the true files do not verify, so the negative controls are meaningless')
        return 1
    # 1. one factor of one certificate with the wrong sign
    t, lab, w, F = next(r for r in res if r[0].startswith('C1'))
    F1 = list(F)
    u, k, e = F1[len(F1) // 2]
    F1[len(F1) // 2] = (u, k, -e)
    expect_fail('certificate of %s with factor %d inverted' % (lab, len(F1) // 2), lambda: not verify(gam, w, F1))
    # 2. one factor of one certificate dropped
    F2 = F[:3] + F[4:]
    expect_fail('certificate of %s with factor 3 dropped' % lab, lambda: not verify(gam, w, F2))
    # 3. a factor naming a commutator of two variables with no common equation
    t, lab, w, F = next(r for r in res if r[0].startswith('C0 conj'))
    j = next(k[1] for (u, k, e) in F if k[0] == 'com')
    far = next(i for i in range(gam.n) if frozenset((j, i)) not in gam.pairs and i != j)
    F3 = list(F)
    idx = next(i for i, (u, k, e) in enumerate(F) if k[0] == 'com')
    F3[idx] = (F3[idx][0], ('com', j, far), 1)
    expect_fail('certificate of %s with a commutator of variables in no common equation' % lab,
                lambda: not verify(gam, w, F3))
    # 4. a gadget equation used by (G2) with a wrong variable: in y3 y4 y5 of the gadget of bar(t*) w'' bar(t*) = u',
    #    y4 is replaced by the y4 of the gadget of bar(t*) w' bar(t*) = u''
    def mut4(P, G):
        name = [v['name'] for v in G['variables']]
        role = {tuple(v['role']): j for j, v in enumerate(G['variables'])}
        w, ts, u = name[role[('gen', P['w'])]], name[role[('t*',)]], name[role[('u',)]]
        tb = name[role[('bar', ts)]]
        y = lambda k, B, C: role[('y', k, tb, name[role[B]], name[role[C]])]
        y3, y4 = y(3, ('dprime', w), ('prime', u)), y(4, ('dprime', w), ('prime', u))
        other = y(4, ('prime', w), ('dprime', u))
        for e in G['equations']:
            if y3 in e['vars'] and y4 in e['vars']:
                e['vars'][e['vars'].index(y4)] = other
    expect_fail('game with one gadget equation used by (G2) corrupted (a wrong variable)',
                lambda: bool(check_dir(d, True, mut4)[3]))
    # 5. the equation {w, w', w''} of Step 3 deleted
    def mut5(P, G):
        role = {tuple(v['role']): j for j, v in enumerate(G['variables'])}
        xw = role[('gen', P['w'])]
        G['equations'] = [e for e in G['equations'] if not (e['source'] == "Step 3: {a,a',a''}" and xw in e['vars'])]
    expect_fail("game with the equation {w, w', w''} deleted", lambda: bool(check_dir(d, True, mut5)[3]))
    # 6. the right-hand side of x_w + x_u = 1 set to 0
    def mut6(P, G):
        for e in G['equations']:
            if e['b'] == 1:
                e['b'] = 0
    expect_fail('game with b = 0 in x_w + x_u = 1', lambda: bool(check_dir(d, True, mut6)[3]))
    # 7. a false relation in P: a C0 triple (x, y, z) replaced by (x, z, y) for a triple with z != y
    def mut7(P, G):
        for i, (x, y, z) in enumerate(P['C0']):
            if y != z:
                P['C0'][i] = [x, z, y]
                break
    expect_fail('presentation with a C0 triple (x,y,z) replaced by (x,z,y)', lambda: bool(check_dir(d, True, mut7)[3]))
    # 8. the certificate of (G2) built for the true files, re-verified against a game in which one equation it uses
    #    has a wrong variable (the equation y3 y4 y5 of one of its gadgets becomes y3 y4 y6): the final verification
    #    alone, without the engine, must reject it
    t, lab, w, F = res[-1]
    def mut8(P, G):
        name = [v['name'] for v in G['variables']]
        role = {tuple(v['role']): j for j, v in enumerate(G['variables'])}
        ts, u, xw = name[role[('t*',)]], name[role[('u',)]], name[role[('gen', P['w'])]]
        y = lambda k: role[('y', k, name[role[('bar', ts)]], name[role[('dprime', xw)]], name[role[('prime', u)]])]
        for e in G['equations']:
            if sorted(e['vars']) == sorted([y(3), y(4), y(5)]):
                e['vars'][e['vars'].index(y(5))] = y(6)
    rawP = json.load(open(os.path.join(d, 'egamma0_P.json')))
    G8 = json.load(open(os.path.join(d, 'game_Ab.json')))
    mut8(rawP, G8)
    gam8 = Gamma(G8)
    expect_fail('the true certificate of (G2) checked against a game with y3 y4 y5 -> y3 y4 y6 in one of its gadgets',
                lambda: not verify(gam8, w, F))
    # 9. a true certificate of 42 factors padded by a factor and its inverse: the replay still accepts it, so only the
    #    cap of 42 factors can reject it
    t, lab, w, F = next(r for r in res if len(r[3]) == CAP)
    F9 = list(F) + [F[0], (F[0][0], F[0][1], -F[0][2])]
    replay9 = verify(gam, w, F9)
    expect_fail('certificate of %s padded to %d factors by a factor and its inverse (replay alone accepts it: %s)'
                % (lab, len(F9), replay9), lambda: not (replay9 and len(F9) <= CAP))
    print('ALL NEGATIVE CONTROLS REJECTED' if allok else 'SOME CORRUPTION WAS ACCEPTED')
    return 0 if allok else 1


if __name__ == '__main__':
    main()
