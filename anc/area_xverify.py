#!/usr/bin/env python3
"""A second, separate check of the area bound A_* = 60 of Proposition 10.3(d) [prop:presentation], by explicit
van Kampen certificates.

Imports nothing from the other programs of anc/ and copies no code from them. Reads <dir>/egamma0_P.json (the
presentation P and the 29 recorded derivations) and, for comparison only, <dir>/relators_pauli.txt. The 27 words of
R_P are transcribed here from Table 2 [tab:RP] of the paper.

For each of the 29 target words (the s-lemma [p, iota p iota] sigma^-1, the 27 words r-hat with q -> iota p iota, and
x z x z w^-1), the program writes down a list of factors (u, r, e): u a word in S_0 u {p}, r a relator of P
(Definition 10.1 [def:EG0]: g g for g in S_0, the product of a linear set in its listed order, a b a c^-1 for (a, b, c)
in C_0, p b p^-1 c^-1 for (b, c) in C_1), and e = +1 or -1. The factors come from the three stages of the proof of
Proposition 10.3(d): each literal occurrence of [p, iota p iota] is replaced by sigma through the s-lemma certificate,
each p-conjugate of an involutive letter is resolved through C_1 (and an inverted letter through g g), and the recorded
moves of egamma0_P.json are replayed on the resolved sequence, one or more cells per move.

The verification is separate from the construction: for each word it checks that every factor names a relator of P
and has sign exactly +1 or -1, multiplies the conjugates u r^e u^-1, reduces freely, and compares with the free
reduction of the target. The number of factors bounds the area. The program then requires every target to have at
most 60 factors, and reports replay validity and the cap separately.

Usage:  python3 -I area_xverify.py <dir>            exit status 0 exactly when every certificate verifies and has at
                                                    most 60 factors
        python3 -I area_xverify.py <dir> --negctl   negative controls; exit status 0 exactly when every corruption is
                                                    rejected
"""
import copy
import json
import os
import sys

CAP = 60


class Reject(Exception):
    pass


# ----------------------------------------------------------------------------------------------- words
# A letter is (name, +1 or -1); a word is a tuple of letters.
def inv(w):
    return tuple((g, -e) for g, e in reversed(w))


def reduce(w):
    out = []
    for a in w:
        if out and out[-1] == (a[0], -a[1]):
            out.pop()
        else:
            out.append(a)
    return tuple(out)


def L(*names):
    """Positive letters."""
    return tuple((g, 1) for g in names)


P1, PM = (('p', 1),), (('p', -1),)


def ppow(n):
    return P1 * n if n >= 0 else PM * (-n)


# ----------------------------------------------------------------------------------------------- the targets
# Table 2 [tab:RP] of the paper, in the abbreviations of Definition 7.1 [def:RP]: s = [p, q], B = p s p^-1,
# t_m = p^(m-1) t p^(1-m), J = x z x z; a capital letter is an inverse letter.
TABLE2 = [
    ('H', 's s'), ('H', 's p s P s p s P s p s P'), ('H', 's p p s P P s^-1 p p s^-1 P P'), ('H', 'p s P q s^-1 Q'),
    ('Q', 't t'),
    ('S', 't s p T P s^-1'), ('S', 't s q T Q s^-1'), ('S', 'd B s p D P s^-1 B^-1'), ('S', 'd B s q D Q s^-1 B^-1'),
    ('C', 't1 t2 t1^-1 t2^-1'),
    ('A', 'd t1 D t2^-1 t1^-1'), ('A', 'd t2 D t2^-1'), ('A', 'd t3 D t3^-1'),
    ('Z', 'p x P X'), ('Z', 'p z P Z'), ('Z', 'q x Q X'), ('Z', 'q z Q Z'), ('Z', 'd x D X'), ('Z', 'd z D Z'),
    ('L', 'x x'), ('L', 'z z'), ('L', 'x z x z x z x z'),
    ('P', 'x t x T X t X T'), ('P', 'x t z T X t Z T'), ('P', 'z t x T Z t X T'), ('P', 'z t z T Z t Z T'),
    ('K', 'J t J^-1 T')]

# letters of R_P in the generators of P: a -> a for a in {p, t, d, x, z}, q -> iota p iota (Proposition 10.3(d))
HAT = {'p': P1, 't': L('t'), 'd': L('d'), 'x': L('x'), 'z': L('z'), 'q': (('i', 1), ('p', 1), ('i', 1))}
ABBR = {'s': 'p q P Q', 'B': 'p s P', 't1': 't', 't2': 'p t P', 't3': 'p p t P P', 'J': 'x z x z'}


def expand(body):
    out = ()
    for tok in body.split():
        neg = tok.endswith('^-1')
        base = tok[:-3] if neg else tok
        if base in ABBR:
            piece = expand(ABBR[base])
        elif base.lower() in HAT and len(base) == 1:
            piece = HAT[base.lower()] if base.islower() else inv(HAT[base.lower()])
        else:
            raise ValueError(tok)
        out += inv(piece) if neg else piece
    return out


SIG = expand('s')                       # [p, iota p iota] = p i p i p^-1 i^-1 p^-1 i^-1, literally
SLEMMA = SIG + (('sigma', -1),)          # the s-lemma target [p, iota p iota] sigma^-1


def sigma_substitute(w):
    """Replace each literal occurrence of SIG by sigma and of SIG^-1 by sigma^-1, scanning from the left."""
    out, k, n, SI = [], 0, 0, inv(SIG)
    while k < len(w):
        if w[k:k + len(SIG)] == SIG:
            out.append(('sigma', 1))
            k += len(SIG)
            n += 1
        elif w[k:k + len(SI)] == SI:
            out.append(('sigma', -1))
            k += len(SI)
            n += 1
        else:
            out.append(w[k])
            k += 1
    return tuple(out), n


# ----------------------------------------------------------------------------------------------- the presentation
class Pres:
    def __init__(self, D):
        self.S0 = list(D['S0'])
        self.S1 = list(D['S1'])
        self.w = D['w']
        self.C0 = {tuple(t) for t in D['C0']}
        self.C1 = {tuple(t) for t in D['C1']}
        self.LIN = [tuple(V) for V in D['LIN']]
        self.fwd = {b: c for b, c in self.C1}          # p b p^-1 = c
        self.bwd = {c: b for b, c in self.C1}

    def relator(self, key):
        """The relator of P named by key, or Reject."""
        kind = key[0]
        if kind == 'sq' and key[1] in self.S0:
            return L(key[1], key[1])
        if kind == 'lin' and tuple(key[1:]) in self.LIN:
            return L(*key[1:])
        if kind == 'C0' and tuple(key[1:]) in self.C0:
            a, b, c = key[1:]
            return L(a, b, a) + ((c, -1),)
        if kind == 'C1' and tuple(key[1:]) in self.C1:
            b, c = key[1:]
            return (('p', 1), (b, 1), ('p', -1), (c, -1))
        raise Reject('not a relator of P: %r' % (key,))

    def lin_of(self, letters):
        for V in self.LIN:
            if sorted(V) == sorted(letters):
                return V
        raise Reject('no linear set %r' % (letters,))


def rotation(V, blk):
    """If blk is a cyclic rotation V[k:] + V[:k] of V, return k, else None."""
    for k in range(len(V)):
        if tuple(V[k:] + V[:k]) == tuple(blk):
            return k
    return None


# ----------------------------------------------------------------------------------------------- the certificates
def front_end(P, word, prefix):
    """Resolve a word in S_0 u {p} of p-exponent 0 to a sequence of positive involutive letters. Each letter g^e with
    p-exponent n before it is the conjugate p^n g^e p^-n; g^-1 -> g costs one cell g g, and each conjugation by p one
    cell of C_1. Returns (sequence, factors); prefix is the word standing before, for the conjugators."""
    n, seq, F = 0, [], []
    for (g, e) in word:
        if g == 'p':
            n += e
            continue
        if g not in P.S0:
            raise Reject('letter %s not in S_0' % g)
        here = prefix + L(*seq)
        if e == -1:
            F.append((here + ppow(n), ('sq', g), -1))
        c = g
        for s in range(abs(n), 0, -1):
            if n > 0:                                    # p c p^-1 -> C_1(c)
                if c not in P.fwd:
                    raise Reject('no relation p %s p^-1 in C_1' % c)
                F.append((here + ppow(s - 1), ('C1', c, P.fwd[c]), 1))
                c = P.fwd[c]
            else:                                        # p^-1 c p -> b with p b p^-1 = c
                if c not in P.bwd:
                    raise Reject('no relation p b p^-1 = %s in C_1' % c)
                F.append((here + ppow(-(s - 1)) + PM, ('C1', P.bwd[c], c), -1))
                c = P.bwd[c]
        seq.append(c)
    if n != 0:
        raise Reject('p-exponent %d' % n)
    return seq, F


def swap_cells(P, here, a, b):
    """Factors with product here (a b a^-1 b^-1) here^-1, from a commutation listed in C_0 (two cells)."""
    if (a, b, b) in P.C0:
        return [(here, ('C0', a, b, b), 1), (here + L(b), ('sq', a), -1)]
    if (b, a, a) in P.C0:
        return [(here + ((b, -1),), ('C0', b, a, a), 1), (here, ('sq', b), -1)]
    raise Reject('%s and %s do not commute by a listed relation' % (a, b))


def lin_rot_cell(P, here, V, k):
    """The factor here (V[k:] + V[:k]) here^-1 (one cell)."""
    return (here + inv(L(*V[:k])), ('lin',) + tuple(V), 1)


def replay(P, seq, moves, prefix):
    """Replay the recorded moves on the resolved sequence; returns the factors. Every move becomes one or more
    cells, each a conjugate of one relator of P."""
    st, F = list(seq), []
    for mv in moves:
        kind, j = mv[0], mv[1]
        here = prefix + L(*st[:j])
        if kind == 'cancel':
            if not (j + 1 < len(st) and st[j] == st[j + 1] == mv[2]):
                raise Reject('bad cancel %r' % (mv,))
            F.append((here, ('sq', st[j]), 1))
            del st[j:j + 2]
        elif kind == 'conj':
            a, b, c = mv[2:5]
            if st[j:j + 3] != [a, b, a]:
                raise Reject('bad conj %r' % (mv,))
            F.append((here, ('C0', a, b, c), 1))
            st[j:j + 3] = [c]
        elif kind == 'swap':
            a, b = mv[2:4]
            if st[j:j + 2] != [a, b]:
                raise Reject('bad swap %r' % (mv,))
            F += swap_cells(P, here, a, b)
            st[j:j + 2] = [b, a]
        elif kind == 'lin':
            blk = list(mv[2])
            if st[j:j + 3] != blk:
                raise Reject('bad lin %r' % (mv,))
            V = P.lin_of(blk)
            k = rotation(V, blk)
            if k is None:                                # swap the first two letters, then a rotation remains
                F += swap_cells(P, here, blk[0], blk[1])
                blk = [blk[1], blk[0], blk[2]]
                k = rotation(V, blk)
            F.append(lin_rot_cell(P, here, V, k))
            del st[j:j + 3]
        elif kind == 'merge':
            a, b, e = mv[2:5]
            if st[j:j + 2] != [a, b]:
                raise Reject('bad merge %r' % (mv,))
            V = P.lin_of([a, b, e])
            k = rotation(V, [a, b, e])
            if k is not None:                            # a b e^-1 = (a b e)(e e)^-1
                F += [lin_rot_cell(P, here, V, k), (here, ('sq', e), -1)]
            else:                                        # a b e^-1 = (a a) a^-1 (b b) a (e b a)^-1
                k = rotation(V, [e, b, a])
                if k is None:
                    raise Reject('bad merge %r' % (mv,))
                c = lin_rot_cell(P, here, V, k)
                F += [(here, ('sq', a), 1), (here + ((a, -1),), ('sq', b), 1), (c[0], c[1], -1)]
            st[j:j + 2] = [e]
        else:
            raise Reject('unknown move %r' % (mv,))
    if st:
        raise Reject('the moves leave %r' % (st,))
    return F


def certificate(P, target, deriv, slemma_F):
    """The factors for one target word, following the three stages of the proof of Proposition 10.3(d)."""
    F = []
    if slemma_F is None:                                 # the s-lemma itself: no substitution
        sub = target
    else:
        sub, _ = sigma_substitute(target)
        # each occurrence of SIG (resp. SIG^-1) is replaced by sigma (resp. sigma^-1): X Y^-1 = SLEMMA, resp.
        # sigma^-1 SLEMMA^-1 sigma, conjugated by the word standing before it, with earlier occurrences already replaced
        before, k, done = (), 0, ()
        while k < len(target):
            if target[k:k + len(SIG)] == SIG:
                F += [(done + u, r, e) for (u, r, e) in slemma_F]
                done += (('sigma', 1),)
                k += len(SIG)
            elif target[k:k + len(SIG)] == inv(SIG):
                F += [(done + (('sigma', -1),) + u, r, -e) for (u, r, e) in reversed(slemma_F)]
                done += (('sigma', -1),)
                k += len(SIG)
            else:
                done += (target[k],)
                k += 1
        assert done == sub
    seq, F2 = front_end(P, sub, ())
    if seq != list(deriv['seq']):
        raise Reject('resolved sequence %s differs from the recorded %s' % (seq, deriv['seq']))
    return F + F2 + replay(P, seq, deriv['moves'], ())


def verify(P, target, F):
    """Separate check: every factor names a relator of P with sign +1 or -1, and the product of the conjugates
    reduces freely to the target. Returns True or raises Reject."""
    prod = ()
    for (u, key, e) in F:
        if e not in (1, -1):
            raise Reject('bad sign %r' % (e,))
        r = P.relator(key)
        prod = reduce(prod + u + (r if e == 1 else inv(r)) + inv(u))
    if prod != reduce(target):
        raise Reject('the product of the factors is not the target word')
    return True


def targets_of(D):
    """The 29 target words with their recorded derivations, matched by family and word."""
    rec = {(d['family'], d['word']): d for d in D['derivations']}
    out = [('slemma', '[p,q] sigma^-1', SLEMMA, rec.get(('slemma', '[p,q] sigma^-1')))]
    for fam, body in TABLE2:
        out.append((fam, body, expand(body), rec.get((fam, body))))
    out.append(('Jlink', '(xz)^2 w^-1', L('x', 'z', 'x', 'z') + ((D['w'], -1),), rec.get(('Jlink', '(xz)^2 w^-1'))))
    return out


def run(D, quiet=False, edit=None):
    """Build and verify every certificate. edit(name, F) may alter a certificate (negative controls). Returns
    {name: number of factors}, or raises Reject."""
    P = Pres(D)
    if P.S1 != ['p']:
        raise Reject('S_1 must be {p}')
    T = targets_of(D)
    if len(D['derivations']) != 29 or any(t[3] is None for t in T):
        raise Reject('the file does not record one derivation for each of the 29 targets')
    slemma_F = None
    areas = {}
    for fam, body, target, deriv in T:
        F = certificate(P, target, deriv, slemma_F if fam != 'slemma' else None)
        if fam == 'slemma':
            slemma_F = list(F)
        if edit is not None:
            F = edit((fam, body), F)
        verify(P, target, F)
        areas[(fam, body)] = len(F)
        if not quiet:
            print('ok    %-6s %-34s %2d factors' % (fam, body, len(F)))
    return areas


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        return 2
    d = sys.argv[1]
    D = json.load(open(os.path.join(d, 'egamma0_P.json')))
    if len(sys.argv) > 2 and sys.argv[2] == '--negctl':
        return negctl(D)
    fails = []
    # the transcription of Table 2 against the data file, as words in the free group
    rp = []
    for line in open(os.path.join(d, 'relators_pauli.txt')):
        line = line.strip()
        if line and not line.startswith('#'):
            fam, body = [x.strip() for x in line.split('|')]
            rp.append((fam, reduce(expand(body))))
    same = sorted(rp) == sorted((f, reduce(expand(b))) for f, b in TABLE2)
    print(('PASS  ' if same else 'FAIL  ') + 'relators_pauli.txt has the 27 words of Table 2, as transcribed here')
    if not same:
        fails.append('R_P transcription')
    try:
        areas = run(D)
    except Reject as ex:
        print('FAIL  %s' % ex)
        return 1
    print('PASS  replay: all %d certificates verify; each factor is a conjugate of a relator of P, and the product '
          'reduces freely to the target word' % len(areas))
    mx = max(areas.values())
    worst = [k for k, v in areas.items() if v == mx]
    sl = areas[('slemma', '[p,q] sigma^-1')]
    print('INFO  s-lemma: %d factors; largest: %d factors, for %s; total over the 29 words: %d'
          % (sl, mx, ', '.join('%s %s' % k for k in worst), sum(areas.values())))
    cap = mx <= CAP
    print(('PASS  ' if cap else 'FAIL  ') + 'cap: every one of the 29 words has at most %d factors, so area at most %d '
          '(largest %d)' % (CAP, CAP, mx))
    if not cap:
        fails.append('cap')
    print('\n%s' % ('ALL CHECKS PASSED' if not fails else 'FAILURES: %s' % ', '.join(fails)))
    return 1 if fails else 0


# ----------------------------------------------------------------------------------------------- negative controls
def negctl(D):
    print('negative controls: each corruption must be rejected')
    allok = True
    worst = ('H', 's p s P s p s P s p s P')

    def expect(label, D2, edit=None, check_cap=False):
        nonlocal allok
        try:
            areas = run(D2, quiet=True, edit=edit)
            rejected = check_cap and max(areas.values()) > CAP
            why = 'cap: %d factors' % max(areas.values()) if rejected else ''
        except Reject as ex:
            rejected, why = True, str(ex)
        print(('PASS  rejected: ' if rejected else 'FAIL  accepted: ') + label + ('  [%s]' % why if why else ''))
        allok &= rejected

    try:
        run(D, quiet=True)
    except Reject:
        print('FAIL  the true file does not verify, so the negative controls are meaningless')
        return 1
    # 1. a factor dropped
    expect('the certificate of %s %s with one factor dropped' % worst, D,
           edit=lambda k, F: F[:5] + F[6:] if k == worst else F)
    # 2. a valid certificate padded by a factor and its inverse: replay still valid, the cap must reject it
    expect('the certificate of %s %s padded to %d factors by a factor and its inverse (replay valid)' % (worst + (62,)),
           D, edit=lambda k, F: F + [F[0], (F[0][0], F[0][1], -F[0][2])] if k == worst else F, check_cap=True)
    # 3. a factor with sign 2
    expect('a factor with sign 2', D, edit=lambda k, F: [(F[0][0], F[0][1], 2)] + F[1:] if k == worst else F)
    # 4. the C_0 triple (sigma, g4, g5) used by a derivation deleted from P
    D4 = copy.deepcopy(D)
    D4['C0'] = [t for t in D4['C0'] if tuple(t) != ('sigma', 'g4', 'g5')]
    expect('the presentation with the C_0 triple (sigma, g4, g5) deleted', D4)
    # 5. a recorded move falsified: in x z x z x z x z, the triple (x, z, g12) replaced by (x, z, g13)
    D5 = copy.deepcopy(D)
    for dd in D5['derivations']:
        if dd['word'] == 'x z x z x z x z':
            for mv in dd['moves']:
                if mv[0] == 'conj' and mv[2:5] == ['x', 'z', 'g12']:
                    mv[4] = 'g13'
                    break
    expect('a derivation with the move (x, z, g12) replaced by (x, z, g13)', D5)
    # 6. the recorded resolved sequence of L: x x replaced by the nontrivial x z
    D6 = copy.deepcopy(D)
    for dd in D6['derivations']:
        if dd['word'] == 'x x':
            dd['seq'] = ['x', 'z']
    expect('the derivation of L: x x with its resolved sequence replaced by x z', D6)
    # 7. claimed certificates of the nontrivial word x z: a derivation (cancel), and the single factor x x
    P = Pres(D)
    for label, fn in (('a derivation of the nontrivial word x z by one cancellation',
                       lambda: certificate(P, L('x', 'z'), {'seq': ['x', 'z'], 'moves': [['cancel', 0, 'x']]}, None)),
                      ('the one-factor certificate x x for the nontrivial word x z',
                       lambda: verify(P, L('x', 'z'), [((), ('sq', 'x'), 1)]))):
        try:
            fn()
            rejected, why = False, ''
        except Reject as ex:
            rejected, why = True, str(ex)
        print(('PASS  rejected: ' if rejected else 'FAIL  accepted: ') + label + ('  [%s]' % why if why else ''))
        allok &= rejected
    print('ALL NEGATIVE CONTROLS REJECTED' if allok else 'SOME CORRUPTION WAS ACCEPTED')
    return 0 if allok else 1


if __name__ == '__main__':
    sys.exit(main())
