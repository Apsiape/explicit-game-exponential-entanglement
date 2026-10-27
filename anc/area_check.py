"""Independent checker for the EGamma_0 presentation P of Proposition 10.3 [prop:presentation], with an exact area count.

Written from the paper's text (Definitions 6.5 [def:GP], 7.1 [def:RP] and 10.1 [def:EG0], Lemma 6.9 [lem:GPp],
Proposition 10.3 [prop:presentation]) and the JSON data only;
no code from anc/ is imported or copied.  Reads (as data):
    <dir>/egamma0_P.json        the presentation and the authors' derivations
    <dir>/relators_pauli.txt    the 27 words of R_P
Checks
  1. format of Definition 10.1 [def:EG0], S1 = {p}, |S0| = 26, |C0| = 76, |C1| = 10, 8 linear sets of size 3, SV18 commutation listing;
  2. every relation of P holds in an own faithful model of G_P^+ (homomorphism P -> G_P^+);
  3. (R1): w -> J = (xz)^2, J central and != 1; centrality triples (g,w,w) and C1 (w,w) present;
  4. the C0 composition 32 + 25 + 19 = 76;
  5. (R3) re-derived independently: own front end + own Dijkstra search over sequences using ONLY listed relations,
     with an exact cell count in the free group F(S0 u S1) (every use of x^2 = e is counted);
     the authors' recorded moves are also replayed with the same exact cost model;
  6. A_* (max area bound over the 29 target words) compared with the paper's A_* = 60;
  7. ell_E = max length of the free reduction of theta(r), r in R (paper: 44), and the longest word of R_P (paper: 22);
  8. negative controls.
Run inside anc/:  python3 -I area_check.py .
"""
import heapq
import itertools
import json
import os
import sys

DIR = sys.argv[1]
D = json.load(open(os.path.join(DIR, 'egamma0_P.json')))
FAILS = []


def ok(cond, msg):
    print(('PASS  ' if cond else 'FAIL  ') + msg, flush=True)
    if not cond:
        FAILS.append(msg)


# ----------------------------------------------------------------- own model of G_P^+
# letters: p P (p, p^-1), q Q, i I (iota), t T, d D, x X, z Z ; affine part acts on configurations (frozensets)
def pt(letter, y):
    r, h = y
    if letter == 'p':
        return (1, h + 1) if r == 1 else ((1, 1) if (r == 2 and h == 1) else ((2, h - 1) if r == 2 else y))
    if letter == 'P':
        return ((2, 1) if h == 1 else (1, h - 1)) if r == 1 else ((2, h + 1) if r == 2 else y)
    if letter == 'q':
        return (1, h + 1) if r == 1 else ((1, 1) if (r == 3 and h == 1) else ((3, h - 1) if r == 3 else y))
    if letter == 'Q':
        return ((3, 1) if h == 1 else (1, h - 1)) if r == 1 else ((3, h + 1) if r == 3 else y)
    if letter in 'iI':
        return y if r == 1 else ((3, h) if r == 2 else (2, h))
    raise ValueError(letter)


O11, O12 = (1, 1), (1, 2)


def aff(letter, v):
    if letter in 'pPqQiI':
        return frozenset(pt(letter, y) for y in v)
    if letter in 'tT':
        return v ^ {O11}
    if letter in 'dD':
        return (v ^ {O12}) if O11 in v else v
    raise ValueError(letter)


def evaluate(word):
    # element = (s, A, B; affine word g); reading a lamp letter after prefix g multiplies by the lamp at site g(0)
    s, A, B = 0, frozenset(), frozenset()
    g = []
    for c in word:
        if c in 'xXzZ':
            v = frozenset()
            for a in reversed(g):
                v = aff(a, v)
            if c in 'xX':
                s ^= int(v in B)
                A = A ^ {v}
            else:
                B = B ^ {v}
        else:
            g.append(c)
    return (s, A, B), g


def affine_identity(g):
    def app(v):
        for a in reversed(g):
            v = aff(a, v)
        return v
    if app(frozenset()) != frozenset():
        return False
    for r in (1, 2, 3):
        for h in range(1, len(g) + 8):
            if app(frozenset([(r, h)])) != frozenset([(r, h)]):
                return False
    return True


def trivial(word):
    lam, g = evaluate(word)
    return lam == (0, frozenset(), frozenset()) and affine_identity(g)


def is_J(word):
    lam, g = evaluate(word)
    return lam == (1, frozenset(), frozenset()) and affine_identity(g)


INVL = {c: c.swapcase() for c in 'pPqQiItTdDxXzZ'}


def winv(w):
    return ''.join(INVL[c] for c in reversed(w))


def fred(w):
    out = []
    for c in w:
        if out and out[-1] == INVL[c]:
            out.pop()
        else:
            out.append(c)
    return ''.join(out)


# ----------------------------------------------------------------- 1. format
S0 = D['S0']
S1 = D['S1']
w = D['w']
C0 = [tuple(t) for t in D['C0']]
C1 = [tuple(t) for t in D['C1']]
LIN = [tuple(V) for V in D['LIN']]
ok(S1 == ['p'], 'S1 = {p}')
ok(len(S0) == 26, '|S0| = 26 (%d)' % len(S0))
ok(len(C0) == 76 and len(set(C0)) == 76, '|C0| = 76 distinct triples (%d)' % len(C0))
ok(len(C1) == 10, '|C1| = 10 (%d)' % len(C1))
ok(len(LIN) == 8 and all(len(set(V)) == 3 for V in LIN), '8 linear sets, each of 3 distinct elements')
ok(all(set(word) <= set('pPiItTdDxXzZ') for word in S0.values()), 'defining words use only p,i,t,d,x,z (no q)')
for b in 'itdxz':
    ok(S0.get(b) == b, 'base generator %s defined as itself' % b)
ok(fred(S0['sigma']) == fred('p' + 'i' + 'p' + 'i' + 'P' + 'I' + 'P' + 'I'), 'sigma = [p, i p i] = p i p i P I P I (freely)')
ok(all(a in S0 and b in S0 and c in S0 for a, b, c in C0), 'C0 triples lie in S0^3 (type E3)')
ok(all(b in S0 and c in S0 for b, c in C1), 'C1 pairs lie in S0^2 (type E4, y = p)')
ok(all(set(V) <= set(S0) for V in LIN), 'linear sets lie in S0 (type E2)')
C0set = set(C0)
miss = [(a, b) for V in LIN for a, b in itertools.combinations(sorted(V), 2) if (a, b, b) not in C0set and (b, a, a) not in C0set]
ok(not miss, 'every pair inside a linear set is listed as a commutation triple (SV18 Sec. 6 format) %s' % miss[:3])

# ----------------------------------------------------------------- 2. homomorphism
bad = [g for g, word in S0.items() if not trivial(word + word) or trivial(word)]
ok(not bad, 'all 26 defining words are nontrivial involutions in G_P^+ %s' % bad[:3])
elts = {}
dup = []
for g, word in S0.items():
    for h, word2 in elts.items():
        if trivial(word + winv(word2)):
            dup.append((g, h))
    elts[g] = word
ok(not dup, 'the 26 generators represent 26 distinct elements %s' % dup[:3])
bad = [t for t in C0 if not trivial(S0[t[0]] + S0[t[1]] + S0[t[0]] + winv(S0[t[2]]))]
ok(not bad, 'all 76 C0 relations a b a = c hold %s' % bad[:3])
bad = [t for t in C1 if not trivial('p' + S0[t[0]] + 'P' + winv(S0[t[1]]))]
ok(not bad, 'all 10 C1 relations p b p^-1 = c hold %s' % bad[:3])
bad = [V for V in LIN if not trivial(''.join(S0[g] for g in V))
       or not all(trivial(S0[a] + S0[b] + winv(S0[a]) + winv(S0[b])) for a, b in itertools.combinations(V, 2))]
ok(not bad, 'all 8 linear relations hold, members commute %s' % bad[:3])
images = {}
for b, c in C1:
    images.setdefault(b, set()).add(c)
ok(all(len(v) == 1 for v in images.values()), 'C1 is a partial function b -> c')

# ----------------------------------------------------------------- 3. (R1)
ok(is_J(S0[w]), 'w = %s maps to J = (xz)^2, the nontrivial central element' % w)
ok(all(trivial(S0[w] + l + winv(S0[w]) + INVL[l]) for l in 'pitdxz'), 'J commutes with p, iota, t, d, x, z in G_P^+')
cent = [(g, w, w) for g in S0 if g != w]
ok(all(t in C0set for t in cent), 'the 25 centrality triples (g, w, w) are in C0')
ok((w, w) in set(C1), 'C1 contains p w p^-1 = w')
ok(trivial('ipiQ'), 'q = iota p iota in G_P^+ (Lemma 6.9 [lem:GPp])')

# named generators of the paper (Proposition 10.3 [prop:presentation] and the text after it)
named = {'g1': 'piP', 'g2': 'ppiPP', 'g7': 'ptP', 'g11': 'pptPP', 'g10': 'tptP', 'g8': 'pdP', 'g14': 'xzxz',
         'g12': 'xzx', 'g13': 'zxz', 'g15': 'xtx', 'g16': 'txt', 'g17': 'xtxt', 'g19': 'ztz', 'g18': 'tzt', 'g20': 'ztzt'}
ok(all(trivial(S0[g] + winv(wd)) for g, wd in named.items()), 'generators named in the text match their JSON words')
ok(trivial(S0['g3'] + winv(S0['g1'] + S0['g2'] + S0['g1'])), 'g3 = iota1 iota2 iota1')
ok(trivial(S0['g4'] + winv('p' + S0['sigma'] + 'P')) and trivial(S0['g6'] + winv('pp' + S0['sigma'] + 'PP')),
   'g4 = p sigma p^-1, g6 = p^2 sigma p^-2')
ok(trivial(S0['g3'] + winv(S0['sigma'] + 'i')), 's-lemma element: iota1 iota2 iota1 = sigma iota (eq. (19) [game:s-lemma])')
expect_lin = [{'g3', 'i', 'sigma'}, {'t', 'g7', 'g10'}, {'g12', 'z', 'g14'}, {'g13', 'x', 'g14'},
              {'g15', 't', 'g17'}, {'g16', 'x', 'g17'}, {'g19', 't', 'g20'}, {'g18', 'z', 'g20'}]
ok(sorted(map(sorted, expect_lin)) == sorted(map(sorted, LIN)),
   'linear sets = {i1i2i1,i,sigma}, {t,t2,tt2}, {xzx,z,w}, {zxz,x,w}, {uvu,v,uvuv}, {vuv,u,uvuv} as in the text')
expect_c1 = {('i', 'g1'), ('g1', 'g2'), ('sigma', 'g4'), ('g4', 'g6'), ('t', 'g7'), ('g7', 'g11'), ('d', 'g8'),
             ('x', 'x'), ('z', 'z'), (w, w)}
ok(set(C1) == expect_c1, 'C1 = the ten triples of the text (p: i->i1->i2, s->psP->p2sP2, t->t2->t3, d->pdP, fixes x,z,w)')

# ----------------------------------------------------------------- R_P and target words
ABBR = {'s': 'pqPQ', 't1': 't', 't2': 'ptP', 't3': 'pptPP', 'J': 'xzxz'}
ABBR['B'] = 'p' + ABBR['s'] + 'P'


def expand(body):
    out = ''
    for tok in body.split():
        inv = tok.endswith('^-1')
        base = tok[:-3] if inv else tok
        piece = ABBR.get(base, base)
        assert set(piece) <= set(INVL), tok
        out += winv(piece) if inv else piece
    return out


RP = []
for line in open(os.path.join(DIR, 'relators_pauli.txt')):
    line = line.strip()
    if line and not line.startswith('#'):
        fam, body = [x.strip() for x in line.split('|')]
        RP.append((fam, body))
ok(len(RP) == 27, 'R_P has 27 words')
TABLE2 = [  # Table 2 [tab:RP] of the paper, written independently from the PDF (families H,Q,S,C,A,Z',L',P',K)
    ('H', 's s'), ('H', 's p s P s p s P s p s P'), ('H', 's p p s P P s^-1 p p s^-1 P P'), ('H', 'p s P q s^-1 Q'),
    ('Q', 't t'), ('S', 't s p T P s^-1'), ('S', 't s q T Q s^-1'), ('S', 'd B s p D P s^-1 B^-1'),
    ('S', 'd B s q D Q s^-1 B^-1'), ('C', 't1 t2 t1^-1 t2^-1'), ('A', 'd t1 D t2^-1 t1^-1'), ('A', 'd t2 D t2^-1'),
    ('A', 'd t3 D t3^-1')] + [('Z', '%s %s %s %s' % (l, a, l.upper(), a.upper())) for l in 'pqd' for a in 'xz'] + [
    ('L', 'x x'), ('L', 'z z'), ('L', 'x z x z x z x z')] + [
    ('P', '%s t %s T %s t %s T' % (a, b, a.upper(), b.upper())) for a in 'xz' for b in 'xz'] + [('K', 'J t J^-1 T')]
ok(all(fred(expand(b1)) == fred(expand(b2)) for (f1, b1), (f2, b2) in zip(sorted(RP), sorted(TABLE2))),
   'relators_pauli.txt agrees with Table 2 [tab:RP] as transcribed from the PDF')
ok(all(trivial(fred(expand(b))) for _, b in RP), 'all 27 words of R_P are trivial in G_P')
lens = [len(fred(expand(b))) for _, b in RP]
print('INFO  longest freely reduced word of R_P: %d letters (paper, Theorem 9.5 [thm:upper]: ell = 22)' % max(lens))


def qsub(word):
    return ''.join('ipi' if c == 'q' else ('IPI' if c == 'Q' else c) for c in word)


# ----------------------------------------------------------------- 5. (R3), exact cost model
# Relators of P as free words (Definition 10.1 [def:EG0]):  E1: g g ;  E2: x y x y^-1 for listed commutations, product in the
# written (sorted) order ;  E3: a b a c^-1 ;  E4: p b p^-1 c^-1.  A move u -> v costs the number of relator cells
# needed for u v^-1 (checked case by case below).
LINorder = {frozenset(V): tuple(V) for V in LIN}   # the written order (JSON lists are sorted)


def rot(t):
    return [tuple(t[k:] + t[:k]) for k in range(len(t))]


def lin_delete_cost(blk):
    V = frozenset(blk)
    if V not in LINorder:
        return None
    order = LINorder[V]
    if tuple(blk) in rot(order):
        return 1                         # a cyclic conjugate of the product relator
    # reversed order: one listed commutation (cost 2) turns it into a rotation
    return 3


def merge_cost(a, b, e):
    V = frozenset((a, b, e))
    if V not in LINorder or len(V) != 3:
        return None
    order = LINorder[V]
    if (a, b, e) in rot(order):
        return 2                         # relator a b e, plus e -> e^-1 (one E1)
    return 3                             # inverse relator rotation a^-1 b^-1 e^-1, plus two E1


def swap_ok(a, b):
    return (a, b, b) in C0set or (b, a, a) in C0set


def neighbours(st, allow_extra=True):
    L = len(st)
    for j in range(L - 1):
        if st[j] == st[j + 1]:
            yield st[:j] + st[j + 2:], 1, ('cancel', j, st[j])
    for j in range(L - 2):
        a, b, a2 = st[j:j + 3]
        if a == a2:
            for (x, y, c) in C0byab.get((a, b), []):
                yield st[:j] + (c,) + st[j + 3:], 1, ('conj', j, a, b, c)
    for j in range(L - 1):
        a, b = st[j], st[j + 1]
        if a != b and swap_ok(a, b) and (allow_extra or (a, b, b) in USED_SWAPS or (b, a, a) in USED_SWAPS):
            yield st[:j] + (b, a) + st[j + 2:], 2, ('swap', j, a, b)
        for V in LIN:
            if a in V and b in V and a != b:
                e = [g for g in V if g not in (a, b)][0]
                c = merge_cost(a, b, e)
                if c is not None:
                    yield st[:j] + (e,) + st[j + 2:], c, ('merge', j, a, b, e)
    for j in range(L - 2):
        blk = st[j:j + 3]
        c = lin_delete_cost(blk)
        if c is not None:
            yield st[:j] + st[j + 3:], c, ('lin', j, blk)


C0byab = {}
for t in C0:
    C0byab.setdefault((t[0], t[1]), []).append(t)
USED_SWAPS = set()


def dijkstra(seq, allow_extra=True, limit=400000):
    start = tuple(seq)
    dist = {start: 0}
    heap = [(0, start, [])]
    n = 0
    while heap:
        d0, st, mv = heapq.heappop(heap)
        if d0 > dist.get(st, 1e18):
            continue
        if not st:
            return d0, mv
        n += 1
        if n > limit:
            break
        for nst, c, m in neighbours(st, allow_extra):
            nd = d0 + c
            if nd < dist.get(nst, 1e18):
                dist[nst] = nd
                heapq.heappush(heap, (nd, nst, mv + [m]))
    return None, None


C1f = {b: c for b, c in C1}
C1b = {c: b for b, c in C1}
INV_S0 = {}


def front_end(word, sigma_letter=True):
    """word in p,P,i,I,t,T,d,D,x,X,z,Z and 'g'/'G' (sigma, sigma^-1). returns (seq, cost) or (None, reason)."""
    n = 0
    seq = []
    cost = 0
    for c in word:
        if c == 'p':
            n += 1
            continue
        if c == 'P':
            n -= 1
            continue
        if c in 'gG':
            g, inv = 'sigma', c == 'G'
        else:
            g, inv = c.lower(), c.isupper()
        cur = g
        for _ in range(abs(n)):
            nxt = (C1f if n > 0 else C1b).get(cur)
            if nxt is None:
                return None, 'C1 chain missing at %s (n=%d)' % (cur, n)
            cur = nxt
        seq.append(cur)
        cost += abs(n) + (1 if inv else 0)
    if n != 0:
        return None, 'p-exponent sum %d != 0' % n
    return seq, cost


SIG = 'pipiPIPI'


def sigma_substitute(word):
    """replace every block s = p i p i P I P I (from q -> i p i) by the letter g, and s^-1 by G."""
    out = ''
    k = 0
    ns = 0
    while k < len(word):
        if word.startswith(SIG, k):
            out += 'g'
            k += len(SIG)
            ns += 1
        elif word.startswith(winv(SIG), k):
            out += 'G'
            k += len(SIG)
            ns += 1
        else:
            out += word[k]
            k += 1
    return out, ns


print('\n(R3) re-derivation with an exact cell count in F(S0 u S1)')
results = {}
# s-lemma first: target s sigma^-1 with s written out
seq, fc = front_end(SIG + 'G')
cost_s, moves_s = dijkstra(seq)
A_s = fc + cost_s
ok(cost_s is not None, 's-lemma  [p, i p i] sigma^-1: front end %s (cost %d), search cost %d, area <= %d' % (seq, fc, cost_s, A_s))
results['slemma'] = A_s
used_C0 = set()
for m in moves_s:
    if m[0] == 'conj':
        used_C0.add(m[2:5])
targets = []
for fam, body in RP:
    raw = qsub(expand(body))          # r-hat: q -> i p i, before free reduction
    ok(trivial(fred(raw)), '%s %-30s r-hat is trivial in G_P^+' % (fam, body))
    sub, ns = sigma_substitute(raw)
    # the substitution is literal: substituting the sigma word back gives r-hat again
    back = sub.replace('g', SIG).replace('G', winv(SIG))
    assert back == raw
    targets.append((fam, body, sub, ns))
targets.append(('Jlink', '(xz)^2 w^-1', None, 0))
Astar = A_s
worst = None
total = 0
authors = {(d['family'], d['word']): d for d in D['derivations']}
for fam, body, sub, ns in targets:
    if fam == 'Jlink':
        seq, fc = ['x', 'z', 'x', 'z', w], 1        # w^-1 -> w is one E1 cell
    else:
        seq, fc = front_end(sub)
        if seq is None:
            ok(False, '%s %s front end failed: %s' % (fam, body, fc))
            continue
    cost, moves = dijkstra(seq)
    if cost is None:
        ok(False, '%s %s: no derivation found by my search' % (fam, body))
        continue
    for m in moves:
        if m[0] == 'conj':
            used_C0.add(m[2:5])
        if m[0] == 'swap':
            used_C0.add((m[2], m[3], m[3]) if (m[2], m[3], m[3]) in C0set else (m[3], m[2], m[2]))
    area = fc + cost + ns * A_s
    total += area
    # replay the authors' recorded moves with the same exact cost model
    key = (fam, body) if fam != 'Jlink' else ('Jlink', '(xz)^2 w^-1')
    dd = authors.get(key)
    rep = None
    if dd is not None:
        st = tuple(dd['seq'])
        same_seq = list(st) == list(seq)
        rc = 0
        good = True
        for mv in dd['moves']:
            kind, j = mv[0], mv[1]
            if kind == 'cancel':
                good &= st[j] == st[j + 1] == mv[2]; st = st[:j] + st[j + 2:]; rc += 1
            elif kind == 'conj':
                a, b, c = mv[2:5]
                good &= st[j:j + 3] == (a, b, a) and (a, b, c) in C0set; st = st[:j] + (c,) + st[j + 3:]; rc += 1
            elif kind == 'swap':
                a, b = mv[2:4]
                good &= st[j:j + 2] == (a, b) and swap_ok(a, b); st = st[:j] + (b, a) + st[j + 2:]; rc += 2
            elif kind == 'merge':
                a, b, e = mv[2:5]
                c = merge_cost(a, b, e)
                good &= st[j:j + 2] == (a, b) and c is not None; st = st[:j] + (e,) + st[j + 2:]; rc += (c or 0)
            elif kind == 'lin':
                blk = tuple(mv[2])
                c = lin_delete_cost(blk)
                good &= st[j:j + 3] == blk and c is not None; st = st[:j] + st[j + 3:]; rc += (c or 0)
        good &= (st == ())
        rep = (same_seq, good, fc + rc + ns * A_s, dd['area_bound'])
    results[(fam, body)] = area
    if area > Astar:
        Astar, worst = area, (fam, body)
    print('      %-6s %-32s n_s=%d  front %3d  search %3d  -> area <= %4d | authors: same seq %s, replay %s, exact cost %s, their bound %s'
          % (fam, body, ns, fc, cost, area, rep[0] if rep else '-', rep[1] if rep else '-', rep[2] if rep else '-',
             rep[3] if rep else '-'))
    if rep:
        ok(rep[0] and rep[1], '       authors\' derivation of %s %s replays under the exact cost model' % (fam, body))
print('INFO  A_s (s-lemma area bound) = %d' % A_s)
print('INFO  my A_* = %d (attained by %s); paper takes A_* = 60; my total over the 29 words = %d' % (Astar, worst, total + A_s))
ok(Astar <= 60, 'A_* <= 60 holds with the exact cell count (my value %d)' % Astar)

# ----------------------------------------------------------------- 4. composition of C0
lin_comm = set()
for V in LIN:
    for a, b in itertools.combinations(sorted(V), 2):
        lin_comm.add((a, b, b) if (a, b, b) in C0set else (b, a, a))
used_auth = set()
for d in D['derivations']:
    for mv in d['moves']:
        if mv[0] == 'conj':
            used_auth.add(tuple(mv[2:5]))
        if mv[0] == 'swap':
            used_auth.add((mv[2], mv[3], mv[3]))
centset = set(cent)
print('INFO  C0 triples used by the authors\' derivations: %d; centrality: %d; linear-set commutations: %d (of which %d '
      'already among the previous two); union = %d' % (len(used_auth), len(centset), len(lin_comm),
                                                        len(lin_comm & (used_auth | centset)), len(used_auth | centset | lin_comm)))
ok(len(used_auth | centset | lin_comm) == 76 and len(used_auth - centset) + len(centset) + len(lin_comm - used_auth - centset) == 76,
   'C0 = (derivation triples) u (25 centrality) u (linear-set commutations); counts 32 + 25 + 19 = 76: %d + %d + %d'
   % (len(used_auth - centset), len(centset), len(lin_comm - used_auth - centset)))
extra19 = lin_comm - used_auth - centset
print('INFO  my own derivations use %d C0 triples, %d of them among the 19 added commutation triples'
      % (len(used_C0), len(used_C0 & extra19)))
# can the derivations avoid the 19 added commutations entirely?
C0_saved = set(C0set)
C0set = C0set - extra19
C0byab = {}
for t in C0set:
    C0byab.setdefault((t[0], t[1]), []).append(t)
worst2 = 0
allfound = True
for fam, body, sub, ns in targets:
    seq, fc = (['x', 'z', 'x', 'z', w], 1) if fam == 'Jlink' else front_end(sub)
    cost, moves = dijkstra(seq)
    if cost is None:
        allfound = False
    else:
        worst2 = max(worst2, fc + cost + ns * A_s)
ok(allfound, 'all 29 derivations exist without the 19 added commutation triples (max area %d)' % worst2)
C0set = C0_saved
C0byab = {}
for t in C0:
    C0byab.setdefault((t[0], t[1]), []).append(t)

# ----------------------------------------------------------------- 7. ell_E
def theta_len(word_names):
    return len(fred(''.join(S0[g] if g != 'p' else 'p' for g in word_names)))


rels = []
for g in S0:
    rels.append(('E1', S0[g] + S0[g]))
for a, b, c in C0:
    rels.append(('E3', S0[a] + S0[b] + S0[a] + winv(S0[c])))
for b, c in C1:
    rels.append(('E4', 'p' + S0[b] + 'P' + winv(S0[c])))
for V in LIN:
    rels.append(('E2', ''.join(S0[g] for g in V)))
L_raw = max(len(r) for _, r in rels)
L_red = max(len(fred(r)) for _, r in rels)
arg = max(rels, key=lambda r: len(r[1]))
arg_red = max(rels, key=lambda r: len(fred(r[1])))
print('INFO  ell_E = max |theta(r)|, r in R: %d letters before free reduction (%s), %d after (%s) (paper: 44)'
      % (L_raw, arg[0], L_red, arg_red[0]))
ok(L_red == 44, 'ell_E = 44 as stated in Proposition 10.3(b) [prop:presentation]')
ok(all(trivial(fred(r)) for _, r in rels), 'every theta(r), r in R, is trivial in G_P^+ (R2 input of Proposition 9.4 [prop:hash-models])')

# ----------------------------------------------------------------- 8. negative controls
print('\nNegative controls')
# (a) a false triple is rejected by the model
ok(not trivial(S0['x'] + S0['t'] + S0['x'] + winv(S0['g16'])), 'false C0 triple x t x = txt rejected by the model')
# (b) a nontrivial word has no derivation
c, _ = dijkstra(['x', 'z'])
ok(c is None, 'no derivation of the nontrivial word x z')
c, _ = dijkstra(['g12', 'g19'])
ok(c is None, 'no derivation of the nontrivial word (xzx)(ztz)')
# (c) deleting a C0 triple that the s-lemma needs breaks it
C0set = C0set - {('g1', 'g2', 'g3')}
C0byab = {}
for t in C0set:
    C0byab.setdefault((t[0], t[1]), []).append(t)
seq, fc = front_end(SIG + 'G')
c, _ = dijkstra(seq)
ok(c is None, 's-lemma underivable after deleting the C0 triple (g1, g2, g3)')

print('\n%s' % ('ALL CHECKS PASSED' if not FAILS else 'FAILURES: %d' % len(FAILS)))
sys.exit(1 if FAILS else 0)
