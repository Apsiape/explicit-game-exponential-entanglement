#!/usr/bin/env python3
"""Independent checker for the Pauli configuration-lamp presentation.  Run inside anc/: python3 -I independent_check.py .

Written from scratch (imports none of the other scripts).  Exact arithmetic only.
 Part A: faithful model of G_P^+ = E_V x| (A x| <iota>), evaluate the 27 R_P words (with q and with q -> iota p iota),
         plus negative controls.
 Part B: the EGamma_0 presentation P (egamma0_P.json): every relation true in the model; w -> J central, J != 1;
         SV18 Sec.6 form check (incl. explicit commutation relations inside linear sets).
 Part C: (R3) derivations: my own front end (abbreviation expansion, q -> i p i, s -> sigma via s-lemma,
         factorisation into p-conjugates, C1 resolution) recomputes the S0-sequence; then every claimed move is
         re-justified by my own test (u + reverse(v) is a cyclic rotation of a relator, S0 letters involutive).
 Part D: negative controls for B and C.
Exit code 0 iff all pass.
"""
import json, os, sys, itertools

FAIL = []
def ok(cond, msg):
    print(("ok    " if cond else "FAIL  ") + msg)
    if not cond:
        FAIL.append(msg)

# ------------------------------------------------------------------ points of Y and permutation letters
def perm_letter(c, y):
    r, h = y
    if c == 'p':
        if r == 1: return (1, h + 1)
        if r == 2: return (1, 1) if h == 1 else (2, h - 1)
        return y
    if c == 'P':
        if r == 1: return (2, 1) if h == 1 else (1, h - 1)
        if r == 2: return (2, h + 1)
        return y
    if c == 'q':
        if r == 1: return (1, h + 1)
        if r == 3: return (1, 1) if h == 1 else (3, h - 1)
        return y
    if c == 'Q':
        if r == 1: return (3, 1) if h == 1 else (1, h - 1)
        if r == 3: return (3, h + 1)
        return y
    if c in 'iI':          # iota: swap rays 2 and 3, height preserving
        return (1, h) if r == 1 else ((3, h) if r == 2 else (2, h))
    raise ValueError(c)

E1 = (1, 1); E2 = (1, 2)
def affine_letter(c, v):
    """v: frozenset of points (a configuration).  returns c(v)."""
    if c in 'pPqQiI':
        return frozenset(perm_letter(c, y) for y in v)
    if c in 'tT':          # translation by e_(1,1)
        return v ^ frozenset([E1])
    if c in 'dD':          # transvection E_{2<-1}: adds e_(1,2) to every configuration containing (1,1)
        return v ^ frozenset([E2]) if E1 in v else v
    raise ValueError(c)

def apply_affine(word, v):
    for c in reversed(word):     # g = l1 l2 ... lk acts as l1(l2(...lk(v)))
        v = affine_letter(c, v)
    return v

ZERO = frozenset()
# E_V element: (s, a, b) with a,b frozensets of sites (sites = configurations)
def e_mul(e1, e2):
    s1, a1, b1 = e1; s2, a2, b2 = e2
    return ((s1 + s2 + len(b1 & a2)) % 2, a1 ^ a2, b1 ^ b2)

def e_act(g, e):
    s, a, b = e
    return (s, frozenset(apply_affine(g, v) for v in a), frozenset(apply_affine(g, v) for v in b))

LAMP = {'x': (0, frozenset([ZERO]), frozenset()), 'X': (0, frozenset([ZERO]), frozenset()),
        'z': (0, frozenset(), frozenset([ZERO])), 'Z': (0, frozenset(), frozenset([ZERO]))}
# x, z are involutions so X = x, Z = z as group elements.

def evaluate(word):
    """word: string over pPqQiItTdDxXzZ (I = iota^-1 = iota).  returns (e, affine word)."""
    e = (0, frozenset(), frozenset()); g = []
    for c in word:
        if c in LAMP:
            e = e_mul(e, e_act(g, LAMP[c]))
        else:
            g.append(c)
    return e, g

def affine_is_id(g):
    if apply_affine(g, ZERO) != ZERO:
        return False
    H = len(g) + 4
    for r in (1, 2, 3):
        for h in range(1, H + 1):
            if apply_affine(g, frozenset([(r, h)])) != frozenset([(r, h)]):
                return False
    return True

def is_identity(word):
    e, g = evaluate(word)
    return e == (0, frozenset(), frozenset()) and affine_is_id(g)

def is_J(word):
    e, g = evaluate(word)
    return e == (1, frozenset(), frozenset()) and affine_is_id(g)

INV = {c: c.swapcase() for c in 'pPqQiItTdDxXzZ'}
def inv(w):
    return ''.join(INV[c] for c in reversed(w))
def freered(w):
    out = []
    for c in w:
        if out and out[-1] == INV[c]:
            out.pop()
        else:
            out.append(c)
    return ''.join(out)

# ------------------------------------------------------------------ Part A: R_P in G_P
ABBR = {'s': 'pqPQ'}
ABBR['B'] = 'p' + ABBR['s'] + 'P'
ABBR['t1'] = 't'; ABBR['t2'] = 'ptP'; ABBR['t3'] = 'pptPP'; ABBR['J'] = 'xzxz'

def expand_tokens(tokens, qsub=False):
    out = ''
    for tok in tokens:
        if tok.endswith('^-1'):
            out += inv(expand_tokens([tok[:-3]], qsub))
            continue
        if tok in ABBR:
            out += expand_tokens(list(ABBR[tok]) if len(ABBR[tok]) > 0 else [], qsub) if tok != 's' else \
                   expand_tokens(list('pqPQ'), qsub)
            continue
        for c in tok:
            if qsub and c == 'q': out += 'ipi'
            elif qsub and c == 'Q': out += 'IPI'
            else: out += c
    return out

def load_RP(path):
    words = []
    for line in open(path):
        line = line.strip()
        if not line or line.startswith('#'): continue
        fam, w = [x.strip() for x in line.split('|')]
        words.append((fam, w))
    return words

def partA(a4):
    print('Part A: R_P evaluated in my own model of G_P^+')
    RP = load_RP(os.path.join(a4, 'relators_pauli.txt'))
    ok(len(RP) == 27, 'R_P has 27 words (%d)' % len(RP))
    for fam, w in RP:
        W = freered(expand_tokens(w.split()))
        Wi = freered(expand_tokens(w.split(), qsub=True))
        ok(is_identity(W) and is_identity(Wi), '%s  %-28s trivial in G_P (len %d) and with q->ipi (len %d)' % (fam, w, len(W), len(Wi)))
    # J central, nontrivial, q = i p i
    ok(is_J('xzxz'), 'J=(xz)^2 is the nontrivial central element (0 ~ J^1)')
    for g in 'pqtdxzi':
        ok(is_identity('xzxz' + g + 'zxzx' + INV[g]), '[J,%s] = 1' % g)
    ok(is_identity('ipiQ'), 'q = iota p iota')
    # Pauli lamps at the 8 sites of the N=3 ladder: (X_u Z_u)^2 = J, distinct sites commute
    T = {1: 't', 2: 'ptP', 3: 'pptPP'}
    sites = []
    for k in range(0, 4):
        for u in itertools.combinations((1, 2, 3), k):
            sites.append(''.join(T[i] for i in u))
    good = all(is_J(Tu + 'xz' + inv(Tu) + Tu + 'xz' + inv(Tu)) for Tu in sites)
    ok(good, '(X_u Z_u)^2 = J at all 8 ladder sites')
    good = True
    for Tu, Tw in itertools.permutations(sites, 2):
        for a, b in itertools.product('xz', repeat=2):
            A = Tu + a + inv(Tu); Bw = Tw + b + inv(Tw)
            good &= is_identity(A + Bw + inv(A) + inv(Bw))
    ok(good, 'distinct ladder sites commute (8*7*4 commutators)')
    # negative controls: words that must NOT be trivial
    neg = ['xzxz', 'xz' + 'XZ', 'xtXT', 'dtDT', 'pqPQ', 'tpTP', 'ptPtpTPT' + 'x', 'xtxTXtXT'[:-1] + 'd',
           'dxDX' + 'z', 'pxPz', 'ipiq']
    for w in neg:
        ok(not is_identity(w), 'negative control rejected: %s' % w)
    ok(not is_identity('ipiQ' + 'ipiQ' + 'tdTD'), 'negative control rejected: corrupted q-substitution word')

# ------------------------------------------------------------------ Part B: the presentation
def gen_word(S0, g):
    return 'p' if g == 'p' else S0[g]

def partB(P):
    print('Part B: the EGamma_0 presentation, relation by relation in my model')
    S0 = P['S0']; w = P['w']
    ok(P['S1'] == ['p'], 'S1 = {p}')
    ok(w in S0, 'w = %s is in S0' % w)
    allgood = True
    for g, word in S0.items():
        allgood &= is_identity(word + word)
    ok(allgood, 'all %d S0 generators are involutions in G_P^+' % len(S0))
    ok(is_J(S0[w]), 'w maps to J (nontrivial central)')
    bad = [t for t in P['C0'] if not is_identity(S0[t[0]] + S0[t[1]] + S0[t[0]] + inv(S0[t[2]]))]
    ok(not bad, 'all %d C0 relations a b a = c hold %s' % (len(P['C0']), bad[:3]))
    bad = [t for t in P['C1'] if not is_identity('p' + S0[t[0]] + 'P' + inv(S0[t[1]]))]
    ok(not bad, 'all %d C1 relations p b p^-1 = c hold %s' % (len(P['C1']), bad[:3]))
    bad = []
    for V in P['LIN']:
        if not is_identity(''.join(S0[g] for g in V)): bad.append(('prod', V))
        for a, b in itertools.combinations(V, 2):
            if not is_identity(S0[a] + S0[b] + inv(S0[a]) + inv(S0[b])): bad.append(('comm', a, b))
    ok(not bad, 'all %d linear relations hold and their members commute %s' % (len(P['LIN']), bad[:3]))
    # centrality relations present (R1)
    C0set = set(tuple(t) for t in P['C0'])
    missing = [g for g in S0 if g != w and (g, w, w) not in C0set]
    ok(not missing, 'centrality triples (g,w,w) present for all g in S0\\{w} %s' % missing[:5])
    ok([w, w] in P['C1'], 'p w p^-1 = w present')
    # SV18 Sec 6 form: each linear set V needs explicit xy=yx relations in R.  Report whether C0 contains them.
    miss = []
    for V in P['LIN']:
        for a, b in itertools.combinations(V, 2):
            if (a, b, b) not in C0set and (b, a, a) not in C0set:
                miss.append((a, b))
    print('INFO  commutation pairs inside linear sets NOT listed explicitly as C0 triples: %d of %d: %s'
          % (len(miss), 3 * len(P['LIN']), miss))
    # they are consequences: a,b,c involutions with abc=1 => ab = c^-1 = c = (ab)^-1 = ba (area <= 6)
    ok(all(len(V) == 3 for V in P['LIN']), 'all linear sets have size 3 (so commutation is derivable, area <= 6)')
    # J central in G_P^+ (also iota)
    return miss

# ------------------------------------------------------------------ Part C: derivations
def relator_cycles(P, extra_comm):
    """relators as cyclic sequences of S0 letters (all S0 letters involutive); C1 handled separately."""
    rels = []
    for g in P['S0']: rels.append((g, g))
    for a, b, c in P['C0']: rels.append((a, b, a, c))
    for V in P['LIN']: rels.append(tuple(V))
    for a, b in extra_comm: rels.append((a, b, a, b))
    cyc = set()
    for r in rels:
        for seq in (r, tuple(reversed(r))):
            for k in range(len(seq)):
                cyc.add(seq[k:] + seq[:k])
    return cyc

def front_end(P, word):
    """returns (seq of S0 letters, number of C1 applications, number of s-substitutions)."""
    C1f = {b: c for b, c in P['C1']}
    C1b = {}
    for b, c in P['C1']:
        C1b.setdefault(c, b)
    toks = word.split()
    # token -> list of items: 'p','P', or ('S0', name).  s -> sigma by the s-lemma, q -> i p i.
    letter_map = {'t': 't', 'T': 't', 'd': 'd', 'D': 'd', 'x': 'x', 'X': 'x', 'z': 'z', 'Z': 'z', 'i': 'i', 'I': 'i'}
    nsub = [0]
    def tok_items(tok):
        if tok.endswith('^-1'):
            it = tok_items(tok[:-3])
            return [('P' if x == 'p' else 'p' if x == 'P' else x) for x in reversed(it)]
        if tok == 's':
            nsub[0] += 1; return [('S0', 'sigma')]
        if tok == 'B': return ['p'] + tok_items('s') + ['P']
        if tok == 't1': return [('S0', 't')]
        if tok == 't2': return ['p', ('S0', 't'), 'P']
        if tok == 't3': return ['p', 'p', ('S0', 't'), 'P', 'P']
        if tok == 'J': return [('S0', c) for c in 'xzxz']
        if tok == '[p,q]': return ['p', ('S0', 'i'), 'p', ('S0', 'i'), 'P', ('S0', 'i'), 'P', ('S0', 'i')]
        if tok == 'sigma': return [('S0', 'sigma')]
        if tok == '(xz)^2': return [('S0', c) for c in 'xzxz']
        if tok == 'w': return [('S0', P['w'])]
        out = []
        for c in tok:
            if c == 'q': out += [('S0', 'i'), 'p', ('S0', 'i')]
            elif c == 'Q': out += [('S0', 'i'), 'P', ('S0', 'i')]
            elif c in 'pP': out.append(c)
            else: out.append(('S0', letter_map[c]))
        return out
    items = []
    for tok in toks:
        items += tok_items(tok)
    n = 0; seq = []; nc1 = 0
    for it in items:
        if it == 'p': n += 1
        elif it == 'P': n -= 1
        else:
            g = it[1]
            if n >= 0:
                for _ in range(n):
                    if g not in C1f: return None, nc1, nsub[0]
                    g = C1f[g]; nc1 += 1
            else:
                for _ in range(-n):
                    if g not in C1b: return None, nc1, nsub[0]
                    g = C1b[g]; nc1 += 1
            seq.append(g)
    if n != 0: return None, nc1, nsub[0]
    return seq, nc1, nsub[0]

def replay(seq, moves, cyc, S0names):
    """apply moves; each move replaces u (at position j) by v; require u + reverse(v) cyclic relator."""
    st = list(seq); cost = 0
    for mv in moves:
        kind, j = mv[0], mv[1]
        if kind == 'cancel':
            u, v = [mv[2], mv[2]], []
        elif kind == 'conj':
            a, b, c = mv[2:5]; u, v = [a, b, a], [c]
        elif kind == 'swap':
            a, b = mv[2:4]; u, v = [a, b], [b, a]
        elif kind == 'merge':
            a, b, e = mv[2:5]; u, v = [a, b], [e]
        elif kind == 'lin':
            u, v = list(mv[2]), []
        else:
            return False, 'unknown move %s' % kind, cost
        if st[j:j + len(u)] != u:
            return False, 'move %s does not match state %s' % (mv, st), cost
        cand = tuple(u + list(reversed(v)))
        if cand not in cyc:
            # allow one extra involution-free step: u v^-1 = relator after cancelling, e.g. swap needs C0 (a,b,b)
            return False, 'move %s not justified by a single relator (word %s)' % (mv, cand), cost
        cost += 1 + len(u) + len(v)          # one relator + involution relators for inverse letters
        st = st[:j] + v + st[j + len(u):]
    return (not st), 'final state %s' % st, cost

def partC(P, extra_comm):
    print('Part C: (R3) derivations re-derived and re-justified')
    cyc = relator_cycles(P, extra_comm)
    cyc_strict = relator_cycles(P, [])
    S0names = set(P['S0'])
    der = P['derivations']
    ok(len(der) == 29, '29 derivations (%d)' % len(der))
    slem_cost = None
    total = 0; used_extra = False
    for D in der:
        if D['family'] == 'slemma':
            seq, nc1, nsub = front_end(P, '[p,q] sigma^-1')
        elif D['family'] == 'Jlink':
            seq, nc1, nsub = front_end(P, '(xz)^2 w')
        else:
            seq, nc1, nsub = front_end(P, D['word'])
        ok(seq == D['seq'], '%-6s %-28s my front end gives their S0 sequence' % (D['family'], D['word']))
        good, msg, cost = replay(seq or [], D['moves'], cyc, S0names)
        good_strict, _, _ = replay(seq or [], D['moves'], cyc_strict, S0names)
        if good and not good_strict: used_extra = True
        c = cost + 2 * nc1 + (slem_cost or 0) * nsub + 2 * len(D['word'])
        if D['family'] == 'slemma': slem_cost = c
        total += c
        ok(good, '       moves replayed to the empty word with my relator test; my area bound %d (theirs %d) %s'
           % (c, D['area_bound'], '' if good else msg))
    print('INFO  derivations needed the added linear-set commutators:', used_extra)
    print('INFO  my generous total area bound for all 29 words: %d' % total)
    return cyc

def partD(P):
    print('Part D: negative controls for the presentation and the derivations')
    import copy
    # (1) a false C0 triple must be caught by the model
    S0 = P['S0']
    a, b, c = 'x', 't', 'g16'
    ok(not is_identity(S0[a] + S0[b] + S0[a] + inv(S0['g16'])), 'false relation x t x = g16 (=txt) rejected by the model')
    ok(is_identity(S0[a] + S0[b] + S0[a] + inv(S0['g15'])), 'sanity: the true relation x t x = g15 is accepted')
    # (2) delete a C0 triple used in a derivation -> replay must fail
    P2 = copy.deepcopy(P)
    P2['C0'] = [t for t in P2['C0'] if t != ['sigma', 'g4', 'g5']]
    cyc2 = relator_cycles(P2, [])
    D = [d for d in P['derivations'] if d['word'] == 's p s P s p s P s p s P'][0]
    good, msg, _ = replay(D['seq'], D['moves'], cyc2, set(S0))
    ok(not good, 'derivation rejected after deleting C0 (sigma,g4,g5)')
    # (3) falsify a C1 entry -> front end must give a different sequence
    P3 = copy.deepcopy(P)
    P3['C1'] = [t if t != ['t', 'g7'] else ['t', 'g11'] for t in P3['C1']]
    seq, _, _ = front_end(P3, 'd t2 D t2^-1')
    ok(seq != ['d', 'g7', 'd', 'g7'], 'front end detects a falsified C1 triple')
    # (4) a non-relator move must be rejected
    good, msg, _ = replay(['x', 'z', 'x', 'z'], [['cancel', 0, 'x']], relator_cycles(P, []), set(S0))
    ok(not good, 'illegal cancel move rejected')
    # (5) a word that is not trivial must not be derivable: (xz)^1 has no derivation (front end + any moves fail)
    good, msg, _ = replay(['x', 'z'], [['conj', 0, 'x', 'z', 'g12']], relator_cycles(P, []), set(S0))
    ok(not good, 'derivation of the nontrivial word x z rejected')

def main():
    if len(sys.argv) < 2:
        sys.exit('usage: python3 -I independent_check.py <dir containing egamma0_P.json>')
    a4 = sys.argv[1]
    partA(a4)
    P = json.load(open(os.path.join(a4, 'egamma0_P.json')))
    miss = partB(P)
    partC(P, miss)
    partD(P)
    print()
    print('ALL CHECKS PASSED' if not FAIL else 'FAILURES: %d' % len(FAIL))
    sys.exit(0 if not FAIL else 1)

if __name__ == '__main__':
    main()
