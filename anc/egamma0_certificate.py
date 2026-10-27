#!/usr/bin/env python3
"""Build and verify an EXTENDED HOMOGENEOUS-LINEAR-PLUS-CONJUGACY (EGamma_0) presentation P
(Slofstra arXiv:1703.08618 Def 4.7) with ONE non-involutive generator p, together with a homomorphism
P -> G_P^+ = G_P x| <iota>, iota the swap of rays 2 and 3, such that
  (R1) the involutive generator w ( -> J = (xz)^2 ) commutes with every generator of P,
  (R2) every relation of P holds in G_P^+ (exact evaluation in the faithful model),
  (R3) every one of the 27 certificate words R_P (with q := iota p iota) is a consequence of the relations of P,
       with an explicit derivation whose length (area bound) is printed.
The presentation is Proposition 10.3 [prop:presentation] of the paper; it is listed in Section C.5 [cert:presentation].
The search for the derivations tries many candidate involutions; P keeps only those that occur on the returned
derivations, numbered g1, g2, ... in the order in which the search met them.
Run:   python3 -I egamma0_certificate.py build      # rebuilds P and derivations, compares with egamma0_P.json
       python3 -I egamma0_certificate.py verify [file]   # independent replay check (default egamma0_P.json)
       python3 -I egamma0_certificate.py negctl     # corrupts the certificate in 4 ways; each must be rejected
Exit status 0 iff the requested action succeeds.
"""
import heapq
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.dont_write_bytecode = True
sys.path.insert(0, HERE)  # import the model from the sibling checker (same directory, our own file)
import check_pauli_lamps as M  # noqa: E402

# ---- extend the model by iota (swap rays 2 and 3; linear, fixes 0, preserves heights) ----
def i_pt(y):
    r, h = y
    return {1: (1, h), 2: (3, h), 3: (2, h)}[r]

M.PT['i'] = i_pt
M.PT['I'] = i_pt
M.INV['i'] = 'I'
M.INV['I'] = 'i'
M.INV['g'] = 'G'   # g = the involutive generator 'sigma' (the transposition s = [p,q]); G = its inverse letter
M.INV['G'] = 'g'
S_WORD = M.free_reduce(list('pipiPIPI'))  # s = [p,q] with q = i p i

def expand_tokens(body, use_sigma):
    w = []
    for tok in body.split():
        inv = tok.endswith('^-1')
        base = tok[:-3] if inv else tok
        if use_sigma and base == 's':
            piece = ['g']
        elif use_sigma and base == 'B':
            piece = ['p', 'g', 'P']
        elif base in M.ABBR:
            piece = M.ABBR[base]
        else:
            piece = [base]
        w += M.inverse(piece) if inv else piece
    return M.free_reduce(expand_q(w))

def subst_sigma(w):
    out = []
    for c in w:
        if c == 'g':
            out += S_WORD
        elif c == 'G':
            out += M.inverse(S_WORD)
        else:
            out.append(c)
    return M.free_reduce(out)

def expand_q(word):
    out = []
    for c in word:
        if c == 'q':
            out += ['i', 'p', 'i']
        elif c == 'Q':
            out += ['I', 'P', 'I']   # exact free-group inverse of i p i
        else:
            out.append(c)
    return M.free_reduce(out)

def is_id(w):
    return M.is_identity(M.free_reduce(list(w)))

INVOL_BASE = ['i', 't', 'd', 'x', 'z']   # base involutive generators (upper case = inverse letter)

class Pres:
    """While the presentation is built, every involution that the search of reduce_seq meets is given a provisional
    name g<k> (k counts all of them, in order of creation), so that the search can compare states.  Only the
    generators that occur on a returned derivation path (its resolved sequence, its moves and its C1 chains) are
    marked as used; finish() discards the others and renumbers the used ones g1, g2, ... in their order of creation."""
    def __init__(self):
        self.defs = {g: [g] for g in INVOL_BASE}   # generator met so far -> defining word in base letters
        self.used = set(INVOL_BASE)                # generators that occur on a returned derivation path
        self.C0 = set()    # (a,b,c): a b a = c
        self.C1 = set()    # (b,c):   p b p^-1 = c
        self.LIN = set()   # frozenset: pairwise commuting, product 1
        self.counter = 0

    def word(self, g):
        return list(self.defs[g])

    def find_or_create(self, w):
        w = M.free_reduce(list(w))
        if not hasattr(self, '_fc'):
            self._fc = {}
        if tuple(w) in self._fc:
            return self._fc[tuple(w)]
        g = self._find_or_create(w)
        self._fc[tuple(w)] = g
        return g

    def _find_or_create(self, w):
        assert is_id(w + w), 'not an involution'
        for g, d in self.defs.items():
            if is_id(w + M.inverse(d)):
                return g
        self.counter += 1
        g = 'g%d' % self.counter
        self.defs[g] = w
        return g

    def commute(self, a, b):
        key = (a, b) if a < b else (b, a)
        if not hasattr(self, '_cc'):
            self._cc = {}
        if key not in self._cc:
            A, B = self.word(a), self.word(b)
            self._cc[key] = is_id(A + B + M.inverse(A) + M.inverse(B))
        return self._cc[key]

    def conj_p(self, n, g):
        """resolve p^n g p^-n to a generator via C1 triples; returns (gen, cost)."""
        cur = g
        self.used.add(cur)
        for _ in range(abs(n)):
            if n > 0:
                nxt = self.find_or_create(['p'] + self.word(cur) + ['P'])
                self.C1.add((cur, nxt))
            else:
                nxt = self.find_or_create(['P'] + self.word(cur) + ['p'])
                self.C1.add((nxt, cur))
            cur = nxt
            self.used.add(cur)
        return cur, abs(n)

    def finish(self):
        """Discard the generators that lie on no returned derivation path and renumber the others g1, g2, ...
        in their order of creation.  Returns the list of discarded provisional names and the renaming map."""
        dropped = [g for g in self.defs if g not in self.used]
        assert not any(g in t for t in self.C0 for g in dropped) and not any(g in t for t in self.C1 for g in dropped)
        assert not any(g in s for s in self.LIN for g in dropped)
        ren, k = {}, 0
        for g in self.defs:
            if g in self.used:
                if g.startswith('g') and g[1:].isdigit():
                    k += 1
                    ren[g] = 'g%d' % k
                else:
                    ren[g] = g
        self.defs = {ren[g]: d for g, d in self.defs.items() if g in ren}
        self.C0 = set(tuple(ren[x] for x in t) for t in self.C0)
        self.C1 = set(tuple(ren[x] for x in t) for t in self.C1)
        self.LIN = set(frozenset(ren[x] for x in s) for s in self.LIN)
        self._fc, self._cc = {}, {}
        return dropped, ren

def decompose(w):
    """w (base letters) with p-exponent sum 0 -> list of (n_k, g_k, inverted?) with
    w = prod_k p^{n_k} g_k^{+-1} p^{-n_k} freely."""
    n = 0
    out = []
    for c in w:
        if c == 'p':
            n += 1
        elif c == 'P':
            n -= 1
        elif c in 'gG':
            out.append((n, 'sigma', c == 'G'))
        else:
            out.append((n, c.lower(), c.isupper()))
    assert n == 0, 'p-exponent sum must vanish'
    return out

def reduce_seq(P, seq, max_expand=200000):
    """best-first search for a derivation of seq (gens, product = 1 in G_P^+) to the empty word using
    moves: cancel aa; aba -> c (C0); swap commuting ab (C0 (a,b,b)); delete a commuting block with
    product 1 (LIN).  Returns list of moves."""
    start = tuple(seq)
    heap = [(len(start), 0, start, [])]
    seen = {start}
    expand = 0
    while heap:
        _, cost, st, moves = heapq.heappop(heap)
        if not st:
            return moves
        expand += 1
        if expand > max_expand:
            break
        cand = []
        L = len(st)
        for j in range(L - 1):
            a, b = st[j], st[j + 1]
            if a == b:
                cand.append((st[:j] + st[j + 2:], ('cancel', j, a)))
        for j in range(L - 2):
            a, b, a2 = st[j], st[j + 1], st[j + 2]
            if a == a2 and a != b:
                c = P.find_or_create(P.word(a) + P.word(b) + P.word(a))
                cand.append((st[:j] + (c,) + st[j + 3:], ('conj', j, a, b, c)))
        for j in range(L - 1):
            a, b = st[j], st[j + 1]
            if a != b and P.commute(a, b):
                cand.append((st[:j] + (b, a) + st[j + 2:], ('swap', j, a, b)))
                e = P.find_or_create(P.word(a) + P.word(b))
                if e not in (a, b):
                    cand.append((st[:j] + (e,) + st[j + 2:], ('merge', j, a, b, e)))
        for j in range(L):
            for k in range(j + 3, min(L, j + 6) + 1):
                blk = st[j:k]
                if len(set(blk)) == len(blk) and all(P.commute(u, v) for u in blk for v in blk if u < v):
                    wd = []
                    for g in blk:
                        wd += P.word(g)
                    if is_id(wd):
                        cand.append((st[:j] + st[k:], ('lin', j, blk)))
        for nst, mv in cand:
            if nst not in seen:
                seen.add(nst)
                heapq.heappush(heap, (len(nst), cost + 1, nst, moves + [mv]))
    raise RuntimeError('no derivation found for %r' % (seq,))

def register_move(P, mv):
    """record the relation that a move of a returned derivation uses, and mark its generators as used."""
    P.used.update(mv[2] if mv[0] == 'lin' else mv[2:])
    if mv[0] == 'conj':
        _, _, a, b, c = mv
        P.C0.add((a, b, c))
    elif mv[0] == 'swap':
        _, _, a, b = mv
        P.C0.add((a, b, b))
    elif mv[0] == 'lin':
        P.LIN.add(frozenset(mv[2]))
    elif mv[0] == 'merge':
        _, _, a, b, e = mv
        P.LIN.add(frozenset((a, b, e)))

def derive_word(P, w2):
    parts = decompose(w2)
    seq = []
    cost = 0
    for n, g, inv in parts:
        gen, c = P.conj_p(n, g)
        seq.append(gen)
        cost += 2 * c + (1 if inv else 0)
    P.used.update(seq)
    moves = reduce_seq(P, seq)
    for mv in moves:
        register_move(P, mv)
    return seq, moves, cost + len(moves)

def mvlist(moves):
    return [list(m) if m[0] != 'lin' else ['lin', m[1], list(m[2])] for m in moves]

def build():
    P = Pres()
    P.defs['sigma'] = list(S_WORD)
    assert is_id(S_WORD + S_WORD)
    rels = M.load(os.path.join(HERE, 'relators_pauli.txt'))
    derivs = []
    total = 0
    # s-lemma: (s-word) sigma^-1 = 1
    seqL, movesL, costL = derive_word(P, M.free_reduce(S_WORD + ['G']))
    derivs.append({'family': 'slemma', 'word': '[p,q] sigma^-1', 'seq': seqL, 'moves': mvlist(movesL), 'area_bound': costL})
    print('  derived s-lemma  [p, i p i] = sigma, area <= %d' % costL)
    for fam, body, w in rels:
        w2 = expand_tokens(body, True)
        assert subst_sigma(w2) == expand_q(w), 'sigma substitution mismatch'
        nsig = sum(1 for c in w2 if c in 'gG')
        seq, moves, cost = derive_word(P, w2)
        cost += nsig * costL
        total += cost
        derivs.append({'family': fam, 'word': body, 'seq': seq, 'moves': mvlist(moves), 'area_bound': cost})
        print('  derived %s %-40s resolved length %2d, area <= %d' % (fam, body, len(seq), cost))
    # w and its link to (xz)^2 :  x z x z w = 1
    w = P.find_or_create(list('xzxz'))
    seqJ = ['x', 'z', 'x', 'z', w]
    P.used.update(seqJ)
    movesJ = reduce_seq(P, seqJ)
    for mv in movesJ:
        register_move(P, mv)
    derivs.append({'family': 'Jlink', 'word': '(xz)^2 w^-1', 'expanded': 'xzxz' + '+' + w, 'seq': seqJ,
                   'moves': [list(m) if m[0] != 'lin' else ['lin', m[1], list(m[2])] for m in movesJ],
                   'area_bound': len(movesJ) + 1})
    # (R1) centrality of w: C0 (g, w, w) for every generator on a derivation path, C1 (w, w)
    nC0_before = len(P.C0)
    for g in list(P.defs):
        if g != w and g in P.used:
            assert P.commute(g, w)
            P.C0.add((g, w, w))
    P.C1.add((w, w))
    nC0_central = len(P.C0)
    # Slofstra-Vidick's EGamma_0 format lists the pairwise commutation relations inside every
    # linear set explicitly.  Add a C0 triple (a, b, b), i.e. a b a = b, for every pair {a, b} of a linear set
    # not already present in either orientation.  (The derivations do not use them.)
    for s in list(P.LIN):
        for a in sorted(s):
            for b in sorted(s):
                if a < b and (a, b, b) not in P.C0 and (b, a, a) not in P.C0:
                    assert P.commute(a, b)
                    P.C0.add((a, b, b))
    print('C0 composition: %d from derivations, %d centrality triples added, %d linear-set commutation triples added'
          % (nC0_before, nC0_central - nC0_before, len(P.C0) - nC0_central))
    # keep only the generators on the returned derivation paths, renumbered g1, g2, ... in order of creation
    n_met = len(P.defs)
    dropped, ren = P.finish()
    w = ren[w]
    for d in derivs:
        d['seq'] = [ren[g] for g in d['seq']]
        d['moves'] = [[m[0], m[1], [ren[g] for g in m[2]]] if m[0] == 'lin' else m[:2] + [ren[g] for g in m[2:]]
                      for m in d['moves']]
        if 'expanded' in d:
            d['expanded'] = 'xzxz' + '+' + w
    print('the search met %d involutive generators; kept the %d on returned derivation paths and discarded %d (%s)'
          % (n_met, len(P.defs), len(dropped), ' '.join(dropped)))
    # each linear set is listed, and its product taken, in the order in which S0 is listed (Lemma B.1 [lem:gadget])
    pos = {g: k for k, g in enumerate(P.defs)}
    lin = sorted((sorted(s, key=pos.get) for s in P.LIN), key=lambda s: [pos[g] for g in s])
    data = {'S0': {g: ''.join(d) for g, d in P.defs.items()}, 'S1': ['p'], 'w': w,
            'C0': sorted(P.C0), 'C1': sorted(P.C1), 'LIN': lin,
            'derivations': derivs}
    out = os.path.join(HERE, 'egamma0_P.rebuilt.json')
    with open(out, 'w', newline='\n') as fh:
        json.dump(data, fh, indent=1)
    print('built P: |S0| = %d involutive generators, S1 = {p}, |C0| = %d, |C1| = %d, |LIN| = %d; total area bound %d'
          % (len(P.defs), len(P.C0), len(P.C1), len(P.LIN), total))
    return out

# ------------------------------------------------------------------ independent verifier
def verify(path):
    with open(path) as fh:
        D = json.load(fh)
    S0 = {g: list(d) for g, d in D['S0'].items()}
    fails = []
    def ok(c, m):
        if not c:
            fails.append(m)
    def W(g):
        return S0[g]
    allowed = set('pPiItTdDxXzZ')
    for g, d in S0.items():
        ok(set(d) <= allowed and 'q' not in d, 'bad letters in %s' % g)
        ok(is_id(d + d), 'S0 generator %s is not an involution in G_P^+' % g)
    for g in INVOL_BASE:
        ok(S0.get(g) == [g], 'base generator %s missing or redefined' % g)
    C0 = set(tuple(x) for x in D['C0'])
    C1 = set(tuple(x) for x in D['C1'])
    LIN = set(frozenset(x) for x in D['LIN'])
    # (R2) every relation true in G_P^+
    for a, b, c in sorted(C0):
        ok(is_id(W(a) + W(b) + W(a) + M.inverse(W(c))), 'C0 %s %s %s false' % (a, b, c))
    for b, c in sorted(C1):
        ok(is_id(['p'] + W(b) + ['P'] + M.inverse(W(c))), 'C1 %s %s false' % (b, c))
    for s in sorted(LIN, key=sorted):
        s = sorted(s)
        wd = []
        for g in s:
            wd += W(g)
        ok(is_id(wd), 'LIN product %s false' % s)
        for u in s:
            for v in s:
                if u < v:
                    ok(is_id(W(u) + W(v) + M.inverse(W(u)) + M.inverse(W(v))), 'LIN %s: %s,%s do not commute' % (s, u, v))
                    ok((u, v, v) in C0 or (v, u, u) in C0,
                       'LIN %s: commutation of %s,%s not listed as a C0 relation (SV18 Sec 6 format)' % (s, u, v))
    # (R1) w central: relations present
    w = D['w']
    ok(is_id(W(w) + M.inverse(list('xzxz'))), 'w is not (xz)^2')
    for g in S0:
        if g != w:
            ok((g, w, w) in C0, 'centrality triple (%s,w,w) missing' % g)
    ok((w, w) in C1, 'centrality C1 (w,w) missing')
    # (R3) replay derivations
    rels = M.load(os.path.join(HERE, 'relators_pauli.txt'))
    want = [('slemma', '[p,q] sigma^-1')] + [(fam, body) for fam, body, _ in rels] + [('Jlink', '(xz)^2 w^-1')]
    ok(S0.get('sigma') == S_WORD, 'sigma must be defined as [p, i p i]')
    got = [(d['family'], d['word']) for d in D['derivations']]
    ok(want == got, 'derivation list does not match the 27 certificate words + Jlink')
    wordmap = {(fam, body): w_ for fam, body, w_ in rels}
    for d in D['derivations']:
        key = (d['family'], d['word'])
        seq = list(d['seq'])
        if key in wordmap or key[0] == 'slemma':
            if key[0] == 'slemma':
                w2 = M.free_reduce(S_WORD + ['G'])
            else:
                w2 = expand_tokens(key[1], True)
                ok(subst_sigma(w2) == expand_q(wordmap[key]), 'sigma substitution mismatch in %s' % (key,))
            parts = decompose(w2)
            # free-group identity  w2 = prod_k p^n_k g_k^(+-1) p^-n_k  (checked, not assumed)
            prod = []
            for n, g, inv in parts:
                letter = {'sigma': 'g'}.get(g, g)
                letter = M.INV[letter] if inv else letter
                prod += ['p'] * n + ['P'] * (-n) + [letter] + ['P'] * n + ['p'] * (-n)
            ok(M.free_reduce(prod) == w2, 'factorization into p-conjugates is not a free identity for %s' % (key,))
            ok(len(parts) == len(seq), 'decomposition length mismatch for %s' % (key,))
            for (n, g, inv), r in zip(parts, seq):
                cur = g
                for _ in range(abs(n)):
                    if n > 0:
                        nxt = [c for (b, c) in C1 if b == cur]
                    else:
                        nxt = [b for (b, c) in C1 if c == cur]
                    if not nxt:
                        ok(False, 'C1 chain broken at %s in %s' % (cur, key))
                        break
                    # choose the one that is the true conjugate (C1 may contain several images only if equal elements)
                    cur = nxt[0]
                ok(cur == r, 'resolved generator mismatch in %s' % (key,))
        else:
            ok(seq[:4] == ['x', 'z', 'x', 'z'] and seq[4] == w, 'Jlink sequence wrong')
        st = list(seq)
        for mv in d['moves']:
            kind, j = mv[0], mv[1]
            if kind == 'cancel':
                ok(j + 1 < len(st) and st[j] == st[j + 1], 'bad cancel in %s' % (key,))
                st = st[:j] + st[j + 2:]
            elif kind == 'conj':
                a, b, c = mv[2], mv[3], mv[4]
                ok(st[j:j + 3] == [a, b, a] and (a, b, c) in C0, 'bad conj move in %s' % (key,))
                st = st[:j] + [c] + st[j + 3:]
            elif kind == 'swap':
                a, b = mv[2], mv[3]
                ok(st[j:j + 2] == [a, b] and ((a, b, b) in C0), 'bad swap in %s' % (key,))
                st = st[:j] + [b, a] + st[j + 2:]
            elif kind == 'merge':
                a, b, e = mv[2], mv[3], mv[4]
                ok(st[j:j + 2] == [a, b] and len({a, b, e}) == 3 and frozenset((a, b, e)) in LIN,
                   'bad merge in %s' % (key,))
                st = st[:j] + [e] + st[j + 2:]
            elif kind == 'lin':
                blk = mv[2]
                ok(st[j:j + len(blk)] == blk and frozenset(blk) in LIN, 'bad lin move in %s' % (key,))
                st = st[:j] + st[j + len(blk):]
            else:
                ok(False, 'unknown move')
        ok(st == [], 'derivation of %s does not end in the empty word' % (key,))
    # sanity: C1 is a partial injective map (p conjugation is a bijection)
    imgs = {}
    for b, c in sorted(C1):
        ok(imgs.setdefault(b, c) == c, 'C1 not a function at %s' % b)
    if fails:
        print('VERIFY FAILED (%d problems):' % len(fails))
        for m in fails[:20]:
            print('   -', m)
        return False
    print('VERIFY OK: %d S0 generators, |C0| = %d, |C1| = %d, |LIN| = %d; all relations true in G_P^+; w central; '
          '%d derivations replayed' % (len(S0), len(C0), len(C1), len(LIN), len(D['derivations'])))
    return True

def negctl(path):
    with open(path) as fh:
        D = json.load(fh)
    bad = []
    # 1. drop one C0 triple used by a derivation
    D1 = json.loads(json.dumps(D))
    used = None
    for d in D1['derivations']:
        for mv in d['moves']:
            if mv[0] == 'conj':
                used = [mv[2], mv[3], mv[4]]
                break
        if used:
            break
    D1['C0'] = [x for x in D1['C0'] if x != used]
    bad.append(('drop a used C0 triple', D1))
    # 2. falsify a C1 triple
    D2 = json.loads(json.dumps(D))
    b, c = D2['C1'][0]
    D2['C1'][0] = [b, 'x' if c != 'x' else 'z']
    bad.append(('falsify a C1 triple', D2))
    # 3. redefine w as x z (not central, not (xz)^2)
    D3 = json.loads(json.dumps(D))
    D3['S0'][D3['w']] = 'xz'
    bad.append(('redefine w', D3))
    # 4. drop one listed commutation relation of a linear set (the EGamma_0 format needs it)
    D4 = json.loads(json.dumps(D))
    lin0 = sorted(D4['LIN'][0])
    pair = None
    for a in lin0:
        for b in lin0:
            if a < b and pair is None:
                pair = (a, b)
    a, b = pair
    D4['C0'] = [x for x in D4['C0'] if x not in ([a, b, b], [b, a, a])]
    bad.append(('drop a linear-set commutation triple', D4))
    allrej = True
    for name, Dx in bad:
        tmp = os.path.join(HERE, '_negctl_tmp.json')
        with open(tmp, 'w') as fh:
            json.dump(Dx, fh)
        try:
            res = verify(tmp)
        except Exception as e:  # loud failure also counts as rejection
            print('   (exception: %s)' % e)
            res = False
        os.remove(tmp)
        print('negative control "%s": %s' % (name, 'REJECTED (good)' if not res else 'ACCEPTED (BAD)'))
        allrej &= not res
    return allrej

if __name__ == '__main__':
    act = sys.argv[1] if len(sys.argv) > 1 else 'verify'
    if act == 'build':
        p = build()
        same = open(p, 'rb').read() == open(os.path.join(HERE, 'egamma0_P.json'), 'rb').read()
        print('rebuilt file %s byte-identical to egamma0_P.json' % ('is' if same else 'is NOT'))
        os.remove(p)
        sys.exit(0 if verify(os.path.join(HERE, 'egamma0_P.json')) and same else 1)
    elif act == 'verify':
        path = sys.argv[2] if len(sys.argv) > 2 else os.path.join(HERE, 'egamma0_P.json')
        sys.exit(0 if verify(path) else 1)
    elif act == 'negctl':
        sys.exit(0 if negctl(os.path.join(HERE, 'egamma0_P.json')) else 1)
    else:
        print(__doc__)
        sys.exit(2)
