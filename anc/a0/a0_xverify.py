#!/usr/bin/env python3
"""Independent re-verification of the area certificates of the remark labelled rem:A0 in the paper.

Shares no code with a0_check.py. Reads egamma0_P.json and game_Ab.json from the directory given as the first
argument, and the certificates written by `a0_check.py <dir> --dump a0_certificates.json` from the second.
Let n be the number of variables and m the number of equations of the game; the letters are x_1, ..., x_n,
written 1, ..., n, and J, written n+1, with negatives for inverses. Before any word is built, every factor is
validated against the game. Its relator key must be ['sq', j], ['Jc', j], ['com', j, k], ['eq', i] or ['J2'],
of exactly this length, with indices that are integers and not booleans: 0 <= j < n for 'sq' and 'Jc'; for 'com',
0 <= j, k < n, j != k, and x_j, x_k in a common equation; 0 <= i < m for 'eq'; no index for 'J2'. Its sign must be
the integer +1 or -1. Its conjugator must be a list of nonzero integers of absolute value at most n+1. Malformed
input is rejected. Every factor is then rebuilt from the game file (an equation of the file, a square, a
commutator of two variables that share an equation, or a relator involving J), its recorded word must equal the
rebuilt one, and the product of the conjugates is reduced freely and compared with the word Psi(r) built directly
from the presentation. Then every certificate must have at most A_0 = 42 factors. The replay and the cap are
reported separately. Exits 0 exactly when every certificate verifies and has at most 42 factors.

Usage:  python3 -I a0_xverify.py .. a0_certificates.json
        python3 -I a0_xverify.py .. a0_certificates.json --negctl   negative controls; exit 0 exactly when each
                                                                    corrupted dump is rejected, and the four
                                                                    out-of-range factors by the validation
"""
import copy, json, sys

CAP = 42


class Bad(Exception):
    pass


def load(d, dump):
    P = json.load(open(d + '/egamma0_P.json')); G = json.load(open(d + '/game_Ab.json'))
    return P, G, json.load(open(dump))['certificates']


def index_ok(i, size):
    return type(i) is int and 0 <= i < size


def check(P, G, C):
    """Returns the largest number of factors, or raises Bad if some certificate does not replay."""
    V = G['variables']; E = G['equations']; n = len(V); J = n + 1
    ix = {tuple(v['role']): j for j, v in enumerate(V)}
    share = {}
    for e in E:
        for a in e['vars']:
            for b in e['vars']:
                share.setdefault(a, set()).add(b)
    arity = {'sq': 2, 'Jc': 2, 'com': 3, 'eq': 2, 'J2': 1}
    def rel(k):
        if type(k) is not list or not k or type(k[0]) is not str or arity.get(k[0]) != len(k):
            raise Bad('invalid relator key %r: not one of [sq, j], [Jc, j], [com, j, k], [eq, i], [J2]' % (k,))
        if k[0] in ('sq', 'Jc', 'com') and not all(index_ok(j, n) for j in k[1:]):
            raise Bad('invalid relator key %r: variable index not an integer in 0..%d' % (k, n - 1))
        if k[0] == 'eq' and not index_ok(k[1], len(E)):
            raise Bad('invalid relator key %r: equation index not an integer in 0..%d' % (k, len(E) - 1))
        if k[0] == 'sq': return [k[1]+1, k[1]+1]
        if k[0] == 'com':
            if not (k[1] != k[2] and k[2] in share.get(k[1], ())): raise Bad('not a commutator of one equation: %r' % (k,))
            return [k[1]+1, k[2]+1, -(k[1]+1), -(k[2]+1)]
        if k[0] == 'eq':
            e = E[k[1]]; return [J]*e['b'] + [x+1 for x in sorted(e['vars'])]
        if k[0] == 'Jc': return [k[1]+1, J, -(k[1]+1), -J]
        return [J, J]
    def mul(a, b):
        a = list(a)
        for x in b:
            if a and a[-1] == -x: a.pop()
            else: a.append(x)
        return a
    X = lambda g: ix[('gen', g)] + 1
    f, v = ix[('f',)] + 1, ix[('v',)] + 1
    targets = [[X(g), X(g)] for g in P['S0']] + [[X(g) for g in L] for L in P['LIN']] + \
        [mul([], [X(a), X(b), X(a), -X(c)]) for a, b, c in P['C0']] + \
        [mul([], [f, v, X(b), -v, -f, -X(c)]) for b, c in P['C1']] + \
        [[X(P['w']), ix[('t*',)]+1, -X(P['w']), -(ix[('t*',)]+1), J]]
    if len(targets) != len(C): raise Bad('%d certificates for %d words' % (len(C), len(targets)))
    mx = 0
    for t, c in zip(targets, C):
        w = []
        for fa in c['factors']:
            r = rel(fa['relator'])
            if r != fa['word']: raise Bad('factor word differs from the relator it names')
            if type(fa['sign']) is not int or fa['sign'] not in (1, -1): raise Bad('sign %r is not +1 or -1' % (fa['sign'],))
            u = fa['conj']
            if type(u) is not list or not all(type(x) is int and 1 <= abs(x) <= J for x in u):
                raise Bad('invalid conjugator %r: not a list of integers x with 1 <= |x| <= %d' % (u, J))
            ui = [-x for x in reversed(u)]
            w = mul(mul(mul(w, u), r if fa['sign'] == 1 else [-x for x in reversed(r)]), ui)
        if w != t: raise Bad('certificate of %s %s does not reduce to its word' % (c['type'], c['word']))
        mx = max(mx, len(c['factors']))
    return mx


def main():
    d, dump = sys.argv[1], sys.argv[2]
    P, G, C = load(d, dump)
    if len(sys.argv) > 3 and sys.argv[3] == '--negctl':
        return negctl(P, G, C)
    try:
        mx = check(P, G, C)
    except Bad as ex:
        print('FAIL  replay: %s' % ex); return 1
    print('independent re-verification: %d certificates OK, max area %d' % (len(C), mx))
    print('PASS  replay: every factor is a conjugate of a relator of Gamma(A,b) with sign +1 or -1, and each product '
          'reduces freely to its word')
    if mx > CAP:
        print('FAIL  cap: a certificate has %d factors, more than %d' % (mx, CAP)); return 1
    print('PASS  cap: every certificate has at most %d factors (largest %d)' % (CAP, mx))
    return 0


def negctl(P, G, C):
    print('negative controls: each corrupted dump must be rejected')
    ok = True
    try:
        check(P, G, C)
    except Bad:
        print('FAIL  the true dump does not verify, so the negative controls are meaningless'); return 1
    k = next(i for i, c in enumerate(C) if len(c['factors']) == CAP)
    def run(label, C2, cap_only=False, by=None):
        nonlocal ok
        try:
            mx = check(P, G, C2)
            rejected, why = mx > CAP, 'replay accepts it; cap: %d factors' % mx
        except Bad as ex:
            rejected, why = True, str(ex)
        print(('PASS  rejected: ' if rejected else 'FAIL  accepted: ') + label + '  [%s]' % why)
        ok &= rejected and (not cap_only or why.startswith('replay accepts')) and (by is None or why.startswith(by))
    C1 = copy.deepcopy(C); fa = copy.deepcopy(C1[k]['factors'][0])
    C1[k]['factors'] += [fa, dict(fa, sign=-fa['sign'])]
    run('a certificate of %d factors padded to %d by a factor and its inverse' % (CAP, CAP + 2), C1, cap_only=True)
    C2 = copy.deepcopy(C); C2[k]['factors'][0]['sign'] = 2
    run('a factor with sign 2', C2)
    C3 = copy.deepcopy(C); C3[k]['factors'][0]['sign'] = 0
    run('a factor with sign 0', C3)
    C4 = copy.deepcopy(C); del C4[k]['factors'][3]
    run('a certificate with one factor dropped', C4)
    # Factors outside the game. In each control a factor and its inverse are appended to a certificate of one factor;
    # they cancel freely and the certificate stays far below the cap, so only the validation can reject the dump.
    n, m = len(G['variables']), len(G['equations']); J = n + 1
    s = next(i for i, c in enumerate(C) if len(c['factors']) == 1)
    def appended(fa):
        C5 = copy.deepcopy(C); C5[s]['factors'] += [fa, dict(fa, sign=-fa['sign'])]
        return C5
    j = n + 17
    run('a certificate of 1 factor with a factor and its inverse appended that name the square of the variable '
        'index %d, beyond the last index %d' % (j, n - 1),
        appended({'conj': [], 'relator': ['sq', j], 'sign': 1, 'word': [j + 1, j + 1]}), by='invalid relator key')
    run('a certificate of 1 factor with a factor and its inverse appended that name [x_j, J] for the variable '
        'index %d, one past the last' % n,
        appended({'conj': [], 'relator': ['Jc', n], 'sign': 1, 'word': [n + 1, J, -(n + 1), -J]}), by='invalid relator key')
    e = G['equations'][-1]
    run('a certificate of 1 factor with a factor and its inverse appended that name the equation of index -1',
        appended({'conj': [], 'relator': ['eq', -1], 'sign': 1, 'word': [J]*e['b'] + [x+1 for x in sorted(e['vars'])]}),
        by='invalid relator key')
    run('a certificate of 1 factor with a factor and its inverse appended that are conjugated by the letter %d, '
        'outside the letters 1..%d of Gamma(A,b) and their inverses' % (J + 1, J),
        appended(dict(C[s]['factors'][0], conj=[J + 1])), by='invalid conjugator')
    print('ALL NEGATIVE CONTROLS REJECTED' if ok else 'SOME CORRUPTION WAS ACCEPTED')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
