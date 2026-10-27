"""Generate the binary linear system (A, b) of the game of Theorem A (Theorem 10.5 [thm:main]).

The input is the EGamma_0 presentation P of Proposition 10.3 [prop:presentation], read as data from egamma0_P.json. The output is the linear
system that the four steps of Lemma B.1 [lem:gadget] (Slofstra's embedding, with w -> J) build from P:

  Step 1  removes the non-involutive generator p: new involutions f, v with p = fv, and for each C1 relation
          p b p^-1 = c an involution Z[b,c] with the conjugacy relations v b v = Z[b,c] and f Z[b,c] f = c;
  Step 2  makes J a commutator: new involutions t* (written t^* in Lemma B.1 [lem:gadget]) and u, the linear set {w, u}
          with right-hand side 1, and the conjugacy relation t* w t* = u;
  Step 3  makes the conjugacy relations nice: a new involution g* (written g^* in Lemma B.1 [lem:gadget]), and for each generator a
          (other than J) the involutions a', a'', bar(a), the linear sets {a, a', a''} and {a, g*, bar(a)}, and the
          conjugacy relation g* a' g* = a''; for each conjugacy relation a b a = c the involutions s[a,b,c], s'[a,b,c],
          the conjugacy relations bar(a) b' bar(a) = c'' and bar(a) b'' bar(a) = c', and the linear sets {b', c'', s[a,b,c]}
          and {c', b'', s'[a,b,c]};
  Step 4  replaces each nice conjugacy relation a b a = c by seven new variables y1..y7[a,b,c] and the six equations
          a y1 y2 = b y2 y3 = y3 y4 y5 = a y5 y6 = c y6 y7 = y1 y4 y7 = e.

Every linear set becomes one equation; the conjugacy relations of Steps 1-3 all become Step-4 gadgets. Variables are
numbered as in Step 4 of Lemma B.1: the generators of the presentation of Step 2 (those of P in file order, then f, v,
the Z[b,c], t*, u), then all a', all a'', g*, all bar(a), all s and s', then the gadget variables. In the output each
equation lists its variables in the order of its product relator, and its right-hand side b (the exponent of J).

Usage (inside anc/):   python3 -I game_Ab_generate.py .      writes game_Ab.json and prints the log
"""
import hashlib
import json
import os
import sys

DIR = sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(DIR, 'egamma0_P.json')
raw = open(SRC, 'rb').read()
P = json.loads(raw)
SHA = hashlib.sha256(raw).hexdigest()

S0 = list(P['S0'])                         # involutive generators, in file order
assert P['S1'] == ['p']
W = P['w']
C0 = [tuple(t) for t in P['C0']]           # (a, b, c): a b a = c
C1 = [tuple(t) for t in P['C1']]           # (b, c): p b p^-1 = c
LIN = [list(V) for V in P['LIN']]          # linear sets, product taken in the listed order

variables = []                              # records {"name", "step", "role"}
index = {}


def new_var(name, step, role):
    assert name not in index, name
    index[name] = len(variables)
    variables.append({'name': name, 'step': step, 'role': role})
    return name


equations = []                              # records {"vars": [names], "b": 0/1, "source": str}


def new_eq(names, b, source):
    assert len(set(names)) == len(names)
    equations.append({'vars': list(names), 'b': b, 'source': source})


# ---------------------------------------------------------------- Step 1: remove p = f v
for a in S0:
    new_var(a, 0, ['gen', a])
new_var('f', 1, ['f'])
new_var('v', 1, ['v'])
conj = list(C0)                             # conjugacy triples of the presentation after Step 2
for (b, c) in C1:
    z = new_var('Z[%s,%s]' % (b, c), 1, ['Z', b, c])
    conj.append(('v', b, z))
    conj.append(('f', z, c))
lin = [(V, 0, 'linear set of P') for V in LIN]

# ---------------------------------------------------------------- Step 2: J = [t*, w]
new_var('t*', 2, ['t*'])
new_var('u', 2, ['u'])
lin.append(([W, 'u'], 1, 'Step 2: {w,u} with right-hand side 1'))
conj.append(('t*', W, 'u'))
T = [r['name'] for r in variables]          # generators of the presentation of Step 2, J excluded
assert len(T) == 40, len(T)
assert len(conj) == 97 and len(lin) == 9

# ---------------------------------------------------------------- Step 3: nice conjugacy relations
for a in T:
    new_var(a + "'", 3, ['prime', a])
for a in T:
    new_var(a + "''", 3, ['dprime', a])
new_var('g*', 3, ['g*'])
for a in T:
    new_var('bar(%s)' % a, 3, ['bar', a])
for (a, b, c) in conj:
    new_var('s[%s,%s,%s]' % (a, b, c), 3, ['s', a, b, c])
    new_var("s'[%s,%s,%s]" % (a, b, c), 3, ["s'", a, b, c])
nice = []
for a in T:
    lin.append(([a, a + "'", a + "''"], 0, "Step 3: {a,a',a''}"))
    lin.append(([a, 'g*', 'bar(%s)' % a], 0, 'Step 3: {a,g,bar a}'))
    nice.append(('g*', a + "'", a + "''"))
for (a, b, c) in conj:
    s1 = 's[%s,%s,%s]' % (a, b, c)
    s2 = "s'[%s,%s,%s]" % (a, b, c)
    nice.append(('bar(%s)' % a, b + "'", c + "''"))
    nice.append(('bar(%s)' % a, b + "''", c + "'"))
    lin.append(([b + "'", c + "''", s1], 0, "Step 3: {b',c'',s}"))
    lin.append(([c + "'", b + "''", s2], 0, "Step 3: {c',b'',s'}"))
assert len(nice) == 234 and len(lin) == 283

# ---------------------------------------------------------------- Step 4: six equations per nice relation
for V, b, source in lin:
    new_eq(V, b, source)
for (a, b, c) in nice:
    key = '[%s,%s,%s]' % (a, b, c)
    y = [new_var('y%d%s' % (k, key), 4, ['y', k, a, b, c]) for k in range(1, 8)]
    src = 'Step 4: gadget of %s %s %s = %s' % (a, b, a, c)
    new_eq([a, y[0], y[1]], 0, src)
    new_eq([b, y[1], y[2]], 0, src)
    new_eq([y[2], y[3], y[4]], 0, src)
    new_eq([a, y[4], y[5]], 0, src)
    new_eq([c, y[5], y[6]], 0, src)
    new_eq([y[0], y[3], y[6]], 0, src)

n, m = len(variables), len(equations)
s = max(len(e['vars']) for e in equations)
out = {
    'description': 'The binary linear system (A, b) of the game of Theorem A, generated from egamma0_P.json by the four '
                   'steps of Lemma B.1 [lem:gadget]. Equation i says that the sum over F_2 of its variables equals b_i; in the solution '
                   'group its product relator is J^{b_i} times the product of its variables in the listed order.',
    'source': 'egamma0_P.json',
    'source_sha256': SHA,
    'n': n, 'm': m, 's': s,
    'variables': variables,
    'equations': [{'vars': [index[x] for x in e['vars']], 'b': e['b'], 'source': e['source']} for e in equations],
}
text = '{\n' + ',\n'.join('"%s": %s' % (k, json.dumps(out[k])) for k in out if k not in ('variables', 'equations'))
for k in ('variables', 'equations'):
    text += ',\n"%s": [\n' % k + ',\n'.join(json.dumps(r) for r in out[k]) + '\n]'
text += '\n}\n'
assert json.loads(text) == out
open(os.path.join(DIR, 'game_Ab.json'), 'w', encoding='utf-8', newline='\n').write(text)

# ---------------------------------------------------------------- log
print('input  egamma0_P.json  sha256 %s' % SHA)
print('P: |S0| = %d, S1 = {p}, |C0| = %d, |C1| = %d, %d linear sets' % (len(S0), len(C0), len(C1), len(LIN)))
steps = {}
for r in variables:
    steps[r['step']] = steps.get(r['step'], 0) + 1
print('variables by step: P %d, Step 1 %d, Step 2 %d, Step 3 %d, Step 4 %d' % tuple(steps.get(k, 0) for k in range(5)))
print('generators after Step 2 (J excluded): %d; conjugacy relations after Step 2: %d; nice relations after Step 3: %d'
      % (len(T), len(conj), len(nice)))
print('equations: %d linear sets + 6 x %d gadget equations = %d' % (len(lin), len(nice), m))
sizes = {}
for e in equations:
    sizes[len(e['vars'])] = sizes.get(len(e['vars']), 0) + 1
print('n = %d variables (J excluded), m = %d equations, s = %d; equations by size %s'
      % (n, m, s, ', '.join('%d: %d' % (k, sizes[k]) for k in sorted(sizes))))
print('right-hand sides: %d equations with b = 1: %s' % (sum(e['b'] for e in equations),
                                                         [' + '.join(e['vars']) for e in equations if e['b']]))
increasing = sum(1 for e in equations if [index[x] for x in e['vars']] == sorted(index[x] for x in e['vars']))
print('equations whose product order is increasing in the variable numbering: %d of %d' % (increasing, m))
print('wrote game_Ab.json')
