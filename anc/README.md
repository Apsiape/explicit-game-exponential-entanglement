# Ancillary files

Ancillary files for *An explicit nonlocal game of quantum value one that needs exponential entanglement*
(Nidhal Mghirbi and Seth Douglas, October 2026). Appendix C of the paper describes them in full.

All programs need Python 3. The programs in this directory need nothing else. Only `pauli_sector_numeric.py`,
`sv_balanced_lift.py` and `numerics/analytic_checks.py` need `numpy`, and the last also needs `scipy`. Run every program from inside
this directory as `python3 -I <program> <arguments>`. Each one exits with status 0 exactly when all its checks
pass. The recorded output of every program is in its `.log` file.

## Machine checks of finite statements (Appendix C)

These checks back the only four statements of the paper that depend on a computation. Each statement is
checked by at least two programs that share no code; the table says exactly what each program establishes.

| Statement | Programs (no shared code between rows of the same statement) | Log |
|---|---|---|
| (C1) The 27 words of the certificate R_P are trivial in G_P | `check_pauli_lamps.py relators_pauli.txt` | `run.log` |
| | `independent_check.py .` | `independent_check.log` |
| | `area_check.py .` (evaluates R_P a third time) | `area_check.log` |
| (C2) validity: the relations of P hold in G_P^+ under the defining words | `egamma0_certificate.py verify` (imports the model of `check_pauli_lamps.py`) | `egamma0_verify.log` |
| | `independent_check.py .` | `independent_check.log` |
| | `area_check.py .` | `area_check.log` |
| (C2) derivability: the 29 derivations reduce their words to the empty word using only relations of P | `egamma0_certificate.py verify` replays them; its own count is not a cell count, and it does not check the `area_bound` labels, which no program uses | `egamma0_verify.log` |
| | `independent_check.py .` re-justifies every move; its generous count gives area at most 335 | `independent_check.log` |
| | `area_check.py .` searches afresh and replays the recorded moves | `area_check.log` |
| | `area_xverify.py .` writes each derivation out as explicit conjugates of relators and checks them by free reduction | `area_xverify.log` |
| (C2) the cap: each of the 29 words has area at most 60 | `area_check.py .` (exact cell count, search and replay) | `area_check.log` |
| | `area_xverify.py .` (explicit certificates; rejects any word with more than 60 factors) | `area_xverify.log` |
| (C3) The linear system (A, b) of the game is the output of the gadget lemma for P | `game_Ab_generate.py <dir>` writes `game_Ab.json`; it transforms its input and does not validate it | `game_Ab_generate.log` |
| | `game_Ab_check.py .` re-derives the system on its own and compares | `game_Ab_check.log` |
| (C4) The area constant A_0 = 42 of the gadget lemma (Remark B.2): every relator of P, and the word [x_w, x_{t*}]J, has an explicit area certificate in the solution group with at most 42 factors | `a0/a0_check.py ..` (run inside `a0/`; rejects any certificate with more than 42 factors; `--negctl` runs nine negative controls; `--dump a0_certificates.json` writes the certificates) | `a0/a0_check.log` |
| | `a0/a0_xverify.py .. a0_certificates.json` re-checks the dumped certificates with its own code. Before building any word it validates every factor against the game: the relator key has its exact form and length, its indices are integers (not booleans) naming a variable, an equation, or two distinct variables of one equation, the sign is +1 or -1, and every conjugator letter is a nonzero integer of absolute value at most n+1 (the letters x_1, ..., x_n, J). It then rebuilds every factor from the game, checks each product by free reduction, and separately requires at most 42 factors; `--negctl` runs eight negative controls, four of which only this validation rejects | `a0/a0_xverify.log` |

Every checking program runs negative controls; the generator `game_Ab_generate.py` does not, since it only
transforms its input. `check_pauli_lamps.py relators_pauli_CORRUPTED.txt` must fail (exit status 1), and its
output is in `negative_control.log`. `egamma0_certificate.py negctl` must reject four corrupted presentations, and
its output is in `egamma0_negctl.log`. `area_xverify.py . --negctl` must reject eight corruptions, among them a
valid certificate padded beyond 60 factors, which only the cap rejects. `egamma0_certificate.py build` rebuilds
`egamma0_P.json`, and its output is in `egamma0_build.log`.

Data files:
- `relators_pauli.txt` holds the 27 words of R_P.
- `egamma0_P.json` holds the presentation P:
  - the defining words of its 26 involutive generators;
  - the sets C_0 and C_1;
  - the 8 linear sets;
  - the 29 derivations.
- `game_Ab.json` holds the game: 1993 variables, each with its role, and 1687 equations with their right-hand sides.

## Numerical sanity tests (no proof depends on them)

- `pauli_sector_numeric.py` runs a flat qubit count on random near-Pauli instances. It writes no log.
- `numerics/analytic_checks.py [count|rounding|return|K|all]` attacks four analytic statements of the paper. It uses
  random and optimised instances, with flat, full-rank, low-rank, skewed and pure states. The four statements are:
  - the qubit count in a state (Theorem 4.1, parts (i)–(iii));
  - the rounding lemma (Lemma 3.6);
  - the sequential-measurement lemma and the loss bound of the return theorem (Lemma 5.3 and Theorem 5.4), on
    perturbed models of the magic square game. This test includes a negative control showing that the state
    commutators cannot be dropped.
  - the bound d ≥ 1/(29e) for the Slofstra–Vidick group K (Theorem 11.9).

  Its output is in `numerics/analytic_checks.log`. No inequality was violated, and the smallest slack on each line
  is recorded.
- `sv_balanced_lift.py` checks the balanced lift of Lemma 11.13 for the models of Example 11.11 with m ≤ 8: the
  reversal tau X tau = X^-1, the residuals of every relator after each step, J -> -I in dimension 8d, and the
  defects of all 2373 relators of the solution group so obtained. As a negative control it builds the literal
  lifts of Slofstra's Proposition 4.8 and confirms the rank obstruction ||T W T^* + W||_f^2 >= 2. Its output is in
  `sv_balanced_lift.log`.

## Reproducing everything

```sh
python3 -I check_pauli_lamps.py relators_pauli.txt
python3 -I check_pauli_lamps.py relators_pauli_CORRUPTED.txt   # expected to fail
python3 -I egamma0_certificate.py verify
python3 -I egamma0_certificate.py negctl
python3 -I independent_check.py .
python3 -I area_check.py .
python3 -I area_xverify.py . && python3 -I area_xverify.py . --negctl
mkdir -p /tmp/regen && cp egamma0_P.json /tmp/regen/ && python3 -I game_Ab_generate.py /tmp/regen && cmp /tmp/regen/game_Ab.json game_Ab.json
python3 -I game_Ab_check.py .
(cd a0 && python3 -I a0_check.py .. && python3 -I a0_check.py .. --negctl && python3 -I a0_xverify.py .. a0_certificates.json && python3 -I a0_xverify.py .. a0_certificates.json --negctl)
python3 -I numerics/analytic_checks.py all
python3 -I sv_balanced_lift.py
```

On a laptop each program takes at most a few seconds, except `numerics/analytic_checks.py all`, which takes a few minutes.
