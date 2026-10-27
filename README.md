# An explicit nonlocal game of quantum value one that needs exponential entanglement

Nidhal Mghirbi and Seth Douglas, October 2026.

[Read the manuscript](paper/main.pdf) · [TeX source](paper/main.tex) · [Ancillary programs](anc/README.md)

Version 1.0.0, October 2026.

How much entanglement does near-optimal play of a two-player nonlocal game require? We give an explicit binary linear system game, with $1687$ equations in $1993$ variables and at most three variables in each equation, whose quantum value is one, and in which every strategy that wins with probability $1-\varepsilon$ needs entanglement entropy $\varepsilon^{-1+o(1)}$, hence local dimension $\exp(\varepsilon^{-1+o(1)})$. The same bound holds for the entanglement of formation of mixed strategies, and a strategy on a maximally entangled state of local dimension $\exp(C\varepsilon^{-1}\log(1/\varepsilon))$ suffices, so the exponent is sharp. For explicit two-player games of quantum value one, the best previous lower bound was polynomial in $1/\varepsilon$. The game comes from a finitely generated, elementary amenable group: a lamplighter whose lamps are Pauli pairs indexed by finite sets of points on the three rays on which Houghton's group acts. Exponentially many of these pairs share one central involution, yet the relation that any two of them commute can be derived from a fixed finite set of relations in a number of steps only quasi-polynomial in the number of points. Two tools may be of independent use. The first counts qubits from approximate Pauli relations measured in an arbitrary state, with the errors of different pairs adding in squares. The second identifies, in both directions and at the natural precision $\sqrt\varepsilon$, the near-optimal strategies of a linear system game with approximate representations of its solution group measured in the players' actual state, so that no power of $\varepsilon$ is lost by passing to a flat state. The same tools give sharp rates for two earlier examples: the CHSH$(n)$ games need $\Theta(\min(n,1/\varepsilon))$ ebits, and the linear system game of Slofstra and Vidick needs local dimension $\Theta(\varepsilon^{-1/2})$.

## Contents

- `paper/main.pdf`: the paper, 90 pages.
- `paper/main.tex`, `paper/sections/`, `paper/refs.bib`: the LaTeX source. Build it from `paper/` with
  `latexmk -pdf main`, or with `pdflatex main && bibtex main && pdflatex main && pdflatex main && pdflatex main`. It needs only standard TeX Live packages, including
  amsmath, mathtools, tikz, cleveref, aliascnt, enumitem, booktabs, longtable and microtype.
- `anc/`: the ancillary programs and data behind the four computational statements (C1)-(C4), and numerical checks of
  analytic statements, among them the balanced lift of Lemma 11.13. See `anc/README.md` and Appendix C of the paper.

## Licensing

The paper and documentation are licensed CC BY 4.0, and the programs in `anc/` MIT or Apache 2.0, at your option. See
[RIGHTS.md](RIGHTS.md).
