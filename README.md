# A counterexample to a conjecture of Cerf on second-order pivots

Yitzchak Shmalo

For an increasing set A in {0,1}^n, R. Cerf (*theta(p_c, Z^d) = 0?*, arXiv:2608.23661, Section 53) considers

    phi_2(A)     = sum over w in A of |P_2^+(A, w)|,
    phi_{2\1}(A) = sum over w in A of |P_2^+(A, w) \ P_1^+(A, w)|,

where P_1^+(A, w) is the set of positive pivots of A at w and P_2^+(A, w) adds the positive pivots at the configurations obtained from w by switching off one occupied coordinate. His Conjecture 53.1 states that every maximizer of either functional contains all configurations with at least n/2 + 1 ones and no configuration with fewer than n/2 - 2 ones.

The paper shows that this fails. For n = h^2 with h divisible by 10 and h > 2,592,000 (for instance n = 10^14) there is an increasing set A with

    2^{-n} phi_{2\1}(A) >= n / 259200 > 10 sqrt(n),

while every increasing set inside the conjectured band has 2^{-n} phi_2 <= 10 sqrt(n). So no maximizer of either functional lies in the band. The set is a random monotone CNF with 2^r clauses of r = h/10 sampled coordinates each, as in Talagrand's construction (Combinatorica 16 (1996)); Section 62 of Cerf's text adapts the same construction to second-order pivots. The proof counts second-order pivots through a graph whose edges are the clauses with exactly two positive coordinates, and handles coordinates repeated within a clause.

## Contents

- `paper/main.tex`, `paper/main.pdf`: the paper.
- `code/checks.py`: exhaustive computation of both functionals, under the literal definition (49.1) and under the occupied-coordinate reading that matches Cerf's tables, over all increasing sets with n <= 5; the clause-graph lemma on all 729 arrays with n = 3, r = 2, M = 3; the exact rational inequalities of the proof for h = 10^7 and h = 2,592,010. Output in `code/checks_out.txt` and `code/checks.json`.
- `lean/Certificate.lean`: the deterministic pair-witness step for arbitrary clause and coordinate types, and the numerical margins at h = 10^7, checked with Lean 4 and Mathlib. The probabilistic estimates are not formalized.

## Running

    cd code
    python checks.py > checks_out.txt

The program uses only the Python standard library and runs in a few seconds. The Lean file compiles inside any Lean 4 project with Mathlib (`lake env lean Certificate.lean`).

## License

Paper: CC BY 4.0. Code: MIT.
