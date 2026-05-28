# Formalizing Bombieri-Vinogradov
A Lean blueprint documenting a formalization of Bombieri-Vinogradov.

## Links
* [Webpage](https://amellendijk.github.io/lean-bombieri-vinogradov/)
* [Blueprint](https://amellendijk.github.io/lean-bombieri-vinogradov/blueprint/)
* [Documentation](https://amellendijk.github.io/lean-bombieri-vinogradov/docs/)
* [Dependency Graph](https://amellendijk.github.io/lean-bombieri-vinogradov/blueprint/dep_graph_document.html)

## Bombieri-Vinogradov
The Bombieri-Vinogradov theorem states that for each fixed $A \geq 0$,

$$\sum_{q \le Q} \max_{y \le x} \max_{a \in (\mathbb{Z}/q\mathbb{Z})^*} \left| \psi(y; q, a) - \frac{y}{\varphi(q)} \right| \ll_A \frac{x}{(\log x)^{A}}$$

uniformly for all $x \ge 2$ and $1 \le Q \le \frac{\sqrt{x}}{(\log x)^{A+3}}$.

This theorem is often described as the "Generalized Riemann Hypothesis on average", because it states that the average deviation $\left| \psi(x; q, a) - \frac{x}{\varphi(q)} \right|$ is at most $x^{1/2}$ modulo log factors, at least for $y$ and $q$ up to around $x^{1/2}. 

## The Project

The main target of this project is the formalization of the Bombieri-Vinogradov theorem, as stated in `BV/MainResults.lean`. 
We assume two axioms, both documented in `BV/Axioms.lean`: 
* The Siegel-Walfisz Theorem
* The Large Sieve Inequality

The large sieve is simple enough to be its own single-person project, and I am interested in adding it to this blueprint when the project nears completion.

Siegel-Waflisz would be a larger project, but it is very much in scope of PNT+. If there is community interest in getting it formalized, I would be very happy to get involved.

This project depends on [Mathlib](https://github.com/leanprover-community/mathlib4) and [PNT+](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd)

## Building the project

1. [Install Lean](https://lean-lang.org/install/)
2. Run `lake exe cache get`
3. Run `lake build`