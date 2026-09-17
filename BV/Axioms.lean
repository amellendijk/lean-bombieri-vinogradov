import Mathlib
import Architect

import BV.Chebyshev

open ArithmeticFunction

open scoped Nat

/-- The implied constant in the Sielgel-Walfisz Theorem -/
axiom C_SW (A : ℕ) (C : ℕ) : ℝ

@[blueprint (latexEnv := "assumption") (hasProof := false) (title := /-- Siegel--Walfisz -/) (statement := /--
Let $A, C \in \N$. For all real $x \ge 2$, all $1 \le q \le (\log x)^C$ and all $a \in (\Z/q\Z)^*$,
$$\psi(x; q, a) = \frac{x}{\varphi(q)} + O_{A, C}\!\left(\frac{x}{(\log x)^A}\right).$$
This is the Siegel--Walfisz theorem in the form ``an arbitrary power of $\log$ savings, uniformly for
$q \le (\log x)^C$''. It is taken as an external input (an axiom in Lean, whose implied constant is an
unspecified real number); no proof is given here. Only the cases $C \in \{0, 2C'\}$ are used, see
\Cref{PNT} and \Cref{Delta_onCoprime_Lambda_bound}.
-/)]
axiom siegel_walfisz (A : ℕ) (C : ℕ) {x : ℝ} (hx : 2 ≤ x)
    {q : ℕ} (hq0 : 0 < q) (hq : q ≤ (Real.log x) ^ C) {a : ZMod q} (ha : IsUnit a) :
  |chebyPsi x a - x / φ q| ≤ C_SW A C * (x / (Real.log x) ^ A)


axiom C_LS : ℝ

  open Classical in
/- Note: We avoid phrasing this axiom in terms of our own definitions (such as summatory) to minimize the chance this axiom
introduces an inconsistency. -/
@[blueprint (latexEnv := "assumption") (hasProof := false) (title := /-- The large sieve inequality -/) (statement := /--
For all real $Q \ge 1$, all $H \in \Z$, all integers $N \ge 1$ and all $c : \Z \to \C$,
$$\sum_{q \le Q} \sumstar_{\chi \bmod q} \frac{q}{\varphi(q)} \left| \sum_{H < n \le H + N} c_n \chi(n) \right|^2 \ll (N + Q^2) \sum_{H < n \le H + N} |c_n|^2,$$
where $\sumstar$ denotes a sum over primitive characters and the implied constant is absolute. This is
the multiplicative large sieve inequality and is taken as an external input (an axiom in Lean, whose
implied constant is an unspecified real number); no proof is given here.
-/)]
axiom large_sieve (Q : ℝ) (hQ : 1 ≤ Q) (H : ℤ) (N : ℕ) (hN : 0 < N) (c : ℤ → ℂ) :
    ∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊, ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
      q / φ q * ‖∑ n ∈ Finset.Ioc H (H+N), c n * χ n‖^2 ≤
    C_LS * (N+Q^2) * ∑ n ∈ Finset.Ioc H (H+N), ‖c n‖^2
