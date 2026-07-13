import Mathlib
import Architect

import BV.Defs

open ArithmeticFunction

open scoped Nat

/-- The implied constant in the Sielgel-Walfisz Theorem -/
axiom C_SW (A : ℕ) (C : ℕ) : ℝ

@[blueprint (latexEnv := "assumption") (statement :=
/--
Let $A, C > 0$. If $1 \leq q \leq (\log x)^C$ and $a \in (\mathbb{Z}/q\mathbb{Z})^*$, then
$$
\psi(x;q,a) = \frac{x}{\varphi(q)} + O_{A, C}\left(\frac{x}{(\log x)^A}\right).
$$
-/
)]
axiom siegel_walfisz (A : ℕ) (C : ℕ) {x : ℝ} (hx : 2 ≤ x)
    {q : ℕ} (hq0 : 0 < q) (hq : q ≤ (Real.log x) ^ C) {a : ZMod q} (ha : IsUnit a) :
  |ψ x a - x / φ q| ≤ C_SW A C * (x / (Real.log x) ^ A)


axiom C_LS : ℝ

/- Note: We avoid phrasing this axiom in terms of our own definitions (such as summatory) to minimize the chance this axiom
introduces an inconsistency. -/
@[blueprint (latexEnv := "assumption") (statement :=
/--
Let $Q \ge 1$, $H \in \Z$, $N \in \Z_{\ge 1}$ and $c = (c_{H+1}, \dots, c_{H+N}) \in \C^N$ We then have
$$\sum_{q \le Q} \sumstar_{\chi \pmod q} \frac{q}{\varphi(q)} \left| \sum_{H < n \le H+N} c_n \chi(n) \right|^2 \ll (N+Q^2) \| \vec{c} \|_2^2,$$
-/
)]
axiom large_sieve (Q : ℝ) (hQ : 1 ≤ Q) (H : ℤ) (N : ℕ) (hN : 0 < N) (c : ℤ → ℂ) :
  open Classical in
  ∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊, ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
      q / φ q * ‖∑ n ∈ Finset.Ioc H (H+N), c n * χ n‖^2 ≤
    C_LS * (N+Q^2) * ∑ n ∈ Finset.Ioc H (H+N), ‖c n‖^2
