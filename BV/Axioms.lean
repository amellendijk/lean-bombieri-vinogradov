import Mathlib
import Architect
open ArithmeticFunction

open scoped Nat

noncomputable def chebyPsi (x : ℝ) {q : ℕ} (a : ZMod q) : ℝ :=
    ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊ with (n : ℕ) = a, Λ n

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
  |chebyPsi x a - x / φ q| ≤ C_SW A C * (x / (Real.log x) ^ A)
