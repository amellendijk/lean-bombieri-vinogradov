/-
Definitions and axioms shared by the comparator challenge and the project
(`BV/Axioms.lean` imports this file and attaches blueprint annotations).

These are exactly the non-standard entries of `permitted_axioms` in `comparator.json`.
-/

import Mathlib

open ArithmeticFunction

open scoped Nat

/-- The Chebyshev function `ψ(x; q, a) = ∑_{n ≤ x, n ≡ a (mod q)} Λ(n)` in arithmetic
progressions. -/
noncomputable def chebyPsi (x : ℝ) {q : ℕ} (a : ZMod q) : ℝ :=
    ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊ with (n : ℕ) = a, Λ n

/-! ## Assumed inputs -/

/-- The implied constant in the Siegel–Walfisz theorem. -/
axiom C_SW (A : ℕ) (C : ℕ) : ℝ

/-- **Siegel–Walfisz.** Let `A, C ≥ 0`. If `1 ≤ q ≤ (log x)^C` and `a` is a unit mod `q`, then
`ψ(x; q, a) = x / φ(q) + O_{A, C}(x / (log x)^A)`. -/
axiom siegel_walfisz (A : ℕ) (C : ℕ) {x : ℝ} (hx : 2 ≤ x)
    {q : ℕ} (hq0 : 0 < q) (hq : q ≤ (Real.log x) ^ C) {a : ZMod q} (ha : IsUnit a) :
  |chebyPsi x a - x / φ q| ≤ C_SW A C * (x / (Real.log x) ^ A)

/-- The implied constant in the large sieve inequality. -/
axiom C_LS : ℝ

open Classical in
/-- **Large sieve inequality.** For `Q ≥ 1`, `H ∈ ℤ`, `N ≥ 1` and `c : ℤ → ℂ`,
`∑_{q ≤ Q} ∑*_{χ mod q} (q / φ(q)) |∑_{H < n ≤ H + N} c n χ(n)|² ≪ (N + Q²) ∑_{H < n ≤ H+N} |c n|²`.

Note: this is phrased purely in terms of Mathlib notions to minimize the chance that the
axiom introduces an inconsistency. -/
axiom large_sieve (Q : ℝ) (hQ : 1 ≤ Q) (H : ℤ) (N : ℕ) (hN : 0 < N) (c : ℤ → ℂ) :
    ∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊, ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
      q / φ q * ‖∑ n ∈ Finset.Ioc H (H+N), c n * χ n‖^2 ≤
    C_LS * (N+Q^2) * ∑ n ∈ Finset.Ioc H (H+N), ‖c n‖^2
