/-
The comparator challenge file for the Bombieri–Vinogradov project.
-/
import Challenge.Axioms

open scoped Nat

/-! ## The challenge -/

/-- **Bombieri–Vinogradov.** For each fixed `A ≥ 0` there is a constant `C` such that
`∑_{q ≤ Q} max_{y ≤ x} max_{a ∈ (ℤ/qℤ)ˣ} |ψ(y; q, a) - y / φ(q)| ≤ C x / (log x)^A`
uniformly for all `x ≥ 2` and `1 ≤ Q ≤ √x / (log x)^(A+3)`. -/
theorem Challenge.bombieri_vinogradov (A : ℕ) :
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x → ∀ Q : ℝ, 1 ≤ Q → Q ≤ √x / (Real.log x) ^ (A + 3) →
      ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ⨆ y ∈ Set.Icc 1 x, ⨆ a : (ZMod q)ˣ,
          |chebyPsi y (a : ZMod q) - y / φ q|
        ≤ C * x / (Real.log x) ^ A := by
  sorry
