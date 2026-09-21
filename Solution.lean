/-
The comparator solution file: restates `Challenge.bombieri_vinogradov` from `Challenge.lean`

Check it with `comparator.json`, see the README.
-/
import BV

open BV

theorem Challenge.bombieri_vinogradov (A : ℕ) :
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x → ∀ Q : ℝ, 1 ≤ Q → Q ≤ √x / (Real.log x) ^ (A + 3) →
      ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ⨆ y ∈ Set.Icc 1 x, ⨆ a : (ZMod q)ˣ,
          |chebyPsi y (a : ZMod q) - y / Nat.totient q|
        ≤ C * x / (Real.log x) ^ A := by
  refine ⟨C_BV A, fun x hx Q hQ hQx ↦ ?_⟩
  have h := _root_.bombieri_vinogradov A hx hQ hQx
  have hIcc : Nat.Icc 1 Q = Finset.Icc 1 ⌊Q⌋₊ := by
    rw [Nat.Icc, if_pos ⟨hQ, by linarith⟩, Nat.ceil_one]
  rwa [hIcc] at h
