import Mathlib
import BV.Defs

/-!
# Dilation and restriction algebra for the Type I (`Λ♯`) bound

Generic, reusable machinery for `Delta_LambdaSharp_bound`. See
`notes/delta_lambda_sharp_bound.md` for the mathematical writeup.

* `dilate e f` is the dilation `n ↦ 1_{e ∣ n} · f (n / e)` (equal to `δ_e * f`).
* `ArithmeticFunction.on_mul_of_saturated` says restriction to a multiplicatively
  saturated set is a Dirichlet-convolution homomorphism.
-/

open ArithmeticFunction
open scoped Moebius zeta

/-- Dilation of an arithmetic function: `dilate e f (n) = 1_{e ∣ n} · f (n / e)`.
Equivalently `δ_e * f` where `δ_e(n) = 1_{n = e}`. -/
noncomputable def dilate (e : ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if e ∣ n then f (n / e) else 0, by simp⟩

@[simp] theorem dilate_apply (e n : ℕ) (f : ArithmeticFunction ℝ) :
    dilate e f n = if e ∣ n then f (n / e) else 0 := rfl

/-- Convolution passes through dilation: `f * dilate e g = dilate e (f * g)`.
(Reindex `d = e · b`; needs `0 < e`.) Combined with `mul_comm` this lets the
dilation land on the left factor, as `Delta_flog_bound` requires. -/
theorem mul_dilate {e : ℕ} (he : 0 < e) (f g : ArithmeticFunction ℝ) :
    f * dilate e g = dilate e (f * g) := by
  sorry

@[simp] theorem dilate_add (e : ℕ) (f g : ArithmeticFunction ℝ) :
    dilate e (f + g) = dilate e f + dilate e g := by
  sorry

/-- Dilation does not increase the `ℓ¹` mass (reindex, then drop the tail beyond
`x / e ≤ x`). -/
theorem summatory_abs_dilate_le {e : ℕ} (he : 0 < e) (f : ArithmeticFunction ℝ) {x : ℝ} :
    summatory (fun k => |dilate e f k|) x ≤ summatory (fun k => |f k|) x := by
  sorry

/-- `.on` is additive (the `sub` form is what the `Λ♯` decomposition needs). -/
theorem ArithmeticFunction.on_sub {R : Type*} [Ring R] (S : Set ℕ) (f g : ArithmeticFunction R) :
    (f - g).on S = f.on S - g.on S := by
  sorry

/-- Restriction to a multiplicatively saturated set `S`
(`a * b ∈ S ↔ a ∈ S ∧ b ∈ S`) is a Dirichlet-convolution homomorphism. The
coprime set `{n | r.Coprime n}` is saturated by `Nat.coprime_mul_iff_right`. -/
theorem ArithmeticFunction.on_mul_of_saturated {R : Type*} [Semiring R] (S : Set ℕ)
    (hS : ∀ a b, a * b ∈ S ↔ a ∈ S ∧ b ∈ S) (f g : ArithmeticFunction R) :
    (f * g).on S = f.on S * g.on S := by
  sorry

/-- The `ℕ → R` restriction `onCoprime` agrees with the arithmetic-function
restriction `.on {n | r.Coprime n}` (both send `0 ↦ 0` as `f 0 = 0`). -/
theorem onCoprime_eq_on_coe {R : Type*} [Zero R] (r : ℕ) (f : ArithmeticFunction R) :
    onCoprime r (⇑f) = ⇑(f.on {n | r.Coprime n}) := by
  sorry

/-- Restriction shrinks the `ℓ¹` mass. -/
theorem summatory_abs_on_le (S : Set ℕ) (f : ArithmeticFunction ℝ) {x : ℝ} :
    summatory (fun k => |f.on S k|) x ≤ summatory (fun k => |f k|) x := by
  sorry

/-- `ℓ¹` submultiplicativity of Dirichlet convolution. -/
theorem summatory_abs_mul_le (f g : ArithmeticFunction ℝ) {x : ℝ} (hx : 0 ≤ x) :
    summatory (fun k => |(f * g) k|) x
      ≤ summatory (fun k => |f k|) x * summatory (fun k => |g k|) x := by
  sorry
