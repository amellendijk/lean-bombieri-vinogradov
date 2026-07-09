/-
# Large Sieve -- Attempt 10: Gauss Sum Inversion for Prime Moduli

Goal: Close character_sum_le_exp_sum for prime moduli by connecting
Dirichlet character sums to exponential sums via Gauss sum inversion.

Key identity (for prime p, nontrivial primitive chi, primitive psi):
  sum_n c_n chi(n) = tau(chi_bar)^{-1} * sum_{a unit} chi(a^{-1}) * sum_n c_n psi(na)

This gives: |sum c_n chi(n)|^2 = (1/p) * |sum_a chi(a^{-1}) S_psi(a)|^2

Summing over chi != 1 and applying Plancherel:
  sum_{chi != 1} (p/(p-1)) |sum c_n chi(n)|^2 <= sum_a |S_psi(a)|^2

Architecture:
  char_sum_bound_prime (this file)
    <- isPrimitive_of_prime (conductor theory)
    <- gaussSum_mulShift_of_isPrimitive (Mathlib)
    <- gauss_sum_norm_sq_prime (Attempt9)
    <- plancherel_dirichlet (Attempt9)
    <- mulChar_weighted_sum_eq_units (SumHelper)
-/

import LargeSieve.Farey
import LargeSieve.Character.SumHelper

open Complex Real Finset BigOperators Classical
open scoped ComplexOrder

noncomputable section

-- ============================================================
-- Part 1: Primitivity for prime moduli
-- ============================================================

/-- For prime p, any nontrivial Dirichlet character is primitive.
    Proof: conductor | p. Since p is prime, conductor in {1, p}.
    conductor = 1 iff chi = 1. Since chi != 1, conductor = p. -/
theorem isPrimitive_of_prime_ne_one (p : ℕ) [hp : Fact (Nat.Prime p)]
    {R : Type*} [CommMonoidWithZero R]
    (χ : DirichletCharacter R p) (hχ : χ ≠ 1) :
    DirichletCharacter.IsPrimitive χ := by
  rw [DirichletCharacter.isPrimitive_def]
  have hcond := DirichletCharacter.conductor_dvd_level χ
  rcases (Fact.out : Nat.Prime p).eq_one_or_self_of_dvd _ hcond with h | h
  · exact absurd ((DirichletCharacter.eq_one_iff_conductor_eq_one
      (Fact.out : Nat.Prime p).ne_zero).mpr h) hχ
  · exact h

-- ============================================================
-- Part 2: Gauss sum inversion identity
-- ============================================================

/-- **Gauss sum inversion identity.**
    For prime p, nontrivial chi, and primitive psi:
    sum_x f(x) * gaussSum(chi^{-1}, psi.mulShift x)
      = gaussSum(chi^{-1}, psi) * sum_x f(x) * chi(x) -/
theorem gauss_sum_inversion (p : ℕ) [hp : Fact (Nat.Prime p)]
    (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1)
    (ψ : AddChar (ZMod p) ℂ) (hψ : ψ.IsPrimitive)
    (f : ZMod p → ℂ) :
    ∑ x : ZMod p, f x * gaussSum χ⁻¹ (ψ.mulShift x) =
    gaussSum χ⁻¹ ψ * ∑ x : ZMod p, f x * χ x := by
  have hχ_inv_ne : χ⁻¹ ≠ 1 := inv_ne_one.mpr hχ
  have hprim : DirichletCharacter.IsPrimitive χ⁻¹ :=
    isPrimitive_of_prime_ne_one p χ⁻¹ hχ_inv_ne
  simp_rw [gaussSum_mulShift_of_isPrimitive ψ hprim]
  simp_rw [inv_inv]
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  ring

-- ============================================================
-- Part 3: Sum decomposition and character sum identities
-- ============================================================

/-- **Gauss sum expression as sum over ZMod p.**
    sum_x f(x) * gaussSum(chi^{-1}, psi.mulShift x) =
    sum_a chi^{-1}(a) * sum_x f(x) * psi(x*a) -/
theorem gauss_sum_expand (p : ℕ) [hp : Fact (Nat.Prime p)]
    (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1)
    (ψ : AddChar (ZMod p) ℂ) (hψ : ψ.IsPrimitive)
    (f : ZMod p → ℂ) :
    ∑ x : ZMod p, f x * gaussSum χ⁻¹ (ψ.mulShift x) =
    ∑ a : ZMod p, (χ⁻¹ : MulChar (ZMod p) ℂ) a *
      ∑ x : ZMod p, f x * ψ (x * a) := by
  simp_rw [gaussSum, AddChar.mulShift_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1; ext a
  simp_rw [← mul_assoc, mul_comm (f _) ((χ⁻¹ : MulChar (ZMod p) ℂ) a)]

/-- **Character sum equals Gauss-inverse times inner product.**
    For prime p, nontrivial chi, and primitive psi:
    tau * sum_x f(x) chi(x) =
    sum_{a : (ZMod p)^x} chi(a^{-1}) * sum_x f(x) psi(xa)

    Uses mulChar_weighted_sum_eq_units to decompose the ZMod p sum
    into units (where chi^{-1}(a) = chi(a^{-1})) and zero (where chi^{-1}(0) = 0). -/
theorem char_sum_eq_gauss_inv (p : ℕ) [hp : Fact (Nat.Prime p)]
    (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1)
    (ψ : AddChar (ZMod p) ℂ) (hψ : ψ.IsPrimitive)
    (f : ZMod p → ℂ) :
    gaussSum χ⁻¹ ψ * ∑ x : ZMod p, f x * χ x =
    ∑ a : (ZMod p)ˣ, χ (a⁻¹ : (ZMod p)ˣ) *
      ∑ x : ZMod p, f x * ψ (x * ↑a) := by
  rw [← gauss_sum_inversion p χ hχ ψ hψ f]
  rw [gauss_sum_expand p χ hχ ψ hψ f]
  -- Now: ∑ a : ZMod p, χ⁻¹(a) * G(a) = ∑ a : (ZMod p)ˣ, χ(a⁻¹) * G(↑a)
  -- Use mulChar_weighted_sum_eq_units to decompose ZMod p sum into units
  rw [mulChar_weighted_sum_eq_units (χ⁻¹ : MulChar (ZMod p) ℂ)
      (fun a => ∑ x : ZMod p, f x * ψ (x * a))]
  -- Now both sides sum over (ZMod p)ˣ; relate χ⁻¹(↑u) to χ(↑(u⁻¹))
  congr 1; ext u
  congr 1
  -- χ⁻¹(↑u) = χ(↑(u⁻¹))
  show (χ⁻¹ : MulChar (ZMod p) ℂ) ↑u = χ ↑(u⁻¹ : (ZMod p)ˣ)
  rw [MulChar.inv_apply']
  congr 1
  exact (Units.val_inv_eq_inv_val u).symm

/-- **Norm-squared identity for character sums (prime modulus).**
    p * |∑ f(x)χ(x)|² = |∑_{a unit} χ(a⁻¹) S_ψ(a)|² -/
theorem char_sum_norm_sq_eq (p : ℕ) [hp : Fact (Nat.Prime p)]
    (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1)
    (ψ : AddChar (ZMod p) ℂ) (hψ : ψ.IsPrimitive)
    (f : ZMod p → ℂ) :
    (p : ℝ) * Complex.normSq (∑ x : ZMod p, f x * χ x) =
    Complex.normSq (∑ a : (ZMod p)ˣ, χ (a⁻¹ : (ZMod p)ˣ) *
      ∑ x : ZMod p, f x * ψ (x * ↑a)) := by
  have heq := char_sum_eq_gauss_inv p χ hχ ψ hψ f
  have h1 : Complex.normSq (gaussSum χ⁻¹ ψ * ∑ x, f x * χ x) =
    Complex.normSq (∑ a : (ZMod p)ˣ, χ ↑(a⁻¹) * ∑ x, f x * ψ (x * ↑a)) := by
    rw [heq]
  rw [map_mul] at h1
  have htau : Complex.normSq (gaussSum χ⁻¹ ψ) = (p : ℝ) :=
    gauss_sum_norm_sq_prime p χ⁻¹ (inv_ne_one.mpr hχ) ψ hψ
  rw [htau] at h1
  exact h1

-- ============================================================
-- Part 4: Main character sum bound
-- ============================================================

/-- **Main character sum bound for prime moduli (nontrivial characters).**
    p · ∑_{χ≠1} |∑ f(x)χ(x)|² ≤ φ(p) · ∑_{a unit} |S_ψ(a)|²

    Proof:
    1. For each χ ≠ 1: p · |∑ fχ|² = |∑_a χ(a⁻¹) S(a)|²  [char_sum_norm_sq_eq]
    2. ∑_{χ≠1} |∑_a χ(a⁻¹) S(a)|² ≤ ∑_χ |...|²  [subset, normSq ≥ 0]
    3. ∑_χ |∑_a χ(a⁻¹) S(a)|² = φ(p) · ∑_a |S(a)|²  [Plancherel] -/
theorem char_sum_bound_prime (p : ℕ) [hp : Fact (Nat.Prime p)]
    [HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod p)ˣ)]
    (ψ : AddChar (ZMod p) ℂ) (hψ : ψ.IsPrimitive)
    (f : ZMod p → ℂ) :
    (p : ℝ) * ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ p)).filter (· ≠ 1),
      Complex.normSq (∑ x : ZMod p, f x * χ x) ≤
    (p.totient : ℝ) * ∑ a : (ZMod p)ˣ,
      Complex.normSq (∑ x : ZMod p, f x * ψ (x * ↑a)) := by
  -- Step 1: Distribute p into the sum
  rw [Finset.mul_sum]
  -- Step 2: For each χ ≠ 1, apply char_sum_norm_sq_eq
  have h_eq : ∀ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ p)).filter (· ≠ 1),
      (p : ℝ) * Complex.normSq (∑ x, f x * χ x) =
      Complex.normSq (∑ a : (ZMod p)ˣ, χ (↑(a⁻¹ : (ZMod p)ˣ)) *
        (∑ x : ZMod p, f x * ψ (x * ↑a))) := by
    intro χ hχ
    have hne : χ ≠ 1 := (Finset.mem_filter.mp hχ).2
    exact char_sum_norm_sq_eq p χ hne ψ hψ f
  rw [Finset.sum_congr rfl h_eq]
  -- Step 3: Subset sum ≤ full sum (normSq ≥ 0), then Plancherel
  let g : DirichletCharacter ℂ p → ℝ := fun χ =>
    Complex.normSq (∑ a : (ZMod p)ˣ, χ ↑(a⁻¹ : (ZMod p)ˣ) *
      (∑ x, f x * ψ (x * ↑a)))
  have h_subset : ∑ χ ∈ Finset.univ.filter (· ≠ 1), g χ ≤ ∑ χ, g χ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun χ _ _ => Complex.normSq_nonneg _)
  have h_planch : ∑ χ, g χ = (p.totient : ℝ) * ∑ a : (ZMod p)ˣ,
      Complex.normSq (∑ x, f x * ψ (x * ↑a)) :=
    plancherel_dirichlet p (fun a => ∑ x, f x * ψ (x * ↑a))
  linarith

-- ============================================================
-- Part 5: Summary and dependency graph
-- ============================================================

/-!
## Dependency Graph

```
char_sum_bound_prime [PROVED ✅]
  <- char_sum_norm_sq_eq [PROVED ✅]
    <- char_sum_eq_gauss_inv [PROVED ✅]
      <- gauss_sum_expand [PROVED ✅]
        <- mulChar_weighted_sum_eq_units [PROVED ✅, SumHelper]
      <- gauss_sum_inversion [PROVED ✅]
    <- gauss_sum_norm_sq_prime [PROVED ✅, Attempt9]
  <- plancherel_dirichlet [PROVED ✅, Attempt9]
  <- isPrimitive_of_prime_ne_one [PROVED ✅]
```

## Progress Summary

ALL SORRY-FREE (this file + SumHelper):
1. isPrimitive_of_prime_ne_one: For prime p, χ ≠ 1 ⟹ IsPrimitive χ
2. gauss_sum_inversion: ∑_x f(x) * gaussSum(χ⁻¹, ψ.mulShift x) = τ * ∑_x f(x)χ(x)
3. gauss_sum_expand: Expand gaussSum into sum over ZMod p
4. mulChar_weighted_sum_eq_units: ∑_a χ(a)*g(a) = ∑_{units} χ(a)*g(a)
5. char_sum_eq_gauss_inv: τ * ∑ fχ = ∑_{a unit} χ(a⁻¹) * S(a)
6. char_sum_norm_sq_eq: p * normSq(∑ fχ) = normSq(∑_{a unit} χ(a⁻¹)S(a))
7. char_sum_bound_prime: p * ∑_{χ≠1} normSq(∑ fχ) ≤ φ(p) * ∑_a normSq(S(a))
-/

end
