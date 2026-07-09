/-
# Large Sieve -- Attempt 11: General moduli via primitive characters

Goal: Close the two remaining Attempt9 gaps for GENERAL moduli q:
  1. gauss_sum_norm_sq_primitive : |τ(χ,ψ)|² = q for primitive χ mod q
  2. char_sum_bound_primitive : the character→exponential bound for any
     finset of primitive characters mod q

Key insight: the classical double-counting proof of |τ(χ)|² = q works for
any modulus once χ is primitive, using Mathlib's
`gaussSum_mulShift_of_isPrimitive` (valid for ALL shifts a, including
non-units — this is exactly where primitivity is needed) together with
additive Plancherel over ZMod q.

NOTE ON CORRECTNESS: the earlier statement `character_sum_le_exp_sum`
(Attempt9) quantified over arbitrary finsets of characters, including
imprimitive/trivial ones. That statement is FALSE (take q = 2, the trivial
character, and c ≡ 1: the LHS is ~N²/2 while the RHS is O(1)). The correct
multiplicative large sieve restricts to PRIMITIVE characters (the starred
sum ∑* in the literature). This file proves the corrected statement.
-/

import LargeSieve.Character.PrimeCase
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

open Complex Real Finset BigOperators Classical ZMod
open scoped ComplexOrder

noncomputable section

-- ============================================================
-- Part 1: Sums over ZMod q reduce to sums over units
-- ============================================================

/-- A function vanishing on non-units sums over all of `ZMod q` the same
    as over the units. -/
lemma sum_eq_sum_units {q : ℕ} [NeZero q] {M : Type*} [AddCommMonoid M]
    (F : ZMod q → M) (hF : ∀ a : ZMod q, ¬IsUnit a → F a = 0) :
    ∑ a : ZMod q, F a = ∑ u : (ZMod q)ˣ, F ↑u := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun a => IsUnit a)]
  have h2 : ∑ a ∈ Finset.univ.filter (fun a => ¬IsUnit a), F a = 0 :=
    Finset.sum_eq_zero fun a ha => hF a (Finset.mem_filter.mp ha).2
  rw [show (Finset.univ.filter (fun a : ZMod q => ¬IsUnit a)) =
      Finset.univ.filter (fun a : ZMod q => ¬(fun a => IsUnit a) a) from rfl] at h2
  rw [h2, add_zero]
  symm
  exact Finset.sum_nbij' (fun (u : (ZMod q)ˣ) => (↑u : ZMod q))
    (fun (a : ZMod q) => if h : IsUnit a then h.unit else 1)
    (fun u _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, u.isUnit⟩)
    (fun _ _ => Finset.mem_univ _)
    (fun u _ => by
      rw [dif_pos u.isUnit]
      exact Units.val_injective u.isUnit.unit_spec)
    (fun a ha => by
      have h := (Finset.mem_filter.mp ha).2
      simp [dif_pos h])
    (fun _ _ => rfl)

/-- Weighted character sums over `ZMod q` reduce to sums over units
    (general-modulus version of `mulChar_weighted_sum_eq_units`). -/
lemma mulChar_sum_eq_units {q : ℕ} [NeZero q]
    (χ : MulChar (ZMod q) ℂ) (g : ZMod q → ℂ) :
    ∑ a : ZMod q, χ a * g a = ∑ u : (ZMod q)ˣ, χ ↑u * g ↑u :=
  sum_eq_sum_units (fun a => χ a * g a)
    (fun a ha => by rw [MulChar.map_nonunit χ ha, zero_mul])

-- ============================================================
-- Part 2: Primitivity is preserved under inverse
-- ============================================================

/-- If χ factors through d, so does χ⁻¹. -/
lemma factorsThrough_inv {q : ℕ} (χ : DirichletCharacter ℂ q) {d : ℕ}
    (h : χ.FactorsThrough d) : (χ⁻¹).FactorsThrough d := by
  obtain ⟨hd, χ₀, hχ₀⟩ := h
  exact ⟨hd, χ₀⁻¹, by rw [map_inv, ← hχ₀]⟩

/-- The conductor is invariant under inverse. -/
lemma conductor_inv {q : ℕ} (χ : DirichletCharacter ℂ q) :
    (χ⁻¹).conductor = χ.conductor := by
  have h1 : (χ⁻¹).conductor ≤ χ.conductor :=
    Nat.sInf_le (factorsThrough_inv χ χ.factorsThrough_conductor)
  have h2 : χ.conductor ≤ (χ⁻¹).conductor := by
    have := factorsThrough_inv χ⁻¹ (χ⁻¹).factorsThrough_conductor
    rw [inv_inv] at this
    exact Nat.sInf_le this
  omega

/-- The inverse of a primitive character is primitive. -/
lemma isPrimitive_inv {q : ℕ} (χ : DirichletCharacter ℂ q)
    (h : χ.IsPrimitive) : (χ⁻¹).IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def, conductor_inv]
  exact h

-- ============================================================
-- Part 3: Additive Plancherel over ZMod q
-- ============================================================

/-- Orthogonality of a primitive additive character. -/
lemma add_char_orthogonality {q : ℕ} [NeZero q]
    (ψ : AddChar (ZMod q) ℂ) (hψ : ψ.IsPrimitive) (z : ZMod q) :
    ∑ b : ZMod q, ψ (b * z) = if z = 0 then (q : ℂ) else 0 := by
  have h := AddChar.sum_mulShift z hψ
  rw [ZMod.card] at h
  simpa [mul_comm] using h

/-- ℂ-valued additive Plancherel over ZMod q (workhorse). -/
private lemma add_plancherel_complex {q : ℕ} [NeZero q]
    (ψ : AddChar (ZMod q) ℂ) (hψ : ψ.IsPrimitive) (g : ZMod q → ℂ) :
    ∑ b : ZMod q,
      (starRingEnd ℂ (∑ x : ZMod q, g x * ψ (x * b))) *
        (∑ x : ZMod q, g x * ψ (x * b)) =
    (q : ℂ) * ∑ x : ZMod q, starRingEnd ℂ (g x) * g x := by
  simp_rw [map_sum, map_mul]
  have hconj : ∀ (x b : ZMod q), starRingEnd ℂ (ψ (x * b)) = ψ (-(x * b)) :=
    fun x b => (AddChar.map_neg_eq_conj ψ (x * b)).symm
  simp_rw [hconj]
  have hterm : ∀ b : ZMod q,
      (∑ x : ZMod q, starRingEnd ℂ (g x) * ψ (-(x * b))) *
        (∑ y : ZMod q, g y * ψ (y * b)) =
      ∑ x : ZMod q, ∑ y : ZMod q,
        (starRingEnd ℂ (g x) * g y) * ψ (b * (y - x)) := by
    intro b
    rw [Fintype.sum_mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [show starRingEnd ℂ (g x) * ψ (-(x * b)) * (g y * ψ (y * b)) =
        (starRingEnd ℂ (g x) * g y) * (ψ (-(x * b)) * ψ (y * b)) from by ring,
      ← AddChar.map_add_eq_mul,
      show -(x * b) + y * b = b * (y - x) from by ring]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  have hswap : ∀ x : ZMod q,
      ∑ b : ZMod q, ∑ y : ZMod q,
        (starRingEnd ℂ (g x) * g y) * ψ (b * (y - x)) =
      ∑ y : ZMod q, (starRingEnd ℂ (g x) * g y) *
        ∑ b : ZMod q, ψ (b * (y - x)) := by
    intro x
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun y _ => (Finset.mul_sum _ _ _).symm
  simp_rw [hswap, add_char_orthogonality ψ hψ, sub_eq_zero, mul_ite, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- Real-valued additive Plancherel over ZMod q:
    ∑_b |∑_x g(x)ψ(xb)|² = q · ∑_x |g(x)|². -/
theorem add_plancherel {q : ℕ} [NeZero q]
    (ψ : AddChar (ZMod q) ℂ) (hψ : ψ.IsPrimitive) (g : ZMod q → ℂ) :
    ∑ b : ZMod q, Complex.normSq (∑ x : ZMod q, g x * ψ (x * b)) =
    (q : ℝ) * ∑ x : ZMod q, Complex.normSq (g x) := by
  have h := add_plancherel_complex ψ hψ g
  have hcast : ((∑ b : ZMod q,
      Complex.normSq (∑ x : ZMod q, g x * ψ (x * b))) : ℂ) =
      ↑((q : ℝ) * ∑ x : ZMod q, Complex.normSq (g x)) := by
    push_cast
    simp_rw [Complex.normSq_eq_conj_mul_self]
    exact h
  exact_mod_cast hcast

-- ============================================================
-- Part 4: |τ(χ,ψ)|² = q for primitive χ (GENERAL modulus)
-- ============================================================

/-- The sum of |χ(x)|² over ZMod q is φ(q), for any Dirichlet char χ
    that is nonvanishing exactly on units with |χ(unit)| = 1. -/
lemma sum_normSq_char {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ∑ x : ZMod q, Complex.normSq (χ x) = (q.totient : ℝ) := by
  rw [sum_eq_sum_units (fun x => Complex.normSq (χ x))
    (fun a ha => by rw [MulChar.map_nonunit χ ha, Complex.normSq_zero])]
  have h1 : ∀ u : (ZMod q)ˣ, Complex.normSq (χ ↑u) = 1 := by
    intro u
    have hn : ‖χ ↑u‖ = 1 := χ.unit_norm_eq_one u
    rw [Complex.normSq_eq_norm_sq, hn, one_pow]
  simp_rw [h1]
  rw [Finset.sum_const, Finset.card_univ, ZMod.card_units_eq_totient]
  simp

/-- **Gauss sum norm for primitive characters, general modulus.**
    For primitive χ mod q and primitive ψ: |τ(χ,ψ)|² = q.

    Proof (double counting): compute ∑_b |τ(χ, ψ.mulShift b)|² two ways.
    Way 1: τ(χ, ψ.mulShift b) = χ⁻¹(b)·τ(χ,ψ) (primitivity!), giving
           φ(q)·|τ|².
    Way 2: expanding and applying additive Plancherel gives q·φ(q). -/
theorem gauss_sum_norm_sq_primitive (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (ψ : AddChar (ZMod q) ℂ) (hψ : ψ.IsPrimitive) :
    Complex.normSq (gaussSum χ ψ) = (q : ℝ) := by
  have hφ : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  -- Way 1
  have hway1 : ∑ b : ZMod q, Complex.normSq (gaussSum χ (ψ.mulShift b)) =
      (q.totient : ℝ) * Complex.normSq (gaussSum χ ψ) := by
    have h1 : ∀ b : ZMod q,
        gaussSum χ (ψ.mulShift b) = χ⁻¹ b * gaussSum χ ψ := fun b =>
      gaussSum_mulShift_of_isPrimitive ψ hχ b
    simp_rw [h1, Complex.normSq_mul]
    rw [← Finset.sum_mul, sum_normSq_char χ⁻¹]
  -- Way 2
  have hway2 : ∑ b : ZMod q, Complex.normSq (gaussSum χ (ψ.mulShift b)) =
      (q : ℝ) * (q.totient : ℝ) := by
    have h2 : ∀ b : ZMod q,
        gaussSum χ (ψ.mulShift b) = ∑ x : ZMod q, χ x * ψ (x * b) := by
      intro b
      simp_rw [gaussSum, AddChar.mulShift_apply, mul_comm b]
    simp_rw [h2]
    rw [add_plancherel ψ hψ (fun x => χ x), sum_normSq_char χ]
  have := hway1.symm.trans hway2
  field_simp at this
  linarith [mul_left_cancel₀ (ne_of_gt hφ)
    (by linarith : (q.totient : ℝ) * Complex.normSq (gaussSum χ ψ) =
      (q.totient : ℝ) * (q : ℝ))]

-- ============================================================
-- Part 5: Character sum identities for general modulus
-- ============================================================

/-- Gauss sum inversion for general modulus (primitive χ). -/
theorem gauss_sum_inversion_general (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (ψ : AddChar (ZMod q) ℂ)
    (f : ZMod q → ℂ) :
    ∑ x : ZMod q, f x * gaussSum χ⁻¹ (ψ.mulShift x) =
    gaussSum χ⁻¹ ψ * ∑ x : ZMod q, f x * χ x := by
  have hprim : (χ⁻¹).IsPrimitive := isPrimitive_inv χ hχ
  simp_rw [gaussSum_mulShift_of_isPrimitive ψ hprim]
  simp_rw [inv_inv]
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  ring

/-- Gauss sum expansion (pure sum manipulation, general modulus). -/
theorem gauss_sum_expand_general (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q)
    (ψ : AddChar (ZMod q) ℂ)
    (f : ZMod q → ℂ) :
    ∑ x : ZMod q, f x * gaussSum χ⁻¹ (ψ.mulShift x) =
    ∑ a : ZMod q, (χ⁻¹ : MulChar (ZMod q) ℂ) a *
      ∑ x : ZMod q, f x * ψ (x * a) := by
  simp_rw [gaussSum, AddChar.mulShift_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1; ext a
  simp_rw [← mul_assoc, mul_comm (f _) ((χ⁻¹ : MulChar (ZMod q) ℂ) a)]

/-- Character sum as Gauss-inverse inner product (general modulus). -/
theorem char_sum_eq_gauss_inv_general (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (ψ : AddChar (ZMod q) ℂ)
    (f : ZMod q → ℂ) :
    gaussSum χ⁻¹ ψ * ∑ x : ZMod q, f x * χ x =
    ∑ a : (ZMod q)ˣ, χ (a⁻¹ : (ZMod q)ˣ) *
      ∑ x : ZMod q, f x * ψ (x * ↑a) := by
  rw [← gauss_sum_inversion_general q χ hχ ψ f]
  rw [gauss_sum_expand_general q χ ψ f]
  rw [mulChar_sum_eq_units (χ⁻¹ : MulChar (ZMod q) ℂ)
      (fun a => ∑ x : ZMod q, f x * ψ (x * a))]
  congr 1; ext u
  congr 1
  show (χ⁻¹ : MulChar (ZMod q) ℂ) ↑u = χ ↑(u⁻¹ : (ZMod q)ˣ)
  have h := mulchar_inv_inv q χ u⁻¹
  rw [inv_inv] at h
  exact h

/-- Norm-squared identity for character sums (general modulus). -/
theorem char_sum_norm_sq_eq_general (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (ψ : AddChar (ZMod q) ℂ) (hψ : ψ.IsPrimitive)
    (f : ZMod q → ℂ) :
    (q : ℝ) * Complex.normSq (∑ x : ZMod q, f x * χ x) =
    Complex.normSq (∑ a : (ZMod q)ˣ, χ (a⁻¹ : (ZMod q)ˣ) *
      ∑ x : ZMod q, f x * ψ (x * ↑a)) := by
  have heq := char_sum_eq_gauss_inv_general q χ hχ ψ f
  have h1 : Complex.normSq (gaussSum χ⁻¹ ψ * ∑ x, f x * χ x) =
    Complex.normSq (∑ a : (ZMod q)ˣ, χ ↑(a⁻¹) * ∑ x, f x * ψ (x * ↑a)) := by
    rw [heq]
  rw [map_mul] at h1
  have htau : Complex.normSq (gaussSum χ⁻¹ ψ) = (q : ℝ) :=
    gauss_sum_norm_sq_primitive q χ⁻¹ (isPrimitive_inv χ hχ) ψ hψ
  rw [htau] at h1
  exact h1

-- ============================================================
-- Part 6: Main character sum bound for general modulus
-- ============================================================

/-- **Main character sum bound (general modulus, primitive characters).**
    For any finset S of PRIMITIVE Dirichlet characters mod q:
    q · ∑_{χ∈S} |∑ f(x)χ(x)|² ≤ φ(q) · ∑_{a unit} |S_ψ(a)|² -/
theorem char_sum_bound_primitive (q : ℕ) [NeZero q]
    [HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod q)ˣ)]
    (ψ : AddChar (ZMod q) ℂ) (hψ : ψ.IsPrimitive)
    (f : ZMod q → ℂ)
    (S : Finset (DirichletCharacter ℂ q)) (hS : ∀ χ ∈ S, χ.IsPrimitive) :
    (q : ℝ) * ∑ χ ∈ S,
      Complex.normSq (∑ x : ZMod q, f x * χ x) ≤
    (q.totient : ℝ) * ∑ a : (ZMod q)ˣ,
      Complex.normSq (∑ x : ZMod q, f x * ψ (x * ↑a)) := by
  rw [Finset.mul_sum]
  have h_eq : ∀ χ ∈ S,
      (q : ℝ) * Complex.normSq (∑ x, f x * χ x) =
      Complex.normSq (∑ a : (ZMod q)ˣ, χ (↑(a⁻¹ : (ZMod q)ˣ)) *
        (∑ x : ZMod q, f x * ψ (x * ↑a))) := by
    intro χ hχ
    exact char_sum_norm_sq_eq_general q χ (hS χ hχ) ψ hψ f
  rw [Finset.sum_congr rfl h_eq]
  let g : DirichletCharacter ℂ q → ℝ := fun χ =>
    Complex.normSq (∑ a : (ZMod q)ˣ, χ ↑(a⁻¹ : (ZMod q)ˣ) *
      (∑ x, f x * ψ (x * ↑a)))
  have h_subset : ∑ χ ∈ S, g χ ≤ ∑ χ, g χ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun χ _ _ => Complex.normSq_nonneg _)
  have h_planch : ∑ χ, g χ = (q.totient : ℝ) * ∑ a : (ZMod q)ˣ,
      Complex.normSq (∑ x, f x * ψ (x * ↑a)) :=
    plancherel_dirichlet q (fun a => ∑ x, f x * ψ (x * ↑a))
  calc ∑ χ ∈ S, g χ ≤ ∑ χ, g χ := h_subset
    _ = _ := h_planch

-- ============================================================
-- Part 7: Bridge to integer-interval sums and explicit e(na/q)
-- ============================================================

/-- Fold an integer-interval sum into residue classes mod q. -/
lemma sum_fold_residues {q : ℕ} [NeZero q] (H : ℤ) (N : ℕ) (c : ℤ → ℂ)
    (h : ZMod q → ℂ) :
    ∑ n ∈ Finset.Ioc H (H + ↑N), c n * h (n : ZMod q) =
    ∑ x : ZMod q, (∑ n ∈ (Finset.Ioc H (H + ↑N)).filter
        (fun (n : ℤ) => ((n : ZMod q) = x)), c n) * h x := by
  simp_rw [Finset.sum_mul]
  rw [← Finset.sum_fiberwise (Finset.Ioc H (H + ↑N))
      (fun n => ((n : ZMod q)))
      (fun n => c n * h ((n : ZMod q)))]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun n hn => ?_
  rw [(Finset.mem_filter.mp hn).2]

/-- The standard additive character mod q agrees with `e` at rationals. -/
lemma stdAddChar_eq_e {q : ℕ} [NeZero q] (n : ℤ) (a : ℕ) :
    ZMod.stdAddChar (((n * (a : ℤ) : ℤ)) : ZMod q) =
    e ((n : ℝ) * ((a : ℝ) / (q : ℝ))) := by
  rw [ZMod.stdAddChar_coe]
  unfold e
  congr 1
  push_cast
  ring

/-- The natural representative of a unit in `(ZMod q)ˣ` inside `Icc 1 q`. -/
def unitRep {q : ℕ} [NeZero q] (u : (ZMod q)ˣ) : ℕ :=
  if ((u : ZMod q)).val = 0 then q else ((u : ZMod q)).val

lemma unitRep_cast {q : ℕ} [NeZero q] (u : (ZMod q)ˣ) :
    ((unitRep u : ℕ) : ZMod q) = (u : ZMod q) := by
  unfold unitRep
  split_ifs with h
  · rw [ZMod.natCast_self]
    exact ((ZMod.val_eq_zero _).mp h).symm
  · exact ZMod.natCast_rightInverse _

lemma unitRep_mem {q : ℕ} [NeZero q] (u : (ZMod q)ˣ) :
    unitRep u ∈ (Finset.Icc 1 q).filter (fun a => Nat.Coprime a q) := by
  have hcop : Nat.Coprime ((u : ZMod q)).val q := ZMod.val_coe_unit_coprime u
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  unfold unitRep
  split_ifs with h
  · have hq1 : q = 1 := by
      have := hcop
      rw [h] at this
      simpa [Nat.Coprime, Nat.gcd_zero_left] using this
    subst hq1
    simp [Nat.Coprime]
  · refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr h,
      le_of_lt (ZMod.val_lt _)⟩, hcop⟩

/-- Exponential sums over ZMod residues equal exponential sums over `Ioc`. -/
lemma unit_exp_sum_eq {q : ℕ} [NeZero q] (H : ℤ) (N : ℕ) (c : ℤ → ℂ)
    (u : (ZMod q)ˣ) :
    ∑ x : ZMod q, (∑ n ∈ (Finset.Ioc H (H + ↑N)).filter
        (fun (n : ℤ) => ((n : ZMod q) = x)), c n) * ZMod.stdAddChar (x * (u : ZMod q)) =
    ∑ n ∈ Finset.Ioc H (H + ↑N),
      c n * e ((n : ℝ) * ((unitRep u : ℝ) / (q : ℝ))) := by
  rw [← sum_fold_residues H N c (fun x => ZMod.stdAddChar (x * (u : ZMod q)))]
  refine Finset.sum_congr rfl fun n _ => ?_
  congr 1
  rw [← stdAddChar_eq_e n (unitRep u)]
  congr 1
  push_cast
  rw [unitRep_cast]

/-- The map `unitRep` is a bijection onto coprime residues in `Icc 1 q`,
    transporting the exponential-sum summand. -/
lemma sum_units_eq_sum_coprime {q : ℕ} [NeZero q] (H : ℤ) (N : ℕ) (c : ℤ → ℂ) :
    ∑ u : (ZMod q)ˣ, Complex.normSq (∑ x : ZMod q,
        (∑ n ∈ (Finset.Ioc H (H + ↑N)).filter
          (fun (n : ℤ) => ((n : ZMod q) = x)), c n) * ZMod.stdAddChar (x * (u : ZMod q))) =
    ∑ a ∈ (Finset.Icc 1 q).filter (fun a => Nat.Coprime a q),
      ‖∑ n ∈ Finset.Ioc H (H + ↑N), c n * e ((n : ℝ) * ((a : ℝ) / (q : ℝ)))‖ ^ 2 := by
  refine Finset.sum_nbij' (fun (u : (ZMod q)ˣ) => unitRep u)
    (fun (a : ℕ) => if h : Nat.Coprime a q then ZMod.unitOfCoprime a h else 1)
    (fun u _ => unitRep_mem u)
    (fun _ _ => Finset.mem_univ _)
    (fun u _ => ?_) (fun a ha => ?_) (fun u _ => ?_)
  · -- left inverse: recover u from unitRep u
    have hcop : Nat.Coprime (unitRep u) q := (Finset.mem_filter.mp (unitRep_mem u)).2
    rw [dif_pos hcop]
    apply Units.ext
    rw [ZMod.coe_unitOfCoprime, unitRep_cast]
  · -- right inverse: unitRep of the unit of a coprime residue is a
    obtain ⟨haI, hcop⟩ := Finset.mem_filter.mp ha
    obtain ⟨ha1, haq⟩ := Finset.mem_Icc.mp haI
    rw [dif_pos hcop]
    unfold unitRep
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
    rcases eq_or_lt_of_le haq with heq | hlt
    · subst heq
      simp
    · rw [Nat.mod_eq_of_lt hlt, if_neg (by omega)]
  · -- summand equality
    rw [unit_exp_sum_eq H N c u, Complex.normSq_eq_norm_sq]

/-- **Character sums bounded by exponential sums at coprime fractions
    (general modulus, primitive characters).** This is the corrected,
    sharper form of `character_sum_le_exp_sum` (Attempt9), with the
    primitivity restriction that makes the statement true, and without
    the spurious factor of q on the right-hand side. -/
theorem character_sum_le_exp_sum_primitive (q : ℕ) [NeZero q]
    [HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod q)ˣ)]
    (H : ℤ) (N : ℕ) (c : ℤ → ℂ)
    (S : Finset (DirichletCharacter ℂ q)) (hS : ∀ χ ∈ S, χ.IsPrimitive) :
    ∑ χ ∈ S,
      (q : ℝ) / (Nat.totient q : ℝ) *
        ‖∑ n ∈ Finset.Ioc H (H + ↑N), c n * (χ n : ℂ)‖ ^ 2 ≤
    ∑ a ∈ (Finset.Icc 1 q).filter (fun a => Nat.Coprime a q),
      ‖∑ n ∈ Finset.Ioc H (H + ↑N), c n * e ((n : ℝ) * ((a : ℝ) / (q : ℝ)))‖ ^ 2 := by
  set f : ZMod q → ℂ := fun x =>
    ∑ n ∈ (Finset.Ioc H (H + ↑N)).filter (fun (n : ℤ) => ((n : ZMod q) = x)), c n with hf
  have hφ : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hψ : (ZMod.stdAddChar (N := q)).IsPrimitive := ZMod.isPrimitive_stdAddChar q
  -- rewrite character sums via residue folding
  have hchar : ∀ χ : DirichletCharacter ℂ q,
      ∑ n ∈ Finset.Ioc H (H + ↑N), c n * (χ n : ℂ) =
      ∑ x : ZMod q, f x * χ x :=
    fun χ => sum_fold_residues H N c (fun x => χ x)
  -- main bound from Part 6
  have hmain := char_sum_bound_primitive q (ZMod.stdAddChar (N := q)) hψ f S hS
  -- convert both sides
  have hLHS : ∑ χ ∈ S, (q : ℝ) / (Nat.totient q : ℝ) *
      ‖∑ n ∈ Finset.Ioc H (H + ↑N), c n * (χ n : ℂ)‖ ^ 2 =
      (1 / (q.totient : ℝ)) * ((q : ℝ) * ∑ χ ∈ S,
        Complex.normSq (∑ x : ZMod q, f x * χ x)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [hchar χ, Complex.normSq_eq_norm_sq]
    field_simp
  have hRHS : ∑ a ∈ (Finset.Icc 1 q).filter (fun a => Nat.Coprime a q),
      ‖∑ n ∈ Finset.Ioc H (H + ↑N), c n * e ((n : ℝ) * ((a : ℝ) / (q : ℝ)))‖ ^ 2 =
      (1 / (q.totient : ℝ)) * ((q.totient : ℝ) * ∑ u : (ZMod q)ˣ,
        Complex.normSq (∑ x : ZMod q, f x * ZMod.stdAddChar (x * (u : ZMod q)))) := by
    rw [← sum_units_eq_sum_coprime H N c,
      ← mul_assoc, one_div, inv_mul_cancel₀ hφ.ne', one_mul]
  rw [hLHS, hRHS]
  apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ 1 / (q.totient : ℝ))
  exact hmain

end
