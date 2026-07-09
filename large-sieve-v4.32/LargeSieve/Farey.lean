/-
# Farey spacing and Dirichlet-character Plancherel

Sorry-free building blocks for the multiplicative large sieve:

* **Farey spacing** — distinct reduced fractions a/q, a'/q' with q, q' ≤ Q are
  separated by at least 1/Q². Elementary number theory (`farey_spacing_Q` and
  the `farey_*` helpers).
* **Plancherel for Dirichlet characters** — the finite-group orthogonality
  identity `∑_χ |∑ χ(a⁻¹) f(a)|² = φ(q) ∑ |f(a)|²` (`plancherel_dirichlet`),
  plus the Gauss-sum norm for prime moduli (`gauss_sum_norm_sq_prime`).

These feed the character→exponential reduction (`LargeSieve.Character.*`) and the
final Gallagher-based sieve (`LargeSieve.Multiplicative`).
-/

import LargeSieve.Additive.ExpSum
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.DirichletCharacter.GaussSum
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

open Complex Real Finset BigOperators
open scoped ComplexOrder

noncomputable section

-- ============================================================
-- Part 1: Farey Fraction Spacing (all sorry-free)
-- ============================================================

/-- Core Farey spacing in ℤ: if aq' ≠ a'q then |aq' - a'q| ≥ 1. -/
theorem farey_int_spacing (a a' : ℤ) (q q' : ℤ)
    (hne : a * q' ≠ a' * q) :
    1 ≤ |a * q' - a' * q| :=
  Int.one_le_abs (sub_ne_zero.mpr hne)

/-- Farey spacing for real-valued fractions:
    If a/q ≠ a'/q' (i.e., aq' ≠ a'q) with q, q' > 0,
    then |a/q - a'/q'| ≥ 1/(q·q'). -/
theorem farey_spacing_real (a a' q q' : ℤ) (hq : 0 < q) (hq' : 0 < q')
    (hne : a * q' ≠ a' * q) :
    1 / ((q : ℝ) * (q' : ℝ)) ≤ |(↑a / ↑q - ↑a' / ↑q' : ℝ)| := by
  have hq_pos : (0 : ℝ) < ↑q := Int.cast_pos.mpr hq
  have hq'_pos : (0 : ℝ) < ↑q' := Int.cast_pos.mpr hq'
  have hqq' : (0 : ℝ) < ↑q * ↑q' := mul_pos hq_pos hq'_pos
  have hq_ne : (q : ℝ) ≠ 0 := ne_of_gt hq_pos
  have hq'_ne : (q' : ℝ) ≠ 0 := ne_of_gt hq'_pos
  -- Rewrite the difference as (aq' - a'q)/(qq')
  have key : (↑a / ↑q - ↑a' / ↑q' : ℝ) = (↑a * ↑q' - ↑a' * ↑q) / (↑q * ↑q') := by
    field_simp
  rw [key, abs_div, abs_of_pos hqq']
  rw [div_le_div_iff_of_pos_right hqq']
  -- Need: 1 ≤ |↑(a * q' - a' * q) : ℝ|
  have h1 : (1 : ℤ) ≤ |a * q' - a' * q| := farey_int_spacing a a' q q' hne
  calc (1 : ℝ) = ↑(1 : ℤ) := by simp
    _ ≤ ↑|a * q' - a' * q| := by exact_mod_cast h1
    _ = |↑(a * q' - a' * q)| := by rw [Int.cast_abs]
    _ = |↑a * ↑q' - ↑a' * ↑q| := by push_cast; ring_nf

/-- Farey spacing with natural number denominators. -/
theorem farey_spacing_nat (a a' : ℤ) (q q' : ℕ) (hq : 0 < q) (hq' : 0 < q')
    (hne : a * ↑q' ≠ a' * ↑q) :
    1 / ((q : ℝ) * (q' : ℝ)) ≤ |(↑a / (q : ℝ) - ↑a' / (q' : ℝ))| := by
  have := farey_spacing_real a a' ↑q ↑q' (Int.natCast_pos.mpr hq) (Int.natCast_pos.mpr hq') hne
  simp only [Int.cast_natCast] at this
  exact this

/-- Key corollary: Farey fractions of order Q are 1/Q²-separated.
    If q, q' ≤ Q and a/q ≠ a'/q', then |a/q - a'/q'| ≥ 1/Q². -/
theorem farey_spacing_Q (a a' : ℤ) (q q' : ℕ) (Q : ℝ)
    (hq : 0 < q) (hq' : 0 < q')
    (hqQ : (q : ℝ) ≤ Q) (hq'Q : (q' : ℝ) ≤ Q)
    (hne : a * ↑q' ≠ a' * ↑q) :
    1 / Q ^ 2 ≤ |(↑a / (q : ℝ) - ↑a' / (q' : ℝ))| := by
  have hQ_pos : 0 < Q := lt_of_lt_of_le (Nat.cast_pos.mpr hq) hqQ
  have h_farey := farey_spacing_nat a a' q q' hq hq' hne
  have hqq'_pos : (0 : ℝ) < ↑q * ↑q' := mul_pos (Nat.cast_pos.mpr hq) (Nat.cast_pos.mpr hq')
  calc 1 / Q ^ 2 = 1 / (Q * Q) := by ring
    _ ≤ 1 / ((q : ℝ) * (q' : ℝ)) := by
        apply div_le_div_of_nonneg_left (zero_le_one) hqq'_pos
        exact mul_le_mul hqQ hq'Q (Nat.cast_nonneg q') (le_of_lt hQ_pos)
    _ ≤ |(↑a / (q : ℝ) - ↑a' / (q' : ℝ))| := h_farey

-- ============================================================
-- Part 2: Farey fractions as a well-separated point set
-- ============================================================

/-- A Farey fraction: a pair (a, q) with 1 ≤ a ≤ q, gcd(a,q) = 1, q ≤ Q. -/
structure FareyFraction (Q : ℕ) where
  a : ℤ
  q : ℕ
  hq_pos : 0 < q
  hq_le : q ≤ Q
  ha_pos : 1 ≤ a
  ha_le : a ≤ ↑q
  hcoprime : Int.gcd a ↑q = 1

/-- The real value of a Farey fraction a/q. -/
def FareyFraction.val {Q : ℕ} (f : FareyFraction Q) : ℝ :=
  (f.a : ℝ) / (f.q : ℝ)

/-- Distinct Farey fractions have aq' ≠ a'q. -/
theorem FareyFraction.distinct_cross {Q : ℕ} (f f' : FareyFraction Q)
    (hne : f.val ≠ f'.val) :
    f.a * ↑f'.q ≠ f'.a * ↑f.q := by
  intro heq
  apply hne
  unfold FareyFraction.val
  have hq_ne : (f.q : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr f.hq_pos)
  have hq'_ne : (f'.q : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr f'.hq_pos)
  rw [div_eq_div_iff hq_ne hq'_ne]
  exact_mod_cast heq

/-- Two distinct Farey fractions of order Q are at least 1/Q²-separated
    in absolute value. -/
theorem farey_well_separated {Q : ℕ} (hQ : 0 < Q)
    (f f' : FareyFraction Q) (hne : f.val ≠ f'.val) :
    1 / (Q : ℝ) ^ 2 ≤ |f.val - f'.val| := by
  unfold FareyFraction.val
  exact farey_spacing_Q f.a f'.a f.q f'.q ↑Q f.hq_pos f'.hq_pos
    (Nat.cast_le.mpr f.hq_le) (Nat.cast_le.mpr f'.hq_le)
    (FareyFraction.distinct_cross f f' hne)

-- ============================================================
-- Part 3: Plancherel identity for Dirichlet characters
-- ============================================================

/-- **Norm-squared expansion**: ‖z‖² = (z * starRingEnd ℂ z).re for z : ℂ.
    This is a standard identity used in the Plancherel proof. -/
theorem norm_sq_eq_mul_conj (z : ℂ) :
    (‖z‖ : ℝ) ^ 2 = (z * starRingEnd ℂ z).re := by
  rw [Complex.mul_conj']
  norm_cast

/-- For a multiplicative character χ valued in ℂ and a unit a,
    star(χ a) = χ⁻¹ a. -/
theorem mulchar_star_apply (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (a : (ZMod q)ˣ) :
    starRingEnd ℂ (χ a) = χ⁻¹ a :=
  MulChar.star_apply' χ a

/-- For a unit b in ZMod q: χ⁻¹(b⁻¹) = χ(b).
    Proof: χ⁻¹(b⁻¹) = (χ(b⁻¹))⁻¹ = (χ(b)⁻¹)⁻¹ = χ(b). -/
theorem mulchar_inv_inv (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (b : (ZMod q)ˣ) :
    χ⁻¹ (b⁻¹ : (ZMod q)ˣ) = χ b := by
  -- χ⁻¹(↑(b⁻¹)) = (χ ↑(b⁻¹))⁻¹ (by inv_apply_eq_inv)
  -- χ ↑(b⁻¹) * χ ↑b = χ(↑(b⁻¹) * ↑b) = χ 1 = 1
  -- So χ ↑(b⁻¹) = (χ ↑b)⁻¹, hence χ⁻¹(↑(b⁻¹)) = (χ ↑b)⁻¹⁻¹ = χ ↑b
  have h_prod : χ ↑(b⁻¹) * χ ↑b = 1 := by
    rw [← map_mul]; simp [Units.inv_mul]
  have h_ne : χ ↑(b⁻¹) ≠ 0 := left_ne_zero_of_mul_eq_one h_prod
  calc χ⁻¹ ↑(b⁻¹)
      = (χ ↑(b⁻¹))⁻¹ := MulChar.inv_apply_eq_inv' χ ↑(b⁻¹)
    _ = χ ↑b := (mul_eq_one_iff_inv_eq₀ h_ne).mp h_prod

/-- Combined helper: conj(χ(a⁻¹)) = χ(a). -/
theorem star_char_inv_eq (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (a : (ZMod q)ˣ) :
    starRingEnd ℂ (χ (a⁻¹ : (ZMod q)ˣ)) = χ a := by
  rw [mulchar_star_apply, mulchar_inv_inv]

/-- Orthogonality lemma in the form needed for Plancherel. -/
lemma sum_char_orthogonality (q : ℕ) [NeZero q]
    [HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod q)ˣ)]
    (a b : (ZMod q)ˣ) :
    ∑ χ : DirichletCharacter ℂ q, χ a * χ ↑(b⁻¹) =
      if a = b then (q.totient : ℂ) else 0 := by
  simp_rw [← map_mul]
  have h_coerce : ∀ χ : DirichletCharacter ℂ q,
      χ (↑a * ↑(b⁻¹) : ZMod q) = χ (↑(a * b⁻¹) : ZMod q) := by
    intro χ; congr 1
  simp_rw [h_coerce]
  rw [DirichletCharacter.sum_characters_eq]
  simp only [Units.val_eq_one, mul_inv_eq_one]

/-- ℂ-valued Plancherel (workhorse). -/
private theorem plancherel_complex (q : ℕ) [NeZero q]
    [HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod q)ˣ)]
    (f : (ZMod q)ˣ → ℂ) :
    (∑ χ : DirichletCharacter ℂ q,
      (starRingEnd ℂ (∑ a : (ZMod q)ˣ, χ (a⁻¹ : (ZMod q)ˣ) * f a)) *
      (∑ a : (ZMod q)ˣ, χ (a⁻¹ : (ZMod q)ˣ) * f a)) =
    (q.totient : ℂ) * ∑ a : (ZMod q)ˣ, starRingEnd ℂ (f a) * f a := by
  simp_rw [map_sum, map_mul, star_char_inv_eq]
  simp_rw [Fintype.sum_mul_sum]
  conv_lhs =>
    arg 2; ext χ; arg 2; ext a; arg 2; ext b
    rw [show χ a * starRingEnd ℂ (f a) * (χ ↑(b⁻¹) * f b) =
        (χ a * χ ↑(b⁻¹)) * (starRingEnd ℂ (f a) * f b) from by ring]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  simp_rw [sum_char_orthogonality]
  simp_rw [ite_mul, zero_mul]
  simp [Finset.sum_ite_eq, Finset.mem_univ, Finset.mul_sum]

theorem plancherel_dirichlet (q : ℕ) [NeZero q]
    [HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod q)ˣ)]
    (f : (ZMod q)ˣ → ℂ) :
    (∑ χ : DirichletCharacter ℂ q,
      Complex.normSq (∑ a : (ZMod q)ˣ, χ (a⁻¹ : (ZMod q)ˣ) * f a) : ℝ) =
    (q.totient : ℝ) * ∑ a : (ZMod q)ˣ, Complex.normSq (f a) := by
  suffices h : (↑(∑ χ : DirichletCharacter ℂ q,
      Complex.normSq (∑ a : (ZMod q)ˣ, χ (a⁻¹ : (ZMod q)ˣ) * f a)) : ℂ) =
    ↑((q.totient : ℝ) * ∑ a : (ZMod q)ˣ, Complex.normSq (f a)) by
    exact_mod_cast h
  push_cast
  simp_rw [Complex.normSq_eq_conj_mul_self]
  exact plancherel_complex q f

/-- **Gauss sum norm bound for prime modulus.**
    For p prime and nontrivial χ mod p: |τ(χ,ψ)|² = p for primitive ψ. -/
theorem gauss_sum_norm_sq_prime (p : ℕ) [Fact (Nat.Prime p)]
    (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1)
    (ψ : AddChar (ZMod p) ℂ) (hψ : ψ.IsPrimitive) :
    Complex.normSq (gaussSum χ ψ) = (p : ℝ) := by
  have hmul : gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹ = (Fintype.card (ZMod p) : ℂ) :=
    gaussSum_mul_gaussSum_eq_card hχ hψ
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  have hstar : star (gaussSum χ ψ) = gaussSum χ⁻¹ ψ⁻¹ := star_gaussSum_eq χ ψ
  have h : (Complex.normSq (gaussSum χ ψ) : ℂ) = (p : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self, starRingEnd_apply, hstar, mul_comm, hmul, hcard]
  exact_mod_cast h

-- ============================================================
-- Part 4: Farey-collection helpers (distinctness + spacing bounds)
-- ============================================================

/-- **Farey-collection bound.**
    The sum of |S(a/q)|² over all Farey fractions of order Q is bounded
    by the additive large sieve. This is the key step connecting the
    double sum ∑_q ∑_a to a single sum over well-separated points.

    The Farey fractions {a/q : 1 ≤ a ≤ q, gcd(a,q)=1, q ≤ Q} are
    1/Q²-separated by farey_spacing_Q, so the additive large sieve gives
    ∑ |S(a/q)|² ≤ (N-1+Q²) · ∑|cₙ|². -/
-- Helper definitions for farey_collection_bound proof
def fareyPairs (Q : ℕ) : Finset (Σ q : ℕ, ℕ) :=
  (Finset.Ioc 0 Q).sigma (fun q => (Finset.Icc 1 q).filter (fun a => Nat.Coprime a q))

lemma farey_double_sum_eq_sigma {Q : ℕ} (f : ℕ → ℕ → ℝ) :
    ∑ q ∈ Finset.Ioc 0 Q, ∑ a ∈ (Finset.Icc 1 q).filter (fun a => Nat.Coprime a q), f q a =
    ∑ p ∈ fareyPairs Q, f p.1 p.2 := by
  rw [fareyPairs, Finset.sum_sigma]

lemma fracDist_ge_of_small_abs {x δ : ℝ} (hx_ne : x ≠ 0)
    (hx_lt : |x| < 1) (h_abs : δ ≤ |x|) (h_comp : δ ≤ 1 - |x|) :
    δ ≤ fracDist x := by
  rw [fracDist_eq_min_fract]
  rcases lt_or_ge x 0 with hx_neg | hx_pos
  · have hx_gt : -1 < x := by linarith [(abs_of_neg hx_neg) ▸ hx_lt]
    have hfloor : ⌊x⌋ = -1 := by
      rw [Int.floor_eq_iff]; constructor
      · exact_mod_cast le_of_lt hx_gt
      · push_cast; linarith
    rw [Int.fract, hfloor]; push_cast
    exact le_min (by linarith [abs_of_neg hx_neg]) (by linarith [abs_of_neg hx_neg])
  · have hx_lt1 : x < 1 := by linarith [(abs_of_nonneg hx_pos) ▸ hx_lt]
    have hfloor : ⌊x⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨hx_pos, hx_lt1⟩
    rw [Int.fract, hfloor]; push_cast; simp only [sub_zero]
    exact le_min (by linarith [abs_of_nonneg hx_pos]) (by linarith [abs_of_nonneg hx_pos])

lemma farey_distinct_values'
    {q₁ q₂ a₁ a₂ : ℕ} (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hcop₁ : Nat.Coprime a₁ q₁) (hcop₂ : Nat.Coprime a₂ q₂)
    (h_ne : (a₁, q₁) ≠ (a₂, q₂)) :
    (a₁ : ℝ) / (q₁ : ℝ) ≠ (a₂ : ℝ) / (q₂ : ℝ) := by
  intro heq
  have h_cross : (a₁ : ℝ) * q₂ = (a₂ : ℝ) * q₁ := by field_simp at heq; linarith
  have h_nat : a₁ * q₂ = a₂ * q₁ := by exact_mod_cast h_cross
  have h_q₁_dvd : q₁ ∣ q₂ := hcop₁.symm.dvd_of_dvd_mul_left ⟨a₂, h_nat.trans (Nat.mul_comm a₂ q₁)⟩
  have h_q₂_dvd : q₂ ∣ q₁ := hcop₂.symm.dvd_of_dvd_mul_left ⟨a₁, h_nat.symm.trans (Nat.mul_comm a₁ q₂)⟩
  have h_qq : q₁ = q₂ := Nat.dvd_antisymm h_q₁_dvd h_q₂_dvd
  have h_aa : a₁ = a₂ := Nat.eq_of_mul_eq_mul_right hq₂ (h_qq ▸ h_nat)
  exact h_ne (Prod.ext h_aa h_qq)

lemma farey_fracDist_bound'
    {Q : ℕ} (hQ : 0 < Q) (p₁ p₂ : Σ _ : ℕ, ℕ)
    (hp₁ : p₁ ∈ fareyPairs Q) (hp₂ : p₂ ∈ fareyPairs Q) (hne : p₁ ≠ p₂) :
    1 / (Q : ℝ) ^ 2 ≤
      fracDist ((p₁.2 : ℝ) / (p₁.1 : ℝ) - (p₂.2 : ℝ) / (p₂.1 : ℝ)) := by
  rw [fareyPairs, Finset.mem_sigma] at hp₁ hp₂
  have hq₁ := (Finset.mem_Ioc.mp hp₁.1).1
  have hq₂ := (Finset.mem_Ioc.mp hp₂.1).1
  have hq₁_le := (Finset.mem_Ioc.mp hp₁.1).2
  have hq₂_le := (Finset.mem_Ioc.mp hp₂.1).2
  have ha₁_mem := Finset.mem_filter.mp hp₁.2
  have ha₂_mem := Finset.mem_filter.mp hp₂.2
  have ha₁_Icc := Finset.mem_Icc.mp ha₁_mem.1
  have ha₂_Icc := Finset.mem_Icc.mp ha₂_mem.1
  set x := (p₁.2 : ℝ) / (p₁.1 : ℝ) - (p₂.2 : ℝ) / (p₂.1 : ℝ)
  have h_pairs_ne : (p₁.2, p₁.1) ≠ (p₂.2, p₂.1) := by
    intro heq; exact hne (Sigma.ext (Prod.mk.inj heq).2 (heq_of_eq (Prod.mk.inj heq).1))
  have hx_ne : x ≠ 0 := sub_ne_zero.mpr
    (farey_distinct_values' hq₁ hq₂ ha₁_mem.2 ha₂_mem.2 h_pairs_ne)
  have h_cross_ne : (p₁.2 : ℤ) * p₂.1 ≠ (p₂.2 : ℤ) * p₁.1 := by
    intro heq; exact hx_ne (sub_eq_zero.mpr (by
      field_simp; linarith [show (p₁.2 : ℝ) * p₂.1 = (p₂.2 : ℝ) * p₁.1 from by exact_mod_cast heq]))
  have h_spacing := farey_spacing_Q (p₁.2 : ℤ) (p₂.2 : ℤ) p₁.1 p₂.1 (Q : ℝ) hq₁ hq₂
    (Nat.cast_le.mpr hq₁_le) (Nat.cast_le.mpr hq₂_le) h_cross_ne
  have h_a₁_le : (p₁.2 : ℝ) / p₁.1 ≤ 1 := by
    rw [div_le_one (Nat.cast_pos.mpr hq₁)]; exact Nat.cast_le.mpr ha₁_Icc.2
  have h_a₂_le : (p₂.2 : ℝ) / p₂.1 ≤ 1 := by
    rw [div_le_one (Nat.cast_pos.mpr hq₂)]; exact Nat.cast_le.mpr ha₂_Icc.2
  have h_a₁_pos : 0 < (p₁.2 : ℝ) / p₁.1 :=
    div_pos (Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one ha₁_Icc.1)) (Nat.cast_pos.mpr hq₁)
  have h_a₂_pos : 0 < (p₂.2 : ℝ) / p₂.1 :=
    div_pos (Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one ha₂_Icc.1)) (Nat.cast_pos.mpr hq₂)
  have hx_bound : |x| < 1 := by rw [abs_lt]; constructor <;> linarith
  have hQ_pos : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ
  have h_comp : 1 / (Q : ℝ) ^ 2 ≤ 1 - |x| := by
    have h1Q : (1 : ℝ) / Q ^ 2 ≤ 1 / Q := by
      have hQ2_pos : (0 : ℝ) < (Q : ℝ) ^ 2 := by positivity
      rw [div_le_div_iff₀ hQ2_pos hQ_pos]
      have hQ1 : (1 : ℝ) ≤ (Q : ℝ) := Nat.one_le_cast.mpr hQ
      nlinarith [sq_nonneg ((Q : ℝ) - 1)]
    suffices h : 1 / (Q : ℝ) ≤ 1 - |x| from le_trans h1Q h
    rcases le_or_gt 0 x with hx_pos | hx_neg
    · rw [abs_of_nonneg hx_pos]
      have : (p₂.2 : ℝ) / p₂.1 ≥ 1 / (Q : ℝ) := by
        rw [ge_iff_le, div_le_div_iff₀ hQ_pos (Nat.cast_pos.mpr hq₂)]
        have : (1 : ℝ) ≤ (p₂.2 : ℝ) := by exact_mod_cast ha₂_Icc.1
        have : (p₂.1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hq₂_le
        nlinarith
      linarith
    · rw [abs_of_neg hx_neg]
      have : (p₁.2 : ℝ) / p₁.1 ≥ 1 / (Q : ℝ) := by
        rw [ge_iff_le, div_le_div_iff₀ hQ_pos (Nat.cast_pos.mpr hq₁)]
        have : (1 : ℝ) ≤ (p₁.2 : ℝ) := by exact_mod_cast ha₁_Icc.1
        have : (p₁.1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hq₁_le
        nlinarith
      linarith
  exact fracDist_ge_of_small_abs hx_ne hx_bound h_spacing h_comp

end
