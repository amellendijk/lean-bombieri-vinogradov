/-
# Large Sieve — Attempt 13: Sorry-free multiplicative large sieve

This file combines:
  - Gallagher's additive large sieve (Attempt12, sorry-free)
  - Character→exponential reduction (Attempt11, sorry-free)
  - Farey spacing (Attempt9, sorry-free)
to produce a FULLY SORRY-FREE multiplicative large sieve inequality:

  ∑_{q≤Q} ∑*_{χ mod q} (q/φ(q)) |∑ cₙχ(n)|² ≤ C_LS·(N+Q²)·∑|cₙ|²

with C_LS = 8π² + 2 ≈ 80.96.

The sharp constant (from Bombieri) is C_LS = 1, but requires Beurling-Selberg
extremal functions (not in Mathlib). Gallagher's 1967 proof avoids this
entirely, at the cost of a larger constant.
-/

import LargeSieve.Additive.Gallagher
import LargeSieve.Character.Reduction

open scoped BigOperators
open Finset

noncomputable section

-- ============================================================
-- Part 1: Gallagher-based Farey collection bound
-- ============================================================

/-- T agrees with expSum: both are ∑ a(n) e(nα) over Icc(M+1, M+N). -/
theorem T_eq_expSum (a : ℤ → ℂ) (M : ℤ) (N : ℕ) (α : ℝ) :
    Gallagher.T a (Finset.Icc (M+1) (M+↑N)) α = expSum a M N α := rfl

/-- Farey fractions a/q with q ≤ Q are in [0,1).
    The case q=1, a=1 maps to fract(1) = 0. All others have a/q ∈ (0,1). -/
def fareyVal (p : ℕ × ℕ) : ℝ := Int.fract ((p.2 : ℝ) / (p.1 : ℝ))

theorem fareyVal_mem_Ico (p : ℕ × ℕ) : fareyVal p ∈ Set.Ico (0:ℝ) 1 :=
  ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

/-- For coprime a, q with 1 ≤ a ≤ q and q ≥ 2, a/q ∈ (0,1) so fract(a/q) = a/q. -/
theorem fareyVal_eq_of_coprime {a q : ℕ} (hq : 2 ≤ q) (ha : 1 ≤ a)
    (haq : a ≤ q) (hcop : Nat.Coprime a q) : fareyVal (q, a) = (a : ℝ) / (q : ℝ) := by
  unfold fareyVal
  simp only
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  have haq_strict : a < q := by
    by_contra h
    push_neg at h
    have heq := Nat.le_antisymm haq h
    subst heq
    simp [Nat.Coprime, Nat.gcd_self] at hcop
    omega
  have h1 : (0 : ℝ) ≤ (a : ℝ) / (q : ℝ) := by positivity
  have h2 : (a : ℝ) / (q : ℝ) < 1 := by
    rw [div_lt_one (by positivity : (0:ℝ) < q)]
    exact Nat.cast_lt.mpr haq_strict
  rw [Int.fract_eq_self.mpr ⟨h1, h2⟩]

/-- For q=1, a=1: fract(1/1) = 0, and e(n·0) = 1 = e(n·1) by periodicity. -/
theorem expSum_at_one_eq_zero (c : ℤ → ℂ) (H : ℤ) (N : ℕ) :
    expSum c H N 1 = expSum c H N 0 := by
  unfold expSum
  congr 1; ext n
  congr 1
  simp [e_int, e_zero, mul_one, mul_zero]

/-- The norm of T(or expSum) at fract(a/q) equals the norm at a/q, since T is 1-periodic. -/
theorem norm_T_fract_eq (a : ℤ → ℂ) (S : Finset ℤ) (x : ℝ) :
    ‖Gallagher.T a S (Int.fract x)‖ = ‖Gallagher.T a S x‖ := by
  have hper := Gallagher.T_periodic a S
  have heq : Gallagher.T a S x = Gallagher.T a S (Int.fract x) := by
    conv_lhs => rw [show x = Int.fract x + ↑⌊x⌋ * 1 from by
      rw [mul_one]; exact (Int.fract_add_floor x).symm]
    have h := hper.sub_int_mul_eq (n := ⌊x⌋) (x := Int.fract x + ↑⌊x⌋ * 1)
    rw [show Int.fract x + ↑⌊x⌋ * 1 - ↑⌊x⌋ * 1 = Int.fract x from by ring] at h
    exact h.symm
  rw [heq]

/-- **Gallagher-based Farey collection bound** (sorry-free).
    Replaces the sharp (N-1+Q²) with C·(N+Q²) where C = 8π²+2. -/
theorem farey_collection_bound_gallagher
    (Q : ℕ) (hQ : 0 < Q) (H : ℤ) (N : ℕ) (hN : 0 < N) (c : ℤ → ℂ) :
    ∑ q ∈ Finset.Ioc 0 Q, ∑ a ∈ (Finset.Icc 1 q).filter (fun a => Nat.Coprime a q),
      ‖expSum c H N ((a : ℝ) / (q : ℝ))‖ ^ 2 ≤
    (8 * Real.pi ^ 2 + 2) * ((↑N : ℝ) + (Q : ℝ) ^ 2) *
      ∑ n ∈ Finset.Icc (H + 1) (H + ↑N), ‖c n‖ ^ 2 := by
  rw [farey_double_sum_eq_sigma]
  set S := fareyPairs Q
  set R := S.card
  by_cases hR0 : R = 0
  · rw [show S = ∅ from Finset.card_eq_zero.mp hR0, Finset.sum_empty]
    apply mul_nonneg (mul_nonneg _ _) _
    · linarith [sq_nonneg Real.pi]
    · have : (1 : ℝ) ≤ (N : ℝ) := Nat.one_le_cast.mpr hN
      linarith [sq_nonneg (Q : ℝ)]
    · exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  · have hR_pos : 0 < R := Nat.pos_of_ne_zero hR0
    have hcard2 : Fintype.card (Fin R) = Fintype.card ↥S := by
      rw [Fintype.card_fin]; exact (Fintype.card_coe S).symm
    let e : Fin R ≃ ↥S := Fintype.equivOfCardEq hcard2
    -- α i = value of i-th Farey fraction
    let α : Fin R → ℝ := fun i =>
      (↑((e i).1 : Σ _ : ℕ, ℕ).2 : ℝ) / (↑((e i).1 : Σ _ : ℕ, ℕ).1 : ℝ)
    have h_sum_eq : ∑ p ∈ S, ‖expSum c H N ((p.2 : ℝ) / (p.1 : ℝ))‖ ^ 2 =
        ∑ i : Fin R, ‖expSum c H N (α i)‖ ^ 2 := by
      rw [← Finset.sum_coe_sort S]
      exact Fintype.sum_equiv e.symm _ _ (fun i => by simp [α])
    rw [h_sum_eq]
    -- β = fract(α), maps to [0,1)
    set β : Fin R → ℝ := fun i => Int.fract (α i)
    -- norms preserved: T(α) = T(fract α) by periodicity
    have hnorm_eq : ∀ i, ‖expSum c H N (α i)‖ = ‖expSum c H N (β i)‖ := by
      intro i; exact (norm_T_fract_eq c _ (α i)).symm
    simp_rw [show ∀ i, ‖expSum c H N (α i)‖ ^ 2 =
        ‖Gallagher.T c (Finset.Icc (H+1) (H+↑N)) (β i)‖ ^ 2 from
      fun i => by rw [hnorm_eq i]; rfl]
    -- Set δ = 1/Q²
    set δ := (1:ℝ) / (Q : ℝ) ^ 2
    have hδ_pos : 0 < δ := by positivity
    have hδ_le : δ ≤ 1 := by
      rw [div_le_one (by positivity : (0:ℝ) < (Q:ℝ)^2)]
      have : (1 : ℝ) ≤ (Q : ℝ) := Nat.one_le_cast.mpr hQ; nlinarith
    -- Extract Farey membership info: q = fst, a = snd
    have mem_info : ∀ i : Fin R,
        0 < (↑(e i) : (Σ _ : ℕ, ℕ)).fst ∧ (↑(e i) : (Σ _ : ℕ, ℕ)).fst ≤ Q ∧
        1 ≤ (↑(e i) : (Σ _ : ℕ, ℕ)).snd ∧ (↑(e i) : (Σ _ : ℕ, ℕ)).snd ≤ (↑(e i) : (Σ _ : ℕ, ℕ)).fst ∧
        Nat.Coprime (↑(e i) : (Σ _ : ℕ, ℕ)).snd (↑(e i) : (Σ _ : ℕ, ℕ)).fst := by
      intro i
      have hm := (e i).2
      change ↑(e i) ∈ fareyPairs Q at hm
      rw [fareyPairs, Finset.mem_sigma] at hm
      have hq := Finset.mem_Ioc.mp hm.1
      have ha := Finset.mem_filter.mp hm.2
      have haIcc := Finset.mem_Icc.mp ha.1
      exact ⟨hq.1, hq.2, haIcc.1, haIcc.2, ha.2⟩
    -- For q ≥ 2, coprime a ≤ q implies a < q, so a/q ∈ (0,1) and fract = id
    have fract_id : ∀ i : Fin R, 2 ≤ (e i).1.fst →
        Int.fract (α i) = α i := by
      intro i hq2
      have ⟨_, _, ha1, haq, hcop⟩ := mem_info i
      have ha_lt : (e i).1.snd < (e i).1.fst := by
        rcases Nat.lt_or_ge (e i).1.snd (e i).1.fst with h | h
        · exact h
        · exfalso; have := Nat.le_antisymm haq h; rw [this] at hcop
          simp [Nat.Coprime, Nat.gcd_self] at hcop; omega
      have h0 : (0 : ℝ) ≤ α i := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      have h1 : α i < 1 := by
        change (↑(e i).1.snd : ℝ) / (↑(e i).1.fst : ℝ) < 1
        rw [div_lt_one (Nat.cast_pos.mpr (by omega : 0 < (e i).1.fst))]
        exact Nat.cast_lt.mpr ha_lt
      exact Int.fract_eq_self.mpr ⟨h0, h1⟩
    -- For q = 1, a = 1, fract(1) = 0
    have fract_one_val : ∀ i : Fin R, (e i).1.fst = 1 →
        Int.fract (α i) = 0 := by
      intro i hq1
      have ⟨_, _, ha1, haq, _⟩ := mem_info i
      have ha_eq : (e i).1.snd = 1 := Nat.le_antisymm (hq1 ▸ haq) ha1
      show Int.fract ((↑(e i).1.snd : ℝ) / (↑(e i).1.fst : ℝ)) = 0
      rw [ha_eq, hq1]; simp [Int.fract_one]
    -- Value ≥ 1/Q when q ≥ 2
    have val_ge_inv_Q : ∀ i : Fin R, 2 ≤ (e i).1.fst →
        (1:ℝ) / (Q : ℝ) ≤ α i := by
      intro i hq2
      have ⟨_, hqQ, ha1, _, _⟩ := mem_info i
      change (1:ℝ) / (Q : ℝ) ≤ (↑(e i).1.snd : ℝ) / (↑(e i).1.fst : ℝ)
      rw [div_le_div_iff₀ (by positivity : (0:ℝ) < Q)
        (Nat.cast_pos.mpr (by omega : 0 < (e i).1.fst))]
      have : (1 : ℝ) ≤ (e i).1.snd := by exact_mod_cast ha1
      have : ((e i).1.fst : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hqQ
      nlinarith
    -- δ ≤ 1/Q (since Q ≥ 1)
    have hδ_le_invQ : δ ≤ 1 / (Q : ℝ) := by
      rw [div_le_div_iff₀ (by positivity : (0:ℝ) < (Q:ℝ)^2) (by positivity : (0:ℝ) < Q)]
      have : (1:ℝ) ≤ Q := Nat.one_le_cast.mpr hQ; nlinarith [sq_nonneg ((Q:ℝ) - 1)]
    -- Separation of β values
    have hsep : ∀ r s, r ≠ s → δ ≤ |β r - β s| := by
      intro r s hrs
      have hne : (e r).1 ≠ (e s).1 := by
        intro heq
        have := e.injective (Subtype.ext heq)
        exact hrs this
      have ⟨hq₁, hq₁Q, ha₁, haq₁, hcop₁⟩ := mem_info r
      have ⟨hq₂, hq₂Q, ha₂, haq₂, hcop₂⟩ := mem_info s
      set q₁ := (e r).1.fst
      set a₁ := (e r).1.snd
      set q₂ := (e s).1.fst
      set a₂ := (e s).1.snd
      by_cases hq₁_one : q₁ = 1
      · -- q₁ = 1 → β r = 0
        have hβr : β r = 0 := fract_one_val r hq₁_one
        rw [hβr, zero_sub, abs_neg]
        -- q₂ must be ≥ 2 (otherwise both are (1,1), contradicting distinctness)
        have hq₂_ge2 : 2 ≤ q₂ := by
          rcases Nat.lt_or_ge q₂ 2 with h | h
          · exfalso
            have hq₂_one : q₂ = 1 := by omega
            have ha₁_eq : a₁ = 1 := Nat.le_antisymm (hq₁_one ▸ haq₁) ha₁
            have ha₂_eq : a₂ = 1 := Nat.le_antisymm (hq₂_one ▸ haq₂) ha₂
            apply hne
            exact Sigma.ext (hq₁_one.trans hq₂_one.symm) (heq_of_eq (ha₁_eq.trans ha₂_eq.symm))
          · exact h
        have hβs : β s = α s := fract_id s hq₂_ge2
        rw [hβs]
        have : α s ≥ 1 / (Q : ℝ) := val_ge_inv_Q s hq₂_ge2
        have hα_pos : 0 < α s := by linarith [show (0:ℝ) < 1 / (Q:ℝ) from by positivity]
        rw [abs_of_pos hα_pos]
        linarith
      · by_cases hq₂_one : q₂ = 1
        · -- q₂ = 1 → β s = 0
          have hβs : β s = 0 := fract_one_val s hq₂_one
          rw [hβs, sub_zero]
          have hq₁_ge2 : 2 ≤ q₁ := by omega
          have hβr : β r = α r := fract_id r hq₁_ge2
          rw [hβr]
          have : α r ≥ 1 / (Q : ℝ) := val_ge_inv_Q r hq₁_ge2
          have hα_pos : 0 < α r := by linarith [show (0:ℝ) < 1 / (Q:ℝ) from by positivity]
          rw [abs_of_pos hα_pos]
          linarith
        · -- Both q ≥ 2: fract is identity, use classical Farey spacing
          have hq₁_ge2 : 2 ≤ q₁ := by omega
          have hq₂_ge2 : 2 ≤ q₂ := by omega
          have hβr : β r = α r := fract_id r hq₁_ge2
          have hβs : β s = α s := fract_id s hq₂_ge2
          rw [hβr, hβs]
          -- After fract is identity, α r = a₁/q₁, α s = a₂/q₂
          -- Distinct sigma pairs → distinct (a,q) pairs
          have h_pairs_ne : (a₁, q₁) ≠ (a₂, q₂) := by
            intro heq
            apply hne
            exact Sigma.ext (Prod.ext_iff.mp heq).2 (heq_of_eq (Prod.ext_iff.mp heq).1)
          have h_cross_ne : (a₁ : ℤ) * q₂ ≠ (a₂ : ℤ) * q₁ := by
            intro heq
            have hval_eq : (a₁ : ℝ) / q₁ = (a₂ : ℝ) / q₂ := by
              field_simp
              linarith [show (a₁ : ℝ) * q₂ = (a₂ : ℝ) * q₁ from by exact_mod_cast heq]
            exact farey_distinct_values' hq₁ hq₂ hcop₁ hcop₂ h_pairs_ne hval_eq
          have hsp := farey_spacing_Q (a₁ : ℤ) (a₂ : ℤ) q₁ q₂ (Q : ℝ) hq₁ hq₂
            (Nat.cast_le.mpr hq₁Q) (Nat.cast_le.mpr hq₂Q) h_cross_ne
          -- hsp uses ℕ→ℤ→ℝ casts; goal uses ℕ→ℝ casts. They agree.
          simp only [Int.cast_natCast] at hsp
          exact hsp
    -- Apply Gallagher
    have hβ_range : ∀ r, β r ∈ Set.Ico (0:ℝ) 1 :=
      fun r => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
    have h_gall := Gallagher.gallagher_large_sieve β hδ_pos hδ_le hβ_range hsep c H N hN
    have hδ_inv : δ⁻¹ = (Q : ℝ) ^ 2 := by
      show (1 / (Q : ℝ) ^ 2)⁻¹ = _; rw [one_div, inv_inv]
    rw [hδ_inv] at h_gall
    exact h_gall

-- ============================================================
-- Part 2: Sorry-free multiplicative large sieve
-- ============================================================

/-- **Sorry-free multiplicative large sieve for primitive characters.**

    ∑_{q≤Q} ∑*_{χ mod q} (q/φ(q)) |∑ cₙχ(n)|² ≤ C_LS·(N+Q²)·∑|cₙ|²

    where C_LS = 8π² + 2. -/
theorem multiplicative_large_sieve_gallagher
    (Q : ℝ) (hQ : 1 ≤ Q) (H : ℤ) (N : ℕ) (hN : 0 < N) (c : ℤ → ℂ)
    (S : (q : ℕ) → Finset (DirichletCharacter ℂ q))
    (hS : ∀ q, ∀ χ ∈ S q, DirichletCharacter.IsPrimitive χ) :
    ∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊,
      ∑ χ ∈ S q,
        (q : ℝ) / (Nat.totient q : ℝ) *
          ‖∑ n ∈ Finset.Ioc H (H + ↑N), c n * (χ n : ℂ)‖ ^ 2 ≤
    (8 * Real.pi ^ 2 + 2) * ((↑N : ℝ) + Q ^ 2) *
      ∑ n ∈ Finset.Ioc H (H + ↑N), ‖c n‖ ^ 2 := by
  have h_Ioc_eq : Finset.Ioc H (H + ↑N) = Finset.Icc (H + 1) (H + ↑N) := by
    ext n; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  -- Step 1: per-q bound (from Attempt11, sorry-free)
  have h_per_q : ∀ q ∈ Finset.Ioc 0 ⌊Q⌋₊,
      ∑ χ ∈ S q, (q : ℝ) / (Nat.totient q : ℝ) *
        ‖∑ n ∈ Finset.Ioc H (H + ↑N), c n * (χ n : ℂ)‖ ^ 2 ≤
      ∑ a ∈ (Finset.Icc 1 q).filter (fun a => Nat.Coprime a q),
        ‖∑ n ∈ Finset.Ioc H (H + ↑N), c n * e ((n : ℝ) * ((a : ℝ) / (q : ℝ)))‖ ^ 2 := by
    intro q hq
    have hq_pos : 0 < q := (Finset.mem_Ioc.mp hq).1
    haveI : NeZero q := ⟨Nat.pos_iff_ne_zero.mp hq_pos⟩
    haveI : NeZero (Monoid.exponent (ZMod q)ˣ) :=
      ⟨Monoid.exponent_ne_zero_of_finite⟩
    exact character_sum_le_exp_sum_primitive q H N c (S q) (hS q)
  -- Step 2: apply Gallagher-based Farey collection bound
  have hQfloor_pos : 0 < ⌊Q⌋₊ := Nat.floor_pos.mpr hQ
  have h_farey := farey_collection_bound_gallagher ⌊Q⌋₊ hQfloor_pos H N hN c
  have h_farey' : ∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊,
      ∑ a ∈ (Finset.Icc 1 q).filter (fun a => Nat.Coprime a q),
        ‖∑ n ∈ Finset.Ioc H (H + ↑N), c n * e (↑n * (↑a / ↑q))‖ ^ 2 ≤
    (8 * Real.pi ^ 2 + 2) * ((↑N : ℝ) + (⌊Q⌋₊ : ℝ) ^ 2) *
      ∑ n ∈ Finset.Ioc H (H + ↑N), ‖c n‖ ^ 2 := by
    simp_rw [h_Ioc_eq]
    simp only [expSum] at h_farey
    exact h_farey
  -- Step 3: ⌊Q⌋₊ ≤ Q so (⌊Q⌋₊)² ≤ Q²
  have h_bound : (8 * Real.pi ^ 2 + 2) * ((↑N : ℝ) + (⌊Q⌋₊ : ℝ) ^ 2) ≤
      (8 * Real.pi ^ 2 + 2) * ((↑N : ℝ) + Q ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ (by linarith [sq_nonneg Real.pi])
    have h1 : (⌊Q⌋₊ : ℝ) ≤ Q := Nat.floor_le (le_trans (by norm_num : (0:ℝ) ≤ 1) hQ)
    have h2 : (⌊Q⌋₊ : ℝ) ^ 2 ≤ Q ^ 2 := sq_le_sq' (by linarith) h1
    linarith
  have h_nonneg : (0 : ℝ) ≤ ∑ n ∈ Finset.Ioc H (H + ↑N), ‖c n‖ ^ 2 :=
    Finset.sum_nonneg (fun n _ => by positivity)
  calc ∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊, ∑ χ ∈ S q,
        (q : ℝ) / (Nat.totient q : ℝ) *
          ‖∑ n ∈ Finset.Ioc H (H + ↑N), c n * (χ n : ℂ)‖ ^ 2
      ≤ ∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊,
          ∑ a ∈ (Finset.Icc 1 q).filter (fun a => Nat.Coprime a q),
            ‖∑ n ∈ Finset.Ioc H (H + ↑N), c n * e (↑n * (↑a / ↑q))‖ ^ 2 :=
        Finset.sum_le_sum h_per_q
    _ ≤ (8 * Real.pi ^ 2 + 2) * ((↑N : ℝ) + (⌊Q⌋₊ : ℝ) ^ 2) *
          ∑ n ∈ Finset.Ioc H (H + ↑N), ‖c n‖ ^ 2 := h_farey'
    _ ≤ (8 * Real.pi ^ 2 + 2) * ((↑N : ℝ) + Q ^ 2) *
          ∑ n ∈ Finset.Ioc H (H + ↑N), ‖c n‖ ^ 2 :=
        mul_le_mul_of_nonneg_right h_bound h_nonneg

-- Verification
#print axioms multiplicative_large_sieve_gallagher

end
