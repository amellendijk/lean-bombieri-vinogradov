import Mathlib
import Architect
import BV.Delta
import BV.Axioms

open ArithmeticFunction BV ProofData DirichletCharacter
open scoped Moebius BV zeta

/-! ## Type II sums: the flat part $\Lambda^\flat$ -/

/-- $S_r(y, \xi) := \left|\sum_{n \le y} \Lambda_r^\flat(n)\,\xi(n)\right|$ -/
@[blueprint (latexEnv := "definition") (statement := /--
$$S_r(y, \xi) := \left|\sum_{n \le y} \Lambda_r^\flat(n)\,\xi(n)\right|$$
-/)]
noncomputable def S [ProofData] {q : ℕ} (r : ℕ) (y : ℝ) (ξ : DirichletCharacter ℂ q) : ℝ :=
    ‖summatory (fun n ↦ onCoprime r Λ♭ n * ξ n) y‖

-- TODO: Figure out how we want to handle C here: ideally we don't have to pass it explicitly every time.
-- TODO: We're using Nat.Icc while the definition of T is left-open. Consider if we want to define and use Nat.Ioc instead
/-- $T_r(x, Q) := \sum_{(\log x)^C < d \le Q/r} \frac{1}{\varphi(d)} \sum_{\xi \pmod{d}}^* \max_{\sqrt{x} \le y \le x} S_r(y, \xi)$ -/
@[blueprint (latexEnv := "definition") (statement := /--
$$T_r(x, Q) := \sum_{(\log x)^C < d \le Q/r} \frac{1}{\varphi(d)} \sumstar_{\xi \pmod{d}} \max_{\sqrt{x} \le y \le x} S_r(y, \xi)$$
-/) (uses := [S])]
noncomputable def T [ProofData] (C : ℝ) (r : ℕ) (Q : ℝ) : ℝ :=
  open Classical in
    ∑ d ∈ Nat.Icc ((Real.log x)^C) (Q/r), (d.totient : ℝ)⁻¹ * ∑ ξ : DirichletCharacter ℂ d with ξ.IsPrimitive, maxy (fun y ↦ S r y ξ)

/-! ### Reduction to character sums -/

/-- The conductor of a Dirichlet character is unchanged when lifting to a multiple of its level.
(This is `DirichletCharacter.conductor_changeLevel` in newer Mathlib, not available here.) -/
lemma conductor_changeLevel_eq {R : Type*} [CommMonoidWithZero R] {n m : ℕ} [NeZero n] [NeZero m]
    (hm : n ∣ m) (ξ : DirichletCharacter R n) :
    (changeLevel hm ξ).conductor = ξ.conductor := by
  have h1 : (changeLevel hm ξ).conductor ∣ ξ.conductor := by
    have hfac : (changeLevel hm ξ).FactorsThrough ξ.conductor :=
      ⟨dvd_trans ξ.conductor_dvd_level hm, ξ.primitiveCharacter, by
        rw [changeLevel_trans (χ := ξ.primitiveCharacter) (hm := ξ.conductor_dvd_level) (hd := hm),
          changeLevel_primitiveCharacter]⟩
    exact (changeLevel hm ξ).conductor_dvd_of_mem_conductorSet (NeZero.ne m) hfac
  refine Nat.dvd_antisymm h1 ?_
  set c := (changeLevel hm ξ).conductor with hc
  have hcn : c ∣ n := dvd_trans h1 ξ.conductor_dvd_level
  obtain ⟨hcm, ψ, hψ⟩ := factorsThrough_conductor (changeLevel hm ξ)
  have hξeq : ξ = changeLevel hcn ψ := by
    apply changeLevel_injective hm
    rw [← changeLevel_trans]
    exact hψ
  exact ξ.conductor_dvd_of_mem_conductorSet (NeZero.ne n) ⟨hcn, ψ, hξeq⟩

/-- For `d ∣ q`, the Dirichlet characters mod `q` of conductor exactly `d` are precisely the
`changeLevel` images of the primitive characters mod `d`.  This is the "intermediate result without
the nonprincipal assumption" underlying `character_sum_by_conductor`. -/
theorem sum_conductor_fiber {R : Type*} [AddCommMonoid R] {q : ℕ} [NeZero q]
    (f : DirichletCharacter ℂ q → R) {d : ℕ} (hd : d ∣ q) :
  open Classical in
    ∑ χ : DirichletCharacter ℂ q with χ.conductor = d, f χ =
      ∑ ξ : DirichletCharacter ℂ d with ξ.IsPrimitive, f (ξ.changeLevel hd) := by
  classical
  have hd0 : d ≠ 0 := by rintro rfl; exact (NeZero.ne q) (Nat.eq_zero_of_zero_dvd hd)
  haveI : NeZero d := ⟨hd0⟩
  have hset : (Finset.univ.filter (fun ξ : DirichletCharacter ℂ d => ξ.IsPrimitive)).image
        (fun ξ => ξ.changeLevel hd)
      = Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.conductor = d) := by
    ext χ
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨ξ, hξ, rfl⟩
      rw [conductor_changeLevel_eq hd ξ]
      exact (DirichletCharacter.isPrimitive_def ξ).mp hξ
    · intro h
      subst h
      exact ⟨χ.primitiveCharacter, DirichletCharacter.primitiveCharacter_isPrimitive χ,
        DirichletCharacter.changeLevel_primitiveCharacter χ⟩
  rw [← hset, Finset.sum_image
    (fun a _ b _ h => DirichletCharacter.changeLevel_injective hd h)]

@[blueprint (latexEnv := "lemma") (statement := /--
This is a standard result. Let $f$ be a function from Dirichlet characters. Then
$$\sum_{\substack{\chi \pmod{q} \\ \chi \ne \chi_0}} f(\chi) = \sum_{\substack{d \mid q \\ d > 1}} \sumstar_{\xi \pmod{d}} f(1_{(n,q)=1}\xi)$$
Note the principal character $\chi_0$ corresponds to the (primitive) trivial character mod $1$, so
it is excluded on the right by the condition $d > 1$.
-/)]
theorem character_sum_by_conductor {R : Type*} [AddCommMonoid R] {q : ℕ} [NeZero q]
    (f : DirichletCharacter ℂ q → R) :
  open Classical in
    ∑ χ : DirichletCharacter ℂ q with χ ≠ 1, f χ =
      ∑ d ∈ (q.divisors.filter (· ≠ 1)).attach,
        ∑ ξ : DirichletCharacter ℂ d with ξ.IsPrimitive,
          f (ξ.changeLevel (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp d.2).1)) := by
  classical
  -- A character is nonprincipal iff its conductor is `> 1`; conductors divide `q`.
  have hmaps : ∀ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
      χ.conductor ∈ q.divisors.filter (· ≠ 1) := by
    intro χ hχ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hχ ⊢
    refine ⟨Nat.mem_divisors.mpr ⟨χ.conductor_dvd_level, NeZero.ne q⟩, ?_⟩
    exact fun h => hχ ((DirichletCharacter.eq_one_iff_conductor_eq_one (NeZero.ne q)).mpr h)
  -- On the fibre over `n ≠ 1`, the constraint `χ ≠ 1` is automatic.
  have hfib : ∀ n : ℕ, n ≠ 1 →
      (Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)).filter
          (fun χ => χ.conductor = n)
        = Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.conductor = n) := by
    intro n hn
    ext χ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨fun he => hn (h ▸ (DirichletCharacter.eq_one_iff_conductor_eq_one (NeZero.ne q)).mp he),
        h⟩
  -- Group the left-hand sum by conductor.
  have hLHS : ∑ χ : DirichletCharacter ℂ q with χ ≠ 1, f χ =
      ∑ n ∈ q.divisors.filter (· ≠ 1),
        ∑ χ : DirichletCharacter ℂ q with χ.conductor = n, f χ := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps f]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [hfib n (Finset.mem_filter.mp hn).2]
  -- Rewrite the right-hand sum, using the fibre bijection and reindexing `attach`.
  have hRHS : (∑ d ∈ (q.divisors.filter (· ≠ 1)).attach,
        ∑ ξ : DirichletCharacter ℂ d with ξ.IsPrimitive,
          f (ξ.changeLevel (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp d.2).1))) =
      ∑ n ∈ q.divisors.filter (· ≠ 1),
        ∑ χ : DirichletCharacter ℂ q with χ.conductor = n, f χ := by
    rw [Finset.sum_congr rfl (fun d _ => (sum_conductor_fiber f
      (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp d.2).1)).symm)]
    rw [Finset.sum_attach (q.divisors.filter (· ≠ 1))
      (fun n => ∑ χ : DirichletCharacter ℂ q with χ.conductor = n, f χ)]
  rw [hLHS]
  exact hRHS.symm

/-- If `q` is coprime to `n`, restricting to coprimality with `r` or with `r * q` agree at `n`. -/
lemma onCoprime_mul_right_eq {R : Type*} [Zero R] {f : ℕ → R} {r q n : ℕ} (h : q.Coprime n) :
    onCoprime r f n = onCoprime (r * q) f n := by
  simp only [onCoprime_apply, Nat.coprime_mul_iff_left, and_iff_left h]

/-- Casting a unit `a : ZMod q` down to `ZMod d` for `d ∣ q` yields a unit. -/
lemma isUnit_cast_of_dvd {q d : ℕ} (hdq : d ∣ q) {a : ZMod q} (ha : IsUnit a) :
    IsUnit (a.cast : ZMod d) := by
  rw [← ZMod.castHom_apply (h := hdq) (R := ZMod d) a]
  exact ha.map (ZMod.castHom hdq (ZMod d))

/-- Casting `a : ZMod q` down through `ZMod d` and then `ZMod e` agrees with casting directly,
for `e ∣ d ∣ q`. -/
lemma cast_cast_of_dvd {q d e : ℕ} (hed : e ∣ d) (hdq : d ∣ q) (a : ZMod q) :
    ((a.cast : ZMod d).cast : ZMod e) = (a.cast : ZMod e) := by
  rw [show (a.cast : ZMod d) = ZMod.castHom hdq (ZMod d) a from (ZMod.castHom_apply a).symm,
    show ((ZMod.castHom hdq (ZMod d) a).cast : ZMod e)
        = ZMod.castHom hed (ZMod e) (ZMod.castHom hdq (ZMod d) a) from (ZMod.castHom_apply _).symm,
    ← RingHom.comp_apply, ZMod.castHom_comp, ZMod.castHom_apply]

/-- The key change-of-level identity: lifting a primitive character `ξ` mod `e` to level `d`
(for `e ∣ d ∣ q`) does not change the summand `star (χ a) * ∑ χ(n) g(n)`, provided `g` is
supported on integers coprime to `q`. -/
lemma changeLevel_summand_eq {q : ℕ} {a : ZMod q} (ha : IsUnit a) {g : ℕ → ℝ}
    (hg : ∀ n, g n ≠ 0 → q.Coprime n) {x : ℝ} {d e : ℕ}
    (hed : e ∣ d) (hdq : d ∣ q) (ξ : DirichletCharacter ℂ e) :
    star ((DirichletCharacter.changeLevel hed ξ) (a.cast : ZMod d))
        * summatory (fun n : ℕ => (DirichletCharacter.changeLevel hed ξ) ↑n * ↑(g n)) x
    = star (ξ (a.cast : ZMod e)) * summatory (fun n : ℕ => ξ ↑n * ↑(g n)) x := by
  have hPartA : (DirichletCharacter.changeLevel hed ξ) (a.cast : ZMod d) = ξ (a.cast : ZMod e) := by
    obtain ⟨u, hu⟩ := isUnit_cast_of_dvd hdq ha
    rw [← hu, DirichletCharacter.changeLevel_eq_cast_of_dvd ξ hed u, hu, cast_cast_of_dvd hed hdq]
  have hPartB : (fun n : ℕ => (DirichletCharacter.changeLevel hed ξ) ↑n * (↑(g n) : ℂ))
      = (fun n : ℕ => ξ ↑n * ↑(g n)) := by
    funext n
    by_cases hgn : g n = 0
    · simp [hgn]
    · have hdn : d.Coprime n := (hg n hgn).coprime_dvd_left hdq
      obtain ⟨v, hv⟩ := (ZMod.isUnit_iff_coprime n d).mpr hdn.symm
      have : (DirichletCharacter.changeLevel hed ξ) (n : ZMod d) = ξ (n : ZMod e) := by
        rw [← hv, DirichletCharacter.changeLevel_eq_cast_of_dvd ξ hed v, hv,
          ← ZMod.castHom_apply (h := hed) (R := ZMod e), map_natCast]
      rw [this]
  rw [hPartA, hPartB]

open Classical in
/-- The inner sum over primitive characters mod `e` appearing in the Möbius decomposition. -/
noncomputable def GinnerTerm {q : ℕ} (a : ZMod q) (g : ℕ → ℝ) (x : ℝ) (e : ℕ) : ℂ :=
  ∑ ξ : DirichletCharacter ℂ e with ξ.IsPrimitive,
    star (ξ (a.cast : ZMod e)) * summatory (fun n : ℕ => ξ ↑n * ↑(g n)) x

open Classical in
/-- `φ(d) Δ_g(x; d, a)` equals the sum over divisors `i ∣ d` of `GinnerTerm` (with the `i = 1`
contribution removed). This is the conductor-grouping of `Delta_eq_sum_char`. -/
lemma totient_mul_Delta_eq {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) {g : ℕ → ℝ}
    (hg : ∀ n, g n ≠ 0 → q.Coprime n) {x : ℝ} {d : ℕ} (hdq : d ∣ q) :
    (d.totient : ℂ) * ↑(Δ_[g](x; d, a.cast))
      = ∑ i ∈ d.divisors, if i = 1 then 0 else GinnerTerm a g x i := by
  classical
  have hd0 : d ≠ 0 := fun h => (NeZero.ne q) (Nat.eq_zero_of_zero_dvd (h ▸ hdq))
  haveI : NeZero d := ⟨hd0⟩
  have hφ : (d.totient : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (NeZero.pos d)).ne'
  have hDelta := Delta_eq_sum_char (𝕜 := ℝ) (f := g) (y := x) (q := d)
    (a := (a.cast : ZMod d)) (isUnit_cast_of_dvd hdq ha)
  simp only [Complex.coe_algebraMap] at hDelta
  rw [hDelta, ← mul_assoc, mul_inv_cancel₀ hφ, one_mul]
  -- Commute the summatory product to match `GinnerTerm`'s convention.
  have horder : ∀ χ : DirichletCharacter ℂ d,
      summatory (fun n : ℕ => (↑(g n) : ℂ) * χ ↑n) x
        = summatory (fun n : ℕ => χ ↑n * ↑(g n)) x := by
    intro χ; congr 1; funext n; rw [mul_comm]
  simp_rw [horder]
  rw [← Finset.sum_filter]
  rw [character_sum_by_conductor (q := d)
    (f := fun χ : DirichletCharacter ℂ d => star (χ (a.cast : ZMod d)) *
      summatory (fun n : ℕ => χ ↑n * ↑(g n)) x)]
  -- Rewrite each conductor-fibre summand via the change-of-level identity.
  trans (∑ e ∈ (d.divisors.filter (· ≠ 1)).attach, GinnerTerm a g x (e : ℕ))
  · apply Finset.sum_congr rfl
    intro e _
    have hed : (e : ℕ) ∣ d := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp e.2).1
    rw [GinnerTerm]
    apply Finset.sum_congr rfl
    intro ξ _
    exact changeLevel_summand_eq ha hg hed hdq ξ
  trans (∑ e ∈ d.divisors.filter (· ≠ 1), GinnerTerm a g x e)
  · exact Finset.sum_attach _ _
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : i = 1 <;> simp [h]

@[blueprint (latexEnv := "lemma") (statement := /--
Let $f$ be an arithmetic function. For $r \le x$, $q > 1$ and $(a, q) = 1$,
$$\sumstar_{\xi \pmod{q}} \bar\xi(a) \sum_{n \le y} \xi(n) f_r(n) = \sum_{d \mid q} \mu(q/d)\,\varphi(d)\,\Delta_{f_{rq}}(y;\, d,\, a)$$
-/) (proof := /--
Fix $P \in \N$ with $q \mid P$. Define $F_P$ and $G_P$ on divisors of $P$ by
\begin{align*}
F_P(q) &:= \sum_{\chi \ne \chi_0 \pmod{q}} \bar\chi(a) \sum_{n \le y} \chi(n) f_{rP}(n) = \Delta_{f_{rP}}(y;\, q,\, a), \\
G_P(d) &:= \sumstar_{\xi \pmod{d}} \bar\xi(a) \sum_{n \le y} \xi(n) f_{rP}(n) \quad (d > 1),\quad G_P(1) = 0.
\end{align*}
Since every non-principal character mod $q$ factors through a unique primitive character, $F_P(q) = \sum_{d \mid q} G_P(d)$.
By Möbius inversion,
$$G_P(q) = \sum_{d \mid q} \mu(q/d)\, F_P(d) = \sum_{d \mid q} \mu(q/d)\, \Delta_{f_{rP}}(y;\, d,\, a).$$
Set $P = q$ to conclude.
-/) (uses := [character_sum_by_conductor])]
theorem character_sum_Mobius (f : ArithmeticFunction ℝ) {r q : ℕ} {x : ℝ} {a : ZMod q} (hq : 1 < q) (ha : IsUnit a) :
  open Classical in
    ∑ ξ : DirichletCharacter ℂ q with ξ.IsPrimitive, star (ξ a) * summatory (fun n ↦ ξ n * onCoprime r f n) x =
      ∑ p ∈ q.divisorsAntidiagonal, μ p.2 * p.1.totient * Δ_[onCoprime (r*q) f](x; p.1, a.cast) := by
  classical
  haveI : NeZero q := ⟨by omega⟩
  set g : ℕ → ℝ := onCoprime (r * q) ⇑f with hg_def
  have hgsupp : ∀ n, g n ≠ 0 → q.Coprime n := by
    intro n hn
    rw [hg_def, onCoprime_apply] at hn
    split_ifs at hn with h
    · exact h.coprime_dvd_left (dvd_mul_left q r)
    · exact absurd rfl hn
  -- Step 1: rewrite the LHS as `GinnerTerm a g x q`.
  have hLHS : (∑ ξ : DirichletCharacter ℂ q with ξ.IsPrimitive,
      star (ξ a) * summatory (fun n : ℕ => ξ ↑n * ↑(onCoprime r ⇑f n)) x) = GinnerTerm a g x q := by
    rw [GinnerTerm]
    apply Finset.sum_congr rfl
    intro ξ _
    rw [ZMod.cast_id q a]
    have hfun : (fun n : ℕ => ξ ↑n * (↑(onCoprime r ⇑f n) : ℂ))
        = (fun n : ℕ => ξ ↑n * ↑(g n)) := by
      funext n
      by_cases hξ : ξ (↑n) = 0
      · simp [hξ]
      · have hu : IsUnit (↑n : ZMod q) := by
          by_contra hnu; exact hξ (ξ.map_nonunit hnu)
        have hqn : q.Coprime n := ((ZMod.isUnit_iff_coprime n q).mp hu).symm
        rw [hg_def, ← onCoprime_mul_right_eq hqn]
    rw [hfun]
  rw [hLHS]
  -- Step 2: Möbius inversion over divisors of `q`.
  set Gp : ℕ → ℂ := fun i => if i ∣ q ∧ i ≠ 1 then GinnerTerm a g x i else 0 with hGp_def
  have hmoeb := (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq (f := Gp)
      (g := fun n => ∑ i ∈ n.divisors, Gp i)).mp (fun n _ => rfl) q (by omega)
  have hGpq : Gp q = GinnerTerm a g x q := by
    simp only [hGp_def]; rw [if_pos ⟨dvd_refl q, by omega⟩]
  rw [hGpq] at hmoeb
  rw [← hmoeb]
  -- Step 3: identify both sides as a sum over `q.divisors`.
  have hLeft : (∑ p ∈ q.divisorsAntidiagonal, μ p.1 • (∑ i ∈ p.2.divisors, Gp i))
      = ∑ d ∈ q.divisors, (μ (q / d) : ℂ) * (d.totient : ℂ) * ↑(Δ_[g](x; d, a.cast)) := by
    rw [Nat.sum_divisorsAntidiagonal' (f := fun a b => μ a • (∑ i ∈ b.divisors, Gp i))]
    apply Finset.sum_congr rfl
    intro d hd
    have hdq : d ∣ q := Nat.dvd_of_mem_divisors hd
    have hsum : (∑ i ∈ d.divisors, Gp i)
        = ∑ i ∈ d.divisors, if i = 1 then 0 else GinnerTerm a g x i := by
      apply Finset.sum_congr rfl
      intro i hi
      have hiq : i ∣ q := (Nat.dvd_of_mem_divisors hi).trans hdq
      simp only [hGp_def]
      by_cases h1 : i = 1 <;> simp [h1, hiq]
    rw [hsum, ← totient_mul_Delta_eq ha hgsupp hdq, zsmul_eq_mul]
    ring
  have hRHS : (↑(∑ p ∈ q.divisorsAntidiagonal,
        ↑(μ p.2) * ↑p.1.totient * Δ_[g](x; p.1, a.cast)) : ℂ)
      = ∑ d ∈ q.divisors, (μ (q / d) : ℂ) * (d.totient : ℂ) * ↑(Δ_[g](x; d, a.cast)) := by
    rw [Complex.ofReal_sum, Nat.sum_divisorsAntidiagonal
      (f := fun d' e' => (↑(↑(μ e') * ↑d'.totient * Δ_[g](x; d', a.cast)) : ℂ))]
    apply Finset.sum_congr rfl
    intro d _
    simp only [Complex.ofReal_mul, Complex.ofReal_intCast, Complex.ofReal_natCast]
  rw [hLeft, hRHS]

/-- `Λ♭ 1 = 0`: the flat part vanishes at `1` because its rightmost factor `μ - μ≤V` does. -/
theorem LambdaFlat_apply_one [ProofData] : Λ♭ 1 = 0 := by
  have hμ : (μ - μ≤V) 1 = 0 := by
    have hsub : (μ - μ≤V) 1 = (μ 1 : ℝ) - μ≤V 1 := rfl
    rw [hsub, moebiusLEV,
      on_apply_of_mem _ _ _ (by
        simp only [Set.mem_Icc]
        exact ⟨le_refl 1, Nat.le_floor (by simpa using one_le_V)⟩)]
    simp
  simp [LambdaFlat, ArithmeticFunction.mul_apply, hμ]

/-- For `q = 0`, the discrepancy of `Λ♭` vanishes: the only natural number congruent to a unit
`a : ZMod 0 = ℤ` is `1` (when `a = 1`), where `Λ♭` vanishes. -/
theorem Delta_LambdaFlat_zero [ProofData] {y : ℝ} {a : ZMod 0} (ha : IsUnit a) :
    Δ_[Λ♭](y; 0, a) = 0 := by
  rw [Delta]
  simp only [Nat.totient_zero, Nat.cast_zero, inv_zero, zero_mul, sub_zero, summatory]
  apply Finset.sum_eq_zero
  intro i hi
  by_cases hmem : i ∈ Nat.modEqs a
  · rw [Set.indicator_of_mem hmem]
    rw [Nat.mem_modEqs] at hmem
    have hi1 : i = 1 := by
      rcases Int.isUnit_iff.mp ha with h1 | h1
      · have : (i : ℤ) = 1 := by exact_mod_cast h1 ▸ hmem
        exact_mod_cast this
      · exfalso
        have hnn : (0 : ℤ) ≤ (i : ℤ) := Int.natCast_nonneg i
        have : (i : ℤ) = -1 := by exact_mod_cast h1 ▸ hmem
        rw [this] at hnn; norm_num at hnn
    rw [hi1, LambdaFlat_apply_one]
  · rw [Set.indicator_of_notMem hmem]

/-- For `d ∣ q`, restricting coprimality to `q * d` is the same as restricting to `q`. -/
theorem onCoprime_mul_eq_of_dvd {R : Type*} [Zero R] {f : ℕ → R} {q d : ℕ} (hdq : d ∣ q) :
    onCoprime (q * d) f = onCoprime q f := by
  funext n
  simp only [onCoprime_apply, Nat.coprime_mul_iff_left]
  by_cases h : q.Coprime n
  · rw [if_pos ⟨h, Nat.Coprime.coprime_dvd_left hdq h⟩, if_pos h]
  · rw [if_neg (fun hc => h hc.1), if_neg h]

@[blueprint (latexEnv := "lemma") (statement := /--
$$\left|\Delta_{\Lambda^\flat}(y;\, q,\, a)\right| \le \frac{1}{\varphi(q)} \left|\sum_{\substack{d \mid q \\ 1 < d \le (\log x)^C}} \sum_{s \mid d} \mu(d/s)\,\varphi(s)\,\Delta_{\Lambda^\flat_q}(y;\,s,\,a)\right| + \frac{1}{\varphi(q)} \sum_{\substack{d \mid q \\ d > (\log x)^C}} \sumstar_{\xi \pmod{d}} S_{q/d}(y, \xi)$$
-/) (uses := [character_sum_by_conductor, character_sum_Mobius, S])]
theorem Delta_LambdaFlat_decomp [ProofData] {C : ℕ} {y : ℝ} (q : ℕ) (a : ZMod q) (ha : IsUnit a)  :
  open Classical in
  |Δ_[Λ♭](y; q, a)| ≤ (q.totient : ℝ)⁻¹ * |∑ d ∈ q.divisors with 1 < (d : ℕ) ∧ ↑d ≤ (Real.log x)^C, ∑ p ∈ d.divisorsAntidiagonal, μ p.2 * p.1.totient * Δ_[onCoprime q Λ♭](y; p.1, a.cast)|
    + (q.totient : ℝ)⁻¹ * ∑ d ∈ q.divisors with (Real.log x)^C < (d : ℕ), ∑ ξ : DirichletCharacter ℂ d with ξ.IsPrimitive, S (q/d) y ξ := by
  classical
  rcases Nat.eq_zero_or_pos q with rfl | hqpos
  · -- `q = 0`: the discrepancy vanishes and the right-hand side is `0`.
    rw [Delta_LambdaFlat_zero ha, abs_zero]
    simp [Nat.divisors_zero]
  haveI : NeZero q := ⟨hqpos.ne'⟩
  set L : ℝ := (Real.log x) ^ C with hL_def
  have hg : ∀ n, onCoprime q ⇑Λ♭ n ≠ 0 → q.Coprime n := by
    intro n hn
    rw [onCoprime_apply] at hn
    split_ifs at hn with h
    · exact h
    · exact absurd rfl hn
  have hφ : (q.totient : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hqpos).ne'
  -- Master identity: write `Δ` as a sum of `GinnerTerm`s over the nontrivial divisors of `q`.
  have hΔg : Δ_[onCoprime q ⇑Λ♭](y; q, a) = Δ_[Λ♭](y; q, a) := Delta_onCoprime_self _ _ ha
  have hmaster : (↑(Δ_[Λ♭](y; q, a)) : ℂ)
      = (q.totient : ℂ)⁻¹ * ∑ d ∈ q.divisors with d ≠ 1, GinnerTerm a (onCoprime q ⇑Λ♭) y d := by
    have hkey := totient_mul_Delta_eq (g := onCoprime q ⇑Λ♭) ha hg (dvd_refl q) (x := y)
    rw [ZMod.cast_id q a, hΔg] at hkey
    have hfilt : (∑ i ∈ q.divisors, if i = 1 then 0 else GinnerTerm a (onCoprime q ⇑Λ♭) y i)
        = ∑ i ∈ q.divisors with i ≠ 1, GinnerTerm a (onCoprime q ⇑Λ♭) y i := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : i = 1 <;> simp [h]
    rw [hfilt] at hkey
    rw [← hkey, ← mul_assoc, inv_mul_cancel₀ hφ, one_mul]
  -- On the small conductors, each `GinnerTerm` is the (real) Möbius/totient/Δ sum.
  have hGsmall : ∀ d ∈ q.divisors.filter (fun d : ℕ => 1 < d ∧ (↑d : ℝ) ≤ L),
      GinnerTerm a (onCoprime q ⇑Λ♭) y d = ↑(∑ p ∈ d.divisorsAntidiagonal,
        (μ p.2 : ℝ) * p.1.totient * Δ_[onCoprime q ⇑Λ♭](y; p.1, a.cast)) := by
    intro d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdvd, _⟩, hd1, _⟩ := hd
    have hcs := character_sum_Mobius Λ♭ (r := q) (x := y)
      (a := (a.cast : ZMod d)) hd1 (isUnit_cast_of_dvd hdvd ha)
    rw [GinnerTerm, hcs]
    congr 1
    apply Finset.sum_congr rfl
    intro p hp
    have hp1 : p.1 ∣ d := Nat.dvd_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hp)
    rw [onCoprime_mul_eq_of_dvd hdvd, cast_cast_of_dvd hp1 hdvd]
  -- Split the master sum into small and large conductors.
  have hsplit : (∑ d ∈ q.divisors with d ≠ 1, GinnerTerm a (onCoprime q ⇑Λ♭) y d)
      = (∑ d ∈ q.divisors with 1 < (d:ℕ) ∧ (↑d:ℝ) ≤ L, GinnerTerm a (onCoprime q ⇑Λ♭) y d)
        + ∑ d ∈ q.divisors with L < ((d:ℕ):ℝ), GinnerTerm a (onCoprime q ⇑Λ♭) y d := by
    rw [← Finset.sum_filter_add_sum_filter_not (q.divisors.filter (· ≠ 1))
        (fun d : ℕ => (↑d:ℝ) ≤ L)]
    have hL1 : (1:ℝ) ≤ L := by rw [hL_def]; exact one_le_pow₀ one_le_log_x
    congr 1
    · apply Finset.sum_congr _ (fun _ _ => rfl)
      rw [Finset.filter_filter]
      apply Finset.filter_congr
      intro d hd
      have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
      constructor
      · rintro ⟨hne, hle⟩; exact ⟨by omega, hle⟩
      · rintro ⟨hlt, hle⟩; exact ⟨by omega, hle⟩
    · apply Finset.sum_congr _ (fun _ _ => rfl)
      rw [Finset.filter_filter]
      apply Finset.filter_congr
      intro d hd
      have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
      constructor
      · rintro ⟨_, hnle⟩; push_neg at hnle; exact hnle
      · intro hlt
        refine ⟨?_, by push_neg; exact hlt⟩
        have : (1:ℝ) < (d:ℝ) := lt_of_le_of_lt hL1 hlt
        have : 1 < d := by exact_mod_cast this
        omega
  -- The small part equals the real Möbius sum (as a complex number).
  have hSsmallEq : (∑ d ∈ q.divisors with 1 < (d:ℕ) ∧ (↑d:ℝ) ≤ L, GinnerTerm a (onCoprime q ⇑Λ♭) y d)
      = ↑(∑ d ∈ q.divisors with 1 < (d:ℕ) ∧ (↑d:ℝ) ≤ L,
          ∑ p ∈ d.divisorsAntidiagonal, (μ p.2 : ℝ) * p.1.totient * Δ_[onCoprime q ⇑Λ♭](y; p.1, a.cast)) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl hGsmall
  -- The large part is bounded termwise by the character sums `S`.
  have hSlargeBound : ‖∑ d ∈ q.divisors with L < ((d:ℕ):ℝ), GinnerTerm a (onCoprime q ⇑Λ♭) y d‖
      ≤ ∑ d ∈ q.divisors with L < ((d:ℕ):ℝ),
          ∑ ξ : DirichletCharacter ℂ d with ξ.IsPrimitive, S (q/d) y ξ := by
    refine le_trans (norm_sum_le _ _) ?_
    apply Finset.sum_le_sum
    intro d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdvd, _⟩, _⟩ := hd
    rw [GinnerTerm]
    refine le_trans (norm_sum_le _ _) ?_
    apply Finset.sum_le_sum
    intro ξ _
    rw [norm_mul, norm_star]
    have hnorm1 : ‖ξ (a.cast : ZMod d)‖ = 1 := by
      have hau : IsUnit (a.cast : ZMod d) := isUnit_cast_of_dvd hdvd ha
      rw [← hau.unit_spec]
      exact DirichletCharacter.unit_norm_eq_one ξ hau.unit
    rw [hnorm1, one_mul, S]
    apply le_of_eq
    congr 1
    simp only [summatory]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hcop : d.Coprime n
    · have heq : onCoprime q ⇑Λ♭ n = onCoprime (q/d) ⇑Λ♭ n := by
        simp only [onCoprime_apply]
        by_cases hq : q.Coprime n
        · rw [if_pos hq, if_pos (Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd hdvd) hq)]
        · rw [if_neg hq, if_neg ?_]
          intro hqd
          apply hq
          have hmul := Nat.Coprime.mul_left hcop hqd
          rwa [Nat.mul_div_cancel' hdvd] at hmul
      rw [heq, mul_comm]
    · have hnu : ¬ IsUnit (↑n : ZMod d) := by
        rw [ZMod.isUnit_iff_coprime]; exact fun h => hcop h.symm
      rw [ξ.map_nonunit hnu]; ring
  -- Assemble.
  rw [show |Δ_[Λ♭](y; q, a)| = ‖(↑(Δ_[Λ♭](y; q, a)) : ℂ)‖ from (Complex.norm_real _).symm,
     hmaster, norm_mul, norm_inv, Complex.norm_natCast, hsplit, ← mul_add]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc ‖(∑ d ∈ q.divisors with 1 < (d:ℕ) ∧ (↑d:ℝ) ≤ L, GinnerTerm a (onCoprime q ⇑Λ♭) y d)
          + ∑ d ∈ q.divisors with L < ((d:ℕ):ℝ), GinnerTerm a (onCoprime q ⇑Λ♭) y d‖
      ≤ ‖∑ d ∈ q.divisors with 1 < (d:ℕ) ∧ (↑d:ℝ) ≤ L, GinnerTerm a (onCoprime q ⇑Λ♭) y d‖
        + ‖∑ d ∈ q.divisors with L < ((d:ℕ):ℝ), GinnerTerm a (onCoprime q ⇑Λ♭) y d‖ := norm_add_le _ _
    _ ≤ |∑ d ∈ q.divisors with 1 < (d:ℕ) ∧ (↑d:ℝ) ≤ L,
            ∑ p ∈ d.divisorsAntidiagonal, (μ p.2 : ℝ) * p.1.totient * Δ_[onCoprime q ⇑Λ♭](y; p.1, a.cast)|
          + ∑ d ∈ q.divisors with L < ((d:ℕ):ℝ),
              ∑ ξ : DirichletCharacter ℂ d with ξ.IsPrimitive, S (q/d) y ξ := by
        rw [hSsmallEq, Complex.norm_real, Real.norm_eq_abs]
        exact add_le_add (le_refl _) hSlargeBound


def C_DLF (A C : ℝ) : ℝ := sorry

@[blueprint (statement := /--
$$\frac{1}{\varphi(q)} \left|\sum_{\substack{d \mid q \\ 1 < d \le (\log x)^C}} \sum_{s \mid d} \mu(d/s)\,\varphi(s)\,\Delta_{\Lambda^\flat_q}(y;\,s,\,a)\right| \ll_{A,C} \frac{x}{\varphi(q)\,(\log x)^{A+1}}$$
-/) (proof := /--
Push the absolute values inside, then
\begin{align*}
\sum_{d \mid q,\, d \le (\log x)^C} \sum_{s \mid d} \varphi(s)\, \left|\Delta_{\Lambda^\flat_q}(y;\, s,\, a)\right|
&\ll_{A,C} \sum_{d \le (\log x)^C} \left(\sum_{s \mid d} \varphi(s)\right) \frac{x}{(\log x)^{A+2C+1}} \\
&\ll \frac{x}{(\log x)^{A+2C+1}} \sum_{d \le (\log x)^C} d \\
&\ll \frac{x}{(\log x)^{A+1}}.
\end{align*}
-/) (uses := [Delta_LambdaFlat_decomp, siegel_walfisz])]
theorem Delta_LambdaFlat_small_conductor [ProofData] (A C : ℕ) {y : ℝ} (q : ℕ) (a : ZMod q) (ha : IsUnit a) :
    |∑ d ∈ q.divisors with 1 < (d : ℕ) ∧ ↑d ≤ (Real.log x)^C,
      ∑ p ∈ d.divisorsAntidiagonal, μ p.2 * ↑p.1.totient * Δ_[onCoprime q Λ♭](y; p.1, a.cast)|
    ≤ C_DLF A C * x / (Real.log x) ^ (A + 1) := by sorry

def C_BV_LFT : ℝ := sorry

@[blueprint (statement := /--
$$\sum_{q \le Q} \max_{\substack{\sqrt{x} \le y \le x \\ a \in (\Z/q\Z)^*}} \left|\Delta_{\Lambda^\flat}(y;\,q,\,a)\right| \le \sum_{r \le Q} \frac{T_r(x,Q)}{\varphi(r)} + O\!\left(\frac{x}{(\log x)^A}\right)$$
-/) (proof := /--
Sum the error from \ref{Delta_LambdaFlat_small_conductor} over $q \le Q$ using
$\sum_{n \le x} 1/\varphi(n) \ll \log x$, then regroup the main sum by $r = q/d$.
-/) (uses := [Delta_LambdaFlat_decomp, Delta_LambdaFlat_small_conductor, character_sum_Mobius, T])]
theorem BV_LambdaFlat_via_T (Q : ℝ) (A C : ℕ) [ProofData] :
  |summatory (fun q ↦ maxya q fun y a ↦ |Δ_[Λ♭](y; q, a)|) Q
  - summatory (fun r ↦ T C r Q) Q| ≤ C_BV_LFT * x / (Real.log x)^A
 := by sorry

/-! ### Large sieve estimates -/

-- TODO: Decide if we need to define the L2 norm on ArithmeticFunctions explicitly here.

@[blueprint (statement := /--
Let $f$ and $g$ be arithmetic functions supported on $[1, M]$ and $[1, N]$ respectively. For $x, Q \ge 1$,
$$\sum_{q \le Q} \sumstar_{\chi \pmod{q}} \frac{q}{\varphi(q)} \max_{y \le x}\left|\sum_{n \le y} (f*g)(n)\chi(n)\right| \ll \left(\sqrt{MN} + \sqrt{M}\,Q + \sqrt{N}\,Q + Q^2\right)(\log x)\,\|f\|_2\,\|g\|_2$$
-/) (proof := /--
Uses Cauchy--Schwarz and the large sieve inequality (\ref{large_sieve}).
The proof in the book uses the classical version of Perron's integral formula as $1_{n \le x} = \int_{-T}^{T}\frac{(x/n)^{\alpha+it}}{\alpha+it} dt/(2\pi) + O(...)$
But we have a different version in PNT+. I haven't worked out how this changes the proof yet.
-/) (uses := [large_sieve])]
theorem LargeSieve_convolution {M N : ℕ} (f g : ArithmeticFunction ℝ) (hf : ∀ n > M, f n = 0) (hg : ∀ n > N, g n = 0)
    {x Q : ℝ} (hx : 1 ≤ x) (hQ : 1 ≤ Q) :
  open Classical in
    summatory (fun q ↦ ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive, q * (q.totient : ℝ)⁻¹ * ⨆ y ∈ Set.Icc 1 x, ‖summatory (fun n ↦ (f * g) n * χ n) y‖) Q
      ≤ (√(N * M) + √M * Q + √N * Q + Q^2) * √(∑ n ∈ Finset.Icc 1 M, (f n)^2) * √(∑ n ∈ Finset.Icc 1 N, (g n)^2) := by sorry


-- TODO: Figure out if the j-1 -s here are harmful (of course they are) and rewrite the proofs to use j/j+1 instead of j-1/j.

private noncomputable def f [ProofData] (j : ℕ) : ArithmeticFunction ℝ :=  ((Λ - Λ≤U) * ζ).on (Set.Ioc (2^(j-1)) (2^j))
private noncomputable def g [ProofData] (j : ℕ) : ArithmeticFunction ℝ :=  (μ).on (Nat.cast ⁻¹' (Set.Ioc V (x / 2^(j-1))))

/-- The finset of natural numbers j such that $x < 2^j ≤ y$-/
noncomputable def pows2Ioc (x y : ℝ) : Finset ℕ :=
  if 1 ≤ y ∧ x < y then
    Finset.Ioc ⌊(Real.logb 2 x)⌋₊  ⌊Real.logb 2 y⌋₊
  else ∅

@[simp]
theorem mem_pows2Ioc (x y : ℝ) (hx : 1 ≤ x) (n : ℕ) :
    n ∈ pows2Ioc x y ↔ x < 2^n ∧ 2^n ≤ y := by
  simp [pows2Ioc]
  split_ifs with hxy
  · simp only [Finset.mem_Ioc]
    rw [Nat.floor_lt, Nat.le_floor_iff]
    · rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith),
        Real.logb_lt_iff_lt_rpow (by norm_num) (by linarith)]
      norm_cast
    · apply Real.logb_nonneg (by norm_num) hxy.1
    · apply Real.logb_nonneg (by norm_num) hx
  · simp only [Finset.notMem_empty, false_iff, not_and, not_le]
    simp only [not_and, not_lt] at hxy
    by_cases hy : 1 ≤ y
    · grind [hxy hy]
    · intro hxn
      have : (1:ℝ) ≤ 2^n := by
        norm_cast
        apply Nat.one_le_pow
        norm_num
      grind


@[blueprint (latexEnv := "lemma") (statement := /--
$$\Lambda^\flat(n) = \sum_{U < 2^j \le 2x/V} (f_j * g_j)(n) \quad \text{for } n \le x,$$
where $f_j(k) = (\Lambda_{>U} * 1)(k)\,1_{2^{j-1} < k \le 2^j}$ and $g_j(\ell) = \mu(\ell)\,1_{V < \ell \le x/2^{j-1}}$.
-/)]
theorem LambdaFlat_dyadic [ProofData] (n : ℕ) (hn : n ≤ x) :
    Λ♭ n = ∑ j ∈ pows2Ioc V (2*x/V), (f j * g j) n
   := by sorry

def C_BV_char_sum : ℝ := sorry

@[blueprint (statement := /--
For $x, Q \ge 2$, $U, V \in [1, x]$ and $r \in \N$,
$$\sum_{q \le Q} \sumstar_{\chi \pmod{q}} \frac{q}{\varphi(q)}\, S_r(y, \chi) \ll \left(x + \frac{Qx}{\sqrt{U}} + \frac{Qx}{\sqrt{V}} + Q^2\sqrt{x}\right)(\log x)^3$$
-/) (proof := /--
Apply the dyadic decomposition \ref{LambdaFlat_dyadic} (restricted to integers coprime to $r$)
and apply \ref{LargeSieve_convolution} to each dyadic piece.
When summing over $j$ note $U \le 2^j$, so $\sum_{U \le 2^j} 2^{-j/2} \ll 1/\sqrt{U}$.
-/) (uses := [LargeSieve_convolution, LambdaFlat_dyadic, S])]
theorem BV_char_sum_bound [ProofData] (r : ℕ) (Q : ℝ) (hQ : 2 ≤ Q) :
  open Classical in
    summatory (fun q ↦ ∑ ξ : DirichletCharacter ℂ q with ξ.IsPrimitive,
      q * (q.totient : ℝ)⁻¹ * maxy (fun y ↦ S r y ξ)) Q
    ≤ C_BV_char_sum * (x + Q * x / Real.sqrt U + Q * x / Real.sqrt V + Q ^ 2 * Real.sqrt x) * (Real.log x) ^ 3 := by sorry

def C_Tr : ℝ := sorry

@[blueprint (statement := /--
$$T_r(x,Q) \ll \frac{x}{(\log x)^{C-3}} + \frac{x(\log x)^4}{\sqrt{U}} + \frac{x(\log x)^4}{\sqrt{V}} + \frac{Q\sqrt{x}\,(\log x)^3}{r}$$
-/) (proof := /--
Divide the sum defining $T_r$ into dyadic intervals in $d$ and apply \ref{BV_char_sum_bound}.
-/) (uses := [BV_char_sum_bound, LambdaFlat_dyadic, T])]
theorem T_r_bound [ProofData] (C : ℕ) (r : ℕ) (Q : ℝ) (hQ : 2 ≤ Q) :
    T C r Q ≤ C_Tr * (x / (Real.log x)^(C-3) + x * (Real.log x)^4 * √U + x * (Real.log x)^4 * √V + Q * √x * (Real.log x)^3 / r)
 := by sorry

def C_BV_LF (A : ℝ) : ℝ := sorry

@[blueprint (statement := /--
For each fixed $A \ge 0$, $x \ge 2$ and $1 \le Q \le \sqrt{x}/(\log x)^{A+3}$,
$$\sum_{q \le Q} \max_{\sqrt{x} \le y \le x} \max_{a \in (\Z/q\Z)^*} \left|\Delta_{\Lambda^\flat}(y;\,q,\,a)\right| \ll_A \frac{x}{(\log x)^A}$$
-/) (proof := /--
Plug the bound from \ref{T_r_bound} into \ref{BV_LambdaFlat_via_T},
then choose $U = V = e^{\sqrt{\log x}}$ and $C = A + 4$.
-/) (uses := [BV_LambdaFlat_via_T, T_r_bound, Delta_LambdaFlat_small_conductor])]
theorem BV_LambdaFlat [ProofData] (A : ℕ) (Q : ℝ) (h1Q : 1 ≤ Q) (hQ : Q ≤ √x / (Real.log x)^(A+3)) :
    ∑ q ∈ Nat.Icc 0 Q, maxya q (fun y a ↦ Δ_[Λ♭](y; q, a)) ≤
      C_BV_LF A * x / (Real.log x)^A := by
  sorry
