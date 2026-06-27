import Mathlib
import Architect
import BV.Delta
import BV.Axioms
import BV.LambdaSharp
import BV.LambdaLE

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

/-- Divisors pair as `(d, n/d)` around `√n`, so `τ(n) ≤ 2√n`.
(Mathlib only has `Nat.card_divisors_le_self : τ(n) ≤ n`.) -/
theorem card_divisors_le_two_mul_sqrt (n : ℕ) :
    (n.divisors.card : ℝ) ≤ 2 * Real.sqrt n := by
  classical
  set f : ℕ → ℕ := fun d => if d * d ≤ n then d else n / d with hf
  -- Each value `b` of `f` has at most two preimages: `b` and `n / b`.
  have hfib : ∀ b ∈ n.divisors.image f, ({a ∈ n.divisors | f a = b}).card ≤ 2 := by
    intro b _hb
    have hsub : {a ∈ n.divisors | f a = b} ⊆ ({b, n / b} : Finset ℕ) := by
      intro a ha
      simp only [Finset.mem_filter, Nat.mem_divisors] at ha
      obtain ⟨⟨hdvd, hn0⟩, hfa⟩ := ha
      simp only [hf] at hfa
      rw [Finset.mem_insert, Finset.mem_singleton]
      split_ifs at hfa with hc
      · exact Or.inl hfa
      · right
        subst hfa
        exact (Nat.div_div_self hdvd hn0).symm
    exact (Finset.card_le_card hsub).trans ((Finset.card_insert_le _ _).trans (by simp))
  have h1 : n.divisors.card ≤ 2 * (n.divisors.image f).card :=
    Finset.card_le_mul_card_image n.divisors 2 hfib
  -- Every value of `f` lies in `[1, ⌊√n⌋]`.
  have h2 : n.divisors.image f ⊆ Finset.Icc 1 (Nat.sqrt n) := by
    intro b hb
    rw [Finset.mem_image] at hb
    obtain ⟨d, hd, rfl⟩ := hb
    have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
    rw [Nat.mem_divisors] at hd
    obtain ⟨hdvd, hn0⟩ := hd
    have hd0 : 0 < d := hd1
    have hdle : d ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd
    rw [Finset.mem_Icc]
    simp only [hf]
    split_ifs with hc
    · exact ⟨hd1, Nat.le_sqrt.mpr hc⟩
    · refine ⟨(Nat.one_le_div_iff hd0).mpr hdle, Nat.le_sqrt.mpr ?_⟩
      have hq : d * (n / d) = n := Nat.mul_div_cancel' hdvd
      have hlt : n / d ≤ d := by
        by_contra h
        push_neg at h
        have : d * d ≤ d * (n / d) := by gcongr
        rw [hq] at this
        exact hc this
      have : (n / d) * (n / d) ≤ d * (n / d) := by gcongr
      rwa [hq] at this
  have h3 : (n.divisors.image f).card ≤ Nat.sqrt n := by
    calc (n.divisors.image f).card ≤ (Finset.Icc 1 (Nat.sqrt n)).card :=
          Finset.card_le_card h2
      _ = Nat.sqrt n := by rw [Nat.card_Icc]; omega
  have h4 : n.divisors.card ≤ 2 * Nat.sqrt n := by omega
  calc (n.divisors.card : ℝ) ≤ ((2 * Nat.sqrt n : ℕ) : ℝ) := by exact_mod_cast h4
    _ = 2 * (Nat.sqrt n : ℝ) := by push_cast; ring
    _ ≤ 2 * Real.sqrt n := by
        gcongr
        exact Real.nat_sqrt_le_real_sqrt

/-- For `x ≥ 1`, `δ > 0`: `(log x)^M ≤ (M/δ)^M · x^δ`. The `δ = 1/2` case recovers the
`√x` bound; we also use `δ = 1/4` to absorb the divisor factor `τ(q) ≤ 2x^{1/4}`. -/
theorem log_pow_le_const_mul_rpow {x : ℝ} (hx : 1 ≤ x) (M : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    (Real.log x) ^ M ≤ ((M : ℝ) / δ) ^ M * x ^ δ := by
  have hx0 : 0 < x := by linarith
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    simp only [pow_zero, Nat.cast_zero, zero_div, one_mul]
    calc (1:ℝ) = (1:ℝ) ^ δ := (Real.one_rpow δ).symm
      _ ≤ x ^ δ := Real.rpow_le_rpow (by norm_num) hx hδ.le
  · have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
    set c : ℝ := δ / (M : ℝ) with hc
    have hMpos : (0:ℝ) < (M : ℝ) := by exact_mod_cast hM
    have hcpos : 0 < c := by rw [hc]; positivity
    have hMδ : (M : ℝ) / δ = c⁻¹ := by rw [hc]; field_simp
    -- Key pointwise bound: log x ≤ (M/δ) · x^c
    have key : Real.log x ≤ c⁻¹ * x ^ c := by
      have h1 : Real.log (x ^ c) = c * Real.log x := Real.log_rpow hx0 c
      have h2 : Real.log (x ^ c) ≤ x ^ c - 1 :=
        Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx0 c)
      have h3 : c * Real.log x ≤ x ^ c := by rw [h1] at h2; linarith
      rw [inv_mul_eq_div, le_div_iff₀ hcpos, mul_comm]
      exact h3
    have hcM : c * (M : ℝ) = δ := by rw [hc]; field_simp
    calc (Real.log x) ^ M
        ≤ (c⁻¹ * x ^ c) ^ M := pow_le_pow_left₀ hlogx key M
      _ = (c⁻¹) ^ M * (x ^ c) ^ M := mul_pow _ _ _
      _ = ((M : ℝ) / δ) ^ M * x ^ δ := by
          rw [hMδ, ← Real.rpow_natCast (x ^ c) M, ← Real.rpow_mul hx0.le, hcM]

/-- The sharp-term budget: with no constraint on `q` beyond `q ≤ √x`, the divisor factor
`τ(q)` is absorbed by the `x^{1/4}` headroom, leaving `x/(log x)^K`. -/
theorem card_divisors_mul_sqrt_mul_log_le_div [ProofData] {q : ℕ}
    (hq : (q : ℝ) ≤ √x) (K : ℕ) :
    (q.divisors.card : ℝ) * Real.sqrt x * Real.log x
      ≤ 2 * (4 * ((K + 1 : ℕ) : ℝ)) ^ (K + 1) * (x / (Real.log x) ^ K) := by
  have hx1 : (1:ℝ) ≤ x := by linarith [le_x]
  have hx0 : (0:ℝ) < x := by linarith [le_x]
  have hL : (0:ℝ) < Real.log x := log_x_pos
  have hLK : (0:ℝ) < (Real.log x) ^ K := pow_pos hL K
  set B : ℝ := (4 * ((K + 1 : ℕ) : ℝ)) ^ (K + 1) with hB
  have hBpos : 0 < B := by rw [hB]; positivity
  have hsqrtx : Real.sqrt x = x ^ (1/2 : ℝ) := Real.sqrt_eq_rpow x
  -- `√(√x) = x^(1/4)`
  have hsqsq : Real.sqrt (Real.sqrt x) = x ^ (1/4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le]
    norm_num
  -- divisor bound: `τ(q) ≤ 2·x^(1/4)`
  have hτ : (q.divisors.card : ℝ) ≤ 2 * x ^ (1/4 : ℝ) := by
    refine (card_divisors_le_two_mul_sqrt q).trans ?_
    have hq14 : Real.sqrt (q : ℝ) ≤ x ^ (1/4 : ℝ) := by
      have := Real.sqrt_le_sqrt hq
      rwa [hsqsq] at this
    gcongr
  -- `(log x)^(K+1) ≤ B · x^(1/4)`
  have hlog : (Real.log x) ^ (K + 1) ≤ B * x ^ (1/4 : ℝ) := by
    have h := log_pow_le_const_mul_rpow hx1 (K + 1) (δ := (1/4 : ℝ)) (by norm_num)
    have hconst : (((K + 1 : ℕ) : ℝ) / (1/4 : ℝ)) = 4 * ((K + 1 : ℕ) : ℝ) := by ring
    rwa [hconst] at h
  -- collapse `x^(1/4)·x^(1/2)·x^(1/4) = x`
  have hxsum : x ^ (1/4 : ℝ) * x ^ (1/2 : ℝ) * x ^ (1/4 : ℝ) = x := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0,
      show (1/4 + 1/2 + 1/4 : ℝ) = 1 by norm_num, Real.rpow_one]
  -- main product inequality
  have hmain : (q.divisors.card : ℝ) * Real.sqrt x * Real.log x * (Real.log x) ^ K
      ≤ 2 * B * x := by
    calc (q.divisors.card : ℝ) * Real.sqrt x * Real.log x * (Real.log x) ^ K
        = (q.divisors.card : ℝ) * Real.sqrt x * (Real.log x) ^ (K + 1) := by
          rw [mul_assoc ((q.divisors.card : ℝ) * Real.sqrt x), ← pow_succ']
      _ ≤ (2 * x ^ (1/4 : ℝ)) * x ^ (1/2 : ℝ) * (B * x ^ (1/4 : ℝ)) := by
          rw [hsqrtx]; gcongr
      _ = 2 * B * (x ^ (1/4 : ℝ) * x ^ (1/2 : ℝ) * x ^ (1/4 : ℝ)) := by ring
      _ = 2 * B * x := by rw [hxsum]
  rw [← mul_div_assoc, le_div_iff₀ hLK]
  exact hmain

/-- For a pointwise-nonnegative `f`, `|Δ_[f](y; s, a)| ≤ 2 · ∑_{n≤y} f(n)`. -/
theorem Delta_abs_le_two_summatory [ProofData] {y : ℝ} {s : ℕ} (hs : 0 < s) {a : ZMod s}
    {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) :
    |Δ_[f](y; s, a)| ≤ 2 * summatory f y := by
  rw [Delta]
  have h1le : (1:ℝ) ≤ (s.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hs
  have htot : (s.totient : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1le
  have hc : (0:ℝ) ≤ (s.totient : ℝ)⁻¹ := by positivity
  have h1 : summatory ((Nat.modEqs a).indicator f) y ≤ summatory f y :=
    summatory_mono_fun _ _ _ (fun n _ ↦ Set.indicator_apply_le' (fun _ ↦ le_rfl) (fun _ ↦ hf n))
  have h1' : 0 ≤ summatory ((Nat.modEqs a).indicator f) y :=
    summatory_nonneg _ y (fun n _ ↦ Set.indicator_nonneg (fun _ _ ↦ hf n) n)
  have h2 : summatory (onCoprime s f) y ≤ summatory f y :=
    summatory_mono_fun _ _ _ (fun n _ ↦ onCoprime_le_of_nonneg (hf n))
  have h2' : 0 ≤ summatory (onCoprime s f) y :=
    summatory_nonneg _ y (fun n _ ↦ onCoprime_nonneg (hf n))
  refine (abs_sub _ _).trans ?_
  rw [abs_of_nonneg h1', abs_of_nonneg (mul_nonneg hc h2')]
  linarith [mul_le_of_le_one_left h2' htot]

/-- Coprime-restricted version of `Delta_LambdaLEU_bound`. -/
theorem Delta_onCoprime_LambdaLEU_bound [ProofData] {y : ℝ} {q s : ℕ} (hs : 0 < s)
    {a : ZMod s} :
    |Δ_[onCoprime q ⇑Λ≤U](y; s, a)| ≤ 2 * U * Real.log x := by
  rw [Delta]
  grw [abs_sub, abs_mul]
  have htot : (s.totient : ℝ)⁻¹ ≤ 1 := by
    have : 0 < s.totient := by simp only [Nat.totient_pos, hs]
    field_simp
    norm_cast
  grw [htot, abs_one]
  rw [abs_of_nonneg, abs_of_nonneg]
  · have h1 : summatory ((Nat.modEqs a).indicator (onCoprime q ⇑Λ≤U)) y ≤ U * Real.log x := by
      apply le_trans (summatory_mono_fun ..) sum_LambdaLEU_le
      intro n hn
      apply Set.indicator_le' (fun _ _ ↦ onCoprime_le_of_nonneg LambdaLEU_nonneg)
      simp
    have h2 : summatory (onCoprime s (onCoprime q ⇑Λ≤U)) y ≤ U * Real.log x := by
      apply le_trans (summatory_mono_fun ..) sum_LambdaLEU_le
      intro n hn
      exact le_trans (onCoprime_le_of_nonneg (onCoprime_nonneg LambdaLEU_nonneg))
        (onCoprime_le_of_nonneg LambdaLEU_nonneg)
    linarith
  · positivity
  · positivity

/-- Replacing `log y` by `log x` (using `√x ≤ y ≤ x`) costs at most a factor `2^N`. -/
theorem y_div_logy_le_x_div_logx [ProofData] {y : ℝ} (hy1 : √x ≤ y) (hy2 : y ≤ x) (N : ℕ) :
    y / (Real.log y) ^ N ≤ 2 ^ N * (x / (Real.log x) ^ N) := by
  have hlogx : 0 < Real.log x := log_x_pos
  have hsqrt_pos : 0 < √x := Real.sqrt_pos.mpr x_pos
  have hlogy_ge : Real.log x / 2 ≤ Real.log y := by
    calc Real.log x / 2 = Real.log (√x) := (Real.log_sqrt x_nonneg).symm
      _ ≤ Real.log y := Real.log_le_log hsqrt_pos hy1
  have hlogy_pos : 0 < Real.log y := lt_of_lt_of_le (by linarith) hlogy_ge
  have hpow : (Real.log x) ^ N / 2 ^ N ≤ (Real.log y) ^ N := by
    have h := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ Real.log x / 2) hlogy_ge N
    rwa [div_pow] at h
  have hpowy_pos : 0 < (Real.log y) ^ N := by positivity
  have hpowx_pos : 0 < (Real.log x) ^ N := by positivity
  calc y / (Real.log y) ^ N
      ≤ x / (Real.log y) ^ N := by
        apply div_le_div_of_nonneg_right hy2 hpowy_pos.le
    _ ≤ x / ((Real.log x) ^ N / 2 ^ N) :=
        div_le_div_of_nonneg_left x_nonneg (by positivity) hpow
    _ = 2 ^ N * (x / (Real.log x) ^ N) := by field_simp

/-- Siegel–Walfisz bound for the coprime-restricted von Mangoldt function.
The `q`-restriction and the `s`-correction cost only `O((log x)²)`, while the main term
comes from Siegel–Walfisz applied at modulus `s ≤ (log y)^{C2}`. -/
theorem Delta_onCoprime_Lambda_bound [ProofData] (A' C2 : ℕ) {y : ℝ}
    (hy2 : 2 ≤ y) (hyx : y ≤ x)
    {q s : ℕ} (hs0 : 0 < s) (hsq : s ∣ q) (hq0 : 0 < q) (hqx : (q:ℝ) ≤ Real.sqrt x)
    (hs : (s:ℝ) ≤ (Real.log y) ^ C2) {a : ZMod s} (ha : IsUnit a) :
    |Δ_[onCoprime q ⇑Λ](y; s, a)|
      ≤ (C_SW A' C2 + C_SW A' 0) * (y / (Real.log y) ^ A')
        + 3 * (Real.log 2)⁻¹ * (Real.log x) ^ 2 := by
  set Λnc : ℕ → ℝ := fun n ↦ if ¬ q.Coprime n then Λ n else 0 with hΛnc
  have hΛnc_nonneg : ∀ n, 0 ≤ Λnc n := by
    intro n; simp only [hΛnc]; split_ifs <;> simp [vonMangoldt_nonneg]
  have hfun : onCoprime q (⇑Λ) = (⇑Λ : ℕ → ℝ) - Λnc := by
    funext n
    simp only [onCoprime_apply, Pi.sub_apply, hΛnc]
    split_ifs with h <;> simp
  have hq_pos : (0:ℝ) < q := by exact_mod_cast hq0
  have hlogq_nonneg : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq0)
  have hlogx_nonneg : 0 ≤ Real.log x := Real.log_nonneg (by linarith [ProofData.le_x])
  have hlog2 : (0:ℝ) ≤ (Real.log 2)⁻¹ := by positivity
  have hlogq_le : Real.log q ≤ Real.log x := by
    calc Real.log q ≤ Real.log (Real.sqrt x) := Real.log_le_log hq_pos hqx
      _ = Real.log x / 2 := Real.log_sqrt x_nonneg
      _ ≤ Real.log x := by linarith
  -- The `q`-non-coprime part is a small error.
  have hΛnc_bound : |Δ_[Λnc](y; s, a)| ≤ 2 * (Real.log 2)⁻¹ * (Real.log x) ^ 2 := by
    have step1 : |Δ_[Λnc](y; s, a)| ≤ 2 * summatory Λnc x :=
      le_trans (Delta_abs_le_two_summatory hs0 hΛnc_nonneg)
        (mul_le_mul_of_nonneg_left (summatory_mono hyx (fun n _ ↦ hΛnc_nonneg n)) (by norm_num))
    have t1 := mul_le_mul_of_nonneg_right C_SVNC_le (mul_nonneg hlogq_nonneg hlogx_nonneg)
    have t2 : (Real.log 2)⁻¹ * (Real.log q * Real.log x)
        ≤ (Real.log 2)⁻¹ * (Real.log x * Real.log x) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hlogq_le hlogx_nonneg) hlog2
    have t3 := le_trans (le_abs_self (summatory Λnc x))
        (sum_vonMangoldt_not_coprime_ll_logq (q:=q) hq0)
    have step2 : summatory Λnc x ≤ (Real.log 2)⁻¹ * (Real.log x * Real.log x) :=
      le_trans t3 (le_trans t1 t2)
    calc |Δ_[Λnc](y; s, a)| ≤ 2 * summatory Λnc x := step1
      _ ≤ 2 * ((Real.log 2)⁻¹ * (Real.log x * Real.log x)) :=
          mul_le_mul_of_nonneg_left step2 (by norm_num)
      _ = 2 * (Real.log 2)⁻¹ * (Real.log x) ^ 2 := by ring
  have hlogs_le : Real.log s ≤ Real.log x :=
    le_trans (Real.log_le_log (by exact_mod_cast hs0)
      (by exact_mod_cast Nat.le_of_dvd hq0 hsq)) hlogq_le
  have hlogs_nonneg : 0 ≤ Real.log s := Real.log_nonneg (by exact_mod_cast hs0)
  -- The main von Mangoldt `Δ` via Siegel–Walfisz.
  have hΛ_bound : |Δ_[(⇑Λ : ℕ → ℝ)](y; s, a)|
      ≤ (C_SW A' C2 + C_SW A' 0) * (y / (Real.log y) ^ A')
        + (Real.log 2)⁻¹ * (Real.log x) ^ 2 := by
    rw [Delta]
    set c : ℝ := ((s.totient : ℝ))⁻¹ with hc_def
    set T1 : ℝ := summatory ((Nat.modEqs a).indicator (⇑Λ)) y with hT1
    set T2 : ℝ := summatory (onCoprime s (⇑Λ)) y with hT2
    have hc0 : (0:ℝ) ≤ c := by rw [hc_def]; positivity
    have hcle : c ≤ 1 := by
      rw [hc_def]; exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.totient_pos.mpr hs0)
    have hSW : |ψ y a - y / (s.totient : ℝ)| ≤ C_SW A' C2 * (y / Real.log y ^ A') :=
      siegel_walfisz A' C2 hy2 hs0 hs ha
    have hPNT : |summatory (fun n ↦ Λ n) y - y| ≤ C_SW A' 0 * (y / Real.log y ^ A') := by
      have h0 := siegel_walfisz A' 0 hy2 (q:=1) (by norm_num) (by simp) (a:=(1:ZMod 1)) (by simp)
      rw [ψ_one_one, ← summatory_vonMangoldt] at h0
      simpa using h0
    have hT2_eq : T2 = summatory (fun n ↦ if s.Coprime n then (Λ n : ℝ) else 0) y := by
      rw [hT2]; congr 1
    have hEs_nonneg : 0 ≤ summatory (fun n ↦ if ¬ s.Coprime n then (Λ n : ℝ) else 0) y :=
      summatory_nonneg _ _ (fun n _ ↦ by split_ifs <;> simp [vonMangoldt_nonneg])
    have hsub : summatory (fun n ↦ Λ n) y - T2
        = summatory (fun n ↦ if ¬ s.Coprime n then (Λ n : ℝ) else 0) y := by
      rw [hT2_eq]; exact summatory_sub_ite _
    have hEs_bound : summatory (fun n ↦ if ¬ s.Coprime n then (Λ n : ℝ) else 0) y
        ≤ (Real.log 2)⁻¹ * (Real.log x * Real.log x) := by
      have hmono : summatory (fun n ↦ if ¬ s.Coprime n then (Λ n : ℝ) else 0) y
          ≤ summatory (fun n ↦ if ¬ s.Coprime n then (Λ n : ℝ) else 0) x :=
        summatory_mono hyx (fun n _ ↦ by split_ifs <;> simp [vonMangoldt_nonneg])
      have hx_bound := le_trans (le_abs_self _)
        (sum_vonMangoldt_not_coprime_ll_logq (q:=s) hs0)
      have u1 := mul_le_mul_of_nonneg_right C_SVNC_le (mul_nonneg hlogs_nonneg hlogx_nonneg)
      have u2 : (Real.log 2)⁻¹ * (Real.log s * Real.log x)
          ≤ (Real.log 2)⁻¹ * (Real.log x * Real.log x) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hlogs_le hlogx_nonneg) hlog2
      exact le_trans hmono (le_trans hx_bound (le_trans u1 u2))
    have hyT2 : |y - T2| ≤ C_SW A' 0 * (y / Real.log y ^ A')
        + (Real.log 2)⁻¹ * (Real.log x * Real.log x) := by
      have e : y - T2 = summatory (fun n ↦ if ¬ s.Coprime n then (Λ n : ℝ) else 0) y
          - (summatory (fun n ↦ Λ n) y - y) := by rw [← hsub]; ring
      rw [e]
      refine (abs_sub _ _).trans ?_
      rw [abs_of_nonneg hEs_nonneg]
      linarith [hEs_bound, hPNT]
    -- Assemble.
    have hT1ψ : T1 = ψ y a := rfl
    have e1 : T1 - c * T2 = (ψ y a - y / (s.totient : ℝ)) + c * (y - T2) := by
      rw [hT1ψ, div_eq_mul_inv, ← hc_def]; ring
    rw [e1]
    refine (abs_add_le _ _).trans ?_
    have hpart2 : |c * (y - T2)|
        ≤ C_SW A' 0 * (y / Real.log y ^ A') + (Real.log 2)⁻¹ * (Real.log x * Real.log x) := by
      rw [abs_mul, abs_of_nonneg hc0]
      refine le_trans (mul_le_mul_of_nonneg_left hyT2 hc0) ?_
      exact mul_le_of_le_one_left (le_trans (abs_nonneg (y - T2)) hyT2) hcle
    refine le_trans (add_le_add hSW hpart2) (le_of_eq ?_)
    ring
  rw [hfun, Delta_sub]
  calc |Δ_[(⇑Λ : ℕ → ℝ)](y; s, a) - Δ_[Λnc](y; s, a)|
      ≤ |Δ_[(⇑Λ : ℕ → ℝ)](y; s, a)| + |Δ_[Λnc](y; s, a)| := abs_sub _ _
    _ ≤ _ := by linarith

/-- Under `ProofData`, the constraints force `log x ≥ 16` (a strengthening of `one_le_log_x`). -/
theorem sixteen_le_log_x [ProofData] : 16 ≤ Real.log x := by
  have hlogx : 0 < Real.log x := log_x_pos
  have hUV : Real.exp (Real.sqrt (Real.log x) + Real.sqrt (Real.log x)) ≤ Real.sqrt x := by
    rw [Real.exp_add]
    calc Real.exp (Real.sqrt (Real.log x)) * Real.exp (Real.sqrt (Real.log x))
        ≤ U * V := mul_le_mul le_U le_V (le_of_lt (Real.exp_pos _)) ProofData.U_nonneg
      _ ≤ Real.sqrt x := ProofData.UV_le
  have h1 : Real.sqrt (Real.log x) + Real.sqrt (Real.log x) ≤ Real.log (Real.sqrt x) := by
    have := Real.log_le_log (Real.exp_pos _) hUV
    rwa [Real.log_exp] at this
  rw [Real.log_sqrt ProofData.x_nonneg] at h1
  have ht : Real.sqrt (Real.log x) ^ 2 = Real.log x := Real.sq_sqrt (le_of_lt hlogx)
  nlinarith [Real.sqrt_nonneg (Real.log x), hlogx, h1, ht,
    sq_nonneg (Real.sqrt (Real.log x) - 4)]

/-- A power `(log x)^j` is bounded by `K · x/(log x)^N` (with `K` depending on `j+N`),
since `(log x)^{j+N} ≤ K·√x ≤ K·x`. -/
theorem log_pow_le_div [ProofData] (j N : ℕ) :
    (Real.log x) ^ j ≤ (2 * ((j + N : ℕ) : ℝ)) ^ (j + N) * (x / (Real.log x) ^ N) := by
  have hlogx : 0 < Real.log x := log_x_pos
  have hsqrtx : Real.sqrt x ≤ x := by
    have h1 : 1 ≤ Real.sqrt x := Real.one_le_sqrt.mpr (by linarith [le_x])
    nlinarith [Real.sq_sqrt x_nonneg, h1, Real.sqrt_nonneg x]
  have hKx : (Real.log x) ^ (j + N) ≤ (2 * ((j + N : ℕ) : ℝ)) ^ (j + N) * x := by
    have h := log_pow_le_const_mul_rpow (by linarith [le_x] : (1:ℝ) ≤ x) (j + N)
      (δ := (1/2 : ℝ)) (by norm_num)
    have hconst : (((j + N : ℕ) : ℝ) / (1/2 : ℝ)) = 2 * ((j + N : ℕ) : ℝ) := by ring
    rw [hconst] at h
    refine le_trans h ?_
    have hxle : x ^ (1/2 : ℝ) ≤ x := by
      calc x ^ (1/2:ℝ) ≤ x ^ (1:ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith [le_x]) (by norm_num)
        _ = x := Real.rpow_one x
    gcongr
  rw [← mul_div_assoc, le_div_iff₀ (by positivity : (0:ℝ) < (Real.log x) ^ N), ← pow_add]
  exact hKx

open Classical in
/-- The implied constant in `Delta_LambdaFlat_small_conductor` (and the per-term bound). -/
noncomputable def C_DLF (A C : ℕ) : ℝ :=
  (C_SW (A + 2 * C + 1) (2 * C) + C_SW (A + 2 * C + 1) 0) * 2 ^ (A + 2 * C + 1)
  + 3 * (Real.log 2)⁻¹ * (2 * ((2 + (A + 2 * C + 1) : ℕ) : ℝ)) ^ (2 + (A + 2 * C + 1))
  + C_DLS * (2 * (4 * ((A + 2 * C + 2 : ℕ) : ℝ)) ^ (A + 2 * C + 2))
  + 2 * (2 * ((1 + (A + 2 * C + 1) : ℕ) : ℝ)) ^ (1 + (A + 2 * C + 1))

/-- The Siegel–Walfisz constant is nonnegative (it bounds an absolute value). -/
theorem C_SW_nonneg [ProofData] (A C : ℕ) : 0 ≤ C_SW A C := by
  have h := siegel_walfisz A C le_x (q := 1) one_pos
    (by exact_mod_cast one_le_pow₀ one_le_log_x) (a := (1 : ZMod 1)) isUnit_one
  have hpos : 0 < x / Real.log x ^ A := div_pos x_pos (pow_pos log_x_pos A)
  have h0 : (0:ℝ) ≤ C_SW A C * (x / Real.log x ^ A) := le_trans (abs_nonneg _) h
  exact (mul_nonneg_iff_of_pos_right hpos).mp h0

/-- `√x · (log x)^j` is bounded by `K · x/(log x)^N`. -/
theorem sqrt_mul_log_pow_le_div [ProofData] (j N : ℕ) :
    Real.sqrt x * (Real.log x) ^ j
      ≤ (2 * ((j + N : ℕ) : ℝ)) ^ (j + N) * (x / (Real.log x) ^ N) := by
  have hlogx : 0 < Real.log x := log_x_pos
  have hsx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt x_nonneg
  have hkey : (Real.log x) ^ (j + N) ≤ (2 * ((j + N : ℕ) : ℝ)) ^ (j + N) * Real.sqrt x := by
    have h := log_pow_le_const_mul_rpow (by linarith [le_x] : (1:ℝ) ≤ x) (j + N)
      (δ := (1/2 : ℝ)) (by norm_num)
    have hconst : (((j + N : ℕ) : ℝ) / (1/2 : ℝ)) = 2 * ((j + N : ℕ) : ℝ) := by ring
    rwa [hconst, ← Real.sqrt_eq_rpow] at h
  rw [← mul_div_assoc, le_div_iff₀ (by positivity : (0:ℝ) < (Real.log x) ^ N)]
  calc Real.sqrt x * (Real.log x) ^ j * (Real.log x) ^ N
      = Real.sqrt x * (Real.log x) ^ (j + N) := by rw [mul_assoc, ← pow_add]
    _ ≤ Real.sqrt x * ((2 * ((j + N : ℕ) : ℝ)) ^ (j + N) * Real.sqrt x) :=
        mul_le_mul_of_nonneg_left hkey (Real.sqrt_nonneg x)
    _ = (2 * ((j + N : ℕ) : ℝ)) ^ (j + N) * x := by
        linear_combination (2 * ((j + N : ℕ) : ℝ)) ^ (j + N) * hsx

/-- Per-term Type-II bound: for a small conductor `s ≤ (log x)^C` and a restriction modulus
`q ≤ √x`, decomposing `Λ♭ = Λ - Λ♯ - Λ_{≤U}` and applying Siegel–Walfisz (main term), the
sharp bound, and the small bound gives `|Δ_{Λ♭_q}| ≪ x/(log x)^{A+2C+1}`. The divisor factor
`τ(q)` from the sharp bound is absorbed via `τ(q) ≤ 2√q ≤ 2x^{1/4}`. -/
theorem Delta_onCoprime_LambdaFlat_pointwise [ProofData] (A C : ℕ) {y : ℝ}
    (hy1 : √x ≤ y) (hyx : y ≤ x)
    {q s : ℕ} (hs0 : 0 < s) (hsq : s ∣ q) (hq0 : 0 < q)
    (hq : (q:ℝ) ≤ √x)
    (hsC : (s:ℝ) ≤ (Real.log x) ^ C) {a : ZMod s} (ha : IsUnit a) :
    |Δ_[onCoprime q ⇑Λ♭](y; s, a)|
      ≤ C_DLF A C * (x / (Real.log x) ^ (A + 2 * C + 1)) := by
  haveI : NeZero s := ⟨by omega⟩
  have hlogx_pos : 0 < Real.log x := log_x_pos
  have hlogx16 : 16 ≤ Real.log x := sixteen_le_log_x
  have hWpos : 0 < x / (Real.log x) ^ (A + 2 * C + 1) := div_pos x_pos (pow_pos hlogx_pos _)
  have hsqrt_le_x : Real.sqrt x ≤ x := by
    have h1 : 1 ≤ Real.sqrt x := Real.one_le_sqrt.mpr (by linarith [le_x])
    nlinarith [Real.sq_sqrt x_nonneg, h1, Real.sqrt_nonneg x]
  have hq_sqrt : (q:ℝ) ≤ Real.sqrt x := hq
  -- 4 ≤ x, 2 ≤ √x ≤ y
  have h4x : (4:ℝ) ≤ x := by
    nlinarith [Real.add_one_le_exp (16:ℝ), Real.exp_log x_pos, Real.exp_le_exp.mpr hlogx16]
  have h2sqrt : (2:ℝ) ≤ Real.sqrt x := by
    have h := Real.sqrt_le_sqrt (show (4:ℝ) ≤ x from h4x)
    rwa [show Real.sqrt 4 = 2 by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)] at h
  have h2y : 2 ≤ y := le_trans h2sqrt hy1
  have hlogy_ge : Real.log x / 2 ≤ Real.log y := by
    calc Real.log x / 2 = Real.log (√x) := (Real.log_sqrt x_nonneg).symm
      _ ≤ Real.log y := Real.log_le_log (Real.sqrt_pos.mpr x_pos) hy1
  have hlogy_ge2 : 2 ≤ Real.log y := by linarith
  -- s ≤ (log y)^{2C}
  have hs2C : (s:ℝ) ≤ (Real.log y) ^ (2 * C) := by
    have hlcy : (0:ℝ) ≤ (Real.log y) ^ C := by positivity
    calc (s:ℝ) ≤ (Real.log x) ^ C := hsC
      _ ≤ (2 * Real.log y) ^ C := by gcongr; linarith
      _ = 2 ^ C * (Real.log y) ^ C := by rw [mul_pow]
      _ ≤ (Real.log y) ^ C * (Real.log y) ^ C :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hlogy_ge2 C) hlcy
      _ = (Real.log y) ^ (2 * C) := by rw [← pow_add, ← two_mul]
  -- decompose Λ♭ = Λ - Λ♯ - Λ≤U
  have hfun2 : onCoprime q (⇑Λ♭)
      = onCoprime q (⇑Λ) - onCoprime q (⇑Λ♯) - onCoprime q (⇑Λ≤U) := by
    funext n
    simp only [onCoprime_apply, Pi.sub_apply]
    split_ifs with h
    · have := Lambda_decomp n; linarith
    · ring
  -- (i) main term via Siegel–Walfisz
  have hMain : |Δ_[onCoprime q (⇑Λ)](y; s, a)|
      ≤ (C_SW (A + 2 * C + 1) (2 * C) + C_SW (A + 2 * C + 1) 0) * 2 ^ (A + 2 * C + 1)
          * (x / (Real.log x) ^ (A + 2 * C + 1))
        + 3 * (Real.log 2)⁻¹ * (2 * ((2 + (A + 2 * C + 1) : ℕ) : ℝ)) ^ (2 + (A + 2 * C + 1))
          * (x / (Real.log x) ^ (A + 2 * C + 1)) := by
    have hb := Delta_onCoprime_Lambda_bound (A + 2 * C + 1) (2 * C) h2y hyx hs0 hsq hq0 hq_sqrt
      hs2C ha
    have hcsw : 0 ≤ C_SW (A + 2 * C + 1) (2 * C) + C_SW (A + 2 * C + 1) 0 :=
      add_nonneg (C_SW_nonneg _ _) (C_SW_nonneg _ _)
    have hconv1 : (C_SW (A + 2 * C + 1) (2 * C) + C_SW (A + 2 * C + 1) 0)
          * (y / (Real.log y) ^ (A + 2 * C + 1))
        ≤ (C_SW (A + 2 * C + 1) (2 * C) + C_SW (A + 2 * C + 1) 0) * 2 ^ (A + 2 * C + 1)
          * (x / (Real.log x) ^ (A + 2 * C + 1)) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (y_div_logy_le_x_div_logx hy1 hyx (A + 2 * C + 1)) hcsw
    have hconv2 : 3 * (Real.log 2)⁻¹ * (Real.log x) ^ 2
        ≤ 3 * (Real.log 2)⁻¹ * (2 * ((2 + (A + 2 * C + 1) : ℕ) : ℝ)) ^ (2 + (A + 2 * C + 1))
          * (x / (Real.log x) ^ (A + 2 * C + 1)) := by
      nlinarith [mul_le_mul_of_nonneg_left (log_pow_le_div 2 (A + 2 * C + 1))
        (show (0:ℝ) ≤ 3 * (Real.log 2)⁻¹ by positivity)]
    linarith [hb, hconv1, hconv2]
  -- (ii) sharp term: keep the `τ(q)` factor and absorb it via `τ(q) ≤ 2√q ≤ 2x^{1/4}`
  have hSharp : |Δ_[onCoprime q (⇑Λ♯)](y; s, a)|
      ≤ C_DLS * (2 * (4 * ((A + 2 * C + 2 : ℕ) : ℝ)) ^ (A + 2 * C + 2))
          * (x / (Real.log x) ^ (A + 2 * C + 1)) := by
    have hb := Delta_LambdaSharp_bound (q := s) (r := q) ha (le_trans hq_sqrt hsqrt_le_x) h2y hyx
    refine le_trans hb ?_
    have hCDLS : (0:ℝ) ≤ C_DLS := by norm_num [C_DLS]
    have hcore := card_divisors_mul_sqrt_mul_log_le_div hq_sqrt (A + 2 * C + 1)
    have hstep : (q.divisors.card : ℝ) * (U * V) * Real.log x
        ≤ (q.divisors.card : ℝ) * Real.sqrt x * Real.log x :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left UV_le (by positivity)) hlogx_pos.le
    calc C_DLS * (q.divisors.card : ℝ) * U * V * Real.log x
        = C_DLS * ((q.divisors.card : ℝ) * (U * V) * Real.log x) := by ring
      _ ≤ C_DLS * ((q.divisors.card : ℝ) * Real.sqrt x * Real.log x) :=
          mul_le_mul_of_nonneg_left hstep hCDLS
      _ ≤ C_DLS * (2 * (4 * ((A + 2 * C + 2 : ℕ) : ℝ)) ^ (A + 2 * C + 2)
            * (x / (Real.log x) ^ (A + 2 * C + 1))) :=
          mul_le_mul_of_nonneg_left hcore hCDLS
      _ = C_DLS * (2 * (4 * ((A + 2 * C + 2 : ℕ) : ℝ)) ^ (A + 2 * C + 2))
            * (x / (Real.log x) ^ (A + 2 * C + 1)) := by ring
  -- (iii) small term
  have hSmall : |Δ_[onCoprime q (⇑Λ≤U)](y; s, a)|
      ≤ 2 * (2 * ((1 + (A + 2 * C + 1) : ℕ) : ℝ)) ^ (1 + (A + 2 * C + 1))
          * (x / (Real.log x) ^ (A + 2 * C + 1)) := by
    refine le_trans (Delta_onCoprime_LambdaLEU_bound hs0) ?_
    have hconv : Real.sqrt x * (Real.log x) ^ 1
        ≤ (2 * ((1 + (A + 2 * C + 1) : ℕ) : ℝ)) ^ (1 + (A + 2 * C + 1))
          * (x / (Real.log x) ^ (A + 2 * C + 1)) := sqrt_mul_log_pow_le_div 1 (A + 2 * C + 1)
    rw [pow_one] at hconv
    calc 2 * U * Real.log x
        ≤ 2 * (Real.sqrt x * Real.log x) := by
          nlinarith [U_le_sqrt_x, hlogx_pos.le, U_nonneg, Real.sqrt_nonneg x]
      _ ≤ 2 * ((2 * ((1 + (A + 2 * C + 1) : ℕ) : ℝ)) ^ (1 + (A + 2 * C + 1))
            * (x / (Real.log x) ^ (A + 2 * C + 1))) := mul_le_mul_of_nonneg_left hconv (by norm_num)
      _ = 2 * (2 * ((1 + (A + 2 * C + 1) : ℕ) : ℝ)) ^ (1 + (A + 2 * C + 1))
            * (x / (Real.log x) ^ (A + 2 * C + 1)) := by ring
  -- assemble
  rw [hfun2, Delta_sub, Delta_sub]
  set DΛ := Δ_[onCoprime q ⇑Λ](y; s, a) with hDΛ
  set DΛs := Δ_[onCoprime q ⇑Λ♯](y; s, a) with hDΛs
  set DΛU := Δ_[onCoprime q ⇑Λ≤U](y; s, a) with hDΛU
  have htri : |DΛ - DΛs - DΛU| ≤ |DΛ| + |DΛs| + |DΛU| := by
    calc |DΛ - DΛs - DΛU| ≤ |DΛ - DΛs| + |DΛU| := abs_sub _ _
      _ ≤ |DΛ| + |DΛs| + |DΛU| := by gcongr; exact abs_sub _ _
  refine le_trans htri ?_
  have hCeq : C_DLF A C * (x / (Real.log x) ^ (A + 2 * C + 1))
      = ((C_SW (A + 2 * C + 1) (2 * C) + C_SW (A + 2 * C + 1) 0) * 2 ^ (A + 2 * C + 1)
            * (x / (Real.log x) ^ (A + 2 * C + 1))
          + 3 * (Real.log 2)⁻¹ * (2 * ((2 + (A + 2 * C + 1) : ℕ) : ℝ)) ^ (2 + (A + 2 * C + 1))
            * (x / (Real.log x) ^ (A + 2 * C + 1)))
        + C_DLS * (2 * (4 * ((A + 2 * C + 2 : ℕ) : ℝ)) ^ (A + 2 * C + 2))
            * (x / (Real.log x) ^ (A + 2 * C + 1))
        + 2 * (2 * ((1 + (A + 2 * C + 1) : ℕ) : ℝ)) ^ (1 + (A + 2 * C + 1))
            * (x / (Real.log x) ^ (A + 2 * C + 1)) := by
    rw [C_DLF]; ring
  rw [hCeq]
  linarith [hMain, hSharp, hSmall]

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
theorem Delta_LambdaFlat_small_conductor [ProofData] (A C : ℕ) {y : ℝ}
    (hy1 : √x ≤ y) (hyx : y ≤ x) (q : ℕ) (hq0 : 0 < q)
    (hq : (q:ℝ) ≤ √x) (a : ZMod q) (ha : IsUnit a) :
    |∑ d ∈ q.divisors with 1 < (d : ℕ) ∧ ↑d ≤ (Real.log x)^C,
      ∑ p ∈ d.divisorsAntidiagonal, μ p.2 * ↑p.1.totient * Δ_[onCoprime q Λ♭](y; p.1, a.cast)|
    ≤ C_DLF A C * x / (Real.log x) ^ (A + 1) := by
  have hlogx_pos : 0 < Real.log x := log_x_pos
  have hWpos : 0 < x / (Real.log x) ^ (A + 2 * C + 1) := div_pos x_pos (pow_pos hlogx_pos _)
  have hCDLF_nonneg : 0 ≤ C_DLF A C := by
    rw [C_DLF]
    have h1 := C_SW_nonneg (A + 2 * C + 1) (2 * C)
    have h2 := C_SW_nonneg (A + 2 * C + 1) 0
    have t1 : (0:ℝ) ≤ (C_SW (A + 2 * C + 1) (2 * C) + C_SW (A + 2 * C + 1) 0) * 2 ^ (A + 2 * C + 1) :=
      mul_nonneg (by linarith) (by positivity)
    have t2 : (0:ℝ) ≤ 3 * (Real.log 2)⁻¹
        * (2 * ((2 + (A + 2 * C + 1) : ℕ) : ℝ)) ^ (2 + (A + 2 * C + 1)) := by positivity
    have t3 : (0:ℝ) ≤ C_DLS * (2 * (4 * ((A + 2 * C + 2 : ℕ) : ℝ)) ^ (A + 2 * C + 2)) := by
      have hC : (0:ℝ) ≤ C_DLS := by norm_num [C_DLS]
      exact mul_nonneg hC (by positivity)
    have t4 : (0:ℝ) ≤ 2 * (2 * ((1 + (A + 2 * C + 1) : ℕ) : ℝ)) ^ (1 + (A + 2 * C + 1)) := by
      positivity
    linarith
  set S := q.divisors.filter (fun d => 1 < (d : ℕ) ∧ (↑d : ℝ) ≤ (Real.log x) ^ C) with hS
  -- per-`d` bound: `|∑_p …| ≤ C_DLF · W · d`
  have hfd : ∀ d ∈ S, |∑ p ∈ d.divisorsAntidiagonal,
        (μ p.2 : ℝ) * ↑p.1.totient * Δ_[onCoprime q Λ♭](y; p.1, a.cast)|
      ≤ C_DLF A C * (x / (Real.log x) ^ (A + 2 * C + 1)) * (d : ℝ) := by
    intro d hd
    rw [hS, Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdq, hqne⟩, hd1, hdlog⟩ := hd
    have hdpos : 0 < d := by omega
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hbound : ∀ p ∈ d.divisorsAntidiagonal,
        |(μ p.2 : ℝ) * ↑p.1.totient * Δ_[onCoprime q Λ♭](y; p.1, a.cast)|
          ≤ (C_DLF A C * (x / (Real.log x) ^ (A + 2 * C + 1))) * (p.1.totient : ℝ) := by
      intro p hp
      rw [Nat.mem_divisorsAntidiagonal] at hp
      obtain ⟨hpd, _⟩ := hp
      have hp1d : p.1 ∣ d := ⟨p.2, hpd.symm⟩
      have hp1q : p.1 ∣ q := hp1d.trans hdq
      have hp1pos : 0 < p.1 := Nat.pos_of_dvd_of_pos hp1d hdpos
      have hp1le : (p.1 : ℝ) ≤ (Real.log x) ^ C :=
        le_trans (by exact_mod_cast Nat.le_of_dvd hdpos hp1d) hdlog
      have hacast : IsUnit (a.cast : ZMod p.1) := isUnit_cast_of_dvd hp1q ha
      have hpt := Delta_onCoprime_LambdaFlat_pointwise A C hy1 hyx hp1pos hp1q hq0 hq hp1le hacast
      have hμ : |(μ p.2 : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (p.1.totient : ℝ))]
      calc |(μ p.2 : ℝ)| * (p.1.totient : ℝ) * |Δ_[onCoprime q Λ♭](y; p.1, a.cast)|
          ≤ 1 * (p.1.totient : ℝ) * (C_DLF A C * (x / (Real.log x) ^ (A + 2 * C + 1))) := by
            gcongr
        _ = (C_DLF A C * (x / (Real.log x) ^ (A + 2 * C + 1))) * (p.1.totient : ℝ) := by ring
    refine le_trans (Finset.sum_le_sum hbound) ?_
    rw [← Finset.mul_sum]
    have hsumφ : ∑ p ∈ d.divisorsAntidiagonal, (p.1.totient : ℝ) = (d : ℝ) := by
      rw [Nat.sum_divisorsAntidiagonal (f := fun a b => ((a.totient : ℝ))), ← Nat.cast_sum]
      congr 1
      exact Nat.sum_totient d
    rw [hsumφ]
  -- sum over `d`, then `∑_{d∈S} d ≤ (log x)^{2C}`
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum hfd) ?_
  rw [← Finset.mul_sum]
  have hsumd : (∑ d ∈ S, (d : ℝ)) ≤ (Real.log x) ^ (2 * C) := by
    have hsub : S ⊆ Finset.Icc 1 ⌊(Real.log x) ^ C⌋₊ := by
      intro d hd
      rw [hS, Finset.mem_filter] at hd
      rw [Finset.mem_Icc]
      refine ⟨by omega, Nat.le_floor hd.2.2⟩
    have hcardnat : S.card ≤ ⌊(Real.log x) ^ C⌋₊ := by
      have := Finset.card_le_card hsub
      rwa [Nat.card_Icc, Nat.add_sub_cancel] at this
    have hcard : (S.card : ℝ) ≤ (Real.log x) ^ C :=
      le_trans (by exact_mod_cast hcardnat) (Nat.floor_le (by positivity))
    have h1 : (∑ d ∈ S, (d : ℝ)) ≤ (S.card : ℝ) * (Real.log x) ^ C := by
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      apply Finset.sum_le_sum
      intro d hd
      rw [hS, Finset.mem_filter] at hd
      exact hd.2.2
    calc (∑ d ∈ S, (d : ℝ)) ≤ (S.card : ℝ) * (Real.log x) ^ C := h1
      _ ≤ (Real.log x) ^ C * (Real.log x) ^ C :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = (Real.log x) ^ (2 * C) := by rw [← pow_add, ← two_mul]
  calc C_DLF A C * (x / (Real.log x) ^ (A + 2 * C + 1)) * (∑ d ∈ S, (d : ℝ))
      ≤ C_DLF A C * (x / (Real.log x) ^ (A + 2 * C + 1)) * (Real.log x) ^ (2 * C) :=
        mul_le_mul_of_nonneg_left hsumd (mul_nonneg hCDLF_nonneg hWpos.le)
    _ = C_DLF A C * x / (Real.log x) ^ (A + 1) := by
        rw [show A + 2 * C + 1 = (A + 1) + 2 * C by ring, pow_add]
        field_simp

/-- `maxy` of a function that is nonnegative on `[√x, x]` is nonnegative. -/
theorem maxy_nonneg [ProofData] {f : ℝ → ℝ}
    (hf : ∀ y, √x ≤ y → y ≤ x → 0 ≤ f y) : 0 ≤ maxy f := by
  rw [maxy]
  refine Real.iSup_nonneg (fun y ↦ Real.iSup_nonneg (fun hy ↦ hf y hy.1 hy.2))

/-- If `f` is bounded above by a nonnegative `B` on `[√x, x]`, then `f y ≤ maxy f`
for any `y ∈ [√x, x]`. -/
theorem le_maxy [ProofData] {f : ℝ → ℝ} {y : ℝ} (hy1 : √x ≤ y) (hy2 : y ≤ x)
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ z, √x ≤ z → z ≤ x → f z ≤ B) :
    f y ≤ maxy f := by
  rw [maxy]
  have hbdd : BddAbove (Set.range fun z => ⨆ (_ : z ∈ Set.Icc (√x) x), f z) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact Real.iSup_le (fun hz => hbound z hz.1 hz.2) hB
  refine le_ciSup_of_le hbdd y (le_of_eq ?_)
  have hmem : y ∈ Set.Icc (√x) x := Set.mem_Icc.mpr ⟨hy1, hy2⟩
  simp [hmem]

/-- `S r y ξ` is nonnegative (it is a norm). -/
theorem S_nonneg [ProofData] {q : ℕ} (r : ℕ) (y : ℝ) (ξ : DirichletCharacter ℂ q) :
    0 ≤ S r y ξ := norm_nonneg _

/-- `S r y ξ ≤ maxy (S r · ξ)` for `y ∈ [√x, x]`. -/
theorem S_le_maxy [ProofData] {q : ℕ} (r : ℕ) (ξ : DirichletCharacter ℂ q) {y : ℝ}
    (hy1 : √x ≤ y) (hy2 : y ≤ x) : S r y ξ ≤ maxy (fun y ↦ S r y ξ) := by
  refine le_maxy (f := fun y ↦ S r y ξ) hy1 hy2
    (B := summatory (fun n ↦ ‖onCoprime r Λ♭ n * ξ n‖) x)
    (summatory_nonneg _ _ (fun n _ ↦ norm_nonneg _)) (fun z hz1 hz2 ↦ ?_)
  simp only [S]
  rw [summatory]
  refine (norm_sum_le _ _).trans ?_
  rw [summatory]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Nat.Icc_mono_right hz2)
    (fun i _ _ ↦ norm_nonneg _)

/-- The implied constant in `Delta_LambdaFlat_small_conductor` is nonnegative. -/
theorem C_DLF_nonneg [ProofData] (A C : ℕ) : 0 ≤ C_DLF A C := by
  rw [C_DLF]
  have h1 := C_SW_nonneg (A + 2 * C + 1) (2 * C)
  have h2 := C_SW_nonneg (A + 2 * C + 1) 0
  have t1 : (0:ℝ) ≤ (C_SW (A + 2 * C + 1) (2 * C) + C_SW (A + 2 * C + 1) 0) * 2 ^ (A + 2 * C + 1) :=
    mul_nonneg (by linarith) (by positivity)
  have t2 : (0:ℝ) ≤ 3 * (Real.log 2)⁻¹
      * (2 * ((2 + (A + 2 * C + 1) : ℕ) : ℝ)) ^ (2 + (A + 2 * C + 1)) := by positivity
  have t3 : (0:ℝ) ≤ C_DLS * (2 * (4 * ((A + 2 * C + 2 : ℕ) : ℝ)) ^ (A + 2 * C + 2)) := by
    have hC : (0:ℝ) ≤ C_DLS := by norm_num [C_DLS]
    exact mul_nonneg hC (by positivity)
  have t4 : (0:ℝ) ≤ 2 * (2 * ((1 + (A + 2 * C + 1) : ℕ) : ℝ)) ^ (1 + (A + 2 * C + 1)) := by
    positivity
  linarith

/-! ### The totient bound `∑_{n ≤ Q} 1/φ(n) ≪ log x`

The proof writes `1/φ` as a Dirichlet convolution `fAF * invAF` (Step 3), where
`fAF d = μ(d)²/(d·φ(d))` and `invAF e = 1/e`.  The hyperbola identity
`ArithmeticFunction.summatory_mul_eq_summatory` then gives
`∑_{n≤Q} 1/φ(n) = ∑_{d≤Q} fAF d · ∑_{e≤Q/d} 1/e ≤ (∑_d fAF d)·(1 + log x) ≤ C_tot · log x`,
using the harmonic bound (Step 6), summability of `fAF` (Steps 4–5), and `1 ≤ log x`.
-/

/-- `e ↦ 1/e` as an arithmetic function (Dirichlet "harmonic" factor `g`). -/
noncomputable def invAF : ArithmeticFunction ℝ where
  toFun n := (n : ℝ)⁻¹
  map_zero' := by simp

@[simp] theorem invAF_apply (n : ℕ) : invAF n = (n : ℝ)⁻¹ := rfl

/-- `d ↦ μ(d)² / (d · φ(d))`; the Dirichlet factor `f` with `1/φ = fAF * invAF`. -/
noncomputable def fAF : ArithmeticFunction ℝ where
  toFun d := ((μ d : ℝ) ^ 2) / (d * d.totient)
  map_zero' := by simp

@[simp] theorem fAF_apply (d : ℕ) : fAF d = ((μ d : ℝ) ^ 2) / (d * d.totient) := rfl

/-- `n ↦ 1/φ(n)` as an arithmetic function. -/
noncomputable def invTotientAF : ArithmeticFunction ℝ where
  toFun n := (n.totient : ℝ)⁻¹
  map_zero' := by simp

@[simp] theorem invTotientAF_apply (n : ℕ) : invTotientAF n = (n.totient : ℝ)⁻¹ := rfl

theorem fAF_nonneg (d : ℕ) : 0 ≤ fAF d := by
  rw [fAF_apply]; positivity

/-- Termwise bound at a prime power, with a factor `2` that is only required at `p = 2`:
`p^k ≤ (if p = 2 then 2 else 1) · (φ(p^k))²`. -/
private theorem primePow_le {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    p ^ k ≤ (if p = 2 then 2 else 1) * ((p ^ k).totient) ^ 2 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.totient_prime_pow hp (by omega), show 1 + j - 1 = j by omega]
  rcases eq_or_ne p 2 with rfl | hp2
  · rw [if_pos rfl, show (2:ℕ) - 1 = 1 by rfl, mul_one, ← pow_mul, ← pow_succ']
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  · rw [if_neg hp2, one_mul]
    have hp3 : 3 ≤ p := by
      have h2 := hp.two_le
      have := Nat.odd_iff.mp ((hp.eq_two_or_odd').resolve_left hp2)
      omega
    have hp1 : 1 ≤ p ^ j := Nat.one_le_pow _ _ (by omega)
    have hsq : p ≤ (p - 1) ^ 2 := by
      obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
      have h2m : 2 ≤ m := by omega
      simp only [Nat.add_sub_cancel]
      nlinarith [h2m]
    calc p ^ (1 + j) = p ^ j * p := by rw [pow_add, pow_one, mul_comm]
      _ ≤ p ^ j * (p ^ j * (p - 1) ^ 2) := by
            gcongr
            calc p ≤ (p - 1) ^ 2 := hsq
              _ ≤ p ^ j * (p - 1) ^ 2 := Nat.le_mul_of_pos_left _ (by omega)
      _ = (p ^ j * (p - 1)) ^ 2 := by ring

/-- A clean lower bound for the totient: `d ≤ 2·φ(d)²` (so `φ(d) ≥ √(d/2)`).  No exceptions. -/
theorem d_le_two_mul_totient_sq (d : ℕ) : d ≤ 2 * d.totient ^ 2 := by
  rcases eq_or_ne d 0 with rfl | hd0
  · simp
  set S := d.factorization.support with hS
  -- `c p = if p = 2 then 2 else 1` collects the prime-2 factor; its product is `≤ 2`.
  have hc : ∏ p ∈ S, (if p = 2 then 2 else 1) ≤ 2 := by
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
    calc (2:ℕ) ^ (S.filter (· = 2)).card ≤ 2 ^ 1 := by
          apply Nat.pow_le_pow_right (by norm_num)
          rw [Finset.filter_eq']
          split <;> simp
      _ = 2 := by norm_num
  -- the totient as a product over prime factors
  have hφ : d.totient = ∏ p ∈ S, (p ^ (d.factorization p)).totient := by
    rw [Nat.totient_eq_prod_factorization hd0]
    refine Finset.prod_congr rfl (fun p hp ↦ ?_)
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by rwa [hS, Nat.support_factorization] at hp)
    have hk : 1 ≤ d.factorization p := by rw [hS, Finsupp.mem_support_iff] at hp; omega
    rw [Nat.totient_prime_pow hpp hk]
  calc d = ∏ p ∈ S, p ^ (d.factorization p) := (Nat.factorization_prod_pow_eq_self hd0).symm
    _ ≤ ∏ p ∈ S, (if p = 2 then 2 else 1) * ((p ^ (d.factorization p)).totient) ^ 2 := by
        refine Finset.prod_le_prod' (fun p hp ↦ ?_)
        have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by rwa [hS, Nat.support_factorization] at hp)
        have hk : 1 ≤ d.factorization p := by rw [hS, Finsupp.mem_support_iff] at hp; omega
        exact primePow_le hpp hk
    _ = (∏ p ∈ S, (if p = 2 then 2 else 1)) *
          ∏ p ∈ S, ((p ^ (d.factorization p)).totient) ^ 2 := Finset.prod_mul_distrib
    _ ≤ 2 * ∏ p ∈ S, ((p ^ (d.factorization p)).totient) ^ 2 := by gcongr
    _ = 2 * d.totient ^ 2 := by rw [hφ, Finset.prod_pow]

/-- **Step 4.** Comparison bound `fAF d ≤ √2 · (1/d^(3/2))`, from `d ≤ 2·φ(d)²`. -/
theorem fAF_le_rpow (d : ℕ) : fAF d ≤ Real.sqrt 2 * (1 / (d : ℝ) ^ ((3 : ℝ) / 2)) := by
  rcases eq_or_ne d 0 with rfl | hd0
  · simp [Real.zero_rpow (by norm_num : (3 : ℝ) / 2 ≠ 0)]
  have hdR : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd0
  have hφR : (0 : ℝ) < d.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hd0)
  have hμ : ((μ d : ℝ)) ^ 2 ≤ 1 := by
    have : ((μ d : ℝ)) ^ 2 = if Squarefree d then 1 else 0 := by
      rw [← Int.cast_pow, ArithmeticFunction.moebius_sq]; split <;> simp
    rw [this]; split <;> norm_num
  have hφsq : (d : ℝ) ≤ 2 * (d.totient : ℝ) ^ 2 := by exact_mod_cast d_le_two_mul_totient_sq d
  have hpow : (d : ℝ) ^ ((3 : ℝ) / 2) = d * Real.sqrt d := by
    rw [Real.sqrt_eq_rpow, show ((3 : ℝ) / 2) = 1 + 1 / 2 by norm_num,
      Real.rpow_add hdR, Real.rpow_one]
  have hsqrt : Real.sqrt d ≤ Real.sqrt 2 * d.totient := by
    rw [show Real.sqrt 2 * (d.totient : ℝ) = Real.sqrt (2 * (d.totient) ^ 2) by
          rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hφR.le]]
    exact Real.sqrt_le_sqrt hφsq
  rw [fAF_apply]
  calc ((μ d : ℝ)) ^ 2 / ((d : ℝ) * d.totient)
      ≤ 1 / ((d : ℝ) * d.totient) := by gcongr
    _ ≤ Real.sqrt 2 * (1 / (d : ℝ) ^ ((3 : ℝ) / 2)) := by
        rw [mul_one_div, div_le_iff₀ (mul_pos hdR hφR), div_mul_eq_mul_div,
            le_div_iff₀ (Real.rpow_pos_of_pos hdR _), one_mul, hpow]
        calc (d : ℝ) * Real.sqrt d
            ≤ (d : ℝ) * (Real.sqrt 2 * d.totient) := mul_le_mul_of_nonneg_left hsqrt hdR.le
          _ = Real.sqrt 2 * ((d : ℝ) * d.totient) := by ring

/-- **Step 5.** `fAF` is summable, by comparison with the convergent `3/2`-series. -/
theorem summable_fAF : Summable (fun d ↦ fAF d) := by
  apply Summable.of_nonneg_of_le fAF_nonneg fAF_le_rpow
  apply Summable.mul_left
  simpa using (Real.summable_one_div_nat_rpow.mpr (by norm_num : (1 : ℝ) < 3 / 2))

/-- **Step 3 (TODO).** The Dirichlet convolution identity `1/φ = fAF * invAF`.
Both sides are multiplicative; reduce to prime powers via `multiplicative_factorization`,
where `(fAF * invAF)(pᵏ) = 1/pᵏ + 1/(pᵏ(p-1)) = 1/(pᵏ⁻¹(p-1)) = 1/φ(pᵏ)`. -/
theorem invAF_isMultiplicative : invAF.IsMultiplicative := by
  refine ⟨by simp, fun {m n} _ ↦ ?_⟩
  simp only [invAF_apply, Nat.cast_mul, mul_inv]

theorem fAF_isMultiplicative : fAF.IsMultiplicative := by
  refine ⟨by simp [fAF_apply], fun {m n} h ↦ ?_⟩
  simp only [fAF_apply]
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h, Nat.totient_mul h]
  push_cast
  ring

theorem invTotientAF_isMultiplicative : invTotientAF.IsMultiplicative := by
  refine ⟨by simp [invTotientAF_apply], fun {m n} h ↦ ?_⟩
  simp only [invTotientAF_apply, Nat.totient_mul h, Nat.cast_mul, mul_inv]

theorem invTotientAF_eq_mul : invTotientAF = fAF * invAF := by
  rw [ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers invTotientAF
        invTotientAF_isMultiplicative (fAF * invAF)
        (fAF_isMultiplicative.mul invAF_isMultiplicative)]
  intro p i hp
  -- `fAF` vanishes at `p^x` for `x ≥ 2` (since `μ(p^x) = 0`).
  have hvanish : ∀ x, 2 ≤ x → fAF (p ^ x) = 0 := fun x hx => by
    rw [fAF_apply, ArithmeticFunction.moebius_apply_prime_pow hp (by omega), if_neg (by omega)]
    simp
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [invTotientAF_apply, (fAF_isMultiplicative.mul invAF_isMultiplicative).map_one]
  -- `i ≥ 1`: expand the convolution as a sum over `range (i+1)`, keeping only `x = 0, 1`.
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => fAF a * invAF b),
      Nat.sum_divisors_prime_pow hp]
  have hsub : Finset.range 2 ⊆ Finset.range (j + 1 + 1) := by
    intro a ha; simp only [Finset.mem_range] at *; omega
  rw [← Finset.sum_subset hsub (fun x _ hx => by
        rw [Finset.mem_range, not_lt] at hx
        rw [hvanish x hx, zero_mul]),
      Finset.sum_range_succ, Finset.sum_range_one]
  -- two surviving terms; simplify the divisions and arithmetic-function values
  have d1 : p ^ (j + 1) / p = p ^ j := by
    rw [pow_succ, Nat.mul_div_cancel _ hp.pos]
  rw [pow_zero, pow_one, Nat.div_one, d1]
  simp only [invTotientAF_apply, fAF_apply, invAF_apply, Nat.totient_prime_pow hp hi,
    Nat.totient_prime hp, Nat.totient_one, ArithmeticFunction.moebius_apply_one,
    ArithmeticFunction.moebius_apply_prime hp]
  have hp1 : 1 ≤ p := hp.one_le
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpne : (p : ℝ) ≠ 0 := by positivity
  have hp1ne : (p : ℝ) - 1 ≠ 0 := by linarith
  have hpjne : (p : ℝ) ^ j ≠ 0 := by positivity
  push_cast [Nat.cast_sub hp1]
  field_simp
  ring

/-- **Step 6 (TODO).** Partial harmonic-sum bound `∑_{e ≤ t} 1/e ≤ 1 + log t` for `t ≥ 1`,
via `summatory (⇑invAF) t = (harmonic ⌊t⌋ : ℝ)` and `harmonic_le_one_add_log`. -/
theorem summatory_invAF_le {t : ℝ} (ht : 1 ≤ t) :
    summatory (⇑invAF) t ≤ 1 + Real.log t := by
  have h0 : (0 : ℝ) ≤ t := by linarith
  have hset : Nat.Icc (1 : ℝ) t = Finset.Icc 1 ⌊t⌋₊ := by
    ext n
    simp only [Nat.mem_Icc, Finset.mem_Icc, Nat.le_floor_iff h0, Nat.one_le_cast]
  have heq : summatory (⇑invAF) t = (harmonic ⌊t⌋₊ : ℝ) := by
    rw [summatory, hset, harmonic_eq_sum_Icc]
    push_cast
    exact Finset.sum_congr rfl (fun n _ ↦ by rw [invAF_apply])
  rw [heq]
  exact harmonic_floor_le_one_add_log t ht

/-- The Mertens-type constant `∑_d μ(d)²/(d φ(d))`, doubled (the `2` converts `1 + log x`
into `2 log x` using `1 ≤ log x`). -/
noncomputable def C_tot : ℝ := 2 * ∑' d, fAF d

/-- The totient bound: `∑_{n ≤ Q} 1/φ(n) ≤ C_tot · log x`. -/
theorem summatory_totient_inv_le [ProofData] (Q : ℝ) (hQ : Q ≤ x) :
    summatory (fun n ↦ (n.totient : ℝ)⁻¹) Q ≤ C_tot * Real.log x := by
  have hlogx : (1 : ℝ) ≤ Real.log x := one_le_log_x
  have hlog_pos : 0 < Real.log x := by linarith
  -- Rewrite `1/φ` as the convolution `fAF * invAF`, then apply the hyperbola identity.
  rw [show (fun n ↦ (n.totient : ℝ)⁻¹) = ⇑(fAF * invAF) from by
        rw [← invTotientAF_eq_mul]; funext n; rw [invTotientAF_apply],
      ArithmeticFunction.summatory_mul_eq_summatory]
  rw [C_tot]
  calc summatory (fun n ↦ fAF n * summatory (⇑invAF) (Q / n)) Q
      ≤ summatory (fun n ↦ fAF n * (2 * Real.log x)) Q := by
        rw [summatory, summatory]
        refine Finset.sum_le_sum (fun d hd ↦ ?_)
        rw [Nat.mem_Icc] at hd
        have hd1 : (1 : ℝ) ≤ d := hd.1
        have hdpos : (0 : ℝ) < d := by linarith
        refine mul_le_mul_of_nonneg_left ?_ (fAF_nonneg d)
        have hQd1 : 1 ≤ Q / d := by
          rw [le_div_iff₀ hdpos]; linarith [hd.2]
        have hQdx : Q / d ≤ x := by
          calc Q / d ≤ Q := by rw [div_le_iff₀ hdpos]; nlinarith [hd.2]
            _ ≤ x := hQ
        calc summatory (⇑invAF) (Q / d)
            ≤ 1 + Real.log (Q / d) := summatory_invAF_le hQd1
          _ ≤ 1 + Real.log x := by
                have := Real.log_le_log (by linarith : (0 : ℝ) < Q / d) hQdx
                linarith
          _ ≤ 2 * Real.log x := by linarith
    _ = summatory (fun n ↦ fAF n) Q * (2 * Real.log x) := summatory_mul
    _ ≤ (∑' d, fAF d) * (2 * Real.log x) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [summatory]
        exact summable_fAF.sum_le_tsum _ (fun i _ ↦ fAF_nonneg i)
    _ = 2 * (∑' d, fAF d) * Real.log x := by ring

/-- The implied constant in `BV_LambdaFlat_via_T`. -/
noncomputable def C_BV_LFT (A C : ℕ) : ℝ := C_DLF A C * C_tot

/-- Per-`q` bound: combine the conductor decomposition with the small-conductor estimate and
replace each `S` by its maximum over `y`. -/
theorem maxya_Delta_LambdaFlat_le [ProofData] (A C : ℕ) {q : ℕ}
    (hq1 : 1 ≤ q) (hqx : (q : ℝ) ≤ √x) :
  open Classical in
    maxya q (fun y a ↦ |Δ_[Λ♭](y; q, a)|)
      ≤ (q.totient : ℝ)⁻¹ * (C_DLF A C * x / (Real.log x) ^ (A + 1))
        + (q.totient : ℝ)⁻¹ * ∑ d ∈ q.divisors with (Real.log x) ^ C < (d : ℕ),
            ∑ ξ : DirichletCharacter ℂ d with ξ.IsPrimitive, maxy (fun y ↦ S (q / d) y ξ) := by
  classical
  have hq0 : 0 < q := hq1
  have hφ : (0 : ℝ) ≤ (q.totient : ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
  refine maxya_le_unit (fun y hy1 hy2 a ha ↦ ?_) ?_
  · refine (Delta_LambdaFlat_decomp (C := C) (y := y) q a ha).trans (add_le_add ?_ ?_)
    · exact mul_le_mul_of_nonneg_left
        (Delta_LambdaFlat_small_conductor A C hy1 hy2 q hq0 hqx a ha) hφ
    · refine mul_le_mul_of_nonneg_left ?_ hφ
      exact Finset.sum_le_sum (fun d _ ↦ Finset.sum_le_sum (fun ξ _ ↦ S_le_maxy _ ξ hy1 hy2))
  · refine add_nonneg (mul_nonneg hφ ?_) (mul_nonneg hφ ?_)
    · exact div_nonneg (mul_nonneg (C_DLF_nonneg A C) x_pos.le) (by positivity)
    · exact Finset.sum_nonneg (fun d _ ↦ Finset.sum_nonneg
        (fun ξ _ ↦ maxy_nonneg (fun y _ _ ↦ S_nonneg _ _ _)))

/-- The summand of the regrouped main term: `1/(φ(d)φ(r)) · ∑*_{ξ mod d} maxₓ S_r(·, ξ)`. -/
noncomputable def gLFT [ProofData] (d r : ℕ) : ℝ :=
  open Classical in
  (d.totient : ℝ)⁻¹ * (r.totient : ℝ)⁻¹ *
    ∑ ξ : DirichletCharacter ℂ d with ξ.IsPrimitive, maxy (fun y ↦ S r y ξ)

theorem gLFT_nonneg [ProofData] (d r : ℕ) : 0 ≤ gLFT d r := by
  classical
  rw [gLFT]
  refine mul_nonneg (mul_nonneg (by positivity) (by positivity)) ?_
  exact Finset.sum_nonneg (fun ξ _ ↦ maxy_nonneg (fun y _ _ ↦ S_nonneg _ _ _))

@[blueprint (statement := /--
$$\sum_{q \le Q} \max_{\substack{\sqrt{x} \le y \le x \\ a \in (\Z/q\Z)^*}} \left|\Delta_{\Lambda^\flat}(y;\,q,\,a)\right| \le \sum_{r \le Q} \frac{T_r(x,Q)}{\varphi(r)} + O\!\left(\frac{x}{(\log x)^A}\right)$$
-/) (proof := /--
Sum the error from \ref{Delta_LambdaFlat_small_conductor} over $q \le Q$ using
$\sum_{n \le x} 1/\varphi(n) \ll \log x$, then regroup the main sum by $r = q/d$.
-/) (uses := [Delta_LambdaFlat_decomp, Delta_LambdaFlat_small_conductor, character_sum_Mobius, T])]
theorem BV_LambdaFlat_via_T [ProofData] (Q : ℝ) (A C : ℕ) (hQ : Q ≤ √x) :
    summatory (fun q ↦ maxya q fun y a ↦ |Δ_[Λ♭](y; q, a)|) Q
      ≤ summatory (fun r ↦ (r.totient : ℝ)⁻¹ * T C r Q) Q
        + C_BV_LFT A C * x / (Real.log x) ^ A := by
  classical
  have hlog_pos : 0 < Real.log x := log_x_pos
  have hlog_ne : Real.log x ≠ 0 := ne_of_gt hlog_pos
  have hsx : √x ≤ x := by
    rw [Real.sqrt_le_iff]
    exact ⟨ProofData.x_nonneg, le_self_pow₀ (by linarith [ProofData.le_x]) (by norm_num)⟩
  have hQx : Q ≤ x := le_trans hQ hsx
  set Kc : ℝ := C_DLF A C * x / (Real.log x) ^ (A + 1) with hKc
  have hKc_nonneg : 0 ≤ Kc := by
    rw [hKc]; exact div_nonneg (mul_nonneg (C_DLF_nonneg A C) x_pos.le) (by positivity)
  -- Rewrite the main bound as a double sum of `gLFT`.
  have hMB : summatory (fun r ↦ (r.totient : ℝ)⁻¹ * T C r Q) Q
      = ∑ r ∈ Nat.Icc 1 Q, ∑ d ∈ Nat.Icc ((Real.log x) ^ C) (Q / r), gLFT d r := by
    rw [summatory]
    refine Finset.sum_congr rfl (fun r _ ↦ ?_)
    rw [T, Real.rpow_natCast, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun d _ ↦ ?_)
    rw [gLFT]; ring
  -- Per-`q` bound, summed over `q ≤ Q`.
  have hkey : summatory (fun q ↦ maxya q fun y a ↦ |Δ_[Λ♭](y; q, a)|) Q
      ≤ ∑ q ∈ Nat.Icc 1 Q,
          ((q.totient : ℝ)⁻¹ * Kc
            + (q.totient : ℝ)⁻¹ * ∑ d ∈ q.divisors with (Real.log x) ^ C < (d : ℕ),
                ∑ ξ : DirichletCharacter ℂ d with ξ.IsPrimitive, maxy (fun y ↦ S (q / d) y ξ)) := by
    rw [summatory]
    refine Finset.sum_le_sum (fun q hq ↦ ?_)
    rw [Nat.mem_Icc] at hq
    rw [hKc]
    exact maxya_Delta_LambdaFlat_le A C (by exact_mod_cast hq.1) (le_trans hq.2 hQ)
  rw [Finset.sum_add_distrib] at hkey
  -- Bound the error part using the (assumed) totient bound.
  have hERR : ∑ q ∈ Nat.Icc 1 Q, (q.totient : ℝ)⁻¹ * Kc
      ≤ C_BV_LFT A C * x / (Real.log x) ^ A := by
    rw [← Finset.sum_mul]
    have htot : ∑ q ∈ Nat.Icc 1 Q, (q.totient : ℝ)⁻¹ ≤ C_tot * Real.log x := by
      have h := summatory_totient_inv_le Q hQx
      rwa [summatory] at h
    calc (∑ q ∈ Nat.Icc 1 Q, (q.totient : ℝ)⁻¹) * Kc
        ≤ (C_tot * Real.log x) * Kc := mul_le_mul_of_nonneg_right htot hKc_nonneg
      _ = C_BV_LFT A C * x / (Real.log x) ^ A := by
          rw [hKc, C_BV_LFT, pow_succ]; field_simp
  -- Bound the main part by regrouping `q = r·d`.
  have hMAIN : ∑ q ∈ Nat.Icc 1 Q, (q.totient : ℝ)⁻¹ *
        ∑ d ∈ q.divisors with (Real.log x) ^ C < (d : ℕ),
          ∑ ξ : DirichletCharacter ℂ d with ξ.IsPrimitive, maxy (fun y ↦ S (q / d) y ξ)
      ≤ summatory (fun r ↦ (r.totient : ℝ)⁻¹ * T C r Q) Q := by
    rw [hMB]
    -- Step A: distribute `1/φ(q)` and use `φ(d)φ(q/d) ≤ φ(q)` term by term.
    refine le_trans (b := ∑ q ∈ Nat.Icc 1 Q,
        ∑ d ∈ q.divisors with (Real.log x) ^ C < (d : ℕ), gLFT d (q / d)) ?_ ?_
    · refine Finset.sum_le_sum (fun q hq ↦ ?_)
      rw [Nat.mem_Icc] at hq
      have hq1 : 1 ≤ q := by exact_mod_cast hq.1
      have hqpos : 0 < q := hq1
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun d hd ↦ ?_)
      rw [Finset.mem_filter, Nat.mem_divisors] at hd
      obtain ⟨⟨hdvd, _⟩, _⟩ := hd
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hqpos
      have hqdpos : 0 < q / d := Nat.div_pos (Nat.le_of_dvd hqpos hdvd) hdpos
      have hsm := Nat.totient_super_multiplicative d (q / d)
      rw [Nat.mul_div_cancel' hdvd] at hsm
      have hcoef : (q.totient : ℝ)⁻¹ ≤ (d.totient : ℝ)⁻¹ * ((q / d).totient : ℝ)⁻¹ := by
        rw [← mul_inv]
        apply inv_anti₀
        · exact_mod_cast Nat.mul_pos (Nat.totient_pos.mpr hdpos) (Nat.totient_pos.mpr hqdpos)
        · exact_mod_cast hsm
      rw [gLFT]
      exact mul_le_mul_of_nonneg_right hcoef
        (Finset.sum_nonneg (fun ξ _ ↦ maxy_nonneg (fun y _ _ ↦ S_nonneg _ _ _)))
    -- Step B: reindex `(q, d) ↦ (q/d, d)`.
    · rw [Finset.sum_sigma', Finset.sum_sigma']
      set LHSsig := (Nat.Icc 1 Q).sigma
        (fun q => q.divisors.filter (fun d => (Real.log x) ^ C < (d : ℕ))) with hLHSsig
      set RHSsig := (Nat.Icc 1 Q).sigma
        (fun r => Nat.Icc ((Real.log x) ^ C) (Q / r)) with hRHSsig
      have hinj : ∀ σ₁ ∈ LHSsig, ∀ σ₂ ∈ LHSsig,
          (fun σ : Σ _ : ℕ, ℕ => (⟨σ.fst / σ.snd, σ.snd⟩ : Σ _ : ℕ, ℕ)) σ₁
            = (fun σ : Σ _ : ℕ, ℕ => (⟨σ.fst / σ.snd, σ.snd⟩ : Σ _ : ℕ, ℕ)) σ₂ → σ₁ = σ₂ := by
        intro σ₁ h₁ σ₂ h₂ heq
        obtain ⟨q₁, d₁⟩ := σ₁
        obtain ⟨q₂, d₂⟩ := σ₂
        simp only [Sigma.mk.injEq, heq_eq_eq] at heq
        simp only [hLHSsig, Finset.mem_sigma, Finset.mem_filter, Nat.mem_divisors] at h₁ h₂
        obtain ⟨_, ⟨hdvd1, _⟩, _⟩ := h₁
        obtain ⟨_, ⟨hdvd2, _⟩, _⟩ := h₂
        obtain ⟨hdiv, hd⟩ := heq
        have hq : q₁ = q₂ := by
          rw [← Nat.mul_div_cancel' hdvd1, ← Nat.mul_div_cancel' hdvd2, hdiv, hd]
        subst hq; subst hd; rfl
      calc ∑ σ ∈ LHSsig, gLFT σ.snd (σ.fst / σ.snd)
          = ∑ τ ∈ LHSsig.image
              (fun σ : Σ _ : ℕ, ℕ => (⟨σ.fst / σ.snd, σ.snd⟩ : Σ _ : ℕ, ℕ)), gLFT τ.snd τ.fst :=
            (Finset.sum_image (f := fun τ : Σ _ : ℕ, ℕ => gLFT τ.snd τ.fst) hinj).symm
        _ ≤ ∑ τ ∈ RHSsig, gLFT τ.snd τ.fst := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun τ _ _ ↦ gLFT_nonneg τ.snd τ.fst)
            intro τ hτ
            rw [Finset.mem_image] at hτ
            obtain ⟨σ, hσ, rfl⟩ := hτ
            obtain ⟨q, d⟩ := σ
            simp only [hLHSsig, Finset.mem_sigma, Finset.mem_filter, Nat.mem_divisors] at hσ
            obtain ⟨hqmem, ⟨hdvd, _⟩, hdL⟩ := hσ
            rw [Nat.mem_Icc] at hqmem
            have hq1 : 1 ≤ q := by exact_mod_cast hqmem.1
            have hqpos : 0 < q := hq1
            have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hqpos
            have hqdpos : 0 < q / d := Nat.div_pos (Nat.le_of_dvd hqpos hdvd) hdpos
            rw [hRHSsig, Finset.mem_sigma]
            refine ⟨?_, ?_⟩
            · rw [Nat.mem_Icc]
              refine ⟨by exact_mod_cast hqdpos, ?_⟩
              calc (↑(q / d) : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.div_le_self q d
                _ ≤ Q := hqmem.2
            · rw [Nat.mem_Icc]
              refine ⟨le_of_lt hdL, ?_⟩
              rw [le_div_iff₀ (by exact_mod_cast hqdpos : (0 : ℝ) < (↑(q / d) : ℝ))]
              calc (d : ℝ) * (↑(q / d) : ℝ) = ((d * (q / d) : ℕ) : ℝ) := by push_cast; ring
                _ = (q : ℝ) := by exact_mod_cast Nat.mul_div_cancel' hdvd
                _ ≤ Q := hqmem.2
  calc summatory (fun q ↦ maxya q fun y a ↦ |Δ_[Λ♭](y; q, a)|) Q
      ≤ (∑ q ∈ Nat.Icc 1 Q, (q.totient : ℝ)⁻¹ * Kc)
        + ∑ q ∈ Nat.Icc 1 Q, (q.totient : ℝ)⁻¹ *
            ∑ d ∈ q.divisors with (Real.log x) ^ C < (d : ℕ),
              ∑ ξ : DirichletCharacter ℂ d with ξ.IsPrimitive,
                maxy (fun y ↦ S (q / d) y ξ) := hkey
    _ ≤ (C_BV_LFT A C * x / (Real.log x) ^ A)
        + summatory (fun r ↦ (r.totient : ℝ)⁻¹ * T C r Q) Q := add_le_add hERR hMAIN
    _ = summatory (fun r ↦ (r.totient : ℝ)⁻¹ * T C r Q) Q
        + C_BV_LFT A C * x / (Real.log x) ^ A := by ring

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
    {x Q : ℝ} (hx : 2 ≤ x) (hQ : 1 ≤ Q) :
    open Classical in
    summatory (fun q ↦ ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive, q * (q.totient : ℝ)⁻¹ * ⨆ y ∈ Set.Icc 1 x, ‖summatory (fun n ↦ (f * g) n * χ n) y‖) Q
      ≤ (√(N * M) + √M * Q + √N * Q + Q^2) * Real.log x * √(∑ n ∈ Finset.Icc 1 M, (f n)^2) * √(∑ n ∈ Finset.Icc 1 N, (g n)^2) := by
  sorry


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
