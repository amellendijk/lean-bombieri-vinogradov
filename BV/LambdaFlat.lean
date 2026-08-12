import Mathlib
import Architect
import BV.Delta
import BV.Axioms
import BV.LambdaSharp
import BV.LambdaLE
import BV.Flat.Perron

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
    ∑ d ∈ Finset.Ioc ⌊(Real.log x)^C⌋₊ ⌊Q/r⌋₊, (d.totient : ℝ)⁻¹ *
      ∑ ξ : DirichletCharacter ℂ d with ξ.IsPrimitive,
        maxyReal (fun y ↦ ENNReal.ofReal (S r y ξ))

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
    exact (changeLevel hm ξ).conductor_dvd_of_mem_conductorSet hfac
  refine Nat.dvd_antisymm h1 ?_
  set c := (changeLevel hm ξ).conductor with hc
  have hcn : c ∣ n := dvd_trans h1 ξ.conductor_dvd_level
  obtain ⟨hcm, ξ', hξ'⟩ := factorsThrough_conductor (changeLevel hm ξ)
  have hξeq : ξ = changeLevel hcn ξ' := by
    apply changeLevel_injective hm
    rw [← changeLevel_trans]
    exact hξ'
  exact ξ.conductor_dvd_of_mem_conductorSet ⟨hcn, ξ', hξeq⟩

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
    exact fun h => hχ (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h)
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
      exact ⟨fun he => hn (h ▸ DirichletCharacter.eq_one_iff_conductor_eq_one.mp he),
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
  grind

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
    grind
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
  grind

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
      grind
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
theorem Delta_LambdaFlat_decomp [ProofData] {C : ℕ} {y : ℝ} (q : ℕ) (hqpos : 0 < q)
    (a : ZMod q) (ha : IsUnit a) :
  open Classical in
  |Δ_[Λ♭](y; q, a)| ≤ (q.totient : ℝ)⁻¹ * |∑ d ∈ q.divisors with 1 < (d : ℕ) ∧ ↑d ≤ (Real.log x)^C, ∑ p ∈ d.divisorsAntidiagonal, μ p.2 * p.1.totient * Δ_[onCoprime q Λ♭](y; p.1, a.cast)|
    + (q.totient : ℝ)⁻¹ * ∑ d ∈ q.divisors with (Real.log x)^C < (d : ℕ), ∑ ξ : DirichletCharacter ℂ d with ξ.IsPrimitive, S (q/d) y ξ := by
  classical
  haveI : NeZero q := ⟨hqpos.ne'⟩
  set L : ℝ := (Real.log x) ^ C with hL_def
  have hg : ∀ n, onCoprime q ⇑Λ♭ n ≠ 0 → q.Coprime n := by
    intro n hn
    rw [onCoprime_apply] at hn
    grind
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
      grind
    grind
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
      grind
    · apply Finset.sum_congr _ (fun _ _ => rfl)
      rw [Finset.filter_filter]
      apply Finset.filter_congr
      intro d hd
      have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
      constructor
      · grind
      · intro hlt
        refine ⟨?_, by grind⟩
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
        grind
      have : (n / d) * (n / d) ≤ d * (n / d) := by gcongr
      rwa [hq] at this
  have h3 : (n.divisors.image f).card ≤ Nat.sqrt n := by
    calc (n.divisors.image f).card ≤ (Finset.Icc 1 (Nat.sqrt n)).card :=
          Finset.card_le_card h2
      _ = Nat.sqrt n := by rw [Nat.card_Icc]; omega
  have h4 : n.divisors.card ≤ 2 * Nat.sqrt n := by omega
  calc (n.divisors.card : ℝ) ≤ ((2 * Nat.sqrt n : ℕ) : ℝ) := by exact_mod_cast h4
    _ = 2 * (Nat.sqrt n : ℝ) := by grind
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
    have hMδ : (M : ℝ) / δ = c⁻¹ := by grind
    -- Key pointwise bound: log x ≤ (M/δ) · x^c
    have key : Real.log x ≤ c⁻¹ * x ^ c := by
      have h1 : Real.log (x ^ c) = c * Real.log x := Real.log_rpow hx0 c
      have h2 : Real.log (x ^ c) ≤ x ^ c - 1 :=
        Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx0 c)
      have h3 : c * Real.log x ≤ x ^ c := by grind
      rw [inv_mul_eq_div, le_div_iff₀ hcpos, mul_comm]
      exact h3
    have hcM : c * (M : ℝ) = δ := by grind
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
    grind
  -- collapse `x^(1/4)·x^(1/2)·x^(1/4) = x`
  have hxsum : x ^ (1/4 : ℝ) * x ^ (1/2 : ℝ) * x ^ (1/4 : ℝ) = x := by
    grind
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
    grind
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
        (sum_vonMangoldt_not_coprime_ll_logq le_x (q:=q) hq0)
    grind
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
      simpa [C_D1] using PNT A' hy2
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
        (sum_vonMangoldt_not_coprime_ll_logq le_x (q:=s) hs0)
      have u1 := mul_le_mul_of_nonneg_right C_SVNC_le (mul_nonneg hlogs_nonneg hlogx_nonneg)
      have u2 : (Real.log 2)⁻¹ * (Real.log s * Real.log x)
          ≤ (Real.log 2)⁻¹ * (Real.log x * Real.log x) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hlogs_le hlogx_nonneg) hlog2
      exact le_trans hmono (le_trans hx_bound (le_trans u1 u2))
    have hyT2 : |y - T2| ≤ C_SW A' 0 * (y / Real.log y ^ A')
        + (Real.log 2)⁻¹ * (Real.log x * Real.log x) := by
      grind
    -- Assemble.
    have hT1ψ : T1 = ψ y a := by
      rw [hT1]
      exact (chebyPsi_eq_summatory y a).symm
    have e1 : T1 - c * T2 = (ψ y a - y / (s.totient : ℝ)) + c * (y - T2) := by
      grind
    rw [e1]
    refine (abs_add_le _ _).trans ?_
    have hpart2 : |c * (y - T2)|
        ≤ C_SW A' 0 * (y / Real.log y ^ A') + (Real.log 2)⁻¹ * (Real.log x * Real.log x) := by
      rw [abs_mul, abs_of_nonneg hc0]
      refine le_trans (mul_le_mul_of_nonneg_left hyT2 hc0) ?_
      exact mul_le_of_le_one_left (le_trans (abs_nonneg (y - T2)) hyT2) hcle
    grind
  rw [hfun, Delta_sub]
  grind

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
    grind
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
    grind
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
  grind

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
      grind
    calc (∑ d ∈ S, (d : ℝ)) ≤ (S.card : ℝ) * (Real.log x) ^ C := h1
      _ ≤ (Real.log x) ^ C * (Real.log x) ^ C :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = (Real.log x) ^ (2 * C) := by rw [← pow_add, ← two_mul]
  calc C_DLF A C * (x / (Real.log x) ^ (A + 2 * C + 1)) * (∑ d ∈ S, (d : ℝ))
      ≤ C_DLF A C * (x / (Real.log x) ^ (A + 2 * C + 1)) * (Real.log x) ^ (2 * C) :=
        mul_le_mul_of_nonneg_left hsumd (mul_nonneg hCDLF_nonneg hWpos.le)
    _ = C_DLF A C * x / (Real.log x) ^ (A + 1) := by
        grind

/-- `S r y ξ` is nonnegative (it is a norm). -/
theorem S_nonneg [ProofData] {q : ℕ} (r : ℕ) (y : ℝ) (ξ : DirichletCharacter ℂ q) :
    0 ≤ S r y ξ := norm_nonneg _

/-- `S r y ξ ≤ maxy (S r · ξ)` for `y ∈ [√x, x]`. -/
theorem S_le_maxy [ProofData] {q : ℕ} (r : ℕ) (ξ : DirichletCharacter ℂ q) {y : ℝ}
    (hy1 : √x ≤ y) (hy2 : y ≤ x) :
    S r y ξ ≤ maxyReal (fun y ↦ ENNReal.ofReal (S r y ξ)) := by
  refine le_maxyReal_ofReal (f := fun z ↦ S r z ξ) hy1 hy2
    (B := summatory (fun n ↦ ‖onCoprime r Λ♭ n * ξ n‖) x)
    (S_nonneg r y ξ) (fun z hz1 hz2 ↦ ?_)
  simp only [S]
  rw [summatory]
  refine (norm_sum_le _ _).trans ?_
  rw [summatory]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    rw [Finset.mem_Ioc] at hn ⊢
    exact ⟨hn.1, hn.2.trans (Nat.floor_mono hz2)⟩
  · exact fun i _ _ ↦ norm_nonneg _

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
      grind
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
          grind
      _ = 2 := by norm_num
  -- the totient as a product over prime factors
  have hφ : d.totient = ∏ p ∈ S, (p ^ (d.factorization p)).totient := by
    rw [Nat.totient_eq_prod_factorization hd0]
    refine Finset.prod_congr rfl (fun p hp ↦ ?_)
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by rwa [hS, Nat.support_factorization] at hp)
    have hk : 1 ≤ d.factorization p := by grind
    rw [Nat.totient_prime_pow hpp hk]
  calc d = ∏ p ∈ S, p ^ (d.factorization p) := (Nat.factorization_prod_pow_eq_self hd0).symm
    _ ≤ ∏ p ∈ S, (if p = 2 then 2 else 1) * ((p ^ (d.factorization p)).totient) ^ 2 := by
        refine Finset.prod_le_prod' (fun p hp ↦ ?_)
        have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by rwa [hS, Nat.support_factorization] at hp)
        have hk : 1 ≤ d.factorization p := by grind
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
    grind
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
    grind
  rw [← Finset.sum_subset hsub (fun x _ hx => by
        grind),
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
  grind

/-- **Step 6 (TODO).** Partial harmonic-sum bound `∑_{e ≤ t} 1/e ≤ 1 + log t` for `t ≥ 1`,
via `summatory (⇑invAF) t = (harmonic ⌊t⌋ : ℝ)` and `harmonic_le_one_add_log`. -/
theorem summatory_invAF_le {t : ℝ} (ht : 1 ≤ t) :
    summatory (⇑invAF) t ≤ 1 + Real.log t := by
  have h0 : (0 : ℝ) ≤ t := by linarith
  have heq : summatory (⇑invAF) t = (harmonic ⌊t⌋₊ : ℝ) := by
    rw [summatory, show Finset.Ioc 0 ⌊t⌋₊ = Finset.Icc 1 ⌊t⌋₊ from rfl,
      harmonic_eq_sum_Icc]
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
        rw [Finset.mem_Ioc] at hd
        have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd.1
        have hdpos : (0 : ℝ) < d := by linarith
        have hQ0 : 0 ≤ Q := by
          by_contra hQneg
          have hfloor : ⌊Q⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
          omega
        have hdQ : (d : ℝ) ≤ Q := by
          calc (d : ℝ) ≤ (⌊Q⌋₊ : ℕ) := by exact_mod_cast hd.2
            _ ≤ Q := Nat.floor_le (by linarith [hd1])
        refine mul_le_mul_of_nonneg_left ?_ (fAF_nonneg d)
        have hQd1 : 1 ≤ Q / d := by
          rw [le_div_iff₀ hdpos]
          linarith
        have hQdx : Q / d ≤ x := by
          calc Q / d ≤ Q := by rw [div_le_iff₀ hdpos]; nlinarith [hd1, hdQ]
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
theorem maxya_Delta_LambdaFlat_enorm_le [ProofData] (A C : ℕ) {q : ℕ}
    (hq1 : 1 ≤ q) (hqx : (q : ℝ) ≤ √x) :
  open Classical in
    maxya q (fun y a ↦ ‖Δ_[Λ♭](y; q, a)‖ₑ)
      ≤ ENNReal.ofReal ((q.totient : ℝ)⁻¹ * (C_DLF A C * x / (Real.log x) ^ (A + 1))
        + (q.totient : ℝ)⁻¹ * ∑ d ∈ q.divisors with (Real.log x) ^ C < (d : ℕ),
            ∑ ξ : DirichletCharacter ℂ d with ξ.IsPrimitive,
              maxyReal (fun y ↦ ENNReal.ofReal (S (q / d) y ξ))) := by
  classical
  have hq0 : 0 < q := hq1
  have hφ : (0 : ℝ) ≤ (q.totient : ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
  apply maxya_Delta_enorm_le_of_abs_le
  intro y hy1 hy2 a ha
  refine (Delta_LambdaFlat_decomp (C := C) (y := y) q hq0 a ha).trans (add_le_add ?_ ?_)
  · exact mul_le_mul_of_nonneg_left
      (Delta_LambdaFlat_small_conductor A C hy1 hy2 q hq0 hqx a ha) hφ
  · refine mul_le_mul_of_nonneg_left ?_ hφ
    exact Finset.sum_le_sum (fun d _ ↦ Finset.sum_le_sum (fun ξ _ ↦ S_le_maxy _ ξ hy1 hy2))

/-- The summand of the regrouped main term: `1/(φ(d)φ(r)) · ∑*_{ξ mod d} maxₓ S_r(·, ξ)`. -/
noncomputable def gLFT [ProofData] (d r : ℕ) : ℝ :=
  open Classical in
  (d.totient : ℝ)⁻¹ * (r.totient : ℝ)⁻¹ *
    ∑ ξ : DirichletCharacter ℂ d with ξ.IsPrimitive,
      maxyReal (fun y ↦ ENNReal.ofReal (S r y ξ))

theorem gLFT_nonneg [ProofData] (d r : ℕ) : 0 ≤ gLFT d r := by
  classical
  rw [gLFT]
  refine mul_nonneg (mul_nonneg (by positivity) (by positivity)) ?_
  exact Finset.sum_nonneg (fun ξ _ ↦ ENNReal.toReal_nonneg)

@[blueprint (statement := /--
$$\sum_{q \le Q} \max_{\substack{\sqrt{x} \le y \le x \\ a \in (\Z/q\Z)^*}} \left|\Delta_{\Lambda^\flat}(y;\,q,\,a)\right| \le \sum_{r \le Q} \frac{T_r(x,Q)}{\varphi(r)} + O\!\left(\frac{x}{(\log x)^A}\right)$$
-/) (proof := /--
Sum the error from \ref{Delta_LambdaFlat_small_conductor} over $q \le Q$ using
$\sum_{n \le x} 1/\varphi(n) \ll \log x$, then regroup the main sum by $r = q/d$.
-/) (uses := [Delta_LambdaFlat_decomp, Delta_LambdaFlat_small_conductor, character_sum_Mobius, T])]
theorem BV_LambdaFlat_via_T [ProofData] (Q : ℝ) (A C : ℕ) (hQ : Q ≤ √x) :
    (∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊, maxya q fun y a ↦ ‖Δ_[Λ♭](y; q, a)‖ₑ)
      ≤ ENNReal.ofReal ((∑ r ∈ Finset.Ioc 0 ⌊Q⌋₊, (r.totient : ℝ)⁻¹ * T C r Q)
        + C_BV_LFT A C * x / (Real.log x) ^ A) := by
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
  have hMB : (∑ r ∈ Finset.Ioc 0 ⌊Q⌋₊, (r.totient : ℝ)⁻¹ * T C r Q)
      = ∑ r ∈ Finset.Ioc 0 ⌊Q⌋₊,
          ∑ d ∈ Finset.Ioc ⌊(Real.log x) ^ C⌋₊ ⌊Q / r⌋₊, gLFT d r := by
    refine Finset.sum_congr rfl (fun r _ ↦ ?_)
    rw [T, Real.rpow_natCast, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun d _ ↦ ?_)
    rw [gLFT]; ring
  -- Per-`q` canonical bound.
  have hterm : ∀ q ∈ Finset.Ioc 0 ⌊Q⌋₊,
      maxya q (fun y a ↦ ‖Δ_[Λ♭](y; q, a)‖ₑ) ≤
        ENNReal.ofReal ((q.totient : ℝ)⁻¹ * Kc
            + (q.totient : ℝ)⁻¹ * ∑ d ∈ q.divisors with (Real.log x) ^ C < (d : ℕ),
                ∑ ξ : DirichletCharacter ℂ d with ξ.IsPrimitive,
                  maxyReal (fun y ↦ ENNReal.ofReal (S (q / d) y ξ))) := by
    intro q hq
    rw [Finset.mem_Ioc_zero_floor] at hq
    rw [hKc]
    exact maxya_Delta_LambdaFlat_enorm_le A C (by exact_mod_cast hq.1) (le_trans hq.2 hQ)
  -- Bound the error part using the (assumed) totient bound.
  have hERR : ∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊, (q.totient : ℝ)⁻¹ * Kc
      ≤ C_BV_LFT A C * x / (Real.log x) ^ A := by
    rw [← Finset.sum_mul]
    have htot : ∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊, (q.totient : ℝ)⁻¹ ≤ C_tot * Real.log x := by
      have h := summatory_totient_inv_le Q hQx
      rwa [summatory] at h
    calc (∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊, (q.totient : ℝ)⁻¹) * Kc
        ≤ (C_tot * Real.log x) * Kc := mul_le_mul_of_nonneg_right htot hKc_nonneg
      _ = C_BV_LFT A C * x / (Real.log x) ^ A := by
          rw [hKc, C_BV_LFT, pow_succ]; field_simp
  -- Bound the main part by regrouping `q = r·d`.
  have hMAIN : ∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊, (q.totient : ℝ)⁻¹ *
        ∑ d ∈ q.divisors with (Real.log x) ^ C < (d : ℕ),
          ∑ ξ : DirichletCharacter ℂ d with ξ.IsPrimitive,
            maxyReal (fun y ↦ ENNReal.ofReal (S (q / d) y ξ))
      ≤ ∑ r ∈ Finset.Ioc 0 ⌊Q⌋₊, (r.totient : ℝ)⁻¹ * T C r Q := by
    rw [hMB]
    -- Step A: distribute `1/φ(q)` and use `φ(d)φ(q/d) ≤ φ(q)` term by term.
    refine le_trans (b := ∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊,
        ∑ d ∈ q.divisors with (Real.log x) ^ C < (d : ℕ), gLFT d (q / d)) ?_ ?_
    · refine Finset.sum_le_sum (fun q hq ↦ ?_)
      rw [Finset.mem_Ioc_zero_floor] at hq
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
        (Finset.sum_nonneg (fun ξ _ ↦ ENNReal.toReal_nonneg))
    -- Step B: reindex `(q, d) ↦ (q/d, d)`.
    · rw [Finset.sum_sigma', Finset.sum_sigma']
      set LHSsig := (Finset.Ioc 0 ⌊Q⌋₊).sigma
        (fun q => q.divisors.filter (fun d => (Real.log x) ^ C < (d : ℕ))) with hLHSsig
      set RHSsig := (Finset.Ioc 0 ⌊Q⌋₊).sigma
        (fun r => Finset.Ioc ⌊(Real.log x) ^ C⌋₊ ⌊Q / r⌋₊) with hRHSsig
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
        grind
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
            rw [Finset.mem_Ioc_zero_floor] at hqmem
            have hq1 : 1 ≤ q := by exact_mod_cast hqmem.1
            have hqpos : 0 < q := hq1
            have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hqpos
            have hqdpos : 0 < q / d := Nat.div_pos (Nat.le_of_dvd hqpos hdvd) hdpos
            rw [hRHSsig, Finset.mem_sigma]
            refine ⟨?_, ?_⟩
            · rw [Finset.mem_Ioc_zero_floor]
              refine ⟨by exact_mod_cast hqdpos, ?_⟩
              calc (↑(q / d) : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.div_le_self q d
                _ ≤ Q := hqmem.2
            · rw [Finset.mem_Ioc]
              have hL0 : 0 ≤ (Real.log x) ^ C := by positivity
              have hlower : ⌊(Real.log x) ^ C⌋₊ < d :=
                (Nat.floor_lt hL0).mpr hdL
              refine ⟨hlower, ?_⟩
              change d ≤ ⌊Q / (↑(q / d) : ℝ)⌋₊
              apply (Nat.le_floor_iff
                (div_nonneg (by linarith [hqmem.2]) (by exact_mod_cast hqdpos.le))).mpr
              rw [le_div_iff₀ (by exact_mod_cast hqdpos : (0 : ℝ) < (↑(q / d) : ℝ))]
              calc (d : ℝ) * (↑(q / d) : ℝ) = ((d * (q / d) : ℕ) : ℝ) := by grind
                _ = (q : ℝ) := by exact_mod_cast Nat.mul_div_cancel' hdvd
                _ ≤ Q := hqmem.2
  let Bq (q : ℕ) : ℝ := (q.totient : ℝ)⁻¹ * Kc +
    (q.totient : ℝ)⁻¹ *
            ∑ d ∈ q.divisors with (Real.log x) ^ C < (d : ℕ),
              ∑ ξ : DirichletCharacter ℂ d with ξ.IsPrimitive,
                maxyReal (fun y ↦ ENNReal.ofReal (S (q / d) y ξ))
  have hBq : ∀ q, 0 ≤ Bq q := by
    intro q
    dsimp [Bq]
    exact add_nonneg (mul_nonneg (by positivity) hKc_nonneg)
      (mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ ↦
        Finset.sum_nonneg fun _ _ ↦ ENNReal.toReal_nonneg))
  have hreal : ∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊, Bq q ≤
      (∑ r ∈ Finset.Ioc 0 ⌊Q⌋₊, (r.totient : ℝ)⁻¹ * T C r Q)
        + C_BV_LFT A C * x / (Real.log x) ^ A := by
    dsimp [Bq]
    rw [Finset.sum_add_distrib]
    grind
  calc
    ∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊, maxya q (fun y a ↦ ‖Δ_[Λ♭](y; q, a)‖ₑ)
        ≤ ∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊, ENNReal.ofReal (Bq q) := by
          apply Finset.sum_le_sum
          grind
    _ = ENNReal.ofReal (∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊, Bq q) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun q _ ↦ hBq q)]
    _ ≤ ENNReal.ofReal ((∑ r ∈ Finset.Ioc 0 ⌊Q⌋₊,
        (r.totient : ℝ)⁻¹ * T C r Q) + C_BV_LFT A C * x / (Real.log x) ^ A) :=
      ENNReal.ofReal_le_ofReal hreal

/-! ### Large sieve estimates -/

-- TODO: Decide if we need to define the L2 norm on ArithmeticFunctions explicitly here.

/-- A concrete smooth bump function, obtained from `SmoothExistence`, used to instantiate the
`Flat.Bump` data needed by `Flat.LargeSieve_convolution_aux`. Kept as a `def` (not a global
`instance`) so it does not clash with the `Flat.Bump` provided by `ProofData` downstream. -/
noncomputable def bumpFn : Flat.Bump where
  ν := SmoothExistence.choose
  diffν := SmoothExistence.choose_spec.1
  νpos := SmoothExistence.choose_spec.2.1
  suppν := SmoothExistence.choose_spec.2.2.1
  mass_one := SmoothExistence.choose_spec.2.2.2

/-- The implied constant in `LargeSieve_convolution` (twice the Theorem 26.6 constant `C_LSC`,
the extra factor `2` absorbing `log(x+1) ≤ 2 log x` for `x ≥ 2`). -/
noncomputable def C_LargeSieve : ℝ := 2 * @Flat.C_LSC bumpFn

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
      ≤ C_LargeSieve * (√(N * M) + √M * Q + √N * Q + Q^2) * Real.log x * √(∑ n ∈ Finset.Icc 1 M, (f n)^2) * √(∑ n ∈ Finset.Icc 1 N, (g n)^2) := by
  classical
  letI : Flat.Bump := bumpFn
  unfold C_LargeSieve
  -- Zero cases: if `M = 0` then `f = 0`, if `N = 0` then `g = 0`, and both sides vanish.
  obtain rfl | hMpos := Nat.eq_zero_or_pos M
  · have hf0 : f = 0 := by
      ext n
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp
      · exact hf n h
    rw [hf0]; simp
  obtain rfl | hNpos := Nat.eq_zero_or_pos N
  · have hg0 : g = 0 := by
      ext n
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp
      · exact hg n h
    rw [hg0]; simp
  -- Complexify `f` and `g` to feed the `FG` data of `Flat.LargeSieve_convolution_aux`.
  let F : ArithmeticFunction ℂ := ⟨fun n => (f n : ℂ), by simp⟩
  let G : ArithmeticFunction ℂ := ⟨fun n => (g n : ℂ), by simp⟩
  have hFa : ∀ n, F n = (f n : ℂ) := fun _ => rfl
  have hGa : ∀ n, G n = (g n : ℂ) := fun _ => rfl
  let inst : Flat.FG := {
    f := F, g := G, M := (M : ℝ), N := (N : ℝ)
    hM_pos := by exact_mod_cast hMpos
    hN_pos := by exact_mod_cast hNpos
    hf := by intro n hn; rw [hFa, hf n (by exact_mod_cast hn)]; simp
    hg := by intro n hn; rw [hGa, hg n (by exact_mod_cast hn)]; simp }
  have hFG : ∀ n, (F * G) n = ((f * g) n : ℂ) := by
    intro n
    simp only [ArithmeticFunction.mul_apply, hFa, hGa]
    push_cast
    rfl
  have key := Flat.LargeSieve_convolution_aux (fg := inst) (show (1:ℝ) ≤ x by linarith) hQ
  have hIccM : Nat.Icc (1:ℝ) (M:ℝ) = Finset.Icc 1 M := by
    ext n; simp only [Nat.mem_Icc, Finset.mem_Icc, Nat.one_le_cast, Nat.cast_le]
  have hIccN : Nat.Icc (1:ℝ) (N:ℝ) = Finset.Icc 1 N := by
    ext n; simp only [Nat.mem_Icc, Finset.mem_Icc, Nat.one_le_cast, Nat.cast_le]
  -- The `ℓ²` norms of the complexified functions agree with those of `f`, `g`.
  have hAm : summatory (fun m => ‖F m‖ ^ 2) (M:ℝ) = ∑ n ∈ Finset.Icc 1 M, f n ^ 2 := by
    rw [summatory, show ⌊(M : ℝ)⌋₊ = M by simp,
      show Finset.Ioc 0 M = Finset.Icc 1 M from rfl]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hFa, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hAn : summatory (fun m => ‖G m‖ ^ 2) (N:ℝ) = ∑ n ∈ Finset.Icc 1 N, g n ^ 2 := by
    rw [summatory, show ⌊(N : ℝ)⌋₊ = N by simp,
      show Finset.Ioc 0 N = Finset.Icc 1 N from rfl]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hGa, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hCLSC : 0 ≤ Flat.C_LSC := by
    have hCJ : 0 ≤ Flat.C_J := by
      unfold Flat.C_J
      have hA := Flat.exists_mellin_smooth1_boundA.choose_spec.1
      have hB := Flat.exists_mellin_smooth1_boundB.choose_spec.1
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have h1 : (0:ℝ) ≤ 2 * Real.sqrt 2 * (1 + 6 * Real.log 2) * Flat.exists_mellin_smooth1_boundA.choose := by positivity
      have h2 : (0:ℝ) ≤ 2 * Flat.exists_mellin_smooth1_boundB.choose / Real.log 2 := by positivity
      linarith
    have hLS := Flat.C_LS_nonneg
    unfold Flat.C_LSC
    exact mul_nonneg (mul_nonneg (by positivity) hLS) hCJ
  -- `log(x+1) ≤ 2 log x` for `x ≥ 2`, since `x + 1 ≤ x²`.
  have hlog : Real.log (x + 1) ≤ 2 * Real.log x := by
    have : x + 1 ≤ x ^ 2 := by nlinarith
    calc Real.log (x + 1) ≤ Real.log (x ^ 2) := Real.log_le_log (by linarith) this
      _ = 2 * Real.log x := by rw [Real.log_pow]; grind
  simp_rw [← hFG]
  refine le_trans key ?_
  change Flat.C_LSC * (√((N:ℝ) * (M:ℝ)) + √(M:ℝ) * Q + √(N:ℝ) * Q + Q ^ 2)
      * √(summatory (fun m => ‖F m‖ ^ 2) (M:ℝ)) * √(summatory (fun m => ‖G m‖ ^ 2) (N:ℝ))
      * Real.log (x + 1) ≤ _
  rw [hAm, hAn]
  have hS : (0:ℝ) ≤ √((N:ℝ) * (M:ℝ)) + √(M:ℝ) * Q + √(N:ℝ) * Q + Q ^ 2 := by positivity
  calc Flat.C_LSC * (√((N:ℝ) * (M:ℝ)) + √(M:ℝ) * Q + √(N:ℝ) * Q + Q ^ 2)
        * √(∑ n ∈ Finset.Icc 1 M, f n ^ 2) * √(∑ n ∈ Finset.Icc 1 N, g n ^ 2) * Real.log (x + 1)
      ≤ Flat.C_LSC * (√((N:ℝ) * (M:ℝ)) + √(M:ℝ) * Q + √(N:ℝ) * Q + Q ^ 2)
        * √(∑ n ∈ Finset.Icc 1 M, f n ^ 2) * √(∑ n ∈ Finset.Icc 1 N, g n ^ 2) * (2 * Real.log x) := by
        apply mul_le_mul_of_nonneg_left hlog
        positivity
    _ = 2 * Flat.C_LSC * (√((N:ℝ) * (M:ℝ)) + √(M:ℝ) * Q + √(N:ℝ) * Q + Q ^ 2) * Real.log x
        * √(∑ n ∈ Finset.Icc 1 M, f n ^ 2) * √(∑ n ∈ Finset.Icc 1 N, g n ^ 2) := by ring


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
  · grind


/-- `((Λ - Λ≤U) * ζ) d = 0` whenever `d ≤ U`: every divisor `m ∣ d` satisfies `m ≤ d ≤ U`,
so `(Λ - Λ≤U) m = Λ m - Λ m = 0`. -/
private theorem AFlat_eq_zero_of_le_U [ProofData] {d : ℕ} (hd : (d : ℝ) ≤ U) :
    ((Λ - Λ≤U) * ζ) d = 0 := by
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  apply Finset.sum_eq_zero
  intro m hm
  have hmd : m ≤ d :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hm).2) (Nat.dvd_of_mem_divisors hm)
  have hmU : (m : ℝ) ≤ U := le_trans (by exact_mod_cast hmd) hd
  show Λ m - Λ≤U m = 0
  rw [LambdaLEU_apply_of_le hmU, sub_self]

/-- `(μ - μ≤V) e = 0` whenever `e ≤ V`: then `μ≤V e = μ e`. -/
private theorem BFlat_eq_zero_of_le_V [ProofData] {e : ℕ} (he : (e : ℝ) ≤ V) :
    (μ - μ≤V) e = 0 := by
  show μ e - μ≤V e = 0
  rcases Nat.eq_zero_or_pos e with rfl | hepos
  · simp
  · have hmem : e ∈ Set.Icc 1 (Nat.floor V) := Set.mem_Icc.mpr ⟨hepos, Nat.le_floor he⟩
    have hval : μ≤V e = μ e := by
      simp only [moebiusLEV]; exact ArithmeticFunction.on_apply_of_mem _ _ _ hmem
    rw [hval, sub_self]

/-- `(μ - μ≤V) e = μ e` whenever `V < e`: then `μ≤V e = 0`. -/
private theorem BFlat_eq_of_gt_V [ProofData] {e : ℕ} (he : V < (e : ℝ)) :
    (μ - μ≤V) e = μ e := by
  show μ e - μ≤V e = μ e
  have hVe : Nat.floor V < e := (Nat.floor_lt V_nonneg).mpr he
  have hnotmem : e ∉ Set.Icc 1 (Nat.floor V) :=
    fun hm => absurd (Set.mem_Icc.mp hm).2 (not_le.mpr hVe)
  have hval : μ≤V e = 0 := by
    simp only [moebiusLEV]; exact ArithmeticFunction.on_apply_of_not_mem _ _ _ hnotmem
  rw [hval, sub_zero]

@[blueprint (latexEnv := "lemma") (statement := /--
$$\Lambda^\flat(n) = \sum_{U < 2^j \le 2x/V} (f_j * g_j)(n) \quad \text{for } n \le x,$$
where $f_j(k) = (\Lambda_{>U} * 1)(k)\,1_{2^{j-1} < k \le 2^j}$ and $g_j(\ell) = \mu(\ell)\,1_{V < \ell \le x/2^{j-1}}$.
-/)]
theorem LambdaFlat_dyadic [ProofData] (n : ℕ) (hn : n ≤ x) :
    Λ♭ n = ∑ j ∈ pows2Ioc U (2*x/V), (f j * g j) n := by
  classical
  have hxpos : (0:ℝ) < x := by linarith [le_x]
  -- Expand the outer Dirichlet convolution on the left.
  rw [show Λ♭ n = ((Λ - Λ≤U) * ζ * (μ - μ≤V)) n from rfl, ArithmeticFunction.mul_apply]
  -- Expand each convolution on the right and swap the order of summation.
  have hexp : ∀ j, (f j * g j) n
      = ∑ p ∈ n.divisorsAntidiagonal, f j p.1 * g j p.2 := fun j => ArithmeticFunction.mul_apply
  rw [Finset.sum_congr rfl (fun j _ => hexp j), Finset.sum_comm]
  -- Reduce to a per-divisor identity.
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [Nat.mem_divisorsAntidiagonal] at hp
  obtain ⟨hde, hn0⟩ := hp
  set d := p.1 with hd_def
  set e := p.2 with he_def
  have hepos : 0 < e := Nat.pos_of_ne_zero (right_ne_zero_of_mul (hde.symm ▸ hn0))
  -- Pointwise values of `f j` and `g j` as `if`-expressions.
  have hfval : ∀ j, f j d
      = if d ∈ Set.Ioc (2^(j-1)) (2^j) then ((Λ - Λ≤U) * ζ) d else 0 := by
    intro j
    by_cases hm : d ∈ Set.Ioc (2^(j-1)) (2^j)
    · rw [show f j d = (((Λ - Λ≤U) * ζ).on (Set.Ioc (2^(j-1)) (2^j))) d from rfl,
        ArithmeticFunction.on_apply_of_mem _ _ _ hm, if_pos hm]
    · rw [show f j d = (((Λ - Λ≤U) * ζ).on (Set.Ioc (2^(j-1)) (2^j))) d from rfl,
        ArithmeticFunction.on_apply_of_not_mem _ _ _ hm, if_neg hm]
  have hgval : ∀ j, g j e
      = if (e : ℝ) ∈ Set.Ioc V (x / (2:ℝ)^(j-1)) then (μ e : ℝ) else 0 := by
    intro j
    simp only [g]
    by_cases hm : (e : ℝ) ∈ Set.Ioc V (x / (2:ℝ)^(j-1))
    · have hmem : e ∈ Nat.cast ⁻¹' (Set.Ioc V (x / (2:ℝ)^(j-1))) := hm
      rw [ArithmeticFunction.on_apply_of_mem _ _ _ hmem, if_pos hm,
        ArithmeticFunction.intCoe_apply]
    · have hmem : e ∉ Nat.cast ⁻¹' (Set.Ioc V (x / (2:ℝ)^(j-1))) := hm
      rw [ArithmeticFunction.on_apply_of_not_mem _ _ _ hmem, if_neg hm]
  by_cases hd : U < (d : ℝ)
  · by_cases he : V < (e : ℝ)
    · -- Main case: `d > U` and `e > V`.  Exactly one `j` contributes.
      have hd2 : 1 < d := by
        have : (1:ℝ) < d := lt_of_le_of_lt one_le_U hd
        exact_mod_cast this
      set j₀ := Nat.clog 2 d with hj0def
      have hj0pos : 0 < j₀ := Nat.clog_pos (by norm_num) hd2
      have hupper : d ≤ 2 ^ j₀ := Nat.le_pow_clog (by norm_num) d
      have hlower : 2 ^ (j₀ - 1) < d :=
        (Nat.lt_clog_iff_pow_lt (by norm_num)).mp (by omega)
      have hd_le : (d : ℝ) ≤ (2:ℝ) ^ j₀ := by exact_mod_cast hupper
      have hlow_real : (2:ℝ) ^ (j₀ - 1) < (d : ℝ) := by exact_mod_cast hlower
      have hpow : (2:ℝ) ^ j₀ = 2 * (2:ℝ) ^ (j₀ - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel hj0pos]
      have hde_real : (d : ℝ) * e ≤ x := by rw [← Nat.cast_mul, hde]; exact hn
      have he_real_pos : (0:ℝ) < (e : ℝ) := by exact_mod_cast hepos
      have hd_lt : (d : ℝ) < x / V := by
        have h1 : (d : ℝ) ≤ x / e := (le_div_iff₀ he_real_pos).mpr hde_real
        have h2 : x / (e : ℝ) < x / V := div_lt_div_of_pos_left hxpos V_pos he
        exact lt_of_le_of_lt h1 h2
      have hpowpos : (0:ℝ) < (2:ℝ) ^ (j₀ - 1) := by positivity
      have hQ2 : (e : ℝ) ≤ x / (2:ℝ) ^ (j₀ - 1) := by
        rw [le_div_iff₀ hpowpos]
        nlinarith [mul_lt_mul_of_pos_left hlow_real he_real_pos, hde_real]
      have hP : d ∈ Set.Ioc (2 ^ (j₀ - 1)) (2 ^ j₀) := Set.mem_Ioc.mpr ⟨hlower, hupper⟩
      have hQ : (e : ℝ) ∈ Set.Ioc V (x / (2:ℝ) ^ (j₀ - 1)) := Set.mem_Ioc.mpr ⟨he, hQ2⟩
      have hj0mem : j₀ ∈ pows2Ioc U (2 * x / V) := by
        rw [mem_pows2Ioc U (2 * x / V) one_le_U]
        grind
      -- Uniqueness of the dyadic index.
      have huniq : ∀ j, (2 ^ (j - 1) < d ∧ d ≤ 2 ^ j) → j = j₀ := by
        rintro j ⟨hj1, hj2⟩
        have e1 : (2:ℕ) ^ (j₀ - 1) < 2 ^ j := lt_of_lt_of_le hlower hj2
        have e2 : (2:ℕ) ^ (j - 1) < 2 ^ j₀ := lt_of_lt_of_le hj1 hupper
        have l1 : j₀ - 1 < j := (Nat.pow_lt_pow_iff_right (by norm_num)).mp e1
        have l2 : j - 1 < j₀ := (Nat.pow_lt_pow_iff_right (by norm_num)).mp e2
        omega
      have hzero : ∀ b ∈ pows2Ioc U (2 * x / V), b ≠ j₀ → f b d * g b e = 0 := by
        grind
      rw [BFlat_eq_of_gt_V he, Finset.sum_eq_single_of_mem j₀ hj0mem hzero,
        hfval j₀, hgval j₀, if_pos hP, if_pos hQ]
    · -- `e ≤ V`: the left side vanishes and so does every right-hand term.
      push_neg at he
      rw [BFlat_eq_zero_of_le_V he, mul_zero]
      symm
      refine Finset.sum_eq_zero (fun j _ => ?_)
      grind
  · -- `d ≤ U`: the left side vanishes and so does every right-hand term.
    push_neg at hd
    rw [AFlat_eq_zero_of_le_U hd, zero_mul]
    symm
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [hfval j, AFlat_eq_zero_of_le_U hd, ite_self, zero_mul]

/-- `C_LargeSieve` is nonnegative. (Same computation as inside `LargeSieve_convolution`.) -/
theorem C_LargeSieve_nonneg : 0 ≤ C_LargeSieve := by
  letI : Flat.Bump := bumpFn
  have hCLSC : 0 ≤ @Flat.C_LSC bumpFn := by
    have hCJ : 0 ≤ Flat.C_J := by
      unfold Flat.C_J
      have hA := Flat.exists_mellin_smooth1_boundA.choose_spec.1
      have hB := Flat.exists_mellin_smooth1_boundB.choose_spec.1
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have h1 : (0:ℝ) ≤ 2 * Real.sqrt 2 * (1 + 6 * Real.log 2) * Flat.exists_mellin_smooth1_boundA.choose := by positivity
      have h2 : (0:ℝ) ≤ 2 * Flat.exists_mellin_smooth1_boundB.choose / Real.log 2 := by positivity
      linarith
    have hLS := Flat.C_LS_nonneg
    unfold Flat.C_LSC
    exact mul_nonneg (mul_nonneg (by positivity) hLS) hCJ
  rw [C_LargeSieve]
  grind

/-- The Type-II coefficient `((Λ - Λ≤U) * ζ) n` lies in `[0, log n]`. -/
private theorem aflat_bounds [ProofData] (n : ℕ) :
    0 ≤ ((Λ - Λ≤U) * ζ) n ∧ ((Λ - Λ≤U) * ζ) n ≤ Real.log n := by
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  constructor
  · refine Finset.sum_nonneg fun d _ => ?_
    simp only [sub_eq_add_neg, ArithmeticFunction.add_apply, ArithmeticFunction.neg_apply]
    have hle : Λ≤U d ≤ Λ d := by
      by_cases h : (d : ℝ) ≤ U
      · rw [LambdaLEU_apply_of_le h]
      · rw [LambdaLEU_apply_of_gt (not_le.mp h)]; exact ArithmeticFunction.vonMangoldt_nonneg
    linarith
  · rw [← ArithmeticFunction.vonMangoldt_sum (n := n)]
    refine Finset.sum_le_sum fun d _ => ?_
    simp only [sub_eq_add_neg, ArithmeticFunction.add_apply, ArithmeticFunction.neg_apply]
    have : (0:ℝ) ≤ Λ≤U d := LambdaLEU_nonneg
    linarith

/-- `(f j).on {coprime to r}` is supported on `[1, 2^j]`. -/
private theorem f_on_coprime_supp [ProofData] (r j : ℕ) {n : ℕ} (hn : 2 ^ j < n) :
    (f j).on {m | r.Coprime m} n = 0 := by
  by_cases hm : n ∈ {m | r.Coprime m}
  · rw [on_apply_of_mem _ _ _ hm]
    show ((Λ - Λ≤U) * ζ).on (Set.Ioc (2 ^ (j - 1)) (2 ^ j)) n = 0
    exact on_apply_of_not_mem _ _ _ (fun hmem => absurd hmem.2 (not_le.mpr hn))
  · exact on_apply_of_not_mem _ _ _ hm

/-- `(g j).on {coprime to r}` is supported on `[1, ⌊x/2^{j-1}⌋]`. -/
private theorem g_on_coprime_supp [ProofData] (r j : ℕ) {n : ℕ}
    (hn : ⌊x / 2 ^ (j - 1)⌋₊ < n) : (g j).on {m | r.Coprime m} n = 0 := by
  by_cases hm : n ∈ {m | r.Coprime m}
  · rw [on_apply_of_mem _ _ _ hm]
    unfold g
    apply on_apply_of_not_mem
    intro hmem
    have h1 : (n : ℝ) ≤ x / 2 ^ (j - 1) := (Set.mem_preimage.mp hmem).2
    have h2 : x / 2 ^ (j - 1) < n := (Nat.floor_lt (div_nonneg x_nonneg (by positivity))).mp hn
    linarith
  · exact on_apply_of_not_mem _ _ _ hm

/-- `ℓ²` bound for the Type-II factor: `∑_{n ≤ 2^j} (f_j)^2 ≤ 2^j (2 log x)^2`. -/
private theorem f_on_coprime_l2 [ProofData] (r j : ℕ) (hj2 : (2 : ℝ) ^ j ≤ 2 * x / V) :
    ∑ n ∈ Finset.Icc 1 (2 ^ j), ((f j).on {m | r.Coprime m} n) ^ 2
      ≤ (2 : ℝ) ^ j * (2 * Real.log x) ^ 2 := by
  have hcard : (Finset.Icc 1 (2 ^ j)).card = 2 ^ j := by rw [Nat.card_Icc, Nat.add_sub_cancel]
  have h2jx : (2 : ℝ) ^ j ≤ x ^ 2 := by
    have hVx : 2 * x / V ≤ x ^ 2 := by
      rw [div_le_iff₀ V_pos]
      nlinarith [le_x, one_le_V, x_nonneg, V_pos]
    linarith
  calc ∑ n ∈ Finset.Icc 1 (2 ^ j), ((f j).on {m | r.Coprime m} n) ^ 2
      ≤ ∑ _n ∈ Finset.Icc 1 (2 ^ j), (2 * Real.log x) ^ 2 := by
        refine Finset.sum_le_sum fun n hn => ?_
        rw [Finset.mem_Icc] at hn
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
        have habs : |(f j).on {m | r.Coprime m} n| ≤ Real.log n := by
          refine le_trans (abs_on_le _ _ _) ?_
          show |((Λ - Λ≤U) * ζ).on (Set.Ioc (2 ^ (j - 1)) (2 ^ j)) n| ≤ Real.log n
          refine le_trans (abs_on_le _ _ _) ?_
          rw [abs_of_nonneg (aflat_bounds n).1]
          exact (aflat_bounds n).2
        have hlogn : Real.log n ≤ 2 * Real.log x := by
          have hnx2 : (n : ℝ) ≤ x ^ 2 := by
            calc (n : ℝ) ≤ (2 : ℝ) ^ j := by exact_mod_cast hn.2
              _ ≤ x ^ 2 := h2jx
          calc Real.log n ≤ Real.log (x ^ 2) := Real.log_le_log (by linarith) hnx2
            _ = 2 * Real.log x := by rw [Real.log_pow]; grind
        have hb : |(f j).on {m | r.Coprime m} n| ≤ 2 * Real.log x := le_trans habs hlogn
        calc ((f j).on {m | r.Coprime m} n) ^ 2 = |(f j).on {m | r.Coprime m} n| ^ 2 := (sq_abs _).symm
          _ ≤ (2 * Real.log x) ^ 2 := by
              apply pow_le_pow_left₀ (abs_nonneg _) hb
    _ = (2 : ℝ) ^ j * (2 * Real.log x) ^ 2 := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul]; grind

/-- `ℓ²` bound for the Möbius factor: `∑_{n ≤ N} (g_j)^2 ≤ N`. -/
private theorem g_on_coprime_l2 [ProofData] (r j : ℕ) :
    ∑ n ∈ Finset.Icc 1 ⌊x / 2 ^ (j - 1)⌋₊, ((g j).on {m | r.Coprime m} n) ^ 2
      ≤ (⌊x / 2 ^ (j - 1)⌋₊ : ℝ) := by
  have hcard : (Finset.Icc 1 ⌊x / 2 ^ (j - 1)⌋₊).card = ⌊x / 2 ^ (j - 1)⌋₊ := by
    rw [Nat.card_Icc, Nat.add_sub_cancel]
  calc ∑ n ∈ Finset.Icc 1 ⌊x / 2 ^ (j - 1)⌋₊, ((g j).on {m | r.Coprime m} n) ^ 2
      ≤ ∑ _n ∈ Finset.Icc 1 ⌊x / 2 ^ (j - 1)⌋₊, (1 : ℝ) := by
        refine Finset.sum_le_sum fun n _ => ?_
        have h1 : |(g j).on {m | r.Coprime m} n| ≤ 1 := by
          refine le_trans (abs_on_le _ _ _) ?_
          unfold g
          refine le_trans (abs_on_le _ _ _) ?_
          rw [ArithmeticFunction.intCoe_apply, ← Int.cast_abs]
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        calc ((g j).on {m | r.Coprime m} n) ^ 2 = |(g j).on {m | r.Coprime m} n| ^ 2 := (sq_abs _).symm
          _ ≤ (1 : ℝ) ^ 2 := by apply pow_le_pow_left₀ (abs_nonneg _) h1
          _ = 1 := one_pow 2
    _ = (⌊x / 2 ^ (j - 1)⌋₊ : ℝ) := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul, mul_one]

/-- The number of dyadic intervals is `≤ 3 log x`. -/
private theorem card_pows2Ioc_le [ProofData] :
    ((pows2Ioc U (2 * x / V)).card : ℝ) ≤ 3 * Real.log x := by
  have hlogx : 0 ≤ Real.log x := le_of_lt log_x_pos
  rw [pows2Ioc]
  split_ifs with hc
  · rw [Nat.card_Ioc]
    have hxV_pos : 0 < 2 * x / V := div_pos (mul_pos two_pos x_pos) V_pos
    have hb_nonneg : 0 ≤ Real.logb 2 (2 * x / V) := Real.logb_nonneg (by norm_num) hc.1
    calc ((⌊Real.logb 2 (2 * x / V)⌋₊ - ⌊Real.logb 2 U⌋₊ : ℕ) : ℝ)
        ≤ (⌊Real.logb 2 (2 * x / V)⌋₊ : ℝ) := by exact_mod_cast Nat.sub_le _ _
      _ ≤ Real.logb 2 (2 * x / V) := Nat.floor_le hb_nonneg
      _ ≤ Real.logb 2 (2 * x) := by
          apply Real.logb_le_logb_of_le (by norm_num) hxV_pos
          rw [div_le_iff₀ V_pos]; nlinarith [x_nonneg, one_le_V]
      _ ≤ 3 * Real.log x := by
          rw [Real.logb, Real.log_mul (by norm_num) (ne_of_gt x_pos)]
          have hlog2 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
          have hlog2x : Real.log 2 ≤ Real.log x :=
            Real.log_le_log (by norm_num) (by linarith [le_x])
          rw [div_le_iff₀ (by linarith)]
          nlinarith [hlogx, hlog2, hlog2x]
  · simp only [Finset.card_empty, Nat.cast_zero]; positivity

noncomputable def C_BV_char_sum : ℝ := 12 * C_LargeSieve

/-- The dyadic decomposition of `Λ♭`, restricted to integers coprime to `r`. -/
private theorem onCoprime_LambdaFlat_dyadic [ProofData] (r n : ℕ) (hn : (n : ℝ) ≤ x) :
    onCoprime r (Λ♭ : ℕ → ℝ) n
      = ∑ j ∈ pows2Ioc U (2 * x / V),
          ((f j).on {m | r.Coprime m} * (g j).on {m | r.Coprime m}) n := by
  have hsat : ∀ a b, a * b ∈ {m | r.Coprime m} ↔ a ∈ {m | r.Coprime m} ∧ b ∈ {m | r.Coprime m} :=
    fun a b => Nat.coprime_mul_iff_right
  by_cases h : r.Coprime n
  · rw [onCoprime_apply, if_pos h, LambdaFlat_dyadic n hn]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← ArithmeticFunction.on_mul_of_saturated _ hsat, on_apply_of_mem _ _ _]
    -- ??
    grind
  · rw [onCoprime_apply, if_neg h]
    refine (Finset.sum_eq_zero fun j _ => ?_).symm
    rw [← ArithmeticFunction.on_mul_of_saturated _ hsat, on_apply_of_not_mem _ _ _]
    simp [h]

/-- The per-dyadic-piece supremum over `[1, x]` appearing in the large sieve. -/
private noncomputable def Gterm [ProofData] (r j : ℕ) {q : ℕ} (ξ : DirichletCharacter ℂ q) : ℝ :=
  ⨆ y ∈ Set.Icc (1 : ℝ) x,
    ‖summatory (fun n ↦ ((f j).on {m | r.Coprime m} * (g j).on {m | r.Coprime m}) n * ξ n) y‖

private theorem Gterm_nonneg [ProofData] (r j : ℕ) {q : ℕ} (ξ : DirichletCharacter ℂ q) :
    0 ≤ Gterm r j ξ :=
  Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => norm_nonneg _

/-- A norm of a partial sum is bounded by the supremum of all such norms over `[1, x]`. -/
private theorem norm_summatory_le_Gterm [ProofData] (r j : ℕ) {q : ℕ}
    (ξ : DirichletCharacter ℂ q) {y : ℝ} (hy1 : 1 ≤ y) (hy2 : y ≤ x) :
    ‖summatory (fun n ↦ ((f j).on {m | r.Coprime m} * (g j).on {m | r.Coprime m}) n * ξ n) y‖
      ≤ Gterm r j ξ := by
  set g₀ := fun n ↦ ((f j).on {m | r.Coprime m} * (g j).on {m | r.Coprime m}) n * ξ n with hg₀
  have hB : ∀ z, 1 ≤ z → z ≤ x → ‖summatory g₀ z‖ ≤ summatory (fun n ↦ ‖g₀ n‖) x := by
    intro z _ hz2
    rw [summatory]
    refine (norm_sum_le _ _).trans ?_
    rw [summatory]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      rw [Finset.mem_Ioc] at hn ⊢
      exact ⟨hn.1, hn.2.trans (Nat.floor_mono hz2)⟩
    · exact fun i _ _ ↦ norm_nonneg _
  have hbdd : BddAbove (Set.range fun z => ⨆ (_ : z ∈ Set.Icc (1:ℝ) x), ‖summatory g₀ z‖) := by
    refine ⟨summatory (fun n ↦ ‖g₀ n‖) x, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact Real.iSup_le (fun hz => hB z hz.1 hz.2)
      (summatory_nonneg _ _ (fun n _ ↦ norm_nonneg _))
  refine le_ciSup_of_le hbdd y (le_of_eq ?_)
  have hmem : y ∈ Set.Icc (1:ℝ) x := Set.mem_Icc.mpr ⟨hy1, hy2⟩
  simp [hmem, g₀]


/-- The maximum of `S_r` over `y ∈ [√x, x]` is bounded by the sum of the dyadic suprema. -/
private theorem maxy_S_le_sum [ProofData] (r : ℕ) {q : ℕ} (ξ : DirichletCharacter ℂ q) :
    maxyReal (fun y ↦ ENNReal.ofReal (S r y ξ)) ≤
      ∑ j ∈ pows2Ioc U (2 * x / V), Gterm r j ξ := by
  refine maxyReal_ofReal_le (Finset.sum_nonneg fun j _ => Gterm_nonneg r j ξ) ?_
  intro y hy1 hy2
  have hx1 : (1 : ℝ) ≤ x := by linarith [le_x]
  have hsqrt1 : (1 : ℝ) ≤ √x := by
    rw [show (1:ℝ) = √1 from (Real.sqrt_one).symm]; exact Real.sqrt_le_sqrt hx1
  have hy1' : (1 : ℝ) ≤ y := le_trans hsqrt1 hy1
  have hStep : S r y ξ
      = ‖∑ j ∈ pows2Ioc U (2 * x / V),
          summatory (fun n ↦ ((f j).on {m | r.Coprime m} * (g j).on {m | r.Coprime m}) n * ξ n) y‖ := by
    rw [S]
    congr 1
    rw [← Finset.summatory_sum_comm]
    refine summatory_congr_fun fun n _ hnx => ?_
    rw [onCoprime_LambdaFlat_dyadic r n (le_trans hnx hy2)]
    push_cast
    rw [Finset.sum_mul]
  rw [hStep]
  refine le_trans (norm_sum_le _ _) ?_
  exact Finset.sum_le_sum fun j _ => norm_summatory_le_Gterm r j ξ hy1' hy2

/-- The character-sum bound for a single dyadic piece `j`, obtained by applying the large sieve
convolution bound `LargeSieve_convolution` and the `ℓ²` estimates. The bound is `j`-independent. -/
private theorem summatory_Gterm_le [ProofData] (r j : ℕ) (Q : ℝ) (hQ : 2 ≤ Q)
    (hj : j ∈ pows2Ioc U (2 * x / V)) :
    open Classical in
    summatory (fun q ↦ ∑ ξ : DirichletCharacter ℂ q with ξ.IsPrimitive,
        (q : ℝ) * (q.totient : ℝ)⁻¹ * Gterm r j ξ) Q
      ≤ C_LargeSieve * 4 * (Real.log x) ^ 2 *
          (x + Q * x / √U + Q * x / √V + Q ^ 2 * √x) := by
  classical
  have hQ1 : (1 : ℝ) ≤ Q := by linarith
  have hQ0 : (0 : ℝ) ≤ Q := by linarith
  have hLpos : 0 < Real.log x := log_x_pos
  have hL0 : (0 : ℝ) ≤ Real.log x := le_of_lt hLpos
  have hx0 : (0 : ℝ) ≤ x := x_nonneg
  have h2x0 : (0 : ℝ) ≤ 2 * x := by linarith
  set L := Real.log x with hLdef
  -- Unpack the dyadic membership.
  rw [mem_pows2Ioc U (2 * x / V) one_le_U j] at hj
  obtain ⟨hjU, hj2⟩ := hj
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with rfl | h
    · exact absurd hjU (by simpa using not_lt.mpr one_le_U)
    · exact h
  set M := (2 : ℕ) ^ j with hMdef
  set N := ⌊x / 2 ^ (j - 1)⌋₊ with hNdef
  have hMcast : (M : ℝ) = (2 : ℝ) ^ j := by grind
  have hMle : (M : ℝ) ≤ 2 * x / V := by grind
  have hUM : U < (M : ℝ) := by grind
  -- Apply the large-sieve convolution bound.
  have hLS := LargeSieve_convolution (M := M) (N := N)
      ((f j).on {m | r.Coprime m}) ((g j).on {m | r.Coprime m})
      (fun n hn => f_on_coprime_supp r j hn) (fun n hn => g_on_coprime_supp r j hn)
      le_x hQ1
  rw [← hLdef] at hLS
  refine le_trans hLS ?_
  set af := Real.sqrt (∑ n ∈ Finset.Icc 1 M, ((f j).on {m | r.Coprime m} n) ^ 2) with hafdef
  set bg := Real.sqrt (∑ n ∈ Finset.Icc 1 N, ((g j).on {m | r.Coprime m} n) ^ 2) with hbgdef
  have haf0 : 0 ≤ af := Real.sqrt_nonneg _
  have hbg0 : 0 ≤ bg := Real.sqrt_nonneg _
  have hsqM_pos : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr (by rw [hMcast]; positivity)
  have hw2' : Real.sqrt (2 * x) * Real.sqrt (2 * x) = 2 * x := Real.mul_self_sqrt h2x0
  -- `ℓ²` bound for the `f`-factor: `af ≤ √M · (2 log x)`.
  have haf : af ≤ Real.sqrt (M : ℝ) * (2 * L) := by
    rw [hafdef]
    have h1 : (∑ n ∈ Finset.Icc 1 M, ((f j).on {m | r.Coprime m} n) ^ 2)
        ≤ (M : ℝ) * (2 * L) ^ 2 := by rw [hMcast]; exact f_on_coprime_l2 r j hj2
    calc Real.sqrt (∑ n ∈ Finset.Icc 1 M, ((f j).on {m | r.Coprime m} n) ^ 2)
        ≤ Real.sqrt ((M : ℝ) * (2 * L) ^ 2) := Real.sqrt_le_sqrt h1
      _ = Real.sqrt (M : ℝ) * (2 * L) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  -- `N ≤ 2x / M`.
  have hxeq : x / (2 : ℝ) ^ (j - 1) = 2 * x / 2 ^ j := by
    have hpow : (2 : ℝ) ^ j = 2 * 2 ^ (j - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hj1]
    grind
  have hN2 : (N : ℝ) ≤ 2 * x / (M : ℝ) := by
    rw [hMcast, ← hxeq]
    exact Nat.floor_le (div_nonneg hx0 (by positivity))
  -- `√N ≤ √(2x) / √M`.
  have hsqrtN : Real.sqrt (N : ℝ) ≤ Real.sqrt (2 * x) / Real.sqrt (M : ℝ) := by
    refine le_trans (Real.sqrt_le_sqrt hN2) ?_
    rw [Real.sqrt_div h2x0]
  -- `ℓ²` bound for the `g`-factor: `bg ≤ √(2x) / √M`.
  have hbg : bg ≤ Real.sqrt (2 * x) / Real.sqrt (M : ℝ) := by
    rw [hbgdef]
    exact le_trans (Real.sqrt_le_sqrt (g_on_coprime_l2 r j)) hsqrtN
  -- `af · bg ≤ 2 (log x) √(2x)`.
  have hP : af * bg ≤ 2 * L * Real.sqrt (2 * x) := by
    have h1 : af * bg ≤ (Real.sqrt (M : ℝ) * (2 * L)) * (Real.sqrt (2 * x) / Real.sqrt (M : ℝ)) :=
      mul_le_mul haf hbg hbg0 (mul_nonneg (Real.sqrt_nonneg _) (by linarith))
    refine le_trans h1 (le_of_eq ?_)
    grind
  -- `√(N·M) ≤ √(2x)`.
  have hNM : Real.sqrt ((N : ℝ) * (M : ℝ)) ≤ Real.sqrt (2 * x) := by
    rw [Real.sqrt_mul (by positivity)]
    calc Real.sqrt (N : ℝ) * Real.sqrt (M : ℝ)
        ≤ (Real.sqrt (2 * x) / Real.sqrt (M : ℝ)) * Real.sqrt (M : ℝ) := by
          gcongr
      _ = Real.sqrt (2 * x) := div_mul_cancel₀ _ (ne_of_gt hsqM_pos)
  -- `√M · √(2x) ≤ 2x / √V`.
  have hsw : Real.sqrt (M : ℝ) * Real.sqrt (2 * x) ≤ 2 * x / Real.sqrt V := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [show 2 * x / Real.sqrt V = Real.sqrt (4 * x ^ 2 / V) by
      rw [Real.sqrt_div (by positivity), show (4 : ℝ) * x ^ 2 = (2 * x) ^ 2 by ring,
        Real.sqrt_sq h2x0]]
    apply Real.sqrt_le_sqrt
    calc (M : ℝ) * (2 * x) ≤ (2 * x / V) * (2 * x) := by
          apply mul_le_mul_of_nonneg_right hMle h2x0
      _ = 4 * x ^ 2 / V := by ring
  -- Term `T1`: the `√(NM)` piece.
  have hT1 : Real.sqrt ((N : ℝ) * (M : ℝ)) * L * af * bg ≤ 4 * L ^ 2 * x := by
    calc Real.sqrt ((N : ℝ) * (M : ℝ)) * L * af * bg
        = Real.sqrt ((N : ℝ) * (M : ℝ)) * L * (af * bg) := by ring
      _ ≤ Real.sqrt (2 * x) * L * (2 * L * Real.sqrt (2 * x)) := by gcongr
      _ = 4 * L ^ 2 * x := by linear_combination (2 * L ^ 2) * hw2'
  -- Term `T2`: the `√M · Q` piece.
  have hT2 : Real.sqrt (M : ℝ) * Q * L * af * bg ≤ 4 * L ^ 2 * (Q * x / Real.sqrt V) := by
    calc Real.sqrt (M : ℝ) * Q * L * af * bg
        = Real.sqrt (M : ℝ) * Q * L * (af * bg) := by ring
      _ ≤ Real.sqrt (M : ℝ) * Q * L * (2 * L * Real.sqrt (2 * x)) := by gcongr
      _ = 2 * Q * L ^ 2 * (Real.sqrt (M : ℝ) * Real.sqrt (2 * x)) := by ring
      _ ≤ 2 * Q * L ^ 2 * (2 * x / Real.sqrt V) := by gcongr
      _ = 4 * L ^ 2 * (Q * x / Real.sqrt V) := by ring
  -- Term `T3`: the `√N · Q` piece.
  have hT3 : Real.sqrt (N : ℝ) * Q * L * af * bg ≤ 4 * L ^ 2 * (Q * x / Real.sqrt U) := by
    calc Real.sqrt (N : ℝ) * Q * L * af * bg
        = Real.sqrt (N : ℝ) * Q * L * (af * bg) := by ring
      _ ≤ (Real.sqrt (2 * x) / Real.sqrt U) * Q * L * (2 * L * Real.sqrt (2 * x)) := by
          have hNU : Real.sqrt (N : ℝ) ≤ Real.sqrt (2 * x) / Real.sqrt U :=
            hsqrtN.trans (by gcongr)
          gcongr
      _ = 4 * L ^ 2 * (Q * x / Real.sqrt U) := by
          grind
  -- Term `T4`: the `Q²` piece.
  have hT4 : Q ^ 2 * L * af * bg ≤ 4 * L ^ 2 * (Q ^ 2 * Real.sqrt x) := by
    have hw_le : Real.sqrt (2 * x) ≤ 2 * Real.sqrt x := by
      nlinarith [Real.sq_sqrt x_nonneg, Real.sqrt_nonneg x,
        Real.sq_sqrt h2x0, Real.sqrt_nonneg (2 * x), x_nonneg]
    calc Q ^ 2 * L * af * bg
        = Q ^ 2 * L * (af * bg) := by ring
      _ ≤ Q ^ 2 * L * (2 * L * Real.sqrt (2 * x)) := by gcongr
      _ = 2 * Q ^ 2 * L ^ 2 * Real.sqrt (2 * x) := by ring
      _ ≤ 2 * Q ^ 2 * L ^ 2 * (2 * Real.sqrt x) := by gcongr
      _ = 4 * L ^ 2 * (Q ^ 2 * Real.sqrt x) := by ring
  -- Combine the four terms.
  have hCLS : 0 ≤ C_LargeSieve := C_LargeSieve_nonneg
  have hkey : (Real.sqrt ((N : ℝ) * (M : ℝ)) + Real.sqrt (M : ℝ) * Q + Real.sqrt (N : ℝ) * Q + Q ^ 2)
        * L * af * bg ≤ 4 * L ^ 2 * (x + Q * x / √U + Q * x / √V + Q ^ 2 * √x) := by
    grind
  rw [show C_LargeSieve * 4 * L ^ 2 * (x + Q * x / √U + Q * x / √V + Q ^ 2 * √x)
      = C_LargeSieve * (4 * L ^ 2 * (x + Q * x / √U + Q * x / √V + Q ^ 2 * √x)) by ring,
    show C_LargeSieve * (Real.sqrt ((N : ℝ) * (M : ℝ)) + Real.sqrt (M : ℝ) * Q
        + Real.sqrt (N : ℝ) * Q + Q ^ 2) * L * af * bg
      = C_LargeSieve * ((Real.sqrt ((N : ℝ) * (M : ℝ)) + Real.sqrt (M : ℝ) * Q
        + Real.sqrt (N : ℝ) * Q + Q ^ 2) * L * af * bg) by ring]
  exact mul_le_mul_of_nonneg_left hkey hCLS

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
      q * (q.totient : ℝ)⁻¹ * maxyReal (fun y ↦ ENNReal.ofReal (S r y ξ))) Q
    ≤ C_BV_char_sum * (x + Q * x / Real.sqrt U + Q * x / Real.sqrt V + Q ^ 2 * Real.sqrt x) * (Real.log x) ^ 3 := by
  classical
  have hQ0 : (0 : ℝ) ≤ Q := by linarith
  -- Bound `maxy S` by the sum of dyadic suprema, then swap the order of summation.
  have hstep1 : summatory (fun q ↦ ∑ ξ : DirichletCharacter ℂ q with ξ.IsPrimitive,
        (q : ℝ) * (q.totient : ℝ)⁻¹ *
          maxyReal (fun y ↦ ENNReal.ofReal (S r y ξ))) Q
      ≤ summatory (fun q ↦ ∑ j ∈ pows2Ioc U (2 * x / V),
          ∑ ξ : DirichletCharacter ℂ q with ξ.IsPrimitive,
            (q : ℝ) * (q.totient : ℝ)⁻¹ * Gterm r j ξ) Q := by
    apply summatory_le_summatory
    intro q _ _
    calc ∑ ξ : DirichletCharacter ℂ q with ξ.IsPrimitive,
          (q : ℝ) * (q.totient : ℝ)⁻¹ * maxyReal (fun y ↦ ENNReal.ofReal (S r y ξ))
        ≤ ∑ ξ : DirichletCharacter ℂ q with ξ.IsPrimitive,
            ∑ j ∈ pows2Ioc U (2 * x / V), (q : ℝ) * (q.totient : ℝ)⁻¹ * Gterm r j ξ := by
          apply Finset.sum_le_sum
          intro ξ _
          rw [← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left (maxy_S_le_sum r ξ) (by positivity)
      _ = ∑ j ∈ pows2Ioc U (2 * x / V),
            ∑ ξ : DirichletCharacter ℂ q with ξ.IsPrimitive,
              (q : ℝ) * (q.totient : ℝ)⁻¹ * Gterm r j ξ := Finset.sum_comm
  refine le_trans hstep1 ?_
  rw [Finset.summatory_sum_comm (fun j q ↦ ∑ ξ : DirichletCharacter ℂ q with ξ.IsPrimitive,
    (q : ℝ) * (q.totient : ℝ)⁻¹ * Gterm r j ξ)]
  -- Nonnegativity of the bracket factor.
  have hbrack : 0 ≤ x + Q * x / Real.sqrt U + Q * x / Real.sqrt V + Q ^ 2 * Real.sqrt x := by
    have h1 : 0 ≤ Q * x / Real.sqrt U := div_nonneg (mul_nonneg hQ0 x_nonneg) (Real.sqrt_nonneg _)
    have h2 : 0 ≤ Q * x / Real.sqrt V := div_nonneg (mul_nonneg hQ0 x_nonneg) (Real.sqrt_nonneg _)
    have h3 : 0 ≤ Q ^ 2 * Real.sqrt x := mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
    have h4 : 0 ≤ x := x_nonneg
    linarith
  have hconst : 0 ≤ C_LargeSieve * 4 * (Real.log x) ^ 2 *
      (x + Q * x / Real.sqrt U + Q * x / Real.sqrt V + Q ^ 2 * Real.sqrt x) :=
    mul_nonneg (mul_nonneg (mul_nonneg C_LargeSieve_nonneg (by norm_num)) (by positivity)) hbrack
  calc ∑ j ∈ pows2Ioc U (2 * x / V),
        summatory (fun q ↦ ∑ ξ : DirichletCharacter ℂ q with ξ.IsPrimitive,
          (q : ℝ) * (q.totient : ℝ)⁻¹ * Gterm r j ξ) Q
      ≤ ∑ _j ∈ pows2Ioc U (2 * x / V), C_LargeSieve * 4 * (Real.log x) ^ 2 *
          (x + Q * x / Real.sqrt U + Q * x / Real.sqrt V + Q ^ 2 * Real.sqrt x) :=
        Finset.sum_le_sum fun j hj => summatory_Gterm_le r j Q hQ hj
    _ = ((pows2Ioc U (2 * x / V)).card : ℝ) * (C_LargeSieve * 4 * (Real.log x) ^ 2 *
          (x + Q * x / Real.sqrt U + Q * x / Real.sqrt V + Q ^ 2 * Real.sqrt x)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (3 * Real.log x) * (C_LargeSieve * 4 * (Real.log x) ^ 2 *
          (x + Q * x / Real.sqrt U + Q * x / Real.sqrt V + Q ^ 2 * Real.sqrt x)) :=
        mul_le_mul_of_nonneg_right card_pows2Ioc_le hconst
    _ = C_BV_char_sum * (x + Q * x / Real.sqrt U + Q * x / Real.sqrt V + Q ^ 2 * Real.sqrt x)
          * (Real.log x) ^ 3 := by
        rw [C_BV_char_sum]; ring

noncomputable def C_Tr : ℝ := 8 * C_BV_char_sum

theorem C_BV_char_sum_nonneg : 0 ≤ C_BV_char_sum := by
  unfold C_BV_char_sum
  exact mul_nonneg (by norm_num) C_LargeSieve_nonneg

theorem C_Tr_nonneg : 0 ≤ C_Tr := by
  unfold C_Tr
  exact mul_nonneg (by norm_num) C_BV_char_sum_nonneg

private theorem sum_Icc_half_le (jL jU : ℕ) (h : jL ≤ jU + 1) :
    ∑ j ∈ Finset.Icc jL jU, (1/2:ℝ)^j ≤ 2 * (1/2)^jL := by
  rw [← Finset.Ico_add_one_right_eq_Icc, geom_sum_Ico (by norm_num) h,
    div_le_iff_of_neg (by norm_num)]
  nlinarith [pow_nonneg (by norm_num:(0:ℝ)≤1/2) (jU+1), pow_nonneg (by norm_num:(0:ℝ)≤1/2) jL]

private theorem sum_Icc_two_le (jL jU : ℕ) :
    ∑ j ∈ Finset.Icc jL jU, (2:ℝ)^j ≤ 2 * 2^jU := by
  calc ∑ j ∈ Finset.Icc jL jU, (2:ℝ)^j
      ≤ ∑ j ∈ Finset.range (jU+1), (2:ℝ)^j :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (by grind)
          (by intros; positivity)
    _ = 2^(jU+1)-1 := by rw [geom_sum_eq (by norm_num)]; ring
    _ ≤ 2 * 2^jU := by ring_nf; grind

@[blueprint (statement := /--
$$T_r(x,Q) \ll \frac{x}{(\log x)^{C-3}} + \frac{x(\log x)^4}{\sqrt{U}} + \frac{x(\log x)^4}{\sqrt{V}} + \frac{Q\sqrt{x}\,(\log x)^3}{r}$$
-/) (proof := /--
Divide the sum defining $T_r$ into dyadic intervals in $d$ and apply \ref{BV_char_sum_bound}.
-/) (uses := [BV_char_sum_bound, LambdaFlat_dyadic, T])]
theorem T_r_bound [ProofData] (C : ℕ) (r : ℕ) (Q : ℝ) (hC : 3 ≤ C) (hQ : 2 ≤ Q) (hQx : Q ≤ x) :
    T C r Q ≤ C_Tr * (x / (Real.log x)^(C-3) + x * (Real.log x)^4 / √U
      + x * (Real.log x)^4 / √V + Q * √x * (Real.log x)^3 / r) := by
  classical
  have hlogx : (16:ℝ) ≤ Real.log x := sixteen_le_log_x
  have hlog0 : (0:ℝ) < Real.log x := by linarith
  have hlne : Real.log x ≠ 0 := ne_of_gt hlog0
  have hxnn : (0:ℝ) ≤ x := x_nonneg
  have hsU : (0:ℝ) < √U := by positivity
  have hsV : (0:ℝ) < √V := by positivity
  have hsx : (0:ℝ) ≤ √x := Real.sqrt_nonneg x
  have hCBV : (0:ℝ) ≤ C_BV_char_sum := C_BV_char_sum_nonneg
  have hQ0 : (0:ℝ) ≤ Q := by linarith
  -- The character-sum summand.
  set B : ℕ → ℝ := fun d ↦ ∑ ξ : DirichletCharacter ℂ d with ξ.IsPrimitive,
      (d:ℝ) * (d.totient:ℝ)⁻¹ *
        maxyReal (fun y ↦ ENNReal.ofReal (S r y ξ)) with hBdef
  have hBnn : ∀ d, 0 ≤ B d := by
    intro d
    refine Finset.sum_nonneg fun ξ _ ↦ ?_
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg d) (inv_nonneg.mpr (Nat.cast_nonneg _)))
      ENNReal.toReal_nonneg
  have hB : ∀ Q' : ℝ, 2 ≤ Q' → summatory B Q'
      ≤ C_BV_char_sum * (x + Q' * x / √U + Q' * x / √V + Q'^2 * √x) * (Real.log x)^3 :=
    fun Q' hQ' ↦ BV_char_sum_bound r Q' hQ'
  -- Rewrite `T` as a sum of `B d / d`.
  have hTeq : T C r Q =
      ∑ d ∈ Finset.Ioc ⌊(Real.log x)^C⌋₊ ⌊Q / (r:ℝ)⌋₊, B d / (d:ℝ) := by
    rw [T, Real.rpow_natCast]
    refine Finset.sum_congr rfl fun d hd ↦ ?_
    rw [Finset.mem_Ioc] at hd
    have hP1 : (1:ℝ) ≤ (Real.log x)^C := one_le_pow₀ (by linarith)
    have hdLower : (Real.log x)^C < (d : ℝ) := by
      rw [← Nat.floor_lt (by positivity : 0 ≤ (Real.log x)^C)]
      exact hd.1
    have hd1 : (1:ℝ) ≤ (d:ℝ) := le_trans hP1 hdLower.le
    have hdne : (d:ℝ) ≠ 0 := by linarith
    simp only [hBdef]
    rw [Finset.mul_sum, Finset.sum_div]
    grind
  rw [hTeq]
  set S : Finset ℕ := Finset.Ioc ⌊(Real.log x)^C⌋₊ ⌊Q / (r:ℝ)⌋₊ with hSdef
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · rw [hSe, Finset.sum_empty]
    apply mul_nonneg C_Tr_nonneg
    have h1 : (0:ℝ) ≤ x / (Real.log x)^(C-3) := by positivity
    have h2 : (0:ℝ) ≤ x * (Real.log x)^4 / √U := by positivity
    have h3 : (0:ℝ) ≤ x * (Real.log x)^4 / √V := by positivity
    have h4 : (0:ℝ) ≤ Q * √x * (Real.log x)^3 / (r:ℝ) :=
      div_nonneg (mul_nonneg (mul_nonneg hQ0 hsx) (by positivity)) (Nat.cast_nonneg r)
    linarith
  · obtain ⟨d0, hd0⟩ := hSne
    have hP1 : (1:ℝ) ≤ (Real.log x)^C := one_le_pow₀ (by linarith)
    rw [hSdef, Finset.mem_Ioc] at hd0
    have hW0 : (0:ℝ) ≤ Q / (r:ℝ) := by
      by_contra hneg
      have hfloor : ⌊Q / (r : ℝ)⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
      omega
    have hdLower : (Real.log x)^C < (d0 : ℝ) := by
      rw [← Nat.floor_lt (by positivity : 0 ≤ (Real.log x)^C)]
      exact hd0.1
    have hdUpper : (d0 : ℝ) ≤ Q / (r : ℝ) :=
      (Nat.le_floor_iff hW0).mp hd0.2
    have hPW : (Real.log x)^C ≤ Q / (r:ℝ) := hdLower.le.trans hdUpper
    have hW1 : (1:ℝ) ≤ Q / (r:ℝ) := le_trans hP1 hPW
    have hr1 : (1:ℝ) ≤ (r:ℝ) := by
      rcases Nat.eq_zero_or_pos r with hr | hr
      · exfalso; subst hr; grind
      · exact_mod_cast hr
    have hWx : Q / (r:ℝ) ≤ x := le_trans (div_le_self hQ0 hr1) hQx
    have hPfloor : ⌊(Real.log x)^C⌋₊ ≠ 0 := (Nat.floor_pos.mpr hP1).ne'
    have hWfloor : ⌊Q / (r:ℝ)⌋₊ ≠ 0 := (Nat.floor_pos.mpr hW1).ne'
    set jL : ℕ := Nat.log 2 ⌊(Real.log x)^C⌋₊ with hjLdef
    set jU : ℕ := Nat.log 2 ⌊Q / (r:ℝ)⌋₊ with hjUdef
    have hjLU : jL ≤ jU := by
      rw [hjLdef, hjUdef]; exact Nat.log_mono_right (Nat.floor_mono hPW)
    have hmaps : ∀ d ∈ S, Nat.log 2 d ∈ Finset.Icc jL jU := by
      intro d hd
      rw [hSdef, Finset.mem_Ioc] at hd
      rw [Finset.mem_Icc]
      refine ⟨?_, ?_⟩
      · rw [hjLdef]
        apply Nat.log_mono_right
        exact Nat.le_of_lt hd.1
      · rw [hjUdef]
        apply Nat.log_mono_right
        exact hd.2
    -- Key numeric facts about `jL, jU`.
    have hjLP1 : (Real.log x)^C < (2:ℝ)^(jL+1) := by
      have h1 : ⌊(Real.log x)^C⌋₊ + 1 ≤ 2^(jL+1) := by
        have := Nat.lt_pow_succ_log_self (b:=2) (by norm_num) ⌊(Real.log x)^C⌋₊
        rwa [← hjLdef] at this
      have h2 : (Real.log x)^C < (⌊(Real.log x)^C⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
      have h3 : ((⌊(Real.log x)^C⌋₊ : ℕ):ℝ) + 1 ≤ (2:ℝ)^(jL+1) := by
        calc ((⌊(Real.log x)^C⌋₊:ℕ):ℝ) + 1 = ((⌊(Real.log x)^C⌋₊ + 1 : ℕ):ℝ) := by grind
          _ ≤ ((2^(jL+1):ℕ):ℝ) := by exact_mod_cast h1
          _ = (2:ℝ)^(jL+1) := by grind
      linarith
    have h2jL : (Real.log x)^C < 2 * (2:ℝ)^jL := by
      have := hjLP1; rw [pow_succ] at this; linarith
    have h2jUleW : (2:ℝ)^jU ≤ Q / (r:ℝ) := by
      calc (2:ℝ)^jU = ((2^jU:ℕ):ℝ) := by grind
        _ ≤ ((⌊Q / (r:ℝ)⌋₊:ℕ):ℝ) := by
            exact_mod_cast (show (2^jU:ℕ) ≤ ⌊Q / (r:ℝ)⌋₊ by
              rw [hjUdef]; exact Nat.pow_log_le_self 2 hWfloor)
        _ ≤ Q / (r:ℝ) := Nat.floor_le hW0
    have h2jUx : (2:ℝ)^jU ≤ x := le_trans h2jUleW hWx
    -- Geometric/cardinality bounds.
    have hsumInv : ∑ j ∈ Finset.Icc jL jU, ((2:ℝ)^j)⁻¹ ≤ 4 / (Real.log x)^C := by
      have hconv : (∑ j ∈ Finset.Icc jL jU, ((2:ℝ)^j)⁻¹) = ∑ j ∈ Finset.Icc jL jU, (1/2:ℝ)^j := by
        apply Finset.sum_congr rfl; intro j _; rw [one_div, inv_pow]
      rw [hconv]
      refine le_trans (sum_Icc_half_le jL jU (by omega)) ?_
      rw [one_div, inv_pow, le_div_iff₀ (by positivity : (0:ℝ) < (Real.log x)^C)]
      have hcancel : (2:ℝ)^jL * ((2:ℝ)^jL)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
      nlinarith [h2jL, hcancel, inv_nonneg.mpr (le_of_lt (show (0:ℝ) < (2:ℝ)^jL by positivity)),
        mul_le_mul_of_nonneg_right (le_of_lt h2jL) (inv_nonneg.mpr (le_of_lt (show (0:ℝ) < (2:ℝ)^jL by positivity)))]
    have hsumPow : ∑ j ∈ Finset.Icc jL jU, (2:ℝ)^j ≤ 2 * (2:ℝ)^jU := sum_Icc_two_le jL jU
    have hcard : ((Finset.Icc jL jU).card : ℝ) ≤ 3 * Real.log x := by
      rw [Nat.card_Icc]
      have hle : ((jU + 1 - jL : ℕ):ℝ) ≤ ((jU + 1 : ℕ):ℝ) := by exact_mod_cast Nat.sub_le _ _
      have hjU1 : ((jU + 1:ℕ):ℝ) ≤ 3 * Real.log x := by
        have hjUlog : (jU:ℝ) * Real.log 2 ≤ Real.log x := by
          have h := Real.log_le_log (show (0:ℝ) < (2:ℝ)^jU by positivity) h2jUx
          rwa [Real.log_pow] at h
        have hlog2 : (0.6931471803:ℝ) < Real.log 2 := Real.log_two_gt_d9
        push_cast
        nlinarith [hjUlog, hlog2, hlogx, (Nat.cast_nonneg jU : (0:ℝ) ≤ (jU:ℝ)),
          mul_nonneg (Nat.cast_nonneg jU : (0:ℝ) ≤ (jU:ℝ))
            (by linarith [hlog2] : (0:ℝ) ≤ Real.log 2 - 0.6931471803)]
      linarith
    -- The final numeric combination.
    have hfinal : ∑ j ∈ Finset.Icc jL jU,
          ((2:ℝ)^j)⁻¹ * (C_BV_char_sum * (x + (2:ℝ)^(j+1)*x/√U + (2:ℝ)^(j+1)*x/√V
            + ((2:ℝ)^(j+1))^2*√x) * (Real.log x)^3)
        ≤ C_Tr * (x / (Real.log x)^(C-3) + x * (Real.log x)^4 / √U
            + x * (Real.log x)^4 / √V + Q * √x * (Real.log x)^3 / (r:ℝ)) := by
      have key : ∀ j : ℕ, ((2:ℝ)^j)⁻¹ * (C_BV_char_sum * (x + (2:ℝ)^(j+1)*x/√U + (2:ℝ)^(j+1)*x/√V
            + ((2:ℝ)^(j+1))^2*√x) * (Real.log x)^3)
          = C_BV_char_sum*(Real.log x)^3*x*((2:ℝ)^j)⁻¹
            + C_BV_char_sum*(Real.log x)^3*(2*x/√U)
            + C_BV_char_sum*(Real.log x)^3*(2*x/√V)
            + C_BV_char_sum*(Real.log x)^3*(4*√x)*(2:ℝ)^j := by
        intro j
        have h2j : (2:ℝ)^j ≠ 0 := by positivity
        grind
      have hA : ∑ j ∈ Finset.Icc jL jU, C_BV_char_sum*(Real.log x)^3*x*((2:ℝ)^j)⁻¹
          ≤ C_BV_char_sum*(Real.log x)^3*x*(4/(Real.log x)^C) := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left hsumInv (mul_nonneg (mul_nonneg hCBV (by positivity)) hxnn)
      have hEc : ∑ j ∈ Finset.Icc jL jU, C_BV_char_sum*(Real.log x)^3*(4*√x)*(2:ℝ)^j
          ≤ C_BV_char_sum*(Real.log x)^3*(4*√x)*(2*(2:ℝ)^jU) := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left hsumPow
          (mul_nonneg (mul_nonneg hCBV (by positivity)) (by positivity))
      have hBb : ∑ j ∈ Finset.Icc jL jU, C_BV_char_sum*(Real.log x)^3*(2*x/√U)
          ≤ (3*Real.log x)*(C_BV_char_sum*(Real.log x)^3*(2*x/√U)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right hcard
          (mul_nonneg (mul_nonneg hCBV (by positivity)) (by positivity))
      have hCc : ∑ j ∈ Finset.Icc jL jU, C_BV_char_sum*(Real.log x)^3*(2*x/√V)
          ≤ (3*Real.log x)*(C_BV_char_sum*(Real.log x)^3*(2*x/√V)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right hcard
          (mul_nonneg (mul_nonneg hCBV (by positivity)) (by positivity))
      have hbA : C_BV_char_sum*(Real.log x)^3*x*(4/(Real.log x)^C)
          ≤ 8*C_BV_char_sum*(x/(Real.log x)^(C-3)) := by
        have hpow : (Real.log x)^C = (Real.log x)^(C-3)*(Real.log x)^3 := by
          rw [← pow_add]; grind
        have heq : C_BV_char_sum*(Real.log x)^3*x*(4/(Real.log x)^C)
            = 4*C_BV_char_sum*(x/(Real.log x)^(C-3)) := by
          rw [hpow]; field_simp
        rw [heq]
        have : (0:ℝ) ≤ C_BV_char_sum*(x/(Real.log x)^(C-3)) := mul_nonneg hCBV (by positivity)
        linarith
      have hbB : (3*Real.log x)*(C_BV_char_sum*(Real.log x)^3*(2*x/√U))
          ≤ 8*C_BV_char_sum*(x*(Real.log x)^4/√U) := by
        have heq : (3*Real.log x)*(C_BV_char_sum*(Real.log x)^3*(2*x/√U))
            = 6*C_BV_char_sum*(x*(Real.log x)^4/√U) := by
          grind
        rw [heq]
        have : (0:ℝ) ≤ C_BV_char_sum*(x*(Real.log x)^4/√U) := mul_nonneg hCBV (by positivity)
        linarith
      have hbC : (3*Real.log x)*(C_BV_char_sum*(Real.log x)^3*(2*x/√V))
          ≤ 8*C_BV_char_sum*(x*(Real.log x)^4/√V) := by
        have heq : (3*Real.log x)*(C_BV_char_sum*(Real.log x)^3*(2*x/√V))
            = 6*C_BV_char_sum*(x*(Real.log x)^4/√V) := by
          grind
        rw [heq]
        have : (0:ℝ) ≤ C_BV_char_sum*(x*(Real.log x)^4/√V) := mul_nonneg hCBV (by positivity)
        linarith
      have hbE : C_BV_char_sum*(Real.log x)^3*(4*√x)*(2*(2:ℝ)^jU)
          ≤ 8*C_BV_char_sum*(Q*√x*(Real.log x)^3/(r:ℝ)) := by
        have hcoef : (0:ℝ) ≤ C_BV_char_sum*(Real.log x)^3*√x :=
          mul_nonneg (mul_nonneg hCBV (by positivity)) hsx
        calc C_BV_char_sum*(Real.log x)^3*(4*√x)*(2*(2:ℝ)^jU)
            = 8*(C_BV_char_sum*(Real.log x)^3*√x)*(2:ℝ)^jU := by ring
          _ ≤ 8*(C_BV_char_sum*(Real.log x)^3*√x)*(Q/(r:ℝ)) :=
              mul_le_mul_of_nonneg_left h2jUleW (by linarith [hcoef])
          _ = 8*C_BV_char_sum*(Q*√x*(Real.log x)^3/(r:ℝ)) := by ring
      calc ∑ j ∈ Finset.Icc jL jU, ((2:ℝ)^j)⁻¹ * (C_BV_char_sum * (x + (2:ℝ)^(j+1)*x/√U
              + (2:ℝ)^(j+1)*x/√V + ((2:ℝ)^(j+1))^2*√x) * (Real.log x)^3)
          = (∑ j ∈ Finset.Icc jL jU, C_BV_char_sum*(Real.log x)^3*x*((2:ℝ)^j)⁻¹)
              + (∑ j ∈ Finset.Icc jL jU, C_BV_char_sum*(Real.log x)^3*(2*x/√U))
              + (∑ j ∈ Finset.Icc jL jU, C_BV_char_sum*(Real.log x)^3*(2*x/√V))
              + (∑ j ∈ Finset.Icc jL jU, C_BV_char_sum*(Real.log x)^3*(4*√x)*(2:ℝ)^j) := by
            rw [Finset.sum_congr rfl (fun j _ ↦ key j), Finset.sum_add_distrib,
              Finset.sum_add_distrib, Finset.sum_add_distrib]
        _ ≤ (C_BV_char_sum*(Real.log x)^3*x*(4/(Real.log x)^C))
              + (3*Real.log x)*(C_BV_char_sum*(Real.log x)^3*(2*x/√U))
              + (3*Real.log x)*(C_BV_char_sum*(Real.log x)^3*(2*x/√V))
              + C_BV_char_sum*(Real.log x)^3*(4*√x)*(2*(2:ℝ)^jU) :=
            add_le_add (add_le_add (add_le_add hA hBb) hCc) hEc
        _ ≤ 8*C_BV_char_sum*(x/(Real.log x)^(C-3)) + 8*C_BV_char_sum*(x*(Real.log x)^4/√U)
              + 8*C_BV_char_sum*(x*(Real.log x)^4/√V) + 8*C_BV_char_sum*(Q*√x*(Real.log x)^3/(r:ℝ)) :=
            add_le_add (add_le_add (add_le_add hbA hbB) hbC) hbE
        _ = C_Tr * (x / (Real.log x)^(C-3) + x * (Real.log x)^4 / √U
              + x * (Real.log x)^4 / √V + Q * √x * (Real.log x)^3 / (r:ℝ)) := by
            rw [C_Tr]; ring
    -- Assemble the dyadic argument.
    calc ∑ d ∈ S, B d / (d:ℝ)
        ≤ ∑ d ∈ S, ((2:ℝ)^(Nat.log 2 d))⁻¹ * B d := by
          apply Finset.sum_le_sum
          intro d hd
          have hd1 : 1 ≤ d := by
            grind
          have hlog_le : (2:ℝ)^(Nat.log 2 d) ≤ (d:ℝ) := by
            calc (2:ℝ)^(Nat.log 2 d) = ((2^(Nat.log 2 d):ℕ):ℝ) := by grind
              _ ≤ (d:ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 (by omega : d ≠ 0)
          rw [div_eq_mul_inv, mul_comm ((2:ℝ)^(Nat.log 2 d))⁻¹ (B d)]
          exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) hlog_le) (hBnn d)
      _ = ∑ j ∈ Finset.Icc jL jU, ∑ d ∈ S with Nat.log 2 d = j,
            ((2:ℝ)^(Nat.log 2 d))⁻¹ * B d := (Finset.sum_fiberwise_of_maps_to hmaps _).symm
      _ = ∑ j ∈ Finset.Icc jL jU, ((2:ℝ)^j)⁻¹ * ∑ d ∈ S with Nat.log 2 d = j, B d := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          grind
      _ ≤ ∑ j ∈ Finset.Icc jL jU, ((2:ℝ)^j)⁻¹ * summatory B ((2:ℝ)^(j+1)) := by
          apply Finset.sum_le_sum
          intro j _
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [summatory]
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro d hd
            rw [Finset.mem_filter] at hd
            obtain ⟨hdS, hdj⟩ := hd
            rw [hSdef, Finset.mem_Ioc] at hdS
            rw [Finset.mem_Ioc]
            refine ⟨by
              grind, ?_⟩
            have hlt : d < 2^(Nat.log 2 d + 1) := Nat.lt_pow_succ_log_self (by norm_num) d
            rw [hdj] at hlt
            apply (Nat.le_floor_iff (by positivity : (0 : ℝ) ≤ (2 : ℝ)^(j+1))).mpr
            calc (d:ℝ) ≤ ((2^(j+1):ℕ):ℝ) := by exact_mod_cast (le_of_lt hlt)
              _ = (2:ℝ)^(j+1) := by grind
          · intro d _ _; exact hBnn d
      _ ≤ ∑ j ∈ Finset.Icc jL jU, ((2:ℝ)^j)⁻¹ *
            (C_BV_char_sum * (x + (2:ℝ)^(j+1)*x/√U + (2:ℝ)^(j+1)*x/√V
              + ((2:ℝ)^(j+1))^2*√x) * (Real.log x)^3) := by
          apply Finset.sum_le_sum
          intro j _
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact hB ((2:ℝ)^(j+1)) (by
            calc (2:ℝ) = (2:ℝ)^1 := (pow_one 2).symm
              _ ≤ (2:ℝ)^(j+1) := pow_le_pow_right₀ (by norm_num) (by omega))
      _ ≤ C_Tr * (x / (Real.log x)^(C-3) + x * (Real.log x)^4 / √U
            + x * (Real.log x)^4 / √V + Q * √x * (Real.log x)^3 / (r:ℝ)) := hfinal

/-- For `L ≥ 0` and `W ≥ e^{√L}`: `L^n ≤ (2^{2n} (2n)!) · √W`.  Used with `W = U, V` to absorb
the divisor factors: `√U, √V ≥ e^{½√log x}` beats every power of `log x`. -/
theorem log_pow_le_const_mul_sqrt [ProofData] (W : ℝ) (n : ℕ)
    (hW : Real.exp (Real.sqrt (Real.log x)) ≤ W) :
    (Real.log x) ^ n ≤ ((2 : ℝ) ^ (2 * n) * (2 * n).factorial) * Real.sqrt W := by
  have hL : (0 : ℝ) ≤ Real.log x := log_x_pos.le
  set s : ℝ := Real.sqrt (Real.log x) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsL : s ^ 2 = Real.log x := Real.sq_sqrt hL
  have hLn : (Real.log x) ^ n = s ^ (2 * n) := by rw [← hsL, ← pow_mul]
  have hfac : (s / 2) ^ (2 * n) / ((2 * n).factorial : ℝ) ≤ Real.exp (s / 2) :=
    Real.pow_div_factorial_le_exp (s / 2) (by positivity) (2 * n)
  have hfac' : (s / 2) ^ (2 * n) ≤ ((2 * n).factorial : ℝ) * Real.exp (s / 2) := by
    rw [← div_le_iff₀' (by positivity : (0 : ℝ) < ((2 * n).factorial : ℝ))]
    exact hfac
  have hexp : Real.exp (s / 2) = Real.sqrt (Real.exp s) := Real.exp_half s
  have hsqrtW : Real.sqrt (Real.exp s) ≤ Real.sqrt W := Real.sqrt_le_sqrt (by grind)
  have h2n : (0 : ℝ) < (2 : ℝ) ^ (2 * n) := by positivity
  calc (Real.log x) ^ n = s ^ (2 * n) := hLn
    _ = (2 : ℝ) ^ (2 * n) * (s / 2) ^ (2 * n) := by rw [div_pow]; field_simp
    _ ≤ (2 : ℝ) ^ (2 * n) * (((2 * n).factorial : ℝ) * Real.exp (s / 2)) := by
        exact mul_le_mul_of_nonneg_left hfac' h2n.le
    _ = ((2 : ℝ) ^ (2 * n) * (2 * n).factorial) * Real.exp (s / 2) := by ring
    _ ≤ ((2 : ℝ) ^ (2 * n) * (2 * n).factorial) * Real.sqrt W := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        grind

/-- Comparison bound `1/(d φ(d)) ≤ √2 · d^{-3/2}`, from `d ≤ 2 φ(d)²`. -/
theorem rphiInv_le_rpow (d : ℕ) :
    ((d : ℝ) * d.totient)⁻¹ ≤ Real.sqrt 2 * (1 / (d : ℝ) ^ ((3 : ℝ) / 2)) := by
  rcases eq_or_ne d 0 with rfl | hd0
  · simp [Real.zero_rpow (by norm_num : (3 : ℝ) / 2 ≠ 0)]
  have hdR : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd0
  have hφR : (0 : ℝ) < d.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hd0)
  have hφsq : (d : ℝ) ≤ 2 * (d.totient : ℝ) ^ 2 := by exact_mod_cast d_le_two_mul_totient_sq d
  have hpow : (d : ℝ) ^ ((3 : ℝ) / 2) = d * Real.sqrt d := by
    rw [Real.sqrt_eq_rpow, show ((3 : ℝ) / 2) = 1 + 1 / 2 by norm_num,
      Real.rpow_add hdR, Real.rpow_one]
  have hsqrt : Real.sqrt d ≤ Real.sqrt 2 * d.totient := by
    rw [show Real.sqrt 2 * (d.totient : ℝ) = Real.sqrt (2 * (d.totient) ^ 2) by
          rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hφR.le]]
    exact Real.sqrt_le_sqrt hφsq
  rw [show ((d : ℝ) * d.totient)⁻¹ = 1 / ((d : ℝ) * d.totient) from (one_div _).symm,
    mul_one_div, div_le_iff₀ (mul_pos hdR hφR), div_mul_eq_mul_div,
    le_div_iff₀ (Real.rpow_pos_of_pos hdR _), one_mul, hpow]
  calc (d : ℝ) * Real.sqrt d
      ≤ (d : ℝ) * (Real.sqrt 2 * d.totient) := mul_le_mul_of_nonneg_left hsqrt hdR.le
    _ = Real.sqrt 2 * ((d : ℝ) * d.totient) := by ring

theorem summable_rphiInv : Summable (fun d : ℕ ↦ ((d : ℝ) * d.totient)⁻¹) := by
  apply Summable.of_nonneg_of_le (fun d ↦ by positivity) rphiInv_le_rpow
  apply Summable.mul_left
  simpa using (Real.summable_one_div_nat_rpow.mpr (by norm_num : (1 : ℝ) < 3 / 2))

/-- The convergent constant `∑_d 1/(d φ(d))`, bounding the diagonal term in `T_r`. -/
noncomputable def C_rphi : ℝ := ∑' d : ℕ, ((d : ℝ) * d.totient)⁻¹

theorem C_rphi_nonneg : 0 ≤ C_rphi := tsum_nonneg (fun d ↦ by positivity)

theorem sum_rphiInv_le (Q : ℝ) : ∑ r ∈ Finset.Ioc 0 ⌊Q⌋₊, ((r : ℝ) * r.totient)⁻¹ ≤ C_rphi :=
  summable_rphiInv.sum_le_tsum _ (fun i _ ↦ by positivity)

/-- The implied constant in `BV_LambdaFlat_enorm`. -/
noncomputable def C_BV_LF (A : ℕ) : ℝ :=
  C_Tr * (C_tot * (1 + 2 * ((2 : ℝ) ^ (2 * (A + 5)) * (2 * (A + 5)).factorial)) + C_rphi)
    + C_BV_LFT A (A + 4)

theorem C_BV_LF_nonneg [ProofData] (A : ℕ) : 0 ≤ C_BV_LF A := by
  have hCtot : 0 ≤ C_tot := by
    rw [C_tot]
    exact mul_nonneg (by norm_num) (tsum_nonneg fun d ↦ fAF_nonneg d)
  rw [C_BV_LF, C_BV_LFT]
  exact add_nonneg
    (mul_nonneg C_Tr_nonneg
      (add_nonneg (mul_nonneg hCtot (by positivity)) C_rphi_nonneg))
    (mul_nonneg (C_DLF_nonneg A (A + 4)) hCtot)

@[blueprint (statement := /--
For each fixed $A \ge 0$, $x \ge 2$ and $1 \le Q \le \sqrt{x}/(\log x)^{A+3}$,
$$\sum_{q \le Q} \max_{\sqrt{x} \le y \le x} \max_{a \in (\Z/q\Z)^*} \left|\Delta_{\Lambda^\flat}(y;\,q,\,a)\right| \ll_A \frac{x}{(\log x)^A}$$
-/) (proof := /--
Plug the bound from \ref{T_r_bound} into \ref{BV_LambdaFlat_via_T},
then choose $U = V = e^{\sqrt{\log x}}$ and $C = A + 4$.
-/) (uses := [BV_LambdaFlat_via_T, T_r_bound, Delta_LambdaFlat_small_conductor])]
theorem BV_LambdaFlat_enorm [ProofData] (A : ℕ) (Q : ℝ) (h1Q : 1 ≤ Q)
    (hQ : Q ≤ √x / (Real.log x) ^ (A + 3)) :
    ∑ q ∈ Finset.Ioc 0 ⌊Q⌋₊,
      maxya q (fun y a ↦ ‖Δ_[Λ♭](y; q, a)‖ₑ) ≤
        ENNReal.ofReal (C_BV_LF A * x / (Real.log x) ^ A) := by
  classical
  have hL16 : (16 : ℝ) ≤ Real.log x := sixteen_le_log_x
  have hL1 : (1 : ℝ) ≤ Real.log x := by linarith
  have hLpos : (0 : ℝ) < Real.log x := by linarith
  have hLne : Real.log x ≠ 0 := hLpos.ne'
  have hx0 : (0 : ℝ) < x := by linarith [le_x]
  have hx1 : (1 : ℝ) ≤ x := by linarith [le_x]
  have hsqrt_nonneg : (0 : ℝ) ≤ √x := Real.sqrt_nonneg x
  have hsqrt_le_x : √x ≤ x := by
    rw [Real.sqrt_le_iff]
    exact ⟨ProofData.x_nonneg, le_self_pow₀ hx1 (by norm_num)⟩
  have hpowge : (1 : ℝ) ≤ (Real.log x) ^ (A + 3) := one_le_pow₀ hL1
  have hQ0 : (0 : ℝ) ≤ Q := by linarith
  have hQ_le_sqrt : Q ≤ √x := by
    refine hQ.trans ?_
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hsqrt_nonneg, hpowge]
  have hQ_le_x : Q ≤ x := hQ_le_sqrt.trans hsqrt_le_x
  have hsU : (0 : ℝ) < √U := Real.sqrt_pos.mpr ProofData.U_pos
  have hsV : (0 : ℝ) < √V := Real.sqrt_pos.mpr ProofData.V_pos
  have hCtot : (0 : ℝ) ≤ C_tot := by
    rw [C_tot]; exact mul_nonneg (by norm_num) (tsum_nonneg (fun d ↦ fAF_nonneg d))
  have hCTr : (0 : ℝ) ≤ C_Tr := C_Tr_nonneg
  have hCrphi : (0 : ℝ) ≤ C_rphi := C_rphi_nonneg
  set K : ℝ := (2 : ℝ) ^ (2 * (A + 5)) * (2 * (A + 5)).factorial with hKdef
  have hK0 : (0 : ℝ) ≤ K := by rw [hKdef]; positivity
  set Cmain : ℝ := C_Tr * (C_tot * (1 + 2 * K) + C_rphi) with hCmain
  have hCmain0 : (0 : ℝ) ≤ Cmain :=
    mul_nonneg hCTr (add_nonneg (mul_nonneg hCtot (by linarith [hK0])) hCrphi)
  -- Step 1: conductor decomposition + main-term regrouping.
  have hvia := BV_LambdaFlat_via_T Q A (A + 4) hQ_le_sqrt
  -- Step 2: main-term bound.
  have hmain : (∑ r ∈ Finset.Ioc 0 ⌊Q⌋₊,
      (r.totient : ℝ)⁻¹ * T ((A + 4 : ℕ)) r Q)
      ≤ Cmain * x / (Real.log x) ^ A := by
    by_cases hQ2 : 2 ≤ Q
    ·
      have htot : ∑ r ∈ Finset.Ioc 0 ⌊Q⌋₊, (r.totient : ℝ)⁻¹ ≤ C_tot * Real.log x := by
        have h := summatory_totient_inv_le Q hQ_le_x; rwa [summatory] at h
      have hrphi : ∑ r ∈ Finset.Ioc 0 ⌊Q⌋₊, ((r : ℝ) * r.totient)⁻¹ ≤ C_rphi := sum_rphiInv_le Q
      have hU5 : x * (Real.log x) ^ 5 / √U ≤ K * x / (Real.log x) ^ A := by
        rw [div_le_div_iff₀ hsU (by positivity)]
        have hlem := log_pow_le_const_mul_sqrt U (A + 5) le_U
        calc x * (Real.log x) ^ 5 * (Real.log x) ^ A
            = x * (Real.log x) ^ (A + 5) := by rw [mul_assoc, ← pow_add, Nat.add_comm 5 A]
          _ ≤ x * (K * √U) := by rw [hKdef]; exact mul_le_mul_of_nonneg_left hlem hx0.le
          _ = K * x * √U := by ring
      have hV5 : x * (Real.log x) ^ 5 / √V ≤ K * x / (Real.log x) ^ A := by
        rw [div_le_div_iff₀ hsV (by positivity)]
        have hlem := log_pow_le_const_mul_sqrt V (A + 5) le_V
        calc x * (Real.log x) ^ 5 * (Real.log x) ^ A
            = x * (Real.log x) ^ (A + 5) := by rw [mul_assoc, ← pow_add, Nat.add_comm 5 A]
          _ ≤ x * (K * √V) := by rw [hKdef]; exact mul_le_mul_of_nonneg_left hlem hx0.le
          _ = K * x * √V := by ring
      have hQ4 : Q * √x * (Real.log x) ^ 3 ≤ x / (Real.log x) ^ A := by
        have h1 : Q * √x ≤ x / (Real.log x) ^ (A + 3) := by
          rw [le_div_iff₀ (by positivity)]
          calc Q * √x * (Real.log x) ^ (A + 3)
              ≤ (√x / (Real.log x) ^ (A + 3)) * √x * (Real.log x) ^ (A + 3) := by gcongr
            _ = √x * √x := by field_simp
            _ = x := Real.mul_self_sqrt hx0.le
        calc Q * √x * (Real.log x) ^ 3 = (Q * √x) * (Real.log x) ^ 3 := by ring
          _ ≤ (x / (Real.log x) ^ (A + 3)) * (Real.log x) ^ 3 := by gcongr
          _ = x / (Real.log x) ^ A := by rw [pow_add]; field_simp
      set S3 : ℝ := x / (Real.log x) ^ (A + 1) + x * (Real.log x) ^ 4 / √U
          + x * (Real.log x) ^ 4 / √V with hS3def
      have hS3nn : (0 : ℝ) ≤ S3 := by rw [hS3def]; positivity
      have hc4nn : (0 : ℝ) ≤ Q * √x * (Real.log x) ^ 3 := by positivity
      have hterm : ∀ r ∈ Finset.Ioc 0 ⌊Q⌋₊, (r.totient : ℝ)⁻¹ * T ((A + 4 : ℕ)) r Q
          ≤ C_Tr * (S3 * (r.totient : ℝ)⁻¹
              + (Q * √x * (Real.log x) ^ 3) * ((r : ℝ) * r.totient)⁻¹) := by
        intro r hr
        rw [Finset.mem_Ioc_zero_floor] at hr
        have hr1 : (1 : ℝ) ≤ r := hr.1
        have hrpos : 0 < r := by exact_mod_cast hr1
        have hTb := T_r_bound (A + 4) r Q (by omega) hQ2 hQ_le_x
        have h34 : (A + 4) - 3 = A + 1 := by omega
        rw [h34] at hTb
        have hstep : (r.totient : ℝ)⁻¹ * T ((A + 4 : ℕ)) r Q
            ≤ (r.totient : ℝ)⁻¹ * (C_Tr * (x / (Real.log x) ^ (A + 1)
                + x * (Real.log x) ^ 4 / √U + x * (Real.log x) ^ 4 / √V
                + Q * √x * (Real.log x) ^ 3 / r)) :=
          mul_le_mul_of_nonneg_left hTb (by positivity)
        refine hstep.trans (le_of_eq ?_)
        grind
      have hb1 : S3 * (∑ r ∈ Finset.Ioc 0 ⌊Q⌋₊, (r.totient : ℝ)⁻¹) ≤ S3 * (C_tot * Real.log x) :=
        mul_le_mul_of_nonneg_left htot hS3nn
      have hb2 : (Q * √x * (Real.log x) ^ 3) * (∑ r ∈ Finset.Ioc 0 ⌊Q⌋₊, ((r : ℝ) * r.totient)⁻¹)
          ≤ (Q * √x * (Real.log x) ^ 3) * C_rphi :=
        mul_le_mul_of_nonneg_left hrphi hc4nn
      have hfinal2 : S3 * (C_tot * Real.log x) + (Q * √x * (Real.log x) ^ 3) * C_rphi
          ≤ (C_tot * (1 + 2 * K) + C_rphi) * x / (Real.log x) ^ A := by
        have ta : x / (Real.log x) ^ (A + 1) * (C_tot * Real.log x) = C_tot * x / (Real.log x) ^ A := by
          grind
        have tb : x * (Real.log x) ^ 4 / √U * (C_tot * Real.log x)
            = C_tot * (x * (Real.log x) ^ 5 / √U) := by ring
        have tc : x * (Real.log x) ^ 4 / √V * (C_tot * Real.log x)
            = C_tot * (x * (Real.log x) ^ 5 / √V) := by ring
        have hdist : S3 * (C_tot * Real.log x)
            = x / (Real.log x) ^ (A + 1) * (C_tot * Real.log x)
              + x * (Real.log x) ^ 4 / √U * (C_tot * Real.log x)
              + x * (Real.log x) ^ 4 / √V * (C_tot * Real.log x) := by grind
        rw [hdist, ta, tb, tc]
        have hb : C_tot * (x * (Real.log x) ^ 5 / √U) ≤ C_tot * (K * x / (Real.log x) ^ A) :=
          mul_le_mul_of_nonneg_left hU5 hCtot
        have hc : C_tot * (x * (Real.log x) ^ 5 / √V) ≤ C_tot * (K * x / (Real.log x) ^ A) :=
          mul_le_mul_of_nonneg_left hV5 hCtot
        have hd : (Q * √x * (Real.log x) ^ 3) * C_rphi ≤ (x / (Real.log x) ^ A) * C_rphi :=
          mul_le_mul_of_nonneg_right hQ4 hCrphi
        grind
      refine le_trans (Finset.sum_le_sum hterm) ?_
      rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hCmain,
        show C_Tr * (C_tot * (1 + 2 * K) + C_rphi) * x / (Real.log x) ^ A
          = C_Tr * ((C_tot * (1 + 2 * K) + C_rphi) * x / (Real.log x) ^ A) from by ring]
      apply mul_le_mul_of_nonneg_left _ hCTr
      exact le_trans (add_le_add hb1 hb2) hfinal2
    · push_neg at hQ2
      have hzero : (∑ r ∈ Finset.Ioc 0 ⌊Q⌋₊,
          (r.totient : ℝ)⁻¹ * T ((A + 4 : ℕ)) r Q) = 0 := by
        refine Finset.sum_eq_zero (fun r hr ↦ ?_)
        rw [Finset.mem_Ioc_zero_floor] at hr
        have hr1 : (1 : ℝ) ≤ r := hr.1
        have hrpos : 0 < r := by exact_mod_cast hr1
        have hlt : Q / r < (Real.log x) ^ (A + 4) := by
          have h1 : Q / r ≤ Q := by
            rw [div_le_iff₀ (by exact_mod_cast hrpos)]; nlinarith [hr1, hQ0]
          have h2 : (16 : ℝ) ≤ (Real.log x) ^ (A + 4) :=
            le_trans hL16 (le_self_pow₀ hL1 (by omega))
          linarith
        have hTz : T ((A + 4 : ℕ)) r Q = 0 := by
          have hfloor : ⌊Q / (r : ℝ)⌋₊ ≤ ⌊(Real.log x) ^ (A + 4)⌋₊ :=
            Nat.floor_mono hlt.le
          rw [T, Real.rpow_natCast, Finset.Ioc_eq_empty (not_lt_of_ge hfloor),
            Finset.sum_empty]
        rw [hTz, mul_zero]
      rw [hzero]
      exact div_nonneg (mul_nonneg hCmain0 hx0.le) (by positivity)
  -- Step 3: combine main term and error term.
  have hcombine : Cmain * x / (Real.log x) ^ A + C_BV_LFT A (A + 4) * x / (Real.log x) ^ A
      = C_BV_LF A * x / (Real.log x) ^ A := by
    rw [C_BV_LF, hCmain, hKdef]; ring
  have hreal : (∑ r ∈ Finset.Ioc 0 ⌊Q⌋₊,
      (r.totient : ℝ)⁻¹ * T ((A + 4 : ℕ)) r Q)
        + C_BV_LFT A (A + 4) * x / (Real.log x) ^ A ≤
      C_BV_LF A * x / (Real.log x) ^ A := by
    grind
  exact hvia.trans (ENNReal.ofReal_le_ofReal hreal)
