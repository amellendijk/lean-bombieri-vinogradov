import Mathlib
import Architect
import BV.Delta
import BV.Axioms

open ArithmeticFunction BV ProofData
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

namespace DirichletCharacter

/-- If `ξ` is a primitive character mod `d` and `d ∣ q` with `q ≠ 0`, then the character mod `q`
induced by `ξ` has conductor `d`. -/
theorem conductor_changeLevel_of_isPrimitive {q d : ℕ} [NeZero q] (hd : d ∣ q)
    {ξ : DirichletCharacter ℂ d} (hξ : ξ.IsPrimitive) :
    (changeLevel hd ξ).conductor = d := by
  have hq : q ≠ 0 := NeZero.ne q
  have hd0 : d ≠ 0 := fun h ↦ hq (Nat.eq_zero_of_zero_dvd (h ▸ hd))
  have h1 : (changeLevel hd ξ).conductor ∣ d :=
    (changeLevel hd ξ).conductor_dvd_of_mem_conductorSet hq ⟨hd, ξ, rfl⟩
  have h2 : ξ = changeLevel h1 (changeLevel hd ξ).primitiveCharacter := by
    apply changeLevel_injective hd
    rw [← changeLevel_trans _ h1 hd]
    exact (changeLevel_primitiveCharacter _).symm
  have h3 : ξ.conductor ∣ (changeLevel hd ξ).conductor :=
    ξ.conductor_dvd_of_mem_conductorSet hd0 ⟨h1, _, h2⟩
  have hξ' : ξ.conductor = d := hξ
  exact Nat.dvd_antisymm h1 ((dvd_of_eq hξ'.symm).trans h3)

/-- Summing a function over the characters mod `q` of conductor `d` is the same as summing
over the primitive characters mod `d`, via `changeLevel`. -/
theorem sum_conductor_eq {R : Type*} [AddCommMonoid R] {q d : ℕ} [NeZero q] (hd : d ∣ q)
    (f : DirichletCharacter ℂ q → R) :
  open Classical in
    ∑ χ : DirichletCharacter ℂ q with χ.conductor = d, f χ =
      ∑ ξ : DirichletCharacter ℂ d with ξ.IsPrimitive, f (ξ.changeLevel hd) := by
  classical
  refine (Finset.sum_bij (fun ξ _ ↦ changeLevel hd ξ) ?_ ?_ ?_ fun _ _ ↦ rfl).symm
  · intro ξ hξ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hξ ⊢
    exact conductor_changeLevel_of_isPrimitive hd hξ
  · intro ξ₁ _ ξ₂ _ h
    exact changeLevel_injective hd h
  · intro χ hχ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hχ
    subst hχ
    exact ⟨χ.primitiveCharacter,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, χ.primitiveCharacter_isPrimitive⟩,
      χ.changeLevel_primitiveCharacter⟩

end DirichletCharacter

/-- Version of `character_sum_by_conductor` without the restriction to non-principal
characters: every character mod `q` arises from a unique primitive character mod a
unique divisor `d` of `q` (its conductor). -/
theorem character_sum_by_conductor' {R : Type*} [AddCommMonoid R] {q : ℕ} [NeZero q]
    (f : DirichletCharacter ℂ q → R) :
  open Classical in
    ∑ χ : DirichletCharacter ℂ q, f χ =
      ∑ d ∈ q.divisors.attach, ∑ ξ : DirichletCharacter ℂ d with ξ.IsPrimitive,
        f (ξ.changeLevel (Nat.dvd_of_mem_divisors d.2)) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (t := q.divisors.attach)
    (g := fun χ : DirichletCharacter ℂ q ↦
      (⟨χ.conductor, Nat.mem_divisors.mpr ⟨χ.conductor_dvd_level, NeZero.ne q⟩⟩ :
        {d : ℕ // d ∈ q.divisors}))
    (fun _ _ ↦ Finset.mem_attach _ _) f]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [← DirichletCharacter.sum_conductor_eq (Nat.dvd_of_mem_divisors d.2) f]
  exact Finset.sum_congr (Finset.filter_congr fun χ _ ↦ by simp [Subtype.ext_iff]) fun _ _ ↦ rfl

@[blueprint (latexEnv := "lemma") (statement := /--
This is a standard result. Let $f$ be a function from Dirichlet characters. Then
$$\sum_{\substack{\chi \pmod{q} \\ \chi \ne \chi_0}} f(\chi) = \sum_{d \mid q} \sumstar_{\xi \pmod{d}} f(1_{(n,q)=1}\xi)$$
-/)]
theorem character_sum_by_conductor {R : Type*} [AddCommMonoid R] {q : ℕ} [NeZero q] (f : DirichletCharacter ℂ q → R) :
  open Classical in
    ∑ χ : DirichletCharacter ℂ q with χ ≠ 1, f χ = ∑ d ∈ q.divisors.attach with d.1 ≠ 1, ∑ ξ : DirichletCharacter ℂ d with ξ.IsPrimitive, f (ξ.changeLevel (Nat.dvd_of_mem_divisors d.2)) := by
  classical
  calc ∑ χ : DirichletCharacter ℂ q with χ ≠ 1, f χ
      = ∑ χ : DirichletCharacter ℂ q, if χ ≠ 1 then f χ else 0 := Finset.sum_filter _ _
    _ = ∑ d ∈ q.divisors.attach, ∑ ξ : DirichletCharacter ℂ d with ξ.IsPrimitive,
          if ξ.changeLevel (Nat.dvd_of_mem_divisors d.2) ≠ 1 then
            f (ξ.changeLevel (Nat.dvd_of_mem_divisors d.2)) else 0 :=
        character_sum_by_conductor' _
    _ = ∑ d ∈ q.divisors.attach, if d.1 ≠ 1 then
          (∑ ξ : DirichletCharacter ℂ d with ξ.IsPrimitive,
            f (ξ.changeLevel (Nat.dvd_of_mem_divisors d.2))) else 0 := by
        refine Finset.sum_congr rfl fun d _ ↦ ?_
        by_cases hd1 : d.1 = 1
        · rw [if_neg fun h ↦ h hd1]
          refine Finset.sum_eq_zero fun ξ _ ↦ ?_
          rw [if_neg]
          simp only [ne_eq, not_not]
          rw [DirichletCharacter.level_one' ξ hd1, DirichletCharacter.changeLevel_one]
        · rw [if_pos hd1]
          refine Finset.sum_congr rfl fun ξ hξ ↦ ?_
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hξ
          have hξ' : ξ.conductor = d.1 := hξ
          have hd0 : d.1 ≠ 0 := (Nat.pos_of_mem_divisors d.2).ne'
          rw [if_pos]
          rw [ne_eq, DirichletCharacter.changeLevel_eq_one_iff]
          intro h
          exact hd1 (hξ' ▸ (DirichletCharacter.eq_one_iff_conductor_eq_one hd0).mp h)
    _ = ∑ d ∈ q.divisors.attach with d.1 ≠ 1,
          ∑ ξ : DirichletCharacter ℂ d with ξ.IsPrimitive,
            f (ξ.changeLevel (Nat.dvd_of_mem_divisors d.2)) := (Finset.sum_filter _ _).symm

open Classical in
/-- The function `G` from the blueprint proof of `character_sum_Mobius` (with `P = q`):
for `e ≠ 1` it is `∑*_{ξ mod e} ξ̄(a) ∑_{n ≤ x} f_{rq}(n) ξ(n)`, and it vanishes at `e = 1`. -/
private noncomputable def Gsum (f : ArithmeticFunction ℝ) (r : ℕ) {q : ℕ} (a : ZMod q) (x : ℝ)
    (e : ℕ) : ℂ :=
  if e = 1 then 0 else
    ∑ ξ : DirichletCharacter ℂ e with ξ.IsPrimitive,
      star (ξ (ZMod.cast a)) * summatory (fun n ↦ ((onCoprime (r * q) f n : ℝ) : ℂ) * ξ n) x

/-- For `d ∣ q`, `∑_{e ∣ d} G(e) = φ(d) Δ_{f_{rq}}(x; d, a)`: expand `Δ` as a sum over the
non-principal characters mod `d` (`Delta_eq_sum_char`), then group the characters by conductor
(`character_sum_by_conductor`). -/
private theorem sum_divisors_Gsum (f : ArithmeticFunction ℝ) {r q d : ℕ} {x : ℝ} {a : ZMod q}
    (hq0 : q ≠ 0) (ha : IsUnit a) (hd0 : 0 < d) (hdq : d ∣ q) :
    ∑ e ∈ d.divisors, Gsum f r a x e =
      (d.totient : ℂ) * ((Δ_[onCoprime (r * q) f](x; d, a.cast) : ℝ) : ℂ) := by
  classical
  have : NeZero q := ⟨hq0⟩
  have : NeZero d := ⟨hd0.ne'⟩
  have ha' : IsUnit (a.cast : ZMod d) := by
    simpa using ha.map (ZMod.castHom hdq (ZMod d))
  have hφ : (d.totient : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hd0).ne'
  have hchange : ∀ {e : ℕ} (hed : e ∣ d) (ξ : DirichletCharacter ℂ e) {b : ZMod d},
      IsUnit b → DirichletCharacter.changeLevel hed ξ b = ξ (ZMod.cast b) := by
    rintro e hed ξ b ⟨u, rfl⟩
    exact DirichletCharacter.changeLevel_eq_cast_of_dvd ξ hed u
  have hΔ := Delta_eq_sum_char (𝕜 := ℝ) (f := onCoprime (r * q) ⇑f) (y := x) (q := d)
    (a := ZMod.cast a) ha'
  simp only [Complex.coe_algebraMap] at hΔ
  have hFd : (d.totient : ℂ) * ((Δ_[onCoprime (r * q) f](x; d, a.cast) : ℝ) : ℂ) =
      ∑ χ : DirichletCharacter ℂ d with χ ≠ 1,
        star (χ (ZMod.cast a)) * summatory (fun n ↦ ((onCoprime (r * q) f n : ℝ) : ℂ) * χ n) x := by
    rw [Finset.sum_filter, hΔ, ← mul_assoc, mul_inv_cancel₀ hφ, one_mul]
  rw [hFd, character_sum_by_conductor, ← Finset.sum_attach d.divisors (Gsum f r a x),
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  have hed : (e : ℕ) ∣ d := Nat.dvd_of_mem_divisors e.2
  by_cases he1 : (e : ℕ) = 1
  · simp [Gsum, he1]
  · rw [if_pos he1]
    simp only [Gsum, if_neg he1]
    refine Finset.sum_congr rfl fun ξ _ ↦ ?_
    have hcast : (ZMod.cast (a.cast : ZMod d) : ZMod (e : ℕ)) = a.cast := by
      rw [← ZMod.natCast_val (R := ZMod d) a, ZMod.cast_natCast hed]
      exact ZMod.natCast_val a
    rw [hchange hed ξ ha', hcast]
    congr 1
    refine summatory_congr rfl fun n _ _ ↦ ?_
    by_cases hn : (r * q).Coprime n
    · have hnd : IsUnit ((n : ZMod d)) := by
        rw [ZMod.isUnit_iff_coprime]
        exact (hn.coprime_dvd_left (hdq.trans (dvd_mul_left q r))).symm
      rw [hchange hed ξ hnd, ZMod.cast_natCast hed]
    · simp [onCoprime_apply, hn]

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
      ∑ p ∈ q.divisorsAntidiagonal, μ p.2 * p.1.totient * ((Δ_[onCoprime (r*q) f](x; p.1, a.cast) : ℝ) : ℂ) := by
  classical
  have hq0 : q ≠ 0 := by omega
  have hq1 : q ≠ 1 := by omega
  have : NeZero q := ⟨hq0⟩
  -- Möbius inversion of `sum_divisors_Gsum` over the divisor-closed set `{n | n ∣ q}`
  have key := ((ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq_on
      (f := Gsum f r a x)
      (g := fun d ↦ (d.totient : ℂ) * ((Δ_[onCoprime (r * q) f](x; d, a.cast) : ℝ) : ℂ))
      {n : ℕ | n ∣ q} (fun m n hmn hn ↦ hmn.trans hn)).mp
      (fun d hd0 hdq ↦ sum_divisors_Gsum f hq0 ha hd0 hdq)) q (Nat.pos_of_ne_zero hq0) dvd_rfl
  simp only [zsmul_eq_mul] at key
  calc ∑ ξ : DirichletCharacter ℂ q with ξ.IsPrimitive,
        star (ξ a) * summatory (fun n ↦ ξ n * onCoprime r f n) x
      = Gsum f r a x q := ?_
    _ = ∑ p ∈ q.divisorsAntidiagonal,
          (μ p.1 : ℂ) * ((p.2.totient : ℂ) * ((Δ_[onCoprime (r * q) f](x; p.2, a.cast) : ℝ) : ℂ)) :=
        key.symm
    _ = ∑ i ∈ q.divisors,
          (μ (q / i) : ℂ) * ((i.totient : ℂ) * ((Δ_[onCoprime (r * q) f](x; i, a.cast) : ℝ) : ℂ)) :=
        Nat.sum_divisorsAntidiagonal' fun i j ↦
          (μ i : ℂ) * ((j.totient : ℂ) * ((Δ_[onCoprime (r * q) f](x; j, a.cast) : ℝ) : ℂ))
    _ = ∑ i ∈ q.divisors,
          (μ (q / i) : ℂ) * (i.totient : ℂ) * ((Δ_[onCoprime (r * q) f](x; i, a.cast) : ℝ) : ℂ) :=
        Finset.sum_congr rfl fun i _ ↦ (mul_assoc _ _ _).symm
    _ = ∑ p ∈ q.divisorsAntidiagonal,
          μ p.2 * p.1.totient * ((Δ_[onCoprime (r*q) f](x; p.1, a.cast) : ℝ) : ℂ) :=
        (Nat.sum_divisorsAntidiagonal fun i j ↦
          (μ j : ℂ) * (i.totient : ℂ) * ((Δ_[onCoprime (r * q) f](x; i, a.cast) : ℝ) : ℂ)).symm
  -- It remains to identify the left-hand side with `Gsum f r a x q`.
  simp only [Gsum, if_neg hq1]
  refine Finset.sum_congr rfl fun ξ _ ↦ ?_
  rw [ZMod.cast_id]
  congr 1
  refine summatory_congr rfl fun n _ _ ↦ ?_
  by_cases hu : IsUnit ((n : ZMod q))
  · have hqn : q.Coprime n := ((ZMod.isUnit_iff_coprime n q).mp hu).symm
    rw [mul_comm]
    congr 1
    simp only [onCoprime_apply, Nat.coprime_mul_iff_left, and_iff_left hqn]
  · simp [MulChar.map_nonunit ξ hu]

@[blueprint (latexEnv := "lemma") (statement := /--
$$\left|\Delta_{\Lambda^\flat}(y;\, q,\, a)\right| \le \frac{1}{\varphi(q)} \left|\sum_{\substack{d \mid q \\ 1 < d \le (\log x)^C}} \sum_{s \mid d} \mu(d/s)\,\varphi(s)\,\Delta_{\Lambda^\flat_q}(y;\,s,\,a)\right| + \frac{1}{\varphi(q)} \sum_{\substack{d \mid q \\ d > (\log x)^C}} \sumstar_{\xi \pmod{d}} S_{q/d}(y, \xi)$$
-/) (uses := [character_sum_by_conductor, character_sum_Mobius, S])]
theorem Delta_LambdaFlat_decomp [ProofData] {C : ℕ} {y : ℝ} (q : ℕ) (a : ZMod q) (ha : IsUnit a)  :
  |Δ_[Λ♭](y; q, a)| ≤ (q.totient : ℝ)⁻¹ * |∑ d ∈ q.divisors with 1 < (d : ℕ) ∧ ↑d ≤ (Real.log x)^C, ∑ p ∈ d.divisorsAntidiagonal, μ p.2 * p.1.totient * Δ_[onCoprime q Λ♭](y; p.1, a.cast)| := by sorry


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
