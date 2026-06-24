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
theorem character_sum_Mobius (f : ArithmeticFunction ℝ) {r q : ℕ} {x : ℝ} {a : ZMod q} (hq : 1 < q) (hrx : r ≤ x) (ha : IsUnit a) :
  open Classical in
    ∑ ξ : DirichletCharacter ℂ q with ξ.IsPrimitive, star (ξ a) * summatory (fun n ↦ ξ n * onCoprime r f n) x =
      ∑ p ∈ q.divisorsAntidiagonal, μ p.2 * p.1.totient * Δ_[onCoprime (r*q) f](x; q, a) := by sorry

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
