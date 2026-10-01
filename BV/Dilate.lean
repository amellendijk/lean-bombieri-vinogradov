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
@[blueprint "def:dilate" (latexEnv := "definition") (title := /-- Dilation -/) (statement := /--
For $e \ge 1$ and an arithmetic function $f$, the \emph{dilation} of $f$ by $e$ is the arithmetic
function
$$(\delta_e * f)(n) := 1_{e \mid n}\, f(n/e),$$
i.e.\ the Dirichlet convolution of $f$ with the indicator $\delta_e$ of the singleton $\{e\}$.
-/)]
noncomputable def dilate (e : ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if e ∣ n then f (n / e) else 0, by simp⟩

@[simp] theorem dilate_apply (e n : ℕ) (f : ArithmeticFunction ℝ) :
    dilate e f n = if e ∣ n then f (n / e) else 0 := rfl

/-- Convolution passes through dilation: `f * dilate e g = dilate e (f * g)`.
(Reindex `d = e · b`; needs `0 < e`.) Combined with `mul_comm` this lets the
dilation land on the left factor, as `Delta_flog_bound` requires. -/
@[blueprint "lem:dilate" (latexEnv := "lemma") (title := /-- Properties of dilation -/) (statement := /--
Let $e \ge 1$ and let $f, g$ be real arithmetic functions. Then
$$f * (\delta_e * g) = \delta_e * (f * g) = (\delta_e * f) * g ,$$
and for every real $x$,
$$\sum_{k \le x} |(\delta_e * f)(k)| \le \sum_{k \le x} |f(k)|.$$
-/) (proof := /--
The identities are instances of associativity and commutativity of Dirichlet convolution. Concretely,
at $n = em$ all three functions equal $\sum_{ab = m} f(a) g(b)$ after the substitution $b \mapsto eb$
(respectively $a \mapsto ea$) in the divisor sum, and all three vanish when $e \nmid n$.

For the inequality, the non-zero terms on the left have $k = em$ with $m \le x/e$, and
$|(\delta_e * f)(em)| = |f(m)|$; reindexing by $m$ gives $\sum_{m \le x/e} |f(m)|$, which is a sub-sum of
the right-hand side since $x/e \le x$ and the terms are non-negative.
-/)]
theorem mul_dilate {e : ℕ} (he : 0 < e) (f g : ArithmeticFunction ℝ) :
    f * dilate e g = dilate e (f * g) := by
  ext n
  rw [dilate_apply]
  by_cases hn : e ∣ n
  · obtain ⟨m, rfl⟩ := hn
    rw [if_pos ⟨m, rfl⟩, mul_apply, mul_apply, Nat.mul_div_cancel_left _ he]
    rw [Finset.sum_congr rfl
      (g := fun x => if e ∣ x.2 then f x.1 * g (x.2 / e) else 0)
      (fun x _ => by rw [dilate_apply, mul_ite, mul_zero])]
    rw [← Finset.sum_filter]
    refine Finset.sum_bij' (fun x _ => (x.1, x.2 / e)) (fun x _ => (x.1, e * x.2)) ?_ ?_ ?_ ?_ ?_
    · rintro ⟨a, b⟩ hx
      simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hx
      obtain ⟨⟨hab, hne⟩, ⟨c, hc⟩⟩ := hx
      refine Nat.mem_divisorsAntidiagonal.2 ⟨?_, ?_⟩
      · subst hc
        show a * (e * c / e) = m
        rw [Nat.mul_div_cancel_left _ he]
        have h2 : e * (a * c) = e * m := by grind
        exact Nat.eq_of_mul_eq_mul_left he h2
      · grind
    · rintro ⟨a, c⟩ hx
      simp only [Nat.mem_divisorsAntidiagonal] at hx
      obtain ⟨hac, hne⟩ := hx
      refine Finset.mem_filter.2 ⟨Nat.mem_divisorsAntidiagonal.2 ⟨?_, ?_⟩, ⟨c, rfl⟩⟩
      · rw [← mul_assoc, mul_comm a, mul_assoc, hac]
      · positivity
    · rintro ⟨a, b⟩ hx
      simp only [Finset.mem_filter] at hx
      obtain ⟨c, hc⟩ := hx.2
      simp [hc, Nat.mul_div_cancel_left _ he]
    · rintro ⟨a, c⟩ _
      simp [Nat.mul_div_cancel_left _ he]
    · grind
  · rw [if_neg hn, mul_apply]
    apply Finset.sum_eq_zero
    rintro ⟨a, b⟩ hx
    rw [dilate_apply, if_neg, mul_zero]
    intro hdvd
    exact hn ((Nat.mem_divisorsAntidiagonal.mp hx).1 ▸ hdvd.mul_left a)

@[simp] theorem dilate_add (e : ℕ) (f g : ArithmeticFunction ℝ) :
    dilate e (f + g) = dilate e f + dilate e g := by
  ext n
  simp only [dilate_apply, ArithmeticFunction.add_apply]
  grind

private theorem mem_Ioc_floor (x : ℝ) (n : ℕ) :
    n ∈ Finset.Ioc 0 ⌊x⌋₊ ↔ 0 < n ∧ n ≤ x := by
  simp +contextual [Nat.pos_iff_ne_zero, Nat.le_floor_iff']

/-- Dividing the `e`-multiples of `{1, …, x}` by `e` gives exactly `{1, …, x/e}`. -/
theorem image_div_filter_dvd {e : ℕ} (he : 0 < e) (x : ℝ) :
    ((Finset.Ioc 0 ⌊x⌋₊).filter (fun m => e ∣ m)).image (fun k => k / e) =
      Finset.Ioc 0 ⌊x / e⌋₊ := by
  have he' : (0 : ℝ) < e := by positivity
  ext m
  simp only [Finset.mem_image, Finset.mem_filter, mem_Ioc_floor]
  constructor
  · rintro ⟨k, ⟨⟨h1, h2⟩, c, rfl⟩, rfl⟩
    rw [Nat.mul_div_cancel_left _ he]
    have hc : 0 < c := by
      grind
    refine ⟨hc, ?_⟩
    rw [le_div_iff₀ he']
    grind
  · rintro ⟨h1, h2⟩
    refine ⟨e * m, ⟨⟨?_, ?_⟩, ⟨m, rfl⟩⟩, Nat.mul_div_cancel_left _ he⟩
    · positivity
    · push_cast
      rw [mul_comm, ← le_div_iff₀ he']
      exact h2

/-- Dilation does not increase the `ℓ¹` mass (reindex `k = e·m`, identifying the
support with `{1, …, x/e} ⊆ {1, …, x}`). -/
@[blueprint "lem:dilate" (latexEnv := "lemma")]
theorem summatory_abs_dilate_le {e : ℕ} (he : 0 < e) (f : ArithmeticFunction ℝ) {x : ℝ} :
    summatory (fun k => |dilate e f k|) x ≤ summatory (fun k => |f k|) x := by
  have he' : (0 : ℝ) < e := by positivity
  simp only [summatory]
  calc ∑ k ∈ Finset.Ioc 0 ⌊x⌋₊, |dilate e f k|
      = ∑ k ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun m => e ∣ m), |f (k / e)| := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [dilate_apply]
        grind
    _ = ∑ m ∈ Finset.Ioc 0 ⌊x / e⌋₊, |f m| := by
        rw [← image_div_filter_dvd he x, Finset.sum_image]
        rintro a ha b hb hab
        simp only [Finset.mem_coe, Finset.mem_filter] at ha hb
        obtain ⟨c, rfl⟩ := ha.2
        obtain ⟨d, rfl⟩ := hb.2
        simp only [Nat.mul_div_cancel_left _ he] at hab
        rw [hab]
    _ ≤ ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, |f m| := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro m hm
          rw [mem_Ioc_floor] at hm ⊢
          refine ⟨hm.1, ?_⟩
          by_cases hx : 0 ≤ x
          · exact hm.2.trans (div_le_self hx (by exact_mod_cast he))
          · push Not at hx
            have : x / e < 0 := div_neg_of_neg_of_pos hx he'
            linarith [hm.1, hm.2]
        · grind

/-- `.on` is additive (the `sub` form is what the `Λ♯` decomposition needs). -/
@[blueprint "lem:restriction-hom" (latexEnv := "lemma")]
theorem ArithmeticFunction.on_sub {R : Type*} [Ring R] (S : Set ℕ) (f g : ArithmeticFunction R) :
    (f - g).on S = f.on S - g.on S := by
  ext n
  simp only [sub_eq_add_neg, ArithmeticFunction.add_apply, ArithmeticFunction.neg_apply]
  by_cases h : n ∈ S <;> simp [h]

/-- Restriction to a multiplicatively saturated set `S`
(`a * b ∈ S ↔ a ∈ S ∧ b ∈ S`) is a Dirichlet-convolution homomorphism. The
coprime set `{n | r.Coprime n}` is saturated by `Nat.coprime_mul_iff_right`. -/
@[blueprint "lem:restriction-hom" (latexEnv := "lemma") (title := /-- Restriction is a convolution homomorphism -/) (statement := /--
Let $S \subseteq \N$ be \emph{multiplicatively saturated}: $ab \in S$ if and only if $a \in S$ and $b \in S$.
Then for all arithmetic functions $f, g$ (with values in a semiring),
$$(f * g)|_S = f|_S * g|_S , \qquad\text{and}\qquad (f - g)|_S = f|_S - g|_S$$
for any $S$ when the values lie in a ring. In particular, since $(ab, r) = 1$ if and only if $(a, r) = 1$
and $(b, r) = 1$, this applies to $S = \{n : (n, r) = 1\}$: $(f * g)_r = f_r * g_r$ for every $r \in \N$.
-/) (proof := /--
Linearity of restriction is clear. For the convolution, evaluate both sides at $n$: the left side is
$1_{n \in S} \sum_{ab = n} f(a) g(b)$ and the right side is $\sum_{ab = n} 1_{a \in S} 1_{b \in S} f(a) g(b)$.
For each pair $ab = n$ saturation gives $1_{n \in S} = 1_{a \in S} 1_{b \in S}$.
-/)]
theorem ArithmeticFunction.on_mul_of_saturated {R : Type*} [Semiring R] (S : Set ℕ)
    (hS : ∀ a b, a * b ∈ S ↔ a ∈ S ∧ b ∈ S) (f g : ArithmeticFunction R) :
    (f * g).on S = f.on S * g.on S := by
  ext n
  by_cases hn : n ∈ S
  · rw [on_apply_of_mem _ _ _ hn, mul_apply, mul_apply]
    refine Finset.sum_congr rfl fun x hx => ?_
    obtain ⟨hab, -⟩ := Nat.mem_divisorsAntidiagonal.mp hx
    obtain ⟨ha, hb⟩ := (hS _ _).mp (hab ▸ hn)
    rw [on_apply_of_mem _ _ _ ha, on_apply_of_mem _ _ _ hb]
  · rw [on_apply_of_not_mem _ _ _ hn, mul_apply]
    symm
    refine Finset.sum_eq_zero fun x hx => ?_
    obtain ⟨hab, -⟩ := Nat.mem_divisorsAntidiagonal.mp hx
    have hnot : ¬ (x.1 ∈ S ∧ x.2 ∈ S) := fun h => hn (hab ▸ (hS _ _).mpr h)
    rw [not_and_or] at hnot
    rcases hnot with h | h
    · rw [on_apply_of_not_mem _ _ _ h, zero_mul]
    · rw [on_apply_of_not_mem _ _ _ h, mul_zero]

/-- The `ℕ → R` restriction `onCoprime` agrees with the arithmetic-function
restriction `.on {n | r.Coprime n}` (both send `0 ↦ 0` as `f 0 = 0`). -/
@[blueprint "def:restriction" (latexEnv := "definition") (hasProof := false)]
theorem onCoprime_eq_on_coe {R : Type*} [Zero R] (r : ℕ) (f : ArithmeticFunction R) :
    onCoprime r (⇑f) = ⇑(f.on {n | r.Coprime n}) := by
  funext n
  rw [onCoprime_apply]
  by_cases h : r.Coprime n
  · rw [if_pos h, on_apply_of_mem _ _ _ (show n ∈ {n | r.Coprime n} from h)]
  · rw [if_neg h, on_apply_of_not_mem _ _ _ (show n ∉ {n | r.Coprime n} from h)]

/-- Restriction shrinks each coefficient in absolute value. -/
theorem abs_on_le (S : Set ℕ) (f : ArithmeticFunction ℝ) (k : ℕ) :
    |f.on S k| ≤ |f k| := by
  by_cases hk : k ∈ S
  · rw [on_apply_of_mem _ _ _ hk]
  · rw [on_apply_of_not_mem _ _ _ hk, abs_zero]
    positivity

/-- `ℓ¹` submultiplicativity of Dirichlet convolution. -/
@[blueprint "lem:l1-submult" (latexEnv := "lemma") (title := /-- Submultiplicativity of the $\ell^1$ norm -/) (statement := /--
For real arithmetic functions $f, g$ and every real $x \ge 0$,
$$\sum_{k \le x} |(f * g)(k)| \le \Big( \sum_{k \le x} |f(k)| \Big) \Big( \sum_{k \le x} |g(k)| \Big).$$
-/) (proof := /--
By the triangle inequality the left side is at most $\sum_{k \le x} \sum_{ab = k} |f(a)||g(b)|$. The
pairs $(a, b)$ with $ab = k \le x$ for the various $k$ are pairwise distinct and all satisfy
$1 \le a \le x$, $1 \le b \le x$, so this double sum is at most $\sum_{a \le x} \sum_{b \le x} |f(a)||g(b)|$.
-/)]
theorem summatory_abs_mul_le (f g : ArithmeticFunction ℝ) {x : ℝ} (_hx : 0 ≤ x) :
    summatory (fun k => |(f * g) k|) x
      ≤ summatory (fun k => |f k|) x * summatory (fun k => |g k|) x := by
  simp only [summatory]
  -- Step 1: triangle inequality on each Dirichlet convolution
  refine le_trans (Finset.sum_le_sum
    (g := fun k => ∑ p ∈ k.divisorsAntidiagonal, |f p.1| * |g p.2|) fun k _ => ?_) ?_
  · rw [mul_apply]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun p _ => abs_mul _ _
  -- Step 2: regroup the double sum and bound it by the product of marginals
  have hdisj : (↑(Finset.Ioc 0 ⌊x⌋₊) : Set ℕ).PairwiseDisjoint
      (fun k => k.divisorsAntidiagonal) := by
    intro k₁ _ k₂ _ hne
    simp only [Function.onFun, Finset.disjoint_left, Nat.mem_divisorsAntidiagonal]
    grind
  rw [← Finset.sum_biUnion hdisj, Finset.sum_mul_sum, ← Finset.sum_product']
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    simp only [Finset.mem_biUnion, Nat.mem_divisorsAntidiagonal] at hp
    obtain ⟨k, hk, hpk, hk0⟩ := hp
    subst hpk
    obtain ⟨hp1, hp2⟩ := Nat.mul_ne_zero_iff.mp hk0
    rw [Finset.mem_Ioc] at hk
    rw [Finset.mem_product, Finset.mem_Ioc, Finset.mem_Ioc]
    refine ⟨⟨Nat.pos_of_ne_zero hp1, ?_⟩, ⟨Nat.pos_of_ne_zero hp2, ?_⟩⟩
    · exact (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hp2)).trans hk.2
    · exact (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hp1)).trans hk.2
  · intro p _ _
    positivity
