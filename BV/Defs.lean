import Mathlib
import Architect

import BV.Axioms
import BV.Summatory

open ArithmeticFunction
open scoped Moebius zeta

open BV

@[blueprint "def:restriction" (latexEnv := "definition") (title := /-- Restriction -/) (statement := /--
For an arithmetic function $f$ and a set $S \subseteq \N$, let $f|_S$ denote the arithmetic function
$f|_S(n) := f(n) 1_{n \in S}$. For $r \in \N$ we write $f_r$ for the restriction of $f$ to the
integers coprime to $r$:
$$f_r(n) := f(n)\, 1_{(n, r) = 1} = \begin{cases} f(n) & \text{if } (r, n) = 1, \\ 0 & \text{otherwise.}\end{cases}$$
Note that $f_1 = f$ and that $f_0$ is supported on $n = 1$ only, since $(0, n) = n$. The same notation
is used for arbitrary functions $f : \N \to R$ with $R$ having a zero; when $f$ is an arithmetic
function the two readings agree.
-/)]
def onCoprime {R : Type*} [Zero R] (r : ℕ) (f : ℕ → R) (n : ℕ) : R :=
  if r.Coprime n then f n else 0

theorem onCoprime_apply {R : Type*} [Zero R] (r : ℕ) (f : ℕ → R) (n : ℕ) :
  onCoprime r f n = if r.Coprime n then f n else 0 := rfl

@[congr]
theorem onCoprime_congr {R : Type*} [Zero R] (r s : ℕ) (f g : ℕ → R) (n m : ℕ)
    (hrs : r = s) (hfg : ∀ x, x = n → r.Coprime x → f x = g x) (hnm : n = m) :
    onCoprime r f n = onCoprime s g m := by
  subst_vars
  simp [onCoprime]
  grind

theorem onCoprime_nonneg {R : Type*} [Zero R] [Preorder R] {r : ℕ} {f : ℕ → R} {n : ℕ}
    (hf : 0 ≤ f n) : 0 ≤ onCoprime r f n := by
  unfold onCoprime
  grind

/- This positivity extension was written by an LLM -/
open Qq Lean Meta Mathlib.Meta.Positivity in
@[positivity onCoprime _ _ _]
def onCoprime_positivity : PositivityExt where eval {u α} zα pα? e :=
  match pα? with | none => pure .none | some pα => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@onCoprime ℝ _ $r $f $n) =>
    let i : Q(ℕ) ← mkFreshExprMVarQ q(ℕ) .syntheticOpaque
    have body : Q(ℝ) := .betaRev f #[i]
    let rbody ← core zα pα body
    match rbody.toNonneg with
    | some pbody =>
      let pr : Q(∀ i, 0 ≤ $f i) ← mkLambdaFVars #[i] pbody
      assumeInstancesCommute
      return .nonnegative q(onCoprime_nonneg ($pr $n))
    | none => throwError "body not nonneg"
  | _, _, _ => throwError "not onCoprime"

theorem onCoprime_le_of_nonneg {R : Type*} [Zero R] [Preorder R] {r : ℕ} {f : ℕ → R} {n : ℕ} (hf : 0 ≤ f n):
    onCoprime r f n ≤ f n := by
  rw [onCoprime]
  grind

@[blueprint "def:parameters" (latexEnv := "definition") (title := /-- Parameter datum -/) (statement := /--
A \emph{parameter datum} consists of real numbers $x, U, V$ satisfying
$$x \ge 2, \qquad UV \le \sqrt{x}, \qquad U \ge e^{\sqrt{\log x}}, \qquad V \ge e^{\sqrt{\log x}}.$$
Every statement in Chapters~\ref{ch:vaughan} to~\ref{ch:assembly} that mentions $x$, $U$ or $V$
without quantifying them is implicitly universally quantified over such a datum, and the implied
constants in those statements never depend on the datum. The main theorem is proved by
instantiating $U = V = e^{\sqrt{\log x}}$ once $x > e^{32}$ (\Cref{thm:bombieri-vinogradov}).
-/)]
class ProofData where
  U : ℝ
  V : ℝ
  x : ℝ
  le_x : 2 ≤ x
  UV_le : U * V ≤ Real.sqrt x
  le_U : Real.exp (Real.sqrt (Real.log x)) ≤ U
  le_V : Real.exp (Real.sqrt (Real.log x)) ≤ V

open ProofData

variable [data : ProofData]

attribute [grind .] le_x

theorem ProofData.x_pos : 0 < x := by
  linarith only [le_x]

@[blueprint "lem:parameters" (latexEnv := "lemma"), grind .]
theorem ProofData.U_pos : 0 < U := by
  calc 0 < Real.exp (√ (Real.log x)) := ?A
    _ ≤ U := le_U
  positivity

@[grind .]
theorem ProofData.U_nonneg : 0 ≤ U := le_of_lt U_pos

@[blueprint "lem:parameters" (latexEnv := "lemma"), grind .]
theorem ProofData.one_le_U : 1 ≤ U := by
  apply le_trans _ le_U
  simp

@[blueprint "lem:parameters" (latexEnv := "lemma"), grind .]
theorem ProofData.V_pos : 0 < V := by
  calc 0 < Real.exp (√(Real.log x)) := ?A
    _ ≤ V := le_V
  positivity

@[grind .]
theorem ProofData.V_nonneg : 0 ≤ V := le_of_lt V_pos

@[blueprint "lem:parameters" (latexEnv := "lemma"), grind .]
theorem ProofData.one_le_V : 1 ≤ V := by
  apply le_trans _ le_V
  simp

@[grind .]
theorem ProofData.x_nonneg : 0 ≤ x := by
  linarith only [le_x]

@[blueprint "lem:parameters" (latexEnv := "lemma"), grind ., bound]
theorem ProofData.U_le_sqrt_x : U ≤ √x := by
  calc _ ≤ U * V := le_mul_of_one_le_right U_nonneg one_le_V
    _ ≤ Real.sqrt x := UV_le

@[blueprint "lem:parameters" (latexEnv := "lemma"), grind ., bound]
theorem ProofData.U_le_x : U ≤ x := by
  calc _ ≤ Real.sqrt x := U_le_sqrt_x
    _ ≤ x := by
      refine Real.sqrt_le_iff.mpr ?_
      constructor
      · exact x_nonneg
      · exact le_self_pow₀ (by linarith only [le_x]) (by positivity)

open Qq Lean Meta Mathlib.Meta.Positivity in
@[positivity @U _]
def U_positivity : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@U $inst) =>
    assumeInstancesCommute
    return .positive q(U_pos)
  | _, _, _ => throwError "not U"

open Qq Lean Meta Mathlib.Meta.Positivity in
@[positivity @V _]
def V_positivity : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@V $inst) =>
    assumeInstancesCommute
    return .positive q(V_pos)
  | _, _, _ => throwError "not V"

@[blueprint "lem:parameters" (latexEnv := "lemma") (title := /-- Consequences of the parameter constraints -/) (statement := /--
For every parameter datum $(x, U, V)$,
$$\log x \ge 16, \qquad x \ge e^{16}, \qquad 2 \le \sqrt x \le x, \qquad e \le U \le \sqrt x \le x, \qquad e \le V \le \sqrt x \le x .$$
-/) (proof := /--
Since $\sqrt{\log x} \ge 0$ we have $U, V \ge e^{\sqrt{\log x}} \ge 1$. Multiplying the two lower bounds
and using $UV \le \sqrt x$ gives $e^{2\sqrt{\log x}} \le UV \le \sqrt{x} = e^{(\log x)/2}$, so
$2\sqrt{\log x} \le \tfrac12 \log x$. Writing $s = \sqrt{\log x} > 0$ this reads $4 s \le s^2$, i.e.\
$s \ge 4$, so $\log x \ge 16$ and $x \ge e^{16}$. In particular $x \ge 4$, so $\sqrt x \ge 2$, and
$\sqrt x \le x$ as $x \ge 1$. Finally $U \le UV \le \sqrt x$ because $V \ge 1$, and $U \ge e^{\sqrt{\log x}} \ge e$
because $\log x \ge 1$; symmetrically for $V$.
-/)]
lemma log_x_pos : 0 < Real.log x := by
  apply Real.log_pos
  linarith only [le_x]

/-- Under `ProofData`, the constraints `exp(√(log x)) ≤ U, V` and `U·V ≤ √x`
force `log x` to be large; in particular `1 ≤ log x`. -/
@[blueprint "lem:parameters" (latexEnv := "lemma")]
theorem one_le_log_x : 1 ≤ Real.log x := by
  have hlogx : 0 < Real.log x := log_x_pos
  -- `exp(2√L) ≤ U·V ≤ √x`
  have hUV : Real.exp (Real.sqrt (Real.log x) + Real.sqrt (Real.log x)) ≤ Real.sqrt x := by
    rw [Real.exp_add]
    calc Real.exp (Real.sqrt (Real.log x)) * Real.exp (Real.sqrt (Real.log x))
        ≤ U * V := mul_le_mul le_U le_V (le_of_lt (Real.exp_pos _)) ProofData.U_nonneg
      _ ≤ Real.sqrt x := ProofData.UV_le
  -- take logs: `2√L ≤ log(√x) = L/2`
  have h1 : Real.sqrt (Real.log x) + Real.sqrt (Real.log x) ≤ Real.log (Real.sqrt x) := by
    have := Real.log_le_log (Real.exp_pos _) hUV
    rwa [Real.log_exp] at this
  rw [Real.log_sqrt ProofData.x_nonneg] at h1
  have ht : Real.sqrt (Real.log x) ^ 2 = Real.log x := Real.sq_sqrt (le_of_lt hlogx)
  nlinarith [Real.sqrt_nonneg (Real.log x), hlogx, h1, ht]

/-- Under `ProofData`, the constraints force `log x ≥ 16`. -/
@[blueprint "lem:parameters" (latexEnv := "lemma")]
theorem sixteen_le_log_x : 16 ≤ Real.log x := by
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

open Qq Lean Meta Mathlib.Meta.Positivity in
@[positivity Real.log x]
def x_positivity : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@x $inst) =>
    assumeInstancesCommute
    return .positive q(x_pos)
  | _, _, _ => throwError "not ProofData.x"

open Qq Lean Meta Mathlib.Meta.Positivity in
@[positivity Real.log x]
def log_x_positivity : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(Real.log (@x $inst)) =>
    assumeInstancesCommute
    return .positive q(log_x_pos)
  | _, _, _ => throwError "not Real.log x"

@[blueprint "lem:parameters" (latexEnv := "lemma")]
theorem Nat.Icc_sqrt_nonempty : (Nat.Icc (√x) x).Nonempty := by
  by_cases hx : 4 ≤ x
  · use ⌊x⌋₊
    simp only [mem_Icc]
    constructor
    · trans x - 1
      · rw [Real.sqrt_le_iff]
        have := le_x
        constructor
        · linarith
        · apply le_of_sub_nonneg
          nlinarith
      · simp only [tsub_le_iff_right]
        apply le_of_lt
        apply Nat.lt_floor_add_one
    · apply Nat.floor_le (x_nonneg)
  · use 2
    simp only [mem_Icc, cast_ofNat]
    constructor
    · rw [Real.sqrt_le_iff]
      grind
    · exact le_x


/-- Restrict an arithmetic function to a set, setting all values outside the set to zero.
Like `Set.indicator` but for `ArithmeticFunction`. -/
@[blueprint "def:restriction" (latexEnv := "definition")]
noncomputable def ArithmeticFunction.on {R : Type*} [Zero R] (s : Set ℕ) (f : ArithmeticFunction R) :
    ArithmeticFunction R :=
  ⟨s.indicator f, by simp⟩


omit [ProofData] in
@[simp]
theorem ArithmeticFunction.on_apply_of_mem {R : Type*} [Zero R] (s : Set ℕ) (f : ArithmeticFunction R) (n : ℕ) (hn : n ∈ s) :
    f.on s n = f n := by
  simp [on, hn]

omit [ProofData] in
@[simp]
theorem ArithmeticFunction.on_apply_of_not_mem {R : Type*} [Zero R] (s : Set ℕ) (f : ArithmeticFunction R) (n : ℕ) (hn : ¬ n ∈ s) :
    f.on s n = 0 := by
  simp [on, hn]

omit [ProofData] in
theorem ArithmeticFunction.on_nonneg {R : Type*} [Zero R] [Preorder R] {s : Set ℕ}
    {f : ArithmeticFunction R} (hf : ∀ n ∈ s, 0 ≤ f n) (n : ℕ) :
    0 ≤ f.on s n := by
  by_cases hn : n ∈ s
  · simp [hn, hf]
  · simp [hn]

omit [ProofData] in
@[simp]
theorem ArithmeticFunction.on_nonneg_iff {R : Type*} [Zero R] [Preorder R] (s : Set ℕ)
    (f : ArithmeticFunction R) :
    (∀ n, 0 ≤ f.on s n) ↔ ∀ n ∈ s, 0 ≤ f n := by
  constructor
  · intro h n hn
    simpa [hn] using h n
  · intro h
    apply on_nonneg h

section Lambda


/-- $\Lambda_{\le U} = 1_{≤ U} \cdot \Lambda$ -/
@[blueprint "def:vaughan-pieces" (latexEnv := "definition") (uses := ["not:arith"]) (title := /-- The pieces of Vaughan's identity -/) (statement := /--
Let $\Lambda_{\le U} := \Lambda \cdot 1_{[1, U]}$ and $\mu_{\le V} := \mu \cdot 1_{[1, V]}$ be the truncated
von Mangoldt and Möbius functions, so that $\Lambda_{\le U}(n) = \Lambda(n)$ if $n \le U$ and
$\Lambda_{\le U}(n) = 0$ if $n > U$, and similarly for $\mu_{\le V}$; write
$\Lambda_{> U} := \Lambda - \Lambda_{\le U}$ and $\mu_{> V} := \mu - \mu_{\le V}$. The \emph{Type~I part} and
the \emph{Type~II part} of $\Lambda$ are the arithmetic functions
$$\Lambda^\sharp := \mu_{\le V} * \log \;-\; \Lambda_{\le U} * \mu_{\le V} * 1, \qquad
\Lambda^\flat := (\Lambda_{> U} * 1) * \mu_{> V} .$$
-/)]
noncomputable def LambdaLEU [ProofData] : ArithmeticFunction ℝ :=
  ArithmeticFunction.vonMangoldt.on (Set.Icc 1 (Nat.floor U))

scoped[BV] notation3 "Λ≤U" => LambdaLEU

open BV

@[simp]
theorem LambdaLEU_apply_of_le {n : ℕ} (hn : n ≤ U) :
    Λ≤U n = Λ n := by
  by_cases hn0 : n = 0
  · simp [hn0]
  simp only [LambdaLEU]
  rw [on_apply_of_mem]
  simp [hn, Nat.le_floor]
  grind

@[simp]
theorem LambdaLEU_apply_of_gt {n : ℕ} (hn : U < n) :
    Λ≤U n = 0 := by
  rw [LambdaLEU, on_apply_of_not_mem]
  simp only [Set.mem_Icc, not_and, not_le]
  intro _
  rw [Nat.floor_lt U_nonneg]
  exact hn

@[simp]
theorem LambdaLEU_nonneg {n : ℕ} : 0 ≤ Λ≤U n := by
  rw [LambdaLEU]
  revert n
  simp

/- This positivity extension was written by an LLM. -/
open Qq Lean Meta Mathlib.Meta.Positivity in
@[positivity DFunLike.coe LambdaLEU _]
def LambdaLEU_positivity : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@DFunLike.coe _ _ _ _ (@LambdaLEU $inst) $n) =>
    assumeInstancesCommute
    return .nonnegative q(@LambdaLEU_nonneg $inst $n)
  | _, _, _ => throwError "not LambdaLEU"

/-- $\mu{\le U} = 1_{≤ U} \cdot \mu$ -/
@[blueprint "def:vaughan-pieces" (latexEnv := "definition")]
noncomputable def moebiusLEV [ProofData] : ArithmeticFunction ℝ :=
  (μ).on (Set.Icc 1 (Nat.floor V))

scoped[BV] notation3 "μ≤V" => moebiusLEV

open ArithmeticFunction in
@[blueprint "def:vaughan-pieces" (latexEnv := "definition")]
noncomputable def LambdaSharp [ProofData] : ArithmeticFunction ℝ :=
   μ≤V * log - Λ≤U * μ≤V * zeta

scoped[BV] notation3 "Λ♯" => LambdaSharp

@[blueprint "def:vaughan-pieces" (latexEnv := "definition")]
noncomputable def LambdaFlat : ArithmeticFunction ℝ :=
  (Λ - Λ≤U) * ζ * (μ - μ≤V)

scoped[BV] notation3 "Λ♭" => LambdaFlat


/-- Decompose $\Lambda = \Lambda^\sharp + \Lambda^\flat + \Lambda_{\le U}$  -/
@[blueprint "prop:vaughan" (latexEnv := "proposition") (proofUses := ["lem:moebius"]) (title := /-- Vaughan's identity -/) (statement := /--
For every $n \in \N$,
$$\Lambda(n) = \Lambda^\sharp(n) + \Lambda^\flat(n) + \Lambda_{\le U}(n).$$
-/) (proof := /--
Expand $\Lambda^\flat$ by bilinearity of the Dirichlet convolution and use the identities
$\Lambda * 1 = \log$ and $1 * \mu = \delta_1$ of \Cref{lem:moebius}:
$$\Lambda^\flat = \Lambda * 1 * \mu - \Lambda * 1 * \mu_{\le V} - \Lambda_{\le U} * 1 * \mu + \Lambda_{\le U} * 1 * \mu_{\le V}
= \Lambda - \log * \mu_{\le V} - \Lambda_{\le U} + \Lambda_{\le U} * \mu_{\le V} * 1 .$$
Adding $\Lambda^\sharp = \mu_{\le V} * \log - \Lambda_{\le U} * \mu_{\le V} * 1$ and $\Lambda_{\le U}$, everything
cancels except $\Lambda$.
-/)]
theorem Lambda_decomp (n : ℕ) : Λ n = Λ♯ n + Λ♭ n + Λ≤U n := by
  simp_rw [← ArithmeticFunction.add_apply]
  congr 1
  simp [LambdaFlat, LambdaSharp, LambdaLEU, ← ArithmeticFunction.vonMangoldt_mul_zeta]
  have : (ζ * μ) = (1 : ArithmeticFunction ℝ) := coe_zeta_mul_coe_moebius
  grind



end Lambda
