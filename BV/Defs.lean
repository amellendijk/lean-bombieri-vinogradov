import Mathlib
import Architect

import BV.Axioms
import BV.Summatory

open ArithmeticFunction
open scoped Moebius zeta

def Nat.modEqs {q : ℕ} (a : ZMod q) : Set ℕ := {n : ℕ | n = a}

@[simp]
theorem Nat.modEqs_one_one : Nat.modEqs (1 : ZMod 1) = Set.univ := by
  have : ∀ n : ZMod 1, n = 1 := fun n ↦ Subsingleton.elim n 1
  simp [modEqs, this]

@[simp]
theorem Nat.mem_modEqs {q : ℕ} (a : ZMod q) (n : ℕ) :
    n ∈ modEqs a ↔ n = a := by
  rfl

lemma chebyPsi_eq_summatory (x : ℝ) {q : ℕ} (a : ZMod q) :
    chebyPsi x a = summatory ((Nat.modEqs a).indicator Λ) x := by
  classical
  simp [summatory_apply, chebyPsi, Finset.sum_filter]
  congr! with n hn
  simp [Set.indicator_apply]

scoped[BV] notation "ψ" => chebyPsi

open BV

lemma summatory_vonMangoldt {x : ℝ} : summatory (fun n ↦ Λ n) x = Chebyshev.psi x := by
  simp [Chebyshev.psi_eq_sum_Icc]
  rw [summatory_apply, ← Finset.add_sum_Ioc_eq_sum_Icc]
  · simp
  · simp

theorem ψ_one_one {x : ℝ} : ψ x (1 : ZMod 1) = Chebyshev.psi x := by
  simp [chebyPsi_eq_summatory, Chebyshev.psi_eq_sum_Icc, summatory_vonMangoldt]

@[blueprint (statement :=
/-- For $f : \N \rightarrow \R$ and $r : \N$ we use $f_r$ to denote $n \mapsto f(n) 1_{(n, r) = 1}$-/
)]
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
  split_ifs with h
  · exact hfg _ rfl h
  · rfl

theorem onCoprime_nonneg {R : Type*} [Zero R] [Preorder R] {r : ℕ} {f : ℕ → R} {n : ℕ}
    (hf : 0 ≤ f n) : 0 ≤ onCoprime r f n := by
  unfold onCoprime
  split
  · exact hf
  · exact le_refl 0

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
  split_ifs <;> simp [hf]

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

@[grind .]
theorem ProofData.U_pos : 0 < U := by
  calc 0 < Real.exp (√ (Real.log x)) := ?A
    _ ≤ U := le_U
  positivity

@[grind .]
theorem ProofData.U_nonneg : 0 ≤ U := le_of_lt U_pos

@[grind .]
theorem ProofData.one_le_U : 1 ≤ U := by
  apply le_trans _ le_U
  simp

@[grind .]
theorem ProofData.V_pos : 0 < V := by
  calc 0 < Real.exp (√(Real.log x)) := ?A
    _ ≤ V := le_V
  positivity

@[grind .]
theorem ProofData.V_nonneg : 0 ≤ V := le_of_lt V_pos

@[grind .]
theorem ProofData.one_le_V : 1 ≤ V := by
  apply le_trans _ le_V
  simp

@[grind .]
theorem ProofData.x_nonneg : 0 ≤ x := by
  linarith only [le_x]

@[grind ., bound]
theorem ProofData.U_le_sqrt_x : U ≤ √x := by
  calc _ ≤ U * V := le_mul_of_one_le_right U_nonneg one_le_V
    _ ≤ Real.sqrt x := UV_le

@[grind ., bound]
theorem ProofData.U_le_x : U ≤ x := by
  calc _ ≤ Real.sqrt x := U_le_sqrt_x
    _ ≤ x := by
      refine Real.sqrt_le_iff.mpr ?_
      constructor
      · exact x_nonneg
      · exact le_self_pow₀ (by linarith only [le_x]) (by norm_num)

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

lemma log_x_pos : 0 < Real.log x := by
  apply Real.log_pos
  linarith only [le_x]

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
      norm_num
      linarith
    · exact le_x


noncomputable def maxy [ProofData] (f : ℝ → ℝ) : ℝ :=  ⨆ y ∈ Set.Icc (√ x) x, f y

theorem maxy_le {f : ℝ → ℝ} {M : ℝ}
    (hf : ∀ y, √x ≤ y → y ≤ x → f y ≤ M) (hM : 0 ≤ M) :
    maxy f ≤ M := by
  simp [maxy]
  apply Real.iSup_le _ hM
  intro y
  apply Real.iSup_le _ hM
  intro hy
  apply hf _ hy.1 hy.2

-- TODO : We're taking the maximum over the naturals in [√x, x], but really we should use reals.
/-- The maximum of $f$ over all $y \in \left[\sqrt{x}, x\right]$ and $a \in (\mathbb{Z} / q\mathbb{Z})^* -/
noncomputable def maxya [ProofData] (q : ℕ) (f : ℝ → ZMod q → ℝ) : ℝ :=
  ⨆ a : (ZMod q)ˣ, maxy (fun y ↦ f y a)

theorem maxya_le {q : ℕ} {f : ℝ → ZMod q → ℝ} {M : ℝ} (hf : ∀ y, √x ≤ y → y ≤ x → ∀ a, f y a ≤ M) (hM : 0 ≤ M) :
    maxya q f ≤ M := by
  rw [maxya]
  apply Real.iSup_le _ hM
  intro a
  apply maxy_le _ hM
  grind

/-- Restrict an arithmetic function to a set, setting all values outside the set to zero.
Like `Set.indicator` but for `ArithmeticFunction`. -/
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
@[blueprint (statement :=
/-- $\Lambda_{\le U} = 1_{≤ U} \cdot \Lambda$ -/
)]
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
@[blueprint (statement :=
/-- $\mu_{\le U} = 1_{≤ U} \cdot \mu$ -/
)]
noncomputable def moebiusLEV [ProofData] : ArithmeticFunction ℝ :=
  (μ).on (Set.Icc 1 (Nat.floor V))

scoped[BV] notation3 "μ≤V" => moebiusLEV

open ArithmeticFunction in
@[blueprint (statement :=
/-- $\Lambda^\sharp = \mu_{\le V} * \log - (\Lambda_{\le U} * \mu_{\le V}) * 1$ -/
)]
noncomputable def LambdaSharp [ProofData] : ArithmeticFunction ℝ :=
   μ≤V * log - Λ≤U * μ≤V * zeta

scoped[BV] notation3 "Λ♯" => LambdaSharp

@[blueprint (statement :=
/-- $\Lambda^\flat = (\Lambda_{>U} * 1) * \mu_{>V}$-/
)]
noncomputable def LambdaFlat : ArithmeticFunction ℝ :=
  (Λ - Λ≤U) * ζ * (μ - μ≤V)

scoped[BV] notation3 "Λ♭" => LambdaFlat


/-- Decompose $\Lambda = \Lambda^\sharp + \Lambda^\flat + \Lambda_{\le U}$  -/
@[blueprint (statement :=
/-- Decompose $\Lambda = \Lambda^\sharp + \Lambda^\flat + \Lambda_{\le U}$  -/
)]
theorem Lambda_decomp (n : ℕ) : Λ n = Λ♯ n + Λ♭ n + Λ≤U n := by
  simp_rw [← ArithmeticFunction.add_apply]
  congr 1
  simp [LambdaFlat, LambdaSharp, LambdaLEU, ← ArithmeticFunction.vonMangoldt_mul_zeta]
  have : (ζ * μ) = (1 : ArithmeticFunction ℝ) := coe_zeta_mul_coe_moebius
  grind



end Lambda
