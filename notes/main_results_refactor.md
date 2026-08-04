# Refactor maximal estimates and isolate upstreamable lemmas

## Summary

- Make maximal quantities canonical `ℝ≥0∞` suprema, with real-valued compatibility corollaries.
- Replace custom real-endpoint intervals along the affected proof path with standard `Finset.Ioc` ranges.
- Move generic Chebyshev, von Mangoldt, `Delta`, logarithmic, and Siegel–Walfisz consequences out of `MainResults.lean`.
- Prepare independent Mathlib contributions from the results that do not depend on project axioms.

## Standard finite ranges

- Redefine `summatory` directly as:

  ```lean
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, f n
  ```

  Make `summatory_apply` definitional or a simp lemma.

- Express conductor sums in the refactored theorem chain as:

  ```lean
  Finset.Ioc 0 ⌊Q⌋₊
  ```

  preserving the range `1 ≤ q ≤ Q`.

- Express the Type II range `(log x)^C < d ≤ Q/r` as:

  ```lean
  Finset.Ioc ⌊(Real.log x)^C⌋₊ ⌊Q / r⌋₊
  ```

  This matches the blueprint’s strict lower bound.

- Remove all zero-conductor splitting and `ZMod 0` arguments from the affected proof chain.

- Do not add further API for the custom real-endpoint interval. Leave unrelated occurrences for a later project-wide removal.

## Maximal quantities

Add `BV/Maximal.lean` and define under `namespace BV`:

```lean
maxy  : (ℝ → ℝ≥0∞) → ℝ≥0∞
maxya : (q : ℕ) → (ℝ → ZMod q → ℝ≥0∞) → ℝ≥0∞
```

Define `maxy` using the interval subtype:

```lean
⨆ y : Set.Icc (√x) x, f y
```

Provide:

- `le_maxy`, `le_maxya`, `maxy_le`, `maxya_le`, and `maxya_le_unit` using the complete-lattice API.
- Finiteness lemmas from upper bounds by `ENNReal.ofReal B`.
- `maxyReal` and `maxyaReal` as documented `toReal` views.
- Bridge lemmas for finite suprema, finite sums, `ENNReal.ofReal`, `enorm`, norms, and real absolute values.

Use:

```lean
maxya q (fun y a ↦ ‖Δ_[f](y; q, a)‖ₑ)
```

for discrepancy maxima. Keep `S`, `T`, `Gterm`, constants, and algebraic estimates in `ℝ`; Type II maxima use:

```lean
maxyReal (fun y ↦ ENNReal.ofReal (S r y ξ))
```

Delete the accidental/nonessential API:

- Unconditional real nonnegativity lemmas for `maxy`.
- The unused raw-`Δ` maximal lemma.
- The unused comparison between raw and absolute-value `Δ` maxima.
- Boundedness and nonnegativity premises that were needed only because the old supremum lived in `ℝ`.

Add canonical estimates:

```lean
BV_LambdaLE_enorm
BV_LambdaSharp_enorm
BV_LambdaFlat_enorm
BV_Delta_Lambda_enorm
bombieri_vinogradov_enorm
```

Keep the existing real theorem names as finite `toReal` corollaries, including the current real-valued `bombieri_vinogradov`.

## Internal lemma isolation

- Move `Delta_add`, `Delta_sub`, `Delta_smul`, `Delta_finset_sum`, the uniform absolute bound, maximal triangle lemmas, and the identity relating `ψ - y/φ(q)` to `ΔΛ` into `BV/Delta.lean`.
- Factor the three-piece maximal triangle estimate through a generic two-function `Delta` triangle lemma. Keep only the `Λ = Λ♯ + Λ♭ + Λ≤U` specialization in `MainResults.lean`.
- Move `sixteen_le_log_x` beside the other `ProofData` consequences.
- Generalize `pnt_ratio_bound` into an explicit lemma over `x`, `z`, and `B`, assuming `1 < z`, `z ≤ x`, and `√x ≤ z`; place it in `BV/ForMathlib/Log.lean`.
- Keep only final constants, three-piece assembly, compact/large cases, and the final real/ENNReal theorems in `MainResults.lean`.

## Chebyshev and Siegel–Walfisz isolation

Create a Chebyshev module independent of the axioms:

- Define the modular Chebyshev function as `Chebyshev.psiMod`.
- Retain `chebyPsi` temporarily as a compatibility alias and preserve the scoped `ψ` notation.
- Move its summatory formula, modulus-one identity, nonnegativity, and comparison with `Chebyshev.psi` there.
- First prove the reusable bound

  ```lean
  |ψ z a - z / q.totient| ≤ Chebyshev.psi z + z
  ```

  and derive the explicit compact-range bound afterward.

Create a Siegel–Walfisz consequences module:

- Generalize `PNT` to an explicit endpoint assumption `2 ≤ z`, without `ProofData`.
- Replace the duplicated non-coprime von Mangoldt estimates with one explicit-endpoint theorem.
- Replace the existing project theorem and the private `coprime_vonMangoldt_error_generic` with one public generic coprime-error theorem.
- Add small `ProofData` wrappers only where existing call sites materially benefit.
- Keep all results depending on `siegel_walfisz` project-local.

## Upstream sequence

Prepare separate commits/PRs without editing the pinned Mathlib checkout.

1. **Prime-power sum generalization**

   Upstream `sum_PrimePow_eq_sum_sum_of_eq_zero` to `Mathlib.NumberTheory.Chebyshev`, generalized over an `AddCommMonoid`.

2. **Non-coprime von Mangoldt estimate**

   State the theorem entirely using standard Mathlib finsets:

   ```lean
   ∑ n ∈ Finset.Ioc 0 ⌊z⌋₊,
     if ¬q.Coprime n then Λ n else 0
   ```

   Prove nonnegativity so the absolute value is unnecessary, then upstream the bound by `log q * log z / log 2`.

3. **Modular Chebyshev package**

   Propose `Chebyshev.psiMod`, its finite-sum formula, nonnegativity, modulus-one identity, and `psiMod_le_psi` as one coherent contribution. Exclude the project compatibility alias and notation from the upstream patch.

4. **Deferred candidate**

   Keep the generalized logarithmic ratio lemma in `BV/ForMathlib/Log.lean` initially. Submit it independently only if its final explicit formulation is demonstrably reusable outside this project.

Do not propose project wrappers such as `summatory`, the maximal operators, or `Delta`-specific maximal lemmas directly to Mathlib.

## Verification

- Test zero, finite constant, monotone, bounded, and unbounded ENNReal suprema; an unbounded family must produce `∞`.
- Verify every live maximal argument is `ℝ≥0∞`-valued and no signed discrepancy maximum remains.
- Verify the real bridge recovers the former absolute-value supremum under the established finite bounds.
- Verify the affected conductor sums use `Finset.Ioc 0 ⌊Q⌋₊` and contain no special zero-conductor reasoning.
- Verify the Type II divisor range has the intended strict lower endpoint.
- Confirm there is one generic non-coprime estimate and one generic coprime-error theorem.
- Compile the foundational modules, all three `Lambda` modules, `MainResults.lean`, and the root `BV` target.
