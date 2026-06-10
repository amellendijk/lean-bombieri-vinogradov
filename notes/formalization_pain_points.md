# Formalization pain points: Theorem 26.6 (smoothed) in `BV/Flat/Perron.lean`

Notes written by Claude after formalizing `summatory_T_ll` (the smoothed Theorem 26.6 of
Koukoulopoulos, following `notes/theorem26_6_smooth.md`). The proof was almost a laboratory for
formalization pain points: the mathematical content is genuinely shallow — the only "ideas" are
Cauchy–Schwarz + the large sieve + splitting the kernel integral at `1/ε` — yet it came out to
roughly 700 lines. This file catalogues where the effort went, roughly ordered by how much of the
line count each item is responsible for. Line numbers refer to the state of the file at the time
of writing (commit following `79acb7e`).

## 1. Side-condition discharging — and a correction about `positivity`

An earlier draft of this note claimed "`positivity` does not look at the local context". **That is
false**, and the correction is recorded here in full because the way the misconception arose is
itself a pain point (see "meta-lesson" below).

What `positivity` actually does: besides its extensions, `Mathlib.Meta.Positivity.core` runs
`compareHyp` over every local hypothesis, at *every* level of its structural recursion. It accepts
hypotheses of the form `0 < e`, `0 ≤ e`, `e ≠ 0`, and even `c < e` / `c ≤ e` / `c = e` for a
numeral `c` (it norm_nums the numeral, so `0.6931471803 < Real.log 2` yields positivity of
`Real.log 2`). There are also extensions for `Real.log` of numerals (`0 < Real.log 2` is proved
with no hypotheses at all), `Real.sqrt`, and Bochner integrals (`0 ≤ ∫ t, ‖f t‖` works). All of
the following were verified to be one-word `positivity` proofs, although the file proves them by
hand-built `mul_pos`/`add_nonneg` chains:

- `0 < 6 * Real.log 2 * x` and `6 * Real.log 2 * x ≠ 0` given `0 < x`;
- `0 ≤ √(N·M) + √M·Q + √N·Q + Q²` given `0 ≤ Q` (the `hB'` chains, `Perron.lean:936-939`);
- `0 ≤ ∫ t, P t * K t` for pointwise-nonneg integrands (the `hb`/`hint_nonneg` helpers).

**Meta-lesson (failure attribution under error cascade).** The belief came from two `(by
positivity)` failures that occurred while an *adjacent* `have h1 := by show …; rw [mul_inv,
mul_inv]` was itself failing to elaborate; the positivity errors were artifacts of the broken
surrounding state. The repair replaced both the broken `h1` and the positivity calls with explicit
terms, and the explicit terms got the credit; from then on `positivity` was avoided for anything
hypothesis-dependent, so no contrary evidence was ever collected, and the misdiagnosis nearly
shipped as a "finding". Two tooling notes: (i) diagnostics emitted while a neighbouring
elaboration error is live are unreliable, and proof authors (human or AI) systematically
misattribute them to innocent tactics; (ii) `set_option trace.Tactic.positivity true` exists and
answers "why did positivity fail" — asking it once would have killed the misconception
immediately.

What *does* survive of the original complaint:

- **`simp` cannot use conditional rewrites with positivity side conditions.** Verified:
  `simp [Complex.norm_cpow_eq_rpow_re_of_pos]` does not fire even with `0 < y` literally in
  context (the lemma needs `0 < r`; simp's discharger won't produce it). So every
  `‖(r:ℂ)^s‖ = r^s.re` computation is a 4-line manual rewrite (`norm_T_le`'s `hpow` at
  `Perron.lean:681-686`, and near-identical blocks in `norm_dpoly_le`, `hcoef_sum`,
  `integrable_term`). A simp discharger that calls `positivity` would erase all of them.
- **`nlinarith` can't find products of three hypotheses**
  (`1 ≤ log(x+1) · 6log2 · x` from three lower bounds, `Perron.lean:899-908`). On paper this is
  "clearly ≥ 0.69 · 4.1 · 1". One ends up hand-assembling `mul_le_mul` towers.
- **Decimal-bounded monotone arithmetic over `log`/`exp` atoms** (`log(6 log 2) ≤ 2`,
  `Perron.lean:970-976`) is completely algorithmic — interval arithmetic — and nothing currently
  does it. (`positivity` proves `0 < log 2`, but upper bounds are out of its scope.)

## 2. Measure-theory plumbing that is pure boilerplate

`kernel_integral_le` (`Perron.lean:281`) is the worst offender. The math is four lines; the Lean
is ~130. Specific gaps:

- **Region conversions.** `∫ over Icc` ↔ `∫ over Ioc` ↔ `intervalIntegral` ↔ improper integral
  each have their own lemma (`integral_Icc_eq_integral_Ioc`, `intervalIntegral.integral_of_le`,
  `integral_Iic_eq_integral_Iio`, ...) and you must thread through all of them to use any
  closed-form integral.
- **Reflection/evenness.** There is `integral_comp_abs` for `∫ over ℝ` but no interval version
  (`∫ x in -a..a, f |x| = 2 ∫ x in 0..a, f x` is missing), and no usable `IntegrableOn`-under-
  `x ↦ -x` API. The `Iio (-T)` tail was bounded by smuggling in a globally integrable dominator
  just to avoid proving `IntegrableOn f (Iio (-T))` from the `Ioi T` version
  (`Perron.lean:390-396`). "This function is even" should be one word.
- **Model integrals are rpow-only.** `integral_Ioi_rpow_of_lt` gives `∫ t^(-2:ℝ)`, but the
  integrand you actually have is `(t^2)⁻¹`; converting needed pointwise `EqOn` congruence with
  positivity *twice* (once for `IntegrableOn`, once for the value, `Perron.lean:366-381`), and the
  `rw` initially failed on an un-beta-reduced lambda. A `norm_num`-style extension that evaluates
  `∫ t in Ioi c, t^(-k)` and `∫ t in a..b, (c+t)⁻¹` outright is exactly the kind of thing that
  could be solved algorithmically.
- **Sum–integral swap.** `∑_q ∑_χ ∫ = ∫ ∑∑` plus pulling scalar weights through is
  `integral_finset_sum` + `integral_const_mul` + two layers of `Finset.sum_congr` choreography
  (`Perron.lean:826-833`). The repo already has a `pull summatory` tactic — a
  `pull integral`/`push integral` handling linearity, with integrability side goals sent to a
  discharger, is the obvious analogue.

## 3. `⨆ y ∈ s` over ℝ is the wrong tool for "max over y ≤ x"

Every contact with the iSup cost something:

- `Real.iSup_le` demands a nonnegativity proof of the *bound* (junk-value artifact of
  `sSup ∅ = 0`);
- nested `⨆ y, ⨆ (_ : y ∈ s)` needs two applications;
- `le_ciSup` spawns `BddAbove` side goals that nobody writes on paper — those were precisely the
  three pre-existing sorries in this file, and closing one required a whole auxiliary lemma
  (`norm_T_le_const`, `Perron.lean:628`) just to say "a finite sum of bounded terms is bounded".

And `sup_summatory_eq_sup_nat` — "a step function on `[1,x]` attains its sup at integer sample
points" — is 40 lines for a triviality. Analytic number theory wants a dedicated `MaxOn`-style API
for sups of step/càdlàg functions over compact intervals, with `BddAbove` automatic.

## 4. Missing or awkwardly-shaped Mathlib lemmas

- **Weighted Cauchy–Schwarz** `∑ w·a·b ≤ √(∑ w a²)·√(∑ w b²)`. Only the unweighted squared form
  exists; `Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul` worked (with `r = w·a·b`, `f = w·a²`,
  `g = w·b²`), but then `√(c²·X·Y) = c·√X·√Y` took a `show … by ring` plus four
  `Real.sqrt_mul`/`Real.sqrt_sq` rewrites with side conditions (`Perron.lean:614-621`). A
  `sqrt`-normalizing simp set would help broadly.
- **Finset reindexing along `ℕ ↪ ℤ`** (`Perron.lean:492-512`). `Finset.sum_nbij'` with five side
  goals, plus an elaboration trap: `(j := fun m ↦ (m : ℤ))` silently elaborated as the *identity
  on ℤ* because the domain was still a metavariable. `push_cast`/`zify` don't touch sum index
  types; they should, or there should be `Finset.sum_Ioc_int_eq_natCast`-style lemmas.
- **`Finset.sum_sigma'` is unusable with `rw`** (higher-order pattern `?f x.1 x.2`); only the
  forward `Finset.sum_sigma` works. Worth a docstring warning or a `simp`-friendly restatement.
- `DirichletCharacter.norm_le_one` exists but isn't tagged for `bound`/`gcongr`, so `‖χ m‖ ≤ 1`
  never happens automatically inside a product estimate.

## 5. Statement hygiene under axiom/sorry-driven development

The most alarming findings were in *statements*, which nothing checks:

- The `large_sieve` axiom said `DirichletCharacter ℚ q`. It elaborated without complaint because a
  `ℚ → ℂ` coercion got silently inserted around `χ n` — the source looked right and the axiom was
  useless. A linter flagging unexpected coercions in axioms (or in any statement in a
  `sorry`-free zone) would catch this class of bug.
- `summatory_T_ll` had `√(∑‖g n‖)` (unsquared) and no `log x` factor — both falsifiable by a
  30-second scaling/limit argument (`g ↦ λ·g` makes the LHS grow like `λ` and the RHS like `√λ`)
  that no tool performs. "Does this inequality survive scaling?" is mechanical; a
  `plausible`-style falsifier for asymptotic statements would pay for itself immediately.
- `C_LS` is an opaque axiom constant with no sign information, so every use needed
  `max C_LS 0` laundering. Lesson: axioms asserting `O`-bounds should bundle `0 < C`, or better,
  be phrased so the constant is `Exists.choose`-defined with a positivity lemma — the
  `summatory_T_ll_exists` / `C_LSC` / `C_LSC_pos` pattern is the workable idiom, but it's
  boilerplate that could be a macro (`∃≪`-style).
- A near-miss of the same kind: the axiom's weight `q / φ q` could have elaborated as ℕ-division
  (which would have made it `⌊q/φ(q)⌋ = 1` for most `q`); `binop%` elaboration happened to save
  it, but the difference is invisible at the source level.

## 6. Tooling papercuts

- `gcongr` is powerful but unpredictable: it sometimes discharges side goals via `assumption` (so
  prepared bullets die with "No goals to be solved"), sometimes decomposes deeper than expected
  (`y^σ ≤ (x+1)^σ` straight to `y ≤ x+1`). Each mismatch is an edit–recheck cycle. An option to
  *list* the goals it intends to leave would remove the guesswork.
- `calc` forces restating the full multi-line expression at every step; with the 5-line right-hand
  side here, that's easily a third of the proof text (`Perron.lean:983-1010`). Statement-local
  abbreviations that survive into `calc` (or a `set` that plays better with lemma application)
  would compress this a lot.
- `maxHeartbeats` is per-declaration, so a long-but-trivial assembly proof times out at its *last*
  step for no local reason (the `set_option maxHeartbeats 1000000` at `Perron.lean:872`) —
  confusing signal, and it pressures you into splitting declarations, which multiplies the `calc`
  restatement cost above.
- `rw` with `mul_inv` (and friends) fires on the first matching occurrence, which in expressions
  with several inverses is often the wrong one; rearranging
  `(σε)⁻¹ = log(x+1)·(6 log 2)·x` took several attempts (`Perron.lean:913-915`). (Correction in
  the same spirit as §1: `field_simp` *does* solve this goal directly given the positivity
  hypotheses in context — verified afterwards. It was abandoned during the session for reasons
  that were never actually tested, another instance of the failure-attribution problem.)

## Top three by leverage

1. A `positivity`-calling discharger for `simp` side conditions (and better visibility into *why*
   a tactic failed — `positivity` itself turned out to be much stronger than this file gives it
   credit for; the file's manual nonnegativity chains are mostly unnecessary, see §1).
2. Closed-form evaluation + region-plumbing automation for one-dimensional integrals
   (evaluate `∫ t in Ioi c, t^(-k)`, split at a point, exploit evenness, swap with finite sums).
3. A proper "max over an interval" API for step functions, with `BddAbove` handled invisibly.

Those three would have cut this file by something like half.

## What worked well

For balance: `grw`, `gcongr` and `positivity` carried a lot of weight; PNT+'s
`Smooth1` API (`MellinOfSmooth1a/b`, `Smooth1Properties_below/above`, `Smooth1LeOne`) slotted in
with no friction; and the `∃ C, 0 < C ∧ ∀ …` + `Exists.choose` pattern for implied constants is
verbose but robust — in particular it forces you to notice exactly which parameters the constant
may depend on (here: the bump `ν`, but not `f, g, M, N, x, Q, ε`), which is precisely the
bookkeeping paper proofs get wrong.
