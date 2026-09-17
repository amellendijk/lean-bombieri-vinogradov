# Blueprint style review against the *primegaps* blueprint

Date: 2026-09-17. Reviewed: the blueprint as built on 2026-09-16 (`blueprint/web/`, chapters 1–10,
generated from the `@[blueprint …]` annotations plus `blueprint/src/content.tex`).
Reference: <https://primegaps.axiommath.ai/paper/>, in particular §3.3 “Prime counting and the
level of distribution” (Notation 3.20 – Lemma 3.23) and the neighbouring sections §3.1, §3.4–3.6
that use the same conventions.

This is a review only; nothing in the blueprint was changed.

## 1. What the reference style looks like

Every numbered item in the reference follows the same template:

- **Environment + descriptive title.** `Notation`, `Definition`, `Lemma`, `Theorem`, each with a
  parenthetical title (“Insensitivity to intersecting with the primes”). `Theorem` is reserved for
  the two external inputs and the main results, and is numbered globally (Theorem 1, 2, 3);
  everything else is numbered by section (Lemma 3.22).
- **Fully quantified statement** in ordinary mathematical language: “Let θ ∈ (0,1), let S ⊆ ℕ and
  let Ξ ≥ 1. Then …”. Constants are explicit existential constants (“there is a constant c such
  that, for every real x ≥ 2, … ≤ c x/(log x)^A”), not ≪. External hypotheses are threaded through
  the statements (“Assume Bombieri–Vinogradov (Theorem 1). Then …”).
- **Metadata lines** generated from the formalisation: `Lean: <decl>` (only when a declaration
  exists), `Uses: …` (dependencies of the statement) and, separately, `Proof uses: …`
  (dependencies of the proof). Lists are short and deduplicated.
- **Proofs** are complete and self-contained, cite earlier results only by number
  (“By Definition 3.21”, “Lemma 3.22 applied with S = ℙ”), never by Lean name, and never appeal
  to “standard” facts without naming a numbered result. Longer proofs are split into labelled
  `Step 1: …`, `Step 2: …` paragraphs and track constants to the end (“with c₀ + 2 log 2”).
  External inputs still get a `Proof` block saying they are quoted, with literature citations
  (Bombieri 1965, Vinogradov 1965, Davenport).
- **Narrative.** Every section opens with a short motivating paragraph, and short remarks between
  items explain conventions (“The additive 1 is a convenience: it makes E(N,q) ≥ 1 …”). The
  document has an Introduction with history and the main theorem, and an Overview chapter.
- **No formalisation details in the mathematics.** Type-class generality, Mathlib lemma names,
  `ℝ≥0∞`, `toReal`, etc. never appear in statements or proofs; the only trace of Lean is the
  `Lean:` line.

## 2. Where the blueprint already matches

- Structure: Introduction (with informal main theorem), Overview, Definitions/preliminaries,
  External inputs, Auxiliary estimates, then the argument, then Assembly. This mirrors the
  reference’s chapters 1–3 and 6.
- Every node has a descriptive title, full hypotheses, and cross-references by number (`\Cref`).
- Proof detail is at the reference level for the main results: Theorems 8.18, 9.8, 9.35, 9.39,
  9.40, 9.41 and Lemma 10.5 have labelled paragraphs (“Pointwise bound.”, “Summation.”,
  “Dyadic blocks in d.”) and check the numerics. Elementary lemmas get short but complete
  proofs, as in the reference.
- Edge cases forced by the formalisation are explained in prose (q = 0, r = 0, x < 1, the term
  n = 0), which is exactly how the reference handles floors and empty products.
- Remarks after statements (“The factor τ(r) cannot be dropped …”, “The additive … is a
  convenience” analogues) are present where they matter.
- External inputs are clearly labelled as quoted (“taken as an external input … no proof is
  given here”), matching the reference wording almost verbatim.

## 3. Divergences

Ordered roughly by how visible they are to a reader.

### 3.1 Dependency metadata is noisy

The reference prints one short `Uses:` list for the statement and a separate `Proof uses:` list.
The blueprint prints a single auto-inferred `Uses` list that

- contains many duplicates (Lemma 3.8 lists Definition 3.7 four times and Definitions 3.1/3.2/3.4
  four times each; Theorem 9.32 lists its four definitions four times; Lemma 3.14 lists
  Definition 3.13 twice), because the node merges several Lean declarations;
- mixes statement and proof dependencies (no `Proof uses:`);
- includes incidental dependencies that are invisible in the text: Theorem 10.6, Corollary 10.7,
  Theorem 10.2 and Lemma 10.5 all list “Definition 9.22, Lemma 9.27, Definition 9.13,
  Theorem 9.12” (the bump function machinery) although the statements never mention it, and
  Theorem 9.11 / Lemma 9.10 list Assumption 4.1 although only Theorem 9.9 uses it.

### 3.2 Formalisation details leak into statements and proofs

The reference keeps Lean out of the mathematics entirely. The blueprint mentions it in:

- Statements: Definition 3.1 (“values in an additive commutative monoid R”), Definition 3.4
  (“with R having a zero”), Definitions 3.7/3.10 (“R a field”), Lemma 3.11 and Lemma 8.1
  (“a field 𝕂 equipped with an algebra map 𝕂 → ℂ (in practice 𝕂 = ℝ or ℂ)”), Lemma 9.3
  (“values in an additive commutative monoid”), Definition 3.13 (“In Lean this is the typeclass
  ProofData”), Definition 3.7 (“as is customary in Lean”), §3.1 (“ℕ = {0,1,2,…} (as in Lean)”),
  Lemma 5.3 (“the divisor set of 0 is empty in Lean”), Theorem 10.6 (“In Lean the left-hand side
  is a sum of the extended-real quantities”).
- Proofs citing Mathlib/PNT+ declarations by name instead of a numbered result: Lemma 5.1
  (`Chebyshev.psi_le_const_mul_self`), Lemma 8.3 (`sum_mul_eq_sub_sub_integral_mul`),
  Lemma 9.26 (`mellinInv_mellin_eq`, `Smooth1MellinConvergent`, `Smooth1ContinuousAt`; the last is
  Lemma 9.18 and should be cited as such), Corollary 10.7 (`ENNReal.toReal`), Lemma 3.19
  (“the extended-real absolute value ‖·‖ₑ”).
- Notation: `‖·‖` for complex absolute values in §9.5–9.6 versus `|·|` elsewhere; the reference
  uses `|·|` throughout.

### 3.3 Constants are ≪ rather than explicit

The reference states every bound with a named constant (“there exist C and N₀ such that for
N ≥ N₀ …”) and tracks it through the proof. The blueprint states almost everything with ≪ / O_A
and says once (§1, §3.1) that constants are not tracked. This is a deliberate choice recorded in
the project memory (see `blueprint-no-named-constants`), so it is listed here as a known,
intentional divergence rather than a defect. Two consequences worth noting:

- The convention is not perfectly uniform: some statements do carry explicit numerics
  (Lemma 4.3, Lemma 4.5 with 2^B, Lemma 7.2 with 2U log x, Theorem 7.3 with 2x/(log x)^{A+2},
  Lemmas 8.15–8.17 with 4τ(r)V log x and 6τ(r)), and Lemma 9.25 computes an explicit constant in
  its proof. The reference would either give the constant everywhere or nowhere.
- Dependence of implied constants is stated in §3.1 (“may depend on the two external inputs and
  the bump function”), but a few statements repeat it locally in different words
  (“with an absolute implied constant”, “with the implied constant of Assumption 4.6”, “the
  implied constants depending only on ν”). The reference fixes the convention once in
  Notation 3.2 and then only uses subscripts.

### 3.4 External inputs are not threaded through statements and have no citations

- The reference writes “Assume Bombieri–Vinogradov (Theorem 1)” at the start of every statement
  that depends on it. The blueprint treats Siegel–Walfisz and the large sieve as global axioms
  (`Assumption` environment) and never restates them as hypotheses; only the informal main
  theorem in §1 says “Assume the Siegel–Walfisz theorem and the large sieve inequality”.
- The reference gives literature citations for quoted results (Bombieri 1965, Vinogradov 1965,
  Davenport). The blueprint has no bibliography at all: Koukoulopoulos is named in prose
  (“Theorem 26.6 of Koukoulopoulos”) and Siegel–Walfisz / the large sieve carry no reference.
- The reference gives even a quoted theorem a `Proof` block (“taken as an external input … No
  proof is given here”). The blueprint puts this sentence inside the statement of the
  `Assumption`, so the node has no proof block; the PNT+ inputs (Theorem 9.12, Lemmas 9.14–9.21)
  do have proof blocks reading “Proved in PrimeNumberTheoremAnd.”

### 3.5 Environment and numbering conventions

- The reference uses `Theorem` only for external inputs and main results and numbers them
  globally. The blueprint uses `Theorem` for many intermediate results (4.2, 4.4, 5.2, 5.6, 6.5,
  7.3, 8.5, 8.17, 8.18, 9.6, 9.8, 9.9, 9.11, 9.31, 9.32, 9.34–9.37, 9.39–9.41, 10.2, 10.6) and
  numbers all environments on one per-chapter counter.
- The reference has a numbered `Notation` environment (Notation 3.1, 3.2, 3.20, 3.24, 3.26).
  The blueprint’s §3.1 is an unnumbered prose paragraph, and things the reference would call
  Notation (Definitions 3.16, 3.17, 9.1, 9.2, 10.3) are `Definition`s.
- §9.5 has two unnumbered subsections (“Inputs from the PrimeNumberTheoremAnd library”, “The
  smoothed bilinear sums”), which appear in the table of contents without numbers. The reference
  numbers every heading.

### 3.6 Narrative coverage is uneven

The reference opens every section with a motivating paragraph. The blueprint has good ones for
Chapters 4, 5, 6, 7 and §§8.1, 8.2, 9.2, 9.5, but none for Chapter 3 (as a whole and §§3.2–3.5),
Chapter 8 (top level), Chapter 9 (top level), §§9.1, 9.3, 9.4, 9.6, 9.7, 9.8, and Chapter 10
(Assembly starts directly with Lemma 10.1). Between-item remarks (the reference’s “Throughout the
blueprint, Lemma 3.14 is applied in the following form …”) are rarer in the blueprint and live
inside the statements instead.

### 3.7 Level of detail: a few proofs are terser than the reference would be

Most proofs are at the reference level. Exceptions:

- One-line appeals: Lemma 3.19 (“Immediate from Lemma 3.18”), Lemma 3.18 (“defining properties
  of a supremum”), Lemma 8.12 (“Convolve the identities … using bilinearity”), Lemma 8.13,
  Lemma 9.10, Theorem 9.11 (first line), Theorem 10.2. The reference writes out even trivial
  proofs as two or three full sentences (cf. Lemma 3.22, Lemma 3.31).
- Argument by analogy: Theorem 9.8 bounds the (Λ_{≤U})_q term with “As in Lemma 7.2 (the restricted
  function is still non-negative …)” instead of a stated lemma or a lemma general enough to cover
  the restricted function.
- Appeals to unnamed standard facts: “hyperbola identity” (Theorem 5.6, Lemma 8.1, Lemma 9.30),
  “super-multiplicativity of φ” (Theorem 9.11), “Chebyshev’s elementary bound” (Lemma 5.1),
  “Möbius inversion on the divisors of q” (Lemma 9.5), “Both sides are multiplicative” (Lemmas
  5.4, 5.5). The reference states these as numbered lemmas in its §3.1/§6.1 (e.g. Lemma 3.7
  Möbius divisor-sum identity, Lemma 3.11 Euler product) and cites them.
- Longer proofs use italic paragraph labels (“Pointwise bound.”) rather than the reference’s
  numbered “Step 1:” labels. Minor, but the reference is consistent about it.

### 3.8 Rendering defects

- Overview §2.2: “The three pieces are treated separately (??)” — the multi-target
  `\Cref{ch:small,ch:typeI,ch:typeII}` in `content.tex` does not resolve in the web build.
- Lemma 9.29 exposes a Lean declaration named `Flat.temp` (BV/Flat/Perron.lean:337) in its
  `Lean declarations` list.
- Duplicate `Uses` entries (see §3.1) are a rendering-level artefact of merging several
  declarations into one node.

### 3.9 Minor duplication

- Lemma 7.1 and the second half of Lemma 8.14 state the same bound Σ_{n≤y} Λ_{≤U}(n) ≤ U log x;
  the reference avoids restating a result under a new number.
- Lemma 3.8 (linearity of Δ) and Lemma 3.18 (supremum properties) bundle four Lean declarations
  each into one node; the reference keeps one mathematical fact per node.

### 3.10 Node granularity follows the Lean declarations, not the mathematics

Axiom's blueprint is organised the other way round from ours: its nodes are mathematical units,
and Lean declarations are attached to them many-to-one, sometimes zero-to-one. Ours is generated
from per-declaration `@[blueprint]` attributes, so the node granularity defaults to the Lean
granularity.

| | Axiom (sampled §§3–4, 48 items) | Ours (110 nodes) |
|---|---|---|
| Items with no Lean declaration at all | 15 (e.g. Lemma 3.14 union bound, Lemma 3.22, Lemma 3.31 “W is squarefree”, Theorem 2 PNT) | 0 by construction; the 10 PNT+ inputs (hand-written in `content.tex`) are the only informal nodes |
| Items listing 2 or 3 declarations | 11 (Lemma 3.12 and 3.13 list three Mathlib lemmas each) | about 20 |
| Lean lemmas in the library | unknown, but many helper lemmas never surface in the text | 339 `theorem`/`lemma` declarations in `BV/`, of which 138 are attached to nodes |

So the coupling is not one of coverage (about 60 % of our Lean lemmas already have no node) but
of shape: the nodes that exist are cut where Lean needed a separate statement, not where a reader
needs a separate step. The naming direction in the reference is telling: declarations are called
`lem_BV_restated`, `lem_W_size`, `lem_admissible_cardinality_char`, i.e. the LaTeX label came first
and the Lean was written to match it.

Clearest cases of Lean-shaped granularity in our blueprint:

- Lemma 9.29, Lemma 9.30, Theorem 9.31, Theorem 9.32: four nodes for “reduce the maximum to
  half-integers, then write the sharp sum as a Mellin integral”. Mathematically one lemma with a
  two-paragraph proof.
- Lemma 8.12 and Lemma 8.13: each a single sentence applying the previous result.
- Lemma 3.18 and Lemma 3.19: supremum bookkeeping that the reference would put in a Notation block.
- Lemma 9.10 / Theorem 9.11 and Lemma 9.33 / Theorem 9.34: pairs where the first is the pointwise
  form and the second sums it.
- Lemma 7.1 and Lemma 8.14 (already noted in §3.9): the same bound under two numbers because two
  files needed it.

This is also the source of the noisy `Uses` lists in §3.1: merging declarations under one label
concatenates their inferred dependencies without deduplication.

What the LeanArchitect mechanism allows: same-label merging already gives many-to-one nodes, so
the glue chains above can be collapsed without touching any Lean proof, at the cost of writing the
merged node's statement and proof as one mathematical step rather than mirroring each declaration.
What it cannot do is a node with no declaration; those must be written by hand in `content.tex`,
as was done for the PNT+ inputs. Moving to the reference style therefore means (i) one label per
chain of glue lemmas, (ii) hand-written informal nodes for steps a reader wants to see but Lean
inlines or takes from Mathlib (hyperbola identity, super-multiplicativity of φ, Möbius inversion on
divisors), and (iii) accepting a coarser dependency graph, which is what the reference's looks like.

## 4. Summary table

| Aspect | Reference (primegaps §3.3 etc.) | This blueprint | Match? |
|---|---|---|---|
| Titles on every item | yes | yes | ✓ |
| Full hypotheses in statements | yes | yes | ✓ |
| Cross-references by number | yes | yes (one broken `??`) | ✓ |
| Proof completeness (main results) | step-labelled, constant-tracking | paragraph-labelled, ≪ | ≈ |
| Proof completeness (elementary lemmas) | 2–3 full sentences | sometimes one line / “immediate” | ≈ |
| Constants | explicit c, N₀ | ≪ / O_A, deliberately | ✗ (intentional) |
| External inputs as hypotheses | “Assume BV (Theorem 1)” everywhere | global axioms, not restated | ✗ |
| Literature citations | yes | none | ✗ |
| `Uses` / `Proof uses` | two clean lists | one noisy list with duplicates | ✗ |
| Lean names in prose | never | Mathlib/PNT+ names in 5 proofs, type-class generality in ~10 statements | ✗ |
| `Theorem` reserved for main results | yes, global numbering | used for ~25 intermediate results | ✗ |
| `Notation` environment | yes, numbered | unnumbered prose | ✗ |
| Section intro paragraphs | every section | about half the sections | ≈ |
| Numbered headings throughout | yes | two `\subsection*` in §9.5 | ≈ |
| Node granularity | mathematical steps; Lean attached many-to-one or not at all | one node per Lean declaration by default; ~20 merged nodes | ✗ |
