import Mathlib


/-!

# Locally Bounded Functions

This file develops the theory of locally bounded functions, and relates it to local integrability.

In particular:
 * A measurable locally bounded function is locally integrable.

TODO:
 * Relate to Continuous / ContinuousOn  (and ContinuousAt for BoundedAtFilter)

-/


/-
Conversation with claude opus 4.7:

I'm trying to find the right level of generality for some
  mathematical API. I've defined this notion of IsLocallyBounded using
   Filter.BoundedAtFilter, but I don't think this will work very well
  with division. In this case I need the function I'm dividing by to
  locally stay away from 0. Perhaps th right thing to do here is to
  generalize BoundedAtFilter to some predicate AwayFromFilterAtFilter
  f l1 l2 saying that f "stays away from" l1 near l2. Does this sound
  right? And how would you say that in the language of filters?

● Yes, this is a sensible direction. The clean filter-theoretic
  phrasing is disjointness of the pushforward:

  def IsAwayFromAtFilter (l₁ : Filter β) (l₂ : Filter α) (f : α → β) :
  Prop :=
    Disjoint (Filter.map f l₂) l₁

  Read: "along l₂, f eventually avoids l₁." For your division use-case
  you'd take l₁ = 𝓝 0 (in a T1/normed setting), and it unfolds to the
  familiar "∃ ε > 0, ∀ᶠ x in l₂, ε ≤ ‖f x‖" — exactly what makes 1/f
  well-behaved.

  This is the natural dual of BoundedAtFilter f l := f =O[l] (1 : α →
  β), which itself is essentially Tendsto f l (cobounded β) — i.e., a
  pushforward condition. Yours is Disjoint (map f l₂) l₁ instead of map
   f l₂ ≤ l₁. The tradeoff: a bespoke IsAwayFromAtFilter predicate is
  more discoverable and gets its own API (mul, comp, etc.), but you
  could also just use Disjoint (map f l) (𝓝 0) inline and skip the
  abstraction until you have ≥3 call sites that want it. Given you're
  already wrapping BoundedAtFilter in IsLocallyBounded, a parallel
  IsLocallyAwayFromZero (specializing l₁ := 𝓝 0) is probably the sweet
  spot — full generality in l₁ rarely pays off.

❯ No I think it should be its own predicate - we'd generalize
  islocallybounded to eat a filter for the codomain, and that way we
  can hopefully let fun_prop do most of the work proving it.

  Read 1 file (ctrl+o to expand)

● Looking at the current shape — IsLocallyBounded f := ∀ x,
  BoundedAtFilter (𝓝 x) f — the natural generalization is to Disjoint,
  since BoundedAtFilter l f is exactly Disjoint (map f l) (cobounded β)
   once you unfold it (bounded = doesn't escape to infinity =
  pushforward disjoint from cobounded).

  So the unifying predicate:

  def IsLocallyDisjoint {α β : Type*} [TopologicalSpace α] (l : Filter
  β) (f : α → β) : Prop :=
    ∀ x, Disjoint (Filter.map f (𝓝 x)) l

  with the existing notion recovered as IsLocallyBounded f :=
  IsLocallyDisjoint (Bornology.cobounded β) f and "locally away from 0"
   as IsLocallyDisjoint (𝓝 0) f. Set-version: replace 𝓝 x with 𝓝[s] x.
  (Bonus: IsLocallyDisjoint (𝓝 a) gives "locally avoids a" for free,
  e.g. for log/Gamma near singularities.)

  For the fun_prop story this is genuinely nice because the combinators
   split cleanly:

  - Closed under composition with continuous maps on the source —
  always: if g is continuous at x, map (f ∘ g) (𝓝 x) ≤ map f (𝓝 (g x)),
   and disjointness is monotone.
  - Closed under target maps that send l somewhere disjoint — e.g. add,
   mul, neg are lemmas about how cobounded/𝓝 0 interact with the
  algebraic ops on β. The mul case for "away from 0" is exactly
  Filter.Tendsto.mul plus the fact that 𝓝 0 * 𝓝 0 ≤ 𝓝 0; for cobounded
  it's the corresponding cobounded-vs-cobounded fact.

  The one wrinkle: you currently get BoundedAtFilter.add/mul etc. for
  free from Asymptotics. After generalizing you'll need to re-prove the
   boundedness combinators in the Disjoint-of-pushforward form (or just
   bridge via a single iff lemma IsLocallyBounded f ↔ IsLocallyDisjoint
   (cobounded β) f and keep the old API on top). I'd recommend the
  bridge — keeps the Mathlib-facing surface unchanged, and lets
  fun_prop use whichever form has the better lemma at hand.


❯  Hmmm... What would the algebraic combinator lemmas actually look
  like? I'd assume we would have separate lemmas for cobounded/ nhds /
   nhdsWithin?

● Good question — and the answer splits along two independent axes:

  Source filter (𝓝 vs 𝓝[s]): doesn't affect the content of the
  algebraic lemmas, only the boilerplate. You'd get IsLocallyDisjoint
  and IsLocallyDisjointOn versions of each combinator with identical
  proofs modulo 𝓝 x ↦ 𝓝[s] x. (Same situation you already have.)

  Target filter (cobounded vs 𝓝 0 vs 𝓝 a vs …): this is where the
  lemmas genuinely differ, because each algebraic op interacts
  differently with each filter. There is no single
  IsLocallyDisjoint.add — the hypothesis on l needed for add to be
  closed depends on l. Concretely:

  ┌────────┬─────────────┬──────────────────────┬─────────────────┐
  │   op   │ cobounded β │  𝓝 0 (away from 0)   │ 𝓝 a (away from  │
  │        │             │                      │       a)        │
  ├────────┼─────────────┼──────────────────────┼─────────────────┤
  │ add    │ ✓           │ ✗ (1 + (−1) = 0)     │ only with extra │
  │        │             │                      │  hyp            │
  ├────────┼─────────────┼──────────────────────┼─────────────────┤
  │ neg    │ ✓           │ ✓                    │ becomes "away   │
  │        │             │                      │ from −a"        │
  ├────────┼─────────────┼──────────────────────┼─────────────────┤
  │ mul    │ ✓           │ ✓ (in a normed       │ n/a             │
  │        │             │ division ring)       │                 │
  ├────────┼─────────────┼──────────────────────┼─────────────────┤
  │ const  │ always      │ iff c ≠ 0            │ iff c ≠ a       │
  │ c      │             │                      │                 │
  ├────────┼─────────────┼──────────────────────┼─────────────────┤
  │ inv    │ swaps with  │ swaps with cobounded │ —               │
  │        │ 𝓝 0         │                      │                 │
  └────────┴─────────────┴──────────────────────┴─────────────────┘

  So the API ends up looking like:

  -- general source-side composition (works for any l)
  @[fun_prop]
  theorem IsLocallyDisjoint.comp_continuous {l : Filter β} {f : α → β}
  {g : γ → α}
      (hf : IsLocallyDisjoint l f) (hg : Continuous g) :
      IsLocallyDisjoint l (f ∘ g)

  -- target-specific algebraic lemmas — separate per filter
  @[fun_prop]
  theorem IsLocallyBounded.add ...                  -- l = cobounded
  @[fun_prop]
  theorem IsLocallyAwayFromZero.mul ...             -- l = 𝓝 0
  @[fun_prop]
  theorem IsLocallyAwayFromZero.inv_isLocallyBounded ... -- bridges 𝓝 0
   ↔ cobounded under inv

  The pattern I'd suggest: keep IsLocallyDisjoint as the primitive
  (carries the source-side composition lemmas, the On ↔ non-On bridge,
  the locally-integrable consequence in the boundedness
  specialization), and then introduce thin abbrevs or defs
  IsLocallyBounded := IsLocallyDisjoint (cobounded _) and
  IsLocallyAwayFrom a := IsLocallyDisjoint (𝓝 a) that carry their own
  algebraic combinator API. That way fun_prop sees a specialized,
  well-tagged predicate per use case (which it handles much better than
   a predicate parametrized over an arbitrary l), but you don't
  duplicate the source-side machinery.

  Practically: you wrote each IsLocallyBounded.{add,neg,mul,smul} lemma
   once and IsLocallyBoundedOn.* once. Adding "away from 0" doubles
  that — six new lemmas, mirroring the existing six, plus a couple of
  inv/bridge lemmas tying the two together. That's the real cost.
-/

open MeasureTheory

theorem MeasureTheory.IntegrableAtFilter.mul_boundedAtFilter {α : Type u_1} {ε' : Type u_4}
    {mα : MeasurableSpace α} {μ : Measure α} [NormedRing ε']
    {l : Filter α} (hl : l.IsMeasurablyGenerated) {f g : α → ε'} (hg_meas : AEStronglyMeasurable g μ)
    (hf : IntegrableAtFilter f l μ) (hg : l.BoundedAtFilter g) :
    IntegrableAtFilter (f * g) l μ := by
  obtain ⟨s, hsl, hs⟩ := hf
  obtain ⟨s', hs'l, hs'_meas, hs'⟩ := hl.exists_measurable_subset hsl
  obtain ⟨c, hc_pos, hc⟩ := hg.exists_pos
  rw [Asymptotics.IsBigOWith, Filter.Eventually] at hc
  simp only [Pi.one_apply, one_mem, CStarRing.norm_of_mem_unitary, mul_one] at hc
  obtain ⟨t, htl, ht_meas, ht⟩ := hl.exists_measurable_subset hc
  use s' ∩ t
  simp only [Filter.inter_mem_iff, hs'l, htl, and_self, true_and]
  rw [← MeasureTheory.integrable_indicator_iff (by measurability),
    show f * g = fun n ↦ f n * g n by rfl, Set.indicator_mul]
  apply Integrable.mul_bdd (c := c)
  · rw [integrable_indicator_iff (by measurability)]
    apply hs.mono_set
    grind
  · fun_prop (disch := measurability)
  · filter_upwards with x
    by_cases hx : x ∈ s' ∩ t
    · simp [hx]
      exact ht (Set.mem_of_mem_inter_right hx)
    · simp [hx]
      grind

-- TODO: Figure out how to not repeat the previous proof
theorem MeasureTheory.IntegrableAtFilter.boundedAtFilter_mul {α : Type u_1} {ε' : Type u_4}
    {mα : MeasurableSpace α} {μ : Measure α} [NormedRing ε']
    {l : Filter α} (hl : l.IsMeasurablyGenerated) {f g : α → ε'} (hg_meas : AEStronglyMeasurable g μ)
    (hf : IntegrableAtFilter f l μ) (hg : l.BoundedAtFilter g) :
    IntegrableAtFilter (g * f) l μ := by
  obtain ⟨s, hsl, hs⟩ := hf
  obtain ⟨s', hs'l, hs'_meas, hs'⟩ := hl.exists_measurable_subset hsl
  obtain ⟨c, hc_pos, hc⟩ := hg.exists_pos
  rw [Asymptotics.IsBigOWith, Filter.Eventually] at hc
  simp only [Pi.one_apply, one_mem, CStarRing.norm_of_mem_unitary, mul_one] at hc
  obtain ⟨t, htl, ht_meas, ht⟩ := hl.exists_measurable_subset hc
  use s' ∩ t
  simp only [Filter.inter_mem_iff, hs'l, htl, and_self, true_and]
  rw [← MeasureTheory.integrable_indicator_iff (by measurability),
    show g * f = fun n ↦ g n * f n by rfl, Set.indicator_mul]
  apply Integrable.bdd_mul (c := c)
  · rw [integrable_indicator_iff (by measurability)]
    apply hs.mono_set
    grind
  · fun_prop (disch := measurability)
  · filter_upwards with x
    by_cases hx : x ∈ s' ∩ t
    · simp [hx]
      exact ht (Set.mem_of_mem_inter_right hx)
    · simp [hx]
      grind

theorem Filter.BoundedAtFilter.integrableAtFilter {α β : Type*}
    [TopologicalSpace α] [MeasurableSpace α] [NormedAddCommGroup β]
    {μ : Measure α} {f : α → β} {l : Filter α}
    (hl : l.IsMeasurablyGenerated) (hμ : μ.FiniteAtFilter l) (hf : l.BoundedAtFilter f)
    (hf_meas : StronglyMeasurableAtFilter f l μ) :
    IntegrableAtFilter f l μ := by
  rw [BoundedAtFilter] at hf
  apply hf.integrableAtFilter
  · exact hf_meas
  · apply Filter.Tendsto.integrableAtFilter (b := 1)
    · apply tendsto_const_nhds
    · apply (Measurable.stronglyMeasurable _).stronglyMeasurableAtFilter
      fun_prop
    · exact hμ

theorem Filter.BoundedAtFilter.integrableAtFilter_nhds {α β : Type*}
    [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α] [NormedAddCommGroup β]
    {μ : Measure α} [IsLocallyFiniteMeasure μ] {f : α → β} (a : α)
    (hf : (nhds a).BoundedAtFilter f)
    (hf_meas : StronglyMeasurableAtFilter f (nhds a) μ) :
    IntegrableAtFilter f (nhds a) μ :=
  Filter.BoundedAtFilter.integrableAtFilter (nhds_isMeasurablyGenerated _) (μ.finiteAt_nhds _) hf hf_meas

theorem Filter.BoundedAtFilter.integrableAtFilter_nhdsWithin {α β : Type*}
    [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α] [NormedAddCommGroup β]
    {μ : Measure α} [IsLocallyFiniteMeasure μ] {f : α → β} {s : Set α} (hs : MeasurableSet s) {a : α}
    (hf : (nhdsWithin a s).BoundedAtFilter f)
    (hf_meas : StronglyMeasurableAtFilter f (nhdsWithin a s) μ) :
    IntegrableAtFilter f (nhdsWithin a s) μ :=
  Filter.BoundedAtFilter.integrableAtFilter (hs.nhdsWithin_isMeasurablyGenerated _) (μ.finiteAt_nhdsWithin _ _) hf hf_meas

-- Potential quibble: It might be helpful to say that e.g. s : ℝ → Finset ℕ is locally bounded, which in this case requires a Norm instance on Finset.
@[fun_prop]
structure IsLocallyBounded {α β : Type*} [TopologicalSpace α] [Norm β] (f : α → β) where
  locally_bdd' : ∀ x, (nhds x).BoundedAtFilter f

theorem IsLocallyBounded.boundedAtFilter {α β : Type*} [TopologicalSpace α] [Norm β] {f : α → β}
    (hf : IsLocallyBounded f) (x : α) : (nhds x).BoundedAtFilter f := hf.locally_bdd' x

theorem IsLocallyBounded.locallyIntegrable {α β : Type*}
    [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α] [NormedAddCommGroup β]
    (μ : Measure α) [IsLocallyFiniteMeasure μ] (f : α → β) (hf_bdd : IsLocallyBounded f)
    (hf_meas : AEStronglyMeasurable f μ) :
    LocallyIntegrable f μ := fun _ ↦
  Filter.BoundedAtFilter.integrableAtFilter_nhds _ (hf_bdd.boundedAtFilter _) hf_meas.stronglyMeasurableAtFilter

theorem MeasureTheory.LocallyIntegrable.mul_isLocallyBounded
    {X R : Type*} [MeasurableSpace X] [TopologicalSpace X] {μ : Measure X} [OpensMeasurableSpace X]
    [LocallyCompactSpace X] [T2Space X] [NormedRing R]
    [SecondCountableTopologyEither X R] {f g : X → R} (hf : LocallyIntegrable f μ)
    (hg : IsLocallyBounded g) (hg_meas : AEStronglyMeasurable g μ) :
    LocallyIntegrable (fun x => f x * g x) μ := fun x ↦
  (hf x).mul_boundedAtFilter (nhds_isMeasurablyGenerated _) hg_meas (hg.locally_bdd' x)

theorem MeasureTheory.LocallyIntegrable.isLocallyBounded_mul
    {X R : Type*} [MeasurableSpace X] [TopologicalSpace X] {μ : Measure X} [OpensMeasurableSpace X]
    [LocallyCompactSpace X] [T2Space X] [NormedRing R]
    [SecondCountableTopologyEither X R] {f g : X → R} (hf : LocallyIntegrable f μ)
    (hg : IsLocallyBounded g) (hg_meas : AEStronglyMeasurable g μ) :
    LocallyIntegrable (fun x => g x * f x) μ := fun x ↦
  (hf x).boundedAtFilter_mul (nhds_isMeasurablyGenerated _) hg_meas (hg.locally_bdd' x)

section Combinators
variable {α β : Type*}

@[fun_prop]
theorem const_isLocallyBounded [TopologicalSpace α] [SeminormedAddCommGroup β] (c : β) :
    IsLocallyBounded (fun (_ : α) ↦ c) :=
  ⟨fun _ ↦ Filter.const_boundedAtFilter _ c⟩

@[fun_prop]
theorem IsLocallyBounded.add [TopologicalSpace α] [SeminormedAddCommGroup β] {f g : α → β}
    (hf : IsLocallyBounded f) (hg : IsLocallyBounded g) :
    IsLocallyBounded (fun x ↦ f x + g x) :=
  ⟨fun _ ↦ (hf.boundedAtFilter _).add (hg.boundedAtFilter _)⟩

@[fun_prop]
theorem IsLocallyBounded.sub [TopologicalSpace α] [SeminormedAddCommGroup β] {f g : α → β}
    (hf : IsLocallyBounded f) (hg : IsLocallyBounded g) :
    IsLocallyBounded (fun x ↦ f x - g x) :=
  ⟨fun _ ↦ (hf.boundedAtFilter _).sub (hg.boundedAtFilter _)⟩

@[fun_prop]
theorem IsLocallyBounded.neg [TopologicalSpace α] [SeminormedAddCommGroup β] {f : α → β}
    (hf : IsLocallyBounded f) :
    IsLocallyBounded (fun x ↦ - f x) :=
  ⟨fun _ ↦ (hf.boundedAtFilter _).neg⟩

@[fun_prop]
theorem IsLocallyBounded.smul
    {𝕜 : Type*} [TopologicalSpace α] [SeminormedRing 𝕜] [SeminormedAddCommGroup β] [Module 𝕜 β]
    [IsBoundedSMul 𝕜 β] {f : α → β} (c : 𝕜)
    (hf : IsLocallyBounded f) : IsLocallyBounded (fun x ↦ c • f x) :=
  ⟨fun _ ↦ (hf.boundedAtFilter _).smul _⟩

@[fun_prop]
theorem IsLocallyBounded.mul [TopologicalSpace α] [SeminormedRing β] {f g : α → β}
    (hf : IsLocallyBounded f) (hg : IsLocallyBounded g) :
    IsLocallyBounded (fun x ↦ f x * g x) :=
  ⟨fun _ ↦ (hf.boundedAtFilter _).mul (hg.boundedAtFilter _)⟩

/- Added by Claude -/
@[fun_prop]
theorem IsLocallyBounded.norm [TopologicalSpace α] [SeminormedAddCommGroup β] {f : α → β}
    (hf : IsLocallyBounded f) :
    IsLocallyBounded (fun x ↦ ‖f x‖) :=
  ⟨fun _ ↦ Asymptotics.isBigO_norm_left.mpr (hf.boundedAtFilter _)⟩

end Combinators


section On

@[fun_prop]
structure IsLocallyBoundedOn {α β : Type*} [TopologicalSpace α] [Norm β] (f : α → β) (s : Set α) where
  locally_bddOn' : ∀ x ∈ s, (nhdsWithin x s).BoundedAtFilter f

/- The API (only the statements) for IsLocallyBoundedOn was generalized from IsLocallyBounded using Claude Sonnet 4.6-/

theorem IsLocallyBoundedOn.boundedAtFilter {α β : Type*} [TopologicalSpace α] [Norm β] {f : α → β}
    {s : Set α} (hf : IsLocallyBoundedOn f s) {x : α} (hx : x ∈ s) :
    (nhdsWithin x s).BoundedAtFilter f := hf.locally_bddOn' x hx

theorem IsLocallyBoundedOn.locallyIntegrableOn {α β : Type*}
    [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α] [NormedAddCommGroup β]
    {μ : Measure α} [IsLocallyFiniteMeasure μ] {f : α → β} {s : Set α} (hs : MeasurableSet s)
    (hf_bdd : IsLocallyBoundedOn f s) (hf_meas : AEStronglyMeasurable f μ) :
    LocallyIntegrableOn f s μ := fun _ ha ↦
  Filter.BoundedAtFilter.integrableAtFilter_nhdsWithin hs (hf_bdd.boundedAtFilter ha) hf_meas.stronglyMeasurableAtFilter

theorem MeasureTheory.LocallyIntegrableOn.mul_isLocallyBoundedOn
    {X R : Type*} [MeasurableSpace X] [TopologicalSpace X] {μ : Measure X} [OpensMeasurableSpace X]
    [LocallyCompactSpace X] [T2Space X] [NormedRing R]
    [SecondCountableTopologyEither X R] {f g : X → R} {s : Set X} (hs : MeasurableSet s)
    (hf : LocallyIntegrableOn f s μ) (hg : IsLocallyBoundedOn g s)
    (hg_meas : AEStronglyMeasurable g μ) :
    LocallyIntegrableOn (fun x => f x * g x) s μ := fun x hx ↦
  (hf x hx).mul_boundedAtFilter (hs.nhdsWithin_isMeasurablyGenerated _) hg_meas (hg.locally_bddOn' x hx)

theorem MeasureTheory.LocallyIntegrableOn.isLocallyBoundedOn_mul
    {X R : Type*} [MeasurableSpace X] [TopologicalSpace X] {μ : Measure X} [OpensMeasurableSpace X]
    [LocallyCompactSpace X] [T2Space X] [NormedRing R]
    [SecondCountableTopologyEither X R] {f g : X → R} {s : Set X} (hs : MeasurableSet s)
    (hf : LocallyIntegrableOn f s μ) (hg : IsLocallyBoundedOn g s)
    (hg_meas : AEStronglyMeasurable g μ) :
    LocallyIntegrableOn (fun x => g x * f x) s μ := fun x hx ↦
  (hf x hx).boundedAtFilter_mul (hs.nhdsWithin_isMeasurablyGenerated _) hg_meas (hg.locally_bddOn' x hx)

section OnCombinators
variable {α β : Type*}

@[fun_prop]
theorem const_isLocallyBoundedOn [TopologicalSpace α] [SeminormedAddCommGroup β] (c : β)
    (s : Set α) : IsLocallyBoundedOn (fun (_ : α) ↦ c) s :=
  ⟨fun _ _ ↦ Filter.const_boundedAtFilter _ c⟩

@[fun_prop]
theorem IsLocallyBoundedOn.add [TopologicalSpace α] [SeminormedAddCommGroup β] {f g : α → β}
    {s : Set α} (hf : IsLocallyBoundedOn f s) (hg : IsLocallyBoundedOn g s) :
    IsLocallyBoundedOn (fun x ↦ f x + g x) s :=
  ⟨fun _ hx ↦ (hf.boundedAtFilter hx).add (hg.boundedAtFilter hx)⟩

@[fun_prop]
theorem IsLocallyBoundedOn.sub [TopologicalSpace α] [SeminormedAddCommGroup β] {f g : α → β}
    {s : Set α} (hf : IsLocallyBoundedOn f s) (hg : IsLocallyBoundedOn g s) :
    IsLocallyBoundedOn (fun x ↦ f x - g x) s :=
  ⟨fun _ hx ↦ (hf.boundedAtFilter hx).sub (hg.boundedAtFilter hx)⟩

@[fun_prop]
theorem IsLocallyBoundedOn.neg [TopologicalSpace α] [SeminormedAddCommGroup β] {f : α → β}
    {s : Set α} (hf : IsLocallyBoundedOn f s) :
    IsLocallyBoundedOn (fun x ↦ -f x) s :=
  ⟨fun _ hx ↦ (hf.boundedAtFilter hx).neg⟩

@[fun_prop]
theorem IsLocallyBoundedOn.smul
    {𝕜 : Type*} [TopologicalSpace α] [SeminormedRing 𝕜] [SeminormedAddCommGroup β] [Module 𝕜 β]
    [IsBoundedSMul 𝕜 β] {f : α → β} {s : Set α} (c : 𝕜)
    (hf : IsLocallyBoundedOn f s) : IsLocallyBoundedOn (fun x ↦ c • f x) s :=
  ⟨fun _ hx ↦ (hf.boundedAtFilter hx).smul _⟩

@[fun_prop]
theorem IsLocallyBoundedOn.mul [TopologicalSpace α] [SeminormedRing β] {f g : α → β} {s : Set α}
    (hf : IsLocallyBoundedOn f s) (hg : IsLocallyBoundedOn g s) :
    IsLocallyBoundedOn (fun x ↦ f x * g x) s :=
  ⟨fun _ hx ↦ (hf.boundedAtFilter hx).mul (hg.boundedAtFilter hx)⟩

/- Added by Claude -/
@[fun_prop]
theorem IsLocallyBoundedOn.norm [TopologicalSpace α] [SeminormedAddCommGroup β] {f : α → β}
    {s : Set α} (hf : IsLocallyBoundedOn f s) :
    IsLocallyBoundedOn (fun x ↦ ‖f x‖) s :=
  ⟨fun _ hx ↦ Asymptotics.isBigO_norm_left.mpr (hf.boundedAtFilter hx)⟩

end OnCombinators

end On

@[fun_prop]
theorem IsLocallyBounded.isLocallyBoundedOn {α β : Type*} [TopologicalSpace α] [Norm β] {f : α → β} (s : Set α)
    (hf : IsLocallyBounded f) : IsLocallyBoundedOn f s :=
  ⟨fun a _ ↦ (hf.locally_bdd' a).mono nhdsWithin_le_nhds⟩


-- @[fun_prop]
-- theorem Continuous.isLocallyBoundedOn {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] [Norm β]
--     [ContinuousENorm β] {f : α → β} (hf : Continuous f) :
--     IsLocallyBounded f := by
--   sorry
