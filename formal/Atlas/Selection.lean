import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Finite-family report selection

This file proves the measure-theoretic union/selection layer of corrected
Theorem 5.2. Individual tail bounds are explicit inputs supplied by the
estimation layer. No independence between reports is assumed. The candidate
index type is fixed and finite; a data-chosen singleton is not a substitute.
The bounds control joint failure with an emitted link, not conditional failure
given that a link is emitted.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Atlas.Selection

variable {Ω R : Type*}

/-- Arbitrary data-dependent selection cannot fail unless some candidate fails. -/
theorem selected_failure_subset (failure : R → Set Ω) (select : Ω → R)
    (emit : Set Ω) :
    {ω | ω ∈ emit ∧ ω ∈ failure (select ω)} ⊆ ⋃ r, failure r :=
  fun ω h ↦ Set.mem_iUnion.mpr ⟨select ω, h.2⟩

/-- On the common certificate event, a missed interval entails a tail event. -/
theorem family_failure_subset (failure tail : R → Set Ω) (cert : Set Ω)
    (hvalid : ∀ r, failure r ∩ cert ⊆ tail r) :
    (⋃ r, failure r) ⊆ (⋃ r, tail r) ∪ certᶜ :=
  fun ω h ↦ (Set.mem_iUnion.mp h).elim fun r hr ↦
    (Classical.em (ω ∈ cert)).elim
      (fun hc ↦ Or.inl (Set.mem_iUnion.mpr ⟨r, hvalid r ⟨hr, hc⟩⟩))
      (fun hc ↦ Or.inr hc)

/-- Disjoint intervals for a common target imply at least one failed interval. -/
theorem conflict_subset_failure {T : Type*} (I : R → Ω → Set T) (target : T) :
    {ω | ∃ r s, Disjoint (I r ω) (I s ω)} ⊆
      ⋃ r, {ω | target ∉ I r ω} :=
  fun ω ⟨r, s, hdis⟩ ↦
    (Classical.em (target ∈ I r ω)).elim
      (fun hr ↦ Set.mem_iUnion.mpr
        ⟨s, fun hs ↦ Set.disjoint_left.mp hdis hr hs⟩)
      (fun hr ↦ Set.mem_iUnion.mpr ⟨r, hr⟩)

variable [MeasurableSpace Ω]

/-- Corrected Theorem 5.2: simultaneous validity on a fixed finite family.
This stronger outer-measure formulation does not require the events measurable. -/
theorem family_failure_le [Fintype R] (μ : Measure Ω)
    (failure tail : R → Set Ω) (cert : Set Ω)
    (budget : R → ℝ≥0∞) (α ρ : ℝ≥0∞)
    (hvalid : ∀ r, failure r ∩ cert ⊆ tail r)
    (htail : ∀ r, μ (tail r) ≤ budget r)
    (hbudget : ∑ r, budget r ≤ α) (hcert : μ certᶜ ≤ ρ) :
    μ (⋃ r, failure r) ≤ α + ρ :=
  calc
    μ (⋃ r, failure r) ≤ μ ((⋃ r, tail r) ∪ certᶜ) :=
      measure_mono (family_failure_subset failure tail cert hvalid)
    _ ≤ μ (⋃ r, tail r) + μ certᶜ := measure_union_le _ _
    _ ≤ α + ρ := add_le_add
      ((measure_iUnion_fintype_le μ tail).trans
        ((Finset.sum_le_sum (fun r _ ↦ htail r)).trans hbudget)) hcert

/-- The selected report and its label may depend on all observed data. -/
theorem selected_failure_le [Fintype R] (μ : Measure Ω)
    (failure tail : R → Set Ω) (cert emit : Set Ω) (select : Ω → R)
    (budget : R → ℝ≥0∞) (α ρ : ℝ≥0∞)
    (hvalid : ∀ r, failure r ∩ cert ⊆ tail r)
    (htail : ∀ r, μ (tail r) ≤ budget r)
    (hbudget : ∑ r, budget r ≤ α) (hcert : μ certᶜ ≤ ρ) :
    μ {ω | ω ∈ emit ∧ ω ∈ failure (select ω)} ≤ α + ρ :=
  (measure_mono (selected_failure_subset failure select emit)).trans
    (family_failure_le μ failure tail cert budget α ρ hvalid htail hbudget hcert)

/-- Under the common-target null, a reconcile/conflict flag is a familywise
error-controlled rejection of the joint model, not a resolved disagreement. -/
theorem conflict_probability_le [Fintype R] {T : Type*} (μ : Measure Ω)
    (I : R → Ω → Set T) (target : T) (tail : R → Set Ω) (cert : Set Ω)
    (budget : R → ℝ≥0∞) (α ρ : ℝ≥0∞)
    (hvalid : ∀ r, {ω | target ∉ I r ω} ∩ cert ⊆ tail r)
    (htail : ∀ r, μ (tail r) ≤ budget r)
    (hbudget : ∑ r, budget r ≤ α) (hcert : μ certᶜ ≤ ρ) :
    μ {ω | ∃ r s, Disjoint (I r ω) (I s ω)} ≤ α + ρ :=
  (measure_mono (conflict_subset_failure I target)).trans
    (family_failure_le μ (fun r ↦ {ω | target ∉ I r ω})
      tail cert budget α ρ hvalid htail hbudget hcert)

/-- Translate the failure bound into simultaneous coverage for probability measures. -/
theorem simultaneous_coverage (μ : Measure Ω) [IsProbabilityMeasure μ]
    (failure : Set Ω) (a : ℝ≥0∞) (hmeas : MeasurableSet failure)
    (hbound : μ failure ≤ a) : 1 - a ≤ μ failureᶜ :=
  calc
    1 - a ≤ 1 - μ failure := tsub_le_tsub_left hbound 1
    _ = μ failureᶜ := (prob_compl_eq_one_sub hmeas).symm

end Atlas.Selection
