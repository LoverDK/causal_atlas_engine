import Atlas.Estimation
import Atlas.Algebra
import Atlas.Selection
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace Atlas.Confidence
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Exact calibration of the Chernoff radius, with a positive MGF proxy. -/
theorem radius_calibration (v η : ℝ) (hv : 0 < v) (hη : 0 < η) (hη1 : η < 1) :
    2 * Real.exp (-(Real.sqrt (2 * v * Real.log (2 / η))) ^ 2 / (2 * v)) = η := by
  have hlog : 0 ≤ Real.log (2 / η) := Real.log_nonneg (by linarith [(le_div_iff₀ hη).mpr (show 1 * η ≤ 2 by linarith)])
  rw [Real.sq_sqrt (mul_nonneg (mul_nonneg zero_le_two hv.le) hlog)]
  rw [neg_div, mul_div_cancel_left₀ (Real.log (2 / η)) (ne_of_gt (mul_pos zero_lt_two hv)), Real.exp_neg, Real.exp_log (div_pos zero_lt_two hη)]
  field_simp

/-- A positive-proxy confidence radius with the actual requested error level. -/
theorem confidence_tail_positive {X : Ω → ℝ} {c : NNReal}
    (hX : HasSubgaussianMGF X c μ) (hc : 0 < (c : ℝ))
    {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    μ.real {ω | Real.sqrt (2 * (c : ℝ) * Real.log (2 / η)) < |X ω|} ≤ η := by
  exact (measureReal_mono (μ := μ)
    (s₂ := {ω | Real.sqrt (2 * (c : ℝ) * Real.log (2 / η)) ≤ |X ω|})
    (fun ω (h : Real.sqrt (2 * (c : ℝ) * Real.log (2 / η)) < |X ω|) => le_of_lt h)).trans
    ((Atlas.subgaussian_two_sided hX (Real.sqrt_nonneg _)).trans_eq
      (radius_calibration (c : ℝ) η hc hη hη1))

/-- Degenerate MGF proxy: the noise is zero almost surely, so the zero radius is valid. -/
theorem confidence_tail_zero {X : Ω → ℝ} (hX : HasSubgaussianMGF X 0 μ) :
    μ.real {ω | 0 < |X ω|} = 0 := by
  apply (measureReal_eq_zero_iff).mpr
  simpa only [not_not] using
    (ae_iff.mp (hX.ae_eq_zero_of_hasSubgaussianMGF_zero.mono
      (fun ω h => show ¬(0 < |X ω|) from by simp [h])))

/-- The calibrated radius includes the zero-proxy case without dividing by zero. -/
theorem confidence_tail {X : Ω → ℝ} {c : NNReal}
    (hX : HasSubgaussianMGF X c μ) {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    μ.real {ω | Real.sqrt (2 * (c : ℝ) * Real.log (2 / η)) < |X ω|} ≤ η := by
  rcases eq_or_lt_of_le c.coe_nonneg with hc | hc
  · have hc0 : c = 0 := NNReal.coe_eq_zero.mp hc.symm
    subst c
    simpa only [NNReal.coe_zero, mul_zero, zero_mul, Real.sqrt_zero,
      confidence_tail_zero hX] using hη.le
  · exact confidence_tail_positive hX hc hη hη1

omit [MeasurableSpace Ω] in
/-- A certified complete remainder reduces interval failure to noise or certificate failure. -/
theorem inflated_failure_subset (estimate X R : Ω → ℝ) (target r : ℝ) (cert : Set Ω)
    (hrem : ∀ ω ∈ cert, |estimate ω - target - X ω| ≤ R ω) :
    {ω | r + R ω < |estimate ω - target|} ⊆ {ω | r < |X ω|} ∪ certᶜ := by
  exact fun ω h => (Classical.em (ω ∈ cert)).elim
    (fun hc => Or.inl (lt_of_not_ge (fun hn =>
      (not_lt_of_ge (Atlas.interval_inflation hn (hrem ω hc))) h)))
    (fun hc => Or.inr hc)

/-- Fixed-report finite-sample interval with a possibly random, certified full remainder.
The failure budget includes the certificate failure probability. -/
theorem certified_interval_failure_le (estimate X R : Ω → ℝ) (target : ℝ) (cert : Set Ω)
    {c : NNReal} (hX : HasSubgaussianMGF X c μ) {η ρ : ℝ}
    (hη : 0 < η) (hη1 : η < 1) (hcert : μ.real certᶜ ≤ ρ)
    (hrem : ∀ ω ∈ cert, |estimate ω - target - X ω| ≤ R ω) :
    μ.real {ω | Real.sqrt (2 * (c : ℝ) * Real.log (2 / η)) + R ω <
      |estimate ω - target|} ≤ η + ρ := by
  exact (measureReal_mono (μ := μ) (inflated_failure_subset estimate X R target _ cert hrem)).trans
    ((measureReal_union_le _ _).trans (add_le_add (confidence_tail hX hη hη1) hcert))

/-- Simultaneous calibrated intervals; a common certificate is charged only once. -/
theorem family_certified_interval_failure_le {ι : Type*} [Fintype ι]
    (estimate X R : ι → Ω → ℝ) (target η : ι → ℝ) (c : ι → NNReal) (cert : Set Ω)
    (hX : ∀ i, HasSubgaussianMGF (X i) (c i) μ)
    (hη : ∀ i, 0 < η i) (hη1 : ∀ i, η i < 1) {ρ : ℝ} (hcert : μ.real certᶜ ≤ ρ)
    (hrem : ∀ i ω, ω ∈ cert → |estimate i ω - target i - X i ω| ≤ R i ω) :
    μ.real (⋃ i, {ω | Real.sqrt (2 * (c i : ℝ) * Real.log (2 / η i)) + R i ω <
      |estimate i ω - target i|}) ≤ (∑ i, η i) + ρ := by
  exact (measureReal_mono (μ := μ) (Atlas.Selection.family_failure_subset _ _ cert
    (fun i ω h => (inflated_failure_subset (estimate i) (X i) (R i) (target i) _ cert
      (hrem i) h.1).resolve_right (not_not.mpr h.2)))).trans
    ((measureReal_union_le _ _).trans (add_le_add
      ((measureReal_iUnion_fintype_le _).trans (Finset.sum_le_sum
        (fun i _ => confidence_tail (hX i) (hη i) (hη1 i)))) hcert))

/-- Any data-dependent emitted report inherits the simultaneous interval bound. -/
theorem selected_certified_interval_failure_le {ι : Type*} [Fintype ι]
    (estimate X R : ι → Ω → ℝ) (target η : ι → ℝ) (c : ι → NNReal)
    (cert emit : Set Ω) (select : Ω → ι)
    (hX : ∀ i, HasSubgaussianMGF (X i) (c i) μ)
    (hη : ∀ i, 0 < η i) (hη1 : ∀ i, η i < 1) {ρ : ℝ} (hcert : μ.real certᶜ ≤ ρ)
    (hrem : ∀ i ω, ω ∈ cert → |estimate i ω - target i - X i ω| ≤ R i ω) :
    μ.real {ω | ω ∈ emit ∧ Real.sqrt (2 * (c (select ω) : ℝ) * Real.log (2 / η (select ω))) +
      R (select ω) ω < |estimate (select ω) ω - target (select ω)|} ≤ (∑ i, η i) + ρ := by
  exact (measureReal_mono (μ := μ) (Atlas.Selection.selected_failure_subset _ select emit)).trans
    (family_certified_interval_failure_le estimate X R target η c cert hX hη hη1 hcert hrem)

/-- Complete signed source/calibration remainder, including curvature on every record. -/
theorem complete_remainder_bound {ι : Type*} (s : Finset ι)
    (a signal curve extract noise b : ι → ℝ) (target targetCurve Bcurv : ℝ)
    (hsignal : ∑ i ∈ s, a i * signal i = target)
    (hcurve : |(∑ i ∈ s, a i * curve i) - targetCurve| ≤ Bcurv)
    (hext : ∀ i ∈ s, |extract i| ≤ b i) :
    |(∑ i ∈ s, a i * (signal i + curve i + extract i + noise i)) -
      (target + targetCurve) - (∑ i ∈ s, a i * noise i)| ≤
      Bcurv + ∑ i ∈ s, |a i| * b i := by
  rw [Atlas.full_error_decomposition s a signal curve extract noise target targetCurve hsignal]
  rw [add_assoc, add_sub_cancel_left]
  exact (abs_add_le _ _).trans (add_le_add hcurve (Atlas.weighted_error_bound s a extract b hext))

/-- Independent signed observations give the corrected finite-sample interval directly.
The same finite index set contains source and calibration records. -/
theorem weighted_complete_interval_failure_le {ι : Type*} (s : Finset ι)
    (a signal curve : ι → ℝ) (extract noise b : ι → Ω → ℝ) (c : ι → NNReal)
    (target targetCurve Bcurv : ℝ) (cert : Set Ω) {η ρ : ℝ}
    (hsignal : ∑ i ∈ s, a i * signal i = target)
    (hcurve : |(∑ i ∈ s, a i * curve i) - targetCurve| ≤ Bcurv)
    (hext : ∀ ω ∈ cert, ∀ i ∈ s, |extract i ω| ≤ b i ω)
    (hind : iIndepFun noise μ) (hnoise : ∀ i ∈ s, HasSubgaussianMGF (noise i) (c i) μ)
    (hη : 0 < η) (hη1 : η < 1) (hcert : μ.real certᶜ ≤ ρ) :
    μ.real {ω | Real.sqrt (2 * ((∑ i ∈ s, NNReal.mk (a i ^ 2) (sq_nonneg (a i)) * c i : NNReal) : ℝ) *
      Real.log (2 / η)) + (Bcurv + ∑ i ∈ s, |a i| * b i ω) <
      |(∑ i ∈ s, a i * (signal i + curve i + extract i ω + noise i ω)) -
        (target + targetCurve)|} ≤ η + ρ := by
  exact certified_interval_failure_le _ _ _ _ cert
    (Atlas.weighted_subgaussian s a noise c hind hnoise) hη hη1 hcert
    (fun ω hω => complete_remainder_bound s a signal curve (fun i => extract i ω)
      (fun i => noise i ω) (fun i => b i ω) target targetCurve Bcurv hsignal hcurve (hext ω hω))

end Atlas.Confidence
