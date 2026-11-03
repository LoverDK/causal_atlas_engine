import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Fixed-report linear estimation. The coefficients include both the source
weights and the signed calibration weights. No conditional-distribution
or matrix-inverse construction is silently postulated by these lemmas. -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace Atlas
variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem weighted_expectation (s : Finset ι) (a : ι → ℝ) (Y : ι → Ω → ℝ)
    (hY : ∀ i ∈ s, Integrable (Y i) μ) :
    (∫ ω, ∑ i ∈ s, a i * Y i ω ∂μ) = ∑ i ∈ s, a i * ∫ ω, Y i ω ∂μ := by
  simp only [integral_finsetSum s (fun i hi => (hY i hi).const_mul (a i)), integral_const_mul]

theorem weighted_unbiased (s : Finset ι) (a τ : ι → ℝ) (Y : ι → Ω → ℝ)
    (hY : ∀ i ∈ s, Integrable (Y i) μ) (hmean : ∀ i, (∫ ω, Y i ω ∂μ) = τ i)
    (target : ℝ) (hreproduce : ∑ i ∈ s, a i * τ i = target) :
    (∫ ω, ∑ i ∈ s, a i * Y i ω ∂μ) = target := by
  simpa only [hmean, hreproduce] using weighted_expectation s a Y hY

theorem weighted_subgaussian (s : Finset ι) (a : ι → ℝ) (X : ι → Ω → ℝ)
    (c : ι → NNReal) (hind : iIndepFun X μ)
    (hX : ∀ i ∈ s, HasSubgaussianMGF (X i) (c i) μ) :
    HasSubgaussianMGF (fun ω => ∑ i ∈ s, a i * X i ω)
      (∑ i ∈ s, (NNReal.mk (a i ^ 2) (sq_nonneg (a i)) * c i)) μ := by
  exact HasSubgaussianMGF.sum_of_iIndepFun
    (hind.comp (fun i x => a i * x) (fun _ => measurable_const.mul measurable_id))
    (fun i hi => (hX i hi).const_mul (a i))

theorem subgaussian_two_sided [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : NNReal}
    (hX : HasSubgaussianMGF X c μ) {u : ℝ} (hu : 0 ≤ u) :
    μ.real {ω | u ≤ |X ω|} ≤ 2 * Real.exp (-u ^ 2 / (2 * (c : ℝ))) := by
  simpa only [le_abs, Set.ofPred_or, two_mul] using
    (measureReal_union_le {ω | u ≤ X ω} {ω | u ≤ -X ω}).trans
      (add_le_add (hX.measure_ge_le hu) (hX.neg.measure_ge_le hu))

theorem weighted_variance (s : Finset ι) (a : ι → ℝ) (X : ι → Ω → ℝ)
    (hind : iIndepFun X μ) (hX : ∀ i ∈ s, MemLp (X i) 2 μ) :
    variance (∑ i ∈ s, fun ω => a i * X i ω) μ =
      ∑ i ∈ s, a i ^ 2 * variance (X i) μ := by
  simpa only [Finset.sum_apply, variance_const_mul] using
    (IndepFun.variance_sum (fun i hi => (hX i hi).const_mul (a i))
      (fun i _ j _ hij => (hind.indepFun hij).comp
        (measurable_const.mul measurable_id) (measurable_const.mul measurable_id)))

end Atlas


