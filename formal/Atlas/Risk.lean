import Atlas.LowerBounds
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Linarith
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Atlas.Risk
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Two observationally identical worlds remain indistinguishable to a randomized
estimator. This version states the risk bound for square-integrable random output. -/
theorem randomized_two_point_risk (Z : Ω → ℝ) (a : ℝ) (hZ : MemLp Z 2 μ) :
    a ^ 2 ≤ max (∫ ω, (Z ω - a) ^ 2 ∂μ) (∫ ω, (Z ω + a) ^ 2 ∂μ) := by
  have hp : ∀ ω, 2 * a ^ 2 ≤ (Z ω - a) ^ 2 + (Z ω + a) ^ 2 :=
    fun ω => by nlinarith [sq_nonneg (Z ω)]
  have hi := integral_mono (integrable_const (2 * a ^ 2))
    ((hZ.sub (memLp_const a)).integrable_sq.add (hZ.add (memLp_const a)).integrable_sq) hp
  simp only [Pi.add_apply, Pi.sub_apply, integral_const, probReal_univ, one_smul] at hi
  rw [integral_add (show Integrable (fun ω => (Z ω - a) ^ 2) μ from
    (hZ.sub (memLp_const a)).integrable_sq) (show Integrable (fun ω => (Z ω + a) ^ 2) μ from
    (hZ.add (memLp_const a)).integrable_sq)] at hi
  linarith [le_max_left (∫ ω, (Z ω - a) ^ 2 ∂μ) (∫ ω, (Z ω + a) ^ 2 ∂μ),
    le_max_right (∫ ω, (Z ω - a) ^ 2 ∂μ) (∫ ω, (Z ω + a) ^ 2 ∂μ)]

/-- A randomized estimator cannot recover an unobserved Lipschitz target;
one of two source-identical worlds has squared risk at least `(L * distance)^2`. -/
theorem randomized_unsupported_target_lower_bound {M ι : Type*} [MetricSpace M]
    (m : ι → M) (target : M) (L : ℝ≥0) (estimate : (ι → ℝ) → Ω → ℝ)
    (hZ : MemLp (estimate (fun _ => 0)) 2 μ) :
    ∃ f : M → ℝ, LipschitzWith L f ∧ (∀ i, f (m i) = 0) ∧
      ((L : ℝ) * Metric.infDist target (Set.range m)) ^ 2 ≤
        ∫ ω, (estimate (fun i => f (m i)) ω - f target) ^ 2 ∂μ := by
  have hz : (fun i => CausalAtlas.gapFunction L (Set.range m) (m i)) = (fun _ => 0) :=
    funext (fun i => CausalAtlas.gapFunction_eq_zero L (Set.mem_range_self i))
  have hnz : (fun i => -CausalAtlas.gapFunction L (Set.range m) (m i)) = (fun _ => 0) :=
    funext (fun i => neg_eq_zero.mpr (CausalAtlas.gapFunction_eq_zero L (Set.mem_range_self i)))
  rcases le_max_iff.mp (randomized_two_point_risk (estimate (fun _ => 0))
    ((L : ℝ) * Metric.infDist target (Set.range m)) hZ) with hp | hn
  · exact ⟨CausalAtlas.gapFunction L (Set.range m), CausalAtlas.gapFunction_lipschitz L _,
      fun i => CausalAtlas.gapFunction_eq_zero L (Set.mem_range_self i),
      by rw [hz]; exact hp⟩
  · exact ⟨fun x => -CausalAtlas.gapFunction L (Set.range m) x,
      CausalAtlas.neg_gapFunction_lipschitz L _,
      fun i => neg_eq_zero.mpr (CausalAtlas.gapFunction_eq_zero L (Set.mem_range_self i)),
      by rw [hnz]; simpa only [CausalAtlas.gapFunction, sub_neg_eq_add] using hn⟩

end Atlas.Risk
