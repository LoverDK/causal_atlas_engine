import Mathlib.Probability.CentralLimitTheorem
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Atlas.Algebra

/-!
# A verified iid subcase of corrected Theorem 5.3

The manuscript's arbitrarily selected triangular-array CLT is not asserted here.
We verify the fixed-report, centered, unit-second-moment iid subcase, Slutsky
perturbations, studentization, and a weighted-error sufficient condition for
relative variance consistency using actual Mathlib convergence objects.
No particular variance estimator is claimed to satisfy that sufficient condition.
These results do not imply exact coverage after adding a nonnegligible radius.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

namespace Atlas.Asymptotics

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']

/-- A genuine fixed-report iid CLT, with standard normal limit. -/
theorem fixed_iid_clt {X : ℕ → Ω → ℝ} {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) P')
    (hmean : P[X 0] = 0) (hsecond : P[X 0 ^ 2] = 1)
    (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution
      (fun (n : ℕ) ω ↦ (Real.sqrt n)⁻¹ * ∑ k ∈ Finset.range n, X k ω)
      atTop Z (fun _ ↦ P) P' :=
  tendstoInDistribution_inv_sqrt_mul_sum hZ hmean hsecond hindep hident

/-- A vanishing normalized remainder preserves any established limit law.
No independence between the remainder and the centered statistic is required. -/
theorem add_negligible {X R : ℕ → Ω → ℝ} {Z : Ω' → ℝ}
    (hX : TendstoInDistribution X atTop Z (fun _ => P) P')
    (hR : TendstoInMeasure P R atTop (fun _ => 0))
    (hm : ∀ n, AEMeasurable (R n) P) :
    TendstoInDistribution (fun n => X n + R n) atTop Z (fun _ => P) P' := by
  simpa only [add_zero, Pi.add_apply] using hX.add_of_tendstoInMeasure_const hR hm

/-- Multiplication by a factor converging in probability to one preserves the limit. -/
theorem mul_consistent_factor {X A : ℕ → Ω → ℝ} {Z : Ω' → ℝ}
    (hX : TendstoInDistribution X atTop Z (fun _ => P) P')
    (hA : TendstoInMeasure P A atTop (fun _ => 1))
    (hm : ∀ n, AEMeasurable (A n) P) :
    TendstoInDistribution (fun n ω => X n ω * A n ω) atTop Z (fun _ => P) P' := by
  simpa only [mul_one] using
    hX.continuous_comp_prodMk_of_tendstoInMeasure_const
      (g := fun (p : ℝ × ℝ) => p.1 * p.2) (continuous_fst.mul continuous_snd) hA hm

omit [IsProbabilityMeasure P] in
/-- Continuity at a constant limit suffices for convergence in probability.
This includes transformations, such as inverse square root, which are not
globally continuous on the real line. -/
theorem continuousAt_inMeasure_const {f : ℕ → Ω → ℝ} {g : ℝ → ℝ} {c : ℝ}
    (hg : ContinuousAt g c) (hf : TendstoInMeasure P f atTop (fun _ => c)) :
    TendstoInMeasure P (fun n ω => g (f n ω)) atTop (fun _ => g c) := by
  rw [tendstoInMeasure_iff_dist] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.mp hg ε hε
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hf δ hδ)
    (fun _ => zero_le) (fun n => measure_mono
      (fun ω hω => le_of_not_gt (fun h => not_lt_of_ge hω (hcont h))))

omit [IsProbabilityMeasure P] in
/-- A consistent relative variance yields a consistent inverse standard deviation. -/
theorem inverse_sqrt_consistent {Q : ℕ → Ω → ℝ}
    (hQ : TendstoInMeasure P Q atTop (fun _ => 1)) :
    TendstoInMeasure P (fun n ω => (Real.sqrt (Q n ω))⁻¹) atTop (fun _ => 1) := by
  simpa using continuousAt_inMeasure_const
    (g := fun q => (Real.sqrt q)⁻¹)
    (Real.continuous_sqrt.continuousAt.inv₀ (by simp)) hQ

/-- Studentization after a negligible normalized remainder. Here `Q` is the
estimated variance divided by the true variance. Independence of `X`, `R`, and
`Q` is not assumed. The pre-studentization limit is an explicit prerequisite. -/
theorem studentized_limit {X R Q : ℕ → Ω → ℝ} {Z : Ω' → ℝ}
    (hX : TendstoInDistribution X atTop Z (fun _ => P) P')
    (hR : TendstoInMeasure P R atTop (fun _ => 0))
    (hQ : TendstoInMeasure P Q atTop (fun _ => 1))
    (hmR : ∀ n, AEMeasurable (R n) P)
    (hmQ : ∀ n, AEMeasurable (Q n) P) :
    TendstoInDistribution
      (fun n ω => (X n ω + R n ω) / Real.sqrt (Q n ω))
      atTop Z (fun _ => P) P' := by
  simpa only [div_eq_mul_inv, Pi.add_apply] using
    mul_consistent_factor (add_negligible hX hR hmR)
      (inverse_sqrt_consistent hQ) (fun n => (hmQ n).sqrt.inv)

omit [IsProbabilityMeasure P] in
/-- An error dominated pointwise by an error vanishing in probability also
vanishes in probability. No independence or measurability hypothesis is needed. -/
theorem dominated_inMeasure_const {f e : ℕ → Ω → ℝ} {c : ℝ}
    (he : TendstoInMeasure P e atTop (fun _ => 0))
    (hbound : ∀ n ω, |f n ω - c| ≤ |e n ω|) :
    TendstoInMeasure P f atTop (fun _ => c) := by
  exact tendstoInMeasure_iff_dist.mpr (fun ε hε =>
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendstoInMeasure_iff_dist.mp he ε hε) (fun _ => zero_le)
      (fun n => measure_mono (fun ω hω => by
        simpa only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero] using
          (show ε ≤ |f n ω - c| from hω).trans (hbound n ω))))

/-- Absolute relative error of the aggregated variance is controlled by the
weighted absolute errors of its individual variance estimates. Zero component
variances are allowed; only the total true variance must be positive. -/
theorem weighted_variance_relative_bound {ι : Type*} (s : Finset ι)
    (w v vhat : ι → ℝ) (hV : 0 < ∑ i ∈ s, w i ^ 2 * v i) :
    |(∑ i ∈ s, w i ^ 2 * vhat i) / (∑ i ∈ s, w i ^ 2 * v i) - 1| ≤
      (∑ i ∈ s, w i ^ 2 * |vhat i - v i|) / (∑ i ∈ s, w i ^ 2 * v i) := by
  rw [div_sub_one (ne_of_gt hV), ← Finset.sum_sub_distrib]
  simp_rw [← mul_sub, abs_div, abs_of_pos hV]
  exact div_le_div_of_nonneg_right
    ((Atlas.weighted_error_bound s (fun i => w i ^ 2) (fun i => vhat i - v i)
      (fun i => |vhat i - v i|) (fun _ _ => le_rfl)).trans
      (Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right
        (le_of_eq (abs_of_nonneg (sq_nonneg (w i)))) (abs_nonneg _)))) hV.le

omit [IsProbabilityMeasure P] in
/-- The weighted relative error criterion implies aggregate variance consistency,
even with random weights and dependence between component variance estimates. -/
theorem variance_consistent_of_weighted_errors {ι : Type*} (s : ℕ → Finset ι)
    (w v vhat : ℕ → Ω → ι → ℝ)
    (hV : ∀ n ω, 0 < ∑ i ∈ s n, w n ω i ^ 2 * v n ω i)
    (he : TendstoInMeasure P
      (fun n ω => (∑ i ∈ s n, w n ω i ^ 2 * |vhat n ω i - v n ω i|) /
        (∑ i ∈ s n, w n ω i ^ 2 * v n ω i)) atTop (fun _ => 0)) :
    TendstoInMeasure P
      (fun n ω => (∑ i ∈ s n, w n ω i ^ 2 * vhat n ω i) /
        (∑ i ∈ s n, w n ω i ^ 2 * v n ω i)) atTop (fun _ => 1) := by
  exact dominated_inMeasure_const he (fun n ω =>
    (weighted_variance_relative_bound (s n) (w n ω) (v n ω) (vhat n ω) (hV n ω)).trans
      (le_abs_self _))

end Atlas.Asymptotics
