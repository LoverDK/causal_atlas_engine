import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Deterministic non-identification bounds (Theorem 5.4(b)).
The distance here is to the observed set, not its convex hull.
The Gaussian statistical minimax theorem 5.4(a) is not claimed by this file. -/
namespace CausalAtlas
open Metric
open scoped NNReal

/-- The scalar two-point obstruction. -/
theorem two_point_absolute (t a : ℝ) :
    a ≤ max |t - a| |t + a| := by
  nlinarith [le_abs_self (t + a), neg_le_abs (t - a),
    le_max_left |t - a| |t + a|, le_max_right |t - a| |t + a|]

/-- Pointwise squared-loss identity; its integral gives the randomized risk bound. -/
theorem two_point_square_identity (t a : ℝ) :
    ((t - a)^2 + (t + a)^2) / 2 = t^2 + a^2 := by
  ring

variable {M : Type*} [MetricSpace M]

noncomputable def gapFunction (L : ℝ≥0) (S : Set M) (x : M) : ℝ :=
  (L : ℝ) * infDist x S

theorem gapFunction_lipschitz (L : ℝ≥0) (S : Set M) :
    LipschitzWith L (gapFunction L S) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  simpa [gapFunction, Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg L.coe_nonneg]
    using mul_le_mul_of_nonneg_left ((lipschitz_infDist_pt S).dist_le_mul x y) L.coe_nonneg

theorem neg_gapFunction_lipschitz (L : ℝ≥0) (S : Set M) :
    LipschitzWith L (fun x ↦ -gapFunction L S x) := by
  exact LipschitzWith.of_dist_le_mul fun x y ↦
    (dist_neg_neg (gapFunction L S x) (gapFunction L S y)).le.trans
      ((gapFunction_lipschitz L S).dist_le_mul x y)

@[simp] theorem gapFunction_eq_zero (L : ℝ≥0) {S : Set M} {x : M} (hx : x ∈ S) :
    gapFunction L S x = 0 := by
  simp [gapFunction, infDist_zero_of_mem hx]

/-- Every deterministic estimator has a Lipschitz counter-world with identical zero observations.
This is stronger than the absolute-loss constant in Theorem 5.4(b). -/
theorem unsupported_target_lower_bound {ι : Type*} (m : ι → M) (target : M)
    (L : ℝ≥0) (estimate : (ι → ℝ) → ℝ) :
    ∃ f : M → ℝ, LipschitzWith L f ∧ (∀ i, f (m i) = 0) ∧
      (L : ℝ) * infDist target (Set.range m) ≤
        |estimate (fun i ↦ f (m i)) - f target| := by
  rcases le_max_iff.mp (two_point_absolute (estimate (fun _ ↦ 0))
    ((L : ℝ) * infDist target (Set.range m))) with hp | hn
  · refine ⟨gapFunction L (Set.range m), gapFunction_lipschitz L _,
      fun i ↦ gapFunction_eq_zero L (Set.mem_range_self i), ?_⟩
    have hz : (fun i => gapFunction L (Set.range m) (m i)) = (fun _ => 0) :=
      funext (fun i => gapFunction_eq_zero L (Set.mem_range_self i))
    rw [hz]
    simpa only [gapFunction] using hp
  · refine ⟨fun x => -gapFunction L (Set.range m) x, neg_gapFunction_lipschitz L _,
      fun i => neg_eq_zero.mpr (gapFunction_eq_zero L (Set.mem_range_self i)), ?_⟩
    have hz : (fun i => -gapFunction L (Set.range m) (m i)) = (fun _ => 0) :=
      funext (fun i => neg_eq_zero.mpr (gapFunction_eq_zero L (Set.mem_range_self i)))
    rw [hz]
    simpa only [gapFunction, sub_neg_eq_add] using hn

end CausalAtlas
