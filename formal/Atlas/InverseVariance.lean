import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! The inverse-variance optimization part of corrected Corollary 5.2.
The feasible set here is the affine hyperplane of normalized real weights.
Additional causal-support constraints are not silently assumed satisfied. -/
open scoped BigOperators
namespace Atlas.InverseVariance

variable {ι : Type*} [Fintype ι] [Nonempty ι]

noncomputable def precisionSum (v : ι → ℝ) : ℝ := ∑ i, (v i)⁻¹
noncomputable def weight (v : ι → ℝ) (i : ι) : ℝ := (v i)⁻¹ / precisionSum v
noncomputable def objective (v a : ι → ℝ) : ℝ := ∑ i, v i * a i ^ 2

theorem scalar_square_expansion (v s a : ℝ) (hv : v ≠ 0) (hs : s ≠ 0) :
    v * (a - v⁻¹ / s)^2 = v * a^2 - 2 * a / s + v⁻¹ / s^2 := by
  field_simp
  ring

theorem precisionSum_pos (v : ι → ℝ) (hv : ∀ i, 0 < v i) : 0 < precisionSum v := by
  exact Finset.sum_pos (fun i _ => inv_pos.mpr (hv i)) Finset.univ_nonempty

theorem weight_pos (v : ι → ℝ) (hv : ∀ i, 0 < v i) (i : ι) : 0 < weight v i := by
  exact div_pos (inv_pos.mpr (hv i)) (precisionSum_pos v hv)

theorem weight_sum (v : ι → ℝ) (hv : ∀ i, 0 < v i) : ∑ i, weight v i = 1 := by
  simp only [weight, ← Finset.sum_div]
  exact div_self (ne_of_gt (precisionSum_pos v hv))

/-- The full square-completion identity, for all normalized signed weights. -/
theorem completion_square (v a : ι → ℝ) (hv : ∀ i, 0 < v i) (ha : ∑ i, a i = 1) :
    objective v a = (precisionSum v)⁻¹ + ∑ i, v i * (a i - weight v i)^2 := by
  have hpoint : ∀ i, v i * (a i - weight v i)^2 =
      v i * a i^2 - 2 * a i / precisionSum v + (v i)⁻¹ / (precisionSum v)^2 :=
    fun i => scalar_square_expansion (v i) (precisionSum v) (a i)
      (ne_of_gt (hv i)) (ne_of_gt (precisionSum_pos v hv))
  simp_rw [hpoint, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div,
    ← Finset.mul_sum, ha]
  change objective v a = (precisionSum v)⁻¹ +
    (objective v a - 2 * 1 / precisionSum v + precisionSum v / precisionSum v ^ 2)
  field_simp [ne_of_gt (precisionSum_pos v hv)]
  ring

/-- The minimum variance is the reciprocal total precision. -/
theorem objective_weight (v : ι → ℝ) (hv : ∀ i, 0 < v i) :
    objective v (weight v) = (precisionSum v)⁻¹ := by
  simpa only [sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero,
    Finset.sum_const_zero, add_zero] using completion_square v (weight v) hv (weight_sum v hv)

/-- Inverse-variance weights minimize the objective over all normalized real weights. -/
theorem objective_minimal (v a : ι → ℝ) (hv : ∀ i, 0 < v i) (ha : ∑ i, a i = 1) :
    objective v (weight v) ≤ objective v a := by
  rw [objective_weight v hv, completion_square v a hv ha]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ =>
    mul_nonneg (hv i).le (sq_nonneg _)))

/-- Equality in the variance bound determines every weight uniquely. -/
theorem objective_eq_iff (v a : ι → ℝ) (hv : ∀ i, 0 < v i) (ha : ∑ i, a i = 1) :
    objective v a = (precisionSum v)⁻¹ ↔ a = weight v := by
  constructor
  · intro heq
    have hz : ∑ i, v i * (a i - weight v i)^2 = 0 := by
      linarith [completion_square v a hv ha]
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ Finset.univ) =>
      mul_nonneg (hv i).le (sq_nonneg (a i - weight v i)))).mp hz
    exact funext (fun i => sub_eq_zero.mp (sq_eq_zero_iff.mp
      ((mul_eq_zero.mp (hzero i (Finset.mem_univ i))).resolve_left (ne_of_gt (hv i)))))
  · intro heq
    simpa only [heq] using objective_weight v hv

end Atlas.InverseVariance
