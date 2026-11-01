import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
open scoped BigOperators
namespace Atlas

/-- The signed combined source/calibration weights reproduce any affine signal
once they reproduce all feature coordinates (including the intercept). -/
theorem affine_signal_reproduction {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (a : ι → ℝ) (x : ι → κ → ℝ) (target β : κ → ℝ)
    (hrepr : ∀ j ∈ t, ∑ i ∈ s, a i * x i j = target j) :
    ∑ i ∈ s, a i * (∑ j ∈ t, x i j * β j) = ∑ j ∈ t, target j * β j := by
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun j hj =>
    (Finset.sum_mul s (fun i => a i * x i j) (β j)).symm.trans
      (congrArg (fun z => z * β j) (hrepr j hj)))

/-- Signed calibration weights must enter an error radius through absolute values. -/
theorem weighted_error_bound {ι : Type*} (s : Finset ι) (a e b : ι → ℝ)
    (he : ∀ i ∈ s, |e i| ≤ b i) :
    |∑ i ∈ s, a i * e i| ≤ ∑ i ∈ s, |a i| * b i := by
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i hi =>
    (abs_mul (a i) (e i)).le.trans (mul_le_mul_of_nonneg_left (he i hi) (abs_nonneg _))))

/-- Complete deterministic remainder propagation into an interval. -/
theorem interval_inflation {estimate target noise radius remainder : ℝ}
    (hnoise : |noise| ≤ radius) (hrem : |estimate - target - noise| ≤ remainder) :
    |estimate - target| ≤ radius + remainder := by
  exact abs_le.mpr ⟨by linarith [(abs_le.mp hnoise).1, (abs_le.mp hrem).1],
    by linarith [(abs_le.mp hnoise).2, (abs_le.mp hrem).2]⟩

/-- All source and calibration curvature terms survive in the error decomposition. -/
theorem full_error_decomposition {ι : Type*} (s : Finset ι)
    (a signal curve extract noise : ι → ℝ) (target targetCurve : ℝ)
    (hsignal : ∑ i ∈ s, a i * signal i = target) :
    (∑ i ∈ s, a i * (signal i + curve i + extract i + noise i)) -
      (target + targetCurve) =
      (∑ i ∈ s, a i * noise i) + ((∑ i ∈ s, a i * curve i) - targetCurve) +
      (∑ i ∈ s, a i * extract i) := by
  simp only [mul_add, Finset.sum_add_distrib, hsignal]
  ring

end Atlas
