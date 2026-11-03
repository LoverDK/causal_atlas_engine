import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Ring
import Atlas.Estimation

/-! Regression-to-atlas connection. The sole algebraic nonsingularity premise is
an invertible Gram determinant; neither the inverse identity nor feature
reproduction is assumed. W may be any matrix for these algebraic results. -/
open Matrix MeasureTheory ProbabilityTheory
open scoped Matrix BigOperators
namespace Atlas.Regression

variable {J P C : Type*} [Fintype J] [Fintype P] [DecidableEq P]

noncomputable def gram (X : Matrix J P ℝ) (W : Matrix J J ℝ) : Matrix P P ℝ :=
  Xᵀ * W * X

noncomputable def calibration (X : Matrix J P ℝ) (W : Matrix J J ℝ) : Matrix P J ℝ :=
  (gram X W)⁻¹ * (Xᵀ * W)

/-- Weighted calibration is a left inverse of the calibration feature matrix. -/
theorem calibration_left_inverse (X : Matrix J P ℝ) (W : Matrix J J ℝ)
    (h : IsUnit (gram X W).det) : calibration X W * X = 1 := by
  simpa only [calibration, gram, Matrix.mul_assoc] using
    Matrix.nonsing_inv_mul (gram X W) h

noncomputable def calibrationWeights (X : Matrix J P ℝ) (W : Matrix J J ℝ)
    (r : P → ℝ) : J → ℝ := (calibration X W)ᵀ *ᵥ r

/-- The actual signed calibration weights reproduce the support residual. -/
theorem calibration_weights_reproduce (X : Matrix J P ℝ) (W : Matrix J J ℝ)
    (h : IsUnit (gram X W).det) (r : P → ℝ) :
    Xᵀ *ᵥ calibrationWeights X W r = r := by
  simp only [calibrationWeights, Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
    calibration_left_inverse X W h, Matrix.transpose_one, Matrix.one_mulVec]

/-- Source and calibration features together exactly reproduce the target. -/
theorem combined_features_reproduce [Fintype C] (S : Matrix C P ℝ)
    (X : Matrix J P ℝ) (W : Matrix J J ℝ) (h : IsUnit (gram X W).det)
    (a : C → ℝ) (target : P → ℝ) :
    Sᵀ *ᵥ a + Xᵀ *ᵥ calibrationWeights X W (target - Sᵀ *ᵥ a) = target := by
  simp only [calibration_weights_reproduce X W h, ← add_sub_assoc, add_sub_cancel_left]

/-- The regression correction equals a signed linear combination of calibration outcomes. -/
theorem calibration_prediction_eq_weights (X : Matrix J P ℝ) (W : Matrix J J ℝ)
    (r : P → ℝ) (y : J → ℝ) :
    r ⬝ᵥ (calibration X W *ᵥ y) = calibrationWeights X W r ⬝ᵥ y := by
  simpa only [calibrationWeights, dotProduct_comm] using
    (Matrix.dotProduct_transpose_mulVec (calibration X W) y r).symm

/-- Combining source outcomes and the regression correction reproduces every linear
feature signal. Affine signals are included by putting an intercept in the features. -/
theorem combined_signal_reproduce [Fintype C] (S : Matrix C P ℝ)
    (X : Matrix J P ℝ) (W : Matrix J J ℝ) (h : IsUnit (gram X W).det)
    (a : C → ℝ) (target β : P → ℝ) :
    a ⬝ᵥ (S *ᵥ β) + calibrationWeights X W (target - Sᵀ *ᵥ a) ⬝ᵥ (X *ᵥ β) =
      target ⬝ᵥ β := by
  rw [← Matrix.dotProduct_transpose_mulVec S β a,
    ← Matrix.dotProduct_transpose_mulVec X β (calibrationWeights X W (target - Sᵀ *ᵥ a)),
    ← dotProduct_add, combined_features_reproduce S X W h a target, dotProduct_comm]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Linearity of the integral for a finite vector of integrable observations. -/
theorem dotProduct_expectation {I : Type*} [Fintype I]
    (a : I → ℝ) (Y : I → Ω → ℝ) (hY : ∀ i, Integrable (Y i) μ) :
    (∫ ω, a ⬝ᵥ (fun i => Y i ω) ∂μ) = a ⬝ᵥ (fun i => ∫ ω, Y i ω ∂μ) := by
  simpa [dotProduct] using Atlas.weighted_expectation Finset.univ a Y (fun i _ => hY i)

/-- Finite signed regression combinations retain integrability. -/
theorem integrable_dotProduct {I : Type*} [Fintype I]
    (a : I → ℝ) (Y : I → Ω → ℝ) (hY : ∀ i, Integrable (Y i) μ) :
    Integrable (fun ω => a ⬝ᵥ (fun i => Y i ω)) μ := by
  simpa [dotProduct] using integrable_finsetSum Finset.univ (fun i _ => (hY i).const_mul (a i))

/-- Actual source/calibration estimator unbiasedness from the invertible Gram
matrix and the mean model; feature reproduction is proved, not a premise. -/
theorem calibrated_estimator_unbiased [Fintype C] (S : Matrix C P ℝ)
    (X : Matrix J P ℝ) (W : Matrix J J ℝ) (h : IsUnit (gram X W).det)
    (a : C → ℝ) (target β : P → ℝ) (YC : C → Ω → ℝ) (YJ : J → Ω → ℝ)
    (hC : ∀ i, Integrable (YC i) μ) (hJ : ∀ j, Integrable (YJ j) μ)
    (hmeanC : ∀ i, (∫ ω, YC i ω ∂μ) = (S *ᵥ β) i)
    (hmeanJ : ∀ j, (∫ ω, YJ j ω ∂μ) = (X *ᵥ β) j) :
    (∫ ω, a ⬝ᵥ (fun i => YC i ω) +
      (target - Sᵀ *ᵥ a) ⬝ᵥ (calibration X W *ᵥ (fun j => YJ j ω)) ∂μ) =
      target ⬝ᵥ β := by
  simp_rw [calibration_prediction_eq_weights]
  rw [integral_add (integrable_dotProduct a YC hC)
    (integrable_dotProduct (calibrationWeights X W (target - Sᵀ *ᵥ a)) YJ hJ),
    dotProduct_expectation a YC hC,
    dotProduct_expectation (calibrationWeights X W (target - Sᵀ *ᵥ a)) YJ hJ]
  simpa only [hmeanC, hmeanJ] using combined_signal_reproduce S X W h a target β

end Atlas.Regression
