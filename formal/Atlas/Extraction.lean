import Atlas.Algebra
import Mathlib.Analysis.InnerProductSpace.Basic

/-! Deterministic propagation of actual feature and effect extraction errors.
The finite index set includes source AND calibration records; every weight is
treated as signed. These are eventwise certificates, not probability claims. -/
open scoped BigOperators InnerProductSpace
namespace Atlas.Extraction

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Cauchy-Schwarz turns an observed-feature error into a signal error. -/
theorem feature_signal_error (x xhat β : E) (u L : ℝ)
    (hx : ‖x - xhat‖ ≤ u) (hβ : ‖β‖ ≤ L) :
    |⟪x - xhat, β⟫_ℝ| ≤ L * u := by
  exact (abs_real_inner_le_norm (x - xhat) β).trans
    ((mul_le_mul hx hβ (norm_nonneg β) ((norm_nonneg (x - xhat)).trans hx)).trans_eq
      (mul_comm u L))

/-- A single record's feature perturbation and effect extraction error combine additively. -/
theorem record_extraction_error (x xhat β : E) (δ u v L : ℝ)
    (hx : ‖x - xhat‖ ≤ u) (hβ : ‖β‖ ≤ L) (hδ : |δ| ≤ v) :
    |⟪x - xhat, β⟫_ℝ + δ| ≤ L * u + v := by
  exact (abs_add_le _ _).trans (add_le_add (feature_signal_error x xhat β u L hx hβ) hδ)

/-- Every included record contributes through the absolute value of its signed weight. -/
theorem weighted_extraction_error (s : Finset ι) (a δ u v : ι → ℝ)
    (x xhat : ι → E) (β : E) (L : ℝ)
    (hx : ∀ i ∈ s, ‖x i - xhat i‖ ≤ u i) (hβ : ‖β‖ ≤ L)
    (hδ : ∀ i ∈ s, |δ i| ≤ v i) :
    |∑ i ∈ s, a i * (⟪x i - xhat i, β⟫_ℝ + δ i)| ≤
      ∑ i ∈ s, |a i| * (L * u i + v i) := by
  exact Atlas.weighted_error_bound s a _ _ (fun i hi =>
    record_extraction_error (x i) (xhat i) β (δ i) (u i) (v i) L (hx i hi) hβ (hδ i hi))

/-- Exact decomposition using the observed design's reproduction identity. -/
theorem observed_design_decomposition (s : Finset ι) (a ζ ε δ : ι → ℝ)
    (x xhat : ι → E) (target targetHat β : E) (ζtarget : ℝ)
    (hreproduce : ∑ i ∈ s, a i * ⟪xhat i, β⟫_ℝ = ⟪targetHat, β⟫_ℝ) :
    (∑ i ∈ s, a i * (⟪x i, β⟫_ℝ + ζ i + ε i + δ i)) -
      (⟪target, β⟫_ℝ + ζtarget) - (∑ i ∈ s, a i * ε i) =
      ((∑ i ∈ s, a i * (⟪x i - xhat i, β⟫_ℝ + δ i)) - ⟪target - targetHat, β⟫_ℝ) +
      ((∑ i ∈ s, a i * ζ i) - ζtarget) := by
  simp only [inner_sub_left, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, hreproduce]
  ring

/-- Full eventwise certificate: mechanism extraction, effect extraction, target
extraction, and all source/calibration curvature terms. The model noise remains explicit. -/
theorem full_extraction_certificate (s : Finset ι) (a ζ ε δ u v : ι → ℝ)
    (x xhat : ι → E) (target targetHat β : E) (ζtarget utarget L Bcurv : ℝ)
    (hreproduce : ∑ i ∈ s, a i * ⟪xhat i, β⟫_ℝ = ⟪targetHat, β⟫_ℝ)
    (hx : ∀ i ∈ s, ‖x i - xhat i‖ ≤ u i) (hβ : ‖β‖ ≤ L)
    (hδ : ∀ i ∈ s, |δ i| ≤ v i) (htarget : ‖target - targetHat‖ ≤ utarget)
    (hcurv : |(∑ i ∈ s, a i * ζ i) - ζtarget| ≤ Bcurv) :
    |(∑ i ∈ s, a i * (⟪x i, β⟫_ℝ + ζ i + ε i + δ i)) -
      (⟪target, β⟫_ℝ + ζtarget) - (∑ i ∈ s, a i * ε i)| ≤
      (∑ i ∈ s, |a i| * (L * u i + v i)) + L * utarget + Bcurv := by
  rw [observed_design_decomposition s a ζ ε δ x xhat target targetHat β ζtarget hreproduce]
  exact (abs_add_le _ _).trans (add_le_add
    ((abs_sub _ _).trans (add_le_add (weighted_extraction_error s a δ u v x xhat β L hx hβ hδ)
      (feature_signal_error target targetHat β utarget L htarget hβ))) hcurv)

/-- Vector reproduction is sufficient for the scalar identity used above. -/
theorem signal_reproduction_of_vector (s : Finset ι) (a : ι → ℝ)
    (xhat : ι → E) (targetHat β : E)
    (h : ∑ i ∈ s, a i • xhat i = targetHat) :
    ∑ i ∈ s, a i * ⟪xhat i, β⟫_ℝ = ⟪targetHat, β⟫_ℝ := by
  simpa only [sum_inner, real_inner_smul_left] using congrArg (fun z => ⟪z, β⟫_ℝ) h

/-- Norm control of a signed finite feature perturbation. -/
theorem weighted_feature_perturbation_norm (s : Finset ι) (a u : ι → ℝ)
    (x xhat : ι → E) (hx : ∀ i ∈ s, ‖x i - xhat i‖ ≤ u i) :
    ‖∑ i ∈ s, a i • (x i - xhat i)‖ ≤ ∑ i ∈ s, |a i| * u i := by
  exact (norm_sum_le s _).trans (Finset.sum_le_sum (fun i hi =>
    (norm_smul (a i) (x i - xhat i)).le.trans (by
      simpa only [Real.norm_eq_abs] using mul_le_mul_of_nonneg_left (hx i hi) (norm_nonneg (a i)))))

/-- The original support-residual geometric inequality, with signed weights allowed. -/
theorem support_residual_perturbation_norm (s : Finset ι) (a u : ι → ℝ)
    (x xhat : ι → E) (target targetHat : E) (utarget : ℝ)
    (hx : ∀ i ∈ s, ‖x i - xhat i‖ ≤ u i) (htarget : ‖target - targetHat‖ ≤ utarget) :
    ‖(target - ∑ i ∈ s, a i • x i) - (targetHat - ∑ i ∈ s, a i • xhat i)‖ ≤
      utarget + ∑ i ∈ s, |a i| * u i := by
  rw [sub_sub_sub_comm, ← Finset.sum_sub_distrib]
  simpa only [smul_sub] using (norm_sub_le (target - targetHat) (∑ i ∈ s, a i • (x i - xhat i))).trans
    (add_le_add htarget (weighted_feature_perturbation_norm s a u x xhat hx))

/-- Support-residual signal perturbation, including the target's extraction error. -/
theorem support_residual_signal_error (s : Finset ι) (a u : ι → ℝ)
    (x xhat : ι → E) (target targetHat β : E) (utarget L : ℝ)
    (hx : ∀ i ∈ s, ‖x i - xhat i‖ ≤ u i) (htarget : ‖target - targetHat‖ ≤ utarget)
    (hβ : ‖β‖ ≤ L) :
    |⟪(target - ∑ i ∈ s, a i • x i) - (targetHat - ∑ i ∈ s, a i • xhat i), β⟫_ℝ| ≤
      L * (utarget + ∑ i ∈ s, |a i| * u i) := by
  exact feature_signal_error _ _ β _ L
    (support_residual_perturbation_norm s a u x xhat target targetHat utarget hx htarget) hβ

end Atlas.Extraction
