import Mathlib.Probability.CentralLimitTheorem

/-!
# A verified iid subcase of corrected Theorem 5.3

The manuscript's arbitrarily selected triangular-array CLT is not asserted here.
We verify the fixed-report, centered, unit-second-moment iid subcase. The Slutsky
perturbation step remains to be formalized. This result uses Mathlib's actual
convergence-in-distribution objects.
They do not prove a variance estimator consistent or imply exact coverage after
adding a nonnegligible curvature/extraction radius.
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

end Atlas.Asymptotics
