import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.FunProp

/-! Support-weight attainment (Lemma A.2), for every finite nonempty archive.
The target space may be any real normed vector space. -/
namespace CausalAtlas

open scoped BigOperators

variable {ι E : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def supportObjective (m : ι → E) (target : E) (a : ι → ℝ) : ℝ :=
  ‖target - ∑ i, a i • m i‖

omit [Nonempty ι] in
theorem supportObjective_continuous (m : ι → E) (target : E) :
    Continuous (supportObjective m target) := by
  fun_prop [supportObjective]

/-- Lemma A.2: the support residual minimization over the simplex attains a minimizer. -/
theorem support_minimizer_exists (m : ι → E) (target : E) :
    ∃ a ∈ stdSimplex ℝ ι, ∀ b ∈ stdSimplex ℝ ι,
      supportObjective m target a ≤ supportObjective m target b := by
  classical
  exact (isCompact_stdSimplex ℝ ι).exists_isMinOn
    ⟨Pi.single (Classical.arbitrary ι) 1, single_mem_stdSimplex ℝ _⟩
    (supportObjective_continuous m target).continuousOn

end CausalAtlas
