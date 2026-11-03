import Atlas.Bridge
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-! A finite estimated-greedy construction and its bridge guarantee.
The estimate may depend on the current set. Exhaustion uses a fallback element;
when the candidate universe is exhausted, this leaves the set unchanged. -/
open scoped BigOperators
namespace CausalAtlas.BridgeAlgorithm

variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
theorem finite_argmax_exists (V : Finset α) (score : α → ℝ) (hV : V.Nonempty) :
    ∃ u ∈ V, ∀ v ∈ V, score v ≤ score u :=
  Finset.exists_max_image V score hV

noncomputable def finiteArgmax (V : Finset α) (score : α → ℝ) (hV : V.Nonempty) : α :=
  Classical.choose (finite_argmax_exists V score hV)

omit [DecidableEq α] in
theorem finiteArgmax_mem (V : Finset α) (score : α → ℝ) (hV : V.Nonempty) :
    finiteArgmax V score hV ∈ V :=
  (Classical.choose_spec (finite_argmax_exists V score hV)).1

omit [DecidableEq α] in
theorem finiteArgmax_max (V : Finset α) (score : α → ℝ) (hV : V.Nonempty) :
    ∀ v ∈ V, score v ≤ score (finiteArgmax V score hV) :=
  (Classical.choose_spec (finite_argmax_exists V score hV)).2

noncomputable def nextChoice (V S : Finset α) (fallback : α) (score : α → ℝ) : α :=
  if h : (V \ S).Nonempty then finiteArgmax (V \ S) score h else fallback

theorem nextChoice_max (V S : Finset α) (fallback : α) (score : α → ℝ)
    (v : α) (hv : v ∈ V \ S) :
    score v ≤ score (nextChoice V S fallback score) := by
  have hn : (V \ S).Nonempty := ⟨v, hv⟩
  simpa only [nextChoice, dite_eq_left hn] using finiteArgmax_max (V \ S) score hn v hv

theorem nextChoice_mem (V S : Finset α) (fallback : α) (score : α → ℝ)
    (hf : fallback ∈ V) : nextChoice V S fallback score ∈ V := by
  unfold nextChoice
  split <;> rename_i hn
  · exact Finset.sdiff_subset (finiteArgmax_mem (V \ S) score hn)
  · exact hf

/-- The construction turns uniform estimate accuracy into true-gain dominance. -/
theorem nextChoice_approximate (V S : Finset α) (fallback : α) (score : α → ℝ)
    (F : Finset α → ℝ) (ε : ℝ) (hf : fallback ∈ V)
    (herror : ∀ v ∈ V, |score v - marginal F S v| ≤ ε)
    (v : α) (hv : v ∈ V \ S) :
    marginal F S v ≤ marginal F S (nextChoice V S fallback score) + 2 * ε := by
  linarith [estimatedGreedy_step
    (herror _ (nextChoice_mem V S fallback score hf))
    (herror v (Finset.sdiff_subset hv)) (nextChoice_max V S fallback score v hv)]

noncomputable def greedySets (V : Finset α) (fallback : α)
    (score : ℕ → Finset α → α → ℝ) : ℕ → Finset α
  | 0 => ∅
  | k + 1 => insert (nextChoice V (greedySets V fallback score k) fallback
      (score k (greedySets V fallback score k))) (greedySets V fallback score k)

noncomputable def greedyChoice (V : Finset α) (fallback : α)
    (score : ℕ → Finset α → α → ℝ) (k : ℕ) : α :=
  nextChoice V (greedySets V fallback score k) fallback (score k (greedySets V fallback score k))

theorem greedySets_zero (V : Finset α) (fallback : α)
    (score : ℕ → Finset α → α → ℝ) : greedySets V fallback score 0 = ∅ := rfl

theorem greedySets_succ (V : Finset α) (fallback : α)
    (score : ℕ → Finset α → α → ℝ) (k : ℕ) :
    greedySets V fallback score (k + 1) =
      insert (greedyChoice V fallback score k) (greedySets V fallback score k) := rfl

/-- Approximation guarantee for the constructed algorithm, without a greedy-dominance premise. -/
theorem constructed_greedy_bound
    (V T : Finset α) (fallback : α) (score : ℕ → Finset α → α → ℝ)
    (F : Finset α → ℝ) (γ ε : ℝ) (B : ℕ)
    (hf : fallback ∈ V) (hTV : T ⊆ V) (hcard : T.card ≤ B)
    (hB : 0 < B) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hε : 0 ≤ ε)
    (hmono : Monotone F) (hweak : WeakSubmodular F γ) (hF0 : F ∅ = 0)
    (herror : ∀ k, k < B → ∀ v ∈ V,
      |score k (greedySets V fallback score k) v -
        marginal F (greedySets V fallback score k) v| ≤ ε) :
    (1 - Real.exp (-γ)) * F T - 2 * (B : ℝ) * ε ≤
      F (greedySets V fallback score B) := by
  exact weakSubmodular_greedy_bound F (greedySets V fallback score)
    (greedyChoice V fallback score) T γ ε B hB hγ0 hγ1 hε hmono hweak hF0
    (greedySets_zero V fallback score) hcard (fun k _ => greedySets_succ V fallback score k)
    (fun k hk v hv => nextChoice_approximate V (greedySets V fallback score k) fallback
      (score k (greedySets V fallback score k)) F ε hf (herror k hk) v
      (Finset.mem_sdiff.mpr ⟨hTV (Finset.mem_sdiff.mp hv).1, (Finset.mem_sdiff.mp hv).2⟩))

/-- Every constructed set remains inside the candidate universe. -/
theorem greedySets_subset (V : Finset α) (fallback : α)
    (score : ℕ → Finset α → α → ℝ) (hf : fallback ∈ V) (k : ℕ) :
    greedySets V fallback score k ⊆ V := by
  exact Nat.rec (Finset.empty_subset V) (fun k ih =>
    Finset.insert_subset_iff.mpr ⟨nextChoice_mem V (greedySets V fallback score k)
      fallback (score k (greedySets V fallback score k)) hf, ih⟩) k

/-- The constructed algorithm always respects its cardinality budget. -/
theorem greedySets_card_le (V : Finset α) (fallback : α)
    (score : ℕ → Finset α → α → ℝ) (k : ℕ) :
    (greedySets V fallback score k).card ≤ k := by
  induction k with
  | zero => simp only [greedySets, Finset.card_empty, le_refl]
  | succ k ih => exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right ih 1)

omit [DecidableEq α] in
/-- A finite universe has an optimal set under every cardinality budget, including zero. -/
theorem budget_optimum_exists (V : Finset α) (F : Finset α → ℝ) (B : ℕ) :
    ∃ T ⊆ V, T.card ≤ B ∧ ∀ U ⊆ V, U.card ≤ B → F U ≤ F T := by
  obtain ⟨T, hT, hmax⟩ := finite_argmax_exists
    (V.powerset.filter (fun S => S.card ≤ B)) F ⟨∅, by simp⟩
  exact ⟨T, Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1,
    (Finset.mem_filter.mp hT).2, fun U hUV hUB => hmax U
      (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hUV, hUB⟩)⟩

/-- A shared event controlling estimated gains gives a probabilistic algorithm guarantee. -/
theorem constructed_greedy_failure_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (cert : Set Ω) (ρ : ENNReal)
    (V T : Finset α) (fallback : α) (score : Ω → ℕ → Finset α → α → ℝ)
    (F : Finset α → ℝ) (γ ε : ℝ) (B : ℕ)
    (hf : fallback ∈ V) (hTV : T ⊆ V) (hcard : T.card ≤ B)
    (hB : 0 < B) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hε : 0 ≤ ε)
    (hmono : Monotone F) (hweak : WeakSubmodular F γ) (hF0 : F ∅ = 0)
    (hcert : μ certᶜ ≤ ρ)
    (herror : ∀ ω ∈ cert, ∀ k, k < B → ∀ v ∈ V,
      |score ω k (greedySets V fallback (score ω) k) v -
        marginal F (greedySets V fallback (score ω) k) v| ≤ ε) :
    μ {ω | F (greedySets V fallback (score ω) B) <
      (1 - Real.exp (-γ)) * F T - 2 * (B : ℝ) * ε} ≤ ρ := by
  exact (MeasureTheory.measure_mono (fun ω hfail hgood =>
    not_lt_of_ge (constructed_greedy_bound V T fallback (score ω) F γ ε B
      hf hTV hcard hB hγ0 hγ1 hε hmono hweak hF0 (herror ω hgood)) hfail)).trans hcert

end CausalAtlas.BridgeAlgorithm
