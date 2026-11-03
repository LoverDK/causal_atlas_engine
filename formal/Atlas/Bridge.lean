import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
open scoped BigOperators
namespace CausalAtlas

def marginal {α : Type*} [DecidableEq α] (F : Finset α → ℝ)
    (S : Finset α) (v : α) : ℝ := F (insert v S) - F S

def WeakSubmodular {α : Type*} [DecidableEq α] (F : Finset α → ℝ)
    (γ : ℝ) : Prop :=
  ∀ S T, γ * (F (S ∪ T) - F S) ≤ ∑ v ∈ T \ S, marginal F S v

/-- Uniform gain errors and estimated greedy choice imply the exact 2ε loss. -/
theorem estimatedGreedy_step {du dv eu ev ε : ℝ}
    (hu : |eu - du| ≤ ε) (hv : |ev - dv| ≤ ε) (hg : ev ≤ eu) :
    dv - 2 * ε ≤ du := by
  linarith [(abs_le.mp hu).2, (abs_le.mp hv).1]

/-- Iterating a contraction with additive error; the simpler linear accumulated-error bound. -/
theorem contraction_bound (D : ℕ → ℝ) (q A c : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hc : 0 ≤ c)
    (hinit : D 0 ≤ A) (n : ℕ) (hstep : ∀ k, k < n → D (k + 1) ≤ q * D k + c) :
    D n ≤ q ^ n * A + n * c := by
  induction n with
  | zero => simpa using hinit
  | succ n ih =>
    have hs := hstep n (Nat.lt_succ_self n)
    have hi := mul_le_mul_of_nonneg_left (ih (fun k hk => hstep k (Nat.lt_trans hk (Nat.lt_succ_self n)))) hq0
    have he := mul_le_mul_of_nonneg_right hq1 (mul_nonneg (Nat.cast_nonneg n) hc)
    simp only [pow_succ, Nat.cast_add, Nat.cast_one]
    nlinarith

/-- The geometric contraction is bounded by the corresponding exponential. -/
theorem geometric_le_exp (t : ℝ) (ht : 0 ≤ 1 - t) (n : ℕ) :
    (1 - t) ^ n ≤ Real.exp (-(n : ℝ) * t) := by
  have hbase : 1 - t ≤ Real.exp (-t) := by linarith [Real.add_one_le_exp (-t)]
  have hp := pow_le_pow_left₀ ht hbase n
  simpa only [← Real.exp_nat_mul, mul_neg, neg_mul] using hp

/-- Weak submodularity converts approximate greedy dominance into progress toward any comparator. -/
theorem weakSubmodular_progress {α : Type*} [DecidableEq α]
    (F : Finset α → ℝ) (γ ε : ℝ) (S T : Finset α) (u : α) (B : ℕ)
    (hmono : Monotone F) (hweak : WeakSubmodular F γ)
    (hγ : 0 ≤ γ) (hε : 0 ≤ ε) (hcard : T.card ≤ B)
    (hgreedy : ∀ v ∈ T \ S, marginal F S v ≤ marginal F S u + 2 * ε) :
    γ * (F T - F S) ≤ (B : ℝ) * (marginal F S u + 2 * ε) := by
  have hm : 0 ≤ marginal F S u := sub_nonneg.mpr (hmono (Finset.subset_insert u S))
  have hw := hweak S T
  have hu := mul_le_mul_of_nonneg_left (sub_le_sub_right (hmono (Finset.subset_union_right : T ⊆ S ∪ T)) (F S)) hγ
  have hs := Finset.sum_le_sum hgreedy
  have hc : (T \ S).card ≤ B := (Finset.card_le_card Finset.sdiff_subset).trans hcard
  have hcr : ((T \ S).card : ℝ) ≤ (B : ℝ) := Nat.cast_le.mpr hc
  simp only [Finset.sum_const, nsmul_eq_mul] at hs
  exact ((hu.trans hw).trans hs).trans
    (mul_le_mul_of_nonneg_right hcr (add_nonneg hm (mul_nonneg zero_le_two hε)))

/-- A one-step gain bound is the required deficit contraction. -/
theorem progress_to_contraction {b γ ε opt current next : ℝ} (hb : 0 < b)
    (h : γ * (opt - current) ≤ b * (next - current + 2 * ε)) :
    opt - next ≤ (1 - γ / b) * (opt - current) + 2 * ε := by
  have hd := (div_le_iff₀ hb).mpr (h.trans_eq (mul_comm b _))
  rw [mul_div_right_comm] at hd
  nlinarith [hd]

/-- Stronger accumulated-error bound than the manuscript: the penalty is 2Bε.
The progress premise is provided by `weakSubmodular_progress` and
`estimatedGreedy_step` for a greedy set sequence. -/
theorem bridge_bound_of_progress (value : ℕ → ℝ) (opt γ ε : ℝ) (B : ℕ)
    (hB : 0 < B) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hε : 0 ≤ ε)
    (hopt : 0 ≤ opt) (hzero : value 0 = 0)
    (hstep : ∀ k, k < B → γ * (opt - value k) ≤
      (B : ℝ) * (value (k + 1) - value k + 2 * ε)) :
    (1 - Real.exp (-γ)) * opt - 2 * (B : ℝ) * ε ≤ value B := by
  have hb : 0 < (B : ℝ) := Nat.cast_pos.mpr hB
  have hb1 : (1 : ℝ) ≤ B := Nat.one_le_cast.mpr hB
  have hq0 : 0 ≤ 1 - γ / (B : ℝ) := sub_nonneg.mpr ((div_le_one hb).mpr (hγ1.trans hb1))
  have hq1 : 1 - γ / (B : ℝ) ≤ 1 := sub_le_self 1 (div_nonneg hγ0 hb.le)
  have hrec := contraction_bound (fun k => opt - value k) (1 - γ / (B : ℝ)) opt (2 * ε)
    hq0 hq1 (mul_nonneg zero_le_two hε)
    (le_of_eq ((congrArg (fun z => opt - z) hzero).trans (sub_zero opt))) B
    (fun k hk => progress_to_contraction hb (hstep k hk))
  have hgeom := geometric_le_exp (γ / (B : ℝ)) hq0 B
  simp only [neg_mul, mul_comm (B : ℝ), div_mul_cancel₀ γ hb.ne'] at hgeom
  nlinarith [mul_le_mul_of_nonneg_right hgeom hopt]

/-- Set-function bridge guarantee for every feasible comparator T.
Uniformly accurate estimated greedy gains imply `hgreedy` by `estimatedGreedy_step`.
Taking T optimal gives the oracle comparison. -/
theorem weakSubmodular_greedy_bound {α : Type*} [DecidableEq α]
    (F : Finset α → ℝ) (S : ℕ → Finset α) (u : ℕ → α) (T : Finset α)
    (γ ε : ℝ) (B : ℕ) (hB : 0 < B) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hε : 0 ≤ ε) (hmono : Monotone F) (hweak : WeakSubmodular F γ)
    (hF0 : F ∅ = 0) (hS0 : S 0 = ∅) (hcard : T.card ≤ B)
    (hnext : ∀ k, k < B → S (k + 1) = insert (u k) (S k))
    (hgreedy : ∀ k, k < B → ∀ v ∈ T \ S k,
      marginal F (S k) v ≤ marginal F (S k) (u k) + 2 * ε) :
    (1 - Real.exp (-γ)) * F T - 2 * (B : ℝ) * ε ≤ F (S B) := by
  exact bridge_bound_of_progress (fun k => F (S k)) (F T) γ ε B hB hγ0 hγ1 hε
    ((le_of_eq hF0.symm).trans (hmono (Finset.empty_subset T)))
    ((congrArg F hS0).trans hF0)
    (fun k hk => by simpa only [marginal, ← hnext k hk] using
      weakSubmodular_progress F γ ε (S k) T (u k) B hmono hweak hγ0 hε hcard (hgreedy k hk))

end CausalAtlas
