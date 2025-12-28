import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import AlethfeldLean.QBF.Rank1.L3Entropy

namespace Alethfeld.QBF.Rank1.ShannonLemma

open Real Alethfeld.QBF.Rank1.L3Entropy

/-- Helper: entropyTerm for positive p -/
lemma entropyTerm_of_pos {p : ℝ} (hp : p > 0) : entropyTerm p = -p * log2 p := by
  unfold entropyTerm; simp [hp]

/-- Key lemma: For p > 0, we have -p log₂(p) ≤ p log₂(3) + (1/3 - p) / log(2)
    This follows from log(x) ≤ x - 1 applied to x = 1/(3p). -/
theorem entropyTerm_le_helper (p : ℝ) (hp : p > 0) :
    -p * log2 p ≤ p * log2 3 + (1/3 - p) / Real.log 2 := by
  sorry

/-- Strict version: For p > 0 and p ≠ 1/3, the entropy term is strictly bounded. -/
theorem entropyTerm_lt_helper (p : ℝ) (hp : p > 0) (hp_ne : p ≠ 1/3) :
    -p * log2 p < p * log2 3 + (1/3 - p) / Real.log 2 := by
  sorry

/-- Helper: entropyTerm bounds sum to log₂(3) -/
theorem entropyTerm_sum_bound (p1 p2 p3 : ℝ) (hp1 : p1 ≥ 0) (hp2 : p2 ≥ 0) (hp3 : p3 ≥ 0)
    (hsum : p1 + p2 + p3 = 1) :
    entropyTerm p1 + entropyTerm p2 + entropyTerm p3 ≤
    (p1 + p2 + p3) * log2 3 + ((1/3 - p1) + (1/3 - p2) + (1/3 - p3)) / Real.log 2 := by
  sorry

/-- Helper: -x log x is concave, so sum is maximized at uniform -/
theorem neg_mul_log_concave_sum (p1 p2 p3 : ℝ) (hp1 : p1 ≥ 0) (hp2 : p2 ≥ 0) (hp3 : p3 ≥ 0)
    (hsum : p1 + p2 + p3 = 1) :
    entropyTerm p1 + entropyTerm p2 + entropyTerm p3 ≤ log2 3 := by
  -- Use the helper to get the bound with residual term
  have hbound := entropyTerm_sum_bound p1 p2 p3 hp1 hp2 hp3 hsum
  -- The residual term (1/3 - p1) + (1/3 - p2) + (1/3 - p3) = 1 - (p1 + p2 + p3) = 0
  have hresidual : (1/3 - p1) + (1/3 - p2) + (1/3 - p3) = 0 := by linarith
  -- And (p1 + p2 + p3) * log2 3 = log2 3
  rw [hsum, hresidual] at hbound
  simp at hbound
  exact hbound

/-- Shannon entropy is maximized by uniform distribution -/
theorem shannon_max_uniform (p1 p2 p3 : ℝ) (hp1 : p1 ≥ 0) (hp2 : p2 ≥ 0) (hp3 : p3 ≥ 0)
    (hsum : p1 + p2 + p3 = 1) :
    entropyTerm p1 + entropyTerm p2 + entropyTerm p3 ≤ log2 3 :=
  neg_mul_log_concave_sum p1 p2 p3 hp1 hp2 hp3 hsum

/-- Strict inequality for Shannon entropy when not uniform. -/
theorem entropyTerm_sum_lt (p1 p2 p3 : ℝ) (hp1 : p1 ≥ 0) (hp2 : p2 ≥ 0) (hp3 : p3 ≥ 0)
    (hsum : p1 + p2 + p3 = 1) (hne : p1 ≠ 1/3 ∨ p2 ≠ 1/3 ∨ p3 ≠ 1/3) :
    entropyTerm p1 + entropyTerm p2 + entropyTerm p3 < log2 3 := by
  sorry

/-- Uniform distribution achieves maximum: H(1/3, 1/3, 1/3) = log₂(3) -/
theorem uniform_achieves_max :
    entropyTerm (1/3) + entropyTerm (1/3) + entropyTerm (1/3) = log2 3 := by
  have one_third_pos : (1:ℝ)/3 > 0 := by norm_num
  have log2_one_third : log2 (1/3) = -log2 3 := by
    unfold log2
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub]
    field_simp
  simp only [entropyTerm_of_pos one_third_pos]
  rw [log2_one_third]
  ring

/-- Shannon entropy maximum characterization. -/
theorem shannon_max_uniform_iff (p1 p2 p3 : ℝ) (hp1 : p1 ≥ 0) (hp2 : p2 ≥ 0) (hp3 : p3 ≥ 0)
    (hsum : p1 + p2 + p3 = 1) :
    entropyTerm p1 + entropyTerm p2 + entropyTerm p3 = log2 3 ↔
    p1 = 1/3 ∧ p2 = 1/3 ∧ p3 = 1/3 := by
  constructor
  · intro h
    by_contra hnot
    have hne : p1 ≠ 1/3 ∨ p2 ≠ 1/3 ∨ p3 ≠ 1/3 := by
      by_contra h_all_eq
      push_neg at h_all_eq
      exact hnot h_all_eq
    have hlt := entropyTerm_sum_lt p1 p2 p3 hp1 hp2 hp3 hsum hne
    linarith
  · intro ⟨h1, h2, h3⟩
    rw [h1, h2, h3]
    exact uniform_achieves_max

end Alethfeld.QBF.Rank1.ShannonLemma
