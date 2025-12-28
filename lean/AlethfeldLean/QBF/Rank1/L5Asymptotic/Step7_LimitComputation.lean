/-
  AlethfeldLean.QBF.Rank1.L5Asymptotic.Step7_LimitComputation

  Step 7: Limit Computation

  Alethfeld Verified Proof | Graph: L5-asymptotic-expanded v52
  EDN Nodes: :L5-step4-6 through :L5-step4-9a
  Status: CLEAN

  This file proves the individual limits and combines them:
  - lim_{n->inf} 2/(n * ln 2) = 0
  - lim_{n->inf} 4/n = 0
  - lim_{n->inf} epsilon_n = 0
  - lim_{n->inf} g(n) = 0 + 4 - 0 + 0 = 4

  Key result (L5-step4-9):
    lim_{n->inf} g(n) = 4
-/
import AlethfeldLean.QBF.Rank1.L5Asymptotic.Step6_Cancellation

namespace Alethfeld.QBF.Rank1.L5Asymptotic

open scoped BigOperators
open Real Filter Topology

/-! ## L5-step4-6: lim 2/(n * ln 2) = 0 -/

/-- L5-step4-6a: lim_{n->inf} c/n = 0 for any constant c. -/
theorem tendsto_const_div_n (c : ℝ) :
    Tendsto (fun n : ℕ => c / n) atTop (nhds 0) := by
  have h := tendsto_const_div_atTop_nhds_zero_nat c
  convert h using 1
  ext n
  simp [div_eq_mul_inv]

/-- L5-step4-6: As n -> infinity: 2/(n * ln 2) -> 0. -/
theorem lim_entropy_coeff :
    Tendsto (fun n : ℕ => 2 / (n * Real.log 2)) atTop (nhds 0) := by
  have hlog : Real.log 2 > 0 := Real.log_pos (by norm_num)
  have h := tendsto_const_div_n (2 / Real.log 2)
  convert h using 1
  ext n
  field_simp

/-! ## L5-step4-7: lim 4/n = 0 -/

/-- L5-step4-7: As n -> infinity: 4/n -> 0. -/
theorem lim_four_div_n :
    Tendsto (fun n : ℕ => (4 : ℝ) / n) atTop (nhds 0) :=
  tendsto_const_div_n 4

/-! ## L5-step4-8: lim epsilon_n = 0 -/

/-- L5-step4-8a: 2^{1-n} = 2/2^n and 2^n -> infinity, so 2/2^n -> 0. -/
theorem lim_two_pow :
    Tendsto (fun n : ℕ => (2 : ℝ)^n) atTop atTop :=
  tendsto_pow_atTop_atTop_of_one_lt (by norm_num)

/-- L5-step4-8: As n -> infinity: epsilon = 2^{1-n} -> 0. -/
theorem lim_epsilon :
    Tendsto epsilon atTop (nhds 0) := epsilon_tendsto_zero

/-! ## L5-step4-9: lim g(n) = 4 -/

/-- L5-step4-9a: lim(a + b + c) = lim a + lim b + lim c when all limits exist. -/
theorem limit_sum {f g h : ℕ → ℝ} {a b c : ℝ}
    (hf : Tendsto f atTop (nhds a))
    (hg : Tendsto g atTop (nhds b))
    (hh : Tendsto h atTop (nhds c)) :
    Tendsto (fun n => f n + g n + h n) atTop (nhds (a + b + c)) :=
  hf.add (hg.add hh)

/-- The main terms 2/(n*ln2) + 4 - 4/n converge to 4. -/
theorem lim_main_terms :
    Tendsto (fun n : ℕ => 2 / (n * Real.log 2) + 4 - 4 / n) atTop (nhds 4) := by
  have h1 := lim_entropy_coeff
  have h2 := lim_four_div_n
  have h := h1.add (tendsto_const_nhds.sub h2)
  convert h using 1
  · ext n; ring
  · ring

/-- The error term tends to 0 since it's bounded by 20 * epsilon. -/
theorem error_tendsto_zero :
    Tendsto (fun n : ℕ => 20 * epsilon n) atTop (nhds 0) := by
  have h := lim_epsilon
  have h' := h.const_mul 20
  convert h' using 1
  simp

/-- g(n) for large n is close to 2/(n*ln2) + 4 - 4/n. -/
theorem g_close_to_explicit {n : ℕ} (hn : n ≥ 2) :
    |g n - (2 / (n * Real.log 2) + 4 - 4/n)| ≤ 20 * epsilon n := by
  obtain ⟨R, hR, hg⟩ := g_final_form hn
  rw [hg]
  simp only [add_sub_cancel_left]
  exact hR

/-- L5-step4-9 (Main Result): lim_{n->inf} g(n) = 4.

    By limit arithmetic: lim g(n) = 0 + 4 - 0 + 0 = 4. -/
theorem g_tendsto_four :
    Tendsto g atTop (nhds 4) := by
  -- Strategy: g(n) = main_terms(n) + error(n) where
  -- main_terms -> 4 and |error| <= 20 * epsilon -> 0
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Get N₁ such that main terms are within ε/2 of 4
  have hmain := lim_main_terms
  rw [Metric.tendsto_atTop] at hmain
  obtain ⟨N₁, hN₁⟩ := hmain (ε/2) (by linarith)
  -- Get N₂ such that error is within ε/2
  have herr := error_tendsto_zero
  rw [Metric.tendsto_atTop] at herr
  obtain ⟨N₂, hN₂⟩ := herr (ε/2) (by linarith)
  -- Take N = max(N₁, N₂, 2)
  use max (max N₁ N₂) 2
  intro n hn
  have hn1 : n ≥ N₁ := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hn)
  have hn2 : n ≥ N₂ := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hn)
  have hn3 : n ≥ 2 := le_trans (le_max_right _ _) hn
  -- Use triangle inequality
  calc dist (g n) 4
      = |g n - 4| := Real.dist_eq (g n) 4
    _ = |(g n - (2 / (n * Real.log 2) + 4 - 4/n)) + ((2 / (n * Real.log 2) + 4 - 4/n) - 4)| := by ring_nf
    _ ≤ |g n - (2 / (n * Real.log 2) + 4 - 4/n)| + |(2 / (n * Real.log 2) + 4 - 4/n) - 4| := abs_add _ _
    _ ≤ 20 * epsilon n + |2 / (n * Real.log 2) + 4 - 4/n - 4| := by
        apply add_le_add (g_close_to_explicit hn3) (le_refl _)
    _ < ε/2 + ε/2 := by
        apply add_lt_add
        · calc 20 * epsilon n = |20 * epsilon n - 0| := by simp [abs_of_pos, mul_pos, epsilon_pos]
            _ = dist (20 * epsilon n) 0 := by rw [Real.dist_eq]
            _ < ε/2 := hN₂ n hn2
        · have : dist (2 / (n * Real.log 2) + 4 - 4/n) 4 < ε/2 := hN₁ n hn1
          rwa [Real.dist_eq] at this
    _ = ε := by ring

end Alethfeld.QBF.Rank1.L5Asymptotic
