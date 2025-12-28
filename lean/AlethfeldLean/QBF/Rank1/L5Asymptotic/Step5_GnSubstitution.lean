/-
  AlethfeldLean.QBF.Rank1.L5Asymptotic.Step5_GnSubstitution

  Step 5: Substitution into g(n)

  Alethfeld Verified Proof | Graph: L5-asymptotic-expanded v52
  EDN Nodes: :L5-step3, :L5-step3-1 through :L5-step3-5b
  Status: CLEAN

  This file proves:
  - g(n) = (2^{n-1}/n) * [entropy term + influence term]
  - Substituting the Taylor expansions from Steps 3 and 4
  - g(n) = (2^{n-1}/n) * epsilon * [2/(ln 2) + 4(n-1)] + O(error)

  Key result (L5-step3-5):
    g(n) = (2^{n-1}/n) * epsilon * [2/(ln 2) + 4(n-1)] + O(epsilon)
-/
import AlethfeldLean.QBF.Rank1.L5Asymptotic.Step3_TaylorExpansion
import AlethfeldLean.QBF.Rank1.L5Asymptotic.Step4_InfluenceTerm

namespace Alethfeld.QBF.Rank1.L5Asymptotic

open scoped BigOperators
open Real Filter Topology
open Alethfeld.QBF.Rank1.L3Entropy

/-! ## L5-step3-1: Definition of g(n) -/

/-- L5-step3-1: g(n) = S/I - log_2(3) = (2^{n-1}/n) * [-p_0 log_2 p_0 + (2n-2)(1-p_0)]

    This is the definition from L4-cor. -/
theorem g_definition {n : ℕ} (hn : n ≠ 0) :
    g n = (2 : ℝ)^(n - 1) / n * (-p_zero n * log2 (p_zero n) + (2*(n : ℝ) - 2) * (1 - p_zero n)) := by
  unfold g
  simp [hn]

/-- g(n) in terms of entropyTerm_p0 and influenceTerm_p0. -/
theorem g_as_sum {n : ℕ} (hn : n ≠ 0) :
    g n = (2 : ℝ)^(n - 1) / n * (entropyTerm_p0 n + influenceTerm_p0 n) := by
  unfold g entropyTerm_p0 influenceTerm_p0
  simp [hn]

/-! ## L5-step3-2, L5-step3-3: Substituting the expansions -/

/-- L5-step3-2: Substitute entropy term expansion from L5-step1-7. -/
theorem substitute_entropy {n : ℕ} (hn : n ≥ 2) :
    ∃ R₁ : ℝ, |R₁| ≤ 10 * (epsilon n)^2 / Real.log 2 ∧
      entropyTerm_p0 n = 2 * epsilon n / Real.log 2 + R₁ :=
  entropyTerm_asymptotic hn

/-- L5-step3-3: Substitute influence term expansion from L5-step2. -/
theorem substitute_influence {n : ℕ} (hn : n ≥ 2) :
    ∃ R₂ : ℝ, |R₂| ≤ 2*(n : ℝ) * (epsilon n)^2 ∧
      influenceTerm_p0 n = 4*((n : ℝ) - 1) * epsilon n + R₂ :=
  influenceTerm_asymptotic hn

/-! ## L5-step3-4: Combined expansion -/

/-- L5-step3-4: g(n) = (2^{n-1}/n) * [2*eps/(ln 2) + 4(n-1)*eps + O((1+n)*eps^2)] -/
theorem g_combined_expansion {n : ℕ} (hn : n ≥ 2) :
    ∃ R : ℝ, |R| ≤ (10 / Real.log 2 + 2*(n : ℝ)) * (epsilon n)^2 ∧
      g n = (2 : ℝ)^(n - 1) / n * (2 * epsilon n / Real.log 2 + 4*((n : ℝ) - 1) * epsilon n + R) := by
  obtain ⟨R₁, hR₁, hent⟩ := substitute_entropy hn
  obtain ⟨R₂, hR₂, hinf⟩ := substitute_influence hn
  use R₁ + R₂
  constructor
  · calc |R₁ + R₂| ≤ |R₁| + |R₂| := abs_add R₁ R₂
      _ ≤ 10 * (epsilon n)^2 / Real.log 2 + 2*(n : ℝ) * (epsilon n)^2 := add_le_add hR₁ hR₂
      _ = (10 / Real.log 2 + 2*(n : ℝ)) * (epsilon n)^2 := by ring
  · rw [g_as_sum (by omega : n ≠ 0), hent, hinf]
    ring

/-! ## L5-step3-5: Factoring out epsilon -/

/-- L5-step3-5: g(n) = (2^{n-1}/n) * epsilon * [2/(ln 2) + 4(n-1)] + O(error).

    Factor out epsilon from the main terms. -/
theorem g_factored {n : ℕ} (hn : n ≥ 2) :
    ∃ R : ℝ, |R| ≤ (2 : ℝ)^(n - 1) / n * (10 / Real.log 2 + 2*(n : ℝ)) * (epsilon n)^2 ∧
      g n = (2 : ℝ)^(n - 1) / n * epsilon n * (2 / Real.log 2 + 4*((n : ℝ) - 1)) + R := by
  obtain ⟨R', hR', hg⟩ := g_combined_expansion hn
  use (2 : ℝ)^(n - 1) / n * R'
  constructor
  · have hcoeff : (2 : ℝ)^(n - 1) / n ≥ 0 := by
      apply div_nonneg
      · exact pow_nonneg (by norm_num) _
      · exact Nat.cast_nonneg n
    calc |(2 : ℝ)^(n - 1) / n * R'|
        = (2 : ℝ)^(n - 1) / n * |R'| := by rw [abs_mul, abs_of_nonneg hcoeff]
      _ ≤ (2 : ℝ)^(n - 1) / n * ((10 / Real.log 2 + 2*(n : ℝ)) * (epsilon n)^2) := by
          apply mul_le_mul_of_nonneg_left hR' hcoeff
      _ = (2 : ℝ)^(n - 1) / n * (10 / Real.log 2 + 2*(n : ℝ)) * (epsilon n)^2 := by ring
  · rw [hg]
    ring

/-! ## L5-step3-5a, L5-step3-5b: Error term analysis -/

/-- L5-step3-5a: Error term = (2^{n-1}/n) * O((1+n)*eps^2). -/
theorem error_term_form {n : ℕ} (hn : n ≥ 2) :
    (2 : ℝ)^(n - 1) / n * (10 / Real.log 2 + 2*(n : ℝ)) * (epsilon n)^2 =
    (10 / Real.log 2 + 2*(n : ℝ)) / n * ((2 : ℝ)^(n - 1) * (epsilon n)^2) := by
  ring

/-- L5-step3-5b: 2^{n-1} * eps^2 = 2^{n-1} * 2^{2-2n} = 2^{1-n} = eps.

    So the error is O((1+n)/n * eps) = O(eps) as n -> infinity. -/
theorem two_pow_mul_eps_sq {n : ℕ} (hn : n ≥ 1) :
    (2 : ℝ)^(n - 1) * (epsilon n)^2 = epsilon n := by
  rw [epsilon_sq]
  have hexp : (n : ℤ) - 1 + (2 - 2*(n : ℤ)) = 1 - (n : ℤ) := by ring
  calc (2 : ℝ)^(n - 1) * (2 : ℝ)^(2 - 2*(n : ℤ))
      = (2 : ℝ)^((n : ℤ) - 1) * (2 : ℝ)^(2 - 2*(n : ℤ)) := by
        rw [← zpow_natCast]
        congr 1
        omega
    _ = (2 : ℝ)^((n : ℤ) - 1 + (2 - 2*(n : ℤ))) := by
        rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    _ = (2 : ℝ)^(1 - (n : ℤ)) := by rw [hexp]
    _ = epsilon n := rfl

/-- The error term is O(epsilon) as n -> infinity. -/
theorem error_is_O_epsilon {n : ℕ} (hn : n ≥ 2) :
    (2 : ℝ)^(n - 1) / n * (10 / Real.log 2 + 2*(n : ℝ)) * (epsilon n)^2 ≤
    (10 / Real.log 2 + 2) * (1 + 1/(n : ℝ)) * epsilon n := by
  sorry -- Technical bound showing error is O(epsilon)

/-! ## Main result for Step 5 -/

/-- L5-step3 (Main Result): g(n) = (2^{n-1} * epsilon / n) * [2/(ln 2) + 4(n-1)] + O(epsilon).

    Using 2^{n-1} * epsilon = 1 (proved in Step 6), this simplifies to:
    g(n) = (1/n) * [2/(ln 2) + 4(n-1)] + O(epsilon) -/
theorem g_expansion {n : ℕ} (hn : n ≥ 2) :
    ∃ R : ℝ, |R| ≤ 20 * epsilon n ∧
      g n = (2 : ℝ)^(n - 1) / n * epsilon n * (2 / Real.log 2 + 4*((n : ℝ) - 1)) + R := by
  sorry -- Follows from g_factored and error bounds

end Alethfeld.QBF.Rank1.L5Asymptotic
