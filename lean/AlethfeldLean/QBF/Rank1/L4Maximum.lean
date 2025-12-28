/-
  AlethfeldLean.QBF.Rank1.L4Maximum

  Lemma L4: Maximum at Magic State

  Alethfeld Verified Proof
  Status: IN PROGRESS | Taint: CLEAN

  Key Result: The ratio S/I is maximized when all qubits are in the
  magic state (x², y², z²) = (1/3, 1/3, 1/3).

  Since I = n·2^{1-n} is constant (L2), maximizing S/I reduces to maximizing S.
  By L3, S depends on Bloch vectors only through Σₖ fₖ where fₖ = H(xₖ², yₖ², zₖ²).
  By Shannon's maximum entropy principle, each fₖ ≤ log₂(3) with equality
  iff the distribution is uniform, i.e., (xₖ², yₖ², zₖ²) = (1/3, 1/3, 1/3).
-/
import AlethfeldLean.QBF.Rank1.L3Entropy
import AlethfeldLean.QBF.Rank1.ShannonLemma
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases

namespace Alethfeld.QBF.Rank1.L4Maximum

open scoped Matrix ComplexConjugate BigOperators
open Real Alethfeld.Quantum Alethfeld.Quantum.Pauli Alethfeld.Quantum.Bloch
open Alethfeld.QBF.Rank1.L2Influence Alethfeld.QBF.Rank1.L3Entropy
open Alethfeld.QBF.Rank1.ShannonLemma

variable {n : ℕ}

/-! ## Magic State Definition -/

/-- The "magic state" Bloch vector (1/√3, 1/√3, 1/√3) -/
def magicBlochVector : BlochVector where
  x := 1 / Real.sqrt 3
  y := 1 / Real.sqrt 3
  z := 1 / Real.sqrt 3
  norm_sq := by
    field_simp
    rw [Real.sq_sqrt (by norm_num)]
    norm_num

/-- Predicate for being the magic state -/
def isMagicState (v : BlochVector) : Prop :=
  v.x^2 = 1/3 ∧ v.y^2 = 1/3 ∧ v.z^2 = 1/3

lemma magic_q_one : magicBlochVector.q 1 = 1/3 := by
  unfold BlochVector.q magicBlochVector
  simp only [Fin.isValue, Fin.val_one, ↓reduceIte]
  field_simp
  rw [Real.sq_sqrt (by norm_num)]

lemma magic_q_two : magicBlochVector.q 2 = 1/3 := by
  unfold BlochVector.q magicBlochVector
  simp only [Fin.isValue, Fin.reduceFinMk, Fin.reduceLT, Fin.val_two, ↓reduceIte]
  field_simp
  rw [Real.sq_sqrt (by norm_num)]

lemma magic_q_three : magicBlochVector.q 3 = 1/3 := by
  unfold BlochVector.q magicBlochVector
  simp only [Fin.isValue, Fin.reduceFinMk, Fin.reduceLT, ↓reduceIte]
  field_simp
  rw [Real.sq_sqrt (by norm_num)]

lemma magic_q_pos (i : Fin 4) (hi : i ≠ 0) : magicBlochVector.q i > 0 := by
  fin_cases i
  · contradiction -- i=0
  · rw [magic_q_one]; norm_num
  · rw [magic_q_two]; norm_num
  · rw [magic_q_three]; norm_num

/-- Bloch entropy at magic state equals log₂(3) -/
theorem blochEntropy_magic : blochEntropy magicBlochVector = log2 3 := by
  unfold blochEntropy
  rw [magic_q_one, magic_q_two, magic_q_three]
  exact uniform_achieves_max

/-! ## Bloch Entropy Bound -/

/-- L4-step4: Bloch entropy is bounded by log₂(3) -/
theorem bloch_entropy_bound (v : BlochVector) : blochEntropy v ≤ log2 3 := by
  unfold blochEntropy
  -- The squared Bloch components form a probability distribution on 3 outcomes
  have hsum : v.q 1 + v.q 2 + v.q 3 = 1 := by
    unfold BlochVector.q
    simp only [Fin.isValue, ↓reduceIte, Fin.reduceFinMk, Fin.reduceLT, Fin.val_one, Fin.val_two]
    have := v.norm_sq
    linarith
  have h1 : v.q 1 ≥ 0 := BlochVector.q_nonneg v 1
  have h2 : v.q 2 ≥ 0 := BlochVector.q_nonneg v 2
  have h3 : v.q 3 ≥ 0 := BlochVector.q_nonneg v 3
  exact shannon_max_uniform (v.q 1) (v.q 2) (v.q 3) h1 h2 h3 hsum

/-! ## Equality Characterization -/

/-- L4-step4: Bloch entropy equals log₂(3) iff magic state -/
theorem bloch_entropy_max_iff (v : BlochVector) :
    blochEntropy v = log2 3 ↔ isMagicState v := by
  constructor
  · -- If blochEntropy = log₂(3), then v is magic state
    intro h
    unfold blochEntropy at h
    have hsum : v.q 1 + v.q 2 + v.q 3 = 1 := by
      unfold BlochVector.q
      simp only [Fin.isValue, ↓reduceIte, Fin.reduceFinMk, Fin.reduceLT, Fin.val_one, Fin.val_two]
      have := v.norm_sq
      linarith
    have h1 : v.q 1 ≥ 0 := BlochVector.q_nonneg v 1
    have h2 : v.q 2 ≥ 0 := BlochVector.q_nonneg v 2
    have h3 : v.q 3 ≥ 0 := BlochVector.q_nonneg v 3
    have h_iff := shannon_max_uniform_iff (v.q 1) (v.q 2) (v.q 3) h1 h2 h3 hsum
    rw [h] at h_iff
    simp only [true_iff] at h_iff
    unfold isMagicState
    rcases h_iff with ⟨h_eq1, h_eq2, h_eq3⟩
    -- Convert 1/3 to 3⁻¹ if needed or just exact match
    constructor; convert h_eq1; norm_num
    constructor; convert h_eq2; norm_num
    convert h_eq3; norm_num
  · -- If v is magic state, then blochEntropy = log₂(3)
    intro hmagic
    unfold isMagicState at hmagic
    rcases hmagic with ⟨h1, h2, h3⟩
    unfold blochEntropy
    -- Manually unfold BlochVector.q for the rewrite pattern match to work
    have hq1 : v.q 1 = 1/3 := by unfold BlochVector.q; simp; convert h1; norm_num
    have hq2 : v.q 2 = 1/3 := by unfold BlochVector.q; simp; convert h2; norm_num
    have hq3 : v.q 3 = 1/3 := by unfold BlochVector.q; simp; convert h3; norm_num
    rw [hq1, hq2, hq3]
    exact uniform_achieves_max

/-! ## Main Theorem: Maximum at Magic State -/

/-- L4: The maximum Bloch entropy is achieved at the magic state. -/
theorem max_at_magic_state (v : BlochVector) :
    blochEntropy v ≤ blochEntropy magicBlochVector := by
  rw [blochEntropy_magic]
  exact bloch_entropy_bound v

/-- L4 (uniqueness): The maximum is achieved ONLY at the magic state. -/
theorem max_iff_magic_state (v : BlochVector) :
    blochEntropy v = blochEntropy magicBlochVector ↔ isMagicState v := by
  rw [blochEntropy_magic]
  exact bloch_entropy_max_iff v

end Alethfeld.QBF.Rank1.L4Maximum