# Pickup Prompt: L4Maximum.lean Sorry Elimination (FAILED)

## Status: BLOCKED - 3 Sorries in ShannonLemma, Build Errors in L4Maximum

**Last Updated:** 2025-12-28 (Session 3)

The goal remains to eliminate all `sorry` statements from `AlethfeldLean/QBF/Rank1/L4Maximum.lean`. 
The module was split into `ShannonLemma.lean` (pure math inequalities) and `L4Maximum.lean` (quantum application) to isolate errors, but both files currently fail to build cleanly without `sorry`.

## Current Status

| Module | File | Status |
|--------|------|--------|
| **Math** | `ShannonLemma.lean` | ❌ 3 `sorry`s (Inequalities failing to prove) |
| **Quantum** | `L4Maximum.lean` | ❌ Build Errors (Definitions & Type Mismatches) |

## Session Summary (Dec 28, 2025 - Session 3)

**Attempted Strategy**:
1.  **Refactoring**: Split `L4Maximum.lean` into a dedicated math module `ShannonLemma.lean` for the entropy bounds ($H(p) \le \log 3$) and the original file for quantum definitions.
2.  **Inequality Proofs**: Tried proving `-p log p \le ...` using `linarith`, `nlinarith`, and `positivity`.
    - **Result**: `linarith` failed to handle the non-linear `log` terms even with hypothesis preprocessing. `nlinarith` also failed.
3.  **Quantum Definitions**: Tried to define `magicBlochVector` and `isMagicState` cleanly.
    - **Result**: `norm_sq` proof for `magicBlochVector` fails due to `div_pow` pattern matching issues with `1 / Real.sqrt 3`.
    - `magic_q_pos` fails due to `Fin` index handling (`Fin 3` vs `Fin 4` mismatch in `fin_cases`).
    - `bloch_entropy_max_iff` fails due to type mismatches between `1/3` (division) and `3⁻¹` (inverse) when using `norm_num`.

## Detailed Failure Report

### 1. `ShannonLemma.lean` (Mathematical Core)
- **Goal**: Prove that $\sum -p_i \log_2 p_i \le \log_2 3$ for $\sum p_i = 1$.
- **Current State**: Contains 3 `sorry` statements.
- **Failures**:
  - `entropyTerm_le_helper`: Proving $-p \log_2 p \le p \log_2 3 + (1/3 - p)/\ln 2$ is proving difficult. The inequality `log x \le x - 1` was invoked, but the algebraic manipulation to bring it to the final form failed with automated tactics.
  - `entropyTerm_sum_bound`: Summing the inequalities fails because `linarith` doesn't see through the `entropyTerm` definition (which has an `if` split for $p > 0$).

### 2. `L4Maximum.lean` (Quantum Application)
- **Goal**: Apply `ShannonLemma` to Bloch vectors.
- **Current Errors**:
  - `magicBlochVector`: The `norm_sq` field proof fails. `rw [div_pow]` cannot find `(1 / sqrt 3) ^ 2`.
  - `magic_q_pos`: `fin_cases i` is used on `i : Fin 4`, but the lemma logic was seemingly written for `Fin 3` or had index mismatch errors.
  - `bloch_entropy_max_iff`: `rw [h1]` where `h1 : v.x^2 = 1/3` fails because the target term might be `(3 : ℝ)⁻¹` or have slightly different structure after simplification.

## Recommended Next Steps for the Next Agent

1.  **Fix `ShannonLemma.lean` First**:
    - Do **not** rely on `linarith` for the main concavity argument.
    - Use `Mathlib.Analysis.Convex.SpecificFunctions.Basic`.
    - Specifically, use the strict concavity of `x \mapsto -x \log x`.
    - Look for `Real.strictConcaveOn_neg_mul_log` or similar in Mathlib.
    - Prove that the sum of strictly concave functions is maximized at the centroid (uniform distribution).

2.  **Fix `L4Maximum.lean` Definitions**:
    - **`magicBlochVector`**: Proof of `norm_sq` should be explicit:
      ```lean
      have : (1 / Real.sqrt 3) ^ 2 = 1 / 3 := by rw [div_pow, one_pow, Real.sq_sqrt (by norm_num)]; field_simp
      rw [this]
      ring
      ```
    - **`magic_q_pos`**: Be very explicit with indices. `BlochVector.q` maps `0 \to 1`, `1 \to x^2`, etc.
      ```lean
      fin_cases i
      · simp [BlochVector.q]; norm_num -- i=0
      · simp [BlochVector.q, magicBlochVector]; ...
      ```
    - **Type Casting**: When equating `1/3`, ensure consistency. Use `(3 : ℝ)⁻¹` if `field_simp` produces it, or force `1/3` with `norm_num`.

3.  **Merge Strategy**:
    - Once `ShannonLemma` compiles *without sorries*, verify `L4Maximum` imports it correctly.
    - Do not try to solve everything in one file if the math is heavy. Keep the split.

## Files to Edit
- `lean/AlethfeldLean/QBF/Rank1/ShannonLemma.lean`
- `lean/AlethfeldLean/QBF/Rank1/L4Maximum.lean`

## Build Command
```bash
lake build AlethfeldLean.QBF.Rank1.ShannonLemma
lake build AlethfeldLean.QBF.Rank1.L4Maximum
```

