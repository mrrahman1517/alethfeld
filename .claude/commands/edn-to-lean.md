---
allowed-tools: Read, Grep, Glob, Bash, Edit, Write, Task
description: Convert EDN proof to Lean 4 formalization
---

# EDN to Lean 4 Conversion

Convert an Alethfeld EDN proof to a Lean 4 formalization.

## Input

User provides path to an EDN proof file.

## Process

### 1. Parse EDN Structure

Read the EDN file and extract:
- `:theorem` - the main claim
- `:symbols` - type declarations
- `:assumptions` - hypotheses
- `:steps` - proof structure
- `:qed` - final conclusion

### 2. Map to Lean Types

| EDN Type | Lean Type |
|----------|-----------|
| `ℝ` | `Real` or `ℝ` |
| `ℕ` | `Nat` or `ℕ` |
| `X → Y` | `X → Y` |
| `Matrix m n R` | `Matrix (Fin m) (Fin n) R` |
| `Operator H` | `H →L[ℂ] H` |

### 3. Generate Lean Structure

```lean
import Mathlib
-- imports based on types used

namespace <ProofName>

-- Definitions from :definitions
def ... := ...

-- Main theorem from :theorem
theorem main_theorem
    (assumptions from :assumptions) :
    <theorem statement> := by
  -- tactics derived from :steps
  sorry -- initially, then fill in
```

### 4. Map Proof Steps to Tactics

| EDN Justification | Lean Tactic |
|-------------------|-------------|
| `:definition-expansion` | `unfold`, `simp only [def]` |
| `:substitution` | `rw`, `conv` |
| `:modus-ponens` | `apply`, `exact` |
| `:algebraic-rewrite` | `ring`, `field_simp` |
| `:case-split` | `cases`, `rcases`, `by_cases` |
| `:induction-step` | `induction` |
| `:contradiction` | `by_contra`, `absurd` |
| `:admitted` | `sorry` |

### 5. Output

Create the Lean file at `lean/AlethfeldLean/<appropriate-path>.lean`

Include:
- Module docstring with theorem statement
- All necessary imports
- Type signatures matching EDN symbols
- Proof skeleton with `sorry` where needed
- Comments linking to EDN step IDs

### 6. Verify

```bash
cd lean && lake build <module-path>
```

Report any type errors and fix them before finishing.
