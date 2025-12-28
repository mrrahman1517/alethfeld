# Pickup Prompt: L2 Sorry Elimination

## Quick Start

```bash
cd /home/tobiasosborne/Projects/alethfeld/lean
bd ready                    # See 9 issues ready to work
bd show <id>                # View issue details with proof strategy
lake build                  # Verify current state compiles
```

## Context

You're working on **Alethfeld**, a Lean 4 formalization of quantum Boolean function analysis. The L2 module (`L2Influence.lean`) proves that the **influence of rank-1 product state QBFs is universal**: I(U) = n * 2^{1-n}, independent of Bloch vectors.

The module compiles but has **4 sorries** that need elimination. A detailed plan with 14 issues has been created.

## Current State

- **File**: `lean/AlethfeldLean/QBF/Rank1/L2Influence.lean`
- **Build**: Compiles successfully (4 sorry warnings)
- **Issues**: 14 open, 9 ready to work, 5 blocked by dependencies

## The 4 Sorries

| Line | Theorem | Difficulty | Track |
|------|---------|------------|-------|
| 81 | `factorization_lemma` | Hard | 1 |
| 90 | `partial_sum_simplified` | Medium | 2 |
| 107 | `influence_j_formula` | Medium | 3 |
| 141 | `influence_decreasing` | Easy | 4 |

## Dependency Graph

```
Track 1 (factorization_lemma):
  S1a: MultiIndex decomposition ─┐
  S1b: Product factorization ────┼─→ S1d: factorization_lemma
  S1c: Sum-product interchange ──┘

Track 2 (partial_sum_simplified):
  S2a: Cardinality complement ───┐
  S2b: Product of constant ──────┼─→ S2d: partial_sum_simplified
  S2c: Exponent arithmetic ──────┤         (depends on S1d)
                                 └─────────┘

Track 3 (influence_j_formula):
  S3a: Rewrite as sum ───────────┐
  S3b: Factor out power ─────────┼─→ S3c: influence_j_formula
                                 │         (depends on S2d)
                                 └─────────┘

Track 4 (influence_decreasing) - INDEPENDENT:
  S4a: n ≤ 2^{n-1} ──→ S4b: Real conversion ──→ S4c: influence_decreasing
```

## Ready Issues (Start Here)

Run `bd ready` to see all. Key ones:

### Track 1 (Critical Path)
- **`alethfeld-xqg`**: MultiIndex decomposition - reindex sum over {α | α_j = ℓ}
- **`alethfeld-loh`**: Product factorization when α_j is fixed
- **`alethfeld-hy2`**: Apply Fintype.prod_sum (Fubini for finite sums)

### Track 4 (Independent, Easy Win)
- **`alethfeld-b0e`**: Prove n ≤ 2^{n-1} by induction (pure arithmetic)

## Recommended Approach

1. **Start with Track 4** (independent, builds confidence):
   ```bash
   bd update alethfeld-b0e --status=in_progress
   # Prove n ≤ 2^{n-1} by induction
   # Then S4b and S4c follow easily
   ```

2. **Then tackle Track 1** (hardest but unblocks everything):
   ```bash
   bd update alethfeld-xqg --status=in_progress
   # This is the key insight: decomposing MultiIndex sums
   ```

3. **Tracks 2 & 3** follow once Track 1 is done.

## Key Mathlib Lemmas You'll Need

```lean
-- For S1a (MultiIndex decomposition)
Fintype.sum_equiv          -- Reindex a sum via equivalence
Equiv.piSplitAt            -- Split Π over Fin n at index j

-- For S1c (Fubini)
Fintype.prod_sum           -- ∑_f ∏_i f(i) = ∏_i ∑_x ...

-- For S2a (Cardinality)
Fintype.card_subtype_compl -- |{x | x ≠ j}| = n - 1

-- For S2b (Product of constant)
Finset.prod_const          -- ∏_{x∈s} c = c^|s|

-- For S4a (Induction)
Nat.one_le_two_pow         -- 1 ≤ 2^n
```

## File Locations

```
lean/
├── AlethfeldLean.lean                      # Root imports
├── AlethfeldLean/
│   ├── Quantum/
│   │   ├── Basic.lean                      # Mat2, QubitMat, MultiIndex
│   │   ├── Pauli.lean                      # Pauli matrices
│   │   └── Bloch.lean                      # BlochVector, q components ← L2 uses this
│   └── QBF/Rank1/
│       ├── L1Fourier.lean                  # Fourier coefficients
│       └── L2Influence.lean                # ← YOUR TARGET FILE
├── API.md                                  # Library reference
└── test_l2_influence.lean                  # Test file
```

## Workflow

```bash
# Claim an issue
bd update <id> --status=in_progress

# Edit the file
# Add helper lemmas above the sorry
# Replace sorry with proof

# Test compilation
lake build

# When done
bd close <id> --reason="Proved theorem X using Y"
bd sync
```

## Session Close Protocol

Before ending:
```bash
git status                  # Check changes
git add <files>             # Stage code
bd sync                     # Commit beads
git commit -m "..."         # Commit code
bd sync                     # Sync again
git push                    # Push to remote
```

## Success Criteria

- All 4 sorries eliminated
- `lake build` completes with no sorry warnings in L2Influence.lean
- All 14 issues closed
- Changes pushed to remote

## Tips

1. **Read the issue descriptions** - each has detailed proof strategy
2. **Use `#check` liberally** - verify lemma types before using
3. **The q_sum lemmas are key** - `BlochVector.q_sum_eq_two` and `q_nonzero_sum_eq_one` are already proven
4. **Track 4 is standalone** - good warmup before the harder Track 1
5. **S1a is the crux** - once you decompose the MultiIndex sum, everything follows

Good luck!
