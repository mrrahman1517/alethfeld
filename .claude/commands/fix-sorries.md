---
allowed-tools: Read, Grep, Glob, Bash, Edit, Write, Task, TodoWrite
description: Systematically eliminate sorry statements from Lean 4 proofs
---

# Sorry Elimination Protocol

Systematically find and fix all `sorry` statements in the Lean 4 codebase.

## Phase 1: Discovery

1. **Run lake build** to get current state:
   ```bash
   cd lean && lake build 2>&1
   ```

2. **Find all sorries:**
   ```bash
   grep -rn "sorry" --include="*.lean" lean/AlethfeldLean/
   ```

3. **Create a todo list** with all sorry locations, ordered by dependency (fix dependencies first).

## Phase 2: Analysis

For each sorry:

1. **Read the context** - the theorem statement, available lemmas, imports
2. **Understand what needs to be proved** - the goal type
3. **Check Mathlib** for relevant lemmas that could help
4. **Identify the proof strategy:**
   - Direct computation?
   - Apply existing lemma?
   - Induction?
   - Case split?
   - Rewrite chain?

## Phase 3: Fix

For each sorry (in dependency order):

1. **Attempt the fix** using appropriate tactics:
   - `simp`, `ring`, `linarith` for arithmetic
   - `exact`, `apply`, `refine` for applying lemmas
   - `rw` for rewrites
   - `constructor`, `use` for existentials
   - `intro`, `intros` for implications/universals

2. **Build and check:**
   ```bash
   cd lean && lake build 2>&1 | head -50
   ```

3. **If successful:** Mark todo complete, move to next
4. **If stuck:** Note the issue, create a beads issue, move on

## Phase 4: Verification

After all sorries addressed:

1. **Full build:**
   ```bash
   cd lean && lake build
   ```

2. **Count remaining sorries:**
   ```bash
   grep -c "sorry" lean/AlethfeldLean/**/*.lean 2>/dev/null || echo "0"
   ```

3. **Report results**

## Output

Track progress with TodoWrite. Report:
- Total sorries found
- Sorries fixed
- Sorries remaining (with reasons)
- Build status
