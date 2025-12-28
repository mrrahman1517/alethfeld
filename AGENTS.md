# Agent Instructions

This project uses **bd** (beads) for issue tracking. Run `bd onboard` to get started.

## Quick Reference

```bash
bd ready              # Find available work
bd show <id>          # View issue details
bd update <id> --status in_progress  # Claim work
bd close <id>         # Complete work
bd sync               # Sync with git
```

## Current Focus: L4Maximum Proofs

**Status:** BLOCKED on Mathematical Inequalities

We are currently trying to eliminate `sorry` statements from `L4Maximum.lean`. The file has been split into:
- `ShannonLemma.lean`: Contains the core mathematical inequalities ($H(p) \le \log 3$).
- `L4Maximum.lean`: Contains the quantum definitions and application of the lemma.

**Next Agent's Priority:**
1.  **Fix `ShannonLemma.lean`**: Use standard Mathlib convexity/concavity arguments instead of manual inequality manipulation with `linarith`.
2.  **Fix `L4Maximum.lean`**: Resolve `norm_sq` and index type mismatch errors.

## Landing the Plane (Session Completion)

**When ending a work session**, you MUST complete ALL steps below. Work is NOT complete until `git push` succeeds.

**MANDATORY WORKFLOW:**

1.  **File issues for remaining work** - Create issues for anything that needs follow-up
2.  **Run quality gates** (if code changed) - Tests, linters, builds
3.  **Update issue status** - Close finished work, update in-progress items
4.  **PUSH TO REMOTE** - This is MANDATORY:
    ```bash
    git pull --rebase
    bd sync
    git push
    git status  # MUST show "up to date with origin"
    ```
5.  **Clean up** - Clear stashes, prune remote branches
6.  **Verify** - All changes committed AND pushed
7.  **Hand off** - Provide context for next session

**CRITICAL RULES:**
- Work is NOT complete until `git push` succeeds
- NEVER stop before pushing - that leaves work stranded locally
- NEVER say "ready to push when you are" - YOU must push
- If push fails, resolve and retry until it succeeds