---
allowed-tools: Read, Grep, Glob, Bash
description: Quick project status check - git, build, beads, sorries
---

# Project Status Check

Quickly assess the current state of the Alethfeld project.

## Checks to Run

### 1. Git Status
```bash
git status --short
git log --oneline -3
```

### 2. Beads (Issue Tracking)
```bash
bd ready
bd stats
```

### 3. Lean Build Status
```bash
cd lean && lake build 2>&1 | tail -20
```

### 4. Sorry Count
```bash
grep -r "sorry" --include="*.lean" lean/AlethfeldLean/ 2>/dev/null | wc -l
```

### 5. Recent Changes
```bash
ls -lt lean/AlethfeldLean/QBF/Rank1/*.lean | head -5
```

## Output Format

```
PROJECT STATUS: Alethfeld
==========================

GIT:
  Branch: <branch>
  Status: <clean|dirty>
  Last commits: <recent commits>

BEADS:
  Ready issues: <n>
  In progress: <n>

LEAN:
  Build: <success|failure>
  Sorries: <n>
  Recent files: <list>

RECOMMENDED NEXT ACTION:
  <suggestion based on status>
```

Keep output concise. This is for quick orientation at session start.
