# Agent Instructions

Before doing substantive work in this repository, read:

- `$HOME/collaboration-protocol.md`

Use it as active collaboration context, especially after compaction or resume.

## Lean Is Code: Core-Patching Workflow

Think of Lean more like coding and less like doing mathematics from scratch.
When an existing proof depends on a premise that is meant to be removed,
treat it like changing Drupal core:

1. Preserve a clean, committed baseline and make a local copy or branch.
2. Remove the old premise at its source in the actual implementation.
3. Compile the real downstream proof and use the resulting type errors as the
   work queue.
4. Fix those errors in place, one by one, recompiling after each coherent
   change, until the complete end-to-end proof builds again.

Do not prematurely replace this workflow with per-prime certificates,
provider structures, standalone harnesses, or an argument that the requested
change is mathematically difficult. A harness may document or regress the
work, but it is not a substitute for patching the real proof. First perform
the dependency surgery and let Lean expose the exact obligations. Escalate a
genuine mathematical obstruction only after the compiler-driven repair has
reached that concrete irreducible obligation.

## Git Commit Wrapper

When committing from Codex, use the guarded wrapper:

```bash
../tools/codex-git-commit -m "Commit message" -- path [path ...]
```

Commit coherent chunks often. Pass only explicit files; do not use broad
pathspecs such as `.` or directories. The wrapper refuses pre-staged changes,
checks the staged diff, and creates a normal commit.
