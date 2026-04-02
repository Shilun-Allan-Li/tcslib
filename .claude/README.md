# lean_claude — Lean 4 Proof Assistant for Claude Code

A multi-agent system for writing Lean 4 proofs incrementally using **sorry-driven development**, without hitting token limits.

## Installation

```bash
cp -r lean_claude /path/to/your/lean/project/.claude
```

Or merge into an existing `.claude` directory:
```bash
cp -r lean_claude/agents/* /path/to/project/.claude/agents/
cp -r lean_claude/commands/* /path/to/project/.claude/commands/
# Merge CLAUDE.md into your existing .claude/CLAUDE.md
```

Your project should already have `lakefile.lean` (or `lakefile.toml`) and `import Mathlib`. If not, the agents will fall back to standalone `lean file.lean` invocations.

## What's Included

```
.claude/
├── CLAUDE.md                   ← System overview + Lean 4 tactic cheatsheet
├── agents/
│   ├── lean-orchestrator.md    ← Writes sorry-skeleton, manages OUTLINE.md
│   ├── lean-prover.md          ← Fills one sorry stub, verifies with lean
│   ├── lean-searcher.md        ← Finds Mathlib lemmas via exact?/apply?/name search
│   ├── lean-checker.md         ← Runs lean, parses errors, maps to sorry stubs
│   └── lean-formatter.md       ← Converts papers to Lean-ready markdown
└── commands/
    ├── lean-prove.md           ← /lean-prove
    ├── lean-step.md            ← /lean-step
    ├── lean-search.md          ← /lean-search
    ├── lean-check.md           ← /lean-check
    └── lean-status.md          ← /lean-status
```

## Core Concept: Sorry-Driven Development

Lean's `sorry` tactic closes any goal instantly. This lets you:

1. **Write the full proof skeleton first** — all `have`, `calc`, `induction` blocks present, all leaves `sorry`'d
2. **Verify the structure typechecks** before writing any real tactics
3. **Fill in one sorry at a time** — each agent invocation handles ~20 tactic lines
4. **Always have a compilable file** — you can check progress at any time

```lean
-- The skeleton: typechecks immediately
theorem foo (n m : ℕ) (h : n < m) : n + 1 ≤ m := by
  have h1 : n + 1 ≤ n + 1 := by sorry  -- SORRY #01
  have h2 : n + 1 ≤ m    := by sorry  -- SORRY #02
  exact h2

-- After /lean-step 1:
theorem foo (n m : ℕ) (h : n < m) : n + 1 ≤ m := by
  have h1 : n + 1 ≤ n + 1 := le_refl _  -- ✓ filled
  have h2 : n + 1 ≤ m    := by sorry  -- SORRY #02
  exact h2
```

## Typical Workflow

```bash
# 0. Optional: format a reference paper first
/lean-format-paper papers/source/reference.pdf

# 1. Start the proof (creates sorry-skeleton in lean_proof/Main.lean)
/lean-prove "theorem inf_primes : ∀ n : ℕ, ∃ p, p > n ∧ Nat.Prime p"

# 2. Check the skeleton compiles
/lean-check

# 3. See the plan
/lean-status

# 4. Fill stubs one by one
/lean-step 1     # prover fills SORRY #01, runs lean to verify
/lean-step 2     # fills SORRY #02
...

# 5. If stuck on a step, search Mathlib
/lean-search "prime greater than any natural number"
/lean-step 3     # retry with search results in context

# 6. If a step is too large, split it
/lean-step split 4

# 7. Check full status at any time
/lean-status
/lean-check

# 8. Done when lean-check shows 0 errors, 0 sorrys
```

## Runtime Files

```
lean_proof/
  Main.lean         ← The live Lean file (always compilable)
  OUTLINE.md        ← Sorry stubs with [ ] / [x] tracking
  search_log.md     ← Mathlib lemma search cache
  error_log.md      ← Error history (prevents repeating failed approaches)
  archive/          ← Previous proofs (/lean-prove --reset)
papers/
  *.md              ← Lean-ready formatted papers
```

## Requirements

- Lean 4 installed: `curl https://elan.lean-lang.org/elan-init.sh -sSf | sh`
- Mathlib: add `require mathlib from git "https://github.com/leanprover-community/mathlib4"` to `lakefile.lean`
- Or use the Mathlib project template: `lake +leanprover/lean4:stable new my_project math`
