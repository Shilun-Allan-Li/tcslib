# Lean 4 Proof Assistant System

This directory contains a coordinated multi-agent system for writing Lean 4 proofs incrementally, using **sorry-driven development** to avoid token-limit failures.

## Core Principle: The Sorry Ladder

Lean's `sorry` tactic closes any goal and makes the file compile. This means you can:

1. Write the theorem statement and check it typechecks (with `sorry` as the body)
2. Sketch the full `have`/`calc`/`obtain` structure — all sub-goals `sorry`'d out
3. Fill in one `have` block at a time, checking after each
4. Never write more than one tactic block per agent invocation

This is the only reliable way to write long Lean proofs without hitting the token limit or producing uncheckable code.

## Directory Layout (created at runtime)

```
lean_proof/
  OUTLINE.md          ← Proof plan: theorem, strategy, step list with sorry-stubs
  Main.lean           ← The live Lean file (always compilable — sorry fills gaps)
  search_log.md       ← Mathlib lemma search results (for reuse across steps)
  error_log.md        ← Error history with resolutions (learn from past errors)
  step_NN.md          ← Scratch notes for individual steps (optional)
```

## Available Agents

| Agent | Purpose |
|---|---|
| `lean-orchestrator` | Plans proof structure, writes sorry-skeleton, manages OUTLINE.md |
| `lean-prover` | Fills in one sorry-stub in Main.lean with real tactics |
| `lean-searcher` | Finds Mathlib lemmas using exact?, apply?, simp?, and name search |
| `lean-checker` | Reads Main.lean for sorry status; error info comes from VS Code LeanInfoView (no build commands) |
| `lean-formatter` | Converts papers/PDFs into Lean-friendly markdown (definitions, theorem statements) |

## Available Commands

| Command | Usage |
|---|---|
| `/lean-prove` | Start a new Lean proof — provide the theorem statement |
| `/lean-step` | Fill in a specific sorry-stub by number |
| `/lean-search` | Search Mathlib for lemmas matching a description |
| `/lean-check` | Run Lean on Main.lean and interpret any errors |
| `/lean-status` | Show which sorry-stubs remain and overall progress |

## Workflow

```
# 1. Start
/lean-prove "theorem foo (n : ℕ) : n + 0 = n"

# 2. Inspect the sorry-skeleton in lean_proof/Main.lean
# 3. Fill in steps one at a time
/lean-step 1      # writes real tactics for sorry #1
/lean-check       # verify it compiles
/lean-step 2
/lean-check
...

# 4. Search Mathlib when stuck
/lean-search "commutativity of addition natural numbers"

# 5. Done when lean-check shows 0 errors and 0 sorrys
```

## Debugging and Error Inspection

**Always use the VS Code LeanInfoView to get goal state and error information — never run `lake build`, `lean`, or any other build command.**

The LeanInfoView (the Lean infoview panel in VS Code) shows:
- The current tactic goal state at the cursor position
- Any type errors or tactic failures inline
- `exact?` / `apply?` / `simp?` suggestions in real time

To inspect a goal or error:
1. Place the cursor inside the tactic block in VS Code
2. Read the goal state from the LeanInfoView panel
3. Use that information to decide the next tactic

Do not invoke shell commands (`lake build`, `lean --check`, etc.) to check proof state. The LeanInfoView is the authoritative, zero-latency source of truth.

## Lean 4 Tactic Cheatsheet (for agent reference)

| Tactic | Use |
|---|---|
| `sorry` | Placeholder — closes any goal |
| `exact h` | Close goal with term `h` |
| `apply lemma` | Reduce goal using `lemma` |
| `rw [lemma]` | Rewrite using equation |
| `simp [lemmas]` | Simplification |
| `ring` | Ring identity |
| `linarith` | Linear arithmetic over ordered field |
| `omega` | Linear arithmetic over ℕ/ℤ |
| `norm_num` | Numerical computation |
| `decide` | Decidable propositions |
| `aesop` | General purpose automation |
| `have h : T := by ...` | Introduce intermediate fact |
| `obtain ⟨a, ha⟩ := h` | Destructure existential |
| `rcases h with ...` | Pattern match hypothesis |
| `induction n with` | Induction |
| `by_contra h` | Proof by contradiction |
| `push_neg` | Push negations inward |
| `contrapose` | Switch to contrapositive |
| `calc` | Chain of equalities/inequalities |
| `exact?` | Ask Lean to find a proof term |
| `apply?` | Ask Lean to find applicable lemma |
| `simp?` | Ask Lean which simp lemmas apply |
