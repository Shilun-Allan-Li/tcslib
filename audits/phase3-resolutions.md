# Phase 3 — audit loop resolutions (CLOSED)

Protocol: `AroraBarakChapter1Plan.md` §5 "Audit protocol". External auditor:
cross-vendor LLM per decision log. This loop also covered **fill round 1** (the 20
proof completions of commit `f8621285`).

## Round 1 (`phase3-pack.md` → `phase3-findings.md`, audited at `f8621285`)

**Two blockers** on the phase-3 statements, three majors, two minors, five notes;
the fill round and its 16 new supporting declarations were audited clean
(findings 9-13). All accepted; resolved in commit `afe5c3ea`:

| Finding | Resolution |
|---|---|
| 1 blocker — algebraic `MachineCode` admits noncomputable-meaning schemes (Argument A); no universal machine can exist relative to them | `EffectiveMachineCode`: an in-model canonizer computing the **fixed, scheme-independent** `CodeTM.serialize` (new concrete definition). Key subtlety, verified both rounds: canonizing into the scheme's *own* `encode` does not exclude the pathology — the fixed target format is essential |
| 2 blocker — input-first `pairEncode x α` layout falsifies all three time bounds (Argument B) | **Code-first layout** `pairEncode α x` (and `pairEncode (pairEncode ⌞t⌟ α) x` for the timed machine); startup is α-dependent and absorbed into `C`; deviation from [AB09]'s `⟨x, α⟩` documented |
| 3 major — no all-string evaluator; divergence not preserved | `universal` restated as `U(x, α) = M_α(x)` over `c.decode` with the completed-output converse |
| 4 major — quadratic theorem mislabeled | Labeled total-function corollary; machine-level partial statement is `universal` |
| 5 major — serialization omitted `q₀` | `serialize` records the initial state (distinct machines no longer collide) |
| 6, 8 minors/notes | Deadline-inclusive timeout documented; `pairEncode_injective` added with the aligned-parser sketch |

## Round 2 (`phase3-reaudit-pack.md` → `phase3-reaudit-findings.md`, audited at `afe5c3ea`)

**Zero blockers, zero majors.** Both round-1 counterexamples re-run and formally
excluded: the auditor proved `serialize` is injective and prefix-free from its parse
grammar, derived the decision procedure showing Argument A's scheme cannot carry a
canonizer, and re-did the startup arithmetic showing the code-first bounds need no
input-length term. The α-dependent constant was confirmed *necessary* (Argument E),
and Argument F supplies complete proof blueprints for phase 4's `UC` diagonalization
and `HALT → UC` reduction, identifying the one missing API piece. Two minors,
resolved in the closing commit:

| Finding | Resolution |
|---|---|
| 3 minor — sketch must emulate the simulated input's **left boundary** (the cell left of the verbatim `x` region is the delimiter's `true`, not blank) | Sketch now specifies the virtual-boundary marker tape, the clamp mirroring `moveInputPos`, and the empty-input case |
| 11 minor — "no leading `false`s" description of `Nat.bits` inaccurate | Corrected to "least-significant-bit first, no redundant most-significant zeros; `Nat.bits 0 = []`" |
| 4, 6 notes — converse wording; α-dependence | "Completed output" wording adopted; α-dependent constant documented as a necessary, deliberate weakening of [AB09]'s machine-dependent constant |
| 8 note — parser complexity | Short-circuit/length-check made explicit in the existence sketch |
| 10 note — phase-4 API gap | Recorded in the plan: phase 4 needs a **guarded/partial composition lemma** (the total-function `computesFunInTime_comp` cannot take the partial evaluator as a component) plus the boundary-wrapper construction; no strengthening of `EffectiveMachineCode` is needed |

## Gate status

**CLOSED.** Phase 4 (uncomputability) is unblocked. Carried obligations, tracked in
the plan:

- Fill phase: 14 sorries (8 heavy phase-1/2 constructions + 6 phase-3 obligations),
  each with an audited sketch; the three phase-3 findings files contain the parse
  grammar, startup arithmetic, boundary-wrapper design, and both phase-4 proof
  blueprints (Argument F) for reuse.
- Phase 4 additionally owes: a guarded/partial composition (or guarded-simulation)
  lemma with buffered intermediate output; statements needing a *named* evaluator or
  a semantically identified code must introduce those interfaces explicitly.
- Later phases must not describe the α-dependent evaluator constant as the book's
  machine-dependent constant (round-2 finding 6).
