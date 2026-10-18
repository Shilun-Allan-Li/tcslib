# External audit pack — Diagonal Part 1: the parameterized time-hierarchy argument (statement gate)

Campaign: the Arora–Barak chapters 3–4 plan, §2.1 (user decision CH34-Q3, 2026-10-08: Thm 3.1 at
`f log f`). The last link of that chain re-derives the time hierarchy theorem from a two-tape
universal machine. The user decided on 2026-10-14 (`backlog.md` RD-5) that Hydroxyi's diagonal
argument in `TCSlib/Complexity/TimeHierarchy/Diagonal.lean` is **parameterized in place**, over
the simulator and its overhead, so that the book-strength theorem becomes a corollary. That
change is authorized for this file only, it must preserve the statement of every existing public
theorem, and it goes through a PR plus a gate. The same day the user also decided that
**Part 1, the parameterization alone, lands early**, with a small statement gate.

**This gate audits Part 1.** The book-strength corollaries, the two-tape instance and the
illustration are not in it; they come at the end of the chain (design note §3.2, §3.3 item 4;
the illustration has been dropped).

**Everything under audit is proved.** There is no `sorry`, and every declaration depends only
on the standard axioms. So the trusted surface is the statements and definitions, plus one
property you can check: the received statements are unchanged.

| File | Content |
|---|---|
| `audits/evidence/diagonal-p1/tree/TCSlib/Complexity/TimeHierarchy/Diagonal.lean` (536 lines, MEASURED) | **the file under audit**, as it will land |
| `audits/evidence/diagonal-p1/patches/Diagonal.patch` | the change against the base, `diff -u` (345 insertions, 122 deletions) |
| `TCSlib/Complexity/TimeHierarchy/Diagonal.lean` at the base (313 lines) | the received file |
| `audits/evidence/u2/U2-design.md` §3 and `probes/U2DiagParam.lean.txt` | the design and its probe |
| `audits/evidence/diagonal-p1/logs/` | every check below (`summary.log` lists them) |
| `audits/evidence/diagonal-p1/scripts/` | the scripts that produce the logs; `run.sh` re-runs them all, fail-closed |

**Base and provenance (maintainer).**
- **Base:** the campaign tip `cd450a526e71a5e437ebe84245ea958bf309eda1`, read by `git rev-parse`
  and exported read-only by `git archive`. Its Lean files equal `c52663f1`'s. The probe-relevant
  files have been unchanged since `759471be`.
- **Snapshot:** `oleans-lh1`, Lean `v4.25.0`.
- **The tip moved during the build**, to `c9cc485b` (#95, #96 and #97 merged). The Lean files
  changed are `SpaceComplexity/Inclusions`, `Build/Embed`, `Build/NDHost`, `Build/RecordTable`
  and `CodeSimulator`. The precheck shows that the landing stays valid there
  (`logs/precheck.log`, `scripts/tipcheck.py`):
  - `Diagonal.lean` is unchanged, so the patch applies as is;
  - no changed module lies in `Diagonal`'s own import closure (23 modules);
  - `Diagonal`'s downstream closure at the tip is the same 11 modules.

  Four of the changed modules (all but `NDHost`) lie in the import closures of the importers.
  Their cut checks were taken at the base, against `oleans-lh1`; the landing replay re-checks
  them at the tip.
- **Tools:** `lean` ran only through `tools/leanelab.sh` (no `-o`, no olean written). Python ran
  only as `python3 -I`. No lake, no network. Nothing in the repository checkout was modified.
- **Authorship:** a maintainer sub-agent wrote the files.

## What the gate covers

1. **Twenty-two new public names**: 14 declarations, plus the constructors and fields of the two
   structures (§ "New public names" below, and Appendix A).
2. **The received surface is unchanged.** The ten received declarations of `Diagonal.lean` keep
   their statements byte for byte. Four of their proofs become one-line instances; five
   docstrings change, in their proof sketches or to add a note (Appendix B).
3. **The module docstring.** It gains a new section, "The parameterized argument". The
   divergence bullet about `f log f` is updated, three entries are added to
   `## Main definitions` and one to `## Main results`.
4. **The consumers.** The five direct importers need no edit (cut checks), and the replay list
   covers the full downstream closure.

Out of scope:
- tactic proofs (machine-checked);
- the two-tape universal machine and Hennie–Stearns, which have their own statement phases;
- the end-of-chain corollaries.

## The change in one paragraph

The received theorem is proved once for a specific machine, `diagSim`. After the change:
- **The argument is stated for any machine `W`.**
  - `diagLangOf W g` is the diagonal language of `W`.
  - It lies in `DTIME (g + 1)` for every `W` (`diagLangOf_mem_DTIME`), because Hydroxyi's
    clocked runner clocks `W`'s own steps.
- **`DiagSimulator Φ`** says `W` reproduces every `DTIME T` language on some input of each large
  length within `A · Φ (T n) n` steps. From it follow the lower bound and the hierarchy theorem
  with overhead `Φ` (`DiagSimulator.diagLang_not_mem_DTIME`, `.time_hierarchy`,
  `.time_hierarchy_of_pos`).
- **`SelfSimulator Ψ`** is the same hypothesis stated at the level of a universal machine. It
  consists of:
  - per-code linear self-simulation of one-bit verdicts on `pairEncode α w`;
  - a normal form of overhead `Ψ` for `DTIME` deciders.

  Input padding turns it into a `DiagSimulator` with overhead `Ψ t + n + 1`
  (`SelfSimulator.toDiagSimulator`).
- **The received theorem is the instance** at `diagSim` with `Ψ t = (t + 1)²`
  (`oneTapeSelfSimulator`), weakened by `mono` to the received `(t + n + 1)²`
  (`sqDiagSimulator`). `diagLang_mem_DTIME`, `diagLang_not_mem_DTIME`, `time_hierarchy` and
  `time_hierarchy_of_pos` are now its one-line corollaries.
- **The received proofs were moved into the generic lemmas, not copied** (with
  `diagSim → W`): the copy-text screen shows no new pair.

## Decisions in force (verify that the file reflects them)

- **The authorization** (user, 2026-10-14; `backlog.md` RD-5): only `Diagonal.lean` is edited,
  in place, preserving the statement of every existing public theorem.
  - No other file of Hydroxyi's is edited (`Separation.lean`, `ClockMachine.lean`,
    `ClockLoop.lean`, `CircuitComplexity/*`), and nothing is copied from them.
  - The probe's illustration (`DTIME(n+1) ⊊ DTIME((n+1)²)`) is dropped, so `Separation`'s log
    lemma is not copied.
- **The facade** `TimeHierarchy.lean`'s stale sentence is fixed in the Diagonal PR only if that
  PR makes it stale. **Part 1 does not.** `Complexity.time_hierarchy` still has the quadratic
  overhead the sentence describes, and the facade's `## Contents` line for `Diagonal` stays
  accurate. The facade is not edited; the sentence goes to the end-of-chain PR.
- **`diagLang`'s definition is unchanged.** `diagLangOf` sits beside it, with
  `diagLang_eq_diagLangOf` as `rfl`.
- **Policy:**
  - statement prose and a `[AB09, …]` tag on every public declaration;
  - proof sketches on the nontrivial proofs (`diagLangOf_mem_DTIME`,
    `DiagSimulator.diagLang_not_mem_DTIME`, `.time_hierarchy`, `.time_hierarchy_of_pos`,
    `SelfSimulator.toDiagSimulator`, `oneTapeSelfSimulator`);
  - 100-character lines;
  - no unacknowledged duplication;
  - imports unchanged.

## New public names (MEASURED, `logs/names.log`)

In namespace `Complexity.TimeHierarchy`:

| Name | Kind | Role |
|---|---|---|
| `diagLangOf` | def | the diagonal language of a machine `W` |
| `diagLang_eq_diagLangOf` | theorem (`rfl`) | `diagLang g = diagLangOf diagSim g` |
| `diagLangOf_mem_DTIME` | theorem | `diagLangOf W g ∈ DTIME (g + 1)` for time-constructible `g`, every `W` |
| `DiagSimulator` (with `mk`, `W`, `simulates`) | structure | padded simulation with overhead `Φ` |
| `DiagSimulator.mono` | def | the same simulator with an overhead `Φ'`, `Φ ≤ K · Φ'` |
| `DiagSimulator.diagLang_not_mem_DTIME` | theorem | the lower bound, infinitely-often form |
| `DiagSimulator.time_hierarchy` | theorem | the hierarchy theorem with overhead `Φ` (needs `t ≤ Φ t n`) |
| `DiagSimulator.time_hierarchy_of_pos` | theorem | the same, with `DTIME g` for positive `g` |
| `SelfSimulator` (with `mk`, `W`, `decode`, `simulates`, `normalForm`) | structure | per-code linear self-simulation plus a normal form of overhead `Ψ` |
| `SelfSimulator.toDiagSimulator` | def | input padding: overhead `Ψ t + n + 1` |
| `oneTapeSelfSimulator` | noncomputable def | the received instance, `Ψ t = (t + 1)²` |
| `le_sq_overhead` | theorem | `t ≤ (t + n + 1)²` |
| `sqDiagSimulator` | noncomputable def | the received instance at overhead `(t + n + 1)²` |
| `sqDiagSimulator_W` | theorem (`rfl`) | its machine is `diagSim` |

**Collision screen.** No new name, constructor or field occurs anywhere in the base tree's
723 Lean files (whole-word screen of the nine distinctive components). So there is no collision,
and no downstream file can refer to them.

## The freeze (MEASURED, `logs/freeze.log`)

**The header** (copyright block, imports, options) is byte-identical. The imports are unchanged,
so the import graph is unchanged.

| Received declaration | Head (statement) | Proof | Docstring |
|---|---|---|---|
| `Complexity.TimeHierarchy.code` | identical | unchanged | unchanged |
| `univTM` | identical | unchanged | unchanged |
| `univTM_spec` | identical | unchanged | unchanged |
| `diagSim` | identical | unchanged | unchanged |
| `diagLang` | identical | **unchanged (the definition)** | unchanged |
| `diagLang_mem_DTIME` | identical | `diagLangOf_mem_DTIME diagSim hg` | sketch rewritten |
| `diag_cost_le` | identical | unchanged | note added: no longer used in this file |
| `diagLang_not_mem_DTIME` | identical | `sqDiagSimulator.diagLang_not_mem_DTIME hT` | sketch rewritten |
| `Complexity.time_hierarchy` | identical | `sqDiagSimulator.time_hierarchy le_sq_overhead hg hfg` | sketch rewritten |
| `Complexity.time_hierarchy_of_pos` | identical | `sqDiagSimulator.time_hierarchy_of_pos le_sq_overhead hg hpos hfg` | sketch rewritten |

- **How the statements stay identical.** The landing script copies each statement from the base
  text programmatically, from `theorem` to its ` := by`. `freeze.py` re-checks every head
  independently.
- **No existing proof is weakened or replaced by `sorry`.** Each replaced proof elaborates to
  the same statement, and the landed code has no `sorry`, `admit`, `native_decide` or `axiom`.
- **The freeze fails closed.** Its negative controls (a changed head; a proof replaced by
  `sorry`) are reported as failures (`logs/negative-controls.log`).

## Axioms (MEASURED, `logs/axioms.log`)

All 24 public declarations of the landed file (10 received, 14 new) depend on `propext`,
`Classical.choice` and `Quot.sound` only. `le_sq_overhead` depends on `propext` and
`Quot.sound` alone. **Part 1 is sorry-free.**

## Consumers (MEASURED, `logs/graph.log`, `logs/cut.log`)

**The downstream closure** of `TCSlib.Complexity.TimeHierarchy.Diagonal` is 11 modules,
excluding the root `TCSlib` (`replay-order.txt`, topological). Every import of every listed
module is either listed earlier or present in `oleans-lh1`.

**The cut method.** The snapshot holds the base `Diagonal` olean, so each direct importer is
checked as follows:
- it is concatenated after the landed `Diagonal.lean` body, together with any intermediate
  module of the closure (for the facade, `Separation`), each body in its own `section`;
- that is elaborated against the snapshot, with `#print axioms` for each of the importer's
  public declarations;
- the output is compared with the importer's own baseline elaboration.

| Direct importer | Uses | Baseline messages | Cut-check messages | Errors | Equal |
|---|---|---|---|---|---|
| `TimeHierarchy/Separation` | `diagLang`, `diagLang_mem_DTIME`, `diagLang_not_mem_DTIME`, `time_hierarchy_of_pos` | 6 | 6 | 0 | yes |
| `Diagonalization/EXPCOM` | the import; prose | 9 | 9 | 0 | yes |
| `Diagonalization/NotTimeConstructible` | `TimeHierarchy.code` | 1 | 1 | 0 | yes |
| `SpaceComplexity/Hierarchy` | `TimeHierarchy.code` | 8 | 8 | 0 | yes |
| `TimeHierarchy` (facade; through `Separation`) | — | 0 | 0 | 0 | yes |

The messages are the axiom prints and the pre-existing `declaration uses 'sorry'` warnings of
`Hierarchy`'s four sorried statements. **No importer needs an edit.** A negative control shows
that the cut method detects a broken landed text.

**The rest of the closure** has only transitive users: `Relativization`, the `Diagonalization`
and `SpaceComplexity` facades, and `CircuitComplexity/Meyer` with its facade. These inherit
unchanged statements and new names that do not collide; they are covered by the user's replay of
`replay-order.txt`, not by this gate.

## Duplication (MEASURED, `logs/screen-before.txt`, `logs/screen-after.txt`, `logs/screen-delta.log`)

**Method.** The retrofit copy-text screen (verbatim, niced, run one at a time) was applied to
seven files: the edited file, its directory, and the two files that use the same inclusion
idiom (`Diagonalization/NTimeHierarchy.lean`, `SpaceComplexity/Hierarchy.lean`).

**Result.** 16 pairs before and 16 after. **None is new and none is gone.** All 16 are
pre-existing pairs inside Hydroxyi's `ClockMachine`/`ClockLoop`/`CodePrefix`, which this change
does not touch. The generic lemmas carry the received proofs, generalized from `diagSim` to `W`,
and the received copies are deleted. So no proof text exists twice.

**Disclosed.** `audits/evidence/u2/probes/U2DiagParam.lean.txt` holds an earlier probe text of the
same layer. It is design evidence: it is not under `TCSlib/`, is not compiled, and is not
library material.

## Lint, widths, hygiene (MEASURED)

- **Lint:** `scripts/style_lint.py` (the repository's) reports 0 findings on the base and on the
  landed file.
- **Widths:** the maximum width is 95; no line is over 100.
- **Hygiene:** UTF-8 with LF line ends and one final newline; no tab, no trailing whitespace, no
  `#`-command; the `set_option` lines are as in the base; no `private` declaration.

## Known deviations (declared by the docstrings; verify that they are benign, and flag any others)

- **`DiagSimulator` asks for a simulation on one input of each large length**, not on every code
  of the machine: the book uses infinitely many codes, and here the input is padded instead.
- **`SelfSimulator`'s constant `C` depends on the code string**, not only on the machine. This
  is the received Argument E, because the canonizer time of an effective scheme is arbitrary.
- **`SelfSimulator` asks for one-bit verdicts only**, not the simulated machine's whole output:
  the diagonal argument uses nothing more.
- **Inherited by the generic theorems** from `Complexity.time_hierarchy`: `DTIME (g + 1)` in
  place of `DTIME g`, and no time-constructibility hypothesis on `f`.
- **`diag_cost_le` is kept** with its statement, as the authorization requires, but this file no
  longer uses it.

## Brief for the auditor

You are auditing the **trusted surface** of a Lean 4 formalization. Here that is the
definitions and statements of the new declarations, and the claim that the received statements
are unchanged. The proofs are machine-checked and sorry-free; do not review tactic scripts for
correctness. Hunt for:
1. **Infidelity.** `diagLangOf`, `DiagSimulator` and `SelfSimulator` must mean what the
   docstrings and [AB09, Theorem 3.1 and its proof, p. 69; §1.4] say. In particular, is
   `DiagSimulator Φ` exactly the property the diagonal argument needs, neither weaker (vacuous)
   nor stronger (unsatisfiable by the intended instances)?
2. **Trivialization.** Could a `DiagSimulator` or a `SelfSimulator` exist for degenerate
   reasons, and so give a hierarchy theorem that is false?
   - The generic `time_hierarchy` is proved, so a false conclusion would mean an inconsistency.
     More likely, a degenerate structure might exist only for degenerate `Φ`.
   - Instantiate adversarially: `Φ = 0`; `Ψ = 0`; a `W` that never halts; `decode` constant;
     `T = 0`.
   - Check that the hypotheses `t ≤ Φ t n` and "`A · Φ (f n) n ≤ g n` for every `A`" exclude
     the degenerate cases, and that each degenerate structure is uninhabited or harmless.
3. **The freeze.** Confirm that the ten received statements are byte-identical, and that
   `diagLang`'s definition is unchanged (`logs/freeze.log`; compare the base and landed files
   yourself). Confirm that the five consumers need no edit (`logs/cut.log`).
4. **Missing hypotheses or a surplus.**
   - Is `hΦ : ∀ t n, t ≤ Φ t n` needed? It is used only for the inclusion half.
   - Is the `+ (pairEncode α w).length + 1` slack in `SelfSimulator.simulates` adequate for the
     planned two-tape instance (U2-U has `C · (t + 1)`)?
   - Is the `+ 1` in `normalForm`'s `c · (Ψ (T n) + 1)` harmless?
5. **Fit for the planned instance.** The book-strength corollary is to take
   `Ψ t = (t + 1)(log₂(t + 1) + 1)`, with `W` the two-tape self-application universal machine.
   Do the structures admit it as stated?
   - The probe `audits/evidence/u2/probes/U2DiagParam.lean.txt` derives the book-form theorem from
     such a `SelfSimulator`, sorry-free.
   - It also derives `SelfSimulator logOverhead` from the sorried G5 and U2 statements.
6. **Debt.** Verify the duplication ledger above: no new copy-text pair; the received proofs
   moved, not copied.

Attempt at least **three adversarial instantiations** (item 2). Propose any sanity theorems
you believe are missing.

## Specific questions for this gate

1. **The field name `W`** (capital, as in the received `clockTM K W`) for the structures'
   machines. Is it acceptable, or should it be renamed, for example `sim`?
2. **`diag_cost_le`** is now unused, and kept only for statement preservation. Keep it (as the
   authorization requires), or recommend its retirement to the user and Hydroxyi later?
3. **The verdict-only `simulates` clause of `SelfSimulator`** (`[b] → [b]`) instead of a
   full-output clause. Is it the right generality? It admits more instances, and the diagonal
   argument needs nothing more.
4. **The facade's sentence is left unchanged** (§ Decisions). Do you agree that Part 1 does not
   make it stale?

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide: **blocker** = a downstream phase would build on a wrong statement; **major** =
a statement is fixable but materially misleading as is, or accumulated debt (failure mode 5 of
`audits/TEMPLATE.md`); **minor** = edge case or naming/attribution defect; **note** =
observation, no change required.

## Appendix A. The new declarations, as landed (docstring and statement; generated by `scripts/appendix.py`)

### `Complexity.TimeHierarchy.diagLangOf` (def, line 170)

```lean
/-- **The diagonal language of a simulator `W`** [AB09, Theorem 3.1, proof]: the strings `x`
on which `W` does **not** halt with output `[true]` within `g(|x|)` steps. The received
`diagLang g` is the case `W = diagSim` (`diagLang_eq_diagLangOf`). -/
def diagLangOf (W : FinTM Bool) (g : ℕ → ℕ) : Language Bool
```

### `Complexity.TimeHierarchy.diagLang_eq_diagLangOf` (theorem, line 174)

```lean
/-- The received diagonal language is the diagonal language of `diagSim`, by definition. -/
theorem diagLang_eq_diagLangOf (g : ℕ → ℕ) : diagLang g = diagLangOf diagSim g
```

### `Complexity.TimeHierarchy.diagLangOf_mem_DTIME` (theorem, line 184)

```lean
/-- **The diagonal language of any simulator is decidable in time `O(g)`** [AB09, Theorem 3.1,
proof]: for time-constructible `g` and every machine `W`, `diagLangOf W g ∈ DTIME (g + 1)`.
Nothing is assumed of `W`: the clocked runner counts `W`'s own steps.

**Proof sketch.** Run the clocked runner `clockTM K W`, with `K` the time-constructibility
witness of `g`: its budget word is `bits (g n)` of value `g n`, so by `clockTM_spec` it outputs
`[x ∈ diagLangOf W g]` within `c_K (g n + 1) + 4|bits (g n)| + n + 4 g n + 6 ≤
(c_K + 15)(g n + 1)` steps, using `|bits m| ≤ m` and `n ≤ g n`. -/
theorem diagLangOf_mem_DTIME (W : FinTM Bool) {g : ℕ → ℕ} (hg : TimeConstructible g) :
    diagLangOf W g ∈ DTIME (fun n => g n + 1)
```

### `Complexity.TimeHierarchy.DiagSimulator` (structure, line 212)

```lean
/-- **A diagonal simulator with overhead `Φ`** (the hypothesis of the diagonal argument
[AB09, Theorem 3.1, proof]; design note `audits/evidence/u2/U2-design.md` §3): a machine `W`
such that for every time bound `T` and every language `L ∈ DTIME T` there are constants `A`
and `N₀` with: for every length `n ≥ N₀` some input `x` of length `n` makes `W` halt with the
verdict `[x ∈ L]` within `A · Φ (T n) n` steps. No clock is part of it: the clocked runner
supplies one for every `W` (`diagLangOf_mem_DTIME`). Deviation: the book simulates a code of
the machine at hand, which has infinitely many codes; here the simulator is only required to
succeed on one input of each large length, which is what the diagonal argument uses. -/
structure DiagSimulator (Φ : ℕ → ℕ → ℕ) where
  /-- the simulating machine -/
  W : FinTM Bool
  /-- padded simulation of every `DTIME T` language within `A · Φ (T n) n` steps -/
  simulates : ∀ (T : ℕ → ℕ) (L : Language Bool), L ∈ DTIME T →
    ∃ A N₀ : ℕ, ∀ n ≥ N₀, ∃ x : List Bool, x.length = n ∧
      W.ComputesInTime x [MultiTapeTM.indicator (L : Set (List Bool)) x] (A * Φ (T n) n)
```

### `Complexity.TimeHierarchy.DiagSimulator.mono` (def, line 226)

```lean
/-- **Weakening the overhead** up to a constant factor: a diagonal simulator with overhead `Φ`
is one, with the same machine, with overhead `Φ'` whenever `Φ ≤ K · Φ'` pointwise. -/
def mono (S : DiagSimulator Φ) {Φ' : ℕ → ℕ → ℕ} (K : ℕ) (h : ∀ t n, Φ t n ≤ K * Φ' t n) :
    DiagSimulator Φ'
```

### `Complexity.TimeHierarchy.DiagSimulator.diagLang_not_mem_DTIME` (theorem, line 245)

```lean
/-- **The diagonal language is not in `DTIME T`** [AB09, Theorem 3.1, proof], for a diagonal
simulator with overhead `Φ`, provided `A · Φ (T n) n ≤ g n` for infinitely many `n`, for every
constant `A` (the infinitely-often form).

**Proof sketch.** Suppose `diagLangOf W g ∈ DTIME T`. The simulation clause gives `A` and
`N₀`; pick `n ≥ N₀` with `A · Φ (T n) n ≤ g n`, and an input `x` of length `n` on which `W`
halts with `[χ(x)]` within `A · Φ (T n) n ≤ g n` steps, `χ` the indicator of the diagonal
language. If `χ(x) = true` then `x ∈ diagLangOf W g`, so `W` does not output `[true]` within
`g n`, a contradiction; if `χ(x) = false` then `x ∉ diagLangOf W g`, so `W` outputs `[true]`
within `g n`, against the uniqueness of its output `[false]`. -/
theorem diagLang_not_mem_DTIME (S : DiagSimulator Φ) {g T : ℕ → ℕ}
    (hT : ∀ A N : ℕ, ∃ n ≥ N, A * Φ (T n) n ≤ g n) :
    diagLangOf S.W g ∉ DTIME T
```

### `Complexity.TimeHierarchy.DiagSimulator.time_hierarchy` (theorem, line 278)

```lean
/-- **The Time Hierarchy Theorem with overhead `Φ`** [AB09, Theorem 3.1], for a diagonal
simulator: if `g` is time constructible, `t ≤ Φ t n` for all `t` and `n`, and for every
constant `A` eventually `A · Φ (f n) n ≤ g n`, then `DTIME(f) ⊊ DTIME(g + 1)`. The deviations
of `Complexity.time_hierarchy` apply (`f` need not be time constructible; `DTIME (g + 1)`).

**Proof sketch.** *Inclusion:* the hypothesis at `A = 1` and `t ≤ Φ t n` give `f n ≤ g n`
for `n ≥ N`; the finitely many smaller lengths are absorbed into the constant, so
`f n ≤ c (g n + 1)` for all `n`, and `DTIME` absorbs `c`. *Strictness:* `diagLangOf W g` lies
in `DTIME (g + 1)` (`diagLangOf_mem_DTIME`) but not in `DTIME f`
(`DiagSimulator.diagLang_not_mem_DTIME`, whose infinitely-often hypothesis follows from the
eventual one). -/
theorem time_hierarchy (S : DiagSimulator Φ) (hΦ : ∀ t n, t ≤ Φ t n)
    {f g : ℕ → ℕ} (hg : TimeConstructible g)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * Φ (f n) n ≤ g n) :
    DTIME f ⊂ DTIME (fun n => g n + 1)
```

### `Complexity.TimeHierarchy.DiagSimulator.time_hierarchy_of_pos` (theorem, line 310)

```lean
/-- **The Time Hierarchy Theorem with overhead `Φ`, for a positive bound** [AB09,
Theorem 3.1]: as `DiagSimulator.time_hierarchy`, with the larger class exactly `DTIME g` when
`g` never vanishes.

**Proof sketch.** `c (g n + 1) ≤ 2c · g n` when `g n ≥ 1`, so `DTIME (g + 1) ⊆ DTIME g`; the
reverse inclusion is `Complexity.DTIME.mono`; conclude from `DiagSimulator.time_hierarchy`. -/
theorem time_hierarchy_of_pos (S : DiagSimulator Φ) (hΦ : ∀ t n, t ≤ Φ t n)
    {f g : ℕ → ℕ} (hg : TimeConstructible g) (hpos : ∀ n, 0 < g n)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * Φ (f n) n ≤ g n) :
    DTIME f ⊂ DTIME g
```

### `Complexity.TimeHierarchy.SelfSimulator` (structure, line 341)

```lean
/-- **A self-simulator with normal-form overhead `Ψ`** (the universal-machine form of the
hypothesis [AB09, §1.4 and Theorem 3.1, proof]; design note `audits/evidence/u2/U2-design.md`
§3): a machine `W` and machines `decode α` indexed by codes `α`, such that
* for every code `α` there is a constant `C`, depending on `α` only, with: whenever
  `decode α` halts on `pairEncode α w` with a one-bit output `[b]` within `t` steps, `W` halts
  on the same input with `[b]` within `C · (t + |pairEncode α w| + 1)` steps (self-application:
  the coded machine runs on the very input that carries its code);
* every `DTIME T` language has a code `α` whose machine decides it within
  `c · (Ψ (T n) + 1)` steps, for a constant `c` (the normal form).

No clock, no uniformity in the code and no output beyond the one-bit verdict is required.
Deviation: the book uses that every machine has infinitely many codes; here one code is fixed
and the input is padded (`SelfSimulator.toDiagSimulator`), as in the received proof, because
the constant `C` depends on the code string. -/
structure SelfSimulator (Ψ : ℕ → ℕ) where
  /-- the self-application simulator -/
  W : FinTM Bool
  /-- the machine each code denotes -/
  decode : List Bool → FinTM Bool
  /-- per-code linear self-simulation of one-bit verdicts -/
  simulates : ∀ α : List Bool, ∃ C : ℕ, ∀ (w : List Bool) (b : Bool) (t : ℕ),
    (decode α).ComputesInTime (pairEncode α w) [b] t →
    W.ComputesInTime (pairEncode α w) [b] (C * (t + (pairEncode α w).length + 1))
  /-- the normal form: every `DTIME T` language has a coded decider within `c · (Ψ T + 1)` -/
  normalForm : ∀ (T : ℕ → ℕ) (L : Language Bool), L ∈ DTIME T →
    ∃ (α : List Bool) (c : ℕ), ∀ x : List Bool,
      (decode α).ComputesInTime x [MultiTapeTM.indicator (L : Set (List Bool)) x]
        (c * (Ψ (T x.length) + 1))
```

### `Complexity.TimeHierarchy.SelfSimulator.toDiagSimulator` (def, line 364)

```lean
/-- **Input padding** [AB09, Theorem 3.1, proof]: a self-simulator with normal-form overhead
`Ψ` is a diagonal simulator, with the same machine, with overhead `Ψ t + n + 1`.

**Proof sketch.** For `L ∈ DTIME T` take the normal form's code `α` and constant `c`, and the
simulation constant `C` of `α`. For `n ≥ 2|α| + 2` the input
`x = pairEncode α 1^(n - 2|α| - 2)` has length `n`; `decode α` decides `L` on it within
`c (Ψ (T n) + 1)` steps, so `W` reproduces the verdict within
`C (c (Ψ (T n) + 1) + n + 1) ≤ C (c + 1) (Ψ (T n) + n + 1)` steps. -/
def SelfSimulator.toDiagSimulator {Ψ : ℕ → ℕ} (S : SelfSimulator Ψ) :
    DiagSimulator (fun t n => Ψ t + n + 1)
```

### `Complexity.TimeHierarchy.oneTapeSelfSimulator` (def, line 429)

```lean
/-- **The received self-simulator** [AB09, Theorem 3.1, proof; Claims 1.5–1.6]: `diagSim` is a
self-simulator for the codes of `code` (`decode α` the machine `code.decode α`), with the
one-work-tape normal form, whose overhead is the square `Ψ t = (t + 1)²`.

**Proof sketch.** *Simulation:* on `x = pairEncode α w`, `preTM` writes `pairEncode α x`
within `3|x| + 5` steps (`preTM_computes`, `scanPre_pairEncode_append`), and `univTM` simulates
the coded machine on `x` within `C (t + 1)` steps (`univTM_spec`); buffered composition adds
the intermediate length plus two, `|pairEncode α x| + 2 ≤ 2|x| + 2`
(`bufferedCompTM_computesInTime`): in all at most `(C + 7)(t + |x| + 1)` steps. *Normal form:*
a decider within `c₀ T` becomes a one-work-tape binary machine within `c₁ (c₀ T + 1)²`
(`Turing.FinTM.one_work_tape_binary`), then a coded machine `N` with the same runs
(`Turing.exists_codeTM`), whose code `code.encode N` decodes back to `N`; and
`c₁ (c₀ T + 1)² ≤ c₁ (c₀ + 1)² ((T + 1)² + 1)`. -/
noncomputable def oneTapeSelfSimulator : SelfSimulator (fun t => (t + 1) ^ 2)
```

### `Complexity.TimeHierarchy.le_sq_overhead` (theorem, line 458)

```lean
/-- The received overhead dominates the time: `t ≤ (t + n + 1)²` for all `t` and `n`. -/
theorem le_sq_overhead (t n : ℕ) : t ≤ (t + n + 1) ^ 2
```

### `Complexity.TimeHierarchy.sqDiagSimulator` (def, line 465)

```lean
/-- **The received diagonal simulator**: `diagSim` with the overhead `(t + n + 1)²` of the
received theorem, from `oneTapeSelfSimulator` by input padding
(`SelfSimulator.toDiagSimulator`) and `(t + 1)² + n + 1 ≤ 2 (t + n + 1)²`. -/
noncomputable def sqDiagSimulator : DiagSimulator (fun t n => (t + n + 1) ^ 2)
```

### `Complexity.TimeHierarchy.sqDiagSimulator_W` (theorem, line 473)

```lean
/-- The received diagonal simulator's machine is `diagSim`, by definition. -/
theorem sqDiagSimulator_W : sqDiagSimulator.W = diagSim
```

## Appendix B. Received declarations whose docstring or proof changed (statement byte-identical; docstring and new proof as landed)

### `Complexity.TimeHierarchy.diagLang_mem_DTIME` (theorem, line 390)

```lean
/-- **The diagonal language is decidable in time `O(g)`** [AB09, Theorem 3.1, proof:
"`D` runs in time `O(g(n))`"]: for time-constructible `g`,
`diagLang g ∈ DTIME (g + 1)`.

**Proof sketch.** The case `W = diagSim` of `diagLangOf_mem_DTIME`, since `diagLang g` is
`diagLangOf diagSim g` by definition (`diagLang_eq_diagLangOf`): the clocked runner
`clockTM K diagSim`, with `K` the time-constructibility witness of `g`, decides it within
`(c_K + 15)(g n + 1)` steps. -/
theorem diagLang_mem_DTIME {g : ℕ → ℕ} (hg : TimeConstructible g) :
    diagLang g ∈ DTIME (fun n => g n + 1) :=
  diagLangOf_mem_DTIME diagSim hg
```

### `Complexity.TimeHierarchy.diag_cost_le` (lemma, line 399)

```lean
/-- The polynomial bookkeeping of the received diagonal argument: with `X = T + n + 1`, the
simulation cost `5n + 7 + C · (c₁ (c₀ T + 1)² + 1)` is at most
`(8 + C (c₁ (c₀ + 1)² + 1)) · X²`. Kept with its statement; the parameterized argument does its
bookkeeping in `oneTapeSelfSimulator`, `SelfSimulator.toDiagSimulator` and `sqDiagSimulator`,
and no declaration of this file uses this lemma. -/
lemma diag_cost_le (n T c₀ c₁ C : ℕ) :
    5 * n + 7 + C * (c₁ * (c₀ * T + 1) ^ 2 + 1) ≤
      (8 + C * (c₁ * (c₀ + 1) ^ 2 + 1)) * (T + n + 1) ^ 2 := by
  have hX : 1 ≤ T + n + 1 := by omega
  have hX2 : T + n + 1 ≤ (T + n + 1) ^ 2 := by nlinarith
  have hlin : c₀ * T + 1 ≤ (c₀ + 1) * (T + n + 1) := by nlinarith
  have hsq : (c₀ * T + 1) ^ 2 ≤ (c₀ + 1) ^ 2 * (T + n + 1) ^ 2 := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left hlin 2
  have hone : 1 ≤ (T + n + 1) ^ 2 := by nlinarith
  have hinner : c₁ * (c₀ * T + 1) ^ 2 + 1 ≤ (c₁ * (c₀ + 1) ^ 2 + 1) * (T + n + 1) ^ 2 := by
    have := Nat.mul_le_mul_left c₁ hsq
    nlinarith
  have hC := Nat.mul_le_mul_left C hinner
  nlinarith
```

### `Complexity.TimeHierarchy.diagLang_not_mem_DTIME` (theorem, line 490)

```lean
/-- **The diagonal language is not in `DTIME T`** [AB09, Theorem 3.1, proof: "`D`
differs from every machine running in time `f`"], provided `g` dominates
`A · (T n + n + 1)²` for infinitely many `n`, for every constant `A`.

**Proof sketch.** The case `sqDiagSimulator` of `DiagSimulator.diagLang_not_mem_DTIME`,
whose machine is `diagSim` (`sqDiagSimulator_W`). Its simulation clause is
`oneTapeSelfSimulator`'s, padded by `SelfSimulator.toDiagSimulator`: a decider `M` of
`diagLang g` within `c₀ T(n)` becomes a one-work-tape binary machine within `c₁ (c₀ T + 1)²`
(`Turing.FinTM.one_work_tape_binary`) and then a coded machine `N` with the same runs
(`Turing.exists_codeTM`), with code `α = ⌞N⌟`. On `x = pairEncode α 1^(n - 2|α| - 2)`, of
length `n`, `preTM` and `univTM` reproduce `M`'s verdict `[χ(x)]` within `A (T n + n + 1)²`
steps, `A` depending on `M` only. At an `n` with `A (T n + n + 1)² ≤ g n` that verdict
contradicts the definition of `diagLang g`: if `χ(x) = true`, `diagSim` does not output
`[true]` within `g n`; if `χ(x) = false`, it does, against the uniqueness of its output
`[false]`. -/
theorem diagLang_not_mem_DTIME {g T : ℕ → ℕ}
    (hT : ∀ A N : ℕ, ∃ n ≥ N, A * (T n + n + 1) ^ 2 ≤ g n) :
    diagLang g ∉ DTIME T :=
  sqDiagSimulator.diagLang_not_mem_DTIME hT
```

### `Complexity.time_hierarchy` (theorem, line 518)

```lean
/-- **The Time Hierarchy Theorem** [AB09, Theorem 3.1], in the form supported by this
development: if `g` is time constructible and `(f(n) + n + 1)² = o(g(n))` — i.e. for
every constant `A`, eventually `A · (f n + n + 1)² ≤ g n` — then
`DTIME(f) ⊊ DTIME(g + 1)`.

Deviations from the book (see the module docstring): the overhead is quadratic
(`(f + n + 1)²` in place of `f log f`), owing to the one-work-tape normal form of
coded machines; `f` need not be time constructible; and the larger class is
`DTIME (g + 1)`, which differs from `DTIME g` only in the degenerate case `g 0 = 0`.

**Proof sketch.** The case `Φ t n = (t + n + 1)²` of `DiagSimulator.time_hierarchy` at
`sqDiagSimulator`, with `t ≤ (t + n + 1)²` (`le_sq_overhead`). *Inclusion:* the hypothesis
with `A = 1` gives `f n ≤ g n` for `n ≥ N`; the finitely many smaller lengths are absorbed
into the constant, so `f n ≤ c (g n + 1)` for all `n`, and `DTIME` absorbs `c`.
*Strictness:* the diagonal language `diagLang g` lies in `DTIME (g + 1)`
(`diagLangOf_mem_DTIME`) but not in `DTIME f` (`DiagSimulator.diagLang_not_mem_DTIME`, whose
infinitely-often hypothesis follows from the eventual one). -/
theorem time_hierarchy {f g : ℕ → ℕ} (hg : TimeConstructible g)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * (f n + n + 1) ^ 2 ≤ g n) :
    DTIME f ⊂ DTIME (fun n => g n + 1) :=
  sqDiagSimulator.time_hierarchy le_sq_overhead hg hfg
```

### `Complexity.time_hierarchy_of_pos` (theorem, line 531)

```lean
/-- **The Time Hierarchy Theorem for a positive bound** [AB09, Theorem 3.1]: as
`Complexity.time_hierarchy`, with the larger class exactly `DTIME g` when `g` never
vanishes (then `DTIME (g + 1) = DTIME g`, the constant `2` being absorbed).

**Proof sketch.** The case `Φ t n = (t + n + 1)²` of
`DiagSimulator.time_hierarchy_of_pos` at `sqDiagSimulator`: `c (g n + 1) ≤ 2c · g n` when
`g n ≥ 1`, so `DTIME (g + 1) ⊆ DTIME g`; the reverse inclusion is `Complexity.DTIME.mono`;
conclude from `DiagSimulator.time_hierarchy`. -/
theorem time_hierarchy_of_pos {f g : ℕ → ℕ} (hg : TimeConstructible g) (hpos : ∀ n, 0 < g n)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * (f n + n + 1) ^ 2 ≤ g n) :
    DTIME f ⊂ DTIME g :=
  sqDiagSimulator.time_hierarchy_of_pos le_sq_overhead hg hpos hfg
```

