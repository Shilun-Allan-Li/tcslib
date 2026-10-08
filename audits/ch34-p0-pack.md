# External audit pack — Chapters 3-4, phase P0 (reception of the existing surface)

Campaign: Arora-Barak chapters 3-4 (`AroraBarakChapters3-4Plan.md`), phase P0.
This round is a **reception audit**: the campaign is adopting, as its foundation for
chapters 3 and 4, a surface that already exists on `main` — written by a colleague
(git author `Hydroxyi`, Jason Dong, GitHub `qedsphere`; commit `f70c57c2`,
2026-10-06) outside the campaign's own statement-gate process. Nothing here is
sorried: every proof is machine-checked. What has **not** happened is an adversarial
statement-level review against the source text, and that is this round.

## Brief for the auditor

You are auditing the **trusted surface** of a Lean 4 formalization: definitions,
theorem statements, and their docstrings. The proofs are machine-checked — do not
review tactic scripts for correctness. The failure modes you are hunting:

1. **Infidelity** — a definition that does not mean what the cited source means.
2. **Trivialization** — a definition or statement satisfiable for degenerate reasons
   (vacuous hypotheses, a class that collapses, an encoding that makes a theorem
   empty).
3. **Hidden weakness** — a proved statement whose form is subtly weaker than its
   docstring or the book's claim (boundary cases: empty input, `n = 0`, `k = 0`
   tapes, constant absorption, quantifier order).
4. **Missing hypotheses or conventions** — side conditions the informal source
   carries (e.g. `S(n) ≥ log n`) that the formal statement drops, where the drop
   changes downstream meaning.

For **every definition** in scope: restate it in your own mathematical English
*without looking at the docstring first*, then compare against the cited source
location, and report any daylight. For **every headline theorem**: state what the
book's version says, what the Lean version delivers, and whether the delivered
strength is what the docstring claims. Attempt at least **5 adversarial
instantiations** — concrete pathological objects plugged into the definitions
(degenerate space bounds, length-0 inputs, constant languages, machines with `k = 0`
work tapes where the types allow it). Propose machine-checkable sanity theorems for
anything you cannot settle by inspection.

Do not give a blanket approval. Your deliverable is the findings table; an empty
table must be accompanied by the per-definition restatements that justify it.

## Scope

| Item | Where |
|---|---|
| Lean files under audit | the 44 modules of `scripts/ab_ch34_received_order.txt` (all attached): `Complexity/TimeHierarchy/` (5 + facade), `Complexity/SpaceComplexity/` (29, incl. `Machines/`), `TuringMachine/{UnaryTape,CounterProg,CounterProgRun}`, `ClassNP/{CounterProgPolyTime,ExpPoly,PolyTimePairing,PClosure,Transducer}` |
| Primary focus (the statements chapters 3-4 will consume) | `time_hierarchy`, `time_hierarchy_of_pos`, `P_ssubset_EXP`; `ComputesInSpace`, `DecidesInSpace`, `SPACE`, `logSpace`, `LOGSPACE`, `ImplicitlyLogspaceComputable`; `configBound`, `ComputesInTime.of_spaceUsed_le`, `LOGSPACE_subset_P`; `compile_correct`, `compile_space`, `arm_decides`, `arm_decides_poly`; `CounterProg` run algebra and its `FinTM` compilation |
| Source text | [AB09] Arora-Barak, *Computational Complexity*, 2009: §3.1 (pp. 68-69) for the time hierarchy; §4.1 (pp. 78-82, Definitions 4.1/4.5, Claim 4.4, Figure 4.1) and §4.3 (Definition 4.16, Lemma 4.17) for space |
| Plan/context documents | `AroraBarakChapters3-4Plan.md` (esp. §1-§2), `policy.md` §2-3, `workflow.md` §3 |
| Out of scope | tactic proofs; `Complexity/PolyHierarchy/` (chapter-5 material, not consumed by this campaign); `CircuitComplexity/LogspaceUniform*` (chapter-6 surface, audited separately); vendored cslib files' upstream design; naming style |

## Repository-side attestations (verify or challenge)

Produced at Lean-source commit `84b79daf` (= `origin/main` `99b187fc` plus the
documentation-only edits listed under "Known deviations", item 0; no code change —
checkable by `git diff 99b187fc 84b79daf -- 'TCSlib/**/*.lean'`).

* **CI**: `main`'s full workflow (lint, `lake build` + docs, blueprint, Verso) is
  green at `99b187fc` (run of 2026-10-08).
* **Fresh elaboration sweep**: all 71 modules of the received set's transitive
  TCSlib closure, in dependency order, through `scripts/lean_check_tree.sh` into a
  **wiped** scratch olean tree: 71/71 pass, 0 `error:` lines, 0
  `declaration uses 'sorry'` warnings, 71 fresh `.olean`s (log attached).
* **Admissions**: `grep -lw sorry` and `grep -l axiom` over the 44 received files:
  zero hits each.
* **Style lint** (`scripts/campaign_style_lint.py`): `TimeHierarchy/` and
  `SpaceComplexity/` 0 FAIL / 0 WARN (34 files); the `TuringMachine/` and `ClassNP/`
  trees 0 FAIL, size WARNs only, all on pre-existing recorded exception files, none
  of them received files (log attached).
* **Drift baseline**: declaration-level snapshots of all 44 files taken with
  `scripts/decl_snapshot.py` (label `ch34-p0-received`, 44/44 OK). The snapshot
  directory is gitignored by repo convention, so the authoritative baseline is
  commit `84b79daf` itself: the snapshot regenerates deterministically via
  `--git-rev 84b79daf`, and every later chapter-3/4 drift attestation compares
  against that commit.

## Known deviations (declared — verify they are benign, flag any others)

0. **P0 documentation edits** (commit `84b79daf`, this phase, comments only): the
   vendored `Deterministic.lean` docstring's claim that [AB09] counts non-blank
   cells was corrected ([AB09, Def 4.1] counts *visited* work-tape locations for
   `SPACE` and *nonblank* only for `NSPACE`); `SpaceComplexity/Basic.lean` now
   records that split and the campaign convention (visited cells for both classes);
   stale "spec phase / sorried" status notes in `Build/*` retired.
1. **Time hierarchy at `f²` strength** (`TimeHierarchy/Diagonal.lean` docstring):
   hypothesis `∀ A, ∃ N, ∀ n ≥ N, A·(f n + n + 1)² ≤ g n`, conclusion
   `DTIME f ⊂ DTIME (g + 1)`; `f` need not be time-constructible; the
   diagonalization pads inputs rather than using infinitely many codes; the
   separation is infinitely-often. The book's `f log f` form ([AB09, Thm 3.1]) is
   scheduled behind the Hennie-Stearns build (plan §2.1); the received form must be
   honest about this everywhere.
2. **`SPACE`**: constants absorbed as `c · s n` (the book's `O(s(n))`);
   `logSpace n = ⌊log₂ n⌋ + 1 ≥ 1`; **no `s(n) ≥ log n` side condition**; deciding
   includes halting on every input; space is visited work-tape cells, summed over
   work tapes, input and output tapes excluded.
3. **Def 4.16** (`ImplicitlyLogspaceComputable`): `0`-based bit index with
   `{⟨x,i⟩ | i < |f(x)|}` (book: `1`-based, `i ≤ |f(x)|`); pairing is
   `pairEncode x (Nat.bits i)`; polynomial bound in the campaign normal form
   `|f(x)| ≤ C·(|x|+1)^c`.
4. **Lemma 4.17 is not received**: only the special case
   `UnaryLogspace.counterProg` exists. Composition of implicitly-logspace functions
   is a planned chapter-4 statement (plan, phase P4.4), not a current claim.
5. **`CounterProg`**: `t` abstract steps compile to at most `t(2t+3)` machine
   steps; the input is read one-way (`rd` only advances).
6. **`univTM`** (`Diagonal.lean`): obtained by choice from `Turing.universal`; its
   constant depends on the code string, the necessity of which is the chapter-1
   audit's Argument E.

## Specific questions for this round (prioritized)

1. **`time_hierarchy`'s hypothesis shape.** Is
   `∀ A, ∃ N, ∀ n ≥ N, A·(f n + n + 1)² ≤ g n` the right rendering of
   "`f(n)² ⋅ (anything machine-dependent)` is eventually below `g`"? Check the
   quantifier order against the proof's needs (the constant `A` arrives *after* the
   adversary machine is fixed), and check that `DTIME (fun n => g n + 1)` in the
   conclusion (and `time_hierarchy_of_pos`'s `0 < g` variant) doesn't quietly
   weaken the separation. Does `P_ssubset_EXP` really follow at the stated
   exponents (`eventually_poly_sq_le_two_pow`)?
2. **`SPACE` without the `s ≥ log n` convention.** [AB09] p. 79 imposes
   `S(n) > log n` as a standing convention. The received `SPACE` does not. Which
   received statements silently depend on it, and does any become false or vacuous
   below it? (E.g. is `LOGSPACE_subset_P` robust at `n = 0, 1`? Is `SPACE s` for
   `s = 0` the class of … what, exactly? Is that intended?)
3. **`configBound`** (`ConfigCount.lean`):
   `(card State + 1) · (n + 2) · 3^(k·(2s+1)) · (2s+1)^k`. Re-derive the count
   independently (state ⊕ halted, input head positions, work-tape windows over
   `Option Bool` contents, head positions within windows) and confirm the formula
   over-counts rather than under-counts in every factor. Then check
   `ComputesInTime.of_spaceUsed_le` really is the "space-bounded ⟹ time-bounded at
   the config count" direction of [AB09, Claim 4.4(1)] (deterministic case), with
   no hidden halting or boundedness assumption.
4. **The `LogProg`/ARM contracts.** `compile_correct`/`compile_space` (atomic
   oracle-call semantics discharged by compilation) and
   `arm_decides`/`arm_decides_poly` (register machine + LOGSPACE deciders ⟹
   `L ∈ LOGSPACE`): are the hypotheses (the `CleanRun` notion; `AHalt` with `PreS`
   and the `K · logSpace`-bit register bound) strong enough to be sound and weak
   enough to be usable? Is there any gap between "the abstract machine decides `L`"
   and "the compiled `FinTM` decides `L`" (input-head handling, call-tape blanking,
   space of the call banks)?
5. **`ImplicitlyLogspaceComputable`** (deviation 3): do the 0-based index and the
   `i < |f(x)|` length language preserve [AB09, Def 4.16]'s intent, in particular
   for the planned `≤ₗ` (chapter 4) where composition (Lemma 4.17) will quantify
   over these languages? Is `indexLang`'s `pairEncode x (Nat.bits i)` encoding
   collision-free at `i = 0` (`Nat.bits 0 = []`)?
6. **`clockTM_spec` / `preTM_computes` / `scanPre_pairEncode_append`**
   (`ClockLoop.lean`, `CodePrefix.lean`): check the budget arithmetic shapes and
   that the clock's `ctrVal s` decode matches what `diagLang` needs (no off-by-one
   between the clock's budget and `diagSim`'s simulation bound).
7. **Reception fitness.** Chapters 3-4 will define `NSPACE`, space
   constructibility, `PSPACE`/`NL`, logspace reductions, and configuration graphs
   *on top of* these definitions (plan §2.4-2.5). From what you see, is any
   received definition shaped so that this program hits a wall (e.g. `SPACE`'s
   `c · s n` absorption interacting badly with the space hierarchy's tight bounds,
   or `ComputesInSpace`'s per-input existential time)? Name the wall now, not in
   phase P4.3.

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide: **blocker** = chapters 3-4 would build on a wrong statement;
**major** = statement is fixable but materially misleading as is; **minor** = edge
case or naming/attribution defect; **note** = observation, no change required.

The gate closes on a round with zero blockers and zero majors (`workflow.md` §3).
Findings go verbatim into `audits/ch34-p0-findings.md`.
