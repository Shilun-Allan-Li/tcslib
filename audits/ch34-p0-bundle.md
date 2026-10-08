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


# ===== ATTACHMENTS =====


## ===== AroraBarakChapters3-4Plan.md =====

```
# Formalization Plan: Arora-Barak Chapters 3-4 — Diagonalization and Space Complexity

**Status: draft for maintainer review (2026-10-08).** Nothing below is decided until the
open questions in §7 are answered; the decision log (§8) records every row as *Proposed*.

Continuation of the Arora-Barak campaign (`AroraBarakChapter1Plan.md`,
`AroraBarakChapter2Plan.md`, both closed), now working from `main`: branch
`complexity/arora-barak-ch3-4`, created from `origin/main` at `99b187fc`. The methodology
is unchanged (`workflow.md`): audited statement phases with proof sketches,
cross-vendor LLM audit gates closing on zero blockers/majors, then fill epochs of
disjoint-ownership batches with zip delivery, drift attestations, and a blueprint
increment at closure. Artifact names: `audits/ch3-*`, `audits/ch4-*`, `briefs/ch3-*`,
`briefs/ch4-*`.

**What changed since Chapter 2.** Much of this plan's raw material already exists on
`main`, written by Hydroxyi (commit `f70c57c2`, 2026-10-06, sorry-free) — notably a time
hierarchy theorem, `P ⊊ EXP`, `SPACE`/`LOGSPACE`, implicitly logspace functions,
`LOGSPACE ⊆ P`, and a logspace register-machine compiler. The plan therefore starts with
a *reception* phase (§4, P0) that brings that surface under the campaign's audit, and
builds Chapter 4 on Hydroxyi's program layers rather than on hand-built machines.

## 1. Scope

Sources: [AB09] ch. 3, pp. 68-77; ch. 4, pp. 78-94. "Exists" means proved on `main`
today; tiers are **core** (this campaign), **core-late** (this campaign, last, and the
first candidates to descope), **deferred** (backlog).

### Chapter 3 — Diagonalization

| Item | Status on `main` | Tier |
|---|---|---|
| Machines as strings: every string is a code, every machine has infinitely many codes (§3 intro) | Exists (ch-1 `Encoding`, padding lemmas) | — |
| **Thm 3.1** time hierarchy | Exists at **`f²` strength**: `Complexity.time_hierarchy` (`A·(f n + n + 1)² ≤ g n` eventually ⇒ `DTIME f ⊂ DTIME (g + 1)`), `time_hierarchy_of_pos`, `P_ssubset_EXP` (`TimeHierarchy/`) | Received in P0; **strengthened to book form via Hennie-Stearns** (user decision 2026-10-08, §2.1) |
| Def 3.4 oracle TMs | Raw model exists: `Turing.OracleTM`, `WellFormed`, lockstep embeddings (`TuringMachine/Oracle.lean`, audited ch-1) | Core: bundle + oracle NDTM (P3.1) |
| Def 3.5 `Pᴼ`, `NPᴼ` | Missing | Core (P3.1) |
| Ex 3.6(1) `co-SAT ∈ P^SAT`; (2) `O ∈ P ⇒ Pᴼ = P` | Missing | Core (P3.1) |
| Ex 3.6(3) `P^EXPCOM = NP^EXPCOM = EXP` | Missing | **Core** (user decision 2026-10-08, CH34-Q4; P3.2) |
| **Thm 3.7** Baker-Gill-Solovay | Missing | Core (P3.2) |
| Ex 3.5 a non-time-constructible function | Missing | Core (P3.2, cheap) |
| **Thm 3.2** nondeterministic time hierarchy (lazy diagonalization), with Ex 2.6 universal NDTM | Missing (no NDTM codes, no universal NDTM) | **Core, mandatory, book strength** — linear-overhead universal NDTM (user decisions 2026-10-08; P3.3, CH34-Q8) |
| **Thm 3.3** Ladner, its Claim, and Ex 3.6(a)(b) | Missing | Core-late (P3.4) |
| Ex 3.1, 3.3, 3.4, 3.7-3.9; relativized hierarchy statements; Remark 3.8 and §3.4.1 (expository) | — | Deferred |

### Chapter 4 — Space complexity

| Item | Status on `main` | Tier |
|---|---|---|
| Def 4.1 `SPACE` | Exists: `Complexity.SPACE` (deterministic, halting, visited work cells, `c · s n`) | Received in P0 |
| Def 4.1 `NSPACE`; space-constructibility | Missing (no NDTM space measure at all) | Core (P4.1) |
| Thm 4.2 (i) `DTIME ⊆ SPACE`, (ii) `SPACE ⊆ NSPACE` | Missing | Core (P4.1) |
| Thm 4.2 (iii) `NSPACE(S) ⊆ DTIME(2^O(S))` | Deterministic core exists (`ComputesInTime.of_spaceUsed_le`, `configBound`); nondeterministic search missing | Core (P4.2) |
| Claim 4.4 (1) configuration count; (2) `O(S)`-size adjacency CNF | (1) deterministic only (`configBound`); (2) missing | Core (P4.2 / P4.3) |
| Def 4.5 `PSPACE`, `NPSPACE`, `L`, `NL` | `L` exists as `LOGSPACE` (`logSpace n = ⌊log₂ n⌋ + 1`); rest missing | Core (P4.1) |
| Ex 4.6 `3SAT ∈ PSPACE`, `NP ⊆ PSPACE` | Missing | Core (P4.1) |
| Ex 4.7 `EVEN`, `MULT ∈ L`; `PATH ∈ NL` | `dblLang ∈ LOGSPACE` exists as an ARM example | Core (P4.1 / P4.4) |
| **Thm 4.8** space hierarchy, with Ex 4.1 space-universal TM | Missing (both universal machines are time-only) | Core (P4.3) |
| Def 4.9 `PSPACE`-hard/complete; Def 4.10 QBF; `TQBF`; **Thm 4.13** | Missing (no QBF anywhere; `PolyHierarchy/` quantifies over strings, not formulas) | Core (P4.3) |
| **Thm 4.14** Savitch; `PSPACE = NPSPACE` | Missing | Core (P4.2) |
| Def 4.16 implicit logspace computability | Exists: `ImplicitlyLogspaceComputable` | Received in P0 |
| `≤ₗ`, `NL`-completeness; **Lemma 4.17** | Missing; a special case exists (`UnaryLogspace.counterProg`) | Core (P4.4) |
| **Thm 4.18** `PATH` is `NL`-complete | Missing (no `PATH` language or graph encoding) | Core (P4.4) |
| **Thm 4.20** Immerman-Szelepcsényi; **Cor 4.21** | Missing | Core (P4.4) |
| `L ⊆ NL ⊆ P`, `L ⊊ PSPACE` (the chain on p. 92) | `LOGSPACE ⊆ P` exists | Core (assembled in P4.2-P4.3) |
| Ex 3.2 `SPACE(n) ≠ NP` | Missing | Core (P4.3, cheap once Thm 4.8 exists) |
| Ex 4.3 (every nontrivial language is `NL`-complete under `≤ₚ`), Ex 4.10 (finite-game determinacy) | Missing | Core, cheap (P4.2 / P4.3) |
| Def 4.19 read-once certificates; Ex 4.7 | Missing | Deferred: Thm 4.20 can be proved directly on NDTMs |
| Example 4.15 (QBF game); Ex 4.2, 4.4-4.6, 4.8, 4.9, 4.12 | — | Deferred |

## 2. Foundation decisions (proposed; each is seeded to the relevant audit)

### 2.1 Thm 3.1 is received at `f²` strength, then strengthened to book form

Hydroxyi's theorem consumes the linear-time `Turing.universal` over one-work-tape codes,
so converting an arbitrary machine to that normal form costs a square. The book's
`f log f` needs the Hennie-Stearns `O(T log T)` simulation ([AB09] §1.7), which the
Chapter-1 plan deferred as phase 5. The received form still yields `P ⊊ EXP`, but **not**
the book's illustrative `DTIME(n) ⊊ DTIME(n^1.5)`, since `n²` exceeds `n^1.5`.

**Decision (user, 2026-10-08, CH34-Q3): strengthen.** Before the chapter-3/4 fill
epochs, the campaign builds (a) the Hennie-Stearns `k`-work-tapes-to-2 conversion at
`C·T log T` ([AB09] §1.7: parallel tracks, buffer zones of size `2^i`, amortized
shifts), and (b) a universal machine over *two-work-tape* codes at linear overhead.
Hydroxyi's diagonal argument then re-derives Thm 3.1 at `f log f`, and Theorem 1.9
reaches book strength, closing chapter 1's deferred phase 5. Until that lands, the
received form is documented as delivered strength, never as Thm 3.1 verbatim. Both
constructions are consumers of the machine-routine layer (§4a).

### 2.2 Oracle classes

- **A finite bundle `FinOracleTM`** carrying `Fintype`/`DecidableEq` for states, with
  `WellFormed` as a field. This is the Chapter-1 phase-1 obligation: "oracle complexity
  classes will introduce a finite oracle-machine bundle".
- **An oracle NDTM** combining the binary-choice NDTM with the oracle step. Def 3.4 says
  only that nondeterministic oracle machines are "defined similarly".
- **`Pᴼ` and `NPᴼ` mirror `P` and `NTIME`** literally: the same `c · T n` and
  `n^c + 1` normal forms, with all-branch halting for `NPᴼ`.
- **Query tape:** the existing persistent convention (no auto-erase). The Chapter-1
  obligation to prove polynomial equivalence with the auto-erased convention is scheduled
  only if some consumer imports an invariance; none in this plan does.
- **One general lemma does most of the light work:** `L ≤ₚ O ⇒ L ∈ Pᴼ`. It writes `f(x)`
  on the query tape, queries, and copies the answer. Ex 3.6(1), the `A` half of Thm 3.7,
  and `NP ⊆ P^SAT` all follow from it.

### 2.3 Baker-Gill-Solovay

- **The `B` half follows the book.** `U_B ∈ NP^B` is a small oracle-NDTM construction.
  `U_B ∉ P^B` is the stage construction. It is mathematics, not machine-building: runs
  that agree on every queried string agree (by lockstep); a run of `t` steps queries at
  most `t` strings, each of length at most `t` (`queryString_length_le` exists); and
  `FinOracleTM`s can be enumerated with every machine recurring infinitely often, through
  `Fintype.equivFin` plus state relabelling, with no universal oracle machine needed.
- **The `A` half takes the book's route: `A = EXPCOM`** (user decision 2026-10-08,
  CH34-Q4 — preferred as the more natural oracle, with `P^EXPCOM = NP^EXPCOM = EXP` the
  memorable byproduct), via the chain `EXP ⊆ P^EXPCOM ⊆ NP^EXPCOM ⊆ EXP` (Ex 3.6(3)).
  - `EXP ⊆ P^EXPCOM`: the reduction `x ↦ ⟨M_L, x, 1^(n+1)^c⟩` (constant prefix, copy,
    unary padding emitter — chapter-2 padding-cluster precedents), then one query
    through the §2.2 lemma.
  - `NP^EXPCOM ⊆ EXP` is **a fill summit**: for each language, a deterministic
    exponential-time machine that enumerates all choice words of the fixed oracle NDTM
    (the `NP_subset_EXP` enumerator pattern), simulates it step by step under each word
    (2B-style invariant), and answers each query `⟨M', x', 1^(n')⟩` by parsing it
    (CodeParser) and running the timed universal machine for `2^(n')` steps (the
    `timed_universal` bridge), under a `2^O(p(n))` ledger. Continuation budget certain.
  - The machine-light alternative — [BGS75, Thm 1]'s own self-referential
    `A = K(A) = {⟨i, x, 0ⁿ⟩ : NPᵢᴬ accepts x in < n steps}`, well-founded because a
    `< n`-step run queries only shorter strings — is **recorded as the fallback**: if
    the summit stalls, switching requires only the oracle-locality lemma (needed for
    the `B` half anyway) plus a maintainer sign-off, and the blueprint would cite
    [BGS75, Thm 1] with a deviation note.

### 2.4 Space

- **Reuse `SPACE` and `LOGSPACE` unchanged**: deterministic, halting, counting visited
  work cells summed over the work tapes, with input and output excluded. [AB09] is itself
  inconsistent here: Def 4.1 counts *visited* cells for `SPACE` but *non-blank* cells for
  `NSPACE`. The vendored `Deterministic.lean` docstring and `SpaceComplexity/Basic.lean`
  currently disagree about what [AB09] says. P0 fixes the documentation, and the visited
  measure is used for both classes.
- **`NSPACE` (CH34-Q7, provisional answer: all branches halt).** It needs a new NDTM space
  measure along `runWith`, adapting the `visitedByTapeHead` pattern to choice words.
  Provisionally, `N` decides `L` in space `s` if on every input there is some `T` with
  `HaltsWithin x T`, every choice word stays within `s(|x|)` cells, and `x ∈ L` iff some
  choice word accepts. All-branch halting matches `NTIME`, lax-434930's convention and
  Remark 4.3's alternative, and it makes the configuration-count arguments direct.
- **Space-constructibility mirrors `TimeConstructible`.** A machine writes
  `(S |x|).bits` within space `c · (S |x|)`, and the definition carries
  `∀ n, logSpace n ≤ S n`, which is [AB09]'s standing `S(n) > log n` (p. 79).
  Theorems needing only weaker hypotheses say so. This is seeded to the P4.1 audit.
- **The classes:** `PSPACE := ⋃ c, SPACE (n^c + 1)`, and likewise `NPSPACE`;
  `NL := NSPACE logSpace`; `coNL` in complement form, like `coNP`.
- **`≤ₗ` reuses `ImplicitlyLogspaceComputable`** (Def 4.16, with its documented
  divergences: `C(|x|+1)^c` length bound and 0-based index).

### 2.5 Machine substrate for Chapter 4: program layers, not hand-built machines

Chapter 2's lesson, and the backlog's machine-routine-layer entry, is that hand-built
machines dominate the cost. For space the relevant layers already exist on `main`:

- **`LogProg.ARM`** (`SpaceComplexity/Machines/`) is an abstract register machine with
  `O(log n)`-bit registers and calls to `LOGSPACE` deciders. It compiles to `FinTM` with a
  space theorem (`compile_space`, `arm_decides`, `arm_decides_poly`). It is
  **deterministic only**.
- **`CounterProg`** (`TuringMachine/CounterProg{,Run}.lean`) has unary registers and
  forward input reading. It compiles with a time bound (`t` steps become at most
  `t(2t+3)`), so it suits the `2^O(S)`-time searches, where register values of size
  `2^O(S)` are affordable. Its input is one-way (`rd` only advances), but a configuration
  successor must read the input at the simulated head. Those searches therefore need
  either ARM-style indexed input access or a rewind instruction.

Proposed extensions, each a P4.x infrastructure statement with its own audit:

1. **A nondeterministic ARM**: a `choose` instruction compiling to `FinNDTM`, with the
   space theorem carried over. This serves `PATH ∈ NL`, Immerman-Szelepcsényi and
   Cor 4.21.
2. **A polynomial-width ARM variant** with registers of `poly(n)` bits, for the
   `PSPACE`-level algorithms: `TQBF ∈ PSPACE`, `NP ⊆ PSPACE`, Savitch at polynomial
   level. It is either a generalization of `compile_space` or a sibling.
3. **A configuration codec**, shared by Thm 4.2(iii), Savitch, Thm 4.18, Cor 4.21 and
   `TQBF` hardness. It encodes the configurations of a fixed machine, with work tapes
   windowed to `s` cells and the input head as a separate register, as `O(s)`-bit
   register contents, and provides a successor/adjacency test as a program. The counting
   half adapts cslib's new upstream `MultiTape/ConfigBound.lean` design (Sept 2026,
   `Storage`/`Cfg.core`) and extends Hydroxyi's deterministic `ConfigCount` to NDTMs.
   It must be cited and adapted, not vendored: cslib targets a newer Lean with the
   module system.

This requires Hydroxyi's agreement, since these are their modules (CH34-Q2).

### 2.6 Formulas and graphs

- **The QBF matrix (CH34-Q5).** Def 4.10 allows a general unquantified matrix; we have
  only `Std.Sat.CNF ℕ` and the DNF dual. Provisional choice: prenex QBF with a **CNF
  matrix**, reusing the CNF carrier, serialization and parser. [AB09] notes on p. 83 that
  the CNF restriction is harmless via auxiliary variables, so `TQBF` hardness pays a
  Tseitin step. A general-formula carrier is the alternative, which Chapter 5 and a
  general `TAUTOLOGY` would also want.
- **`PATH` needs the campaign's first graph encoding**: an adjacency-matrix
  serialization plus `s`, `t` in binary via `pairEncode`, with a parser and the
  `codeFallback`-style totalization. It stays in-house in `Complexity/`, with
  `GraphTheory.Digraph.Reachable` as the semantic target.

### 2.7 Universal machines

- **Thm 4.8 needs a space-efficient universal machine (Ex 4.1).** The existing `universal`
  and `timed_universal` are time-only, and their code scheme covers only the
  one-work-tape binary normal form. So either the Chapter-1 robustness conversions
  (`one_work_tape`, alphabet reduction) gain space theorems, or a fresh space-universal
  machine takes multi-tape codes. This is the largest single risk in Chapter 4 (§6).
- **Thm 3.2 needs NDTM codes and a clocked universal NDTM (Ex 2.6), at linear
  overhead** (user decision 2026-10-08, CH34-Q8). Polynomial overhead would deliver only
  `f(n+1)^c = o(g(n))`; linear overhead gives the book's `f(n+1) = o(g(n))`. The
  guess-then-verify technique (guess the whole tableau of choice/configuration data,
  then check each tape's consistency in one pass — Book-Greibach style) achieves a
  code-dependent constant factor, which is the strongest form possible: a simulation of
  `t` steps cannot run faster than the `t` steps it reproduces, and the code-dependent
  constant is necessary for the same reason as chapter 1's Argument E. Another
  routine-layer consumer.

## 3. Architecture and module layout

New campaign directories (namespace `Complexity`, facades per policy §1):

| Directory | Contents |
|---|---|
| `TuringMachine/OracleFinite.lean`, `TuringMachine/OracleNondeterministic.lean` | `FinOracleTM`, oracle NDTM, runs, and lockstep embeddings of plain machines |
| `ClassOracle/` | `Pᴼ`, `NPᴼ`, the `≤ₚ ⇒ Pᴼ` lemma, Ex 3.6, oracle-machine enumeration, `Relativization.lean` (Thm 3.7) |
| `Diagonalization/` | `NTimeHierarchy.lean` (Thm 3.2), `Ladner.lean` (Thm 3.3), `NotTimeConstructible.lean` (Ex 3.5) |
| `TuringMachine/NondeterministicSpace.lean`, `TuringMachine/NDCodes.lean` | NDTM space measure; NDTM codes and the universal NDTM |
| `SpaceComplexity/` (extending Hydroxyi's tree, subject to CH34-Q2) | `NSPACE.lean`, `Classes.lean` (`PSPACE`/`NPSPACE`/`NL`/`coNL`), `Constructible.lean`, `Inclusions.lean` (Thm 4.2), `ConfigGraph.lean`, `Savitch.lean`, `Hierarchy.lean`, `Logspace/{Reductions,Path,ImmermanSzelepcsenyi}.lean` |
| `Formulas/QBF.lean`, `Formulas/QBFEncoding.lean`; `ClassPSPACE/TQBF.lean` | the QBF carrier and serialization; Thm 4.13 |

Chapter-1/2 files stay frozen at their audited surface. Additions to Hydroxyi's trees
follow whatever ownership rule CH34-Q2 sets.

## 4. Phasing

Statement phases, each gated by an audit before the next one lands. The order reflects
infrastructure dependencies and retires risk early: the light half of Chapter 3, then
Chapter 4, then Chapter 3's two heavy diagonalizations.

| Phase | Contents | New sorried statements (est.) |
|---|---|---|
| **P0 — Reception** | Statements-only audit of the existing surface the campaign will build on: `time_hierarchy`, `P_ssubset_EXP`, `SPACE`, `LOGSPACE`, `ImplicitlyLogspaceComputable`, `LOGSPACE_subset_P`, `ComputesInTime.of_spaceUsed_le`, and the `arm_decides` and `compile_space` contracts. Docstring fixes (the §2.4 inconsistency; the stale "spec phase, sorried" notes in `Build/*`). Drift baseline recorded. No new sorries. | 0 |
| **P3.1 — Oracle classes** | `FinOracleTM`, the oracle NDTM, `Pᴼ`, `NPᴼ`; `P ⊆ Pᴼ`, `NPᴼ` contains `Pᴼ`; the `≤ₚ ⇒ Pᴼ` lemma; Ex 3.6(1)(2); `NP ⊆ P^SAT` as a sanity theorem | ~10 |
| **P3.2 — Relativization** | Oracle-machine enumeration; `U_B ∈ NP^B`; the stage construction; the EXPCOM cluster (`EXPCOM`, `EXP ⊆ P^EXPCOM`, `NP^EXPCOM ⊆ EXP`, `P^EXPCOM = NP^EXPCOM = EXP` — Ex 3.6(3)); Thm 3.7; Ex 3.5 | ~11 |
| **P4.1 — Space classes** | NDTM space measure, `NSPACE`, space-constructibility, the classes; Thm 4.2(i)(ii); `L ⊆ NL`; `3SAT ∈ PSPACE`, `NP ⊆ PSPACE`; `EVEN`, `MULT ∈ L`; the nondeterministic and polynomial-width ARM interfaces | ~14 |
| **P4.2 — Configuration graphs** | The configuration codec; Claim 4.4(1) for NDTMs; Thm 4.2(iii); Savitch; `PSPACE = NPSPACE`; `NL ⊆ P`; Ex 4.3 | ~10 |
| **P4.3 — `PSPACE`-completeness and space hierarchy** | Def 4.9; the QBF carrier, `TQBF`, Claim 4.4(2), Thm 4.13 (both halves); the space-universal machine (Ex 4.1); Thm 4.8; `L ⊊ PSPACE`; Ex 3.2; Ex 4.10 | ~12 |
| **P4.4 — Logspace and `NL`** | `≤ₗ`, `NL`-completeness, Lemma 4.17; the graph encoding, `PATH ∈ NL`, Thm 4.18; Thm 4.20; Cor 4.21 | ~10 |
| **P3.3 — Nondeterministic hierarchy** | NDTM codes, the clocked universal NDTM (Ex 2.6), Thm 3.2 at delivered strength | ~6 |
| **P3.4 — Ladner** | `SAT_H`; Ex 3.6(a) (`H` in polynomial time); the Claim; Ex 3.6(b); Thm 3.3 | ~6 |

That is roughly 78 new audited statements, against Chapter 2's 59.

### 4a. Pre-campaign infrastructure (user decisions 2026-10-08)

The machine-routine layer and its two headline consumers run **in parallel with the
statement phases**, and gate only the fill epochs:

1. **The routine layer** (`machine-library-design.md` §12, to be written): bank
   embedding, seam composition, catalog promotion — **scoped to amply support the
   chapter-1/2 retrofit**, not just the new consumers. Its catalog therefore covers the
   privately re-derived bank / relocation / dispatch / frame families of `Build/*`,
   `Universal*`, and `CookLevin/Hardness.lean` (the backlog retrofit entry's list), and
   **every routine carries a space cost alongside its time cost** from the start, so
   chapter 4 and the space statements (P4.x) can consume it without a second pass. The
   P0/P4.1 space statements are drafted while the layer is being designed, precisely so
   they can inform what else the layer needs (CH34-Q1).
2. **Hennie-Stearns + the two-work-tape universal machine** (§2.1): the layer's first
   new consumers, giving Thms 1.9 and 3.1 at book strength. The two-tape universal is a
   rewrite of `Universal.lean`, making it the natural retrofit pilot. Candidate bonus,
   to be checked at design time: carrying space bounds through it may also yield the
   space-efficient universal machine that Thm 4.8 needs (Ex 4.1).
3. **The chapter-1/2 retrofit** itself is *not* a gate for chapters 3-4: public surfaces
   are frozen, so retrofit batches run alongside the chapter-3/4 phases under the
   standard sweep + traversal + audit protocol.

**Fill campaign.** Fill work starts after the gates close, in epochs ordered by risk as
before. Two infrastructure prerequisites gate the machine-heavy epochs:

- the machine-routine layer as scoped above;
- the ARM extensions of §2.5.

**Integration with `main`.** Proposed: one PR per closed chapter (Chapter 3's light half
may go earlier), not one campaign-sized PR like #3. Main's CI runs only on pushes to
`main`, so each PR carries the local evidence: sweep, axiom prints, and the blueprint web
build.

## 5. Prior art to consult (design only; cite, never transcribe)

- **Édouard Bonnet's Lax Archive entries** (Lean 4.33, Mathlib `db584cd6`). They use a
  different machine model (stack machines, one work tape), so none of their code ports.
  - lax-434930 `classical-complexity` (commit `0c084031…`): `L ⊆ NL ⊆ P ⊆ NP ⊆ PSPACE =
    NPSPACE ⊆ EXPTIME`. Its space model counts every visited work cell, requires every
    branch to halt, and uses `c · log₂(n+2)`. It embeds the lax-307052 Savitch proof.
  - lax-362205 Immerman-Szelepcsényi (`EdouardBonnet/immerman-szelepcsenyi` @
    `e0ffe91e`): inductive counting on finite configuration graphs.
  - lax-783278 Arc Kayles: a machine-to-game `PSPACE`-hardness that bears on the shape of
    the `TQBF` hardness proof.
  - Licences: lax-434930 states Apache-2.0 for its incorporated helpers; the others' pages
    state none. Check each before any design adaptation, under the 2026-10-06 citation
    discipline.
- **cslib upstream** (`leanprover/cslib` `main`): `MultiTape/ConfigBound.lean` and
  `TapeLemmas.lean` (space-bounded configuration counting, `exists_spaceUsedByTape_max`).
  We already diverge from cslib's relational `MultiTapeNTM` (Chapter-2 decision log).
- **Szymon Toruńczyk, lax-218471**: compositional polynomial-time computation with
  black-box subroutines. It bears on the §2.2 `≤ₚ ⇒ Pᴼ` lemma and Ex 3.6(2).

## 6. Risks and honest effort assessment

- **Chapter 4 is the larger half**, and almost all of it is machine work with *space*
  ledgers. Every existing campaign construction (Chapters 1-2, `Build/*`) is time-only,
  and `machine-library-design.md` lists "no space bounds" among its non-goals. Building
  Chapter 4 on hand-built machines would repeat Chapter 2's cost profile several times
  over. The §2.5 program layers are the mitigation, and the plan depends on them.
- **The summits**, in rough order of size:
  1. the space-universal machine plus Thm 4.8 (or space theorems for the Chapter-1
     conversions);
  2. the `NP^EXPCOM ⊆ EXP` simulator (§2.3 — choice-word enumeration, per-step oracle
     NDTM simulation, and timed-universal query answering compounded in one machine);
  3. `TQBF` hardness (a polynomial-time emitter of the `ψᵢ` formula, comparable to the
     Cook-Levin emitter);
  4. Ladner's `H` in polynomial time;
  5. the universal NDTM at linear overhead (guess-then-verify, §2.7);
  6. Thm 4.2(iii) and Savitch over the configuration codec;
  7. Immerman-Szelepcsényi;
  8. Lemma 4.17.
- **Delivered-strength honesty**: Thms 3.1 and 3.2 land weaker than the book unless
  Hennie-Stearns is built. Every docstring must say so; this was the round-1 lesson of
  every prior audit.
- **Coordination**: Chapter 4 extends a colleague's live tree, and the plan needs their
  agreement before P4.1.
- **Estimated scale**: roughly 75 statements over eight statement phases plus P0. The
  total is larger than Chapter 2; Chapter 3 alone is comparable to Chapter 1.

## 7. Open design questions (human review required)

Answered 2026-10-08 by the maintainer except where marked open; the register below is
the record, and `backlog.md` §1 gets only the open ones.

1. **CH34-Q1 — sequencing against the machine-routine layer.** **Answered: yes to
   both.** Statement phases run in parallel with the §12 design; the space statements
   are drafted early to inform the layer's scope; the catalog records space costs
   alongside time. Addendum (same date): the layer is scoped to **amply support the
   chapter-1/2 retrofit** as well (§4a).
2. **CH34-Q2 — alignment with Hydroxyi.** **Answered: extend in place, co-owned.**
3. **CH34-Q3 — Thm 3.1 strength.** **Answered: strengthen** — Hennie-Stearns + the
   two-work-tape universal before the fill epochs (§2.1, §4a).
4. **CH34-Q4 — the `A` half of Thm 3.7.** **Answered (2026-10-08): the book's
   `EXPCOM` route** — more natural, and `P^EXPCOM = NP^EXPCOM = EXP` is the memorable
   identity; Ex 3.6(3) is core and `NP^EXPCOM ⊆ EXP` joins the summit list. Research
   note retained: the machine-light self-referential oracle is [BGS75, Thm 1]'s own
   proof (verified against the scanned original, pp. 433-434) and stays recorded as
   the fallback (§2.3). [BGS75] detail for the P3.1 audit: the polynomial clock must
   hold under *every* oracle, which constrains how `Pᴼ`/`NPᴼ` quantify the time bound.
5. **CH34-Q5 — QBF matrix.** **Answered: CNF.**
6. **CH34-Q6 — tiers.** **Answered: Thm 3.2 mandatory; Thm 3.3 (Ladner) core-late.**
7. **CH34-Q7 — `NSPACE` halting convention.** **Answered: all branches halt.**
8. **CH34-Q8 — universal-NDTM overhead.** **Answered (2026-10-08): linear overhead**,
   the strongest form possible (§2.7) — Thm 3.2 lands at the book's
   `f(n+1) = o(g(n))`.

## 8. Decision log

| Decision | Status |
|---|---|
| Chapters 3-4 run as one campaign on `complexity/arora-barak-ch3-4` (from `main` @ `99b187fc`), same methodology as Chapters 1-2; artifacts `ch3-*`/`ch4-*` | Proposed |
| Existing sorry-free Chapter-3/4 material on `main` (Hydroxyi, `f70c57c2`) is received and audited (P0), never duplicated | Proposed |
| Prior-art survey (2026-10-08): repository inventory (§1 tables); Bonnet lax-434930/362205/783278, cslib `ConfigBound`, Toruńczyk lax-218471 (§5) | Recorded |
| Chapter 4 machine work goes through program layers (`LogProg.ARM`, `CounterProg`, proposed extensions §2.5) | Proposed |
| §2 foundation choices and §7 provisional answers | **Answered 2026-10-08** (user): Q1 yes to both, Q2 extend in place co-owned, Q3 strengthen, Q5 CNF, Q6 Thm 3.2 mandatory / Ladner core-late, Q7 all branches halt. Q4 and Q8 open |
| Routine layer set up in parallel with the statement phases, scoped to **amply support the ch-1/2 retrofit** (full bank/relocation/dispatch/frame catalog), with space costs throughout; Hennie-Stearns + two-tape universal as first consumers; retrofit itself not a gate (§4a) | Decided (user, 2026-10-08) |
| CH34-Q4 answered (user, 2026-10-08): **EXPCOM route** for the `A` half of Thm 3.7 — Ex 3.6(3) promoted to core, the `NP^EXPCOM ⊆ EXP` simulator added to the summit list (continuation budget certain); [BGS75, Thm 1]'s self-referential oracle recorded as fallback | Decided |
| CH34-Q8 answered (user, 2026-10-08): the universal NDTM is built at **linear overhead** (guess-then-verify), so Thm 3.2 lands at book strength `f(n+1) = o(g(n))` | Decided |
| CH34-Q4 research (2026-10-08): the machine-light oracle `A = K(A)` **is** [BGS75]'s own Theorem 1 (verified against the scanned original, pp. 433-434), so no deviation from the primary source; [AB09]'s `EXPCOM` is the substitution. Awaiting maintainer confirmation of the route | Recorded |
| Citation audit (2026-10-08), prompted by the maintainer: no missing code-inspiration citation found in campaign-authored Lean code — vendored cslib files carry full headers (pin `a3747758`), `Composition.lean` cites [Balbach22], `Build/*` + `machine-library-design.md` §1-11 were frozen 2026-10-03, two days **before** the first Bonnet examination (2026-10-05, scratchpad-only, never imported; backlog records the after-the-fact cost comparison as convergence). No brief ever carried external code. Hydroxyi's `TimeHierarchy//SpaceComplexity//PolyHierarchy/` trees cite only [AB09]; two design similarities flagged to *ask* (not assertions): `LogProg` compiler vs lax-434930's `TimeCompiler`; `ConfigCount.core` vs cslib `ConfigBound`'s `Cfg.core` (upstream 2026-09-14). §12 citation duty ([lax-434930], Apache-2.0) remains binding when that design is written | Recorded |

```


## ===== policy.md =====

```
# TCSlib Contribution Policy

Standards for all Lean contributions to this repository, whether written by humans or by
agents. This document covers three things: **modularity** (how code is organized),
**attribution** (how every result is traced to a source), and **proof sketches** (how every
formal proof is accompanied by readable mathematics).

It complements, and does not replace:

- `workflow.md` — the campaign formalization process (phases, audit gates, fill epochs)
  that produces code meeting these standards.
- `.github/copilot-instructions.md` — build workflows, import rules, CI integration points.
- `AGENTS.md` / `.claude/CLAUDE.md` — the sorry-ladder proof workflow and agent roster.
- `blueprint/BLUEPRINT_PIPELINE.md` — how blueprint entries are generated and validated.

Where this document names an existing mechanism (blueprint macros, hygiene scripts), the
policy is to *use that mechanism*, not to invent a parallel one.

## 1. Modularity

**Layout.** Content lives at `TCSlib/<Area>/<Topic>/<Piece>.lean`, one coherent concept or
lemma cluster per file, with a facade file `TCSlib/<Area>/<Topic>.lean` that imports every
child and carries a `/-! -/` module docstring with a `## Contents` list (one line per child).
See `TCSlib/Complexity/NPReductions.lean` for the reference example.

**File size.** Target 150–600 lines per math file. A file approaching 1000 lines should be
split unless there is a positive reason not to (e.g. a single long proof that cannot be
usefully decomposed).

**Exports.** Every new topic facade must be imported from `TCSlib.lean`. CI only builds what
is reachable from `TCSlib.lean`; an unexported file is invisible to CI, docs, and the
blueprint.

**Imports.** Precise module imports only. A bare `import Mathlib` fails CI. Import only what
the file uses.

**Namespaces.** Namespaces are area-local: pick one namespace root per topic and use it
consistently within that topic. Do not leak auxiliary definitions into the root namespace;
mark internal helpers `private` or put them in a dedicated inner namespace.
*Model registry exception*: a model-defining **type** (a machine, circuit, formula, or
decision-tree model) may live at the root namespace, Mathlib-style, provided it is
registered in the catalog facade `TCSlib/ComputationalModels.lean`; its operations and
lemmas still live in the type's own namespace. Anything else at root is a leak.

**Layering.** Keep definition files separate from heavyweight theorem files, so that
downstream work can import a model or a class definition without pulling in every proof about
it. When a development has both a "raw/general" layer and a "bundled" layer (e.g. a machine
model that is parametric in its types, plus a bundled version carrying finiteness instances),
headline definitions and theorems are stated against the bundled layer; the raw layer is
internal plumbing.

**Helpers.** Foundational helper lemmas that serve a whole area belong in that area's
`Basic.lean`, not in the file that first needed them.

**File header.** Every math file begins with the Mathlib-style copyright block, its imports,
the repo-standard options

```
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
```

then a module docstring containing `# Title`, `## Main definitions`, `## Main results`, and
`## References` (see §2).

## 2. Attribution

Every mathematical statement in the library must be traceable to a source, at the level of
precision of a textbook theorem number or a paper section.

**File-level.** Every math file's module docstring contains a `## References` section giving
full citations with short tags, e.g.

```
## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
```

**Declaration-level.** Every definition, theorem, and lemma that corresponds to a result in
a source carries the tag with a precise location in its docstring: `[AB09, Claim 1.6]`,
`[AB09, §1.7]`, `[GRS25, Thm 4.2.1]`. Purely technical glue lemmas with no textbook
counterpart may omit the tag; anything a reader would recognize as "a result" may not.

**Deviations.** If the formal statement deviates from the source — different constants,
strengthened or weakened hypotheses, a reformulation — the docstring must say so and briefly
say why (e.g. "stated with explicit constant 5k rather than O(·), following the proof").

**Statement prose.** Every public declaration's docstring begins with a natural-language
statement of what it asserts (for a definition: what it is), precise enough that a reader
could judge the formalization's fidelity without parsing the Lean. The `[Tag, location]`
citation and any deviation note attach to that statement; the proof sketch (§3) follows it.
A bare label ("Unfolding lemma", "Helper for X") is not a statement. Instances are exempt,
as are vendored files (which follow upstream style). `private` declarations should carry
docstrings too, but at reviewer discretion rather than as a hard requirement. The blueprint
remains the cross-referenced informal layer for dependency structure (see **Blueprint**);
the docstring statement is what external audits compare blind restatements against, so it
is part of the trusted surface.

**Blueprint.** When an ingested reference exists under `blueprint/src/references/`, blueprint
entries use `\statementsource{<ref>}{<anchor>}` and `\proofsource{<ref>}{<anchor>}` to cite
it, subject to the existing rule that these are written only after an approved proofmatch
run. When starting a new chapter or paper, ingest it as a reference pair
(`<name>.raw.md` + `<name>.md`) so these citations are possible.

**Vendored code.** Lean code adapted from another project keeps the original copyright
header and license notice, and its file docstring names the source project, the commit it
was taken from, and a summary of local modifications.

**Design adaptation.** When a construction, proof architecture, or module design is
adapted from — or materially inspired by — another project's code, the debt is cited even
when no code is transcribed. The module docstring's `## References` section names the
source project, author, module or archive entry, the commit or version consulted, and its
license, with a short tag usable at declaration level; the precedent is
`TuringMachine/Composition.lean`'s `[Balbach22]` for the Isabelle AFP `Cook_Levin`
composition-combinator architecture. Design documents and blueprint entries built on the
adapted design carry the same citation. Examining external code purely for comparison,
with nothing taken, creates no citation duty, but on a campaign it belongs in the
campaign's records (plan decision log or backlog) so the provenance question is answerable
later. (Maintainer guideline, binding, 2026-10-06.)

## 3. Proof sketches

Every nontrivial formal proof is accompanied by a human-readable English proof sketch, kept
next to the Lean it describes.

**What counts as nontrivial.** Rule of thumb: any proof longer than ~20 lines of tactics, or
that would rate difficulty ≥ 3 on the blueprint scale. One-line `simp`/`omega`/`exact`
proofs need no sketch.

**Where sketches live.** In the Lean file itself:

- For most theorems: a `**Proof sketch.**` paragraph at the end of the theorem's docstring,
  written in mathematical English (not Lean identifiers), naming the key intermediate steps.
- For long proofs: additionally, short comments at the major `have`/section boundaries tying
  the tactics back to the sketch's steps.

The named intermediate steps of a sketch should be visible in the formalization as `have`s
or standalone lemmas — if the sketch says "first reduce to the one-tape case", there should
be a lemma that is that reduction.

**Where sketches do not live.** Not in the blueprint. Blueprint statement entries state
claims only; `scripts/dataset_hygiene.py --strict` hard-fails on proof content there. The
blueprint records *what* is true and its dependency structure; the Lean docstrings record
*why* it is true.

**Sketches and the sorry ladder.** When landing a sorry-skeleton, write the sketch at
skeleton time — the sketch *is* the plan, and each `sorry` should correspond to a named step
of it. A skeleton whose sketch cannot be written is not ready to land.

**Synchronization.** When a proof strategy changes, the sketch changes in the same commit.
A sketch that describes a proof the code no longer performs is worse than no sketch.

## Review checklist

Before merging new Lean content, check:

1. Files follow the Area/Topic layout with a facade, and `TCSlib.lean` exports are updated.
2. Imports are precise; no bare `import Mathlib`.
3. Every file has a `## References` section; every source-derived declaration has a
   `[Tag, location]` in its docstring; deviations from sources are noted.
4. Every nontrivial proof (or sorry-stub standing in for one) has a proof sketch.
5. Every public declaration (instances and vendored files excepted) has a docstring
   opening with a natural-language statement of what it asserts
   (`python3 scripts/style_lint.py` checks presence mechanically; statement quality is
   review judgment).
6. `zsh scripts/lean_check.sh <file>` reports zero errors for each touched file.
7. If blueprint content was touched: `python3 scripts/blueprint_validate.py --strict` and
   `python3 scripts/dataset_hygiene.py --strict` pass.

```


## ===== workflow.md =====

```
# TCSlib Formalization Workflow

How large formalization campaigns are run in this repository. [`policy.md`](policy.md)
says what landed Lean code must look like; this document says what *process* produces
it. The reference implementation is the Arora-Barak campaign
(`AroraBarakChapter1Plan.md`, complete and audited end to end;
`AroraBarakChapter2Plan.md`, in progress) — file paths below cite its artifacts as
worked examples. Where an older document describes a mechanism this one supersedes
(e.g. the PR-based fill delivery in `AroraBarakChapter1Plan.md` §5, since replaced by
zip delivery), this document records current practice.

```
plan  →  statement phases  →  audit gates  →  fill campaign  →  closure
          (sorry-skeletons)    (per phase)     (epochs/batches)   (attestation, final
                                                                   audit, blueprint)
```

The load-bearing idea: **statements are audited before proofs are attempted.** Lean
already checks proofs; the dominant failure mode of formalization is a wrong or
subtly-weakened *statement*, and that is cheapest to catch while everything is still a
`sorry`. Every phase therefore lands as a compiling skeleton, passes an adversarial
external audit gate, and only then becomes fill work.

## 1. The campaign plan

Each campaign (typically one textbook chapter) begins with a plan file at the repo
root — `<Source>Chapter<N>Plan.md` — containing:

* **Scope**: which results are mandatory core, which are deferred, with source
  citations.
* **Foundation decisions**: the definitional conventions, each with its rationale
  (these are where audits bite; see §3).
* **Architecture and module layout**: directories, namespaces, facades, per policy §1.
* **Phasing**: the statement phases and the anticipated fill epochs.
* **Risks and honest effort assessment**.
* **Open design questions (human review required)**: decisions reserved for a human
  maintainer. Audit rounds *verify* these but never *dispose* of them; each records
  the maintainer's provisional choice and stays open until a human closes it. The
  consolidated register — full statements, cross-links, and status — is
  [`backlog.md`](backlog.md); the plans keep stable numbered stubs, which is what
  audit documents cite.
* **Decision log**: an append-only table. Every methodological decision, every audit
  round's verdict, and every repair round gets a row. The log is the campaign's
  memory; when a decision is reversed, the old row is marked **Superseded** in place,
  never deleted.

## 2. Statement phases (sorry-skeletons)

A phase lands the definitions plus the theorem *statements* of one coherent slice,
every proof a `sorry` under a policy-grade proof sketch (policy §3: the sketch is
written at skeleton time and is the plan; a skeleton whose sketch cannot be written is
not ready to land). Ground rules:

* Definitions and sorried statements only. Proofs appear in a skeleton only for
  definitional-unfolding lemmas whose home module mirrors proved infrastructure (the
  precedent: the `runWith` algebra of `TuringMachine/Nondeterministic.lean`, mirroring
  the vendored `runFrom` lemmas), and any such deviation is flagged in the audit pack
  with the proofs declared part of the audited surface.
* Sketches name their obligations: a sketch that will need a machine construction
  names each sub-machine as an explicit fill obligation, so the eventual brief can
  inherit the list.
* Everything gate-verifies before commit: per-module checks plus a full fresh sweep
  (§6), style lint, and the headline axiom prints.

## 3. Audit gates (between phases)

Right after a skeleton lands — statements frozen — an **external adversarial audit**
runs before any fill or any next phase. The auditor is an LLM from a different vendor,
in a fresh context, reviewing the trusted surface (definitions, statements, sketches,
and any skeleton-time proofs) against the source text.

**Artifacts**, all committed under `audits/` with campaign-scoped names
(`ch2-phase1-*`, `epoch4-*`):

* `…-pack.md` — the auditor's instructions: the audited commit, repository-side
  attestations (freeze by path enumeration, sweep results, admission inventory, axiom
  prints, lint — stated so the auditor can verify or challenge them, with source facts
  kept separate from maintainer execution claims), the under-audit inventory, a
  prioritized brief (the plan's seeded design questions go here), and the findings
  table format with the severity guide: **blocker** (a downstream phase would build on
  a wrong statement) / **major** (fixable but materially misleading) / **minor** /
  **note**. `audits/TEMPLATE.md` is the skeleton.
* `…-bundle.md` — a single uploadable file: the pack verbatim, then every attachment
  under a `## ===== <path> =====` header (prior findings, both plans, `policy.md`,
  the root, and the full module tree).
* A short kickoff message (drafted per round, pasted by the maintainer into a fresh
  auditor chat with the bundle attached).
* `…-findings.md` — the auditor's report, preserved **verbatim**, including anything
  the maintainer disputes. Pack errata found later are acknowledged in the resolutions
  file; shipped packs are never edited retroactively.

**The gate rule**: a gate closes only on a round reporting **zero blockers and zero
majors**. A round with majors triggers repairs and a full re-audit round (minors may
be swept in the closing commit and re-verified). Repairs adopt the auditor's own
constructions where supplied, are re-gated, and are recorded in the decision log; when
the loop closes, `…-resolutions.md` summarizes every round, every repair, and the note
dispositions. The complete worked example is the three-round
`audits/ch2-phase1-{pack,findings,reaudit-…,round3-…,resolutions}.md` loop.

Audits complement, never replace, in-Lean sanity theorems — the machine-checked and
permanent form of the same checks.

## 4. The fill campaign (epochs and batches)

With all phase gates closed, the audited-true sorries are filled in **epochs** —
sequential, ordered by risk retirement, with an audit round at each epoch boundary —
each consisting of **batches** run in parallel by cloud agents with disjoint file
ownership, from self-contained briefs in `briefs/`.

**Binding batch ground rules** (full text repeated in every brief):

1. **Exclusive file ownership.** Helpers live `private` in owned files; a lemma that
   belongs in a shared file is *requested* in the report and added serially at epoch
   merge, flagged for the next audit.
2. **Statement freeze.** Audited declarations are never renamed, re-signatured, or
   re-stated by fill work. A target that looks unprovable as stated is an
   *escalation*, reported with the obstruction — never "fixed" inline.
3. **Verification per batch**: the check script (§6) over the owned files, zero
   `error:` lines, sorries only at documented out-of-scope items.

**Delivery is by zip, not PR.** Each batch returns an archive containing `REPORT.md`,
the full source files, a `git format-patch` series, a git bundle, the batch's sweep
log, the axiom-print log, and `SHA256SUMS`. The maintainer verifies before
integrating: checksums; the statement freeze (comment-stripped comparison of every
audited signature); enumeration of any removals; public-declaration drift; a full
fresh sweep; the headline axiom prints. Integration is `git am -3` from the patch
series, preserving the agent's authorship. Large fills that exhaust one agent's budget
continue via a continuation brief to a fresh agent (the `universal` B2 precedent).

**Epoch boundaries**: the maintainer re-runs the full sweep, produces a **drift
attestation** (§6), and prepares the epoch's audit pack with elaboration evidence;
the epoch's gate follows the same zero-blockers/majors rule as phase gates.

## 5. Closure

When the last sorry falls: a zero-sorry sweep with build evidence; a campaign-wide
drift attestation against the audited baselines; a final audit pack covering the fill
rounds; and the blueprint increment — dependency graph from `.ilean` artifacts,
`scripts/blueprint_{enumerate,assemble,validate}.py`, blueprint-writer agents, with
the blueprint **late-bound** throughout (extraction only at boundaries; no blueprint
LaTeX hand-written ahead of the Lean; `blueprint/BLUEPRINT_PIPELINE.md` has the
pipeline detail).

## 6. Verification tooling

* **`scripts/lean_check_tree.sh <module>`** — the campaign's elaboration gate: a
  direct `lean` invocation per module (**`lake build` is banned on campaign
  branches** — see the Chapter-1 decision log), emitting fresh `.olean`s into a
  scratch tree. Pass requires exit 0, zero `error:` lines, *and* a fresh olean, so a
  stale artifact can never satisfy the check. The full sweep runs it over every
  module, in dependency order, from `scripts/ab_ch1_module_order.txt`:

  ```
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < scripts/ab_ch1_module_order.txt )
  ```

  Admission counting is by `declaration uses 'sorry'` warnings in the sweep log; the
  expected count is attested in every pack.
* **`scripts/campaign_style_lint.py`** (named `scripts/style_lint.py` until the
  main merge, which adopted main's per-file policy linter under that name — the
  historical audit logs' invocations refer to this tool) — mechanical policy checks: statement-prose docstrings,
  sketch-before-sorry, file sizes, `## References`, facade coverage. Campaign
  baseline: zero FAIL (legacy pre-campaign files outside the audited surface are
  tolerated and listed).
* **Axiom prints** — `#print axioms` for every headline theorem on the *fresh* olean
  tree: closed results must show exactly `[propext, Classical.choice, Quot.sound]`;
  sorried statements show `sorryAx`, and any other axiom is a stop-the-line event.
* **Drift attestation** — the anti-tamper check between audited baselines: strip
  comments from every module, compare both the **multiset** of declarations and the
  **ordered declaration sequence** against the baseline, and enumerate public
  declarations (gained / lost / changed) so that "nothing audited moved" is a checked
  claim, not an impression.
* **Vendored files** are frozen at their recorded upstream pin and periodically
  byte-compared against upstream; local modifications live only in the header list.

## 7. Relationship to the other documents

* [`policy.md`](policy.md) — the standards this workflow enforces (modularity,
  attribution, sketches, review checklist).
* [`lean-glossary.md`](lean-glossary.md) — the Lean/Mathlib jargon appearing in
  declaration names and docstrings (fuel, Sigma, `Prop` vs `Bool`, the naming
  grammar, …), for readers fluent in TCS but not in Lean.
* [`AGENTS.md`](AGENTS.md) / `.claude/` — the sorry-ladder proof technique and agent
  roster; useful *inside* a fill batch, but campaign verification runs through §6, not
  through `lake build` or editor-only checks.
* [`blueprint/BLUEPRINT_PIPELINE.md`](blueprint/BLUEPRINT_PIPELINE.md) — blueprint
  generation and validation.
* [`.github/copilot-instructions.md`](.github/copilot-instructions.md) — main-branch
  build and CI; campaign branches deviate as recorded in their decision logs.

```


## ===== scripts/ab_ch34_received_order.txt =====

```
TCSlib/Complexity/TuringMachine/UnaryTape
TCSlib/Complexity/TuringMachine/CounterProg
TCSlib/Complexity/TuringMachine/CounterProgRun
TCSlib/Complexity/ClassNP/CounterProgPolyTime
TCSlib/Complexity/ClassNP/ExpPoly
TCSlib/Complexity/ClassNP/PolyTimePairing
TCSlib/Complexity/ClassNP/PClosure
TCSlib/Complexity/ClassNP/Transducer
TCSlib/Complexity/SpaceComplexity/Basic
TCSlib/Complexity/SpaceComplexity/ConfigCount
TCSlib/Complexity/SpaceComplexity/Machines/Layout
TCSlib/Complexity/SpaceComplexity/Machines/Program
TCSlib/Complexity/SpaceComplexity/Machines/Sim
TCSlib/Complexity/SpaceComplexity/Machines/CallReturn
TCSlib/Complexity/SpaceComplexity/Machines/Call
TCSlib/Complexity/SpaceComplexity/Machines/Compile
TCSlib/Complexity/SpaceComplexity/Machines/CleanSweep
TCSlib/Complexity/SpaceComplexity/Machines/Clean
TCSlib/Complexity/SpaceComplexity/Machines/Bank
TCSlib/Complexity/SpaceComplexity/Machines/Bin
TCSlib/Complexity/SpaceComplexity/Machines/Lib
TCSlib/Complexity/SpaceComplexity/Machines/FragDec
TCSlib/Complexity/SpaceComplexity/Machines/Frag
TCSlib/Complexity/SpaceComplexity/Machines/ParsePlain
TCSlib/Complexity/SpaceComplexity/Machines/Parse
TCSlib/Complexity/SpaceComplexity/Machines/Parse2
TCSlib/Complexity/SpaceComplexity/Machines/ParseCmp
TCSlib/Complexity/SpaceComplexity/Machines/ARM
TCSlib/Complexity/SpaceComplexity/Machines/ARMSim
TCSlib/Complexity/SpaceComplexity/Machines/ARMRun
TCSlib/Complexity/SpaceComplexity/Machines/ARMProof
TCSlib/Complexity/SpaceComplexity/ImplicitPoly
TCSlib/Complexity/SpaceComplexity/Machines/ARMKit
TCSlib/Complexity/SpaceComplexity/Machines/DblLang
TCSlib/Complexity/SpaceComplexity/UnaryLogspace
TCSlib/Complexity/SpaceComplexity/CounterProgSim
TCSlib/Complexity/SpaceComplexity/CounterProgSimRun
TCSlib/Complexity/SpaceComplexity
TCSlib/Complexity/TimeHierarchy/ClockMachine
TCSlib/Complexity/TimeHierarchy/ClockLoop
TCSlib/Complexity/TimeHierarchy/CodePrefix
TCSlib/Complexity/TimeHierarchy/Diagonal
TCSlib/Complexity/TimeHierarchy/Separation
TCSlib/Complexity/TimeHierarchy

```


## ===== audits/logs/ch34-p0-sweep.log =====

```
== TCSlib/Complexity/TuringMachine/UnaryTape  13:09:53
== TCSlib/Complexity/TuringMachine/Configuration  13:09:54
TCSlib/Complexity/TuringMachine/Configuration.lean:137:17: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Configuration.lean:140:61: warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
TCSlib/Complexity/TuringMachine/Configuration.lean:155:17: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
== TCSlib/Complexity/TuringMachine/Deterministic  13:09:55
== TCSlib/Complexity/TuringMachine/Finite  13:09:56
== TCSlib/Complexity/TuringMachine/Simulation  13:09:57
== TCSlib/Complexity/TuringMachine/CounterProg  13:09:59
== TCSlib/Complexity/TuringMachine/CounterProgRun  13:10:02
== TCSlib/Complexity/TuringMachine/Composition  13:10:03
== TCSlib/Complexity/ClassNP/PolyTime  13:10:05
== TCSlib/Complexity/ClassNP/CounterProgPolyTime  13:10:06
== TCSlib/Complexity/TuringMachine/StateRenaming  13:10:07
== TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction  13:10:08
== TCSlib/Complexity/TuringMachine/Sweep  13:10:09
== TCSlib/Complexity/TuringMachine/Robustness/SingleTape  13:10:11
== TCSlib/Complexity/TuringMachine/Encoding  13:10:13
== TCSlib/Complexity/ClassP/TimeConstructible  13:10:14
== TCSlib/Complexity/TuringMachine/Build/Convention  13:10:16
== TCSlib/Complexity/TuringMachine/Build/Wrappers  13:10:17
== TCSlib/Complexity/TuringMachine/Build/Loop  13:10:19
TCSlib/Complexity/TuringMachine/Build/Loop.lean:2932:8: warning: This simp argument is unused:
  Fin.val_zero

Hint: Omit it from the simp argument list.
  simp only [emCallClearCfg, MultiTapeTM.step, emCallClearTM, Cfg.workTapeSymbols, F̵i̵n̵.̵v̵a̵l̵_̵z̵e̵r̵o̵,̵ ̵Fin.val_one,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲Nat.one_ne_zero, ↓reduceIte, hmark, reduceCtorEq, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:2932:22: warning: This simp argument is unused:
  Fin.val_one

Hint: Omit it from the simp argument list.
  simp only [emCallClearCfg, MultiTapeTM.step, emCallClearTM, Cfg.workTapeSymbols, Fin.val_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲F̵i̵n̵.̵v̵a̵l̵_̵o̵n̵e̵,̵ ̵Nat.one_ne_zero, ↓reduceIte, hmark, reduceCtorEq, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:2932:35: warning: This simp argument is unused:
  Nat.one_ne_zero

Hint: Omit it from the simp argument list.
  simp only [emCallClearCfg, MultiTapeTM.step, emCallClearTM, Cfg.workTapeSymbols, Fin.val_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲Fin.val_one, N̵a̵t̵.̵o̵n̵e̵_̵n̵e̵_̵z̵e̵r̵o̵,̵ ̵↓reduceIte, hmark, reduceCtorEq, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:2974:27: warning: This simp argument is unused:
  Fin.val_zero

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emCallClearCfg, emCallClearTM, Cfg.workTapeSymbols, F̵i̵n̵.̵v̵a̵l̵_̵z̵e̵r̵o̵,̵ ̵Fin.val_one,
  ̲  ̲ ̲ ̲ ̲ ̲Nat.one_ne_zero, ↓reduceIte, hmark, reduceCtorEq, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:2974:41: warning: This simp argument is unused:
  Fin.val_one

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emCallClearCfg, emCallClearTM,
  ̵  ̵ ̵ ̵ ̵ ̵Cfg.workTapeSymbols, Fin.val_zero,
  ̲ F̵i̵n̵.̵v̵a̵l̵_̵o̵n̵e̵,̵  ̲ ̲ ̲ ̲Nat.one_ne_zero, ↓reduceIte, hmark,
  ̵  ̵ ̵ ̵ ̵ ̵reduceCtorEq, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:2974:54: warning: This simp argument is unused:
  Nat.one_ne_zero

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emCallClearCfg, emCallClearTM, Cfg.workTapeSymbols, Fin.val_zero,
  ̲  ̲ ̲ ̲ ̲ ̲Fin.val_one, N̵a̵t̵.̵o̵n̵e̵_̵n̵e̵_̵z̵e̵r̵o̵,̵ ̵↓reduceIte, hmark, reduceCtorEq, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3021:8: warning: This simp argument is unused:
  Fin.val_zero

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emCallClearCfg, emCallClearTM, Cfg.workTapeSymbols, F̵i̵n̵.̵v̵a̵l̵_̵z̵e̵r̵o̵,̵ ̵Fin.val_one,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲Nat.one_ne_zero, ↓reduceIte, hblank, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3021:22: warning: This simp argument is unused:
  Fin.val_one

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emCallClearCfg, emCallClearTM, Cfg.workTapeSymbols, Fin.val_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲F̵i̵n̵.̵v̵a̵l̵_̵o̵n̵e̵,̵ ̵Nat.one_ne_zero, ↓reduceIte, hblank, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3021:35: warning: This simp argument is unused:
  Nat.one_ne_zero

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emCallClearCfg, emCallClearTM, Cfg.workTapeSymbols, Fin.val_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲Fin.val_one, N̵a̵t̵.̵o̵n̵e̵_̵n̵e̵_̵z̵e̵r̵o̵,̵ ̵↓reduceIte, hblank, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3053:6: warning: This simp argument is unused:
  Fin.val_zero

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emCallClearCfg, emCallClearTM, Cfg.workTapeSymbols, F̵i̵n̵.̵v̵a̵l̵_̵z̵e̵r̵o̵,̵ ̵Fin.val_one,
  ̲  ̲ ̲ ̲ ̲ ̲Nat.one_ne_zero, ↓reduceIte, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3053:20: warning: This simp argument is unused:
  Fin.val_one

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emCallClearCfg, emCallClearTM, Cfg.workTapeSymbols, Fin.val_zero,
  ̲  ̲ ̲ ̲ ̲ ̲F̵i̵n̵.̵v̵a̵l̵_̵o̵n̵e̵,̵ ̵Nat.one_ne_zero, ↓reduceIte, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3053:33: warning: This simp argument is unused:
  Nat.one_ne_zero

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emCallClearCfg, emCallClearTM, Cfg.workTapeSymbols, Fin.val_zero,
  ̲  ̲ ̲ ̲ ̲ ̲Fin.val_one, N̵a̵t̵.̵o̵n̵e̵_̵n̵e̵_̵z̵e̵r̵o̵,̵ ̵↓reduceIte, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3082:22: warning: This simp argument is unused:
  min_le_right

Hint: Omit it from the simp argument list.
  simp [emCallSpan, m̵i̵n̵_̵l̵e̵_̵r̵i̵g̵h̵t̵,̵ ̵le_max_right]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3082:36: warning: This simp argument is unused:
  le_max_right

Hint: Omit it from the simp argument list.
  simp [emCallSpan, min_le_right,̵ ̵l̵e̵_̵m̵a̵x̵_̵r̵i̵g̵h̵t̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3270:24: warning: This simp argument is unused:
  hspan

Hint: Omit it from the simp argument list.
  simp [emCallSpan, h̵s̵p̵a̵n̵,̵ ̵bufferTape, hn, List.getElem?_eq_none hlen]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3271:24: warning: This simp argument is unused:
  hspan

Hint: Omit it from the simp argument list.
  simp [emCallSpan, h̵s̵p̵a̵n̵,̵ ̵bufferTape, hn]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3579:27: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3579:27: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3832:19: warning: This simp argument is unused:
  show (1 : Fin 2) ≠ 0 by decide

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emCallFinishCfg, emCallFinishTM, Cfg.workTapeSymbols, Fin.isValue,
  ̲  ̲ ̲ ̲ ̲ ̲s̵h̵o̵w̵ ̵(̵1̵ ̵:̵ ̵F̵i̵n̵ ̵2̵)̵ ̵≠̵ ̵0̵ ̵b̵y̵ ̵d̵e̵c̵i̵d̵e̵,̵ ̵↓reduceIte, hblank]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3834:50: warning: This simp argument is unused:
  emCallFinishCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, e̵m̵C̵a̵l̵l̵F̵i̵n̵i̵s̵h̵C̵f̵g̵,̵ ̵sub_eq_add_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3849:21: warning: This simp argument is unused:
  show (1 : Fin 2) ≠ 0 by decide

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emCallFinishCfg, emCallFinishTM, Cfg.workTapeSymbols,
          Fin.isValue, s̵h̵o̵w̵ ̵(̵1̵ ̵:̵ ̵F̵i̵n̵ ̵2̵)̵ ̵≠̵ ̵0̵ ̵b̵y̵ ̵d̵e̵c̵i̵d̵e̵,̵ ̵↓reduceIte, hread]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3852:30: warning: This simp argument is unused:
  emCallFinishCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, emCallF̵i̵n̵i̵s̵h̵C̵f̵g̵,̵ ̵e̵m̵C̵a̵l̵l̵_erase_last]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3853:54: warning: This simp argument is unused:
  emCallFinishCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, e̵m̵C̵a̵l̵l̵F̵i̵n̵i̵s̵h̵C̵f̵g̵,̵ ̵sub_eq_add_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3881:50: warning: This simp argument is unused:
  emCallFinishCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, e̵m̵C̵a̵l̵l̵F̵i̵n̵i̵s̵h̵C̵f̵g̵,̵ ̵sub_eq_add_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3881:67: warning: This simp argument is unused:
  sub_eq_add_neg

Hint: Omit it from the simp argument list.
  simp [Action.apply, emCallFinishCfg,̵ ̵s̵u̵b̵_̵e̵q̵_̵a̵d̵d̵_̵n̵e̵g̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3892:52: warning: This simp argument is unused:
  emCallFinishCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, e̵m̵C̵a̵l̵l̵F̵i̵n̵i̵s̵h̵C̵f̵g̵,̵ ̵sub_eq_add_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3925:26: warning: This simp argument is unused:
  emCallFinishCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, e̵m̵C̵a̵l̵l̵F̵i̵n̵i̵s̵h̵C̵f̵g̵,̵ ̵sub_eq_add_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3941:30: warning: This simp argument is unused:
  emCallFinishCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, e̵m̵C̵a̵l̵l̵F̵i̵n̵i̵s̵h̵C̵f̵g̵,̵ ̵bufferTape_append]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3943:30: warning: This simp argument is unused:
  emCallFinishCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, e̵m̵C̵a̵l̵l̵F̵i̵n̵i̵s̵h̵C̵f̵g̵,̵ ̵sub_eq_add_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3943:47: warning: This simp argument is unused:
  sub_eq_add_neg

Hint: Omit it from the simp argument list.
  simp [Action.apply, emCallFinishCfg,̵ ̵s̵u̵b̵_̵e̵q̵_̵a̵d̵d̵_̵n̵e̵g̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3944:43: warning: This simp argument is unused:
  emCallFinishCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, e̵m̵C̵a̵l̵l̵F̵i̵n̵i̵s̵h̵C̵f̵g̵,̵ ̵sub_eq_add_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3944:60: warning: This simp argument is unused:
  sub_eq_add_neg

Hint: Omit it from the simp argument list.
  simp [Action.apply, emCallFinishCfg,̵ ̵s̵u̵b̵_̵e̵q̵_̵a̵d̵d̵_̵n̵e̵g̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3968:65: warning: This simp argument is unused:
  emCallFinishCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, e̵m̵C̵a̵l̵l̵F̵i̵n̵i̵s̵h̵C̵f̵g̵,̵ ̵sub_eq_add_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3968:82: warning: This simp argument is unused:
  sub_eq_add_neg

Hint: Omit it from the simp argument list.
  simp [Action.apply, emCallFinishCfg,̵ ̵s̵u̵b̵_̵e̵q̵_̵a̵d̵d̵_̵n̵e̵g̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3979:54: warning: This simp argument is unused:
  emCallFinishCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, emCallF̵i̵n̵i̵s̵h̵C̵f̵g̵,̵ ̵e̵m̵C̵a̵l̵l̵_erase_last]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3981:30: warning: This simp argument is unused:
  emCallFinishCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, e̵m̵C̵a̵l̵l̵F̵i̵n̵i̵s̵h̵C̵f̵g̵,̵ ̵sub_eq_add_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4040:21: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4040:33: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4077:2: warning: 'all_goals
  repeat
    first
    | rfl
    | omega
    | split' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4077:12: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4168:47: warning: This simp argument is unused:
  Fin.addCases_right

Hint: Omit it from the simp argument list.
  simp only [emCallSlots, Fin.addCases_left,̵ ̵F̵i̵n̵.̵a̵d̵d̵C̵a̵s̵e̵s̵_̵r̵i̵g̵h̵t̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4182:28: warning: This simp argument is unused:
  Fin.addCases_left

Hint: Omit it from the simp argument list.
  simp only [emCallSlots, Fin.addCases_l̵e̵f̵t̵,̵ ̵F̵i̵n̵.̵a̵d̵d̵C̵a̵s̵e̵s̵_̵right]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4189:67: warning: This simp argument is unused:
  emCallSlots

Hint: Omit it from the simp argument list.
  simp [emCallLayout, emCallPairIndex, tapeBlocks, e̵m̵C̵a̵l̵l̵S̵l̵o̵t̵s̵,̵
  ̵ ̵ ̵ ̵ ̵Fin.addCases, bufferedCompTM,
  ̲  ̲ ̲ ̲emCallIdleTM, emCallRightTM, emCallTrackTM]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4199:2: warning: 'all_goals
  repeat
    first
    | rfl
    | omega
    | split' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4200:2: warning: 'all_goals
  repeat
    first
    | rfl
    | omega
    | split' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4199:12: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4200:12: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4213:4: warning: 'all_goals
  repeat
    first
    | rfl
    | omega
    | split' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4214:4: warning: 'all_goals
  repeat
    first
    | rfl
    | omega
    | split' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4213:14: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4214:14: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4489:32: warning: This simp argument is unused:
  emCall_pair_inverse

Hint: Omit it from the simp argument list.
  simp [emCallCfg, e̵m̵C̵a̵l̵l̵_̵p̵a̵i̵r̵_̵i̵n̵v̵e̵r̵s̵e̵,̵ ̵emCallFinishCfg, Cfg.ofWords, stateWord, emCallPairIndex,
  ̲  ̲ ̲ ̲ ̲ ̲emCallPairSelect]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4491:32: warning: This simp argument is unused:
  emCall_pair_inverse

Hint: Omit it from the simp argument list.
  simp [emCallCfg, e̵m̵C̵a̵l̵l̵_̵p̵a̵i̵r̵_̵i̵n̵v̵e̵r̵s̵e̵,̵ ̵emCallFinishCfg, Cfg.ofWords, stateWord, emCallPairIndex,
  ̲  ̲ ̲ ̲ ̲ ̲emCallPairSelect, bufferedCompTM, emCallIdleTM, emCallRightTM, emCallTrackTM]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4622:37: warning: This simp argument is unused:
  hi

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, hs, hi̵,̵ ̵h̵w]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4622:41: warning: This simp argument is unused:
  hw

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, hs, hi,̵ ̵h̵w̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:5466:33: warning: This simp argument is unused:
  Function.comp_def

Hint: Omit it from the simp argument list.
  simp [List.append_assoc,̵ ̵F̵u̵n̵c̵t̵i̵o̵n̵.̵c̵o̵m̵p̵_̵d̵e̵f̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
== TCSlib/Complexity/TuringMachine/Build/Primitives  13:10:32
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2492:42: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2498:72: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2492:42: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2498:72: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2490:82: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2520:72: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2520:72: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2508:38: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2512:38: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2570:29: warning: This simp argument is unused:
  List.append_nil

Hint: Omit it from the simp argument list.
  simp only [↓reduceIte,̵ ̵L̵i̵s̵t̵.̵a̵p̵p̵e̵n̵d̵_̵n̵i̵l̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2533:42: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2538:42: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2541:42: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2580:46: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2604:43: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2927:25: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2927:25: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3026:59: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3174:34: warning: This simp argument is unused:
  splitRestoreScan

Hint: Omit it from the simp argument list.
  simp [Action.apply,̵ ̵s̵p̵l̵i̵t̵R̵e̵s̵t̵o̵r̵e̵S̵c̵a̵n̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3204:79: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3204:79: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3267:6: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3312:52: warning: This simp argument is unused:
  Nat.cast_one

Hint: Omit it from the simp argument list.
  simp only [List.length_nil, Nat.zero_add, N̵a̵t̵.̵c̵a̵s̵t̵_̵o̵n̵e̵,̵ ̵Fin.ext_iff, Fin.val_one] at h₁

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3312:66: warning: This simp argument is unused:
  Fin.ext_iff

Hint: Omit it from the simp argument list.
  simp only [List.length_nil, Nat.zero_add, Nat.cast_one, Fin.e̵x̵t̵_̵i̵f̵f̵,̵ ̵F̵i̵n̵.̵val_one] at h₁

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3312:79: warning: This simp argument is unused:
  Fin.val_one

Hint: Omit it from the simp argument list.
  simp only [List.length_nil, Nat.zero_add, Nat.cast_one, Fin.ext_iff,̵ ̵F̵i̵n̵.̵v̵a̵l̵_̵o̵n̵e̵] at h₁

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3352:20: warning: This simp argument is unused:
  MultiTapeTM.step

Hint: Omit it from the simp argument list.
  simp [M̵u̵l̵t̵i̵T̵a̵p̵e̵T̵M̵.̵s̵t̵e̵p̵,̵ ̵catalogPolyUnaryTM, Action.apply, catalogPolyCfg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3352:38: warning: This simp argument is unused:
  catalogPolyUnaryTM

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.step, c̵a̵t̵a̵l̵o̵g̵P̵o̵l̵y̵U̵n̵a̵r̵y̵T̵M̵,̵ ̵Action.apply, catalogPolyCfg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3352:72: warning: This simp argument is unused:
  catalogPolyCfg

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.step, catalogPolyUnaryTM, Action.apply,̵ ̵c̵a̵t̵a̵l̵o̵g̵P̵o̵l̵y̵C̵f̵g̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3353:10: warning: This simp argument is unused:
  MultiTapeTM.step

Hint: Omit it from the simp argument list.
  simp [M̵u̵l̵t̵i̵T̵a̵p̵e̵T̵M̵.̵s̵t̵e̵p̵,̵ ̵catalogPolyUnaryTM, Action.apply, catalogPolyCfg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3353:28: warning: This simp argument is unused:
  catalogPolyUnaryTM

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.step, c̵a̵t̵a̵l̵o̵g̵P̵o̵l̵y̵U̵n̵a̵r̵y̵T̵M̵,̵ ̵Action.apply, catalogPolyCfg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3353:62: warning: This simp argument is unused:
  catalogPolyCfg

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.step, catalogPolyUnaryTM, Action.apply,̵ ̵c̵a̵t̵a̵l̵o̵g̵P̵o̵l̵y̵C̵f̵g̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3400:23: warning: This simp argument is unused:
  Prod.mk.injEq

Hint: Omit it from the simp argument list.
  simp only [ht0, MultiTapeTM.runFrom_zero, splitRestoreScan, Cfg.ofWords,
      Option.some.injEq,̵ ̵P̵r̵o̵d̵.̵m̵k̵.̵i̵n̵j̵E̵q̵] at hstate

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:4917:8: warning: This simp argument is unused:
  Fin.val_zero

Hint: Omit it from the simp argument list.
  simp only [emitterClearCfg, MultiTapeTM.step, emitterClearTM, Cfg.workTapeSymbols,
          Fin.val_z̵e̵r̵o,̵ ̵F̵i̵n.̵v̵a̵l̵_̵o̵n̵e, Nat.one_ne_zero, ↓reduceIte, hmark, reduceCtorEq, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:4917:22: warning: This simp argument is unused:
  Fin.val_one

Hint: Omit it from the simp argument list.
  simp only [emitterClearCfg, MultiTapeTM.step, emitterClearTM, Cfg.workTapeSymbols,
          Fin.val_zero, F̵i̵n̵.̵v̵a̵l̵_̵o̵n̵e̵,̵ ̵Nat.one_ne_zero, ↓reduceIte, hmark, reduceCtorEq, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:4917:35: warning: This simp argument is unused:
  Nat.one_ne_zero

Hint: Omit it from the simp argument list.
  simp only [emitterClearCfg, MultiTapeTM.step, emitterClearTM, Cfg.workTapeSymbols,
          Fin.val_zero, Fin.val_one, N̵a̵t̵.̵o̵n̵e̵_̵n̵e̵_̵z̵e̵r̵o̵,̵ ̵↓reduceIte, hmark, reduceCtorEq, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:4959:27: warning: This simp argument is unused:
  Fin.val_zero

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emitterClearCfg, emitterClearTM, Cfg.workTapeSymbols, F̵i̵n̵.̵v̵a̵l̵_̵z̵e̵r̵o̵,̵ ̵Fin.val_one,
  ̲  ̲ ̲ ̲ ̲ ̲Nat.one_ne_zero, ↓reduceIte, hmark, reduceCtorEq, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:4959:41: warning: This simp argument is unused:
  Fin.val_one

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emitterClearCfg, emitterClearTM,
  ̵  ̵ ̵ ̵ ̵ ̵Cfg.workTapeSymbols, Fin.val_zero,
  ̲ F̵i̵n̵.̵v̵a̵l̵_̵o̵n̵e̵,̵  ̲ ̲ ̲ ̲Nat.one_ne_zero, ↓reduceIte, hmark,
  ̵  ̵ ̵ ̵ ̵ ̵reduceCtorEq, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:4959:54: warning: This simp argument is unused:
  Nat.one_ne_zero

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emitterClearCfg, emitterClearTM, Cfg.workTapeSymbols, Fin.val_zero,
  ̲  ̲ ̲ ̲ ̲ ̲Fin.val_one, N̵a̵t̵.̵o̵n̵e̵_̵n̵e̵_̵z̵e̵r̵o̵,̵ ̵↓reduceIte, hmark, reduceCtorEq, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5006:8: warning: This simp argument is unused:
  Fin.val_zero

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emitterClearCfg, emitterClearTM, Cfg.workTapeSymbols,
          Fin.val_z̵e̵r̵o,̵ ̵F̵i̵n.̵v̵a̵l̵_̵o̵n̵e, Nat.one_ne_zero, ↓reduceIte, hblank, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5006:22: warning: This simp argument is unused:
  Fin.val_one

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emitterClearCfg, emitterClearTM, Cfg.workTapeSymbols,
          Fin.val_zero, F̵i̵n̵.̵v̵a̵l̵_̵o̵n̵e̵,̵ ̵Nat.one_ne_zero, ↓reduceIte, hblank, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5006:35: warning: This simp argument is unused:
  Nat.one_ne_zero

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emitterClearCfg, emitterClearTM, Cfg.workTapeSymbols,
          Fin.val_zero, Fin.val_one, N̵a̵t̵.̵o̵n̵e̵_̵n̵e̵_̵z̵e̵r̵o̵,̵ ̵↓reduceIte, hblank, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5038:6: warning: This simp argument is unused:
  Fin.val_zero

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emitterClearCfg, emitterClearTM, Cfg.workTapeSymbols, F̵i̵n̵.̵v̵a̵l̵_̵z̵e̵r̵o̵,̵ ̵Fin.val_one,
  ̲  ̲ ̲ ̲ ̲ ̲Nat.one_ne_zero, ↓reduceIte, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5038:20: warning: This simp argument is unused:
  Fin.val_one

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emitterClearCfg, emitterClearTM, Cfg.workTapeSymbols, Fin.val_zero,
  ̲  ̲ ̲ ̲ ̲ ̲F̵i̵n̵.̵v̵a̵l̵_̵o̵n̵e̵,̵ ̵Nat.one_ne_zero, ↓reduceIte, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5038:33: warning: This simp argument is unused:
  Nat.one_ne_zero

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emitterClearCfg, emitterClearTM, Cfg.workTapeSymbols, Fin.val_zero,
  ̲  ̲ ̲ ̲ ̲ ̲Fin.val_one, N̵a̵t̵.̵o̵n̵e̵_̵n̵e̵_̵z̵e̵r̵o̵,̵ ̵↓reduceIte, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5067:23: warning: This simp argument is unused:
  min_le_right

Hint: Omit it from the simp argument list.
  simp [emitterSpan, m̵i̵n̵_̵l̵e̵_̵r̵i̵g̵h̵t̵,̵ ̵le_max_right]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5067:37: warning: This simp argument is unused:
  le_max_right

Hint: Omit it from the simp argument list.
  simp [emitterSpan, min_le_right,̵ ̵l̵e̵_̵m̵a̵x̵_̵r̵i̵g̵h̵t̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5255:25: warning: This simp argument is unused:
  hspan

Hint: Omit it from the simp argument list.
  simp [emitterSpan, h̵s̵p̵a̵n̵,̵ ̵bufferTape, hn, List.getElem?_eq_none hlen]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5256:25: warning: This simp argument is unused:
  hspan

Hint: Omit it from the simp argument list.
  simp [emitterSpan, h̵s̵p̵a̵n̵,̵ ̵bufferTape, hn]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5573:37: warning: This simp argument is unused:
  emitterBankCfg

Hint: Omit it from the simp argument list.
  simp [e̵m̵i̵t̵t̵e̵r̵B̵a̵n̵k̵C̵f̵g̵,̵ ̵MultiTapeTM.step, hs, controlAction, Action.apply]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5573:53: warning: This simp argument is unused:
  MultiTapeTM.step

Hint: Omit it from the simp argument list.
  simp [emitterBankCfg, M̵u̵l̵t̵i̵T̵a̵p̵e̵T̵M̵.̵s̵t̵e̵p̵,̵ ̵hs, controlAction, Action.apply]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5573:90: warning: This simp argument is unused:
  Action.apply

Hint: Omit it from the simp argument list.
  simp [emitterBankCfg, MultiTapeTM.step, hs, controlAction,̵ ̵A̵c̵t̵i̵o̵n̵.̵a̵p̵p̵l̵y̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5578:44: warning: This simp argument is unused:
  MultiTapeTM.step

Hint: Omit it from the simp argument list.
  simp [emitterBankCfg, emitterSlots, M̵u̵l̵t̵i̵T̵a̵p̵e̵T̵M̵.̵s̵t̵e̵p̵,̵ ̵hs, controlAction, Action.apply, -Fin.natAdd_eq_addNat]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5583:44: warning: This simp argument is unused:
  MultiTapeTM.step

Hint: Omit it from the simp argument list.
  simp [emitterBankCfg, emitterSlots, M̵u̵l̵t̵i̵T̵a̵p̵e̵T̵M̵.̵s̵t̵e̵p̵,̵ ̵hs, controlAction, Action.apply, -Fin.natAdd_eq_addNat]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5589:44: warning: This simp argument is unused:
  MultiTapeTM.step

Hint: Omit it from the simp argument list.
  simp [emitterBankCfg, emitterSlots, M̵u̵l̵t̵i̵T̵a̵p̵e̵T̵M̵.̵s̵t̵e̵p̵,̵ ̵hs, controlAction, Action.apply, -Fin.natAdd_eq_addNat]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5594:44: warning: This simp argument is unused:
  MultiTapeTM.step

Hint: Omit it from the simp argument list.
  simp [emitterBankCfg, emitterSlots, M̵u̵l̵t̵i̵T̵a̵p̵e̵T̵M̵.̵s̵t̵e̵p̵,̵ ̵hs, controlAction, Action.apply, -Fin.natAdd_eq_addNat]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5802:27: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5802:27: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:6228:52: warning: This simp argument is unused:
  emitterP2PrepareCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, e̵m̵i̵t̵t̵e̵r̵P̵2̵P̵r̵e̵p̵a̵r̵e̵C̵f̵g̵,̵ ̵hwrite]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:6229:52: warning: This simp argument is unused:
  emitterP2PrepareCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply,̵ ̵e̵m̵i̵t̵t̵e̵r̵P̵2̵P̵r̵e̵p̵a̵r̵e̵C̵f̵g̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:6264:37: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:6284:50: warning: This simp argument is unused:
  emitterP2PrepareCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply,̵ ̵e̵m̵i̵t̵t̵e̵r̵P̵2̵P̵r̵e̵p̵a̵r̵e̵C̵f̵g̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:6295:52: warning: This simp argument is unused:
  emitterP2PrepareCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, e̵m̵i̵t̵t̵e̵r̵P̵2̵P̵r̵e̵p̵a̵r̵e̵C̵f̵g̵,̵ ̵sub_eq_add_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:6314:50: warning: This simp argument is unused:
  emitterP2PrepareCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply,̵ ̵e̵m̵i̵t̵t̵e̵r̵P̵2̵P̵r̵e̵p̵a̵r̵e̵C̵f̵g̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:6325:52: warning: This simp argument is unused:
  emitterP2PrepareCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, e̵m̵i̵t̵t̵e̵r̵P̵2̵P̵r̵e̵p̵a̵r̵e̵C̵f̵g̵,̵ ̵sub_eq_add_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:6705:74: warning: This simp argument is unused:
  emitterP2RightIndex

Hint: Omit it from the simp argument list.
  simp [emitterP2LeftIndex,̵ ̵e̵m̵i̵t̵t̵e̵r̵P̵2̵R̵i̵g̵h̵t̵I̵n̵d̵e̵x̵] at hv

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:6719:54: warning: This simp argument is unused:
  emitterP2LeftIndex

Hint: Omit it from the simp argument list.
  simp [emitterP2L̵e̵f̵t̵I̵n̵d̵e̵x̵,̵ ̵e̵m̵i̵t̵t̵e̵r̵P̵2̵RightIndex] at hv

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:6726:56: warning: This simp argument is unused:
  emitterP2LeftIndex

Hint: Omit it from the simp argument list.
  simp [emitterP2L̵e̵f̵t̵I̵n̵d̵e̵x̵,̵ ̵e̵m̵i̵t̵t̵e̵r̵P̵2̵RightIndex] at hv

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:7455:6: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:7455:6: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:7458:6: warning: 'simp [MultiTapeTM.step, emitterTokenTM, Action.apply, scanCfg, List.append_assoc]' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:7458:6: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:7509:63: warning: This simp argument is unused:
  List.append_assoc

Hint: Omit it from the simp argument list.
  simp [emitterTokenTM, Action.apply, scanCfg, pairEncode, L̵i̵s̵t̵.̵a̵p̵p̵e̵n̵d̵_̵a̵s̵s̵o̵c̵,̵ ̵hlen]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
== TCSlib/Complexity/ClassNP/PolyTimePairing  13:10:46
== TCSlib/Complexity/ClassP/DTIME  13:10:47
== TCSlib/Complexity/ClassP/P  13:10:48
== TCSlib/Complexity/ClassNP/NP  13:10:50
== TCSlib/Complexity/ClassNP/EXP  13:10:51
TCSlib/Complexity/ClassNP/EXP.lean:2734:66: warning: This simp argument is unused:
  bufferTape

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.initCfg, Cfg.init, a3LoadCfg,̵ ̵b̵u̵f̵f̵e̵r̵T̵a̵p̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/EXP.lean:2760:88: warning: This simp argument is unused:
  bufferTape

Hint: Omit it from the simp argument list.
  simp [Action.apply, Cfg.ofWords, stateWord, b̵u̵f̵f̵e̵r̵T̵a̵p̵e̵,̵ ̵hz]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/EXP.lean:2778:66: warning: This simp argument is unused:
  a3LoadCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, a̵3̵L̵o̵a̵d̵C̵f̵g̵,̵ ̵hz]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/EXP.lean:2779:66: warning: This simp argument is unused:
  a3LoadCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, a̵3̵L̵o̵a̵d̵C̵f̵g̵,̵ ̵hz, sub_eq_add_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
== TCSlib/Complexity/ClassNP/ExpPoly  13:10:58
== TCSlib/Complexity/ClassNP/CoNP  13:11:00
== TCSlib/Complexity/ClassNP/PClosure  13:11:01
== TCSlib/Complexity/ClassNP/Transducer  13:11:02
== TCSlib/Complexity/SpaceComplexity/Basic  13:11:03
== TCSlib/Complexity/SpaceComplexity/ConfigCount  13:11:04
== TCSlib/Complexity/SpaceComplexity/Machines/Layout  13:11:06
== TCSlib/Complexity/SpaceComplexity/Machines/Program  13:11:08
== TCSlib/Complexity/SpaceComplexity/Machines/Sim  13:11:10
== TCSlib/Complexity/SpaceComplexity/Machines/CallReturn  13:11:13
== TCSlib/Complexity/SpaceComplexity/Machines/Call  13:11:15
== TCSlib/Complexity/SpaceComplexity/Machines/Compile  13:11:18
== TCSlib/Complexity/SpaceComplexity/Machines/CleanSweep  13:11:19
== TCSlib/Complexity/SpaceComplexity/Machines/Clean  13:11:21
== TCSlib/Complexity/SpaceComplexity/Machines/Bank  13:11:23
== TCSlib/Complexity/SpaceComplexity/Machines/Bin  13:11:24
== TCSlib/Complexity/SpaceComplexity/Machines/Lib  13:11:25
== TCSlib/Complexity/SpaceComplexity/Machines/FragDec  13:11:27
== TCSlib/Complexity/SpaceComplexity/Machines/Frag  13:11:29
== TCSlib/Complexity/SpaceComplexity/Machines/ParsePlain  13:11:31
== TCSlib/Complexity/SpaceComplexity/Machines/Parse  13:11:34
== TCSlib/Complexity/SpaceComplexity/Machines/Parse2  13:11:36
== TCSlib/Complexity/SpaceComplexity/Machines/ParseCmp  13:11:40
== TCSlib/Complexity/SpaceComplexity/Machines/ARM  13:11:43
== TCSlib/Complexity/SpaceComplexity/Machines/ARMSim  13:11:44
== TCSlib/Complexity/SpaceComplexity/Machines/ARMRun  13:11:46
== TCSlib/Complexity/SpaceComplexity/Machines/ARMProof  13:11:48
== TCSlib/Complexity/SpaceComplexity/ImplicitPoly  13:11:50
== TCSlib/Complexity/SpaceComplexity/Machines/ARMKit  13:11:53
== TCSlib/Complexity/SpaceComplexity/Machines/DblLang  13:11:55
== TCSlib/Complexity/SpaceComplexity/UnaryLogspace  13:11:57
== TCSlib/Complexity/SpaceComplexity/CounterProgSim  13:11:58
== TCSlib/Complexity/SpaceComplexity/CounterProgSimRun  13:12:00
== TCSlib/Complexity/SpaceComplexity  13:12:02
== TCSlib/Complexity/TimeHierarchy/ClockMachine  13:12:03
== TCSlib/Complexity/TimeHierarchy/ClockLoop  13:12:05
== TCSlib/Complexity/TimeHierarchy/CodePrefix  13:12:07
== TCSlib/Complexity/TuringMachine/CodeParser  13:12:08
TCSlib/Complexity/TuringMachine/CodeParser.lean:339:13: warning: This simp argument is unused:
  codeBitsNat_bits

Hint: Omit it from the simp argument list.
  simp only [c̵o̵d̵e̵B̵i̵t̵s̵N̵a̵t̵_̵b̵i̵t̵s̵,̵ ̵List.append_assoc, codeReadFin_append, bind, Option.bind,
  ̵  ̵ ̵ ̵codeReadTable_append,
  ̲  ̲ ̲ ̲List.all_replicate, id_eq, Bool.true_eq, or_true,
  ̵  ̵ ̵ ̵ite_self, ↓reduceIte, pure]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:339:70: warning: This simp argument is unused:
  bind

Hint: Omit it from the simp argument list.
  simp only [codeBitsNat_bits, List.append_assoc, codeReadFin_append, b̵i̵n̵d̵,̵ ̵Option.bind,
      codeReadTable_append, List.all_replicate, id_eq, Bool.true_eq, or_true,
  ̵  ̵ ̵ ̵ite_self, ↓reduceIte,
  ̲  ̲ ̲ ̲pure]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:339:76: warning: This simp argument is unused:
  Option.bind

Hint: Omit it from the simp argument list.
  simp only [codeBitsNat_bits, List.append_assoc, codeReadFin_append, bind, O̵p̵t̵i̵o̵n̵.̵b̵i̵n̵d̵,̵
  ̵ ̵ ̵ ̵ ̵codeReadTable_append,
  ̲  ̲ ̲ ̲List.all_replicate, id_eq, Bool.true_eq, or_true,
  ̵  ̵ ̵ ̵ite_self, ↓reduceIte, pure]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:340:53: warning: This simp argument is unused:
  Bool.true_eq

Hint: Omit it from the simp argument list.
  simp only [codeBitsNat_bits, List.append_assoc, codeReadFin_append, bind, Option.bind,
      codeReadTable_append, List.all_replicate, id_eq, B̵oo̵l̵.̵t̵ru̵e̵_e̵q̵,̵ ̵o̵r̵_̵true,
  ̵  ̵ ̵ ̵ite_self, ↓reduceIte, pure]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:340:67: warning: This simp argument is unused:
  or_true

Hint: Omit it from the simp argument list.
  simp only [codeBitsNat_bits, List.append_assoc, codeReadFin_append, bind, Option.bind,
      codeReadTable_append, List.all_replicate, id_eq, Bool.true_eq, o̵r̵_̵t̵r̵u̵e̵,̵
  ̵ ̵ ̵ ̵ ̵ite_self, ↓reduceIte, pure]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:420:43: warning: This simp argument is unused:
  h₁

Hint: Omit it from the simp argument list.
  simp [pairDecode, h₁̵,̵ ̵h̵₂, h₃] at h

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:420:47: warning: This simp argument is unused:
  h₂

Hint: Omit it from the simp argument list.
  simp [pairDecode, h₁, h₂̵,̵ ̵h̵₃] at h

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:420:51: warning: This simp argument is unused:
  h₃

Hint: Omit it from the simp argument list.
  simp [pairDecode, h₁, h₂,̵ ̵h̵₃̵] at h

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
== TCSlib/Complexity/TuringMachine/MathlibBridge  13:12:10
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:450:8: warning: This simp argument is unused:
  Function.update_self

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index, F̵u̵n̵c̵t̵i̵o̵n̵.̵u̵p̵d̵a̵t̵e̵_̵s̵e̵l̵f̵,̵ ̵hs]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:456:12: warning: This simp argument is unused:
  Action.apply_workTapes

Hint: Omit it from the simp argument list.
  simp [A̵c̵t̵i̵o̵n̵.̵a̵p̵p̵l̵y̵_̵w̵o̵r̵k̵T̵a̵p̵e̵s̵,̵ ̵bridgeOne, bridgeCfg, hi, hk]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:461:8: warning: This simp argument is unused:
  Function.update_self

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index, F̵u̵n̵c̵t̵i̵o̵n̵.̵u̵p̵d̵a̵t̵e̵_̵s̵e̵l̵f̵,̵ ̵hs,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲SignType.pos_eq_one, SignType.coe_one, List.length_cons, Nat.cast_add, Nat.cast_one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:486:8: warning: This simp argument is unused:
  Function.update_self

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index,
          F̵u̵n̵c̵t̵i̵o̵n̵.̵u̵p̵d̵a̵t̵e̵_̵s̵e̵l̵f̵,̵ ̵SignType.neg_eq_neg_one, SignType.coe_neg_one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:492:12: warning: This simp argument is unused:
  Action.apply_workTapes

Hint: Omit it from the simp argument list.
  simp [A̵c̵t̵i̵o̵n̵.̵a̵p̵p̵l̵y̵_̵w̵o̵r̵k̵T̵a̵p̵e̵s̵,̵ ̵bridgeOne, bridgeCfg, hi, hk]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:497:8: warning: This simp argument is unused:
  Function.update_self

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index,
          F̵u̵n̵c̵t̵i̵o̵n̵.̵u̵p̵d̵a̵t̵e̵_̵s̵e̵l̵f̵,̵ ̵SignType.neg_eq_neg_one, SignType.coe_neg_one, SignType.zero_eq_zero, SignType.coe_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲List.length_cons, Nat.cast_add, Nat.cast_one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:498:50: warning: This simp argument is unused:
  List.length_cons

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index,
          Function.update_self, SignType.neg_eq_neg_one, SignType.coe_neg_one, SignType.zero_eq_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲SignType.coe_zero, L̵i̵s̵t̵.̵l̵e̵n̵g̵t̵h̵_̵c̵o̵n̵s̵,̵ ̵Nat.cast_add, Nat.cast_one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:498:68: warning: This simp argument is unused:
  Nat.cast_add

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index,
          Function.update_self, SignType.neg_eq_neg_one, SignType.coe_neg_one, SignType.zero_eq_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲SignType.coe_zero, List.length_cons, N̵a̵t̵.̵c̵a̵s̵t̵_̵a̵d̵d̵,̵ ̵Nat.cast_one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:498:82: warning: This simp argument is unused:
  Nat.cast_one

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index,
          Function.update_self, SignType.neg_eq_neg_one, SignType.coe_neg_one, SignType.zero_eq_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲SignType.coe_zero, List.length_cons, N̵a̵t̵.̵c̵a̵s̵t̵_̵a̵d̵d̵,̵ ̵N̵a̵t̵.̵c̵a̵s̵t̵_̵o̵n̵e̵]̵N̲a̲t̲.̲c̲a̲s̲t̲_̲a̲d̲d̲]̲

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:721:32: warning: This simp argument is unused:
  Num.cast_zero

Hint: Omit it from the simp argument list.
  simp only [Num.to_of_nat,̵ ̵N̵u̵m̵.̵c̵a̵s̵t̵_̵z̵e̵r̵o̵] at hz

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:823:75: warning: This simp argument is unused:
  hk

Hint: Omit it from the simp argument list.
  simp [bridgeStore, PartrecToTM2.K'.elim, hi, hk̵,̵ ̵h̵] at *

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:871:15: warning: This simp argument is unused:
  Action.apply

Hint: Omit it from the simp argument list.
  simp only [̵A̵c̵t̵i̵o̵n̵.̵a̵p̵p̵l̵y̵,̵ ̵b̵r̵i̵d̵g̵e̵C̵f̵g̵,̵[̲b̲r̲i̲d̲g̲e̲C̲f̲g̲,̲ bridgeOne, SignType.zero_eq_zero, moveInputPos_zero]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:871:40: warning: This simp argument is unused:
  bridgeOne

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeCfg, b̵r̵i̵d̵g̵e̵O̵n̵e̵,̵ ̵SignType.zero_eq_zero, moveInputPos_zero]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:880:41: warning: This simp argument is unused:
  SignType.coe_zero

Hint: Omit it from the simp argument list.
  simp only [bridgeCfg, bridgeStore_at, ↓reduceIte, List.length_nil, Nat.cast_zero, neg_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲SignType.zero_eq_zero, S̵i̵g̵n̵T̵y̵p̵e̵.̵c̵o̵e̵_̵z̵e̵r̵o̵,̵ ̵SignType.neg_eq_neg_one, SignType.coe_neg_one, zero_add]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
== TCSlib/Complexity/TuringMachine/UniversalStartup  13:12:12
TCSlib/Complexity/TuringMachine/UniversalStartup.lean:160:54: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalStartup.lean:164:54: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalStartup.lean:190:52: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalStartup.lean:197:54: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalStartup.lean:215:52: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalStartup.lean:274:46: warning: This simp argument is unused:
  VirtualTag

Hint: Omit it from the simp argument list.
  simp_all ̵[̵V̵i̵r̵t̵u̵a̵l̵T̵a̵g̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
== TCSlib/Complexity/TuringMachine/UniversalInterpreter  13:12:13
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:330:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:353:6: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:378:83: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:439:60: warning: This simp argument is unused:
  zero_add

Hint: Omit it from the simp argument list.
  simp only [universalStateWindow, Nat.cast_zero, add_zero,̵ ̵z̵e̵r̵o̵_̵a̵d̵d̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:503:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:510:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:519:71: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:519:83: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:546:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:553:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:563:39: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:1020:75: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:1021:16: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:1021:28: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
== TCSlib/Complexity/TuringMachine/UniversalBlock  13:12:17
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:68:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:83:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:62:10: warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:79:64: warning: This simp argument is unused:
  universalSkipDone

Hint: Omit it from the simp argument list.
  simp [universalInterpreter, universalFour, hr, h, hz,̵ ̵u̵n̵i̵v̵e̵r̵s̵a̵l̵S̵k̵i̵p̵D̵o̵n̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:93:50: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:93:62: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:108:10: warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:164:53: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:164:65: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:185:50: warning: This simp argument is unused:
  Nat.add_zero

Hint: Omit it from the simp argument list.
  simp only [List.length_nil, List.flatMap_nil, Nat.a̵d̵d̵_̵zero,̵ ̵N̵a̵t̵.̵z̵e̵r̵o̵_add,
  ̵  ̵ ̵ ̵ ̵ ̵Nat.cast_zero, add_zero,
  ̲  ̲ ̲ ̲ ̲ ̲MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:244:40: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:271:40: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:289:6: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:289:61: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:289:73: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:289:6: warning: 'simp only [Fin.val_mk, Nat.cast_add, Nat.cast_one]' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:289:61: warning: 'congr 1' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:289:73: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:313:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:321:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:426:40: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:574:68: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
== TCSlib/Complexity/TuringMachine/Universal  13:12:20
TCSlib/Complexity/TuringMachine/Universal.lean:310:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:333:6: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:358:83: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:423:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:430:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:439:71: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:439:83: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:466:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:473:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:483:39: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:617:75: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:618:16: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:618:28: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:640:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:655:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:634:10: warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
TCSlib/Complexity/TuringMachine/Universal.lean:651:85: warning: This simp argument is unused:
  universalSkipDone

Hint: Omit it from the simp argument list.
  simp [timedCutInterpreter, universalInterpreter, universalFour, hr, h, hz,̵ ̵u̵n̵i̵v̵e̵r̵s̵a̵l̵S̵k̵i̵p̵D̵o̵n̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Universal.lean:665:50: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:665:62: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:680:10: warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
TCSlib/Complexity/TuringMachine/Universal.lean:736:53: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:736:65: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:757:50: warning: This simp argument is unused:
  Nat.add_zero

Hint: Omit it from the simp argument list.
  simp only [List.length_nil, List.flatMap_nil, Nat.a̵d̵d̵_̵zero,̵ ̵N̵a̵t̵.̵z̵e̵r̵o̵_add,
  ̵  ̵ ̵ ̵ ̵ ̵Nat.cast_zero, add_zero,
  ̲  ̲ ̲ ̲ ̲ ̲MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Universal.lean:816:40: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:843:40: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:861:6: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:861:61: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:861:73: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:861:6: warning: 'simp only [Fin.val_mk, Nat.cast_add, Nat.cast_one]' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:861:61: warning: 'congr 1' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:861:73: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:885:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:893:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:1002:40: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:1102:68: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Universal.lean:1480:16: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1480:34: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1480:61: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1480:16: warning: 'apply Fin.ext' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1480:34: warning: 'simp only [Fin.val_mk]' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1480:61: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1574:30: warning: This simp argument is unused:
  Nat.reduceAdd

Hint: Omit it from the simp argument list.
  simp only [Nat.add_assoc,̵ ̵N̵a̵t̵.̵r̵e̵d̵u̵c̵e̵A̵d̵d̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Universal.lean:1579:16: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1579:34: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1579:61: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1579:16: warning: 'apply Fin.ext' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1579:34: warning: 'simp only [Fin.val_mk]' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1579:61: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1602:28: warning: This simp argument is unused:
  Nat.reduceAdd

Hint: Omit it from the simp argument list.
  simp only [Nat.add_assoc,̵ ̵N̵a̵t̵.̵r̵e̵d̵u̵c̵e̵A̵d̵d̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Universal.lean:1604:43: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Universal.lean:1604:10: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:1604:28: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:1604:55: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:2274:46: warning: This simp argument is unused:
  VirtualTag

Hint: Omit it from the simp argument list.
  simp_all ̵[̵V̵i̵r̵t̵u̵a̵l̵T̵a̵g̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
== TCSlib/Complexity/TimeHierarchy/Diagonal  13:12:27
== TCSlib/Complexity/TimeHierarchy/Separation  13:12:30
== TCSlib/Complexity/TimeHierarchy  13:12:31
SWEEP_OK 71-module closure, fresh scratch tree, at e64cec9e

```


## ===== audits/logs/ch34-p0-stylelint.log =====

```
INFO  TCSlib/Complexity/TimeHierarchy/ClockLoop.lean     369 lines; 9 public / 0 private declarations
INFO  TCSlib/Complexity/TimeHierarchy/ClockMachine.lean  539 lines; 33 public / 0 private declarations
INFO  TCSlib/Complexity/TimeHierarchy/CodePrefix.lean    280 lines; 7 public / 3 private declarations
INFO  TCSlib/Complexity/TimeHierarchy/Diagonal.lean      313 lines; 10 public / 0 private declarations
INFO  TCSlib/Complexity/TimeHierarchy/Separation.lean    183 lines; 6 public / 3 private declarations

style_lint: 0 FAIL, 0 WARN over 5 files
INFO  TCSlib/Complexity/SpaceComplexity/Basic.lean                149 lines; 10 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/ConfigCount.lean          460 lines; 19 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/CounterProgSim.lean       495 lines; 25 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/CounterProgSimRun.lean    246 lines; 6 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/ImplicitPoly.lean         416 lines; 16 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ARM.lean         304 lines; 20 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ARMKit.lean      93 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ARMProof.lean    333 lines; 19 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ARMRun.lean      285 lines; 9 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ARMSim.lean      548 lines; 30 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Bank.lean        226 lines; 14 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Bin.lean         176 lines; 12 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Call.lean        360 lines; 6 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/CallReturn.lean  495 lines; 13 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Clean.lean       438 lines; 15 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/CleanSweep.lean  508 lines; 22 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Compile.lean     265 lines; 11 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/DblLang.lean     358 lines; 20 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Frag.lean        455 lines; 15 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/FragDec.lean     479 lines; 21 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Layout.lean      421 lines; 29 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Lib.lean         333 lines; 16 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Parse.lean       376 lines; 9 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Parse2.lean      662 lines > target 600
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Parse2.lean      662 lines; 24 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ParseCmp.lean    438 lines; 14 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ParsePlain.lean  571 lines; 28 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Program.lean     342 lines; 25 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Sim.lean         564 lines; 25 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/UnaryLogspace.lean        319 lines; 26 public / 0 private declarations

style_lint: 0 FAIL, 0 WARN over 29 files
WARN  TCSlib/Complexity/TuringMachine/Build/Loop.lean                     5713 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/Primitives.lean               7636 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/MathlibBridge.lean                  1109 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean           1147 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean  1127 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean      1102 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Universal.lean                      2884 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean           1027 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
INFO  TCSlib/Complexity/TuringMachine/Build/Convention.lean               157 lines; 8 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Loop.lean                     5713 lines; 8 public / 214 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Primitives.lean               7636 lines; 18 public / 318 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Wrappers.lean                 739 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Build/Wrappers.lean                 739 lines; 10 public / 19 private declarations
INFO  TCSlib/Complexity/TuringMachine/CodeParser.lean                     790 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/CodeParser.lean                     790 lines; 13 public / 49 private declarations
INFO  TCSlib/Complexity/TuringMachine/Composition.lean                    685 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Composition.lean                    685 lines; 8 public / 11 private declarations
INFO  TCSlib/Complexity/TuringMachine/Configuration.lean                  224 lines; 18 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/CounterProg.lean                    562 lines; 28 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/CounterProgRun.lean                 414 lines; 34 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Deterministic.lean                  430 lines; 34 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Encoding.lean                       606 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Encoding.lean                       606 lines; 30 public / 10 private declarations
INFO  TCSlib/Complexity/TuringMachine/Finite.lean                         257 lines; 13 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/MathlibBridge.lean                  1109 lines; 2 public / 75 private declarations
INFO  TCSlib/Complexity/TuringMachine/Nondeterministic.lean               248 lines; 16 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Oracle.lean                         517 lines; 29 public / 2 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean   600 lines; 1 public / 50 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/Bidirectional.lean       464 lines; 2 public / 37 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean           1147 lines; 1 public / 38 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean  1127 lines; 47 public / 42 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/ObliviousLedger.lean     219 lines; 4 public / 2 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule.lean   688 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule.lean   688 lines; 19 public / 20 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean      1102 lines; 8 public / 59 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean          981 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean          981 lines; 2 public / 53 private declarations
INFO  TCSlib/Complexity/TuringMachine/Simulation.lean                     948 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Simulation.lean                     948 lines; 49 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/StateRenaming.lean                  124 lines; 6 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Sweep.lean                          392 lines; 22 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/UnaryTape.lean                      84 lines; 8 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Universal.lean                      2884 lines; 4 public / 129 private declarations
INFO  TCSlib/Complexity/TuringMachine/UniversalBlock.lean                 794 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/UniversalBlock.lean                 794 lines; 6 public / 17 private declarations
INFO  TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean           1027 lines; 37 public / 13 private declarations
INFO  TCSlib/Complexity/TuringMachine/UniversalStartup.lean               591 lines; 10 public / 21 private declarations

style_lint: 0 FAIL, 8 WARN over 31 files
WARN  TCSlib/Complexity/ClassNP/EXP.lean                  3237 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/ClassNP/Nondeterminism.lean       4416 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/ClassNP/SAT.lean                  4635 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/ClassNP/TMSAT.lean                1755 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/ClassNP/Tautology.lean            1728 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
INFO  TCSlib/Complexity/ClassNP/CoNP.lean                 165 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/ClassNP/CounterProgPolyTime.lean  90 lines; 2 public / 0 private declarations
INFO  TCSlib/Complexity/ClassNP/EXP.lean                  3237 lines; 8 public / 145 private declarations
INFO  TCSlib/Complexity/ClassNP/ExpPoly.lean              153 lines; 8 public / 1 private declarations
INFO  TCSlib/Complexity/ClassNP/NP.lean                   559 lines; 3 public / 30 private declarations
INFO  TCSlib/Complexity/ClassNP/NTIME.lean                222 lines; 7 public / 0 private declarations
INFO  TCSlib/Complexity/ClassNP/Nondeterminism.lean       4416 lines; 8 public / 198 private declarations
INFO  TCSlib/Complexity/ClassNP/PClosure.lean             183 lines; 13 public / 0 private declarations
INFO  TCSlib/Complexity/ClassNP/PolyTime.lean             162 lines; 5 public / 1 private declarations
INFO  TCSlib/Complexity/ClassNP/PolyTimePairing.lean      338 lines; 24 public / 2 private declarations
INFO  TCSlib/Complexity/ClassNP/Reductions.lean           477 lines; 10 public / 16 private declarations
INFO  TCSlib/Complexity/ClassNP/SAT.lean                  4635 lines; 5 public / 277 private declarations
INFO  TCSlib/Complexity/ClassNP/TMSAT.lean                1755 lines; 6 public / 76 private declarations
INFO  TCSlib/Complexity/ClassNP/Tautology.lean            1728 lines; 5 public / 93 private declarations
INFO  TCSlib/Complexity/ClassNP/Transducer.lean           158 lines; 7 public / 0 private declarations

style_lint: 0 FAIL, 5 WARN over 15 files

```


## ===== TCSlib/Complexity/TuringMachine/UnaryTape.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.SplitIfs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Unary work tapes

A work tape (`ℤ → Option Bool`, as in `Turing.Cfg`) holding a natural number `m` in unary:
cells `0, …, m - 1` hold `1` and every other cell is blank. Machines that keep counters on
their work tapes in unary — the Tseitin emitter of
`TCSlib.Complexity.CircuitComplexity.CircuitSatReductionMachineTapes` and the counter
programs of `TCSlib.Complexity.TuringMachine.CounterProg` — increment a counter by writing
`1` on its first blank cell and decrement it by erasing its last cell.

## Main definitions

* `Turing.UnaryTape.ones` — the unary tape of `m`.
* `Turing.UnaryTape.wrT` — the effect of an optional write at a head position.

## Main results

* `Turing.UnaryTape.update_ones_succ`, `Turing.UnaryTape.update_ones_pred` — increment and
  decrement.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2: the multi-tape machine.)
-/

namespace Turing

namespace UnaryTape

/-- The unary tape of a counter with value `m`: cells `0, …, m - 1` hold `1`. -/
def ones (m : ℕ) : ℤ → Option Bool := fun c => if 0 ≤ c ∧ c < m then some true else none

/-- A unary tape holds `1` on the cells `0, …, m - 1`. -/
theorem ones_lt {m : ℕ} {c : ℤ} (h0 : 0 ≤ c) (h : c < m) : ones m c = some true := by
  simp [ones, h0, h]

/-- A unary tape is blank from cell `m` on. -/
theorem ones_ge {m : ℕ} {c : ℤ} (h : (m : ℤ) ≤ c) : ones m c = none := by
  simp only [ones]; rw [if_neg]; omega

/-- A unary tape is blank left of cell `0`. -/
theorem ones_neg {m : ℕ} {c : ℤ} (h : c < 0) : ones m c = none := by
  simp only [ones]; rw [if_neg]; omega

/-- The unary tape of `0` is blank. -/
theorem ones_zero : ones 0 = fun _ => none := by
  funext c; simp only [ones]; rw [if_neg]; omega

/-- Writing `1` on the first blank cell of the unary tape of `m` gives that of `m + 1`. -/
theorem update_ones_succ (m : ℕ) :
    Function.update (ones m) (m : ℤ) (some true) = ones (m + 1) := by
  funext c
  simp only [Function.update_apply, ones]
  split_ifs <;> first | rfl | (exfalso; omega)

/-- Erasing the last cell of the unary tape of `j + 1` gives that of `j`. -/
theorem update_ones_pred (j : ℕ) :
    Function.update (ones (j + 1)) (j : ℤ) none = ones j := by
  funext c
  simp only [Function.update_apply, ones]
  split_ifs <;> first | rfl | (exfalso; omega)

/-- Writing at a head position: no write leaves the tape unchanged, a write `some s` sets
the cell `pos` to `s`. -/
def wrT (tape : ℤ → Option Bool) (pos : ℤ) : Option (Option Bool) → ℤ → Option Bool
  | none => tape
  | some s => Function.update tape pos s

end UnaryTape

end Turing

```


## ===== TCSlib/Complexity/TuringMachine/CounterProg.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Tactic.DeriveFintype
import TCSlib.Complexity.TuringMachine.Simulation
import TCSlib.Complexity.TuringMachine.UnaryTape

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Unary counter programs and their Turing machines

A small programming model for the polynomial-time *emitters* of [AB09, §6.2] (the machine
that prints the circuit of [AB09, Thm 6.6], Remark 6.7): a **counter program** is a goto
program over finitely many registers holding natural numbers, which can increment,
decrement and zero-test a register, print a bit or print the value of a register in unary,
and read its input once from left to right.  Every counter program is compiled into a
binary multi-tape Turing machine of the library's model (`Turing.FinTM`), one work tape
per register holding the value in unary, and an abstract run of `t` steps is simulated in
at most `t (2t + 3)` machine steps (`Complexity.CounterProg.exists_tm`).  Hence a string
function computed by a counter program in polynomially many abstract steps is
polynomial-time computable (`Complexity.CounterProg.polyTimeComputable`,
`TCSlib.Complexity.ClassNP.CounterProgPolyTime`).

The compilation follows the three-counter machine of the `CKT-SAT ≤p 3SAT` emitter
(`CircuitComplexity/CircuitSatReductionMachine.lean`), made generic: a register of value
`v` is the tape `1ᵛ` (`Turing.UnaryTape.ones`) with its head on the blank cell `v`.

Counter programs keep their registers in **unary**, which suits polynomial-time
emitters. The logarithmic-space counterpart, with registers in binary and a read-only
input, is the abstract register machine `Complexity.LogProg` of
`TCSlib.Complexity.SpaceComplexity.Machines` (cf. `SpaceComplexity/Machines/ARM.lean`);
a polynomially-running counter program is simulated by one in
`TCSlib.Complexity.SpaceComplexity.CounterProgSim`.

## Main definitions

* `Complexity.CounterProg.Instr`, `Complexity.CounterProg.St` — instructions and abstract
  states; `Complexity.CounterProg.step`, `Complexity.CounterProg.run` — the semantics.
* `Complexity.CounterProg.toTM` — the compiled machine.

## Main results

* `Complexity.CounterProg.sim_step` — one abstract step is at most `2B + 3` machine steps
  when all registers are at most `B`.
* (The simulation of whole runs, `Complexity.CounterProg.exists_tm`, is in
  `TCSlib.Complexity.TuringMachine.CounterProgRun`.)

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§1.2: the multi-tape machine; §6.2, Remark 6.7.)
-/

namespace Complexity

namespace CounterProg

open Turing Turing.UnaryTape

/-! ## Programs and their semantics -/

/-- An instruction of a counter program over `R` registers with labels `Λ`: halt, jump,
print a bit, increment or decrement (saturating at `0`) a register, branch on a register
being zero, print a register's value in unary (`1ᵛ`), or read the next input symbol
(branching on end-of-input / `0` / `1`; a read symbol is consumed). -/
inductive Instr (R : ℕ) (Λ : Type) where
  /-- Stop. -/
  | halt
  /-- Jump to `next`. -/
  | goto (next : Λ)
  /-- Print the bit `b`. -/
  | out (b : Bool) (next : Λ)
  /-- Increment register `r`. -/
  | inc (r : Fin R) (next : Λ)
  /-- Decrement register `r` (`0` stays `0`). -/
  | dec (r : Fin R) (next : Λ)
  /-- Go to `zero` if register `r` is `0`, else to `pos`. -/
  | jz (r : Fin R) (zero pos : Λ)
  /-- Print `1ᵛ`, `v` the value of register `r`. -/
  | pr (r : Fin R) (next : Λ)
  /-- Read the next input symbol: at the end go to `onEnd`, else consume it and go to
  `onFalse` or `onTrue`. -/
  | rd (onEnd onFalse onTrue : Λ)

/-- An abstract state: the current label (`none` once halted), the registers, the number
of input symbols consumed, and the output so far. -/
@[ext]
structure St (R : ℕ) (Λ : Type) where
  /-- The current label, `none` when halted. -/
  lbl : Option Λ
  /-- The register values. -/
  regs : Fin R → ℕ
  /-- The number of input symbols read. -/
  pos : ℕ
  /-- The output printed so far. -/
  out : List Bool

variable {R : ℕ} {Λ : Type}

/-- **One step** of the program `P` on input `x`. -/
def step (P : Λ → Instr R Λ) (x : List Bool) (s : St R Λ) : St R Λ :=
  match s.lbl with
  | none => s
  | some l =>
    match P l with
    | .halt => ⟨none, s.regs, s.pos, s.out⟩
    | .goto l' => ⟨some l', s.regs, s.pos, s.out⟩
    | .out b l' => ⟨some l', s.regs, s.pos, s.out ++ [b]⟩
    | .inc r l' => ⟨some l', Function.update s.regs r (s.regs r + 1), s.pos, s.out⟩
    | .dec r l' => ⟨some l', Function.update s.regs r (s.regs r - 1), s.pos, s.out⟩
    | .jz r l0 l1 => ⟨some (if s.regs r = 0 then l0 else l1), s.regs, s.pos, s.out⟩
    | .pr r l' => ⟨some l', s.regs, s.pos, s.out ++ List.replicate (s.regs r) true⟩
    | .rd le lf lt =>
      match x[s.pos]? with
      | none => ⟨some le, s.regs, s.pos, s.out⟩
      | some false => ⟨some lf, s.regs, s.pos + 1, s.out⟩
      | some true => ⟨some lt, s.regs, s.pos + 1, s.out⟩

/-- `t` steps of the program. -/
def run (P : Λ → Instr R Λ) (x : List Bool) (s : St R Λ) (t : ℕ) : St R Λ :=
  (step P x)^[t] s

/-- The initial state at label `l₀`: all registers `0`, nothing read or printed. -/
def init (l₀ : Λ) : St R Λ := ⟨some l₀, fun _ => 0, 0, []⟩

variable (P : Λ → Instr R Λ) (x : List Bool)

/-- Zero steps change nothing. -/
theorem run_zero (s : St R Λ) : run P x s 0 = s := rfl

/-- Running `a + b` steps is running `a` steps, then `b`. -/
theorem run_add (s : St R Λ) (a b : ℕ) : run P x s (a + b) = run P x (run P x s a) b := by
  simp only [run, Nat.add_comm a b, Function.iterate_add_apply]

/-- Running `t + 1` steps is one step, then `t` steps. -/
theorem run_succ (s : St R Λ) (t : ℕ) : run P x s (t + 1) = run P x (step P x s) t := by
  simp only [run, Function.iterate_succ_apply]

/-- A halted state does not change. -/
theorem run_of_halted (s : St R Λ) (h : s.lbl = none) (t : ℕ) : run P x s t = s := by
  induction t with
  | zero => rfl
  | succ t ih => rw [run_succ, show step P x s = s by simp [step, h], ih]

/-- A step increases each register by at most one. -/
theorem step_regs_le (s : St R Λ) (r : Fin R) : (step P x s).regs r ≤ s.regs r + 1 := by
  unfold step
  split
  · omega
  · split <;> (try split) <;> simp only [Function.update_apply] <;> (try split_ifs) <;>
      first | omega | (subst_vars; omega)

/-- A step never moves past the end of the input. -/
theorem step_pos_le (s : St R Λ) (h : s.pos ≤ x.length) : (step P x s).pos ≤ x.length := by
  unfold step
  split
  · exact h
  · split <;> try exact h
    split
    · exact h
    all_goals
      rename_i heq
      have := (List.getElem?_eq_some_iff.mp heq).1
      simp only; omega

/-- After `t` steps each register has grown by at most `t`. -/
theorem run_regs_le (s : St R Λ) (r : Fin R) (t : ℕ) : (run P x s t).regs r ≤ s.regs r + t := by
  induction t generalizing s with
  | zero => simp [run_zero]
  | succ t ih =>
    rw [run_succ]
    have := ih (step P x s)
    have := step_regs_le P x s r
    omega

/-! ## The compiled machine -/

/-- The control states of the compiled machine: executing a label (`main`), or in the
middle of a decrement, a zero test, or the two walks of a print. -/
inductive TSt (R : ℕ) (Λ : Type) where
  /-- About to execute the instruction at label `l`. -/
  | main (l : Λ)
  /-- Second step of a decrement of `r`. -/
  | decB (r : Fin R) (l : Λ)
  /-- Second step of a zero test of `r`. -/
  | jzB (r : Fin R) (l0 l1 : Λ)
  /-- Printing register `r`: walking left over its cells. -/
  | prW (r : Fin R) (l : Λ)
  /-- Printing register `r`: walking back right. -/
  | prB (r : Fin R) (l : Λ)
  deriving DecidableEq, Fintype

/-- An action on work tape `t` only. -/
def act (t : Fin R) (im : SignType) (wr : Option (Option Bool)) (m : SignType)
    (o : Option Bool) (q : Option (TSt R Λ)) : Action R Bool (TSt R Λ) :=
  ⟨im, fun i => if i = t then (wr, m) else (none, 0), o, q⟩

/-- An action touching no work tape. -/
def ctl (im : SignType) (o : Option Bool) (q : Option (TSt R Λ)) : Action R Bool (TSt R Λ) :=
  ⟨im, fun _ => (none, 0), o, q⟩

/-- **The transition table** of the compiled machine. -/
def tr : TSt R Λ → Option Bool → (Fin R → Option Bool) → Action R Bool (TSt R Λ)
  | .main l, sym, _ =>
    match P l with
    | .halt => ctl 0 none none
    | .goto l' => ctl 0 none (some (.main l'))
    | .out b l' => ctl 0 (some b) (some (.main l'))
    | .inc r l' => act r 0 (some (some true)) .pos none (some (.main l'))
    | .dec r l' => act r 0 none .neg none (some (.decB r l'))
    | .jz r l0 l1 => act r 0 none .neg none (some (.jzB r l0 l1))
    | .pr r l' => act r 0 none .neg none (some (.prW r l'))
    | .rd le lf lt =>
      match sym with
      | none => ctl 0 none (some (.main le))
      | some false => ctl .pos none (some (.main lf))
      | some true => ctl .pos none (some (.main lt))
  | .decB r l, _, w =>
    if (w r).isSome then act r 0 (some none) 0 none (some (.main l))
    else act r 0 none .pos none (some (.main l))
  | .jzB r l0 l1, _, w =>
    if (w r).isSome then act r 0 none .pos none (some (.main l1))
    else act r 0 none .pos none (some (.main l0))
  | .prW r l, _, w =>
    if (w r).isSome then act r 0 none .neg (some true) (some (.prW r l))
    else act r 0 none .pos none (some (.prB r l))
  | .prB r l, _, w =>
    if (w r).isSome then act r 0 none .pos none (some (.prB r l))
    else ctl 0 none (some (.main l))

/-- **The machine of a counter program**: one work tape per register, started at `l₀`. -/
def toTM [Fintype Λ] [DecidableEq Λ] (l₀ : Λ) : FinTM Bool where
  k := R
  State := TSt R Λ
  tm := { q₀ := .main l₀, tr := tr P }

variable [Fintype Λ] [DecidableEq Λ] (l₀ : Λ)

/-- The machine configuration of an abstract state: register `r` of value `v` is the tape
`1ᵛ` with its head on cell `v`; the input head reads symbol `pos`. -/
def enc (s : St R Λ) : Cfg R Bool (TSt R Λ) x :=
  ⟨s.lbl.map .main, ⟨min (s.pos + 1) (x.length + 1), by omega⟩, fun r => ones (s.regs r),
    fun r => (s.regs r : ℤ), s.out⟩

/-- One machine step from a running configuration applies the transition. -/
theorem step_some (q : TSt R Λ) (p : Fin (x.length + 2)) (tp : Fin R → ℤ → Option Bool)
    (hd : Fin R → ℤ) (out : List Bool) :
    (toTM P l₀).tm.step (⟨some q, p, tp, hd, out⟩ : Cfg R Bool (TSt R Λ) x) =
      (tr P q (Cfg.inputSymbol (⟨some q, p, tp, hd, out⟩ : Cfg R Bool (TSt R Λ) x))
        (fun i => tp i (hd i))).apply ⟨some q, p, tp, hd, out⟩ := rfl

omit [Fintype Λ] [DecidableEq Λ] in
/-- The effect of a one-tape action. -/
theorem apply_act {q' : Option (TSt R Λ)} (t : Fin R) (im : SignType)
    (wr : Option (Option Bool)) (m : SignType) (o : Option Bool) (q : Option (TSt R Λ))
    (p : Fin (x.length + 2)) (tp : Fin R → ℤ → Option Bool) (hd : Fin R → ℤ)
    (out : List Bool) :
    (act t im wr m o q).apply (⟨q', p, tp, hd, out⟩ : Cfg R Bool (TSt R Λ) x) =
      ⟨q, moveInputPos p im, Function.update tp t (wrT (tp t) (hd t) wr),
        Function.update hd t (hd t + m), out ++ o.toList⟩ := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    by_cases hi : i = t
    · subst hi; cases wr <;> simp [act, Action.apply, wrT]
    · simp [act, Action.apply, hi]
  · funext i
    by_cases hi : i = t
    · subst hi; simp [act, Action.apply]
    · simp [act, Action.apply, hi]

omit [Fintype Λ] [DecidableEq Λ] in
/-- The effect of a tape-free action. -/
theorem apply_ctl {q' : Option (TSt R Λ)} (im : SignType) (o : Option Bool)
    (q : Option (TSt R Λ)) (p : Fin (x.length + 2)) (tp : Fin R → ℤ → Option Bool)
    (hd : Fin R → ℤ) (out : List Bool) :
    (ctl im o q).apply (⟨q', p, tp, hd, out⟩ : Cfg R Bool (TSt R Λ) x) =
      ⟨q, moveInputPos p im, tp, hd, out ++ o.toList⟩ := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i; simp [ctl, Action.apply]
  · funext i; simp [ctl, Action.apply]

/-! ## The walks of a print -/

/-- The left walk of a print: in `prW r l`, from head `j - 1` over a register tape `1ᵐ`
(`j ≤ m`), the machine emits `j` ones in `j + 1` steps and turns into `prB r l` at head
`0`.

**Proof sketch.** Induction on `j`: at head `-1` the cell is blank and the head turns
right; at head `j - 1 ≥ 0` the cell holds `1`, which is emitted, and the head moves left. -/
theorem print_walk (r : Fin R) (l : Λ) (p : Fin (x.length + 2)) (tp : Fin R → ℤ → Option Bool)
    (hd : Fin R → ℤ) (m : ℕ) (htp : tp r = ones m) :
    ∀ (j : ℕ) (out : List Bool), j ≤ m →
      (toTM P l₀).tm.runFrom (⟨some (.prW r l), p, tp, Function.update hd r ((j : ℤ) - 1),
        out⟩ : Cfg R Bool (TSt R Λ) x) (j + 1) =
        ⟨some (.prB r l), p, tp, Function.update hd r 0, out ++ List.replicate j true⟩ := by
  intro j
  induction j with
  | zero =>
    intro out _
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero, step_some]
    have hb : tp r (Function.update hd r ((0 : ℕ) - 1 : ℤ) r) = none := by
      simp [htp, ones_neg]
    simp only [tr, hb, Option.isSome_none, Bool.false_eq_true, if_false]
    rw [apply_act]
    simp [wrT, moveInputPos_zero]
  | succ j ih =>
    intro out hj
    rw [MultiTapeTM.runFrom_succ_eq_step, step_some]
    have hb : tp r (Function.update hd r (((j + 1 : ℕ) : ℤ) - 1) r) = some true := by
      simp only [Function.update_self, htp]
      exact ones_lt (by omega) (by omega)
    simp only [tr, hb, Option.isSome_some, if_true]
    rw [apply_act]
    simp only [wrT, Function.update_eq_self, moveInputPos_zero, Function.update_idem,
      Function.update_self]
    rw [show (((j + 1 : ℕ) : ℤ) - 1 + ((SignType.neg : SignType) : ℤ)) = (j : ℤ) - 1 by
      simp [SignType.cast]; omega]
    rw [ih _ (by omega)]
    simp [List.replicate_succ', ← List.replicate_succ]

/-- The right walk of a print: in `prB r l`, from head `m - d` over `1ᵐ`, the machine walks
right to the blank cell `m` in `d + 1` steps and resumes at label `l`.

**Proof sketch.** Induction on `d`: at cell `m` the cell is blank and the machine resumes;
at cell `m - d - 1 < m` the cell holds `1` and the head moves right. -/
theorem back_walk (r : Fin R) (l : Λ) (p : Fin (x.length + 2)) (tp : Fin R → ℤ → Option Bool)
    (hd : Fin R → ℤ) (m : ℕ) (htp : tp r = ones m) (out : List Bool) :
    ∀ d : ℕ, d ≤ m →
      (toTM P l₀).tm.runFrom (⟨some (.prB r l), p, tp,
        Function.update hd r (((m - d : ℕ) : ℤ)), out⟩ : Cfg R Bool (TSt R Λ) x) (d + 1) =
        ⟨some (.main l), p, tp, Function.update hd r (m : ℤ), out⟩ := by
  intro d
  induction d with
  | zero =>
    intro _
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero, step_some]
    have hb : tp r (Function.update hd r (((m - 0 : ℕ) : ℤ)) r) = none := by
      simp [htp, ones_ge]
    simp only [tr, hb, Option.isSome_none, Bool.false_eq_true, if_false]
    rw [apply_ctl]
    simp [moveInputPos_zero]
  | succ d ih =>
    intro hd'
    rw [MultiTapeTM.runFrom_succ_eq_step, step_some]
    have hb : tp r (Function.update hd r (((m - (d + 1) : ℕ) : ℤ)) r) = some true := by
      simp only [Function.update_self, htp]
      exact ones_lt (by omega) (by omega)
    simp only [tr, hb, Option.isSome_some, if_true]
    rw [apply_act]
    simp only [wrT, Function.update_eq_self, moveInputPos_zero, Function.update_idem,
      Function.update_self, Option.toList_none, List.append_nil]
    rw [show (((m - (d + 1) : ℕ) : ℤ) + ((SignType.pos : SignType) : ℤ)) =
      (((m - d : ℕ) : ℤ)) by simp [SignType.cast]; omega]
    exact ih (by omega)

/-! ## Simulation of one step -/

omit [Fintype Λ] [DecidableEq Λ] in
/-- Updating one register tape is the tape vector of the updated registers. -/
theorem tapes_update (ρ : Fin R → ℕ) (t : Fin R) (m : ℕ) :
    Function.update (fun r => ones (ρ r)) t (ones m) =
      fun r => ones (Function.update ρ t m r) := by
  funext i
  by_cases hi : i = t
  · subst hi; simp
  · simp [hi]

omit [Fintype Λ] [DecidableEq Λ] in
/-- Updating one head is the head vector of the updated registers. -/
theorem heads_update (ρ : Fin R → ℕ) (t : Fin R) (m : ℕ) :
    Function.update (fun r => ((ρ r : ℕ) : ℤ)) t (m : ℤ) =
      fun r => ((Function.update ρ t m r : ℕ) : ℤ) := by
  funext i
  by_cases hi : i = t
  · subst hi; simp
  · simp [hi]

omit [Fintype Λ] [DecidableEq Λ] in
/-- The input position of `enc` when the reading position is within the input. -/
theorem enc_inputPos (s : St R Λ) (h : s.pos ≤ x.length) :
    ((enc x s).inputPos : ℕ) = s.pos + 1 := by
  simp [enc]; omega

omit [Fintype Λ] [DecidableEq Λ] in
/-- The symbol read in `enc`. -/
theorem enc_inputSymbol (s : St R Λ) (h : s.pos ≤ x.length) :
    (enc x s).inputSymbol = x[s.pos]? :=
  FinTM.inputSymbol_at _ s.pos h (enc_inputPos x s h)

/-- **One abstract step is at most `2B + 3` machine steps**, when every register is at most
`B` and the reading position is within the input.

**Proof sketch.** Case analysis on the instruction.  Jumps, prints of a bit, increments and
reads are one machine step (an increment writes `1` on the blank cell under the head and
steps right); decrements and zero tests step left onto the last cell of the register and
then act on what they read (two steps); printing a register of value `v` steps left and
walks left over its `v` cells emitting `1`s and back right (`print_walk`, `back_walk`),
`2v + 3` steps. -/
theorem sim_step (s : St R Λ) (l : Λ) (hl : s.lbl = some l) (hp : s.pos ≤ x.length) (B : ℕ)
    (hB : ∀ r, s.regs r ≤ B) :
    ∃ t ≤ 2 * B + 3, (toTM P l₀).tm.runFrom (enc x s) t = enc x (step P x s) := by
  obtain ⟨lbl, ρ, pos, out⟩ := s
  simp only at hl hp hB
  subst hl
  have hsym := enc_inputSymbol x ⟨some l, ρ, pos, out⟩ hp
  set ip : Fin (x.length + 2) := ⟨min (pos + 1) (x.length + 1), by omega⟩ with hip
  have henc : enc x ⟨some l, ρ, pos, out⟩ =
      (⟨some (.main l), ip, fun r => ones (ρ r), fun r => (ρ r : ℤ), out⟩ :
        Cfg R Bool (TSt R Λ) x) := rfl
  have hone : ∀ c : Cfg R Bool (TSt R Λ) x, (toTM P l₀).tm.runFrom c 1 = (toTM P l₀).tm.step c :=
    fun c => rfl
  rw [henc] at hsym ⊢
  cases hP : P l with
  | halt =>
    refine ⟨1, by omega, ?_⟩
    rw [hone, step_some]
    simp only [tr, hP]
    rw [apply_ctl, moveInputPos_zero]
    simp [step, hP, enc, hip]
  | goto l' =>
    refine ⟨1, by omega, ?_⟩
    rw [hone, step_some]
    simp only [tr, hP]
    rw [apply_ctl, moveInputPos_zero]
    simp [step, hP, enc, hip]
  | out b l' =>
    refine ⟨1, by omega, ?_⟩
    rw [hone, step_some]
    simp only [tr, hP]
    rw [apply_ctl, moveInputPos_zero]
    simp [step, hP, enc, hip]
  | inc r l' =>
    refine ⟨1, by omega, ?_⟩
    rw [hone, step_some]
    simp only [tr, hP]
    rw [apply_act, moveInputPos_zero]
    simp only [step, hP, enc, Option.map_some, wrT, update_ones_succ, Option.toList_none,
      List.append_nil]
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    · exact tapes_update ρ r (ρ r + 1)
    · rw [show ((ρ r : ℕ) : ℤ) + ((SignType.pos : SignType) : ℤ) = ((ρ r + 1 : ℕ) : ℤ) by
        simp [SignType.cast]]
      exact heads_update ρ r (ρ r + 1)
  | dec r l' =>
    refine ⟨2, by omega, ?_⟩
    rw [show (2 : ℕ) = 1 + 1 from rfl, MultiTapeTM.runFrom_add, hone (MultiTapeTM.runFrom _ 1),
      hone, step_some]
    simp only [tr, hP]
    rw [apply_act, moveInputPos_zero, step_some]
    simp only [tr, wrT, Function.update_self, Function.update_eq_self, Option.toList_none,
      List.append_nil]
    rcases Nat.eq_zero_or_pos (ρ r) with h0 | h0
    · have hb : ones (ρ r) ((ρ r : ℤ) + ((SignType.neg : SignType) : ℤ)) = none :=
        ones_neg (by simp [SignType.cast]; omega)
      simp only [hb, Option.isSome_none, Bool.false_eq_true, if_false]
      rw [apply_act, moveInputPos_zero]
      simp only [step, hP, enc, Option.map_some, wrT, Function.update_eq_self,
        Function.update_idem, Function.update_self, Option.toList_none, List.append_nil]
      refine Cfg.ext rfl rfl ?_ ?_ rfl
      · funext i
        by_cases hi : i = r
        · subst hi; simp [h0]
        · simp [hi]
      · funext i
        by_cases hi : i = r
        · subst hi; simp [h0, SignType.cast]
        · simp [hi]
    · obtain ⟨v, hv⟩ : ∃ v, ρ r = v + 1 := ⟨ρ r - 1, by omega⟩
      have hb : ones (ρ r) ((ρ r : ℤ) + ((SignType.neg : SignType) : ℤ)) = some true :=
        ones_lt (by simp [SignType.cast]; omega) (by simp [SignType.cast])
      simp only [hb, Option.isSome_some, if_true]
      rw [apply_act, moveInputPos_zero]
      simp only [step, hP, enc, Option.map_some, wrT, Function.update_self,
        Function.update_idem, Option.toList_none, List.append_nil]
      have hz : ((ρ r : ℤ) + ((SignType.neg : SignType) : ℤ)) = ((v : ℕ) : ℤ) := by
        simp [SignType.cast]; omega
      refine Cfg.ext rfl rfl ?_ ?_ rfl
      · rw [hz, hv, update_ones_pred, show v + 1 - 1 = v by omega]
        exact tapes_update ρ r v
      · rw [hz, hv, show v + 1 - 1 = v by omega,
          show ((v : ℕ) : ℤ) + ((0 : SignType) : ℤ) = ((v : ℕ) : ℤ) by simp]
        exact heads_update ρ r v
  | jz r l0 l1 =>
    refine ⟨2, by omega, ?_⟩
    rw [show (2 : ℕ) = 1 + 1 from rfl, MultiTapeTM.runFrom_add, hone (MultiTapeTM.runFrom _ 1),
      hone, step_some]
    simp only [tr, hP]
    rw [apply_act, moveInputPos_zero, step_some]
    simp only [tr, wrT, Function.update_self, Function.update_eq_self, Option.toList_none,
      List.append_nil]
    have hback : ∀ (q : TSt R Λ), (act r 0 none .pos none (some q)).apply
        (⟨some (TSt.jzB r l0 l1), ip, fun r => ones (ρ r),
          Function.update (fun r => ((ρ r : ℕ) : ℤ)) r ((ρ r : ℤ) + ((SignType.neg : SignType) :
              ℤ)),
          out⟩ : Cfg R Bool (TSt R Λ) x) =
        ⟨some q, ip, fun r => ones (ρ r), fun r => (ρ r : ℤ), out⟩ := by
      intro q
      rw [apply_act, moveInputPos_zero]
      refine Cfg.ext rfl rfl ?_ ?_ (by simp)
      · simp [wrT]
      · funext i
        by_cases hi : i = r
        · subst hi; simp [SignType.cast]
        · simp [hi]
    rcases Nat.eq_zero_or_pos (ρ r) with h0 | h0
    · have hb : ones (ρ r) ((ρ r : ℤ) + ((SignType.neg : SignType) : ℤ)) = none :=
        ones_neg (by simp [SignType.cast]; omega)
      simp only [hb, Option.isSome_none, Bool.false_eq_true, if_false]
      rw [hback]
      simp [step, hP, enc, h0, hip]
    · have hb : ones (ρ r) ((ρ r : ℤ) + ((SignType.neg : SignType) : ℤ)) = some true :=
        ones_lt (by simp [SignType.cast]; omega) (by simp [SignType.cast])
      simp only [hb, Option.isSome_some, if_true]
      rw [hback]
      simp [step, hP, enc, show ρ r ≠ 0 by omega, hip]
  | pr r l' =>
    refine ⟨1 + (ρ r + 1) + (ρ r + 1), by have := hB r; omega, ?_⟩
    have h1 : (toTM P l₀).tm.runFrom (⟨some (.main l), ip, fun r => ones (ρ r),
        fun r => (ρ r : ℤ), out⟩ : Cfg R Bool (TSt R Λ) x) 1 =
        ⟨some (.prW r l'), ip, fun r => ones (ρ r),
          Function.update (fun r => ((ρ r : ℕ) : ℤ)) r (((ρ r : ℕ) : ℤ) - 1), out⟩ := by
      rw [hone, step_some]
      simp only [tr, hP]
      rw [apply_act, moveInputPos_zero]
      simp only [wrT, Function.update_eq_self, Option.toList_none, List.append_nil]
      rw [show ((ρ r : ℤ) + ((SignType.neg : SignType) : ℤ)) = ((ρ r : ℕ) : ℤ) - 1 by
        simp [SignType.cast]; omega]
      rfl
    have h2 := print_walk P x l₀ r l' ip (fun r => ones (ρ r)) (fun r => (ρ r : ℤ)) (ρ r) rfl
      (ρ r) out le_rfl
    have h3 := back_walk P x l₀ r l' ip (fun r => ones (ρ r)) (fun r => (ρ r : ℤ)) (ρ r) rfl
      (out ++ List.replicate (ρ r) true) (ρ r) le_rfl
    rw [show (((ρ r - ρ r : ℕ) : ℤ)) = 0 by simp] at h3
    rw [MultiTapeTM.runFrom_add _ (1 + (ρ r + 1)) (ρ r + 1),
      MultiTapeTM.runFrom_add _ 1 (ρ r + 1), h1]
    erw [h2, h3]
    simp [step, hP, enc, hip]
  | rd le lf lt =>
    refine ⟨1, by omega, ?_⟩
    rw [hone, step_some, hsym]
    simp only [tr, hP]
    cases hx : x[pos]? with
    | none =>
      simp only
      rw [apply_ctl, moveInputPos_zero]
      simp [step, hP, hx, enc, hip]
    | some b =>
      have hlt : pos < x.length := (List.getElem?_eq_some_iff.mp hx).1
      have hmv : moveInputPos ip .pos =
          (⟨min (pos + 1 + 1) (x.length + 1), by omega⟩ : Fin (x.length + 2)) := by
        rw [moveInputPos_pos_of_ne_right _ (by simp [hip]; omega)]
        apply Fin.ext; simp [hip]; omega
      cases b <;> (simp only; rw [apply_ctl, hmv]; simp [step, hP, hx, enc])

end CounterProg

end Complexity

```


## ===== TCSlib/Complexity/TuringMachine/CounterProgRun.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Tactic.Linarith
import TCSlib.Complexity.TuringMachine.CounterProg

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Reasoning about counter programs

Hoare-style run lemmas for the counter programs of `TCSlib.Complexity.TuringMachine.CounterProg`: the
relation `Complexity.CounterProg.Goes` ("from this label and these registers the program
reaches that label and those registers, printing `e`, within `b` steps"), its
composition, one lemma per instruction, the count-down loop, straight-line *templates*
(lists of print-a-bit / print-a-register micro-operations, the shape in which the emitter
of [AB09, Remark 6.7] prints a gadget of the circuit), and *linear expressions* — sums of
registers plus a constant, printed in unary by a template.

## Main definitions

* `Complexity.CounterProg.Goes` — the run relation.
* `Complexity.CounterProg.MOp`, `Complexity.CounterProg.tmplInstr` — template micro-operations
  and the instruction executing one.
* `Complexity.CounterProg.LinE` — linear expressions in the registers.

## Main results

* `Complexity.CounterProg.sim_run` — a run of `t` abstract steps is at most `t (2B + 3)`
  machine steps.
* `Complexity.CounterProg.exists_tm` — a halting abstract run of `t` steps is a machine
  computation within `t (2t + 3)` steps.
* `Complexity.CounterProg.Goes.trans` — composition.
* `Complexity.CounterProg.goes_loop` — the count-down loop.
* `Complexity.CounterProg.goes_tmpl` — running a template prints its micro-operations.
* `Complexity.CounterProg.flatMap_exec_linOps` — a linear expression prints its value in
  unary.
* `Complexity.CounterProg.run_pos_le`, `run_out`, `run_init_out_le` — the input position
  and the output grow boundedly along a run.

The consequence for polynomial time (`Complexity.CounterProg.polyTimeComputable`,
`polyTimeComputable_of_goes`) is in `TCSlib.Complexity.ClassNP.CounterProgPolyTime`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§6.2, Remark 6.7.)
-/

namespace Complexity

namespace CounterProg

variable {R : ℕ} {Λ : Type} (P : Λ → Instr R Λ) (x : List Bool)

/-! ## The run relation -/

/-- From label `l` with registers `ρ`, having read `p` input symbols, the program reaches the
label `l'` (`none`: it halts) with registers `ρ'` and `p'` symbols read, printing `e`, within
`b` steps (whatever was printed before). -/
def Goes (l : Λ) (ρ : Fin R → ℕ) (p : ℕ) (l' : Option Λ) (ρ' : Fin R → ℕ) (p' : ℕ)
    (e : List Bool) (b : ℕ) : Prop :=
  ∀ o, ∃ t ≤ b, run P x ⟨some l, ρ, p, o⟩ t = ⟨l', ρ', p', o ++ e⟩

variable {P x}

/-- Runs compose: bounds add and outputs concatenate. -/
theorem Goes.trans {l l' : Λ} {l'' : Option Λ} {ρ ρ' ρ'' : Fin R → ℕ} {p p' p'' : ℕ}
    {e e' : List Bool} {b b' : ℕ} (h : Goes P x l ρ p (some l') ρ' p' e b)
    (h' : Goes P x l' ρ' p' l'' ρ'' p'' e' b') : Goes P x l ρ p l'' ρ'' p'' (e ++ e') (b + b') := by
  intro o
  obtain ⟨t, ht, h1⟩ := h o
  obtain ⟨t', ht', h2⟩ := h' (o ++ e)
  exact ⟨t + t', by omega, by rw [run_add, h1, h2, List.append_assoc]⟩

/-- A bound can be weakened. -/
theorem Goes.mono {l : Λ} {l' : Option Λ} {ρ ρ' : Fin R → ℕ} {p p' : ℕ} {e : List Bool}
    {b b' : ℕ} (h : Goes P x l ρ p l' ρ' p' e b) (hb : b ≤ b') : Goes P x l ρ p l' ρ' p' e b' :=
  fun o => let ⟨t, ht, h1⟩ := h o; ⟨t, by omega, h1⟩

/-- The registers and position can be rewritten along equalities. -/
theorem Goes.congr {l : Λ} {l' : Option Λ} {ρ ρ' σ σ' : Fin R → ℕ} {p p' q q' : ℕ}
    {e e' : List Bool} {b b' : ℕ} (h : Goes P x l ρ p l' ρ' p' e b) (h1 : ρ = σ) (h2 : ρ' = σ')
    (h3 : p = q) (h4 : p' = q') (h5 : e = e') (h6 : b ≤ b') : Goes P x l σ q l' σ' q' e' b' := by
  subst h1 h2 h3 h4 h5; exact h.mono h6

/-- One step of a running state. -/
theorem goes_of_step {l : Λ} {ρ : Fin R → ℕ} {p : ℕ} {l' : Option Λ} {ρ' : Fin R → ℕ} {p' : ℕ}
    {e : List Bool} (h : ∀ o, step P x ⟨some l, ρ, p, o⟩ = ⟨l', ρ', p', o ++ e⟩) :
    Goes P x l ρ p l' ρ' p' e 1 :=
  fun o => ⟨1, le_rfl, h o⟩

/-! ## One instruction -/

section Instructions

variable {l l' : Λ} {ρ : Fin R → ℕ} {p : ℕ}

/-- A `halt` instruction stops the program in one step. -/
theorem goes_halt (h : P l = .halt) : Goes P x l ρ p none ρ p [] 1 :=
  goes_of_step fun o => by simp [step, h]

/-- A `goto` instruction jumps in one step. -/
theorem goes_goto (h : P l = .goto l') : Goes P x l ρ p (some l') ρ p [] 1 :=
  goes_of_step fun o => by simp [step, h]

/-- An `out b` instruction prints `b` in one step. -/
theorem goes_out {b : Bool} (h : P l = .out b l') : Goes P x l ρ p (some l') ρ p [b] 1 :=
  goes_of_step fun o => by simp [step, h]

/-- An `inc r` instruction increments register `r` in one step. -/
theorem goes_inc {r : Fin R} (h : P l = .inc r l') :
    Goes P x l ρ p (some l') (Function.update ρ r (ρ r + 1)) p [] 1 :=
  goes_of_step fun o => by simp [step, h]

/-- A `dec r` instruction decrements register `r` (saturating) in one step. -/
theorem goes_dec {r : Fin R} (h : P l = .dec r l') :
    Goes P x l ρ p (some l') (Function.update ρ r (ρ r - 1)) p [] 1 :=
  goes_of_step fun o => by simp [step, h]

/-- A zero test on a register holding `0` takes the `zero` branch. -/
theorem goes_jz_zero {r : Fin R} {l0 l1 : Λ} (h : P l = .jz r l0 l1) (hr : ρ r = 0) :
    Goes P x l ρ p (some l0) ρ p [] 1 :=
  goes_of_step fun o => by simp [step, h, hr]

/-- A zero test on a register not holding `0` takes the other branch. -/
theorem goes_jz_pos {r : Fin R} {l0 l1 : Λ} (h : P l = .jz r l0 l1) (hr : ρ r ≠ 0) :
    Goes P x l ρ p (some l1) ρ p [] 1 :=
  goes_of_step fun o => by simp [step, h, hr]

/-- A `pr r` instruction prints the value of register `r` in unary in one step. -/
theorem goes_pr {r : Fin R} (h : P l = .pr r l') :
    Goes P x l ρ p (some l') ρ p (List.replicate (ρ r) true) 1 :=
  goes_of_step fun o => by simp [step, h]

/-- Reading at the end of the input takes the end branch, consuming nothing. -/
theorem goes_rd_end {le lf lt : Λ} (h : P l = .rd le lf lt) (hx : x[p]? = none) :
    Goes P x l ρ p (some le) ρ p [] 1 :=
  goes_of_step fun o => by simp [step, h, hx]

/-- Reading a `0` takes the `0` branch and consumes it. -/
theorem goes_rd_false {le lf lt : Λ} (h : P l = .rd le lf lt) (hx : x[p]? = some false) :
    Goes P x l ρ p (some lf) ρ (p + 1) [] 1 :=
  goes_of_step fun o => by simp [step, h, hx]

/-- Reading a `1` takes the `1` branch and consumes it. -/
theorem goes_rd_true {le lf lt : Λ} (h : P l = .rd le lf lt) (hx : x[p]? = some true) :
    Goes P x l ρ p (some lt) ρ (p + 1) [] 1 :=
  goes_of_step fun o => by simp [step, h, hx]

end Instructions

/-! ## The count-down loop -/

/-- **The count-down loop.**  At `head` the program tests register `r` (exit when it is `0`),
otherwise decrements it and runs the body, which returns to `head`.  If iteration `j < K`
of the body takes the registers `st j` (with `r` already decremented to `K - j - 1`) to
`st (j + 1)` printing `em j`, and `st j r = K - j`, then the loop takes `st 0` to `st K`
printing `em 0 ++ … ++ em (K - 1)`.

**Proof sketch.** Induction on the number of remaining iterations. -/
theorem goes_loop {head dl body exit : Λ} {r : Fin R} (hh : P head = .jz r exit dl)
    (hd : P dl = .dec r body) (K : ℕ) (st : ℕ → Fin R → ℕ) (ps : ℕ → ℕ) (em : ℕ → List Bool)
    (b : ℕ) (hr : ∀ j ≤ K, st j r = K - j)
    (hbody : ∀ j < K, Goes P x body (Function.update (st j) r (K - j - 1)) (ps j) (some head)
      (st (j + 1)) (ps (j + 1)) (em j) b) :
    Goes P x head (st 0) (ps 0) (some exit) (st K) (ps K) ((List.range K).flatMap em)
      (K * (b + 2) + 1) := by
  have key : ∀ i ≤ K, Goes P x head (st (K - i)) (ps (K - i)) (some exit) (st K) (ps K)
      (((List.range i).map (fun j => K - i + j)).flatMap em) (i * (b + 2) + 1) := by
    intro i
    induction i with
    | zero =>
      intro _
      simpa using goes_jz_zero (ρ := st K) (p := ps K) hh (by simpa using hr K le_rfl)
    | succ i ih =>
      intro hi
      have h1 : st (K - (i + 1)) r ≠ 0 := by rw [hr _ (by omega)]; omega
      have hj : K - (i + 1) + 1 = K - i := by omega
      have hb := hbody (K - (i + 1)) (by omega)
      rw [hj, show K - (K - (i + 1)) - 1 = i by omega] at hb
      have hdec : Function.update (st (K - (i + 1))) r (st (K - (i + 1)) r - 1) =
          Function.update (st (K - (i + 1))) r i := by
        rw [hr _ (by omega)]; congr 1; omega
      have := (((goes_jz_pos (p := ps (K - (i + 1))) hh h1).trans
        (goes_dec (p := ps (K - (i + 1))) hd)).trans
          (hdec ▸ hb)).trans (ih (by omega))
      refine this.congr rfl rfl rfl rfl ?_ (by nlinarith)
      rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.flatMap_cons]
      simp only [List.nil_append, Nat.add_zero]
      congr 2
      apply List.map_congr_left
      intro j _
      simp only [Function.comp]; omega
  simpa using key K le_rfl

/-! ## Templates -/

/-- A template micro-operation: print a bit, or print a register in unary. -/
inductive MOp (R : ℕ) where
  /-- Print the bit `b`. -/
  | out (b : Bool)
  /-- Print register `r` in unary. -/
  | pr (r : Fin R)

/-- What a micro-operation prints, with registers `ρ`. -/
def MOp.exec (ρ : Fin R → ℕ) : MOp R → List Bool
  | .out b => [b]
  | .pr r => List.replicate (ρ r) true

/-- The instruction at position `i` of a template run at labels `lab 0, lab 1, …`, continuing
at `next` after the last micro-operation. -/
def tmplInstr (tm : List (MOp R)) (lab : ℕ → Λ) (next : Λ) (i : ℕ) : Instr R Λ :=
  match tm[i]? with
  | some (.out b) => .out b (lab (i + 1))
  | some (.pr r) => .pr r (lab (i + 1))
  | none => .goto next

/-- **Running a template**: if the labels `lab i` hold the template's instructions, the
program prints the micro-operations' outputs in `|tm| + 1` steps and continues at `next`,
registers unchanged.

**Proof sketch.** Induction on the number of remaining micro-operations: each is one
`out` or `pr` step to the next label, and past the end a `goto` reaches `next`. -/
theorem goes_tmpl (tm : List (MOp R)) (lab : ℕ → Λ) (next : Λ)
    (hP : ∀ i ≤ tm.length, P (lab i) = tmplInstr tm lab next i) (ρ : Fin R → ℕ) (p : ℕ) :
    Goes P x (lab 0) ρ p (some next) ρ p (tm.flatMap (MOp.exec ρ)) (tm.length + 1) := by
  have key : ∀ d i, i + d = tm.length →
      Goes P x (lab i) ρ p (some next) ρ p ((tm.drop i).flatMap (MOp.exec ρ)) (d + 1) := by
    intro d
    induction d with
    | zero =>
      intro i hi
      have h := hP i (by omega)
      rw [tmplInstr, List.getElem?_eq_none (by omega)] at h
      simpa [List.drop_eq_nil_of_le (show tm.length ≤ i by omega)] using goes_goto (ρ := ρ) (p :=
          p) h
    | succ d ih =>
      intro i hi
      have hlt : i < tm.length := by omega
      have h := hP i (by omega)
      rw [tmplInstr, List.getElem?_eq_getElem hlt] at h
      rw [List.drop_eq_getElem_cons hlt, List.flatMap_cons]
      have hrest := ih (i + 1) (by omega)
      cases hop : tm[i] with
      | out b =>
        rw [hop] at h
        exact ((goes_out h).trans hrest).mono (by omega)
      | pr r =>
        rw [hop] at h
        exact ((goes_pr h).trans hrest).mono (by omega)
  simpa using key tm.length 0 (by omega)

/-! ## Linear expressions -/

/-- A linear expression in the registers: a list of registers (with multiplicity) and a
constant; its value is the sum of the listed registers plus the constant. -/
abbrev LinE (R : ℕ) := List (Fin R) × ℕ

/-- The value of a linear expression. -/
def LinE.val (ρ : Fin R → ℕ) (e : LinE R) : ℕ := (e.1.map ρ).sum + e.2

/-- The micro-operations printing a linear expression in unary. -/
def linOps (e : LinE R) : List (MOp R) := e.1.map .pr ++ List.replicate e.2 (.out true)

/-- **A linear expression prints its value in unary.** -/
theorem flatMap_exec_linOps (ρ : Fin R → ℕ) (e : LinE R) :
    (linOps e).flatMap (MOp.exec ρ) = List.replicate (e.val ρ) true := by
  obtain ⟨rs, c⟩ := e
  simp only [linOps, LinE.val, List.flatMap_append]
  have h1 : (rs.map MOp.pr).flatMap (MOp.exec ρ) = List.replicate (rs.map ρ).sum true := by
    induction rs with
    | nil => rfl
    | cons r rs ih =>
      simp only [List.map_cons, List.flatMap_cons, ih, List.sum_cons, MOp.exec,
        List.replicate_add]
  have h2 : (List.replicate c (MOp.out true : MOp R)).flatMap (MOp.exec ρ) =
      List.replicate c true := by
    induction c with
    | zero => rfl
    | succ c ih =>
      simp only [List.replicate_succ, List.flatMap_cons, ih, MOp.exec, List.singleton_append]
  rw [h1, h2, List.replicate_add]

/-- The micro-operations printing a fixed bit string. -/
def bitsOps (l : List Bool) : List (MOp R) := l.map .out

/-- A fixed bit string prints itself. -/
theorem flatMap_exec_bitsOps (ρ : Fin R → ℕ) (l : List Bool) :
    (bitsOps l : List (MOp R)).flatMap (MOp.exec ρ) = l := by
  induction l with
  | nil => rfl
  | cons b l ih => simp only [bitsOps, List.map_cons, List.flatMap_cons,
      MOp.exec] at ih ⊢; rw [ih]; rfl

section SimRun

open Turing Turing.UnaryTape

variable (P : Λ → Instr R Λ) (x : List Bool) [Fintype Λ] [DecidableEq Λ] (l₀ : Λ)

/-! ## Simulation of a run -/

/-- **A run of `t` abstract steps is at most `t (2B + 3)` machine steps** when all registers
stay below `B` (it suffices that they start `t` below it).

**Proof sketch.** Induction on `t`: a halted state is a halted configuration; otherwise
simulate one step (`sim_step`) and continue, registers having grown by at most one. -/
theorem sim_run (B : ℕ) : ∀ (t : ℕ) (s : St R Λ), s.pos ≤ x.length → (∀ r, s.regs r + t ≤ B) →
    ∃ t' ≤ t * (2 * B + 3), (toTM P l₀).tm.runFrom (enc x s) t' = enc x (run P x s t) := by
  intro t
  induction t with
  | zero => intro s _ _; exact ⟨0, by simp, rfl⟩
  | succ t ih =>
    intro s hp hB
    cases hl : s.lbl with
    | none => exact ⟨0, by omega, by rw [run_of_halted P x s hl]; rfl⟩
    | some l =>
      obtain ⟨t₁, ht₁, h₁⟩ := sim_step P x l₀ s l hl hp B (fun r => by have := hB r; omega)
      obtain ⟨t₂, ht₂, h₂⟩ := ih (step P x s) (step_pos_le P x s hp)
        (fun r => by have := hB r; have := step_regs_le P x s r; omega)
      refine ⟨t₁ + t₂, by nlinarith, ?_⟩
      rw [MultiTapeTM.runFrom_add, h₁, h₂, run_succ]

/-- **A counter program is a Turing machine**: if the program halts on `x` after `t`
abstract steps, its machine computes the program's output within `t (2t + 3)` steps.

**Proof sketch.** The machine's initial configuration encodes the initial abstract state
(blank tapes are the registers `0`); registers stay below `t` during the run
(`run_regs_le`), so `sim_run` with `B = t` applies, and the halted configuration is
absorbing. -/
theorem exists_tm (x : List Bool) (t : ℕ) (h : (run P x (init l₀) t).lbl = none) :
    (toTM P l₀).ComputesInTime x (run P x (init l₀) t).out (t * (2 * t + 3)) := by
  have hinit : (toTM P l₀).tm.initCfg x = enc x (init l₀ : St R Λ) := by
    simp only [MultiTapeTM.initCfg, Cfg.init, enc, init]
    refine Cfg.ext rfl ?_ ?_ ?_ rfl
    · apply Fin.ext; simp
    · funext r; simp [ones_zero]
    · funext r; simp
  obtain ⟨t', ht', h'⟩ := sim_run P x l₀ t t (init l₀) (by simp [init])
    (fun r => by simp [init])
  have hhalt : ((toTM P l₀).tm.runFrom ((toTM P l₀).tm.initCfg x) t').state = none := by
    rw [hinit, h']; simp [enc, h]
  refine (FinTM.computesInTime_iff _ _ _ _).mpr ⟨?_, ?_⟩
  · have := (toTM P l₀).tm.runFrom_add ((toTM P l₀).tm.initCfg x) t' (t * (2 * t + 3) - t')
    rw [Nat.add_sub_of_le ht', MultiTapeTM.runFrom_of_halt _ hhalt] at this
    rw [this]; exact hhalt
  · have := (toTM P l₀).tm.runFrom_add ((toTM P l₀).tm.initCfg x) t' (t * (2 * t + 3) - t')
    rw [Nat.add_sub_of_le ht', MultiTapeTM.runFrom_of_halt _ hhalt] at this
    rw [this, hinit, h']; rfl

end SimRun

/-! ## Growth of positions and outputs -/

section Growth

variable (P x)

/-- The input position grows by at most one per step. -/
theorem run_pos_le (s : St R Λ) (t : ℕ) : (run P x s t).pos ≤ s.pos + t := by
  induction t generalizing s with
  | zero => simp [run_zero]
  | succ t ih =>
    rw [run_succ]
    have := ih (step P x s)
    have : (step P x s).pos ≤ s.pos + 1 := by
      unfold step; split
      · omega
      · split <;> (try split) <;> simp
    omega

/-- A step appends to the output. -/
theorem step_out (s : St R Λ) : ∃ e, (step P x s).out = s.out ++ e := by
  unfold step; split
  · exact ⟨[], by simp⟩
  · split <;> (try split) <;> simp

/-- A run appends to the output. -/
theorem run_out (s : St R Λ) (t : ℕ) : ∃ e, (run P x s t).out = s.out ++ e := by
  induction t generalizing s with
  | zero => exact ⟨[], by simp [run_zero]⟩
  | succ t ih =>
    rw [run_succ]
    obtain ⟨e, he⟩ := step_out P x s
    obtain ⟨e', he'⟩ := ih (step P x s)
    exact ⟨e ++ e', by rw [he', he, List.append_assoc]⟩

/-- A step prints at most one more than the largest register. -/
theorem step_out_le (s : St R Λ) (K : ℕ) (h : ∀ r, s.regs r ≤ K) :
    (step P x s).out.length ≤ s.out.length + K + 1 := by
  unfold step; split
  · omega
  · split <;> (try split) <;> simp <;> (try have := h ‹_›) <;> omega

/-- From the start, `t` steps print at most `t (t + 1)` bits. -/
theorem run_init_out_le (l₀ : Λ) (t : ℕ) : (run P x (init l₀) t).out.length ≤ t * (t + 1) := by
  induction t with
  | zero => simp [run_zero, init]
  | succ t ih =>
    rw [run_add, show run P x (run P x (init l₀) t) 1 = step P x (run P x (init l₀) t) from rfl]
    have := step_out_le P x (run P x (init l₀) t) t (fun r => by
      have := run_regs_le P x (init l₀) r t; simpa [init] using this)
    nlinarith

end Growth

end CounterProg

end Complexity

```


## ===== TCSlib/Complexity/ClassNP/CounterProgPolyTime.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Tactic.Ring
import TCSlib.Complexity.ClassNP.PolyTime
import TCSlib.Complexity.TuringMachine.CounterProgRun

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Counter programs in polynomial time

A counter program (`TCSlib.Complexity.TuringMachine.CounterProg`) that halts within
polynomially many abstract steps computes a polynomial-time function: its compiled
machine simulates `t` abstract steps within `t (2t + 3)` machine steps
(`Complexity.CounterProg.exists_tm`). This is how the emitters of [AB09, Remark 6.7] are
shown to run in polynomial time.

## Main results

* `Complexity.CounterProg.polyTimeComputable` — polynomially many abstract steps give a
  polynomial-time computable function.
* `Complexity.CounterProg.polyTimeComputable_of_goes` — the same, in the `Goes` form.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§6.2, Remark 6.7.)
-/

namespace Complexity

namespace CounterProg

variable {R : ℕ} {Λ : Type}

section SimRun

variable (P : Λ → Instr R Λ) [Fintype Λ] [DecidableEq Λ] (l₀ : Λ)

/-- **Counter programs running in polynomially many steps compute polynomial-time
functions**: if on every input `x` the program halts within `C (|x| + 1)^c` abstract steps
with output `f x`, then `f` is polynomial-time computable.

**Proof sketch.** `exists_tm` gives the machine, within `t (2t + 3) ≤ (2C² + 3C) (n + 1)^{2c}`
steps. -/
theorem polyTimeComputable (f : List Bool → List Bool) (C c : ℕ)
    (h : ∀ x : List Bool, ∃ t ≤ C * (x.length + 1) ^ c,
      (run P x (init l₀) t).lbl = none ∧ (run P x (init l₀) t).out = f x) :
    PolyTimeComputable f := by
  refine ⟨toTM P l₀, 2 * C * C + 3 * C, 2 * c, fun x => ?_⟩
  obtain ⟨t, ht, hl, ho⟩ := h x
  have hM := exists_tm P l₀ x t hl
  rw [ho] at hM
  refine hM.mono ?_
  show t * (2 * t + 3) ≤ (2 * C * C + 3 * C) * (x.length + 1) ^ (2 * c)
  set N := (x.length + 1) ^ c
  have hN : (x.length + 1) ^ (2 * c) = N * N := by rw [← pow_add]; ring_nf
  have h1 : 1 ≤ N := Nat.one_le_pow _ _ (by omega)
  rw [hN]
  calc t * (2 * t + 3) ≤ (C * N) * (2 * (C * N) + 3 * N) := by
        apply Nat.mul_le_mul ht; nlinarith
    _ = (2 * C * C + 3 * C) * (N * N) := by ring

end SimRun

/-! ## Halting programs are polynomial-time -/

variable [Fintype Λ] [DecidableEq Λ]

/-- **A counter program that halts within polynomially many steps computes a
polynomial-time function**: if from the start label with all registers `0` the program
halts on every `x` within `C (|x| + 1)^c` steps printing `f x`, then `f` is in FP.
(`polyTimeComputable` in the `Goes` form.) -/
theorem polyTimeComputable_of_goes (P : Λ → Instr R Λ) (l₀ : Λ) (f : List Bool → List Bool)
    (C c : ℕ) (h : ∀ x : List Bool, ∃ (ρ : Fin R → ℕ) (p : ℕ),
      Goes P x l₀ (fun _ => 0) 0 none ρ p (f x) (C * (x.length + 1) ^ c)) :
    PolyTimeComputable f := by
  refine polyTimeComputable P l₀ f C c fun x => ?_
  obtain ⟨ρ, p, hg⟩ := h x
  obtain ⟨t, ht, hrun⟩ := hg []
  exact ⟨t, ht, by simp [init, hrun], by simp [init, hrun]⟩

end CounterProg

end Complexity

```


## ===== TCSlib/Complexity/ClassNP/ExpPoly.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Tactic.Linarith
import TCSlib.Complexity.ClassNP.EXP

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Exponential-polynomial time bounds

A bound `T` is *exponential-polynomial* if `T n ≤ 2^{K(n+1)^k}` for some constants. Such
bounds are closed under sums, products, domination and polynomial reparametrization, and a
language decided within one is in `EXP = ⋃_c DTIME(2^{n^c})` [AB09, §2.6.2]. This toolkit
bounds brute-force enumerations, e.g. in `Σ₂ᵖ ⊆ EXP` (`CircuitComplexity/MeyerSigmaEXP.lean`).
It is close to, but distinct from, the numerical helper `Complexity.ExpBound`
(`C · 2^{(n+1)^c}`) of `ClassNP/EXP.lean`.

## Main definitions

* `Complexity.ExpPoly` — "bounded by `2^{K (n+1)^k}`".

## Main results

* `Complexity.ExpPoly.of_le`, `ExpPoly.add`, `ExpPoly.mul`, `ExpPoly.comp_poly`,
  `Complexity.expPoly_exp`, `Complexity.expPoly_poly` — closure properties.
* `Complexity.ExpPoly.mem_EXP` — exponential-polynomial time is `EXP`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Claim 2.4, p. 41; §2.6.2.)
-/

namespace Complexity

/-- **An exponential-polynomial bound**: `T n ≤ 2^{K (n+1)^k}` for some constants. -/
def ExpPoly (T : ℕ → ℕ) : Prop := ∃ K k : ℕ, ∀ n, T n ≤ 2 ^ (K * (n + 1) ^ k)

/-- Raising the degree of a positive base. -/
private theorem pow_mono_deg (n k k' : ℕ) (h : k ≤ k') : (n + 1) ^ k ≤ (n + 1) ^ k' :=
  Nat.pow_le_pow_right (by omega) h

/-- Exponential-polynomial bounds are closed under domination. -/
theorem ExpPoly.of_le {T T' : ℕ → ℕ} (h : ExpPoly T') (hle : ∀ n, T n ≤ T' n) : ExpPoly T := by
  obtain ⟨K, k, hK⟩ := h
  exact ⟨K, k, fun n => (hle n).trans (hK n)⟩

/-- The exponential `c · 2^{n^e}` is exponential-polynomial. -/
theorem expPoly_exp (c e : ℕ) : ExpPoly (fun n => c * 2 ^ n ^ e) := by
  refine ⟨c + 1, e, fun n => ?_⟩
  have h1 : c < 2 ^ c := Nat.lt_two_pow_self
  have h2 : n ^ e ≤ (n + 1) ^ e := Nat.pow_le_pow_left (by omega) e
  have h3 : 1 ≤ (n + 1) ^ e := Nat.one_le_pow _ _ (by omega)
  calc c * 2 ^ n ^ e ≤ 2 ^ c * 2 ^ (n + 1) ^ e :=
        Nat.mul_le_mul h1.le (Nat.pow_le_pow_right (by omega) h2)
    _ = 2 ^ (c + (n + 1) ^ e) := by rw [pow_add]
    _ ≤ 2 ^ ((c + 1) * (n + 1) ^ e) := Nat.pow_le_pow_right (by omega) (by nlinarith)

/-- A polynomial `a (n+1)^d` is exponential-polynomial. -/
theorem expPoly_poly (a d : ℕ) : ExpPoly (fun n => a * (n + 1) ^ d) := by
  refine ⟨a + d, 1, fun n => ?_⟩
  have h1 : a < 2 ^ a := Nat.lt_two_pow_self
  have h2 : (n + 1) ^ d ≤ (2 ^ (n + 1)) ^ d := Nat.pow_le_pow_left Nat.lt_two_pow_self.le d
  calc a * (n + 1) ^ d ≤ 2 ^ a * 2 ^ (d * (n + 1)) := by
        rw [pow_mul'] at *; exact Nat.mul_le_mul h1.le h2
    _ = 2 ^ (a + d * (n + 1)) := by rw [pow_add]
    _ ≤ 2 ^ ((a + d) * (n + 1) ^ 1) := Nat.pow_le_pow_right (by omega) (by rw [pow_one]; nlinarith)

/-- Exponential-polynomial bounds are closed under sums. -/
theorem ExpPoly.add {T₁ T₂ : ℕ → ℕ} (h₁ : ExpPoly T₁) (h₂ : ExpPoly T₂) :
    ExpPoly (fun n => T₁ n + T₂ n) := by
  obtain ⟨K₁, k₁, hK₁⟩ := h₁
  obtain ⟨K₂, k₂, hK₂⟩ := h₂
  refine ⟨K₁ + K₂ + 1, max k₁ k₂, fun n => ?_⟩
  set P := (n + 1) ^ max k₁ k₂
  have hp1 : (n + 1) ^ k₁ ≤ P := pow_mono_deg n _ _ (le_max_left _ _)
  have hp2 : (n + 1) ^ k₂ ≤ P := pow_mono_deg n _ _ (le_max_right _ _)
  have hP : 1 ≤ P := Nat.one_le_pow _ _ (by omega)
  have e1 : T₁ n ≤ 2 ^ (K₁ * P) :=
    (hK₁ n).trans (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ hp1))
  have e2 : T₂ n ≤ 2 ^ (K₂ * P) :=
    (hK₂ n).trans (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ hp2))
  have e3 : 2 ^ (K₁ * P) ≤ 2 ^ (K₁ * P + K₂ * P) := Nat.pow_le_pow_right (by omega) (by omega)
  have e4 : 2 ^ (K₂ * P) ≤ 2 ^ (K₁ * P + K₂ * P) := Nat.pow_le_pow_right (by omega) (by omega)
  calc T₁ n + T₂ n ≤ 2 * 2 ^ (K₁ * P + K₂ * P) := by omega
    _ = 2 ^ (K₁ * P + K₂ * P + 1) := by rw [pow_succ]; ring
    _ ≤ 2 ^ ((K₁ + K₂ + 1) * P) := Nat.pow_le_pow_right (by omega) (by nlinarith)

/-- Exponential-polynomial bounds are closed under products. -/
theorem ExpPoly.mul {T₁ T₂ : ℕ → ℕ} (h₁ : ExpPoly T₁) (h₂ : ExpPoly T₂) :
    ExpPoly (fun n => T₁ n * T₂ n) := by
  obtain ⟨K₁, k₁, hK₁⟩ := h₁
  obtain ⟨K₂, k₂, hK₂⟩ := h₂
  refine ⟨K₁ + K₂, max k₁ k₂, fun n => ?_⟩
  set P := (n + 1) ^ max k₁ k₂
  have hp1 : (n + 1) ^ k₁ ≤ P := pow_mono_deg n _ _ (le_max_left _ _)
  have hp2 : (n + 1) ^ k₂ ≤ P := pow_mono_deg n _ _ (le_max_right _ _)
  calc T₁ n * T₂ n ≤ 2 ^ (K₁ * P) * 2 ^ (K₂ * P) :=
        Nat.mul_le_mul ((hK₁ n).trans (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ hp1)))
          ((hK₂ n).trans (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ hp2)))
    _ = 2 ^ ((K₁ + K₂) * P) := by rw [← pow_add]; ring_nf

/-- **Exponential-polynomial bounds compose with polynomial arguments**: if `T` is
exponential-polynomial, so is `n ↦ T (a (n+1)^d)`. -/
theorem ExpPoly.comp_poly {T : ℕ → ℕ} (h : ExpPoly T) (a d : ℕ) :
    ExpPoly (fun n => T (a * (n + 1) ^ d)) := by
  obtain ⟨K, k, hK⟩ := h
  refine ⟨K * (a + 1) ^ k, d * k, fun n => ?_⟩
  have h1 : a * (n + 1) ^ d + 1 ≤ (a + 1) * (n + 1) ^ d := by
    have : 1 ≤ (n + 1) ^ d := Nat.one_le_pow _ _ (by omega)
    nlinarith
  calc T (a * (n + 1) ^ d) ≤ 2 ^ (K * (a * (n + 1) ^ d + 1) ^ k) := hK _
    _ ≤ 2 ^ (K * ((a + 1) * (n + 1) ^ d) ^ k) :=
        Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 k))
    _ = 2 ^ (K * (a + 1) ^ k * (n + 1) ^ (d * k)) := by rw [mul_pow, ← pow_mul]; ring_nf

/-- **Exponential-polynomial time is `EXP`** [AB09, Claim 2.4's budget normalization]:
a language decided within an exponential-polynomial bound is in `EXP`.

**Proof sketch.** For `n ≥ 2`, `K (n+1)^k ≤ n^K · n^{2k}`; small lengths are absorbed into
the constant (the argument of the private `enumExponent_bound` of `ClassNP/EXP.lean`). -/
theorem ExpPoly.mem_EXP {T : ℕ → ℕ} (h : ExpPoly T) {L : Language Bool} (hL : L ∈ DTIME T) :
    L ∈ EXP := by
  obtain ⟨K, k, hK⟩ := h
  obtain ⟨c₀, M, hM⟩ := hL
  have hexp : ∀ n : ℕ, 2 ^ (K * (n + 1) ^ k) ≤ 2 ^ (K * 2 ^ k) * 2 ^ n ^ (K + 2 * k) := by
    intro n
    by_cases hn : 2 ≤ n
    · have hK' : K ≤ n ^ K :=
        (Nat.le_of_lt (Nat.lt_two_pow_self (n := K))).trans (Nat.pow_le_pow_left hn K)
      have hn' : n + 1 ≤ n ^ 2 := by nlinarith
      have he : K * (n + 1) ^ k ≤ n ^ (K + 2 * k) := by
        calc K * (n + 1) ^ k ≤ n ^ K * (n ^ 2) ^ k :=
               Nat.mul_le_mul hK' (Nat.pow_le_pow_left hn' k)
             _ = n ^ (K + 2 * k) := by rw [← Nat.pow_mul, ← Nat.pow_add]
      exact (Nat.pow_le_pow_right (by omega) he).trans
        (Nat.le_mul_of_pos_left _ (Nat.pow_pos (by omega)))
    · have hs : (n + 1) ^ k ≤ 2 ^ k := Nat.pow_le_pow_left (by omega) k
      calc 2 ^ (K * (n + 1) ^ k) ≤ 2 ^ (K * 2 ^ k) :=
             Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left K hs)
           _ ≤ 2 ^ (K * 2 ^ k) * 2 ^ n ^ (K + 2 * k) :=
             Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))
  refine Set.mem_iUnion.mpr ⟨K + 2 * k, c₀ * 2 ^ (K * 2 ^ k), M, fun x => (hM x).mono ?_⟩
  calc c₀ * T x.length ≤ c₀ * 2 ^ (K * (x.length + 1) ^ k) := Nat.mul_le_mul_left _ (hK _)
    _ ≤ c₀ * (2 ^ (K * 2 ^ k) * 2 ^ x.length ^ (K + 2 * k)) := Nat.mul_le_mul_left _ (hexp _)
    _ = _ := by ring

end Complexity

```


## ===== TCSlib/Complexity/ClassNP/PolyTimePairing.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.ClassNP.PolyTime
import TCSlib.Complexity.TuringMachine.Build.Primitives

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Polynomial-time pairing, projections and branching

Closure facts for the function class FP (`Complexity.PolyTimeComputable`, implicit
throughout [AB09, ch. 2]) needed when a reduction must keep its input while computing
from it: constant functions, the threaded payload map, pairing of two polynomial-time
functions through `Turing.pairEncode`, the total pair projections, concatenation,
Boolean branching and length tests, and the unary length maps `x ↦ 1^|x|` and
`x ↦ 1^{C(|x|+1)^d}` (the input of a uniformity machine, [AB09, Def 6.12]). All are
assembled from the proved machine catalog of
`TCSlib.Complexity.TuringMachine.Build.Primitives`. The closure facts for the class `P`
built on them are in `TCSlib.Complexity.ClassNP.PClosure`.

## Main definitions

* `Complexity.pairMapSnd` — on `pairEncode a b`, output `pairEncode a (g b)`; malformed
  words go to `[]`.
* `Complexity.pairFstD`, `Complexity.pairSndD` — total pair projections (`[]` on
  malformed words).

## Main results

* `Complexity.polyTimeComputable_of_linear` — a linear-time machine contract gives a
  polynomial-time computable function.
* `Complexity.polyTimeComputable_const` — constant functions are polynomial-time.
* `Complexity.PolyTimeComputable.pairMapSnd` — the threaded payload map preserves
  polynomial time.
* `Complexity.PolyTimeComputable.pairEncode` — `x ↦ pairEncode (f x) (g x)` is
  polynomial-time when `f` and `g` are.
* `Complexity.polyTimeComputable_unary` — `x ↦ 1^|x|` is polynomial-time;
  `Complexity.polyTimeComputable_polyUnary` — so is `x ↦ 1^{C(|x|+1)^d}`.
* `Complexity.PolyTimeComputable.append` — FP is closed under concatenation.
* `Complexity.polyTimeComputable_pairFstD`, `polyTimeComputable_pairSndD`,
  `polyTimeComputable_pairSwap`, `polyTimeComputable_pairConcat`,
  `polyTimeComputable_prepend` — projections and rearrangements of pairs.
* `Complexity.polyTimeComputable_ite`, `polyTimeComputable_and` — Boolean branching.
* `Complexity.polyTimeComputable_lenLe`, `polyTimeComputable_lenEq` — length tests on
  pairs.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Ch. 2; §6.2, Definition 6.12.)
-/

namespace Complexity

open Turing

/-- A function computed by a finite binary machine within a linear bound `a · (n + 1)`
is polynomial-time computable. -/
theorem polyTimeComputable_of_linear {f : List Bool → List Bool}
    (h : ∃ (M : FinTM Bool) (a : ℕ), M.ComputesFunInTime f (fun n => a * (n + 1))) :
    PolyTimeComputable f := by
  obtain ⟨M, a, hM⟩ := h
  exact ⟨M, a, 1, by simpa only [Nat.pow_one] using hM⟩

/-- Every constant function `fun _ => w` is polynomial-time computable. -/
theorem polyTimeComputable_const (w : List Bool) : PolyTimeComputable (fun _ => w) :=
  polyTimeComputable_of_linear (FinTM.computesFunInTime_const w)

/-- The threaded payload map of `g`: on a pair `pairEncode a b` it outputs
`pairEncode a (g b)` (the first component is carried unchanged), and on a word that is
not a pair it outputs `[]`. -/
def pairMapSnd (g : List Bool → List Bool) (z : List Bool) : List Bool :=
  match pairDecode z with
  | some (a, b) => pairEncode a (g b)
  | none => []

/-- On a pair, the threaded payload map transforms the second component. -/
@[simp]
theorem pairMapSnd_pairEncode (g : List Bool → List Bool) (a b : List Bool) :
    pairMapSnd g (pairEncode a b) = pairEncode a (g b) := by
  simp [pairMapSnd, pairDecode_pairEncode]

/-- If `g` is polynomial-time computable, so is its threaded payload map
`Complexity.pairMapSnd g`.

**Proof sketch.** `Turing.FinTM.computesFunInTime_pairMapSnd` with the monotone
majorant `C (n+1)^c` of `g`'s bound gives a budget `K (n + 1 + C (n+1)^c)`, which is at
most `K (C + 1) (n+1)^(c+1)`. -/
theorem PolyTimeComputable.pairMapSnd {g : List Bool → List Bool}
    (hg : PolyTimeComputable g) : PolyTimeComputable (Complexity.pairMapSnd g) := by
  obtain ⟨G, C, c, hG⟩ := hg
  obtain ⟨M, K, hM⟩ := FinTM.computesFunInTime_pairMapSnd hG
    (by
      intro m n h
      exact Nat.mul_le_mul_left C (Nat.pow_le_pow_left (Nat.add_le_add_right h 1) c))
  refine ⟨M, K * (C + 1), c + 1, fun x => (hM x).mono ?_⟩
  have hn : x.length + 1 ≤ (x.length + 1) ^ (c + 1) := by
    simpa only [Nat.pow_one] using
      Nat.pow_le_pow_right (Nat.succ_pos x.length) (show 1 ≤ c + 1 by omega)
  have hc := Nat.mul_le_mul_left C
    (Nat.pow_le_pow_right (Nat.succ_pos x.length) (Nat.le_succ c))
  calc
    _ ≤ K * ((x.length + 1) ^ (c + 1) + C * (x.length + 1) ^ (c + 1)) :=
      Nat.mul_le_mul_left K (Nat.add_le_add hn hc)
    _ = _ := by ring

/-- Appending to a pair appends to its second component. -/
private lemma pairEncode_append (a b c : List Bool) :
    pairEncode a b ++ c = pairEncode a (b ++ c) := by
  simp [pairEncode, List.append_assoc]

/-- **Pairing two polynomial-time functions is polynomial-time**: if `f` and `g` are
polynomial-time computable, so is `x ↦ pairEncode (f x) (g x)`.

**Proof sketch.** Only the second component of a pair can be transformed in place
(`Complexity.pairMapSnd`), so the first component is built with an empty payload and
then retained. Duplicating `x` (`Turing.FinTM.computesFunInTime_pairDup`) and mapping
the payload gives `H x = pairEncode (f x) []`; duplicating `x` and mapping `H` gives
`s x = pairEncode x (H x)`; duplicating `s x` and mapping `g ∘ fst` gives
`t x = pairEncode (s x) (g x)`. Concatenating the components of `t x`
(`Turing.FinTM.computesFunInTime_pairConcat`) yields
`pairEncode x (pairEncode (f x) (g x))`, whose second component is the result. -/
theorem PolyTimeComputable.pairEncode {f g : List Bool → List Bool}
    (hf : PolyTimeComputable f) (hg : PolyTimeComputable g) :
    PolyTimeComputable (fun x => Turing.pairEncode (f x) (g x)) := by
  have hd := polyTimeComputable_of_linear FinTM.computesFunInTime_pairDup
  have hp := polyTimeComputable_of_linear FinTM.computesFunInTime_pairFst
  have hs := polyTimeComputable_of_linear FinTM.computesFunInTime_pairSnd
  have hc := polyTimeComputable_of_linear FinTM.computesFunInTime_pairConcat
  -- `H x = pairEncode (f x) []`, `s x = pairEncode x (H x)`, `t x = pairEncode (s x) (g x)`
  have hH := (((polyTimeComputable_const []).pairMapSnd).comp hd).comp hf
  have hS := hH.pairMapSnd.comp hd
  have hT := ((hg.comp hp).pairMapSnd.comp hd).comp hS
  -- concatenate, then project the second component
  have h := hs.comp (hc.comp hT)
  convert h using 1
  funext x
  simp only [Function.comp_apply, pairMapSnd_pairEncode, pairDecode_pairEncode,
    Option.map_some, Option.getD_some]
  rw [pairEncode_append, pairEncode_append]
  simp [pairDecode_pairEncode]

/-- The last `true` of `1^(n+1)` is its last letter: stripping it leaves `1ⁿ`. -/
private lemma splitAtLastTrue_replicate_succ (n : ℕ) :
    splitAtLastTrue (List.replicate (n + 1) true) = some (List.replicate n true) := by
  rw [splitAtLastTrue, List.reverse_replicate, List.replicate_succ]
  simp [List.reverse_replicate]

/-- **The unary length map is polynomial-time**: `x ↦ 1^|x|` is polynomial-time
computable. (This is how the input `1ⁿ` of a uniformity machine [AB09, Def 6.12] is
produced from an input of length `n`.)

**Proof sketch.** Pair `x` with `1^(|x|+1)` (the unary polynomial generator at
`1 · (n + 1)¹`, `Turing.FinTM.computesFunInTime_polyUnary`), strip the last `true` of the
second component (`Turing.FinTM.computesFunInTime_stripLast`), and project the second
component (`Turing.FinTM.computesFunInTime_pairSnd`). -/
theorem polyTimeComputable_unary :
    PolyTimeComputable (fun x => List.replicate x.length true) := by
  have hu : PolyTimeComputable (fun x => List.replicate (1 * (x.length + 1) ^ 1) true) := by
    obtain ⟨M, c, hM⟩ := FinTM.computesFunInTime_polyUnary 1 1
    exact ⟨M, c, 2, hM⟩
  have hpair := polyTimeComputable_id.pairEncode hu
  have hstrip : PolyTimeComputable (fun x => match pairDecode x with
      | some (a, v) =>
        match splitAtLastTrue v with
        | some u => Turing.pairEncode a u
        | none => []
      | none => []) := by
    obtain ⟨M, c, hM⟩ := FinTM.computesFunInTime_stripLast
    exact ⟨M, c, 2, hM⟩
  have hs := polyTimeComputable_of_linear FinTM.computesFunInTime_pairSnd
  convert hs.comp (hstrip.comp hpair) using 1
  funext x
  simp only [Function.comp_apply, id, pairDecode_pairEncode, Nat.pow_one, Nat.one_mul,
    splitAtLastTrue_replicate_succ, Option.map_some, Option.getD_some]

/-- **FP is closed under concatenation**: if `f` and `g` are polynomial-time computable,
so is `x ↦ f x ++ g x`. (Pair the two results, `PolyTimeComputable.pairEncode`, then
concatenate the components, `Turing.FinTM.computesFunInTime_pairConcat`.) -/
theorem PolyTimeComputable.append {f g : List Bool → List Bool}
    (hf : PolyTimeComputable f) (hg : PolyTimeComputable g) :
    PolyTimeComputable (fun x => f x ++ g x) := by
  have hc := polyTimeComputable_of_linear FinTM.computesFunInTime_pairConcat
  convert hc.comp (hf.pairEncode hg) using 1
  funext x
  simp [pairDecode_pairEncode]

/-- `x ↦ 1^{C (|x| + 1)^d}` is polynomial-time computable. -/
theorem polyTimeComputable_polyUnary (C d : ℕ) :
    PolyTimeComputable fun x => List.replicate (C * (x.length + 1) ^ d) true := by
  obtain ⟨M, a, hM⟩ := FinTM.computesFunInTime_polyUnary C d
  exact ⟨M, a, d + 1, hM⟩

/-- Prepending a fixed word is polynomial-time. -/
theorem polyTimeComputable_prepend (w : List Bool) : PolyTimeComputable (fun x => w ++ x) :=
  polyTimeComputable_of_linear (FinTM.computesFunInTime_prepend w)

/-! ### Total pair projections -/

/-- The total first projection of a `Turing.pairEncode` pair (`[]` on malformed words). -/
def pairFstD (z : List Bool) : List Bool := ((pairDecode z).map Prod.fst).getD []

/-- The total second projection of a `Turing.pairEncode` pair (`[]` on malformed words). -/
def pairSndD (z : List Bool) : List Bool := ((pairDecode z).map Prod.snd).getD []

/-- The first projection of a pair is its first component. -/
@[simp] theorem pairFstD_pairEncode (a b : List Bool) : pairFstD (pairEncode a b) = a := by
  simp [pairFstD, pairDecode_pairEncode]

/-- The second projection of a pair is its second component. -/
@[simp] theorem pairSndD_pairEncode (a b : List Bool) : pairSndD (pairEncode a b) = b := by
  simp [pairSndD, pairDecode_pairEncode]

/-- The first projection of a word is no longer than the word. -/
theorem length_pairFstD_le (z : List Bool) : (pairFstD z).length ≤ z.length := by
  cases h : pairDecode z with
  | none => simp [pairFstD, h]
  | some ab =>
    obtain ⟨a, b⟩ := ab
    have hz := Turing.eq_pairEncode_of_pairDecode z a b h
    subst hz
    simp [length_pairEncode]
    omega

/-- The first projection is polynomial-time computable. -/
theorem polyTimeComputable_pairFstD : PolyTimeComputable pairFstD :=
  polyTimeComputable_of_linear FinTM.computesFunInTime_pairFst

/-- The second projection is polynomial-time computable. -/
theorem polyTimeComputable_pairSndD : PolyTimeComputable pairSndD :=
  polyTimeComputable_of_linear FinTM.computesFunInTime_pairSnd

/-- Iterated first projections (the root of a nested tuple) are polynomial-time. -/
theorem polyTimeComputable_iterate_pairFstD (n : ℕ) : PolyTimeComputable (pairFstD^[n]) := by
  induction n with
  | zero => simp only [Function.iterate_zero]; exact polyTimeComputable_id
  | succ n ih =>
    rw [Function.iterate_succ']
    exact polyTimeComputable_pairFstD.comp ih

/-- Concatenating the two components of a pair is polynomial-time. -/
theorem polyTimeComputable_pairConcat :
    PolyTimeComputable (fun z => pairFstD z ++ pairSndD z) := by
  have h := polyTimeComputable_of_linear FinTM.computesFunInTime_pairConcat
  convert h using 1
  funext z
  cases hz : pairDecode z with
  | none => simp [pairFstD, pairSndD, hz]
  | some p => cases p; simp [pairFstD, pairSndD, hz]

/-- Swapping the components of a pair is polynomial-time. -/
theorem polyTimeComputable_pairSwap :
    PolyTimeComputable (fun z => pairEncode (pairSndD z) (pairFstD z)) :=
  polyTimeComputable_pairSndD.pairEncode polyTimeComputable_pairFstD

/-! ### Branching and length tests -/

/-- **Polynomial-time branching**: if the test `p` (as a one-bit output) and both branches
are polynomial-time computable, so is `x ↦ if p x then f x else g x`.

**Proof sketch.** The timed branch contract `Turing.FinTM.computesFunInTime_cond` runs
the test, then the selected branch; enlarge the three degrees to their maximum and
absorb the constants. -/
theorem polyTimeComputable_ite {p : List Bool → Bool} {f g : List Bool → List Bool}
    (hp : PolyTimeComputable (fun x => [p x]))
    (hf : PolyTimeComputable f) (hg : PolyTimeComputable g) :
    PolyTimeComputable (fun x => if p x then f x else g x) := by
  obtain ⟨D, A, a, hD⟩ := hp
  obtain ⟨F, B, b, hF⟩ := hf
  obtain ⟨G, C, c, hG⟩ := hg
  obtain ⟨M, K, hM⟩ := FinTM.computesFunInTime_cond hD hF hG
  let e := max a (max b c)
  refine ⟨M, K * (A + B + C + 1), e, fun x => (hM x).mono ?_⟩
  have hpow (d : ℕ) (hd : d ≤ e) : (x.length + 1) ^ d ≤ (x.length + 1) ^ e :=
    Nat.pow_le_pow_right (Nat.succ_pos _) hd
  have ha := Nat.mul_le_mul_left A (hpow a (Nat.le_max_left _ _))
  have hb := Nat.mul_le_mul_left B (hpow b
    ((Nat.le_max_left b c).trans (Nat.le_max_right a (max b c))))
  have hc := Nat.mul_le_mul_left C (hpow c
    ((Nat.le_max_right b c).trans (Nat.le_max_right a (max b c))))
  have hbc : max (B * (x.length + 1) ^ b) (C * (x.length + 1) ^ c) ≤
      B * (x.length + 1) ^ e + C * (x.length + 1) ^ e :=
    max_le (by omega) (by omega)
  have hone := Nat.one_le_pow e (x.length + 1) (Nat.succ_pos _)
  calc
    _ ≤ K * (A * (x.length + 1) ^ e +
        (B * (x.length + 1) ^ e + C * (x.length + 1) ^ e) +
        (x.length + 1) ^ e) :=
      Nat.mul_le_mul_left K (Nat.add_le_add (Nat.add_le_add ha hbc) hone)
    _ = _ := by ring

/-- Polynomial-time Boolean conjunction of two one-bit tests. -/
theorem polyTimeComputable_and {p q : List Bool → Bool}
    (hp : PolyTimeComputable (fun x => [p x])) (hq : PolyTimeComputable (fun x => [q x])) :
    PolyTimeComputable (fun x => [p x && q x]) := by
  convert polyTimeComputable_ite hp hq (polyTimeComputable_const [false]) using 1
  funext x
  cases p x <;> rfl

/-- The length test `|snd z| ≤ |fst z|` on pairs is polynomial-time.

**Proof sketch.** The catalog's threaded length check at `(C, e) = (1, 1)` decides
`|b| ≤ |a| + 1` on `⟨a, b⟩`; apply it to `⟨fst z, 1 :: snd z⟩`. -/
theorem polyTimeComputable_lenLe :
    PolyTimeComputable (fun z => [decide ((pairSndD z).length ≤ (pairFstD z).length)]) := by
  have hchk : PolyTimeComputable (fun x => [match pairDecode x with
      | some (a, b) => decide (b.length ≤ 1 * (a.length + 1) ^ 1)
      | none => false]) := by
    obtain ⟨M, a, hM⟩ := FinTM.computesFunInTime_pairLenCheck 1 1
    exact ⟨M, a, 2, hM⟩
  have hpair : PolyTimeComputable (fun z => pairEncode (pairFstD z) (true :: pairSndD z)) :=
    polyTimeComputable_pairFstD.pairEncode
      ((polyTimeComputable_prepend [true]).comp polyTimeComputable_pairSndD)
  convert hchk.comp hpair using 1
  funext z
  simp [pairDecode_pairEncode]

/-- The length-equality test `|fst z| = |snd z|` on pairs is polynomial-time. -/
theorem polyTimeComputable_lenEq :
    PolyTimeComputable (fun z => [decide ((pairFstD z).length = (pairSndD z).length)]) := by
  have h := polyTimeComputable_and polyTimeComputable_lenLe
    (polyTimeComputable_lenLe.comp polyTimeComputable_pairSwap)
  convert h using 1
  funext z
  simp only [pairFstD_pairEncode, pairSndD_pairEncode]
  congr 1
  by_cases h1 : (pairFstD z).length = (pairSndD z).length
  · simp [h1]
  · rcases Nat.lt_or_gt_of_ne h1 with h2 | h2
    · simp [h1, Nat.not_le_of_lt h2]
    · simp [h1, Nat.not_le_of_lt h2]

end Complexity

```


## ===== TCSlib/Complexity/ClassNP/PClosure.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.ClassNP.CoNP
import TCSlib.Complexity.ClassNP.PolyTimePairing

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Closure properties of `P`

The class `P` [AB09, Def 1.13] is closed under polynomial-time preimages (many-one
reductions), under the Boolean operations, and hence under Boolean functions of finitely
many tests. These facts are used tacitly throughout [AB09] (e.g. ch. 2, ch. 5, ch. 6); here
they are derived from the function class FP (`TCSlib.Complexity.ClassNP.PolyTimePairing`)
and the closure under complement (`Complexity.compl_mem_P`, `ClassNP/CoNP.lean`).

## Main results

* `Complexity.mem_P_iff_polyTimeComputable` — `V ∈ P` iff its one-bit indicator is in FP;
  `Complexity.mem_P_of_test`, `Complexity.test_of_mem_P` — the same for Boolean tests.
* `Complexity.preimage_mem_P` — `P` is closed under polynomial-time preimages.
* `Complexity.inter_mem_P`, `Complexity.union_mem_P`, `Complexity.empty_mem_P`,
  `Complexity.univ_mem_P` — Boolean closure.
* `Complexity.mem_P_of_atoms` — `P` is closed under Boolean functions of finitely many
  tests.
* `Complexity.lenEq_mem_P`, `lenLe_mem_P`, `lenEq_preimage_mem_P`, `lenLe_preimage_mem_P`
  — length comparisons are in `P`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.6, Definition 1.13; §2.2.)
-/

namespace Complexity

open Turing

/-! ### `P` and polynomial-time functions -/

/-- `V ∈ P` iff its singleton indicator `x ↦ [1_V(x)]` is polynomial-time computable. -/
theorem mem_P_iff_polyTimeComputable {V : Language Bool} :
    V ∈ P ↔ PolyTimeComputable (fun x => [MultiTapeTM.indicator V x]) := by
  constructor
  · intro h
    obtain ⟨C, c, M, hM⟩ := mem_P_iff.mp h
    exact ⟨M, C, c, hM⟩
  · rintro ⟨M, C, c, hM⟩
    exact mem_P_iff.mpr ⟨C, c, M, hM⟩

/-- **`P` is closed under polynomial-time preimages**: if `V ∈ P` and `g` is
polynomial-time computable then `g⁻¹(V) ∈ P` (the decider of `V` run on `g x`). -/
theorem preimage_mem_P {V : Language Bool} {g : List Bool → List Bool} (hV : V ∈ P)
    (hg : PolyTimeComputable g) : g ⁻¹' V ∈ P :=
  mem_P_iff_polyTimeComputable.mpr ((mem_P_iff_polyTimeComputable.mp hV).comp hg)

/-- A language whose Boolean test is polynomial-time computable (as a one-bit output) is
in `P`. -/
theorem mem_P_of_test {b : List Bool → Bool} (h : PolyTimeComputable (fun z => [b z])) :
    {z | b z = true} ∈ P := by
  rw [mem_P_iff_polyTimeComputable]
  convert h using 2 with z
  by_cases hz : b z = true <;> simp [MultiTapeTM.indicator, hz]

/-- The Boolean test of a language in `P` is polynomial-time computable. -/
theorem test_of_mem_P {L : Language Bool} (h : L ∈ P) :
    PolyTimeComputable (fun z => [MultiTapeTM.indicator L z]) :=
  mem_P_iff_polyTimeComputable.mp h

/-! ### Boolean closure -/

/-- **`P` is closed under intersection.** -/
theorem inter_mem_P {L₁ L₂ : Language Bool} (h₁ : L₁ ∈ P) (h₂ : L₂ ∈ P) :
    {z | z ∈ L₁ ∧ z ∈ L₂} ∈ P := by
  have h := mem_P_of_test (polyTimeComputable_and (test_of_mem_P h₁) (test_of_mem_P h₂))
  convert h using 1
  ext z
  by_cases a : z ∈ L₁ <;> by_cases b : z ∈ L₂ <;> simp [MultiTapeTM.indicator, a, b]

/-- **`P` is closed under union** (branching on the first test). -/
theorem union_mem_P {L₁ L₂ : Language Bool} (h₁ : L₁ ∈ P) (h₂ : L₂ ∈ P) :
    {z | z ∈ L₁ ∨ z ∈ L₂} ∈ P := by
  have ht : PolyTimeComputable
      (fun z => [MultiTapeTM.indicator L₁ z || MultiTapeTM.indicator L₂ z]) := by
    convert polyTimeComputable_ite (test_of_mem_P h₁) (polyTimeComputable_const [true])
      (test_of_mem_P h₂) using 1
    funext z
    cases MultiTapeTM.indicator L₁ z <;> rfl
  convert mem_P_of_test ht using 1
  ext z
  by_cases a : z ∈ L₁ <;> by_cases b : z ∈ L₂ <;> simp [MultiTapeTM.indicator, a, b]

/-- The empty language is in `P`. -/
theorem empty_mem_P : ({_z | false = true} : Language Bool) ∈ P :=
  mem_P_of_test (polyTimeComputable_const [false])

/-- The full language is in `P`. -/
theorem univ_mem_P : ({_z | true = true} : Language Bool) ∈ P :=
  mem_P_of_test (polyTimeComputable_const [true])

/-- **`P` is closed under Boolean functions of finitely many tests**: if each test
`b i` decides a language in `P`, so does `z ↦ F (b · z)` for any `F`.

**Proof sketch.** The language is the finite union, over the valuations `β` with
`F β = true`, of the finite intersections `⋂ᵢ {z | b i z = β i}`; each set in the
intersection is a test language or its complement. -/
theorem mem_P_of_atoms {ι : Type} [Fintype ι] [DecidableEq ι] (b : ι → List Bool → Bool)
    (hb : ∀ i, ({z | b i z = true} : Language Bool) ∈ P) (F : (ι → Bool) → Bool) :
    ({z | F (fun i => b i z) = true} : Language Bool) ∈ P := by
  classical
  -- one valuation
  have hval : ∀ β : ι → Bool, ∀ s : Finset ι,
      ({z | ∀ i ∈ s, b i z = β i} : Language Bool) ∈ P := by
    intro β s
    induction s using Finset.induction_on with
    | empty => simpa using univ_mem_P
    | insert i s hi ih =>
      have hi' : ({z | b i z = β i} : Language Bool) ∈ P := by
        cases hβ : β i
        · have := compl_mem_P (hb i)
          convert this using 1
          ext z
          change b i z = false ↔ ¬ (b i z = true)
          simp
        · exact hb i
      have := inter_mem_P hi' ih
      convert this using 1
      ext z
      simp
  have hunion : ∀ s : Finset (ι → Bool),
      ({z | ∃ β ∈ s, ∀ i, b i z = β i} : Language Bool) ∈ P := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using empty_mem_P
    | insert β s hβ ih =>
      have h1 := hval β Finset.univ
      have := union_mem_P h1 ih
      convert this using 1
      ext z
      change (∃ β' ∈ insert β s, ∀ i, b i z = β' i) ↔
        (∀ i ∈ Finset.univ, b i z = β i) ∨ (∃ β' ∈ s, ∀ i, b i z = β' i)
      simp
  have h := hunion (Finset.univ.filter fun β => F β = true)
  convert h using 1
  ext z
  simp only [Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hz; exact ⟨_, hz, fun i => rfl⟩
  · rintro ⟨β, hβ, hb'⟩
    have : (fun i => b i z) = β := funext hb'
    rw [this]; exact hβ

/-! ### Length comparisons -/

/-- The pairs whose two components have equal length form a language in `P`. -/
theorem lenEq_mem_P : {z : List Bool | (pairFstD z).length = (pairSndD z).length} ∈ P := by
  have h := mem_P_of_test polyTimeComputable_lenEq
  simpa using h

/-- The pairs whose second component is at most as long as the first form a language
in `P`. -/
theorem lenLe_mem_P : {z : List Bool | (pairSndD z).length ≤ (pairFstD z).length} ∈ P := by
  have h := mem_P_of_test polyTimeComputable_lenLe
  simpa using h

/-- Comparing the lengths of two polynomial-time computable strings is in `P`. -/
theorem lenEq_preimage_mem_P {f g : List Bool → List Bool} (hf : PolyTimeComputable f)
    (hg : PolyTimeComputable g) : {z | (f z).length = (g z).length} ∈ P := by
  have h := preimage_mem_P lenEq_mem_P (hf.pairEncode hg)
  simpa using h

/-- `|g z| ≤ |f z|` for polynomial-time `f`, `g` is decidable in `P`. -/
theorem lenLe_preimage_mem_P {f g : List Bool → List Bool} (hf : PolyTimeComputable f)
    (hg : PolyTimeComputable g) : {z | (g z).length ≤ (f z).length} ∈ P := by
  have h := preimage_mem_P lenLe_mem_P (hf.pairEncode hg)
  simpa using h

end Complexity

```


## ===== TCSlib/Complexity/ClassNP/Transducer.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.ClassNP.PolyTimePairing
import TCSlib.Complexity.TuringMachine.Simulation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# One-pass transducers run in linear time

A *one-pass transducer* (a Mealy machine) reads its input once from left to right in a
finite control state, emitting at most one bit per input bit. This file realizes every
such transducer as a work-tape-free Turing machine running in time `|x| + 1`, so its
string function is polynomial-time computable. It is the machine-side tool behind
several reductions of [AB09, ch. 6]: the validator and output-clause stages of
`CKT-SAT ≤p 3SAT` ([AB09, Lem 6.11], `CircuitComplexity/CircuitSatReduction.lean`), the
marker stripping of the Karp–Lipton prefix language, and the field recoding of Meyer's
verifier.

## Main definitions

* `Complexity.transduce` — the string function of a transducer with transition `δ` and
  emission `o`.
* `Complexity.transducerTM` — the machine running it.

## Main results

* `Complexity.transducerTM_computes` — the machine computes the transducer's function
  within `|x| + 1` steps.
* `Complexity.polyTimeComputable_transduce` — hence it is in FP.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2: the multi-tape machine; §6.1.2, Lemma 6.11.)
-/

namespace Complexity

open Turing

variable {σ : Type}

/-- The string function of a one-pass transducer: from control state `q`, each input
bit `b` emits `o q b` (one bit or nothing) and moves to `δ q b`. -/
def transduce (δ : σ → Bool → σ) (o : σ → Bool → Option Bool) : σ → List Bool → List Bool
  | _, [] => []
  | q, b :: l => (o q b).toList ++ transduce δ o (δ q b) l

/-- The transducer on a concatenation: run the first part, then the second part from the
state reached. -/
theorem transduce_append (δ : σ → Bool → σ) (o : σ → Bool → Option Bool) (q : σ)
    (l₁ l₂ : List Bool) :
    transduce δ o q (l₁ ++ l₂) =
      transduce δ o q l₁ ++ transduce δ o (l₁.foldl δ q) l₂ := by
  induction l₁ generalizing q with
  | nil => rfl
  | cons b l ih => simp [transduce, ih]

/-- The transition table of the transducer machine: on a bit, emit, move right and change
state; on the right blank, halt. -/
def transducerTr (δ : σ → Bool → σ) (o : σ → Bool → Option Bool) :
    σ → Option Bool → (Fin 0 → Option Bool) → Action 0 Bool σ
  | q, some b, _ => ⟨.pos, fun _ => (none, 0), o q b, some (δ q b)⟩
  | _, none, _ => ⟨0, fun _ => (none, 0), none, none⟩

/-- **The transducer machine**: no work tapes, control states `σ`, started in `q₀`. -/
def transducerTM [Fintype σ] [DecidableEq σ] (δ : σ → Bool → σ)
    (o : σ → Bool → Option Bool) (q₀ : σ) : FinTM Bool where
  k := 0
  State := σ
  tm := { q₀ := q₀, tr := transducerTr δ o }

/-- The run of the transducer machine: from state `q` reading the suffix `x.drop i`, it
halts after `|x| - i + 1` steps having appended `transduce δ o q (x.drop i)`.

**Proof sketch.** Induction on the suffix: on a bit the machine emits `o q b` and steps
right (`inputSymbol_at` reads `x[i]`), on the right blank it halts. -/
theorem transducer_run [Fintype σ] [DecidableEq σ] (δ : σ → Bool → σ)
    (o : σ → Bool → Option Bool) (q₀ : σ) (x : List Bool) :
    ∀ (l : List Bool) (q : σ) (cfg : Cfg 0 Bool σ x) (i : ℕ), l = x.drop i → i ≤ x.length →
      cfg.state = some q → cfg.inputPos.val = i + 1 →
      ((transducerTM δ o q₀).tm.runFrom cfg (l.length + 1)).state = none ∧
      ((transducerTM δ o q₀).tm.runFrom cfg (l.length + 1)).output =
        cfg.output ++ transduce δ o q l := by
  intro l
  induction l with
  | nil =>
    intro q cfg i hl hi hq hp
    have hix : i = x.length := by
      have := congrArg List.length hl
      simp at this
      omega
    have hsym : cfg.inputSymbol = none := by
      rw [FinTM.inputSymbol_at cfg i hi hp]; simp [hix]
    simp only [List.length_nil, Nat.zero_add, MultiTapeTM.runFrom_succ_eq_step,
      MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    rw [hq]
    simp only
    rw [hsym]
    simp [transducerTM, transducerTr, transduce]
  | cons b l ih =>
    intro q cfg i hl hi hq hp
    have hlt : i < x.length := by
      by_contra h
      rw [List.drop_eq_nil_of_le (by omega)] at hl
      exact List.cons_ne_nil _ _ hl
    have hb : x[i]? = some b := by
      have := congrArg List.head? hl
      simpa [List.head?_drop] using this.symm
    have hsym : cfg.inputSymbol = some b := by
      rw [FinTM.inputSymbol_at cfg i hi hp, hb]
    have hl' : l = x.drop (i + 1) := by
      have := congrArg List.tail hl
      simpa [List.tail_drop] using this
    rw [List.length_cons, MultiTapeTM.runFrom_succ_eq_step]
    have hstep : (transducerTM δ o q₀).tm.step cfg =
        ⟨some (δ q b), moveInputPos cfg.inputPos .pos, cfg.workTapes,
          fun i => cfg.workTapePos i + 0, cfg.output ++ (o q b).toList⟩ := by
      unfold MultiTapeTM.step
      rw [hq]
      simp only
      rw [hsym]
      simp only [transducerTM, transducerTr, Action.apply]
      congr 1
    have hp' : (moveInputPos cfg.inputPos .pos).val = i + 1 + 1 := by
      rw [moveInputPos_pos_of_ne_right _ (by omega)]
      simp [hp]
    obtain ⟨h1, h2⟩ := ih (δ q b) ((transducerTM δ o q₀).tm.step cfg) (i + 1) hl' (by omega)
      (by rw [hstep]) (by rw [hstep]; exact hp')
    refine ⟨h1, ?_⟩
    rw [h2, hstep]
    simp [transduce]

/-- **The transducer machine computes the transducer's function** within `|x| + 1` steps. -/
theorem transducerTM_computes [Fintype σ] [DecidableEq σ] (δ : σ → Bool → σ)
    (o : σ → Bool → Option Bool) (q₀ : σ) :
    (transducerTM δ o q₀).ComputesFunInTime (transduce δ o q₀) fun n => n + 1 := by
  intro x
  obtain ⟨h1, h2⟩ := transducer_run δ o q₀ x x q₀ ((transducerTM δ o q₀).tm.initCfg x) 0
    (by simp) (by simp) rfl rfl
  exact (FinTM.computesInTime_iff _ _ _ _).mpr ⟨h1, by rw [h2]; rfl⟩

/-- A one-pass transducer computes a polynomial-time function. -/
theorem polyTimeComputable_transduce [Fintype σ] [DecidableEq σ] (δ : σ → Bool → σ)
    (o : σ → Bool → Option Bool) (q₀ : σ) :
    PolyTimeComputable (transduce δ o q₀) :=
  polyTimeComputable_of_linear
    ⟨transducerTM δ o q₀, 1, fun x => by
      simpa only [Nat.one_mul] using transducerTM_computes δ o q₀ x⟩

end Complexity

```


## ===== TCSlib/Complexity/SpaceComplexity/Basic.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Data.Nat.Log
import TCSlib.Complexity.ClassP.DTIME
import TCSlib.Complexity.TuringMachine.Encoding

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Space-bounded computation, `SPACE`, `L`, and implicitly logspace computable functions

[AB09, Def 4.1]: a language is in `SPACE(s(n))` when some machine decides it while
visiting at most `c · s(n)` work-tape cells on every input of length `n`; `L = SPACE(log n)`
[AB09, Def 4.5]. [AB09, Def 4.16]: a function `f` is *implicitly logspace computable* when it
is polynomially bounded and the two languages "the `i`-th bit of `f(x)` is `1`" and
"`i` is a position of `f(x)`" are in `L`.

## The machine model

We reuse the campaign's machines (`Turing.FinTM Bool`) unchanged. They already have the
shape of [AB09, Fig. 4.1]:

* **the input tape is read-only**: a transition (`Turing.Action`) has no write component
  for the input tape, only a head move, clamped to the input and its two boundary blanks;
* **the output tape is write-once, append-only**: a step appends at most one symbol;
* **space is the number of work-tape cells visited** (`Turing.MultiTapeTM.spaceUsed`, the
  sum over the work tapes of the visited cells), exactly the measure of [AB09, Def 4.1]
  ("at most `c · s(n)` locations on M's work tapes (excluding the input tape) are ever
  visited by M's head").

## Main definitions

* `Turing.FinTM.ComputesInSpace` — `M` computes `f`, halting on every input, visiting at most
  `s(|x|)` work cells.
* `Turing.FinTM.DecidesInSpace` — `M` decides `L` within space `s`. [AB09, Def 4.1]
* `Complexity.SPACE` — the class of languages decidable in space `c · s(n)`. [AB09, Def 4.1]
* `Complexity.logSpace` — the logarithmic space bound `⌊log₂ n⌋ + 1`.
* `Complexity.LOGSPACE` — the class `L = SPACE(log n)`. [AB09, Def 4.5]
* `Complexity.indexLang` — the language `{⟨x, i⟩ | p x i}` with `i` in binary.
* `Complexity.ImplicitlyLogspaceComputable` — [AB09, Def 4.16].

## Main results

* `Complexity.SPACE.mono` — `SPACE` is monotone in the space bound.

## Divergences from [AB09]

* **The logarithm.** [AB09] writes `SPACE(log n)` and requires `s(n) ≥ log n` (p. 79). We use
  `logSpace n = ⌊log₂ n⌋ + 1`, which is at least `1` (so short inputs get constant space, the
  standard reading of the convention) and is `Θ(log n)` for `n ≥ 2`.
* **Pairs and indices** (Def 4.16). The pair `⟨x, i⟩` is `Turing.pairEncode x (Nat.bits i)`:
  the campaign's self-delimiting pairing with the index in little-endian binary without
  redundant zeros (`Nat.bits 0 = []`). Indices are **`0`-based**: the bit language is
  `{⟨x, i⟩ | f(x)ᵢ = 1}` with `f(x)ᵢ` the `i`-th bit from `0`, and the length language is
  `{⟨x, i⟩ | i < |f(x)|}` where [AB09] writes `i ≤ |f(x)|` for `1`-based `i`.
* **Polynomial bound** (Def 4.16). [AB09] asks `|f(x)| ≤ |x|^c`; at `x = ε` that forces
  `f(ε) = ε` for `c ≥ 1`. We use the campaign normal form `|f(x)| ≤ C · (|x| + 1)^c`
  (`Complexity.PolyBound` shape).
* **Halting.** Deciding (resp. computing) includes halting on every input, as in [AB09]
  ("a TM M deciding L"); the space bound is checked at the halting time, and since space is
  monotone in time and frozen after halting this is the space of the whole computation.
* **One measure for both classes.** [AB09, Def 4.1]'s own wording splits: *visited*
  work-tape locations for `SPACE` (the clause quoted above) but *nonblank* locations for
  `NSPACE`. The campaign convention is the visited-cells measure for both; the planned
  `NSPACE` (`AroraBarakChapters3-4Plan.md`, phase P4.1) counts visited cells along every
  choice word, with all branches halting.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1, Definitions 4.1 and 4.5; §4.3, Definition 4.16.)
-/

namespace Turing.FinTM

/-- The machine `M` computes `f` in space `s`: on every input `x` it halts with output `f x`,
and up to that time it has visited at most `s |x|` work-tape cells (summed over its work
tapes). The input tape (read-only) and the output tape (append-only) do not count.
[AB09, Def 4.1, for functions] -/
def ComputesInSpace (M : FinTM Bool) (f : List Bool → List Bool) (s : ℕ → ℕ) : Prop :=
  ∀ x : List Bool, ∃ t, M.ComputesInTime x (f x) t ∧
    M.tm.spaceUsed (M.tm.initCfg x) t ≤ s x.length

/-- The machine `M` decides `L` in space `s`: it computes the indicator `[x ∈ L]` (a
one-bit output) in space `s`. [AB09, Def 4.1] -/
def DecidesInSpace (M : FinTM Bool) (L : Language Bool) (s : ℕ → ℕ) : Prop :=
  M.ComputesInSpace (fun x => [MultiTapeTM.indicator (L : Set (List Bool)) x]) s

/-- A space bound can be weakened. -/
theorem ComputesInSpace.mono {M : FinTM Bool} {f : List Bool → List Bool} {s s' : ℕ → ℕ}
    (h : M.ComputesInSpace f s) (hs : ∀ n, s n ≤ s' n) : M.ComputesInSpace f s' := by
  intro x
  obtain ⟨t, ht, hsp⟩ := h x
  exact ⟨t, ht, hsp.trans (hs _)⟩

end Turing.FinTM

namespace Complexity

open Turing

/-- **`SPACE(s)`** [AB09, Def 4.1]: the languages decided by some finite binary-alphabet
machine visiting at most `c · s(n)` work-tape cells on inputs of length `n`, for some
constant `c`. -/
def SPACE (s : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∃ (c : ℕ) (M : FinTM Bool), M.DecidesInSpace L fun n => c * s n}

/-- `SPACE` is monotone in the space bound. -/
theorem SPACE.mono {s₁ s₂ : ℕ → ℕ} (h : ∀ n, s₁ n ≤ s₂ n) : SPACE s₁ ⊆ SPACE s₂ := by
  rintro L ⟨c, M, hM⟩
  exact ⟨c, M, hM.mono fun n => Nat.mul_le_mul_left c (h n)⟩

/-- The logarithmic space bound `⌊log₂ n⌋ + 1`: `Θ(log n)`, and at least `1`, following the
convention `s(n) ≥ log n` of [AB09, p. 79]. -/
def logSpace (n : ℕ) : ℕ := Nat.log 2 n + 1

/-- **The class `L`** [AB09, Def 4.5]: `L = SPACE(log n)`, the languages decidable by a
machine visiting `O(log n)` work-tape cells. (Named `LOGSPACE` to keep the letter `L` free
for language variables.) -/
def LOGSPACE : Set (Language Bool) := SPACE logSpace

/-- The language `{⟨x, i⟩ | p x i}`, the pair encoded as `Turing.pairEncode x (Nat.bits i)`
(index in little-endian binary). The shape of the two languages of [AB09, Def 4.16]. -/
def indexLang (p : List Bool → ℕ → Prop) : Language Bool :=
  {w | ∃ x i, w = pairEncode x (Nat.bits i) ∧ p x i}

/-- **Implicitly logspace computable functions** [AB09, Def 4.16]: `f` is polynomially
bounded, `|f(x)| ≤ C · (|x| + 1)^c`, and both the bit language
`{⟨x, i⟩ | f(x)ᵢ = 1}` and the length language `{⟨x, i⟩ | i < |f(x)|}` are in `L`.
Indices are `0`-based and written in binary (`Nat.bits`); see the module docstring for the
divergences (`0`-based `i < |f(x)|` for the book's `1`-based `i ≤ |f(x)|`, and the `+ 1`
in the polynomial bound). -/
def ImplicitlyLogspaceComputable (f : List Bool → List Bool) : Prop :=
  (∃ C c : ℕ, ∀ x : List Bool, (f x).length ≤ C * (x.length + 1) ^ c) ∧
  indexLang (fun x i => (f x).getD i false = true) ∈ LOGSPACE ∧
  indexLang (fun x i => i < (f x).length) ∈ LOGSPACE

/-- `logSpace` is monotone. -/
lemma logSpace_mono {a b : ℕ} (h : a ≤ b) : logSpace a ≤ logSpace b := by
  unfold logSpace
  have := Nat.log_mono_right (b := 2) h
  omega

end Complexity

```


## ===== TCSlib/Complexity/SpaceComplexity/ConfigCount.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Interval
import Mathlib.Order.Interval.Finset.Nat
import TCSlib.Complexity.SpaceComplexity.Basic
import TCSlib.Complexity.ClassP.P
import TCSlib.Complexity.ClassNP.PolyTime

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Configuration counting: space-bounded machines halt quickly, `L ⊆ P`

[AB09, §4.1.1 and Thm 4.2]: a deterministic machine that halts never repeats a
configuration, and a machine using `s` work cells has at most `2^{O(s)} · poly(n)`
configurations, so it halts within that many steps. For `s = O(log n)` this is a
polynomial, giving `L ⊆ P` and "logspace computations run in polynomial time" [AB09, p. 112].

## Main definitions

* `Turing.FinTM.configBound` — the configuration count
  `(|Q| + 1) · (n + 2) · 3^{k(2s+1)} · (2s + 1)^k` of a `k`-tape machine with state set `Q`
  on inputs of length `n` with at most `s` visited work cells.

## Main results

* `Turing.MultiTapeTM.abs_pos_lt_card_visited` — the visited cells of a tape form an
  interval around the origin, so every visited position `z` has `|z| < #visited`.
* `Turing.FinTM.ComputesInTime.of_spaceUsed_le` — a computation that has halted by time `t`
  having visited at most `s` cells has in fact halted by time `configBound M |x| s`.
  [AB09, §4.1.1, the deterministic case of Thm 4.2]
* `Complexity.LOGSPACE_subset_P` — `L ⊆ P`. [AB09, Thm 4.2 for `S = log n`]
* `Complexity.polyTimeComputable_of_computesInSpace` — a function computed in logarithmic
  space is polynomial-time computable. [AB09, p. 112: "logspace computations run in
  polynomial time"]

## Design

A configuration of the vendored model also records the output tape, which grows; the
argument is run on the *core* `(state, input position, work tapes, work heads)`, whose
evolution does not depend on the output. If two times before the first halting time have
the same core, the core sequence is periodic from then on and the machine never halts.
Cores reached with at most `s` visited cells are coded injectively into a finite type:
heads lie in `[-s, s]` (the visited set is an interval containing `0`, by a discrete
intermediate value argument) and every nonblank cell has been visited.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.1, Claim 4.4 and Theorem 4.2; §6.2.1, p. 112.)
-/

namespace Turing

namespace MultiTapeTM

variable {k : ℕ} {S : Type} {x : List Bool}

/-! ### Internal helpers: cores of configurations -/

namespace ConfigCount

/-- The core of a configuration: everything but the output tape. -/
def core (c : Cfg k Bool S x) :
    Option S × Fin (x.length + 2) × (Fin k → ℤ → Option Bool) × (Fin k → ℤ) :=
  (c.state, c.inputPos, c.workTapes, c.workTapePos)

/-- The core after a step depends only on the core before it. -/
lemma core_step (tm : MultiTapeTM k Bool S) {c d : Cfg k Bool S x} (h : core c = core d) :
    core (tm.step c) = core (tm.step d) := by
  simp only [core, Prod.mk.injEq] at h
  obtain ⟨hs, hi, hw, hp⟩ := h
  have hsym : c.inputSymbol = d.inputSymbol := by
    unfold Cfg.inputSymbol; simp only [hi]
  have hws : c.workTapeSymbols = d.workTapeSymbols := by
    funext i; simp only [Cfg.workTapeSymbols, hw, hp]
  unfold step
  rw [hs]
  cases d.state with
  | none => simp [core, hs, hi, hw, hp]
  | some q =>
    simp only [core, Action.apply, hsym, hws, hi, hw, hp]

/-- Equal cores stay equal along runs. -/
lemma core_runFrom (tm : MultiTapeTM k Bool S) {c d : Cfg k Bool S x} (h : core c = core d)
    (t : ℕ) : core (tm.runFrom c t) = core (tm.runFrom d t) := by
  induction t with
  | zero => simpa using h
  | succ t ih =>
    rw [runFrom_succ_eq_step', runFrom_succ_eq_step']
    exact core_step tm ih

/-- Before the first halting time, no core repeats.

**Proof sketch.** If the cores at times `t₁ < t₂` agree, then the cores at `t₁ + j` and
`t₂ + j` agree for every `j`, so the core at `t₁ + r` equals the core at `t₁ + (r mod p)`
with `p = t₂ - t₁`. At the first halting time `T = t₁ + r` the state is `none`, but
`t₁ + (r mod p) < t₂ < T` is an earlier, non-halted time. -/
lemma core_injOn (tm : MultiTapeTM k Bool S) (c : Cfg k Bool S x) (T : ℕ)
    (hT : (tm.runFrom c T).state = none)
    (hmin : ∀ t < T, (tm.runFrom c t).state ≠ none) {t₁ t₂ : ℕ} (h₁₂ : t₁ < t₂)
    (h₂ : t₂ < T) : core (tm.runFrom c t₁) ≠ core (tm.runFrom c t₂) := by
  intro heq
  set p := t₂ - t₁ with hp
  have hpos : 0 < p := by omega
  -- the core at `t₁ + r` equals the one at `t₁ + (r - p)` once `r ≥ p`
  have hback : ∀ r, p ≤ r →
      core (tm.runFrom c (t₁ + r)) = core (tm.runFrom c (t₁ + (r - p))) := by
    intro r hr
    have e1 : t₁ + r = t₂ + (r - p) := by omega
    rw [e1, runFrom_add, runFrom_add c t₁]
    exact core_runFrom tm heq.symm _
  have hmod : ∀ r, core (tm.runFrom c (t₁ + r)) = core (tm.runFrom c (t₁ + r % p)) := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      by_cases hr : r < p
      · rw [Nat.mod_eq_of_lt hr]
      · rw [hback r (by omega), ih (r - p) (by omega), ← Nat.mod_eq_sub_mod (by omega)]
  have hTgt : t₂ < T := h₂
  have hr := hmod (T - t₁)
  rw [show t₁ + (T - t₁) = T by omega] at hr
  have hlt : t₁ + (T - t₁) % p < T := by
    have := Nat.mod_lt (T - t₁) hpos
    omega
  apply hmin _ hlt
  have := congrArg Prod.fst hr
  simp only [core] at this
  rw [← this, hT]

/-- Discrete intermediate values: a sequence of integers starting at `0` and moving by at
most one per step passes through every integer between `0` and any of its values.

**Proof sketch.** Induction on `t`. If `y` lies between `0` and `p t`, the induction hypothesis
applies. Otherwise `y` lies between `p t` and `p (t + 1)`, which differ by at most one, so `y =
p (t + 1)`. -/
lemma exists_eq_of_between (p : ℕ → ℤ) (h0 : p 0 = 0) (hstep : ∀ j, |p (j + 1) - p j| ≤ 1) :
    ∀ t (y : ℤ), (0 ≤ y ∧ y ≤ p t ∨ p t ≤ y ∧ y ≤ 0) → ∃ j ≤ t, p j = y := by
  intro t
  induction t with
  | zero =>
    intro y hy
    exact ⟨0, le_rfl, by rw [h0] at hy; omega⟩
  | succ t ih =>
    intro y hy
    have hs := hstep t
    rw [abs_le] at hs
    by_cases hin : 0 ≤ y ∧ y ≤ p t ∨ p t ≤ y ∧ y ≤ 0
    · obtain ⟨j, hj, hpj⟩ := ih y hin
      exact ⟨j, by omega, hpj⟩
    · exact ⟨t + 1, le_rfl, by omega⟩

end ConfigCount

open ConfigCount

/-- The positions visited by work head `i` from an initial configuration form a set in
which every position `z` satisfies `|z| < #visited`: the visited set contains the whole
interval between `0` and `z`.

**Proof sketch.** The visited set contains `0` (the start) and, by the discrete intermediate
value theorem (`exists_eq_of_between`, the head moves by at most one cell per step), every
integer between `0` and any visited `z`. So it contains the `|z| + 1` integers between `0` and
`z`, and its cardinality exceeds `|z|`. -/
lemma abs_pos_lt_card_visited (tm : MultiTapeTM k Bool S) (x : List Bool) (t : ℕ)
    (i : Fin k) {z : ℤ} (hz : z ∈ tm.visitedByTapeHead (tm.initCfg x) t i) :
    |z| < (tm.visitedByTapeHead (tm.initCfg x) t i).card := by
  set p : ℕ → ℤ := fun j => (tm.runFrom (tm.initCfg x) j).workTapePos i with hpdef
  have h0 : p 0 = 0 := by simp [p]
  have hstep : ∀ j, |p (j + 1) - p j| ≤ 1 := by
    intro j
    simp only [p, runFrom_succ_eq_step']
    exact tm.workTapePos_step_le _ i
  obtain ⟨t', ht', hzt⟩ : ∃ t' ≤ t, p t' = z := by
    simp only [visitedByTapeHead, Finset.mem_image, Finset.mem_range] at hz
    obtain ⟨t', ht', h⟩ := hz
    exact ⟨t', by omega, h⟩
  -- the interval between `0` and `z` lies in the visited set
  have hsub : Finset.Icc (min 0 z) (max 0 z) ⊆ tm.visitedByTapeHead (tm.initCfg x) t i := by
    intro y hy
    rw [Finset.mem_Icc] at hy
    obtain ⟨j, hj, hpj⟩ := exists_eq_of_between p h0 hstep t' y (by
      rw [hzt]; rcases le_total 0 z with h | h
      · left; simp only [min_eq_left h, max_eq_right h] at hy; omega
      · right; simp only [min_eq_right h, max_eq_left h] at hy; omega)
    simp only [visitedByTapeHead, Finset.mem_image, Finset.mem_range]
    exact ⟨j, by omega, hpj⟩
  have hc := Finset.card_le_card hsub
  rw [Int.card_Icc] at hc
  rcases le_total 0 z with h | h
  · simp only [min_eq_left h, max_eq_right h] at hc
    rw [abs_of_nonneg h]; omega
  · simp only [min_eq_right h, max_eq_left h] at hc
    rw [abs_of_nonpos h]; omega

/-- A cell holding a nonblank symbol at time `t` was visited by its head before time `t`.

**Proof sketch.** Induction on `t`. Initially every work cell is blank. A step writes only the
cell under the head, which is visited at that step; other cells keep their contents and stay
visited by monotonicity of the visited sets. -/
lemma mem_visited_of_ne_none (tm : MultiTapeTM k Bool S) (x : List Bool) (t : ℕ)
    (i : Fin k) (z : ℤ) (hz : (tm.runFrom (tm.initCfg x) t).workTapes i z ≠ none) :
    z ∈ tm.visitedByTapeHead (tm.initCfg x) t i := by
  induction t with
  | zero => simp [initCfg, Cfg.init] at hz
  | succ t ih =>
    simp only [visitedByTapeHead, Finset.mem_image, Finset.mem_range] at ih ⊢
    rw [runFrom_succ_eq_step'] at hz
    unfold step at hz
    cases hs : (tm.runFrom (tm.initCfg x) t).state with
    | none =>
      rw [hs] at hz
      obtain ⟨j, hj, h⟩ := ih hz
      exact ⟨j, by omega, h⟩
    | some q =>
      rw [hs] at hz
      dsimp only [Action.apply] at hz
      cases hw : ((tm.tr q (tm.runFrom (tm.initCfg x) t).inputSymbol
          (tm.runFrom (tm.initCfg x) t).workTapeSymbols).workTapes i).1 with
      | none =>
        rw [hw] at hz
        obtain ⟨j, hj, h⟩ := ih hz
        exact ⟨j, by omega, h⟩
      | some a =>
        rw [hw] at hz
        dsimp only at hz
        by_cases hzp : z = (tm.runFrom (tm.initCfg x) t).workTapePos i
        · exact ⟨t, by omega, hzp.symm⟩
        · rw [Function.update_of_ne hzp] at hz
          obtain ⟨j, hj, h⟩ := ih hz
          exact ⟨j, by omega, h⟩

/-- Visited sets grow with time. -/
lemma visitedByTapeHead_mono (tm : MultiTapeTM k Bool S) (c : Cfg k Bool S x) {t t' : ℕ}
    (h : t ≤ t') (i : Fin k) : tm.visitedByTapeHead c t i ⊆ tm.visitedByTapeHead c t' i := by
  intro z hz
  simp only [visitedByTapeHead, Finset.mem_image, Finset.mem_range] at hz ⊢
  obtain ⟨j, hj, h'⟩ := hz
  exact ⟨j, by omega, h'⟩

/-- Space used grows with time. -/
lemma spaceUsed_mono (tm : MultiTapeTM k Bool S) (c : Cfg k Bool S x) {t t' : ℕ}
    (h : t ≤ t') : tm.spaceUsed c t ≤ tm.spaceUsed c t' :=
  Finset.sum_le_sum fun i _ => Finset.card_le_card (tm.visitedByTapeHead_mono c h i)

namespace ConfigCount

/-- The code of an integer in `[-B, B]` as an element of `Fin (2B + 1)`. -/
def posCode (B : ℕ) (z : ℤ) : Fin (2 * B + 1) :=
  ⟨min (z + B).toNat (2 * B), by omega⟩

/-- The position code is injective on positions of absolute value at most `B`. -/
lemma posCode_injOn (B : ℕ) {z z' : ℤ} (hz : |z| ≤ B) (hz' : |z'| ≤ B)
    (h : posCode B z = posCode B z') : z = z' := by
  simp only [posCode, Fin.mk.injEq] at h
  rw [abs_le] at hz hz'
  omega

/-- The finite code of a core with heads and nonblank cells in `[-B, B]`. -/
def coreCode (B : ℕ) (c : Cfg k Bool S x) :
    Option S × Fin (x.length + 2) × (Fin k → Fin (2 * B + 1) → Option Bool) ×
      (Fin k → Fin (2 * B + 1)) :=
  (c.state, c.inputPos, fun i j => c.workTapes i ((j : ℤ) - B),
    fun i => posCode B (c.workTapePos i))

/-- The code is injective on cores whose heads and nonblank cells lie in `[-B, B]`.

**Proof sketch.** State, input position and head positions are read off the code directly, the
positions by injectivity of `posCode` on `[-B, B]`. A cell `z` with `|z| ≤ B` is recorded in the
code. A cell with `|z| > B` is blank in both configurations by hypothesis. -/
lemma coreCode_inj (B : ℕ) {c d : Cfg k Bool S x}
    (hc : ∀ i, |c.workTapePos i| ≤ B ∧ ∀ z, c.workTapes i z ≠ none → |z| ≤ B)
    (hd : ∀ i, |d.workTapePos i| ≤ B ∧ ∀ z, d.workTapes i z ≠ none → |z| ≤ B)
    (h : coreCode B c = coreCode B d) : core c = core d := by
  simp only [coreCode, Prod.mk.injEq] at h
  obtain ⟨hs, hi, hw, hp⟩ := h
  simp only [core, Prod.mk.injEq]
  refine ⟨hs, hi, ?_, ?_⟩
  · funext i z
    by_cases hz : |z| ≤ B
    · have := congrFun (congrFun hw i) ⟨(z + B).toNat, by rw [abs_le] at hz; omega⟩
      simp only at this
      rwa [show (((z + B).toNat : ℕ) : ℤ) - B = z by rw [abs_le] at hz; omega] at this
    · have h1 : c.workTapes i z = none := by
        by_contra hne; exact hz ((hc i).2 z hne)
      have h2 : d.workTapes i z = none := by
        by_contra hne; exact hz ((hd i).2 z hne)
      rw [h1, h2]
  · funext i
    exact posCode_injOn B (hc i).1 (hd i).1 (congrFun hp i)

end ConfigCount

end MultiTapeTM

namespace FinTM

open MultiTapeTM MultiTapeTM.ConfigCount

/-- The number of codes of configurations of `M` on inputs of length `n` with heads and
nonblank cells in `[-s, s]`: `(|Q| + 1) · (n + 2) · 3^{k(2s+1)} · (2s + 1)^k`. -/
def configBound (M : FinTM Bool) (n s : ℕ) : ℕ :=
  (Fintype.card M.State + 1) * (n + 2) * 3 ^ (M.k * (2 * s + 1)) * (2 * s + 1) ^ M.k

/-- **Space-bounded halting computations are short** [AB09, §4.1.1]: if `M` has halted on
`x` with output `w` by time `t`, having visited at most `s` work cells, then it has halted
with output `w` by time `configBound M |x| s`.

**Proof sketch.** Let `T ≤ t` be the first halting time. Up to time `t` every head lies in
`[-s, s]` (`abs_pos_lt_card_visited`: the visited cells of a tape form an interval around
`0`, of size at most the space used) and so does every nonblank cell
(`mem_visited_of_ne_none`). Hence the cores at times `< T` have pairwise distinct
(`core_injOn`) codes in a finite type of size `configBound M |x| s`, so `T` is at most
that size; the output is frozen after `T`. -/
theorem ComputesInTime.of_spaceUsed_le {M : FinTM Bool} {x w : List Bool} {t s : ℕ}
    (h : M.ComputesInTime x w t) (hs : M.tm.spaceUsed (M.tm.initCfg x) t ≤ s) :
    M.ComputesInTime x w (M.configBound x.length s) := by
  classical
  rw [computesInTime_iff] at h ⊢
  obtain ⟨hhalt, hout⟩ := h
  have hex : ∃ T, (M.tm.runFrom (M.tm.initCfg x) T).state = none := ⟨t, hhalt⟩
  set T := Nat.find hex with hTdef
  have hT : (M.tm.runFrom (M.tm.initCfg x) T).state = none := Nat.find_spec hex
  have hTt : T ≤ t := Nat.find_min' hex hhalt
  have hmin : ∀ t' < T, (M.tm.runFrom (M.tm.initCfg x) t').state ≠ none :=
    fun t' ht' => Nat.find_min hex ht'
  -- bounds on heads and nonblank cells up to time `t`
  have hbound : ∀ t' ≤ t, ∀ i, |(M.tm.runFrom (M.tm.initCfg x) t').workTapePos i| ≤ s ∧
      ∀ z, (M.tm.runFrom (M.tm.initCfg x) t').workTapes i z ≠ none → |z| ≤ s := by
    intro t' ht' i
    have hcard : (M.tm.visitedByTapeHead (M.tm.initCfg x) t i).card ≤ s :=
      (M.tm.spaceUsedByTape_le_spaceUsed _ t i).trans hs
    have hmem : ∀ z ∈ M.tm.visitedByTapeHead (M.tm.initCfg x) t i, |z| ≤ s := fun z hz =>
      ((M.tm.abs_pos_lt_card_visited x t i hz).trans_le (by exact_mod_cast hcard)).le
    refine ⟨hmem _ ?_, fun z hz => hmem z ?_⟩
    · simp only [visitedByTapeHead, Finset.mem_image, Finset.mem_range]
      exact ⟨t', by omega, rfl⟩
    · exact M.tm.visitedByTapeHead_mono _ ht' i (M.tm.mem_visited_of_ne_none x t' i z hz)
  -- injectivity of the code map on times before `T`
  have hinj : Set.InjOn (fun t' => coreCode s (M.tm.runFrom (M.tm.initCfg x) t'))
      (Finset.range T : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    have hc := coreCode_inj s (hbound a (by omega)) (hbound b (by omega)) hab
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h' | h'
    · exact core_injOn M.tm _ T hT hmin h' hb hc
    · exact core_injOn M.tm _ T hT hmin h' ha hc.symm
  have hcardT : T ≤ M.configBound x.length s := by
    have := Finset.card_le_card_of_injOn _ (fun a _ => Finset.mem_univ _) hinj
    simp only [Finset.card_range, Finset.card_univ, Fintype.card_prod, Fintype.card_option,
      Fintype.card_fin, Fintype.card_pi, Finset.prod_const, Fintype.card_bool] at this
    rw [← pow_mul, Nat.mul_comm (2 * s + 1) M.k] at this
    refine this.trans (le_of_eq ?_)
    simp only [configBound]
    ring
  have hfin : M.tm.runFrom (M.tm.initCfg x) (M.configBound x.length s) =
      M.tm.runFrom (M.tm.initCfg x) T := by
    rw [show M.configBound x.length s = T + (M.configBound x.length s - T) by omega,
      runFrom_add, runFrom_of_halt _ hT]
  have hfin' : M.tm.runFrom (M.tm.initCfg x) t = M.tm.runFrom (M.tm.initCfg x) T := by
    rw [show t = T + (t - T) by omega, runFrom_add, runFrom_of_halt _ hT]
  rw [hfin]
  exact ⟨hT, by rw [← hfin']; exact hout⟩

/-- For a logarithmic space bound the configuration count is polynomial:
`configBound M n (c · logSpace n) ≤ A · (n + 1)^d` with `A = 2 (|Q| + 1) 2^{5kc + 3k}` and
`d = 5kc + 1`.

**Proof sketch.** Write `L = ⌊log₂ n⌋`, so `2^L ≤ n + 1`, and `s = c (L + 1)`. Bound
`3 ≤ 2²` and `2s + 1 ≤ 2^{s+1}`; the product `3^{k(2s+1)} (2s+1)^k` is then at most
`2^{5ks + 3k} = (2^L)^{5kc} · 2^{5kc + 3k}`, and `n + 2 ≤ 2 (n + 1)`. -/
theorem configBound_logSpace_le (M : FinTM Bool) (c n : ℕ) :
    M.configBound n (c * Complexity.logSpace n) ≤
      ((Fintype.card M.State + 1) * 2 * 2 ^ (5 * M.k * c + 3 * M.k)) *
        (n + 1) ^ (5 * M.k * c + 1) := by
  set L := Nat.log 2 n with hL
  set s := c * Complexity.logSpace n with hs
  have hsL : s = c * (L + 1) := rfl
  have h2L : 2 ^ L ≤ n + 1 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [hL, h]
    · exact (Nat.pow_log_le_self 2 (by omega)).trans (Nat.le_succ n)
  have h3 : 3 ^ (M.k * (2 * s + 1)) ≤ 2 ^ (2 * (M.k * (2 * s + 1))) := by
    rw [pow_mul 2 2]; exact Nat.pow_le_pow_left (show 3 ≤ 2 ^ 2 by decide) _
  have hs2 : 2 * s + 1 ≤ 2 ^ (s + 1) := by
    have := s.lt_two_pow_self
    rw [pow_succ]; omega
  have h4 : (2 * s + 1) ^ M.k ≤ 2 ^ ((s + 1) * M.k) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left hs2 _
  have hexp : 2 * (M.k * (2 * s + 1)) + (s + 1) * M.k =
      L * (5 * M.k * c) + (5 * M.k * c + 3 * M.k) := by
    rw [hsL]; ring
  have hprod : 3 ^ (M.k * (2 * s + 1)) * (2 * s + 1) ^ M.k ≤
      (n + 1) ^ (5 * M.k * c) * 2 ^ (5 * M.k * c + 3 * M.k) := by
    calc 3 ^ (M.k * (2 * s + 1)) * (2 * s + 1) ^ M.k
        ≤ 2 ^ (2 * (M.k * (2 * s + 1))) * 2 ^ ((s + 1) * M.k) := Nat.mul_le_mul h3 h4
      _ = (2 ^ L) ^ (5 * M.k * c) * 2 ^ (5 * M.k * c + 3 * M.k) := by
        rw [← pow_add, hexp, pow_add, pow_mul]
      _ ≤ (n + 1) ^ (5 * M.k * c) * 2 ^ (5 * M.k * c + 3 * M.k) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left h2L _)
  calc M.configBound n s
      = (Fintype.card M.State + 1) * (n + 2) *
          (3 ^ (M.k * (2 * s + 1)) * (2 * s + 1) ^ M.k) := by
        simp only [configBound]; ring
    _ ≤ (Fintype.card M.State + 1) * (2 * (n + 1)) *
          ((n + 1) ^ (5 * M.k * c) * 2 ^ (5 * M.k * c + 3 * M.k)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hprod
    _ = ((Fintype.card M.State + 1) * 2 * 2 ^ (5 * M.k * c + 3 * M.k)) *
          (n + 1) ^ (5 * M.k * c + 1) := by ring

/-- A computation in logarithmic space is a computation in polynomial time, by the same
machine: if `M` computes `f` in space `c · logSpace`, then `M` computes `f` within
`A · (n + 1)^d` steps. [AB09, p. 112: "logspace computations run in polynomial time"]

**Proof sketch.** `ComputesInTime.of_spaceUsed_le` bounds the halting time by the
configuration count, which `configBound_logSpace_le` bounds by a polynomial. -/
theorem ComputesInSpace.computesFunInTime {M : FinTM Bool} {f : List Bool → List Bool}
    {c : ℕ} (h : M.ComputesInSpace f fun n => c * Complexity.logSpace n) :
    M.ComputesFunInTime f fun n =>
      ((Fintype.card M.State + 1) * 2 * 2 ^ (5 * M.k * c + 3 * M.k)) *
        (n + 1) ^ (5 * M.k * c + 1) := by
  intro x
  obtain ⟨t, ht, hsp⟩ := h x
  exact (ht.of_spaceUsed_le hsp).mono (configBound_logSpace_le M c x.length)

end FinTM

end Turing

namespace Complexity

open Turing

/-- **`L ⊆ P`** [AB09, Thm 4.2 with `S(n) = log n`; p. 112]: a language decided in
logarithmic space is decided in polynomial time — by the same machine.

**Proof sketch.** `Turing.FinTM.ComputesInSpace.computesFunInTime` turns the logspace
decider into a decider within `A · (n + 1)^d` steps; conclude with `Complexity.mem_P_iff`. -/
theorem LOGSPACE_subset_P : LOGSPACE ⊆ P := by
  rintro L ⟨c, M, hM⟩
  rw [mem_P_iff]
  exact ⟨_, _, M, FinTM.ComputesInSpace.computesFunInTime hM⟩

/-- A function computed by a machine in logarithmic space is polynomial-time computable.
[AB09, p. 112] -/
theorem polyTimeComputable_of_computesInSpace {f : List Bool → List Bool} {M : FinTM Bool}
    {c : ℕ} (h : M.ComputesInSpace f fun n => c * logSpace n) : PolyTimeComputable f :=
  ⟨M, _, _, FinTM.ComputesInSpace.computesFunInTime h⟩

end Complexity

```


## ===== TCSlib/Complexity/SpaceComplexity/Machines/Layout.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Tactic.Ring
import TCSlib.Complexity.TuringMachine.Simulation
import TCSlib.Complexity.TuringMachine.Encoding

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Virtual-input layout for subroutine calls

When a logspace machine calls a decider on an input it cannot afford to write down, it
presents a *virtual input* assembled from pieces it does have: a part of its own input and
short words held on work tapes [AB09, proof of Lemma 4.17, Fig. 4.3]. This file fixes the
shape of such virtual inputs and the bookkeeping of a head walking over them, as pure list
and arithmetic facts; the machine that realizes the walk is in
`TCSlib.Complexity.SpaceComplexity.Machines.Gadget`.

A virtual input is a list of *segments* `(w, d)`, a word `w` rendered doubled (`d = true`,
each bit written twice) or plain, joined by the separator `[false, true]`. With two
segments `[(x, true), (y, false)]` this is exactly `Turing.pairEncode x y`.

A head on the virtual input is described by its segment `s` and a *track position*
(`TPos`): the left end of the segment (the cell before its first rendered bit), a cell
`c` of the underlying word together with a parity bit (which of the two copies, for a
doubled segment), or its right end (the cell after its last rendered bit). The left end of
segment `s + 1` is the last separator bit of segment `s`'s separator and its right end the
first; the left end of segment `0` and the right end of the last segment are the two
blank cells around the virtual input.

## Main definitions

* `Complexity.LogProg.vword` — the virtual input of a segment list.
* `Complexity.LogProg.vpos` — the (shifted, as in `Turing.Cfg.inputPos`) virtual position
  of a track position.
* `Complexity.LogProg.tmove` — the track position after a head move.

## Main results

* `Complexity.LogProg.vpos_tmove` — `tmove` implements the clamped input-head move of the
  machine model on the virtual input.
* `Complexity.LogProg.inputSymbol_vpos` — the symbol read at a track position.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.3, proof of Lemma 4.17.)
-/

namespace Complexity.LogProg

open Turing

-- The doubling `Turing.dbl`, `Turing.getElem?_dbl` and `Turing.pairEncode_eq_dbl` live in
-- `TCSlib.Complexity.TuringMachine.Encoding`.

/-- A segment of a virtual input: a word, and whether it is rendered doubled. -/
abbrev Seg := List Bool × Bool

/-- The rendering of a segment. -/
def render (s : Seg) : List Bool := if s.2 then dbl s.1 else s.1

/-- The length of the rendering of a segment. -/
def rlen (s : Seg) : ℕ := if s.2 then 2 * s.1.length else s.1.length

/-- A doubled segment renders to twice its word's length. -/
@[simp] lemma rlen_true (w : List Bool) : rlen (w, true) = 2 * w.length := rfl
/-- A plain segment renders to its word's length. -/
@[simp] lemma rlen_false (w : List Bool) : rlen (w, false) = w.length := rfl

/-- The rendering of a segment has length `rlen`. -/
@[simp] lemma length_render (s : Seg) : (render s).length = rlen s := by
  unfold render rlen; split <;> simp

/-- The virtual input of a nonempty segment list: the renderings joined by `[false, true]`. -/
def vword : List Seg → List Bool
  | [] => []
  | [s] => render s
  | s :: t :: rest => render s ++ [false, true] ++ vword (t :: rest)

/-- The offset of segment `i` in the virtual input. -/
def off : List Seg → ℕ → ℕ
  | _, 0 => 0
  | [], _ + 1 => 0
  | s :: rest, i + 1 => rlen s + 2 + off rest i

/-- Segment `i`, with a default beyond the list. -/
def seg (segs : List Seg) (i : ℕ) : Seg := segs.getD i ([], false)

/-- The segment `0` of `s :: rest` is `s`. -/
@[simp] lemma seg_cons_zero (s : Seg) (rest : List Seg) : seg (s :: rest) 0 = s := rfl
/-- The segment `i + 1` of `s :: rest` is segment `i` of `rest`. -/
@[simp] lemma seg_cons_succ (s : Seg) (rest : List Seg) (i : ℕ) :
    seg (s :: rest) (i + 1) = seg rest i := rfl

/-- The next offset is past the segment and its separator. -/
lemma off_succ (segs : List Seg) (i : ℕ) (hi : i + 1 < segs.length) :
    off segs (i + 1) = off segs i + rlen (seg segs i) + 2 := by
  induction segs generalizing i with
  | nil => simp at hi
  | cons s rest ih =>
    cases i with
    | zero => simp [off]
    | succ i =>
      simp only [off, seg_cons_succ]
      rw [ih i (by simp at hi; omega)]
      ring

/-- The virtual input ends with the last segment. -/
lemma length_vword (segs : List Seg) (h : segs ≠ []) :
    (vword segs).length = off segs (segs.length - 1) + rlen (seg segs (segs.length - 1)) := by
  induction segs with
  | nil => exact absurd rfl h
  | cons s rest ih =>
    cases rest with
    | nil => simp [vword, off, seg]
    | cons t rest' =>
      have := ih (by simp)
      simp only [vword, List.length_append, length_render, List.length_cons] at this ⊢
      simp only [Nat.add_sub_cancel, off, seg_cons_succ]
      simp only [Nat.add_sub_cancel] at this
      rw [this]
      cases rest'.length <;> simp [off]; ring

/-- Inside segment `i`, the virtual input reads the segment's rendering: cell `off segs i + k` holds
letter `k` of `render (seg segs i)`.

**Proof sketch.** Induction on the segment list: segment `0` is the start of the virtual input,
and segment `i + 1` is segment `i` of the rest after the first rendering and its separator,
whose length shifts the offset. -/
lemma getElem?_vword_seg (segs : List Seg) (i k : ℕ) (hi : i < segs.length)
    (hk : k < rlen (seg segs i)) :
    (vword segs)[off segs i + k]? = (render (seg segs i))[k]? := by
  induction segs generalizing i with
  | nil => simp at hi
  | cons s rest ih =>
    cases rest with
    | nil =>
      have : i = 0 := by simp at hi; omega
      subst this; simp [vword, off]
    | cons t rest' =>
      cases i with
      | zero =>
        simp only [vword, off, seg_cons_zero, Nat.zero_add] at hk ⊢
        rw [List.append_assoc, List.getElem?_append_left (by simpa using hk)]
      | succ i =>
        simp only [vword, off, seg_cons_succ] at hk ⊢
        rw [show rlen s + 2 + off (t :: rest') i + k = (render s ++ [false, true]).length +
          (off (t :: rest') i + k) by simp; ring, List.getElem?_append_right (by simp)]
        simp only [Nat.add_sub_cancel_left]
        exact ih i (by simp at hi ⊢; omega) hk

/-- The separator `0 1` after segment `i` of a virtual input sits right after that segment's
rendering.

**Proof sketch.** Induction on the segment list: for `i = 0` the virtual input is the first
rendering followed by `[false, true]`; for `i + 1` drop the first rendering and its separator,
shifting the offsets by their length. -/
lemma getElem?_vword_sep (segs : List Seg) (i : ℕ) (hi : i + 1 < segs.length) :
    (vword segs)[off segs i + rlen (seg segs i)]? = some false ∧
    (vword segs)[off segs i + rlen (seg segs i) + 1]? = some true := by
  induction segs generalizing i with
  | nil => simp at hi
  | cons s rest ih =>
    cases rest with
    | nil => simp at hi
    | cons t rest' =>
      cases i with
      | zero =>
        simp only [vword, off, seg_cons_zero, Nat.zero_add]
        constructor
        · rw [List.append_assoc, List.getElem?_append_right (by simp)]; simp
        · rw [List.append_assoc, List.getElem?_append_right (by simp)]; simp
      | succ i =>
        simp only [vword, off, seg_cons_succ]
        have h := ih i (by simp at hi ⊢; omega)
        constructor
        · rw [show rlen s + 2 + off (t :: rest') i + rlen (seg (t :: rest') i) =
            (render s ++ [false, true]).length + (off (t :: rest') i +
              rlen (seg (t :: rest') i)) by simp; ring, List.getElem?_append_right (by simp)]
          simpa using h.1
        · rw [show rlen s + 2 + off (t :: rest') i + rlen (seg (t :: rest') i) + 1 =
            (render s ++ [false, true]).length + (off (t :: rest') i +
              rlen (seg (t :: rest') i) + 1) by simp; ring,
            List.getElem?_append_right (by simp)]
          simpa using h.2

/-! ## Track positions -/

/-- A position of a head on a segment: its left end, a cell of the underlying word with a
parity (the copy, for doubled segments), or its right end. -/
inductive TPos where
  | left
  | cell (c : ℕ) (p : Bool)
  | right
  deriving DecidableEq

/-- The underlying word length of segment `s`. -/
def wlen (segs : List Seg) (s : ℕ) : ℕ := (seg segs s).1.length

/-- A track position is valid when its cell lies in the word. -/
def TPos.Valid (segs : List Seg) (s : ℕ) : TPos → Prop
  | .cell c _ => c < wlen segs s
  | _ => True

/-- The rendered offset of a cell inside its segment. -/
def cellOff (segs : List Seg) (s c : ℕ) (p : Bool) : ℕ :=
  if (seg segs s).2 then 2 * c + p.toNat else c

/-- The virtual position (`inputPos`-style: `0` is the left blank, cell `j` of the virtual
input is position `j + 1`) of a track position. -/
def vpos (segs : List Seg) (s : ℕ) : TPos → ℕ
  | .left => off segs s
  | .cell c p => off segs s + 1 + cellOff segs s c p
  | .right => off segs s + 1 + rlen (seg segs s)

/-- The rendered offset of a cell of a segment's word lies within the segment's rendering. -/
lemma cellOff_lt (segs : List Seg) (s c : ℕ) (p : Bool) (hc : c < wlen segs s) :
    cellOff segs s c p < rlen (seg segs s) := by
  unfold cellOff rlen
  unfold wlen at hc
  generalize seg segs s = sg at *
  obtain ⟨w, d⟩ := sg
  cases d <;> cases p <;> simp at hc ⊢ <;> omega

/-- The track position after a head move by `m` (`tmove`'s first component is the new
segment). -/
def tmove (segs : List Seg) (s : ℕ) : TPos → SignType → ℕ × TPos
  | tp, .zero => (s, tp)
  | .cell c p, .pos =>
    if (seg segs s).2 ∧ p = false then (s, .cell c true)
    else if c + 1 < wlen segs s then (s, .cell (c + 1) false) else (s, .right)
  | .cell c p, .neg =>
    if (seg segs s).2 ∧ p = true then (s, .cell c false)
    else if c = 0 then (s, .left) else (s, .cell (c - 1) true)
  | .right, .pos => if s + 1 < segs.length then (s + 1, .left) else (s, .right)
  | .right, .neg => if wlen segs s = 0 then (s, .left) else (s, .cell (wlen segs s - 1) true)
  | .left, .pos => if wlen segs s = 0 then (s, .right) else (s, .cell 0 false)
  | .left, .neg => if s = 0 then (s, .left) else (s - 1, .right)

/-- `tmove` preserves validity and the segment bound. -/
lemma tmove_valid (segs : List Seg) (s : ℕ) (hs : s < segs.length) (tp : TPos)
    (htp : tp.Valid segs s) (m : SignType) :
    (tmove segs s tp m).1 < segs.length ∧
      (tmove segs s tp m).2.Valid segs (tmove segs s tp m).1 := by
  cases m <;> cases tp <;> simp only [tmove] <;> (try split_ifs) <;>
    simp_all [TPos.Valid] <;> omega

/-- The virtual input's length in terms of the last segment. -/
lemma vpos_right_last (segs : List Seg) (s : ℕ) (hs : s + 1 = segs.length) :
    vpos segs s .right = (vword segs).length + 1 := by
  rw [length_vword segs (by rintro rfl; simp at hs)]
  simp only [vpos, show segs.length - 1 = s by omega]
  ring

/-- Every segment ends inside the virtual input. -/
lemma off_add_rlen_le (segs : List Seg) (j : ℕ) (hj : j < segs.length) :
    off segs j + rlen (seg segs j) ≤ (vword segs).length := by
  induction segs generalizing j with
  | nil => simp at hj
  | cons s rest ih =>
    cases rest with
    | nil =>
      have : j = 0 := by simp at hj; omega
      subst this; simp [vword, off]
    | cons t rest' =>
      cases j with
      | zero => simp [vword, off]
      | succ j =>
        have := ih j (by simp at hj ⊢; omega)
        simp only [vword, off, seg_cons_succ, List.length_append, length_render,
          List.length_cons, List.length_nil] at this ⊢
        omega

/-- The clamped input move, numerically. -/
lemma moveInputPos_val (N p : ℕ) (hp : p < N + 2) (m : SignType) :
    (moveInputPos (n := N) ⟨p, hp⟩ m).val =
      match m with
      | .zero => p
      | .pos => min (p + 1) (N + 1)
      | .neg => p - 1 := by
  cases m <;> simp only [moveInputPos, SignType.zero_eq_zero, SignType.coe_zero,
    SignType.pos_eq_one, SignType.coe_one, SignType.neg_eq_neg_one, SignType.coe_neg_one] <;>
    split <;> simp_all <;> omega

/-- `tmove` implements the clamped head move: the virtual position after the move is the
old one moved by `m`, clamped to `[0, |V| + 1]`.

**Proof sketch.** Case analysis on the track position and the move. Inside a word the
rendered offset changes by one (doubled segments switch copies before cells). From an end
of a segment the head passes to the neighbouring separator bit, which is the opposite end
of the neighbouring segment (`off_succ`); the outermost ends clamp (`vpos_right_last`). -/
lemma vpos_tmove (segs : List Seg) (s : ℕ) (hs : s < segs.length) (tp : TPos)
    (htp : tp.Valid segs s) (m : SignType) (hlt : vpos segs s tp < (vword segs).length + 2) :
    vpos segs (tmove segs s tp m).1 (tmove segs s tp m).2 =
      (moveInputPos (n := (vword segs).length) ⟨vpos segs s tp, hlt⟩ m).val := by
  rw [moveInputPos_val]
  have F1 := off_add_rlen_le segs s hs
  have F2 : s + 1 < segs.length → off segs (s + 1) = off segs s + rlen (seg segs s) + 2 ∧
      off segs (s + 1) + rlen (seg segs (s + 1)) ≤ (vword segs).length := fun h =>
    ⟨off_succ segs s h, off_add_rlen_le segs (s + 1) h⟩
  have F3 : s + 1 = segs.length → off segs s + rlen (seg segs s) = (vword segs).length := by
    intro h; have := vpos_right_last segs s h; simp only [vpos] at this; omega
  have F4 : 0 < s → off segs s = off segs (s - 1) + rlen (seg segs (s - 1)) + 2 := by
    intro h
    have := off_succ segs (s - 1) (by omega)
    rwa [Nat.sub_add_cancel h] at this
  have F5 : 0 < s → off segs (s - 1) + rlen (seg segs (s - 1)) ≤ (vword segs).length :=
    fun h => off_add_rlen_le segs (s - 1) (by omega)
  unfold TPos.Valid at htp
  generalize hsg : seg segs s = sg at *
  obtain ⟨w, d⟩ := sg
  unfold wlen at htp
  rw [hsg] at htp
  dsimp only at htp
  cases m with
  | zero => simp only [tmove]
  | pos =>
    cases tp with
    | left =>
      simp only [tmove, wlen, hsg]
      split_ifs with h <;>
        cases d <;> simp only [vpos, cellOff, rlen_true, rlen_false, hsg, ↓reduceIte, Bool.false_eq_true,
          Bool.toNat_false] at * <;> omega
    | cell c p =>
      simp only [tmove, wlen, hsg]
      split_ifs with h1 h2 <;>
        cases d <;> cases p <;> simp only [vpos, cellOff, rlen_true, rlen_false, hsg, ↓reduceIte,
          Bool.false_eq_true, Bool.true_eq_false, Bool.toNat_false, Bool.toNat_true, and_true,
          and_false, not_true, not_false_eq_true] at * <;> omega
    | right =>
      simp only [tmove]
      split_ifs with h
      · obtain ⟨e1, e2⟩ := F2 h
        simp only [vpos]
        rw [e1]
        cases d <;> simp only [vpos, rlen_true, rlen_false, hsg] at * <;>
          omega
      · have := F3 (by omega)
        cases d <;> simp only [vpos, rlen_true, rlen_false, hsg] at * <;>
          omega
  | neg =>
    cases tp with
    | left =>
      simp only [tmove]
      split_ifs with h
      · subst h; simp [vpos, off]
      · have e := F4 (by omega)
        simp only [vpos] at hlt ⊢
        rw [e]
        omega
    | cell c p =>
      simp only [tmove, hsg]
      split_ifs with h1 h2 <;>
        cases d <;> cases p <;> simp only [vpos, cellOff, rlen_true, rlen_false, hsg, ↓reduceIte,
          Bool.false_eq_true, Bool.toNat_false, Bool.toNat_true, and_true,
          and_false, not_true, not_false_eq_true] at * <;> omega
    | right =>
      simp only [tmove, wlen, hsg]
      split_ifs with h <;>
        cases d <;> simp only [vpos, cellOff, rlen_true, rlen_false, hsg, ↓reduceIte, Bool.false_eq_true,
          Bool.toNat_true] at * <;> omega

/-- The symbol of the virtual input at a track position. -/
def vsym (segs : List Seg) (s : ℕ) : TPos → Option Bool
  | .left => if s = 0 then none else some true
  | .cell c _ => (seg segs s).1[c]?
  | .right => if s + 1 < segs.length then some false else none

/-- The input symbol read at a configuration whose input head is at a track position is
`vsym`.

**Proof sketch.** Unfold the input symbol at position `vpos segs s tp`. A cell position falls
inside segment `s`'s rendering (`cellOff_lt`), giving its letter. A left or right blank position
falls on the end marker, on the separator `0 1` (`getElem?_vword_sep`) or past the end, which is
`vsym`'s case split. -/
lemma inputSymbol_vpos {k : ℕ} {S : Type} (segs : List Seg) (s : ℕ) (hs : s < segs.length)
    (tp : TPos) (htp : tp.Valid segs s) (cfg : Cfg k Bool S (vword segs))
    (hpos : cfg.inputPos.val = vpos segs s tp) : cfg.inputSymbol = vsym segs s tp := by
  have hgen : ∀ j, cfg.inputPos.val = j + 1 → j ≤ (vword segs).length →
      cfg.inputSymbol = (vword segs)[j]? := fun j hj hl => FinTM.inputSymbol_at cfg j hl hj
  have hlt := cfg.inputPos.isLt
  cases tp with
  | left =>
    simp only [vpos, vsym] at hpos ⊢
    split_ifs with h
    · subst h
      have hz : cfg.inputPos = 0 := Fin.ext (by simpa [off] using hpos)
      simp [Cfg.inputSymbol, hz]
    · obtain ⟨j, rfl⟩ : ∃ j, s = j + 1 := ⟨s - 1, by omega⟩
      rw [off_succ segs j hs] at hpos
      rw [hgen (off segs j + rlen (seg segs j) + 1) (by omega) (by omega)]
      exact (getElem?_vword_sep segs j hs).2
  | cell c p =>
    simp only [TPos.Valid, wlen] at htp
    simp only [vpos, vsym] at hpos ⊢
    have hc := cellOff_lt segs s c p htp
    rw [hgen (off segs s + cellOff segs s c p) (by omega) (by omega),
      getElem?_vword_seg segs s _ hs hc]
    unfold cellOff render
    split
    · exact (getElem?_dbl _ c htp p).trans (List.getElem?_eq_getElem htp).symm
    · rfl
  | right =>
    simp only [vpos, vsym] at hpos ⊢
    split_ifs with h
    · rw [hgen (off segs s + rlen (seg segs s)) (by omega) (by omega)]
      exact (getElem?_vword_sep segs s h).1
    · have hl : s + 1 = segs.length := by omega
      have := vpos_right_last segs s hl
      simp only [vpos] at this
      have hz : cfg.inputPos.val = (vword segs).length + 1 := by omega
      have hne : cfg.inputPos ≠ 0 := by intro h0; rw [h0] at hz; simp at hz
      simp [Cfg.inputSymbol, hne, hz]

end Complexity.LogProg

```


## ===== TCSlib/Complexity/SpaceComplexity/Machines/Program.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import TCSlib.Complexity.SpaceComplexity.Machines.Layout

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Register-tape programs with subroutine calls, and their compiled machines

A *register-tape program* (`Complexity.LogProg.RProg`) is a multi-tape machine over `m`
work tapes (its *registers*) in which some states are *call nodes*: in a call node the
program asks a fixed decider whether a *virtual input* — a part of its own input followed by
the words on some of its registers, `Complexity.LogProg.vword` — belongs to the decider's
language, and continues in one of two states. This is the "pretend there is a virtual input
tape" device of [AB09, proof of Lemma 4.17, Fig. 4.3], packaged once.

This file defines the program model and the machine `Complexity.LogProg.compileTM` that
realizes it: the registers become work tapes `0, …, m - 1`, the decider's work tapes follow,
and a call node is executed by simulating the decider step for step on the virtual input.
The virtual input head is represented by the real input head and the register heads
(`Complexity.LogProg.TPos`), so the simulation needs no extra space.

Related model: `Complexity.CounterProg` (`TCSlib.Complexity.TuringMachine.CounterProg`) is a
goto program over unary counters for the polynomial-time emitters of [AB09, §6.2]. It overlaps
in spirit with the programs here, which store registers in binary (as logarithmic space
requires) and call deciders on virtual inputs; the two are kept separate, and a polynomially
running counter program is simulated by an abstract register machine in
`TCSlib.Complexity.SpaceComplexity.CounterProgSim`.

## Main definitions

* `Complexity.LogProg.Mode` — which part of the real input opens the virtual input: all of
  it, doubled (`whole`, giving `Turing.pairEncode x _`), or its leading run of `1`s, plain
  (`unaryFst`, giving `Turing.pairEncode 1ⁿ _` on inputs `Turing.pairEncode 1ⁿ _`).
* `Complexity.LogProg.CallSpec`, `Complexity.LogProg.RProg` — call nodes and programs.
* `Complexity.LogProg.callSegs` — the segments of the virtual input of a call.
* `Complexity.LogProg.CSt`, `Complexity.LogProg.ctr`, `Complexity.LogProg.compileTM` — the
  compiled machine.
* `Complexity.LogProg.seam` — the compiled configuration of a program configuration.

## Main results

* `Complexity.LogProg.step_seam_prog` — away from call nodes the compiled machine runs the
  program in lockstep.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.3, proof of Lemma 4.17.)
-/

namespace Complexity.LogProg

open Turing

/-- Which part of the real input opens a virtual input. -/
inductive Mode where
  /-- the whole input, doubled: virtual inputs `pairEncode x _` -/
  | whole
  /-- the leading run of `1`s of the input, plain: on an input `pairEncode 1ⁿ _` this is
  `1²ⁿ`, so the virtual inputs are `pairEncode 1ⁿ _` -/
  | unaryFst
  deriving DecidableEq

/-- The first segment of a virtual input. -/
def Mode.seg0 : Mode → List Bool → Seg
  | .whole, x => (x, true)
  | .unaryFst, x => (x.takeWhile (· = true), false)

/-- The register segments: every word but the last is doubled. -/
def argSegs : List (List Bool) → List Seg
  | [] => []
  | [w] => [(w, false)]
  | w :: v :: ws => (w, true) :: argSegs (v :: ws)

/-- There is one register segment per argument word. -/
@[simp] lemma length_argSegs (ws : List (List Bool)) : (argSegs ws).length = ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih => cases ws with
    | nil => rfl
    | cons v ws => simp [argSegs] at ih ⊢; omega

/-- Segment `i` of the register segments is register word `i`, doubled unless last. -/
lemma seg_argSegs (ws : List (List Bool)) (i : ℕ) (hi : i < ws.length) :
    seg (argSegs ws) i = (ws[i], decide (i + 1 < ws.length)) := by
  induction ws generalizing i with
  | nil => simp at hi
  | cons w ws ih =>
    cases ws with
    | nil =>
      have : i = 0 := by simp at hi; omega
      subst this; simp [argSegs, seg]
    | cons v ws =>
      cases i with
      | zero => simp [argSegs, seg]
      | succ i =>
        simp only [argSegs, seg_cons_succ]
        rw [ih i (by simp at hi ⊢; omega)]
        simp

/-- A call node: the decider to call, the virtual-input mode, the argument registers, and
the two continuation states. -/
structure CallSpec (m d : ℕ) (Λ : Type) where
  /-- which decider -/
  dec : Fin d
  /-- the first segment of the virtual input -/
  mode : Mode
  /-- the registers whose words follow, in order -/
  args : List (Fin m)
  /-- the state after a positive answer -/
  yes : Λ
  /-- the state after a negative answer -/
  no : Λ

/-- A register-tape program over `m` registers calling `d` deciders: a machine on the
registers together with the set of call nodes (on which its transition table is ignored). -/
structure RProg (m d : ℕ) (Λ : Type) where
  /-- the transitions at the ordinary nodes -/
  tm : MultiTapeTM m Bool Λ
  /-- the call nodes -/
  call : Λ → Option (CallSpec m d Λ)

/-- The segments of the virtual input of a call on input `x` with register words `W`. -/
def callSegs {m d : ℕ} {Λ : Type} (cs : CallSpec m d Λ) (x : List Bool)
    (W : Fin m → List Bool) : List Seg :=
  cs.mode.seg0 x :: argSegs (cs.args.map W)

/-- A call's virtual input has one segment per argument register plus the leading segment. -/
@[simp] lemma length_callSegs {m d : ℕ} {Λ : Type} (cs : CallSpec m d Λ) (x : List Bool)
    (W : Fin m → List Bool) : (callSegs cs x W).length = cs.args.length + 1 := by
  simp [callSegs]

set_option synthInstance.maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1000 in
/-- The states of the compiled machine. -/
inductive CSt (Λ SD : Type) (m : ℕ) where
  /-- running the program at node `l` -/
  | prog (l : Λ)
  /-- simulating the decider (state `q`) for the call at `l`: current segment `s`, parity,
  direction of the last track move, and the decider's emitted bit so far -/
  | sim (l : Λ) (q : SD) (s : Fin (m + 1)) (par dir : Bool) (res : Option Bool)
  /-- returning: the mandatory first left move of the input rewind -/
  | ret1 (l : Λ) (s : Fin (m + 1)) (dir res : Bool)
  /-- returning: scanning the input head left -/
  | ret2 (l : Λ) (s : Fin (m + 1)) (dir res : Bool)
  /-- returning: restoring the head of argument register number `a` (`scan`: in its left
  scan) -/
  | retR (l : Λ) (s : Fin (m + 1)) (dir res : Bool) (a : Fin m) (scan : Bool)
  deriving DecidableEq, Fintype

/-- Track bookkeeping of one simulated step (a pure function): from the segment `s`, parity,
direction of the last move, whether the current track reads a cell, and the virtual head
move, compute the new segment, parity, direction, and the move of the current track's real
head. `dbl`: the segment is doubled; `last`/`first`: it is the last/first segment. -/
def gstep (dbl last first : Bool) (s : ℕ) (par dir isChar : Bool) :
    SignType → ℕ × Bool × Bool × SignType
  | .zero => (s, par, dir, 0)
  | .pos =>
    if isChar then (if dbl ∧ par = false then (s, true, dir, 0) else (s, false, true, .pos))
    else if dir then (if last then (s, par, dir, 0) else (s + 1, true, false, 0))
    else (s, false, true, .pos)
  | .neg =>
    if isChar then (if dbl ∧ par = true then (s, false, dir, 0) else (s, true, false, .neg))
    else if dir then (s, true, false, .neg)
    else (if first then (s, par, dir, 0) else (s - 1, false, true, 0))

/-- Clamp a natural number into `Fin (m + 1)`. -/
def toFin (m s : ℕ) : Fin (m + 1) := ⟨min s m, by omega⟩

/-- The rendering flag of segment `s` of a call (from the mode for `s = 0`). -/
def segDbl {m d : ℕ} {Λ : Type} (cs : CallSpec m d Λ) (s : ℕ) : Bool :=
  if s = 0 then decide (cs.mode = .whole) else decide (s < cs.args.length)

/-- The register read by segment `s ≥ 1` (a default otherwise). -/
def segReg {m d : ℕ} {Λ : Type} (cs : CallSpec m d Λ) (s : ℕ) (h : 0 < m) : Fin m :=
  cs.args.getD (s - 1) ⟨0, h⟩

/-- Whether segment `s`'s current reading is a cell of its word: a bit on a register or
on the input in `whole` mode, a `1` in `unaryFst` mode. -/
def isCharRead (mode : Mode) (s : ℕ) (rd : Option Bool) : Bool :=
  if s = 0 ∧ mode = .unaryFst then decide (rd = some true) else rd.isSome

/-- The virtual symbol presented to the decider. -/
def virtSym (mode : Mode) (s nseg : ℕ) (dir : Bool) (rd : Option Bool) : Option Bool :=
  if isCharRead mode s rd then (if s = 0 ∧ mode = .unaryFst then some true else rd)
  else if dir then (if s + 1 = nseg then none else some false)
  else (if s = 0 then none else some true)

/-- The register action of a return step on argument register `r`: move `mv`. -/
def regMove {m : ℕ} (r : Fin m) (mv : SignType) : Fin m → Option (Option Bool) × SignType :=
  fun r' => (none, if r' = r then mv else 0)

/-- The state after finishing argument register `a` of a return: the next argument register,
or back to the program. -/
def nextRet {Λ SD : Type} {m d : ℕ} (cs : CallSpec m d Λ) (l : Λ) (s : Fin (m + 1))
    (dir res : Bool) (a : ℕ) : CSt Λ SD m :=
  if h : a < cs.args.length ∧ a < m then .retR l s dir res ⟨a, h.2⟩ false
  else .prog (if res then cs.yes else cs.no)

section Compile

variable {m d kD : ℕ} {Λ SD : Type}

/-- The idle action on the decider block. -/
def dIdle : Fin kD → Option (Option Bool) × SignType := fun _ => (none, 0)

/-- **The transition table of the compiled machine.** See the module docstring; at a call
node the setup step moves the argument heads one cell left (onto the left blanks of their
words) and starts the decider; a simulated step reads the virtual symbol from the current
track, performs the decider's work-tape actions on the decider block, moves the current
track's real head according to `gstep`, and records the decider's emission; when the decider
halts the return phase rewinds the input head and the argument heads. -/
def ctr (P : RProg m d Λ) (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD) :
    CSt Λ SD m → Option Bool → (Fin (m + kD) → Option Bool) → Action (m + kD) Bool (CSt Λ SD m)
  | .prog l, inp, w =>
    match P.call l with
    | none =>
      let a := P.tm.tr l inp (fun r => w (Fin.castAdd kD r))
      ⟨a.inputTape, Fin.append a.workTapes dIdle, a.output, a.state.map .prog⟩
    | some cs =>
      ⟨0, Fin.append (fun r => (none, if r ∈ cs.args then -1 else 0)) dIdle, none,
        some (.sim l (q0 cs.dec) 0 false true none)⟩
  | .sim l q s par dir res, inp, w =>
    match P.call l with
    | none => ⟨0, fun _ => (none, 0), none, none⟩
    | some cs =>
      let rd : Option Bool :=
        if s.val = 0 then inp
        else if hm : 0 < m then w (Fin.castAdd kD (segReg cs s hm)) else none
      let ic := isCharRead cs.mode s rd
      let vs := virtSym cs.mode s (cs.args.length + 1) dir rd
      let a := D.tr q vs (fun i => w (Fin.natAdd m i))
      let g := gstep (segDbl cs s) (decide (s.val + 1 = cs.args.length + 1))
        (decide (s.val = 0)) s par dir ic a.inputTape
      let res' := res <|> a.output
      ⟨if s.val = 0 then g.2.2.2 else 0,
        Fin.append (fun r => (none, if h : 0 < m then
            (if s.val ≠ 0 ∧ r = segReg cs s h then g.2.2.2 else 0) else 0)) a.workTapes,
        none,
        some (match a.state with
          | some q' => .sim l q' (toFin m g.1) g.2.1 g.2.2.1 res'
          | none => .ret1 l (toFin m g.1) g.2.2.1 (res'.getD false))⟩
  | .ret1 l s dir res, _, _ => ⟨-1, fun _ => (none, 0), none, some (.ret2 l s dir res)⟩
  | .ret2 l s dir res, inp, _ =>
    match inp with
    | some _ => ⟨-1, fun _ => (none, 0), none, some (.ret2 l s dir res)⟩
    | none =>
      match P.call l with
      | none => ⟨0, fun _ => (none, 0), none, none⟩
      | some cs => ⟨1, fun _ => (none, 0), none, some (nextRet cs l s dir res 0)⟩
  | .retR l s dir res a scan, _, w =>
    match P.call l with
    | none => ⟨0, fun _ => (none, 0), none, none⟩
    | some cs =>
      let r := cs.args.getD a a
      let rd := w (Fin.castAdd kD r)
      let leftSide : Bool := decide (s.val < a.val + 1) || (decide (s.val = a.val + 1) && !dir)
      if scan then
        match rd with
        | some _ => ⟨0, Fin.append (regMove r (-1)) dIdle, none, some (.retR l s dir res a true)⟩
        | none => ⟨0, Fin.append (regMove r 1) dIdle, none,
            some (nextRet cs l s dir res (a.val + 1))⟩
      else
        match rd with
        | none =>
          if leftSide then
            ⟨0, Fin.append (regMove r 1) dIdle, none, some (nextRet cs l s dir res (a.val + 1))⟩
          else ⟨0, Fin.append (regMove r (-1)) dIdle, none, some (.retR l s dir res a true)⟩
        | some _ => ⟨0, Fin.append (regMove r (-1)) dIdle, none, some (.retR l s dir res a true)⟩

/-- **The compiled machine** of a program `P` with start node `l₀`, calling the deciders
`D` from the start states `q0 j`. -/
def compileTM (P : RProg m d Λ) (l₀ : Λ) (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD) :
    MultiTapeTM (m + kD) Bool (CSt Λ SD m) where
  q₀ := .prog l₀
  tr := ctr P D q0

/-- The compiled configuration of a program configuration: the program's registers, the
decider block blank with heads at the origin. -/
def seam {x : List Bool} (c : Cfg m Bool Λ x) : Cfg (m + kD) Bool (CSt Λ SD m) x :=
  ⟨c.state.map .prog, c.inputPos, Fin.append c.workTapes (fun _ _ => none),
    Fin.append c.workTapePos (fun _ => 0), c.output⟩

/-- The initial configuration of the compiled machine is the seam of the program's. -/
lemma seam_init (P : RProg m d Λ) (l₀ : Λ) (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD)
    (x : List Bool) :
    (compileTM P l₀ D q0).initCfg x = seam (kD := kD) (Cfg.init (k := m) l₀ x) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i z
    refine Fin.addCases (fun r => ?_) (fun j => ?_) i <;> simp [seam, Cfg.init]
  · funext i
    refine Fin.addCases (fun r => ?_) (fun j => ?_) i <;> simp [seam, Cfg.init]

/-- **Lockstep away from calls**: at a non-call node the compiled machine makes exactly the
program's step.

**Proof sketch.** At a non-call program node the compiled transition is the program's
transition, relabelled (`ctr` on `prog` states), with the decider tapes untouched. Unfold one
step on both sides and compare the components of `seam`. -/
lemma step_seam_prog (P : RProg m d Λ) (l₀ : Λ) (D : MultiTapeTM kD Bool SD)
    (q0 : Fin d → SD) {x : List Bool} (c : Cfg m Bool Λ x) (l : Λ) (hl : c.state = some l)
    (hcall : P.call l = none) :
    (compileTM P l₀ D q0).step (seam c) = seam (P.tm.step c) := by
  have hstate : (seam (kD := kD) (SD := SD) c).state = some (.prog l) := by
    simp [seam, hl]
  unfold MultiTapeTM.step
  rw [hstate, hl]
  have hin : (seam (kD := kD) (SD := SD) c).inputSymbol = c.inputSymbol := rfl
  have hw : (fun r => (seam (kD := kD) (SD := SD) c).workTapeSymbols (Fin.castAdd kD r)) =
      c.workTapeSymbols := by
    funext r; simp [seam, Cfg.workTapeSymbols]
  simp only [compileTM, ctr, hcall, hin, hw]
  refine Cfg.ext ?_ rfl ?_ ?_ rfl
  · simp [seam]
  · funext i z
    refine Fin.addCases (fun r => ?_) (fun j => ?_) i
    · simp only [Action.apply, Fin.append_left, seam]
    · simp [Action.apply, seam, dIdle]
  · funext i
    refine Fin.addCases (fun r => ?_) (fun j => ?_) i
    · simp [Action.apply, seam]
    · simp [Action.apply, seam, dIdle]

/-- A halted program configuration is a halted compiled configuration. -/
lemma seam_state_none {x : List Bool} (c : Cfg m Bool Λ x) (h : c.state = none) :
    (seam (kD := kD) (SD := SD) c).state = none := by
  simp [seam, h]

end Compile

end Complexity.LogProg

```


## ===== TCSlib/Complexity/SpaceComplexity/Machines/Sim.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.Program

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Simulating a decider on a virtual input, step by step

The heart of the compiled machine of `TCSlib.Complexity.SpaceComplexity.Machines.Program`:
while a call is in progress, the compiled machine's configuration is related
(`Complexity.LogProg.SimRel`) to the decider's configuration on the virtual input, and one
compiled step simulates one decider step (`Complexity.LogProg.sim_step`).

The virtual input head is never stored: it is the head of the current segment's *track*
(the real input head for segment `0`, an argument register's head otherwise), read through
the track position bookkeeping of `TCSlib.Complexity.SpaceComplexity.Machines.Layout`.
Heads of segments before the current one rest on their right ends, heads of later segments
on their left ends.

## Main definitions

* `Complexity.LogProg.trackPos` — the real head position of a track position.
* `Complexity.LogProg.TrackRel` — the compiled configuration represents the decider's
  configuration with the virtual head at a given track position.
* `Complexity.LogProg.SimRel`, `Complexity.LogProg.HaltRel` — during the call, and right
  after the decider has halted.

## Main results

* `Complexity.LogProg.gstep_tmove` — the compiled machine's local bookkeeping `gstep`
  implements `tmove`.
* `Complexity.LogProg.sim_step` — one compiled step simulates one decider step.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.3, proof of Lemma 4.17.)
-/

namespace Complexity.LogProg

open Turing

/-- The position of a track head, in register coordinates (word from cell `0`; the input
track is shifted by one). -/
def trackPos (segs : List Seg) (s : ℕ) : TPos → ℤ
  | .left => -1
  | .cell c _ => c
  | .right => wlen segs s

/-- Whether a track position is a cell. -/
def TPos.isCell : TPos → Bool
  | .cell _ _ => true
  | _ => false

/-- The consistency of the stored parity and direction with a track position. -/
def Consistent (segs : List Seg) (s : ℕ) (par dir : Bool) : TPos → Prop
  | .left => dir = false
  | .right => dir = true
  | .cell _ p => (seg segs s).2 = true → p = par

/-- **The local bookkeeping is `tmove`**: `gstep` computes the new segment of `tmove`, a
consistent parity and direction, and moves the current track's head to the new track
position; a change of segment happens only between the touching ends of two neighbouring
segments and moves no head.

**Proof sketch.** Case analysis on the move and the track position; `gstep` sees the track
position through `isCell` and the stored direction (which, by consistency, names the end
of the segment the head is on) and the parity (which, by consistency, is the copy in a
doubled segment). -/
lemma gstep_tmove (segs : List Seg) (s : ℕ) (hs : s < segs.length) (tp : TPos)
    (htp : tp.Valid segs s) (par dir : Bool) (hc : Consistent segs s par dir tp)
    (mv : SignType) :
    let G := gstep (seg segs s).2 (decide (s + 1 = segs.length)) (decide (s = 0)) s par dir
      tp.isCell mv
    let T := tmove segs s tp mv
    G.1 = T.1 ∧ Consistent segs T.1 G.2.1 G.2.2.1 T.2 ∧
      ((G.1 = s ∧ trackPos segs s T.2 = trackPos segs s tp + (G.2.2.2 : ℤ)) ∨
       (G.2.2.2 = 0 ∧ ((G.1 = s + 1 ∧ tp = .right ∧ T.2 = .left) ∨
          (G.1 + 1 = s ∧ tp = .left ∧ T.2 = .right)))) := by
  generalize hsg : seg segs s = sg at *
  obtain ⟨w, dd⟩ := sg
  simp only [TPos.Valid, wlen, hsg] at htp
  cases mv <;> cases tp
  case neg.right =>
    simp only [Consistent] at hc
    subst hc
    simp only [gstep, tmove, TPos.isCell, wlen, hsg, Bool.false_eq_true, ↓reduceIte]
    split_ifs with h
    · simp [trackPos, wlen, hsg, h, Consistent, SignType.neg_eq_neg_one]
    · simp only [trackPos, wlen, hsg, Consistent, SignType.neg_eq_neg_one,
        SignType.coe_neg_one, true_and, implies_true]
      left
      omega
  all_goals
    simp only [Consistent, hsg] at hc
    simp only [gstep, tmove, TPos.isCell, wlen, hsg]
    (try split_ifs) <;>
    first
    | omega
    | (simp [Consistent, trackPos, wlen, hsg, SignType.pos_eq_one,
        SignType.neg_eq_neg_one, SignType.coe_one] at * <;> omega)
    | simp_all

/-- The input symbol under the head, by position: the left blank at `0`, then the input. -/
lemma inputSymbol_eq {k : ℕ} {S : Type} {x : List Bool} (cfg : Cfg k Bool S x) :
    cfg.inputSymbol = if cfg.inputPos.val = 0 then none else x[cfg.inputPos.val - 1]? := by
  have hlt := cfg.inputPos.isLt
  split_ifs with h
  · have hz : cfg.inputPos = 0 := Fin.ext h
    simp [Cfg.inputSymbol, hz]
  · exact FinTM.inputSymbol_at cfg (cfg.inputPos.val - 1) (by omega) (by omega)

/-! ## The segments of a call -/

/-- Inside the leading run of `1`s, the input reads `1`. -/
lemma takeWhile_true_getElem? (x : List Bool) (c : ℕ)
    (hc : c < (x.takeWhile (· = true)).length) : x[c]? = some true := by
  induction x generalizing c with
  | nil => simp at hc
  | cons b x ih =>
    cases b with
    | false => simp at hc
    | true =>
      cases c with
      | zero => rfl
      | succ c =>
        simp only [List.takeWhile_cons, decide_true, ↓reduceIte, List.length_cons] at hc
        simpa using ih c (by omega)

/-- Right after the leading run of `1`s, the input does not read `1`. -/
lemma takeWhile_true_end (x : List Bool) : x[(x.takeWhile (· = true)).length]? ≠ some true := by
  induction x with
  | nil => simp
  | cons b x ih =>
    cases b with
    | false => simp
    | true => simpa using ih

/-- In `whole` mode the leading segment is the input, doubled. -/
lemma Mode.seg0_whole {md : Mode} (h : md = .whole) (x : List Bool) :
    md.seg0 x = (x, true) := by subst h; rfl

/-- In `unaryFst` mode the leading segment is the leading run of `1`s of the input, plain. -/
lemma Mode.seg0_unaryFst {md : Mode} (h : md = .unaryFst) (x : List Bool) :
    md.seg0 x = (x.takeWhile (· = true), false) := by subst h; rfl

section Segs

variable {m d : ℕ} {Λ : Type} (cs : CallSpec m d Λ) (x : List Bool) (W : Fin m → List Bool)

/-- Segment `0` of a call's virtual input is the mode's leading segment. -/
@[simp] lemma seg_callSegs_zero : seg (callSegs cs x W) 0 = cs.mode.seg0 x := rfl

/-- Segment `a + 1` of a call's virtual input is the word of argument register `a`, doubled
unless it is the last. -/
lemma seg_callSegs_succ (a : ℕ) (ha : a < cs.args.length) :
    seg (callSegs cs x W) (a + 1) = (W cs.args[a], decide (a + 1 < cs.args.length)) := by
  simp only [callSegs, seg_cons_succ]
  rw [seg_argSegs _ a (by simpa using ha)]
  simp

/-- `segDbl` tells whether segment `s` of a call's virtual input is doubled. -/
lemma segDbl_eq (s : ℕ) (hs : s < cs.args.length + 1) :
    segDbl cs s = (seg (callSegs cs x W) s).2 := by
  unfold segDbl
  split_ifs with h
  · subst h; simp only [seg_callSegs_zero]; cases cs.mode <;> rfl
  · obtain ⟨a, rfl⟩ : ∃ a, s = a + 1 := ⟨s - 1, by omega⟩
    rw [seg_callSegs_succ cs x W a (by omega)]

/-- The leading segment's word is no longer than the input. -/
lemma wlen_zero_le : wlen (callSegs cs x W) 0 ≤ x.length := by
  simp only [wlen, seg_callSegs_zero]
  cases cs.mode
  · simp [Mode.seg0]
  · simp only [Mode.seg0]; exact (List.takeWhile_prefix _).length_le

/-- `segReg` gives the argument register of segment `s ≥ 1`. -/
lemma segReg_eq (s : ℕ) (h : 0 < m) (h1 : 0 < s) (h2 : s ≤ cs.args.length) :
    segReg cs s h = cs.args[s - 1] := by
  simp [segReg, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show s - 1 < cs.args.length by omega)]

end Segs

/-! ## The simulation relation -/

section Rel

variable {m d kD : ℕ} {Λ SD : Type} {x : List Bool} (c0 : Cfg m Bool Λ x) (l : Λ)
  (cs : CallSpec m d Λ) (W : Fin m → List Bool)

/-- The position of register `r` while the virtual head is at segment `s`, track position
`tp`: argument registers before the current segment rest on their right ends, later ones on
their left ends; other registers keep their positions. -/
def regPos (s : ℕ) (tp : TPos) (r : Fin m) : ℤ :=
  if r ∈ cs.args then
    if cs.args.idxOf r + 1 < s then wlen (callSegs cs x W) (cs.args.idxOf r + 1)
    else if s < cs.args.idxOf r + 1 then -1 else trackPos (callSegs cs x W) s tp
  else c0.workTapePos r

/-- The real input head position while the virtual head is at segment `s`, track position
`tp` (the input track is shifted by one cell). -/
def inPos (cs : CallSpec m d Λ) (x : List Bool) (W : Fin m → List Bool) (s : ℕ) (tp : TPos) :
    ℕ :=
  if s = 0 then (trackPos (callSegs cs x W) 0 tp + 1).toNat else wlen (callSegs cs x W) 0 + 1

/-- The compiled configuration `g` represents the decider configuration `dc` with the
virtual head at segment `s`, track position `tp`; registers hold their call-time contents. -/
structure TrackRel (g : Cfg (m + kD) Bool (CSt Λ SD m) x)
    (dc : Cfg kD Bool SD (vword (callSegs cs x W))) (s : ℕ) (par dir : Bool) (tp : TPos) :
    Prop where
  hs : s < cs.args.length + 1
  valid : tp.Valid (callSegs cs x W) s
  cons : Consistent (callSegs cs x W) s par dir tp
  vpos : dc.inputPos.val = vpos (callSegs cs x W) s tp
  inp : g.inputPos.val = inPos cs x W s tp
  regTape : ∀ r, g.workTapes (Fin.castAdd kD r) = c0.workTapes r
  regPos : ∀ r, g.workTapePos (Fin.castAdd kD r) = regPos c0 cs W s tp r
  dTape : ∀ i, g.workTapes (Fin.natAdd m i) = dc.workTapes i
  dPos : ∀ i, g.workTapePos (Fin.natAdd m i) = dc.workTapePos i
  out : g.output = c0.output

/-- During a call: the compiled machine simulates the live decider configuration `dc`. -/
def SimRel (g : Cfg (m + kD) Bool (CSt Λ SD m) x)
    (dc : Cfg kD Bool SD (vword (callSegs cs x W))) : Prop :=
  ∃ (q : SD) (s : Fin (m + 1)) (par dir : Bool) (tp : TPos),
    g.state = some (.sim l q s par dir dc.output.head?) ∧ dc.state = some q ∧
    TrackRel c0 cs W g dc s par dir tp

/-- Right after the decider halted: the compiled machine enters its return phase. -/
def HaltRel (g : Cfg (m + kD) Bool (CSt Λ SD m) x)
    (dc : Cfg kD Bool SD (vword (callSegs cs x W))) : Prop :=
  ∃ (s : Fin (m + 1)) (par dir : Bool) (tp : TPos),
    g.state = some (.ret1 l s dir (dc.output.head?.getD false)) ∧ dc.state = none ∧
    TrackRel c0 cs W g dc s par dir tp

variable {c0 cs W}

/-- **The track reading**: the compiled machine's reading of the current track classifies
the track position correctly and yields the virtual input symbol there.

**Proof sketch.** Case on the track position. On a cell of a segment the compiled machine reads
the input letter (segment `0`) or the register letter under the register head, which `TrackRel`
ties to the virtual input. On a left or right blank the read symbol is blank, and `isCharRead`
and `virtSym` reconstruct the separator or end symbol from the segment index and direction
(`inputSymbol_vpos`). -/
lemma track_read (hW : ∀ r ∈ cs.args, c0.workTapes r = FinTM.bufferTape (W r))
    (hnd : cs.args.Nodup) {g : Cfg (m + kD) Bool (CSt Λ SD m) x}
    {dc : Cfg kD Bool SD (vword (callSegs cs x W))} {s : ℕ} {par dir : Bool} {tp : TPos}
    (R : TrackRel c0 cs W g dc s par dir tp) :
    let rd : Option Bool :=
      if s = 0 then g.inputSymbol
      else if hm : 0 < m then g.workTapeSymbols (Fin.castAdd kD (segReg cs s hm)) else none
    isCharRead cs.mode s rd = tp.isCell ∧
      virtSym cs.mode s (cs.args.length + 1) dir rd = vsym (callSegs cs x W) s tp := by
  have hval := R.valid
  have hcons := R.cons
  by_cases hs0 : s = 0
  · subst hs0
    have hin := R.inp
    simp only [inPos, ↓reduceIte] at hin
    have hrd : g.inputSymbol = if g.inputPos.val = 0 then none
        else x[g.inputPos.val - 1]? := inputSymbol_eq g
    simp only [↓reduceIte]
    rw [hrd, hin]
    have hw0 := wlen_zero_le cs x W
    cases tp with
    | left =>
      simp only [Consistent] at hcons
      subst hcons
      simp [trackPos, isCharRead, virtSym, vsym, TPos.isCell]
    | cell c p =>
      simp only [TPos.Valid, wlen, seg_callSegs_zero] at hval
      simp only [trackPos, vsym, seg_callSegs_zero, TPos.isCell]
      have hc : ((c : ℤ) + 1).toNat = c + 1 := by omega
      rw [hc]
      simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      cases hm : cs.mode with
      | whole =>
        rw [Mode.seg0_whole hm] at hval
        simp only [Mode.seg0]
        simp [isCharRead, virtSym, hval]
      | unaryFst =>
        rw [Mode.seg0_unaryFst hm] at hval
        simp only [Mode.seg0]
        have hx := takeWhile_true_getElem? x c hval
        have hx' : (x.takeWhile (· = true))[c]? = some true := by
          rw [List.getElem?_eq_getElem hval]
          have := List.mem_takeWhile_imp (List.getElem_mem hval)
          simpa using this
        simp only [isCharRead, virtSym, and_self, ↓reduceIte, hx, decide_true]
        simpa using hx'.symm
    | right =>
      simp only [Consistent] at hcons
      subst hcons
      simp only [trackPos, vsym, TPos.isCell, wlen, seg_callSegs_zero]
      have hc : (((cs.mode.seg0 x).1.length : ℤ) + 1).toNat = (cs.mode.seg0 x).1.length + 1 := by
        omega
      rw [hc]
      simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, length_callSegs]
      have hnot : isCharRead cs.mode 0 x[(cs.mode.seg0 x).1.length]? = false := by
        cases hm : cs.mode with
        | whole => simp [isCharRead, Mode.seg0]
        | unaryFst =>
          simp only [isCharRead, and_self, ↓reduceIte, decide_eq_false_iff_not, Mode.seg0]
          exact takeWhile_true_end x
      refine ⟨hnot, ?_⟩
      simp only [virtSym, hnot, Bool.false_eq_true, ↓reduceIte]
      split_ifs <;> first | rfl | omega
  · obtain ⟨a, rfl⟩ : ∃ a, s = a + 1 := ⟨s - 1, by omega⟩
    have ha : a < cs.args.length := by have := R.hs; omega
    have hm : 0 < m := Fin.pos cs.args[a]
    simp only [Nat.add_one_ne_zero, ↓reduceIte, dif_pos hm]
    rw [segReg_eq cs (a + 1) hm (by omega) (by omega)]
    simp only [Nat.add_sub_cancel]
    have hidx : cs.args.idxOf cs.args[a] = a := List.idxOf_getElem hnd a ha
    have hreg : g.workTapeSymbols (Fin.castAdd kD cs.args[a]) =
        FinTM.bufferTape (W cs.args[a]) (trackPos (callSegs cs x W) (a + 1) tp) := by
      simp only [Cfg.workTapeSymbols, R.regTape, R.regPos, regPos, List.getElem_mem,
        ↓reduceIte, hidx, lt_self_iff_false]
      rw [hW _ (List.getElem_mem ha)]
    rw [hreg]
    have hseg := seg_callSegs_succ cs x W a ha
    cases tp with
    | left =>
      simp only [Consistent] at hcons
      subst hcons
      simp [trackPos, isCharRead, virtSym, vsym, TPos.isCell, FinTM.bufferTape]
    | cell c p =>
      simp only [TPos.Valid, wlen, hseg] at hval
      simp [trackPos, isCharRead, virtSym, vsym, TPos.isCell, FinTM.bufferTape, hseg,
        List.getElem?_eq_getElem hval]
    | right =>
      simp only [Consistent] at hcons
      subst hcons
      simp only [trackPos, wlen, hseg, TPos.isCell]
      have hb : FinTM.bufferTape (W cs.args[a]) ((W cs.args[a]).length : ℤ) = none := by
        simp
      rw [hb]
      simp only [isCharRead, virtSym, vsym, Option.isSome_none,
        ↓reduceIte, length_callSegs]
      simp only [Nat.add_one_ne_zero, false_and, ↓reduceIte, Bool.false_eq_true, true_and]
      split_ifs <;> first | rfl | omega

/-- A valid track position lies between the two ends. -/
lemma trackPos_bounds (segs : List Seg) (s : ℕ) (tp : TPos) (h : tp.Valid segs s) :
    -1 ≤ trackPos segs s tp ∧ trackPos segs s tp ≤ wlen segs s := by
  cases tp <;> simp only [trackPos, TPos.Valid] at h ⊢ <;> omega

/-- The register positions after one simulated step.

**Proof sketch.** Case on the step. Within a segment, only the head of that segment's register
(if any) moves, by `mv`. Crossing between segments (`mv = 0`), the register positions are
unchanged and the track positions at the old and new segments agree. Unfold `regPos` in each
case. -/
lemma regPos_after (hnd : cs.args.Nodup) (s : ℕ) (tp : TPos) (G1 : ℕ) (T2 : TPos)
    (mv : SignType)
    (hcase : (G1 = s ∧ trackPos (callSegs cs x W) s T2 =
        trackPos (callSegs cs x W) s tp + (mv : ℤ)) ∨
      (mv = 0 ∧ ((G1 = s + 1 ∧ tp = .right ∧ T2 = .left) ∨
        (G1 + 1 = s ∧ tp = .left ∧ T2 = .right))))
    (r : Fin m) (hm : 0 < m) (hsl : s ≤ cs.args.length) :
    regPos c0 cs W s tp r + (if s ≠ 0 ∧ r = segReg cs s hm then (mv : ℤ) else 0) =
      regPos c0 cs W G1 T2 r := by
  have hseg : ∀ (h0 : s ≠ 0), segReg cs s hm = cs.args[s - 1]'(by omega) := fun h0 =>
    segReg_eq cs s hm (by omega) hsl
  by_cases hr : r ∈ cs.args
  · have hidx := List.idxOf_lt_length_of_mem hr
    have hget : cs.args[cs.args.idxOf r] = r := List.getElem_idxOf hidx
    -- `r` is the current register iff its index is `s - 1`
    have hcur : (s ≠ 0 ∧ r = segReg cs s hm) ↔ cs.args.idxOf r + 1 = s := by
      constructor
      · rintro ⟨h0, rfl⟩
        rw [hseg h0, List.idxOf_getElem hnd]; omega
      · intro h
        refine ⟨by omega, ?_⟩
        rw [hseg (by omega)]
        conv_lhs => rw [← hget]
        congr 1; omega
    simp only [regPos, hr, ↓reduceIte]
    rcases hcase with ⟨rfl, ht⟩ | ⟨rfl, ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩⟩
    · by_cases hc : cs.args.idxOf r + 1 = G1
      · rw [if_pos (hcur.mpr hc)]
        simp only [show ¬ (cs.args.idxOf r + 1 < G1) by omega, ↓reduceIte,
          show ¬ (G1 < cs.args.idxOf r + 1) by omega, ht]
      · rw [if_neg (fun h => hc (hcur.mp h))]
        split_ifs <;> first | rfl | omega
    · simp only [SignType.coe_zero, ite_self, add_zero]
      split_ifs <;> (try simp only [trackPos]) <;>
        first | rfl | omega | (rw [show cs.args.idxOf r + 1 = s by omega])
    · simp only [SignType.coe_zero, ite_self, add_zero]
      split_ifs <;> (try simp only [trackPos]) <;>
        first | rfl | omega | (rw [show cs.args.idxOf r + 1 = G1 by omega])
  · have hne : ¬ (s ≠ 0 ∧ r = segReg cs s hm) := by
      rintro ⟨h0, rfl⟩
      rw [hseg h0] at hr
      exact hr (List.getElem_mem _)
    simp only [regPos, hr, ↓reduceIte, hne, add_zero]

/-- The input head position after one simulated step.

**Proof sketch.** Case on the step. Within segment `0` the input head moves by `mv`, and within
other segments it stays. Crossing between segments it stays, and the input positions of the two
adjacent track positions agree. Unfold `inPos` in each case. -/
lemma inPos_after (s : ℕ) (tp : TPos) (htp : tp.Valid (callSegs cs x W) s) (G1 : ℕ) (T2 : TPos)
    (hT2 : T2.Valid (callSegs cs x W) G1) (mv : SignType)
    (hcase : (G1 = s ∧ trackPos (callSegs cs x W) s T2 =
        trackPos (callSegs cs x W) s tp + (mv : ℤ)) ∨
      (mv = 0 ∧ ((G1 = s + 1 ∧ tp = .right ∧ T2 = .left) ∨
        (G1 + 1 = s ∧ tp = .left ∧ T2 = .right))))
    (p : Fin (x.length + 2)) (hp : p.val = inPos cs x W s tp) :
    (moveInputPos p (if s = 0 then mv else 0)).val = inPos cs x W G1 T2 := by
  have hw0 := wlen_zero_le cs x W
  rcases hcase with ⟨rfl, ht⟩ | ⟨rfl, hc⟩
  · by_cases hs0 : G1 = 0
    · subst hs0
      simp only [↓reduceIte, inPos] at hp ⊢
      have hb := trackPos_bounds _ 0 tp htp
      have hb' := trackPos_bounds _ 0 T2 hT2
      have hpv : p = ⟨p.val, p.isLt⟩ := rfl
      rw [hpv, moveInputPos_val]
      cases mv <;> simp only [SignType.zero_eq_zero, SignType.coe_zero, SignType.pos_eq_one,
        SignType.coe_one, SignType.neg_eq_neg_one, SignType.coe_neg_one] at ht ⊢ <;> omega
    · simp only [hs0, ↓reduceIte, inPos] at hp ⊢
      rw [moveInputPos_zero, hp]
  · rcases hc with ⟨rfl, rfl, rfl⟩ | ⟨h1, rfl, rfl⟩
    · simp only [ite_self, moveInputPos_zero, hp, inPos,
        Nat.add_one_ne_zero, ↓reduceIte]
      split_ifs with h
      · subst h; simp [trackPos]
      · rfl
    · simp only [moveInputPos_zero, hp, inPos,
        show s ≠ 0 by omega, ↓reduceIte]
      split_ifs with h
      · subst h; simp [trackPos]
      · rfl

/-- The head of an appended optional emission. -/
lemma head?_append_toList (l : List Bool) (o : Option Bool) :
    (l ++ o.toList).head? = (l.head? <|> o) := by
  cases l <;> cases o <;> rfl


/-- **One compiled step simulates one decider step.** If the compiled configuration `g`
simulates the live decider configuration `dc`, then after one step of each, `g` simulates
`dc` again, or — if the decider has just halted — `g` has entered its return phase.

**Proof sketch.** The track reading presents the decider's own input symbol
(`track_read`, `inputSymbol_vpos`) and the decider block holds the decider's tapes, so the
compiled machine applies exactly the decider's action to the decider block. The track
bookkeeping `gstep` is `tmove` (`gstep_tmove`), which moves the virtual head as the machine
model does (`vpos_tmove`); the real heads follow (`inPos_after`, `regPos_after`). The
emission is recorded, not written. -/
theorem sim_step {l₀ : Λ} (P : RProg m d Λ) (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD)
    (hcall : P.call l = some cs)
    (hW : ∀ r ∈ cs.args, c0.workTapes r = FinTM.bufferTape (W r)) (hnd : cs.args.Nodup)
    {g : Cfg (m + kD) Bool (CSt Λ SD m) x} {dc : Cfg kD Bool SD (vword (callSegs cs x W))}
    (h : SimRel c0 l cs W g dc) :
    ((D.step dc).state ≠ none →
        SimRel c0 l cs W ((compileTM P l₀ D q0).step g) (D.step dc)) ∧
      ((D.step dc).state = none →
        HaltRel c0 l cs W ((compileTM P l₀ D q0).step g) (D.step dc)) := by
  obtain ⟨q, s, par, dir, tp, hg, hdc, R⟩ := h
  have hlen : cs.args.length ≤ m := by simpa using hnd.length_le_card
  have hsl : s.val < (callSegs cs x W).length := by simpa using R.hs
  have hread := track_read hW hnd R
  have hvs : dc.inputSymbol = vsym (callSegs cs x W) s tp :=
    inputSymbol_vpos _ s hsl tp R.valid dc R.vpos
  have hdr : (fun i => g.workTapeSymbols (Fin.natAdd m i)) = dc.workTapeSymbols := by
    funext i; simp only [Cfg.workTapeSymbols, R.dTape, R.dPos]
  set a := D.tr q dc.inputSymbol dc.workTapeSymbols with ha
  have hDstep : D.step dc = a.apply dc := by
    unfold MultiTapeTM.step; rw [hdc]
  -- the compiled action
  have hdbl := segDbl_eq cs x W s R.hs
  have hgt := gstep_tmove (callSegs cs x W) s hsl tp R.valid par dir R.cons a.inputTape
  simp only [length_callSegs] at hgt
  obtain ⟨hT1, hT2⟩ := tmove_valid (callSegs cs x W) s hsl tp R.valid a.inputTape
  set G := gstep (seg (callSegs cs x W) s).2 (decide (s.val + 1 = cs.args.length + 1))
    (decide (s.val = 0)) s par dir tp.isCell a.inputTape with hGdef
  obtain ⟨hG1, hcons', hcase⟩ := hgt
  set T := tmove (callSegs cs x W) s tp a.inputTape with hTdef
  have hGs : G.1 ≤ m := by rw [hG1]; simp at hT1; omega
  have htoFin : (toFin m G.1).val = G.1 := by simp [toFin]; omega
  have hgstep : (compileTM P l₀ D q0).step g =
      (⟨if s.val = 0 then G.2.2.2 else 0,
        Fin.append (fun r => (none, if h : 0 < m then
            (if s.val ≠ 0 ∧ r = segReg cs s h then G.2.2.2 else 0) else 0)) a.workTapes,
        none,
        some (match a.state with
          | some q' => .sim l q' (toFin m G.1) G.2.1 G.2.2.1 (dc.output.head? <|> a.output)
          | none => .ret1 l (toFin m G.1) G.2.2.1
              ((dc.output.head? <|> a.output).getD false))⟩ :
        Action (m + kD) Bool (CSt Λ SD m)).apply g := by
    unfold MultiTapeTM.step
    rw [hg]
    simp only [compileTM, ctr, hcall]
    rw [hread.1, hread.2, ← hvs, hdr, ← ha, hdbl]
    rfl
  have hout : (D.step dc).output.head? = (dc.output.head? <|> a.output) := by
    rw [hDstep]; simp only [Action.apply]; exact head?_append_toList _ _
  -- the track relation after the step
  have hR' : TrackRel c0 cs W ((compileTM P l₀ D q0).step g) (D.step dc) (toFin m G.1)
      G.2.1 G.2.2.1 T.2 := by
    rw [htoFin]
    have hTv : T.2.Valid (callSegs cs x W) G.1 := by rw [hG1]; exact hT2
    refine ⟨by rw [hG1]; simpa using hT1, hTv, by rw [hG1]; exact hcons', ?_, ?_, ?_, ?_, ?_, ?_,
      ?_⟩
    · -- virtual input head
      rw [hDstep, hG1]
      simp only [Action.apply]
      have hlt : vpos (callSegs cs x W) s tp < (vword (callSegs cs x W)).length + 2 := by
        rw [← R.vpos]; exact dc.inputPos.isLt
      have hp : dc.inputPos = ⟨vpos (callSegs cs x W) s tp, hlt⟩ := Fin.ext R.vpos
      rw [hp, ← vpos_tmove _ s hsl tp R.valid a.inputTape hlt]
    · -- real input head
      rw [hgstep]
      simp only [Action.apply]
      exact inPos_after s tp R.valid G.1 T.2 hTv G.2.2.2 hcase g.inputPos R.inp
    · intro r
      rw [hgstep]
      simp only [Action.apply, Fin.append_left]
      exact R.regTape r
    · intro r
      rw [hgstep]
      simp only [Action.apply, Fin.append_left]
      have hm : 0 < m := Fin.pos r
      rw [dif_pos hm, R.regPos r]
      have key := regPos_after (c0 := c0) hnd s tp G.1 T.2 G.2.2.2 hcase r hm (by have := R.hs; omega)
      rw [← key]
      congr 1
      split_ifs <;> simp
    · intro i
      rw [hgstep, hDstep]
      simp only [Action.apply, Fin.append_right, R.dTape, R.dPos]
    · intro i
      rw [hgstep, hDstep]
      simp only [Action.apply, Fin.append_right, R.dPos]
    · rw [hgstep]
      simp only [Action.apply, Option.toList_none, List.append_nil]
      exact R.out
  constructor
  · intro hlive
    obtain ⟨q', hq'⟩ := Option.ne_none_iff_exists'.mp hlive
    have haq : a.state = some q' := by rw [hDstep] at hq'; simpa [Action.apply] using hq'
    refine ⟨q', toFin m G.1, G.2.1, G.2.2.1, T.2, ?_, hq', hR'⟩
    rw [hgstep]
    simp only [Action.apply, haq, hout]
  · intro hhalt
    have haq : a.state = none := by rw [hDstep] at hhalt; simpa [Action.apply] using hhalt
    refine ⟨toFin m G.1, G.2.1, G.2.2.1, T.2, ?_, hhalt, hR'⟩
    rw [hgstep]
    simp only [Action.apply, haq, hout]

end Rel

end Complexity.LogProg

```


## ===== TCSlib/Complexity/SpaceComplexity/Machines/CallReturn.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.Sim

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The return phase of a subroutine call

The first half of `TCSlib.Complexity.SpaceComplexity.Machines.Call`: compiled configurations
built from their blocks, and the return phase of a call — rewinding the input head and
moving every argument register head back to cell `0`.

## Main definitions

* `Complexity.LogProg.mkCfg` — a compiled configuration from its register and decider
  blocks.

## Main results

* `Complexity.LogProg.ret2_run` — the input rewind of the return.
* `Complexity.LogProg.retR_run` — restoring one argument register head.
* `Complexity.LogProg.regs_run` — restoring all argument register heads.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.3, proof of Lemma 4.17.)
-/

namespace Complexity.LogProg

open Turing

variable {m d kD : ℕ} {Λ SD : Type} {x : List Bool}

/-- A compiled configuration from its register block and decider block. -/
def mkCfg (st : Option (CSt Λ SD m)) (ip : Fin (x.length + 2)) (rt : Fin m → ℤ → Option Bool)
    (rp : Fin m → ℤ) (dt : Fin kD → ℤ → Option Bool) (dp : Fin kD → ℤ) (out : List Bool) :
    Cfg (m + kD) Bool (CSt Λ SD m) x :=
  ⟨st, ip, Fin.append rt dt, Fin.append rp dp, out⟩

/-- The configuration built by `mkCfg st …` is in state `st`. -/
@[simp] lemma mkCfg_state (st : Option (CSt Λ SD m)) (ip : Fin (x.length + 2)) rt rp
    (dt : Fin kD → ℤ → Option Bool) dp out :
    (mkCfg st ip rt rp dt dp out).state = st := rfl

/-- An action moving only the input head and register heads. -/
lemma apply_moves (st : Option (CSt Λ SD m)) (ip : Fin (x.length + 2))
    (rt : Fin m → ℤ → Option Bool) (rp : Fin m → ℤ) (dt : Fin kD → ℤ → Option Bool)
    (dp : Fin kD → ℤ) (out : List Bool) (mvI : SignType) (f : Fin m → SignType)
    (st' : CSt Λ SD m) :
    (⟨mvI, Fin.append (fun r => (none, f r)) dIdle, none, some st'⟩ :
        Action (m + kD) Bool (CSt Λ SD m)).apply (mkCfg st ip rt rp dt dp out) =
      mkCfg (some st') (moveInputPos ip mvI) rt (fun r => rp r + f r) dt dp out := by
  refine Cfg.ext rfl rfl ?_ ?_ (by simp [mkCfg])
  · funext i z
    refine Fin.addCases (fun r => ?_) (fun j => ?_) i <;> simp [mkCfg, dIdle]
  · funext i
    refine Fin.addCases (fun r => ?_) (fun j => ?_) i <;> simp [mkCfg, dIdle]

/-- An action moving one register head. -/
lemma apply_regMove (st : Option (CSt Λ SD m)) (ip : Fin (x.length + 2))
    (rt : Fin m → ℤ → Option Bool) (rp : Fin m → ℤ) (dt : Fin kD → ℤ → Option Bool)
    (dp : Fin kD → ℤ) (out : List Bool) (r : Fin m) (mv : SignType) (st' : CSt Λ SD m) :
    (⟨0, Fin.append (regMove r mv) dIdle, none, some st'⟩ :
        Action (m + kD) Bool (CSt Λ SD m)).apply (mkCfg st ip rt rp dt dp out) =
      mkCfg (some st') ip rt (Function.update rp r (rp r + mv)) dt dp out := by
  have := apply_moves st ip rt rp dt dp out 0 (fun r' => if r' = r then mv else 0) st'
  simp only [moveInputPos_zero] at this
  convert this using 2
  funext r'
  by_cases h : r' = r
  · subst h; simp
  · simp [h]

/-- An action moving only the input head. -/
lemma apply_inputOnly (st : Option (CSt Λ SD m)) (ip : Fin (x.length + 2))
    (rt : Fin m → ℤ → Option Bool) (rp : Fin m → ℤ) (dt : Fin kD → ℤ → Option Bool)
    (dp : Fin kD → ℤ) (out : List Bool) (mvI : SignType) (st' : CSt Λ SD m) :
    (⟨mvI, fun _ => (none, 0), none, some st'⟩ : Action (m + kD) Bool (CSt Λ SD m)).apply
        (mkCfg st ip rt rp dt dp out) =
      mkCfg (some st') (moveInputPos ip mvI) rt rp dt dp out := by
  refine Cfg.ext rfl rfl ?_ ?_ (by simp [mkCfg])
  · funext i z
    refine Fin.addCases (fun r => ?_) (fun j => ?_) i <;> simp [mkCfg]
  · funext i
    refine Fin.addCases (fun r => ?_) (fun j => ?_) i <;> simp [mkCfg]

/-- The seam of a program configuration as a `mkCfg`. -/
lemma seam_eq_mkCfg (c : Cfg m Bool Λ x) :
    seam (kD := kD) (SD := SD) c = mkCfg (c.state.map .prog) c.inputPos c.workTapes
      c.workTapePos (fun _ _ => none) (fun _ => 0) c.output := rfl

/-! ## The return phase -/

section Return

variable (P : RProg m d Λ) (l₀ : Λ) (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD)

/-- The input scan of the return: from position `j ≤ |x|` the head walks left to the left
blank and steps onto the first cell.

**Proof sketch.** Induction on `j`. At a position `j > 0` the input symbol is a letter of the
input, so the head moves left and the state stays `ret2`; at position `0` the left blank sends
the head to position `1` and the machine enters the next return state. No work head moves. -/
lemma ret2_run (l : Λ) (cs : CallSpec m d Λ) (hcall : P.call l = some cs)
    (s : Fin (m + 1)) (dir b : Bool) (rt : Fin m → ℤ → Option Bool) (rp : Fin m → ℤ)
    (dt : Fin kD → ℤ → Option Bool) (dp : Fin kD → ℤ) (out : List Bool) :
    ∀ (j : ℕ) (ip : Fin (x.length + 2)), ip.val = j → j ≤ x.length →
      (∀ t ≤ j + 1, ((compileTM P l₀ D q0).runFrom
          (mkCfg (some (.ret2 l s dir b)) ip rt rp dt dp out) t).workTapePos =
        Fin.append rp dp) ∧
      (compileTM P l₀ D q0).runFrom (mkCfg (some (.ret2 l s dir b)) ip rt rp dt dp out)
          (j + 1) = mkCfg (some (nextRet cs l s dir b 0)) 1 rt rp dt dp out := by
  intro j
  induction j with
  | zero =>
    intro ip hip _
    have hz : ip = 0 := Fin.ext hip
    have hstep : (compileTM P l₀ D q0).step (mkCfg (some (.ret2 l s dir b)) ip rt rp dt dp out) =
        mkCfg (some (nextRet cs l s dir b 0)) 1 rt rp dt dp out := by
      unfold MultiTapeTM.step
      simp only [mkCfg_state]
      have hsym : (mkCfg (some (.ret2 l s dir b)) ip rt rp dt dp out :
          Cfg (m + kD) Bool (CSt Λ SD m) x).inputSymbol = none := by
        simp [Cfg.inputSymbol, mkCfg, hz]
      simp only [compileTM, ctr, hsym, hcall]
      rw [apply_inputOnly]
      congr 1
      rw [hz]; exact Fin.ext (by simp [moveInputPos])
    refine ⟨fun t ht => ?_, by simpa using hstep⟩
    rcases Nat.lt_or_ge t 1 with h | h
    · obtain rfl : t = 0 := by omega
      rfl
    · obtain rfl : t = 1 := by omega
      simp only [MultiTapeTM.runFrom, Function.iterate_one] at hstep ⊢
      rw [hstep]; rfl
  | succ j ih =>
    intro ip hip hj
    have hsym : (mkCfg (some (.ret2 l s dir b)) ip rt rp dt dp out :
        Cfg (m + kD) Bool (CSt Λ SD m) x).inputSymbol = some x[j] :=
      inputSymbolInner j (by simp [mkCfg, hip]; omega) (by omega)
    have hstep : (compileTM P l₀ D q0).step (mkCfg (some (.ret2 l s dir b)) ip rt rp dt dp out) =
        mkCfg (some (.ret2 l s dir b)) (moveInputPos ip (-1)) rt rp dt dp out := by
      unfold MultiTapeTM.step
      simp only [mkCfg_state]
      simp only [compileTM, ctr, hsym]
      rw [apply_inputOnly]
    have hval : (moveInputPos ip (-1)).val = j := by
      rw [show (-1 : SignType) = .neg from rfl, FinTM.moveInputPos_neg_val]; omega
    obtain ⟨ihb, ihr⟩ := ih (moveInputPos ip (-1)) hval (by omega)
    refine ⟨fun t ht => ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos t with h | h
      · subst h; rfl
      · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
        rw [MultiTapeTM.runFrom_succ_eq_step, hstep]
        exact ihb t' (by omega)
    · rw [MultiTapeTM.runFrom_succ_eq_step, hstep]
      exact ihr

/-- The left scan of an argument register in the return: from position `p ∈ [-1, |w|)` the
head walks left to the left blank `-1` and steps onto cell `0`.

**Proof sketch.** Induction on `n = p + 1`. While the head of register `rr` reads a letter of
`w` it moves left; at the left blank `-1` it moves right onto cell `0` and the machine enters
the next return state. Only that head moves, and it stays in `[-1, max p 0]`. -/
lemma retR_scan (l : Λ) (cs : CallSpec m d Λ) (hcall : P.call l = some cs)
    (s : Fin (m + 1)) (dir b : Bool) (a : Fin m) (w : List Bool) (rr : Fin m)
    (hrr : cs.args.getD a a = rr)
    (rt : Fin m → ℤ → Option Bool) (hrt : rt rr = FinTM.bufferTape w)
    (dt : Fin kD → ℤ → Option Bool) (dp : Fin kD → ℤ) (out : List Bool)
    (ip : Fin (x.length + 2)) :
    ∀ (n : ℕ) (rp : Fin m → ℤ), rp (rr) + 1 = n → (n : ℤ) ≤ w.length →
      (∀ t ≤ n + 1, ∀ r, (((compileTM P l₀ D q0).runFrom
          (mkCfg (some (.retR l s dir b a true)) ip rt rp dt dp out) t).workTapePos
            (Fin.castAdd kD r) = rp r ∨
          (r = rr ∧ -1 ≤ ((compileTM P l₀ D q0).runFrom
            (mkCfg (some (.retR l s dir b a true)) ip rt rp dt dp out) t).workTapePos
              (Fin.castAdd kD r) ∧ ((compileTM P l₀ D q0).runFrom
            (mkCfg (some (.retR l s dir b a true)) ip rt rp dt dp out) t).workTapePos
              (Fin.castAdd kD r) ≤ max (rp r) 0)) ∧
        ((compileTM P l₀ D q0).runFrom
          (mkCfg (some (.retR l s dir b a true)) ip rt rp dt dp out) t).workTapePos
            ∘ Fin.natAdd m = dp) ∧
      (compileTM P l₀ D q0).runFrom
          (mkCfg (some (.retR l s dir b a true)) ip rt rp dt dp out) (n + 1) =
        mkCfg (some (nextRet cs l s dir b (a.val + 1))) ip rt
          (Function.update rp (rr) 0) dt dp out := by
  intro n
  induction n with
  | zero =>
    intro rp hp _
    have hpos : rp (rr) = -1 := by omega
    have hrd : (mkCfg (some (.retR l s dir b a true)) ip rt rp dt dp out :
        Cfg (m + kD) Bool (CSt Λ SD m) x).workTapeSymbols (Fin.castAdd kD (rr)) =
          none := by
      simp [Cfg.workTapeSymbols, mkCfg, hrt, hpos]
    have hstep : (compileTM P l₀ D q0).step
        (mkCfg (some (.retR l s dir b a true)) ip rt rp dt dp out) =
        mkCfg (some (nextRet cs l s dir b (a.val + 1))) ip rt
          (Function.update rp (rr) 0) dt dp out := by
      unfold MultiTapeTM.step
      simp only [mkCfg_state]
      simp only [compileTM, ctr, hcall, hrr, hrd, ↓reduceIte]
      rw [apply_regMove]
      congr 1
      rw [hpos]; simp
    refine ⟨fun t ht r => ?_, ?_⟩
    · rcases Nat.lt_or_ge t 1 with h | h
      · obtain rfl : t = 0 := by omega
        exact ⟨Or.inl (by simp [mkCfg]), by funext i; simp [mkCfg]⟩
      · obtain rfl : t = 1 := by omega
        simp only [MultiTapeTM.runFrom, Function.iterate_one, hstep]
        refine ⟨?_, by funext i; simp [mkCfg]⟩
        by_cases hr : r = rr
        · subst hr; right; simp [mkCfg, hpos]
        · left; simp [mkCfg, hr]
    · simpa using hstep
  | succ n ih =>
    intro rp hp hn
    have hpos : rp (rr) = n := by omega
    have hrd : (mkCfg (some (.retR l s dir b a true)) ip rt rp dt dp out :
        Cfg (m + kD) Bool (CSt Λ SD m) x).workTapeSymbols (Fin.castAdd kD (rr)) =
          some w[n] := by
      simp [Cfg.workTapeSymbols, mkCfg, hrt, hpos, FinTM.bufferTape,
        List.getElem?_eq_getElem (show n < w.length by omega)]
    set rp' := Function.update rp (rr) (n - 1 : ℤ) with hrp'
    have hstep : (compileTM P l₀ D q0).step
        (mkCfg (some (.retR l s dir b a true)) ip rt rp dt dp out) =
        mkCfg (some (.retR l s dir b a true)) ip rt rp' dt dp out := by
      unfold MultiTapeTM.step
      simp only [mkCfg_state]
      simp only [compileTM, ctr, hcall, hrr, hrd, ↓reduceIte]
      rw [apply_regMove]
      congr 1
      rw [hrp', hpos, sub_eq_add_neg]; simp
    obtain ⟨ihb, ihr⟩ := ih rp' (by simp [hrp']) (by omega)
    refine ⟨fun t ht r => ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos t with h | h
      · subst h; exact ⟨Or.inl (by simp [mkCfg]), by funext i; simp [mkCfg]⟩
      · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
        rw [MultiTapeTM.runFrom_succ_eq_step, hstep]
        obtain ⟨h1, h2⟩ := ihb t' (by omega) r
        refine ⟨?_, h2⟩
        by_cases hr : r = rr
        · subst hr
          right
          rcases h1 with h1 | h1
          · rw [h1]; simp [hrp', hpos]
          · refine ⟨rfl, h1.2.1, h1.2.2.trans ?_⟩
            simp only [hrp', Function.update_self, hpos]
            omega
        · left
          rcases h1 with h1 | h1
          · rw [h1]; simp [hrp', hr]
          · exact absurd h1.1 hr
    · rw [MultiTapeTM.runFrom_succ_eq_step, hstep, ihr]
      congr 1
      funext r
      by_cases hr : r = rr
      · subst hr; simp
      · simp [hrp', hr]

/-- The side test of the return phase for argument register number `a`. -/
def leftSide (s : Fin (m + 1)) (dir : Bool) (a : Fin m) : Bool :=
  decide (s.val < a.val + 1) || (decide (s.val = a.val + 1) && !dir)

/-- Restoring one argument register head: from any position in `[-1, |w|]` (a blank end
being identified by the side test) the head returns to cell `0`.

**Proof sketch.** If the head is on a letter, or on a blank identified as the left end by the
side test, the scan `retR_scan` applies (after at most one step right from `-1`). If it is on
the right blank `|w|`, one step moves it left onto the last letter and `retR_scan` applies from
there. In both cases only the head of `rr` moves, within `[-1, |w|]`. -/
lemma retR_run (l : Λ) (cs : CallSpec m d Λ) (hcall : P.call l = some cs)
    (s : Fin (m + 1)) (dir b : Bool) (a : Fin m) (w : List Bool) (rr : Fin m)
    (hrr : cs.args.getD a a = rr) (rt : Fin m → ℤ → Option Bool)
    (hrt : rt rr = FinTM.bufferTape w) (dt : Fin kD → ℤ → Option Bool) (dp : Fin kD → ℤ)
    (out : List Bool) (ip : Fin (x.length + 2)) (rp : Fin m → ℤ)
    (hp : -1 ≤ rp rr ∧ rp rr ≤ w.length) (hl : rp rr = -1 → leftSide s dir a = true)
    (hrgt : rp rr = w.length → leftSide s dir a = false) :
    ∃ T, (∀ t ≤ T, ∀ r, (((compileTM P l₀ D q0).runFrom
          (mkCfg (some (.retR l s dir b a false)) ip rt rp dt dp out) t).workTapePos
            (Fin.castAdd kD r) = rp r ∨
          (r = rr ∧ -1 ≤ ((compileTM P l₀ D q0).runFrom
            (mkCfg (some (.retR l s dir b a false)) ip rt rp dt dp out) t).workTapePos
              (Fin.castAdd kD r) ∧ ((compileTM P l₀ D q0).runFrom
            (mkCfg (some (.retR l s dir b a false)) ip rt rp dt dp out) t).workTapePos
              (Fin.castAdd kD r) ≤ max (rp r) 0)) ∧
        ((compileTM P l₀ D q0).runFrom
          (mkCfg (some (.retR l s dir b a false)) ip rt rp dt dp out) t).workTapePos
            ∘ Fin.natAdd m = dp) ∧
      (compileTM P l₀ D q0).runFrom
          (mkCfg (some (.retR l s dir b a false)) ip rt rp dt dp out) T =
        mkCfg (some (nextRet cs l s dir b (a.val + 1))) ip rt
          (Function.update rp rr 0) dt dp out := by
  have hread : (mkCfg (some (.retR l s dir b a false)) ip rt rp dt dp out :
      Cfg (m + kD) Bool (CSt Λ SD m) x).workTapeSymbols (Fin.castAdd kD rr) =
        FinTM.bufferTape w (rp rr) := by
    simp [Cfg.workTapeSymbols, mkCfg, hrt]
  by_cases hm1 : rp rr = -1
  · -- on the left blank: one step right
    have hrd : FinTM.bufferTape w (rp rr) = none := by rw [hm1]; simp
    have hstep : (compileTM P l₀ D q0).step
        (mkCfg (some (.retR l s dir b a false)) ip rt rp dt dp out) =
        mkCfg (some (nextRet cs l s dir b (a.val + 1))) ip rt
          (Function.update rp rr 0) dt dp out := by
      unfold MultiTapeTM.step
      simp only [mkCfg_state]
      have hls := hl hm1
      simp only [leftSide] at hls
      simp only [compileTM, ctr, hcall, hrr, hread, hrd, Bool.false_eq_true, ↓reduceIte, hls]
      rw [apply_regMove]
      congr 1
      rw [hm1]; simp
    refine ⟨1, fun t ht r => ?_, by simpa using hstep⟩
    rcases Nat.lt_or_ge t 1 with h | h
    · obtain rfl : t = 0 := by omega
      exact ⟨Or.inl (by simp [mkCfg]), by funext i; simp [mkCfg]⟩
    · obtain rfl : t = 1 := by omega
      simp only [MultiTapeTM.runFrom, Function.iterate_one, hstep]
      refine ⟨?_, by funext i; simp [mkCfg]⟩
      by_cases hr : r = rr
      · subst hr; right; simp [mkCfg, hm1]
      · left; simp [mkCfg, hr]
  · -- otherwise: one step left, then the left scan
    have hn : ∃ n : ℕ, rp rr = n := ⟨(rp rr).toNat, by omega⟩
    obtain ⟨n, hn⟩ := hn
    have hside : FinTM.bufferTape w (rp rr) = none → leftSide s dir a = false := by
      intro hnone
      apply hrgt
      by_contra hne
      have hlt : n < w.length := by omega
      rw [hn] at hnone
      simp [FinTM.bufferTape, List.getElem?_eq_getElem hlt] at hnone
    set rp' := Function.update rp rr (rp rr - 1) with hrp'
    have hstep : (compileTM P l₀ D q0).step
        (mkCfg (some (.retR l s dir b a false)) ip rt rp dt dp out) =
        mkCfg (some (.retR l s dir b a true)) ip rt rp' dt dp out := by
      unfold MultiTapeTM.step
      simp only [mkCfg_state]
      simp only [compileTM, ctr, hcall, hrr, hread, Bool.false_eq_true, ↓reduceIte]
      cases hb : FinTM.bufferTape w (rp rr) with
      | none =>
        have hls := hside hb
        simp only [leftSide] at hls
        simp only [hls, ↓reduceIte, Bool.false_eq_true]
        rw [apply_regMove]
        congr 1
      | some _ =>
        simp only
        rw [apply_regMove]
        congr 1
    obtain ⟨hb, hr⟩ := retR_scan P l₀ D q0 l cs hcall s dir b a w rr hrr rt hrt dt dp out ip n rp'
      (by simp [hrp', hn]) (by omega)
    refine ⟨n + 1 + 1, fun t ht r => ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos t with h | h
      · subst h; exact ⟨Or.inl (by simp [mkCfg]), by funext i; simp [mkCfg]⟩
      · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
        rw [MultiTapeTM.runFrom_succ_eq_step, hstep]
        obtain ⟨h1, h2⟩ := hb t' (by omega) r
        refine ⟨?_, h2⟩
        by_cases hrr' : r = rr
        · subst hrr'
          right
          rcases h1 with h1 | h1
          · rw [h1]; simp only [hrp', Function.update_self]
            exact ⟨trivial, by omega, by omega⟩
          · refine ⟨rfl, h1.2.1, h1.2.2.trans ?_⟩
            simp only [hrp', Function.update_self]
            omega
        · left
          rcases h1 with h1 | h1
          · rw [h1]; simp [hrp', hrr']
          · exact absurd h1.1 hrr'
    · rw [MultiTapeTM.runFrom_succ_eq_step, hstep, hr]
      congr 1
      simp [hrp']

/-- The register positions after restoring the first `a` argument registers. -/
def retPos (cs : CallSpec m d Λ) (rp0 : Fin m → ℤ) (a : ℕ) (r : Fin m) : ℤ :=
  if r ∈ cs.args ∧ cs.args.idxOf r < a then 0 else rp0 r

/-- Register positions within the call's range: non-arguments untouched, argument `r` in
`[-1, |W r|]`. -/
def RegBox (cs : CallSpec m d Λ) (c0pos : Fin m → ℤ) (W : Fin m → List Bool)
    (p : Fin m → ℤ) : Prop :=
  ∀ r, (r ∉ cs.args → p r = c0pos r) ∧ (r ∈ cs.args → -1 ≤ p r ∧ p r ≤ (W r).length)

/-- Restoring all argument registers, one after the other.

**Proof sketch.** Induction on the number `k` of argument registers still to restore. Each
register is restored by `retR_run`, whose side test is supplied by `hside`; the restored head is
at `0`, so the positions remain in the register box. When all are restored the machine returns
to the program state `yes` or `no` according to the answer `b`. -/
lemma regs_run (l : Λ) (cs : CallSpec m d Λ) (hcall : P.call l = some cs) (hnd : cs.args.Nodup)
    (s : Fin (m + 1)) (dir b : Bool) (W : Fin m → List Bool) (rt : Fin m → ℤ → Option Bool)
    (hrt : ∀ r ∈ cs.args, rt r = FinTM.bufferTape (W r)) (dt : Fin kD → ℤ → Option Bool)
    (dp : Fin kD → ℤ) (out : List Bool) (ip : Fin (x.length + 2)) (c0pos rp0 : Fin m → ℤ)
    (hbox : RegBox cs c0pos W rp0)
    (hside : ∀ (a : ℕ) (ha : a < cs.args.length) (hm : a < m),
      (rp0 cs.args[a] = -1 → leftSide s dir ⟨a, hm⟩ = true) ∧
      (rp0 cs.args[a] = (W cs.args[a]).length → leftSide s dir ⟨a, hm⟩ = false)) :
    ∀ k a, a + k = cs.args.length →
      ∃ T, (∀ t ≤ T, RegBox cs c0pos W (fun r => ((compileTM P l₀ D q0).runFrom
          (mkCfg (some (nextRet cs l s dir b a)) ip rt (retPos cs rp0 a) dt dp out) t).workTapePos
            (Fin.castAdd kD r)) ∧
          ((compileTM P l₀ D q0).runFrom
          (mkCfg (some (nextRet cs l s dir b a)) ip rt (retPos cs rp0 a) dt dp out) t).workTapePos
            ∘ Fin.natAdd m = dp) ∧
        (compileTM P l₀ D q0).runFrom
          (mkCfg (some (nextRet cs l s dir b a)) ip rt (retPos cs rp0 a) dt dp out) T =
          mkCfg (some (.prog (if b then cs.yes else cs.no))) ip rt
            (retPos cs rp0 cs.args.length) dt dp out := by
  have hlen : cs.args.length ≤ m := by simpa using hnd.length_le_card
  -- the positions at every stage stay in the box
  have hret : ∀ a, RegBox cs c0pos W (retPos cs rp0 a) := by
    intro a r
    refine ⟨fun hr => by simp [retPos, hr, (hbox r).1 hr], fun hr => ?_⟩
    unfold retPos
    split_ifs
    · exact ⟨by omega, by omega⟩
    · exact (hbox r).2 hr
  intro k
  induction k with
  | zero =>
    intro a ha
    have hna : ¬ (a < cs.args.length ∧ a < m) := by omega
    refine ⟨0, fun t ht => ?_, ?_⟩
    · obtain rfl : t = 0 := by omega
      exact ⟨fun r => by simpa [mkCfg] using hret a r, by funext i; simp [mkCfg]⟩
    · simp only [MultiTapeTM.runFrom_zero, nextRet, hna, ↓reduceDIte]
      rw [show a = cs.args.length by omega]
  | succ k ih =>
    intro a ha
    have hal : a < cs.args.length := by omega
    have ham : a < m := by omega
    have hnr : nextRet (SD := SD) cs l s dir b a = .retR l s dir b ⟨a, ham⟩ false := by
      simp [nextRet, hal, ham]
    set rr := cs.args[a] with hrrdef
    have hrr : cs.args.getD (⟨a, ham⟩ : Fin m).val ⟨a, ham⟩ = rr := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hal, hrrdef]
    have hmem : rr ∈ cs.args := List.getElem_mem hal
    have hidx : cs.args.idxOf rr = a := List.idxOf_getElem hnd a hal
    have hp0 : retPos cs rp0 a rr = rp0 rr := by simp [retPos, hidx]
    obtain ⟨hs1, hs2⟩ := hside a hal ham
    obtain ⟨T₁, hb₁, hr₁⟩ := retR_run P l₀ D q0 l cs hcall s dir b ⟨a, ham⟩ (W rr) rr hrr rt
      (hrt rr hmem) dt dp out ip (retPos cs rp0 a)
      (by rw [hp0]; exact (hbox rr).2 hmem) (by rw [hp0]; exact hs1) (by rw [hp0]; exact hs2)
    have hupd : Function.update (retPos cs rp0 a) rr 0 = retPos cs rp0 (a + 1) := by
      funext r
      by_cases hr : r = rr
      · subst hr; simp [retPos, hidx, hmem]
      · rw [Function.update_of_ne hr]
        unfold retPos
        by_cases hm : r ∈ cs.args
        · have hne : cs.args.idxOf r ≠ a := by
            intro h; apply hr; rw [hrrdef]
            have := List.getElem_idxOf (List.idxOf_lt_length_of_mem hm)
            rw [← this]; congr 1
          simp only [hm, true_and]
          split_ifs <;> first | rfl | omega
        · simp [hm]
    rw [hupd] at hr₁
    obtain ⟨T₂, hb₂, hr₂⟩ := ih (a + 1) (by omega)
    refine ⟨T₁ + T₂, fun t ht => ?_, ?_⟩
    · rw [hnr]
      rcases Nat.lt_or_ge t T₁ with h | h
      · have h1 := fun r => (hb₁ t h.le r).1
        have h2 := (hb₁ t h.le rr).2
        refine ⟨fun r => ⟨fun hr => ?_, fun hr => ?_⟩, by simpa using h2⟩
        · beta_reduce
          rcases h1 r with h1 | h1
          · rw [h1]; exact ((hret a) r).1 hr
          · exact absurd (h1.1 ▸ hmem) hr
        · beta_reduce
          rcases h1 r with h1 | h1
          · rw [h1]; exact ((hret a) r).2 hr
          · refine ⟨h1.2.1, h1.2.2.trans ?_⟩
            have := ((hret a) r).2 hr
            omega
      · obtain ⟨t', rfl⟩ : ∃ t', t = T₁ + t' := ⟨t - T₁, by omega⟩
        rw [MultiTapeTM.runFrom_add, hr₁]
        exact hb₂ t' (by omega)
    · rw [hnr, MultiTapeTM.runFrom_add, hr₁, hr₂]

end Return

end Complexity.LogProg

```


## ===== TCSlib/Complexity/SpaceComplexity/Machines/Call.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.CallReturn

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A whole subroutine call of the compiled machine

From a program configuration at a call node, the compiled machine moves the argument
heads onto their left blanks (*setup*), simulates the decider on the virtual input step for
step (`Complexity.LogProg.sim_step`), and when the decider halts rewinds the input head and
the argument heads (*return*). For a *clean* decider — one that halts with blank work tapes
and heads at the origin — this ends in the compiled configuration of the program
configuration after the call (`Complexity.LogProg.call_run`), with every head in a known
range at every intermediate time.

Compiled configurations (`mkCfg`) and the return phase are in
`TCSlib.Complexity.SpaceComplexity.Machines.CallReturn`, which this file re-exports.

## Main definitions

* `Complexity.LogProg.mkCfg` — a compiled configuration from its register and decider
  blocks.
* `Complexity.LogProg.CleanRun` — the decider halts from a start state cleanly, with heads
  in a given range, answering a given bit.

## Main results

* `Complexity.LogProg.call_run` — a call runs to completion.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.3, proof of Lemma 4.17.)
-/

namespace Complexity.LogProg

open Turing

variable {m d kD : ℕ} {Λ SD : Type} {x : List Bool}

/-! ## The whole call -/

/-- The decider started in state `q` on `V` halts — at time `T` — with output `[b]`, blank
work tapes and heads at the origin, its heads staying within `[-B, B]`. -/
def CleanRun (D : MultiTapeTM kD Bool SD) (q : SD) (V : List Bool) (b : Bool) (B : ℕ) : Prop :=
  ∃ T, (D.runFrom (Cfg.init q V) T).state = none ∧ (D.runFrom (Cfg.init q V) T).output = [b] ∧
    (D.runFrom (Cfg.init q V) T).workTapes = (fun _ _ => none) ∧
    (D.runFrom (Cfg.init q V) T).workTapePos = (fun _ => 0) ∧
    ∀ t ≤ T, ∀ i, |(D.runFrom (Cfg.init q V) t).workTapePos i| ≤ B

/-- Properties of all configurations along two consecutive run segments. -/
lemma runFrom_forall_append {K : ℕ} {S : Type} {tm : MultiTapeTM K Bool S}
    {c : Cfg K Bool S x} {T₁ T₂ : ℕ} {Q : Cfg K Bool S x → Prop}
    (h₁ : ∀ t ≤ T₁, Q (tm.runFrom c t)) (h₂ : ∀ t ≤ T₂, Q (tm.runFrom (tm.runFrom c T₁) t)) :
    ∀ t ≤ T₁ + T₂, Q (tm.runFrom c t) := by
  intro t ht
  rcases Nat.lt_or_ge t T₁ with h | h
  · exact h₁ t h.le
  · obtain ⟨t', rfl⟩ : ∃ t', t = T₁ + t' := ⟨t - T₁, by omega⟩
    rw [MultiTapeTM.runFrom_add]
    exact h₂ t' (by omega)

/-- The first segment of a virtual input starts at offset `0`. -/
@[simp] lemma off_zero (segs : List Seg) : off segs 0 = 0 := by cases segs <;> rfl

section Whole

variable {l : Λ} {cs : CallSpec m d Λ} {W : Fin m → List Bool} {c0 : Cfg m Bool Λ x}

/-- During a call the register positions stay in the call's range. -/
lemma regPos_box (_hnd : cs.args.Nodup) (s : ℕ) (tp : TPos)
    (hval : tp.Valid (callSegs cs x W) s) (_hs : s < cs.args.length + 1) :
    RegBox cs c0.workTapePos W (regPos c0 cs W s tp) := by
  intro r
  refine ⟨fun hr => by simp [regPos, hr], fun hr => ?_⟩
  have hidx := List.idxOf_lt_length_of_mem hr
  have hget : cs.args[cs.args.idxOf r] = r := List.getElem_idxOf hidx
  have hw : wlen (callSegs cs x W) (cs.args.idxOf r + 1) = (W r).length := by
    simp only [wlen]; rw [seg_callSegs_succ cs x W _ hidx, hget]
  simp only [regPos, hr, ↓reduceIte]
  split_ifs with h1 h2
  · rw [hw]; omega
  · omega
  · have hs' : s = cs.args.idxOf r + 1 := by omega
    have := trackPos_bounds _ s tp hval
    rw [hs'] at this ⊢
    rw [hw] at this
    exact this

/-- The side tests of the return phase agree with the register positions at the halt.

**Proof sketch.** A register head is at `-1` or at `|W r|` only when the track position sits at
the left or right blank of that register's segment. Consistency of the track position with the
segment parity and direction (`Consistent`) then fixes which side the return phase's test
`leftSide` reports. -/
lemma regPos_side (hnd : cs.args.Nodup) (s : Fin (m + 1)) (par dir : Bool) (tp : TPos)
    (hcons : Consistent (callSegs cs x W) s par dir tp)
    (hval : tp.Valid (callSegs cs x W) s) (a : ℕ) (ha : a < cs.args.length) (hm : a < m) :
    (regPos c0 cs W s tp cs.args[a] = -1 → leftSide s dir ⟨a, hm⟩ = true) ∧
      (regPos c0 cs W s tp cs.args[a] = (W cs.args[a]).length →
        leftSide s dir ⟨a, hm⟩ = false) := by
  have hidx : cs.args.idxOf cs.args[a] = a := List.idxOf_getElem hnd a ha
  have hw : wlen (callSegs cs x W) (a + 1) = (W cs.args[a]).length := by
    simp only [wlen]; rw [seg_callSegs_succ cs x W _ ha]
  simp only [regPos, List.getElem_mem, ↓reduceIte, hidx, leftSide]
  split_ifs with h1 h2
  · rw [hw]
    have e1 : ¬ (s : ℕ) < a + 1 := by omega
    have e2 : ¬ (s : ℕ) = a + 1 := by omega
    simp only [e1, e2, decide_false, Bool.false_and, Bool.or_false, Bool.false_eq_true]
    constructor <;> intro h <;> first | rfl | omega
  · simp only [h2, decide_true, Bool.true_or]
    exact ⟨fun _ => trivial, fun h => h.elim⟩
  · have hs' : (s : ℕ) = a + 1 := by omega
    cases tp with
    | left =>
      simp only [Consistent] at hcons
      subst hcons
      simp [trackPos, hs']
    | cell c p =>
      simp only [TPos.Valid, hs'] at hval
      simp only [trackPos]
      rw [hw] at hval
      constructor <;> intro h <;> omega
    | right =>
      simp only [Consistent] at hcons
      subst hcons
      simp only [trackPos, hs', hw]
      constructor <;> intro h <;> simp; omega

/-- **A whole call.** From a program configuration at a call node whose argument registers
hold `W` with their heads at the origin, input head on the first cell, and a decider that
answers `b` cleanly within head range `B`, the compiled machine reaches the compiled
configuration of the program configuration after the call — state `yes` or `no` by `b`,
input head on the first cell, everything else unchanged. Throughout, the registers stay in
the call's range and the decider block in `[-B, B]`.

**Proof sketch.** One setup step (`apply_moves`) establishes the simulation relation with
the decider's initial configuration; `sim_step` carries it to the decider's first halting
time; there the decider's tapes are clean, and the return phase (`ret2_run`, `regs_run`)
restores the input head and the argument heads (`regPos_side` checks the side tests). -/
theorem call_run (P : RProg m d Λ) (l₀ : Λ) (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD)
    (hl : c0.state = some l) (hcall : P.call l = some cs)
    (hW : ∀ r ∈ cs.args, c0.workTapes r = FinTM.bufferTape (W r))
    (hW0 : ∀ r ∈ cs.args, c0.workTapePos r = 0) (hnd : cs.args.Nodup)
    (hin : c0.inputPos.val = 1) (b : Bool) (B : ℕ)
    (hD : CleanRun D (q0 cs.dec) (vword (callSegs cs x W)) b B) :
    ∃ T, (∀ t ≤ T, RegBox cs c0.workTapePos W (fun r => ((compileTM P l₀ D q0).runFrom
          (seam c0) t).workTapePos (Fin.castAdd kD r)) ∧
        ∀ i, |((compileTM P l₀ D q0).runFrom (seam c0) t).workTapePos (Fin.natAdd m i)| ≤ B) ∧
      (compileTM P l₀ D q0).runFrom (seam c0) T =
        seam { c0 with state := some (if b then cs.yes else cs.no), inputPos := 1 } := by
  classical
  obtain ⟨T, hTh, hTo, hTt, hTp, hTb⟩ := hD
  set V := vword (callSegs cs x W) with hV
  set dc0 : Cfg kD Bool SD V := Cfg.init (q0 cs.dec) V with hdc0
  have hlen : cs.args.length ≤ m := by simpa using hnd.length_le_card
  -- the setup step
  have hsetup : (compileTM P l₀ D q0).step (seam c0) =
      mkCfg (some (.sim l (q0 cs.dec) 0 false true none)) c0.inputPos c0.workTapes
        (fun r => c0.workTapePos r + ((if r ∈ cs.args then -1 else 0 : SignType) : ℤ))
        (fun _ _ => none) (fun _ => 0) c0.output := by
    rw [seam_eq_mkCfg]
    unfold MultiTapeTM.step
    simp only [mkCfg_state, hl, Option.map_some]
    simp only [compileTM, ctr, hcall]
    rw [apply_moves, moveInputPos_zero]
  -- the first halting time of the decider
  have hex : ∃ t, (D.runFrom dc0 t).state = none := ⟨T, hTh⟩
  set T0 := Nat.find hex with hT0def
  have hT0 : (D.runFrom dc0 T0).state = none := Nat.find_spec hex
  have hT0le : T0 ≤ T := Nat.find_min' hex hTh
  have hlive : ∀ t < T0, (D.runFrom dc0 t).state ≠ none := fun t ht => Nat.find_min hex ht
  have hfin : D.runFrom dc0 T = D.runFrom dc0 T0 := by
    rw [show T = T0 + (T - T0) by omega, MultiTapeTM.runFrom_add,
      MultiTapeTM.runFrom_of_halt _ hT0]
  have hT0pos : 0 < T0 := by
    rcases Nat.eq_zero_or_pos T0 with h | h
    · rw [h] at hT0; simp [dc0] at hT0
    · exact h
  -- the simulation relation at the start
  have hsim0 : SimRel c0 l cs W ((compileTM P l₀ D q0).step (seam c0)) dc0 := by
    have hw0 := wlen_zero_le cs x W
    let tp : TPos := if wlen (callSegs cs x W) 0 = 0 then .right else .cell 0 false
    refine ⟨q0 cs.dec, 0, false, true, tp, ?_, rfl, ?_⟩
    · rw [hsetup]; rfl
    refine ⟨by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [tp]; split_ifs with h <;> simp [TPos.Valid]; omega
    · simp only [tp]; split_ifs <;> simp [Consistent]
    · simp only [tp, dc0, Cfg.init]
      split_ifs with h
      · simp only [vpos, wlen, rlen] at h ⊢; split <;> simp_all
      · simp [vpos, off_zero, cellOff]
    · rw [hsetup]
      simp only [mkCfg, tp, inPos, Fin.val_zero, ↓reduceIte, hin]
      split_ifs with h <;> simp [trackPos, h]
    · intro r; rw [hsetup]; simp [mkCfg]
    · intro r
      rw [hsetup]
      simp only [mkCfg, Fin.append_left, regPos]
      by_cases hr : r ∈ cs.args
      · simp [hr, hW0 r hr]
      · simp [hr]
    · intro i; rw [hsetup]; simp [mkCfg, dc0, Cfg.init]
    · intro i; rw [hsetup]; simp [mkCfg, dc0, Cfg.init]
    · rw [hsetup]; rfl
  -- the simulation, up to the halt
  have hsim : ∀ t ≤ T0, (t < T0 → SimRel c0 l cs W ((compileTM P l₀ D q0).runFrom ((compileTM P l₀ D q0).step (seam c0)) t)
        (D.runFrom dc0 t)) ∧
      (t = T0 → HaltRel c0 l cs W ((compileTM P l₀ D q0).runFrom ((compileTM P l₀ D q0).step (seam c0)) t) (D.runFrom dc0 t)) := by
    intro t
    induction t with
    | zero => intro _; exact ⟨fun _ => hsim0, fun h => absurd h (by omega)⟩
    | succ t ih =>
      intro ht
      have h := (ih (by omega)).1 (by omega)
      have hs := sim_step l P D q0 hcall hW hnd h (l₀ := l₀)
      rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step']
      constructor
      · intro hlt
        apply hs.1
        rw [← MultiTapeTM.runFrom_succ_eq_step']
        exact hlive _ hlt
      · intro heq
        apply hs.2
        rw [← MultiTapeTM.runFrom_succ_eq_step', heq]
        exact hT0
  -- the halt
  obtain ⟨s, par, dir, tp, hgst, -, R⟩ := (hsim T0 le_rfl).2 rfl
  have hout0 : (D.runFrom dc0 T0).output = [b] := by rw [← hfin]; exact hTo
  have hb : ((D.runFrom dc0 T0).output.head?.getD false) = b := by rw [hout0]; rfl
  set gH := (compileTM P l₀ D q0).runFrom ((compileTM P l₀ D q0).step (seam c0)) T0 with hgH
  have hgHeq : gH = mkCfg (some (.ret1 l s dir b)) gH.inputPos c0.workTapes
      (regPos c0 cs W s tp) (fun _ _ => none) (fun _ => 0) c0.output := by
    refine Cfg.ext (by rw [hgst, hb]; rfl) rfl ?_ ?_ R.out
    · funext i z
      refine Fin.addCases (fun r => ?_) (fun j => ?_) i
      · simp [mkCfg, R.regTape]
      · simp only [mkCfg, Fin.append_right, R.dTape]
        rw [← hfin, hTt]
    · funext i
      refine Fin.addCases (fun r => ?_) (fun j => ?_) i
      · simp [mkCfg, R.regPos]
      · simp only [mkCfg, Fin.append_right, R.dPos]
        rw [← hfin, hTp]
  -- the return: input rewind
  have hret1 : (compileTM P l₀ D q0).step gH =
      mkCfg (some (.ret2 l s dir b)) (moveInputPos gH.inputPos (-1)) c0.workTapes
        (regPos c0 cs W s tp) (fun _ _ => none) (fun _ => 0) c0.output := by
    conv_lhs => rw [hgHeq]
    unfold MultiTapeTM.step
    simp only [mkCfg_state]
    simp only [compileTM, ctr]
    rw [apply_inputOnly]
  have hj : (moveInputPos gH.inputPos (-1)).val ≤ x.length := by
    rw [show (-1 : SignType) = .neg from rfl, FinTM.moveInputPos_neg_val]
    have := gH.inputPos.isLt; omega
  obtain ⟨hb2, hr2⟩ := ret2_run P l₀ D q0 l cs hcall s dir b c0.workTapes (regPos c0 cs W s tp)
    (fun _ _ => none) (fun _ => 0) c0.output _ _ rfl hj
  -- the return: argument registers
  have hbox0 := regPos_box (c0 := c0) hnd s tp R.valid R.hs
  have hret0 : retPos cs (regPos c0 cs W s tp) 0 = regPos c0 cs W s tp := by
    funext r; simp [retPos]
  obtain ⟨T₃, hb3, hr3⟩ := regs_run P l₀ D q0 l cs hcall hnd s dir b W c0.workTapes hW
    (fun _ _ => none) (fun _ => 0) c0.output 1 c0.workTapePos (regPos c0 cs W s tp) hbox0
    (fun a ha hm => regPos_side hnd s par dir tp R.cons R.valid a ha hm)
    cs.args.length 0 (by omega)
  rw [hret0] at hb3 hr3
  have hretL : retPos cs (regPos c0 cs W s tp) cs.args.length = c0.workTapePos := by
    funext r
    unfold retPos
    by_cases hr : r ∈ cs.args
    · simp [hr, List.idxOf_lt_length_of_mem hr, hW0 r hr]
    · simp [hr, regPos]
  rw [hretL] at hr3
  -- assemble
  have hfinal : (mkCfg (some (CSt.prog (if b then cs.yes else cs.no))) 1 c0.workTapes
      c0.workTapePos (fun _ _ => none) (fun _ => 0) c0.output : Cfg (m + kD) Bool (CSt Λ SD m) x) =
      seam (kD := kD) (SD := SD)
        { c0 with state := some (if b then cs.yes else cs.no), inputPos := 1 } := by
    rw [seam_eq_mkCfg]; rfl
  refine ⟨1 + (T0 + (1 + ((moveInputPos gH.inputPos (-1)).val + 1 + T₃))), ?_, ?_⟩
  · -- the box along the whole call
    have hregBoxSeam : RegBox cs c0.workTapePos W c0.workTapePos := by
      intro r
      refine ⟨fun _ => rfl, fun hr => ?_⟩
      rw [hW0 r hr]; simp
    let Q : Cfg (m + kD) Bool (CSt Λ SD m) x → Prop := fun g =>
      RegBox cs c0.workTapePos W (fun r => g.workTapePos (Fin.castAdd kD r)) ∧
        ∀ i, |g.workTapePos (Fin.natAdd m i)| ≤ B
    show ∀ t ≤ _, Q ((compileTM P l₀ D q0).runFrom (seam c0) t)
    apply runFrom_forall_append (Q := Q)
    · intro t ht
      rcases Nat.eq_zero_or_pos t with h | h
      · subst h
        refine ⟨by simpa [seam] using hregBoxSeam, fun i => by simp [seam]⟩
      · obtain rfl : t = 1 := by omega
        rw [show (compileTM P l₀ D q0).runFrom (seam c0) 1 = ((compileTM P l₀ D q0).step (seam c0)) from rfl]
        obtain ⟨_, _, _, _, _, _, _, R0⟩ := hsim0
        refine ⟨?_, fun i => ?_⟩
        · intro r; simp only [R0.regPos]; exact regPos_box hnd _ _ R0.valid R0.hs r
        · rw [R0.dPos]; simp [dc0, Cfg.init]
    rw [show (compileTM P l₀ D q0).runFrom (seam c0) 1 = (compileTM P l₀ D q0).step (seam c0)
      from rfl]
    apply runFrom_forall_append (Q := Q)
    · intro t ht
      have hTR : ∃ s par dir tp, TrackRel c0 cs W ((compileTM P l₀ D q0).runFrom ((compileTM P l₀ D q0).step (seam c0)) t)
          (D.runFrom dc0 t) s par dir tp := by
        rcases Nat.lt_or_ge t T0 with h | h
        · obtain ⟨_, s', par', dir', tp', -, -, R'⟩ := (hsim t ht).1 h
          exact ⟨s', par', dir', tp', R'⟩
        · obtain ⟨s', par', dir', tp', -, -, R'⟩ := (hsim t ht).2 (by omega)
          exact ⟨s', par', dir', tp', R'⟩
      obtain ⟨s', par', dir', tp', R'⟩ := hTR
      refine ⟨?_, fun i => ?_⟩
      · intro r; simp only [R'.regPos]; exact regPos_box hnd s' tp' R'.valid R'.hs r
      · rw [R'.dPos]; exact hTb t (by omega) i
    apply runFrom_forall_append (Q := Q)
    · intro t ht
      rcases Nat.eq_zero_or_pos t with h | h
      · subst h
        rw [MultiTapeTM.runFrom_zero, ← hgH, hgHeq]
        exact ⟨fun r => by simpa [mkCfg] using hbox0 r, fun i => by simp [mkCfg]⟩
      · obtain rfl : t = 1 := by omega
        rw [show (compileTM P l₀ D q0).runFrom ((compileTM P l₀ D q0).runFrom ((compileTM P l₀ D q0).step (seam c0)) T0) 1 =
          (compileTM P l₀ D q0).step gH from rfl, hret1]
        exact ⟨fun r => by simpa [mkCfg] using hbox0 r, fun i => by simp [mkCfg]⟩
    rw [show (compileTM P l₀ D q0).runFrom ((compileTM P l₀ D q0).runFrom ((compileTM P l₀ D q0).step (seam c0)) T0) 1 =
      (compileTM P l₀ D q0).step gH from rfl, hret1]
    apply runFrom_forall_append (Q := Q)
    · intro t ht
      dsimp only [Q]
      rw [hb2 t ht]
      exact ⟨fun r => by simpa using hbox0 r, fun i => by simp⟩
    rw [hr2]
    intro t ht
    dsimp only [Q]
    obtain ⟨h1, h2⟩ := hb3 t ht
    refine ⟨h1, fun i => ?_⟩
    have := congrFun h2 i
    simp only [Function.comp_apply] at this
    rw [this]; simp
  · rw [MultiTapeTM.runFrom_add]
    change (compileTM P l₀ D q0).runFrom ((compileTM P l₀ D q0).step (seam c0)) _ = _
    rw [MultiTapeTM.runFrom_add, ← hgH, MultiTapeTM.runFrom_add]
    rw [show (compileTM P l₀ D q0).runFrom gH 1 = (compileTM P l₀ D q0).step gH from rfl, hret1,
      MultiTapeTM.runFrom_add, hr2, hr3, hfinal]


end Whole

end Complexity.LogProg

```


## ===== TCSlib/Complexity/SpaceComplexity/Machines/Compile.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Algebra.BigOperators.Fin
import TCSlib.Complexity.SpaceComplexity.Machines.Call

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Correctness of the compiled machine

The semantics of a register-tape program (`Complexity.LogProg.rstep`): ordinary nodes take
their machine step, a call node asks an oracle about the virtual input of the call
(`Complexity.LogProg.vword` of `Complexity.LogProg.callSegs`) and continues in its `yes` or
`no` state with the input head back on the first cell. If the deciders answer the oracle
cleanly, the compiled machine (`Complexity.LogProg.compileTM`) computes what the program
computes (`Complexity.LogProg.compile_correct`), in space bounded by the program's register
ranges plus the deciders' space (`Complexity.LogProg.compile_space`).

## Main definitions

* `Complexity.LogProg.tapeWord` — the word stored on a register tape.
* `Complexity.LogProg.rstep` — one step of a program, calls being atomic oracle questions.
* `Complexity.LogProg.CallsOK` — the preconditions of every call along a run.
* `Complexity.LogProg.compileFinTM` — the compiled machine as a bundled finite machine.

## Main results

* `Complexity.LogProg.compile_correct` — the compiled machine halts with the program's
  output, all heads in the given ranges at all times.
* `Complexity.LogProg.compile_space` — its space usage is at most the sum of the register
  ranges plus `kD (2B + 1)`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.3, proof of Lemma 4.17.)
-/

namespace Complexity.LogProg

open Turing

variable {m d kD : ℕ} {Λ SD : Type} {x : List Bool}

/-- The word stored on a register tape (from cell `0`; `[]` if the tape is not of this
shape). -/
noncomputable def tapeWord (f : ℤ → Option Bool) : List Bool :=
  open Classical in if h : ∃ w, f = FinTM.bufferTape w then h.choose else []

/-- A stored word is read back. -/
lemma tapeWord_bufferTape (w : List Bool) : tapeWord (FinTM.bufferTape w) = w := by
  have h : ∃ w', FinTM.bufferTape w = FinTM.bufferTape w' := ⟨w, rfl⟩
  unfold tapeWord
  rw [dif_pos h]
  have hspec := h.choose_spec
  -- `bufferTape` is injective
  apply List.ext_getElem?
  intro i
  have := congrFun hspec (i : ℤ)
  simpa [FinTM.bufferTape] using this.symm

/-- The register words of a program configuration. -/
noncomputable def regWords (c : Cfg m Bool Λ x) (r : Fin m) : List Bool := tapeWord (c.workTapes r)

/-- **One step of a register-tape program**: an ordinary node takes its machine step; a call
node asks `oracle` (decider `cs.dec`) about its virtual input and moves to `yes` or `no`,
with the input head on the first cell. -/
noncomputable def rstep (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool)
    (c : Cfg m Bool Λ x) : Cfg m Bool Λ x :=
  match c.state with
  | none => c
  | some l =>
    match P.call l with
    | none => P.tm.step c
    | some cs =>
      { c with
        state := some (if oracle cs.dec (vword (callSegs cs x (regWords c))) then cs.yes
          else cs.no),
        inputPos := 1 }

/-- The program run: `n` steps of `rstep`. -/
noncomputable def rrun (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool)
    (c : Cfg m Bool Λ x) (n : ℕ) : Cfg m Bool Λ x :=
  (rstep P oracle)^[n] c

/-- Running a register-tape program `n + 1` steps is one more step after `n` steps. -/
lemma rrun_succ (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (c : Cfg m Bool Λ x)
    (n : ℕ) : rrun P oracle c (n + 1) = rstep P oracle (rrun P oracle c n) := by
  simp [rrun, Function.iterate_succ_apply']

/-- The preconditions of a call at configuration `c` (if `c` is at a call node): distinct
argument registers holding words with their heads at the origin and within the register
ranges, input head on the first cell, and a decider answering the oracle cleanly within head
range `B`. -/
def CallOK (P : RProg m d Λ) (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD)
    (oracle : Fin d → List Bool → Bool) (lo hi : Fin m → ℤ) (B : ℕ) (c : Cfg m Bool Λ x) :
    Prop :=
  ∀ l cs, c.state = some l → P.call l = some cs →
    cs.args.Nodup ∧ c.inputPos.val = 1 ∧
    (∀ r ∈ cs.args, c.workTapes r = FinTM.bufferTape (regWords c r) ∧ c.workTapePos r = 0 ∧
      lo r ≤ -1 ∧ ((regWords c r).length : ℤ) ≤ hi r) ∧
    CleanRun D (q0 cs.dec) (vword (callSegs cs x (regWords c)))
      (oracle cs.dec (vword (callSegs cs x (regWords c)))) B

/-- **Correctness of the compiled machine.** If the program halts after `N` steps with
output `w`, its register heads stay in `[lo r, hi r]`, and every call along the way meets
its preconditions, then the compiled machine halts with output `w`, and at every time its
register heads are in `[lo r, hi r]` and its decider heads in `[-B, B]`.

**Proof sketch.** Induction on the program run, keeping the compiled machine on the seam
(`Complexity.LogProg.seam`) of the program configuration: ordinary steps are simulated in
lockstep (`step_seam_prog`), calls by `call_run`. -/
theorem compile_correct (P : RProg m d Λ) (l₀ : Λ) (D : MultiTapeTM kD Bool SD)
    (q0 : Fin d → SD) (oracle : Fin d → List Bool → Bool) (lo hi : Fin m → ℤ) (B : ℕ)
    (N : ℕ)
    (hbox : ∀ t ≤ N, ∀ r, lo r ≤ (rrun P oracle (Cfg.init l₀ x) t).workTapePos r ∧
      (rrun P oracle (Cfg.init l₀ x) t).workTapePos r ≤ hi r)
    (hcalls : ∀ t < N, CallOK P D q0 oracle lo hi B (rrun P oracle (Cfg.init l₀ x) t)) :
    ∃ T, (compileTM P l₀ D q0).runFrom ((compileTM P l₀ D q0).initCfg x) T =
        seam (rrun P oracle (Cfg.init l₀ x) N) ∧
      ∀ t ≤ T, (∀ r, lo r ≤ ((compileTM P l₀ D q0).runFrom ((compileTM P l₀ D q0).initCfg x)
          t).workTapePos (Fin.castAdd kD r) ∧
          ((compileTM P l₀ D q0).runFrom ((compileTM P l₀ D q0).initCfg x) t).workTapePos
            (Fin.castAdd kD r) ≤ hi r) ∧
        ∀ i, |((compileTM P l₀ D q0).runFrom ((compileTM P l₀ D q0).initCfg x) t).workTapePos
          (Fin.natAdd m i)| ≤ B := by
  induction N with
  | zero =>
    refine ⟨0, by rw [MultiTapeTM.runFrom_zero, seam_init]; rfl, fun t ht => ?_⟩
    obtain rfl : t = 0 := by omega
    refine ⟨fun r => ?_, fun i => ?_⟩
    · have := hbox 0 le_rfl r
      simpa [seam_init, seam, rrun] using this
    · simp
  | succ N ih =>
    obtain ⟨T, hT, hTb⟩ := ih (fun t ht => hbox t (by omega)) (fun t ht => hcalls t (by omega))
    set c := rrun P oracle (Cfg.init l₀ x) N with hc
    have hbN := hbox N (by omega)
    have hbN1 := hbox (N + 1) le_rfl
    rw [rrun_succ, ← hc] at hbN1 ⊢
    -- one program step from `c`
    have hstep : ∃ T', (compileTM P l₀ D q0).runFrom (seam c) T' = seam (rstep P oracle c) ∧
        ∀ t ≤ T', (∀ r, lo r ≤ ((compileTM P l₀ D q0).runFrom (seam c) t).workTapePos
            (Fin.castAdd kD r) ∧ ((compileTM P l₀ D q0).runFrom (seam c) t).workTapePos
              (Fin.castAdd kD r) ≤ hi r) ∧
          ∀ i, |((compileTM P l₀ D q0).runFrom (seam c) t).workTapePos (Fin.natAdd m i)| ≤ B := by
      cases hs : c.state with
      | none =>
        refine ⟨0, by simp [rstep, hs], fun t ht => ?_⟩
        obtain rfl : t = 0 := by omega
        exact ⟨fun r => by simpa [seam] using hbN r, fun i => by simp [seam]⟩
      | some l =>
        cases hcl : P.call l with
        | none =>
          have hst := step_seam_prog P l₀ D q0 c l hs hcl
          have hr : rstep P oracle c = P.tm.step c := by simp [rstep, hs, hcl]
          refine ⟨1, by rw [hr]; exact hst, fun t ht => ?_⟩
          rcases Nat.lt_or_ge t 1 with h | h
          · obtain rfl : t = 0 := by omega
            exact ⟨fun r => by simpa [seam] using hbN r, fun i => by simp [seam]⟩
          · obtain rfl : t = 1 := by omega
            rw [show (compileTM P l₀ D q0).runFrom (seam c) 1 =
              (compileTM P l₀ D q0).step (seam c) from rfl, hst, ← hr]
            exact ⟨fun r => by simpa [seam] using hbN1 r, fun i => by simp [seam]⟩
        | some cs =>
          obtain ⟨hnd, hin, hargs, hclean⟩ := hcalls N (by omega) l cs hs hcl
          obtain ⟨T', hb', hr'⟩ := call_run P l₀ D q0 hs hcl (fun r hr => (hargs r hr).1)
            (fun r hr => (hargs r hr).2.1) hnd hin _ B hclean
          have hr : rstep P oracle c = { c with
              state := some (if oracle cs.dec (vword (callSegs cs x (regWords c))) then cs.yes
                else cs.no), inputPos := 1 } := by simp [rstep, hs, hcl]
          refine ⟨T', by rw [hr]; exact hr', fun t ht => ⟨fun r => ?_, (hb' t ht).2⟩⟩
          obtain ⟨h1, h2⟩ := (hb' t ht).1 r
          beta_reduce at h1 h2
          by_cases hrm : r ∈ cs.args
          · obtain ⟨-, -, hlo, hhi⟩ := hargs r hrm
            have := h2 hrm
            constructor <;> omega
          · rw [h1 hrm]; exact hbN r
    obtain ⟨T', hT', hTb'⟩ := hstep
    refine ⟨T + T', by rw [MultiTapeTM.runFrom_add, hT, hT'], ?_⟩
    apply runFrom_forall_append (Q := fun g =>
      (∀ r, lo r ≤ g.workTapePos (Fin.castAdd kD r) ∧ g.workTapePos (Fin.castAdd kD r) ≤ hi r) ∧
        ∀ i, |g.workTapePos (Fin.natAdd m i)| ≤ B) hTb
    rw [hT]
    exact hTb'

/-- The space used up to time `T` is bounded by the sizes of ranges containing every head
at every time up to `T`. -/
lemma spaceUsed_le_of_ranges {K : ℕ} {S : Type} (tm : MultiTapeTM K Bool S)
    (c : Cfg K Bool S x) (T : ℕ) (lo hi : Fin K → ℤ)
    (h : ∀ t ≤ T, ∀ i, lo i ≤ (tm.runFrom c t).workTapePos i ∧
      (tm.runFrom c t).workTapePos i ≤ hi i) :
    tm.spaceUsed c T ≤ ∑ i, (hi i - lo i + 1).toNat := by
  unfold MultiTapeTM.spaceUsed MultiTapeTM.spaceUsedByTape
  refine Finset.sum_le_sum fun i _ => ?_
  have hsub : tm.visitedByTapeHead c T i ⊆ Finset.Icc (lo i) (hi i) := by
    intro z hz
    simp only [MultiTapeTM.visitedByTapeHead, Finset.mem_image, Finset.mem_range] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    rw [Finset.mem_Icc]
    exact h t (by omega) i
  refine (Finset.card_le_card hsub).trans (le_of_eq ?_)
  rw [Int.card_Icc]
  congr 1
  ring

/-- The compiled machine as a bundled finite machine. -/
def compileFinTM [Fintype Λ] [DecidableEq Λ] [Fintype SD] [DecidableEq SD]
    (P : RProg m d Λ) (l₀ : Λ) (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD) : FinTM Bool where
  k := m + kD
  State := CSt Λ SD m
  tm := compileTM P l₀ D q0

/-- **The compiled machine computes what the program computes, in the program's space plus
the deciders' space**: if the program halts after `N` steps with output `w`, register heads
in `[lo r, hi r]`, and all calls meet their preconditions with decider head range `B`, then
the compiled machine halts on `x` with output `w`, having visited at most
`∑ r (hi r - lo r + 1) + kD (2B + 1)` work cells.

**Proof sketch.** `compile_correct` gives the halting time and the head ranges;
`spaceUsed_le_of_ranges` turns ranges into space, the register tapes and the decider tapes
being the two blocks of `Fin (m + kD)`. -/
theorem compile_space [Fintype Λ] [DecidableEq Λ] [Fintype SD] [DecidableEq SD]
    (P : RProg m d Λ) (l₀ : Λ) (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD)
    (oracle : Fin d → List Bool → Bool) (lo hi : Fin m → ℤ) (B N : ℕ) (w : List Bool)
    (hhalt : (rrun P oracle (Cfg.init l₀ x) N).state = none)
    (hout : (rrun P oracle (Cfg.init l₀ x) N).output = w)
    (hbox : ∀ t ≤ N, ∀ r, lo r ≤ (rrun P oracle (Cfg.init l₀ x) t).workTapePos r ∧
      (rrun P oracle (Cfg.init l₀ x) t).workTapePos r ≤ hi r)
    (hcalls : ∀ t < N, CallOK P D q0 oracle lo hi B (rrun P oracle (Cfg.init l₀ x) t)) :
    ∃ T, (compileFinTM P l₀ D q0).ComputesInTime x w T ∧
      (compileFinTM P l₀ D q0).tm.spaceUsed ((compileFinTM P l₀ D q0).tm.initCfg x) T ≤
        ∑ r, (hi r - lo r + 1).toNat + kD * (2 * B + 1) := by
  obtain ⟨T, hT, hTb⟩ := compile_correct P l₀ D q0 oracle lo hi B N hbox hcalls
  refine ⟨T, ?_, ?_⟩
  · rw [FinTM.computesInTime_iff]
    change ((compileTM P l₀ D q0).runFrom ((compileTM P l₀ D q0).initCfg x) T).state = none ∧
      ((compileTM P l₀ D q0).runFrom ((compileTM P l₀ D q0).initCfg x) T).output = w
    rw [hT]
    exact ⟨by show Option.map _ _ = none; rw [hhalt]; rfl, by show _ = w; exact hout⟩
  · change (compileTM P l₀ D q0).spaceUsed ((compileTM P l₀ D q0).initCfg x) T ≤ _
    have := spaceUsed_le_of_ranges (compileTM P l₀ D q0) ((compileTM P l₀ D q0).initCfg x) T
      (Fin.append lo (fun _ => -(B : ℤ))) (Fin.append hi (fun _ => (B : ℤ))) (by
        intro t ht i
        refine Fin.addCases (fun r => ?_) (fun j => ?_) i
        · simpa using (hTb t ht).1 r
        · have := (hTb t ht).2 j
          simp only [Fin.append_right]
          rw [abs_le] at this
          exact this)
    refine this.trans (le_of_eq ?_)
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
    congr 1
    congr 1
    omega

end Complexity.LogProg

```


## ===== TCSlib/Complexity/SpaceComplexity/Machines/CleanSweep.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.Compile
import TCSlib.Complexity.SpaceComplexity.ConfigCount

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The cleaned machine and its cleanup sweeps

The first half of `TCSlib.Complexity.SpaceComplexity.Machines.Clean`: the cleaned machine
`Complexity.LogProg.cleanTM M` (simulate `M` while marking visited cells on mark tapes, then
sweep every tape) and the runs of the three sweeps of one tape: right to the end of the
marked interval, left erasing it, and back to the origin mark.

## Main definitions

* `Complexity.LogProg.cleanTM` — the cleaned machine.

## Main results

* `Complexity.LogProg.goR_run`, `Complexity.LogProg.erase_run`,
  `Complexity.LogProg.back_run` — the sweeps of one tape.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.1.)
-/

namespace Complexity.LogProg

open Turing

/-- The cleanup phases for one work tape. -/
inductive CPh where
  /-- mark the current cell -/
  | mark
  /-- walk right over the marked cells -/
  | goR
  /-- walk left over the marked cells, erasing -/
  | erase
  /-- walk right back to the origin mark, and erase it -/
  | back
  deriving DecidableEq, Fintype

/-- The states of the cleaned machine. -/
inductive CleanSt (S : Type) (k : ℕ) where
  /-- write the origin marks, then simulate from state `q` -/
  | init (q : S)
  /-- simulate the original machine in state `q` -/
  | sim (q : S)
  /-- clean work tape `i`, in phase `ph` -/
  | cl (i : Fin k) (ph : CPh)
  deriving DecidableEq, Fintype

variable {k : ℕ} {S : Type}

/-- The idle action on a block of tapes. -/
def idleK : Fin k → Option (Option Bool) × SignType := fun _ => (none, 0)

/-- The action of a cleanup phase on tape `i` and its mark tape: optional writes `wD`, `wM`,
both heads moving by `mv`. -/
def clAct (i : Fin k) (wD wM : Option (Option Bool)) (mv : SignType) (st : Option (CleanSt S k)) :
    Action (k + k) Bool (CleanSt S k) :=
  ⟨0, Fin.append (fun j => if j = i then (wD, mv) else (none, 0))
    (fun j => if j = i then (wM, mv) else (none, 0)), none, st⟩

/-- The state after cleaning tape `i`: the next tape, or halt. -/
def clNext (i : Fin k) : Option (CleanSt S k) :=
  if h : i.val + 1 < k then some (.cl ⟨i.val + 1, h⟩ .mark) else none

/-- **The cleaned machine.** Work tapes `0, …, k - 1` are `M`'s, tapes `k, …, 2k - 1` the
mark tapes. -/
def cleanTM (M : MultiTapeTM k Bool S) (q₀ : S) : MultiTapeTM (k + k) Bool (CleanSt S k) where
  q₀ := .init q₀
  tr
    | .init q, _, _ =>
      ⟨0, Fin.append idleK (fun _ => (some (some true), 0)), none, some (.sim q)⟩
    | .sim q, a, w =>
      let act := M.tr q a (fun i => w (Fin.castAdd k i))
      ⟨act.inputTape,
        Fin.append act.workTapes (fun i =>
          (if w (Fin.natAdd k i) = some true then none else some (some false),
            (act.workTapes i).2)),
        act.output,
        match act.state with
        | some q' => some (.sim q')
        | none => if h : 0 < k then some (.cl ⟨0, h⟩ .mark) else none⟩
    | .cl i .mark, _, w =>
      clAct i none (if w (Fin.natAdd k i) = some true then none else some (some false)) 0
        (some (.cl i .goR))
    | .cl i .goR, _, w =>
      if (w (Fin.natAdd k i)).isSome then clAct i none none 1 (some (.cl i .goR))
      else clAct i none none (-1) (some (.cl i .erase))
    | .cl i .erase, _, w =>
      match w (Fin.natAdd k i) with
      | some true => clAct i (some none) none (-1) (some (.cl i .erase))
      | some false => clAct i (some none) (some none) (-1) (some (.cl i .erase))
      | none => clAct i none none 1 (some (.cl i .back))
    | .cl i .back, _, w =>
      match w (Fin.natAdd k i) with
      | some true => clAct i none (some none) 0 (clNext i)
      | _ => clAct i none none 1 (some (.cl i .back))

/-- A configuration of the cleaned machine from its two blocks. -/
def ccfg {x : List Bool} (st : Option (CleanSt S k)) (ip : Fin (x.length + 2))
    (Dt : Fin k → ℤ → Option Bool) (Dp : Fin k → ℤ) (Mt : Fin k → ℤ → Option Bool)
    (Mp : Fin k → ℤ) (out : List Bool) : Cfg (k + k) Bool (CleanSt S k) x :=
  ⟨st, ip, Fin.append Dt Mt, Fin.append Dp Mp, out⟩

/-- The configuration built by `ccfg st …` is in state `st`. -/
@[simp] lemma ccfg_state {x : List Bool} (st : Option (CleanSt S k)) (ip : Fin (x.length + 2))
    (Dt : Fin k → ℤ → Option Bool) (Dp : Fin k → ℤ) (Mt : Fin k → ℤ → Option Bool)
    (Mp : Fin k → ℤ) (out : List Bool) : (ccfg st ip Dt Dp Mt Mp out).state = st := rfl

/-- A `ccfg` configuration reads mark tape `i` at the mark head position. -/
@[simp] lemma ccfg_mark {x : List Bool} (st : Option (CleanSt S k)) (ip : Fin (x.length + 2))
    (Dt : Fin k → ℤ → Option Bool) (Dp : Fin k → ℤ) (Mt : Fin k → ℤ → Option Bool)
    (Mp : Fin k → ℤ) (out : List Bool) (i : Fin k) :
    (ccfg st ip Dt Dp Mt Mp out).workTapeSymbols (Fin.natAdd k i) = Mt i (Mp i) := by
  simp only [ccfg, Cfg.workTapeSymbols, Fin.append_right]

/-- A `ccfg` configuration reads decider tape `i` at the decider head position. -/
@[simp] lemma ccfg_work {x : List Bool} (st : Option (CleanSt S k)) (ip : Fin (x.length + 2))
    (Dt : Fin k → ℤ → Option Bool) (Dp : Fin k → ℤ) (Mt : Fin k → ℤ → Option Bool)
    (Mp : Fin k → ℤ) (out : List Bool) (i : Fin k) :
    (ccfg st ip Dt Dp Mt Mp out).workTapeSymbols (Fin.castAdd k i) = Dt i (Dp i) := by
  simp only [ccfg, Cfg.workTapeSymbols, Fin.append_left]

/-- Apply an optional write at a position. -/
def wr (w : Option (Option Bool)) (f : ℤ → Option Bool) (p : ℤ) : ℤ → Option Bool :=
  match w with
  | none => f
  | some s => Function.update f p s

/-- The effect of a cleanup action.

**Proof sketch.** Unfold the action's application on a `ccfg` configuration: it writes the
decider and mark cells of tape `i` under their heads and moves both heads of tape `i` by `mv`.
Both updates commute with `Fin.append`, which is checked tape by tape on the two blocks. -/
lemma apply_clAct {x : List Bool} (i : Fin k) (wD wM : Option (Option Bool)) (mv : SignType)
    (st st' : Option (CleanSt S k)) (ip : Fin (x.length + 2)) (Dt : Fin k → ℤ → Option Bool)
    (Dp : Fin k → ℤ) (Mt : Fin k → ℤ → Option Bool) (Mp : Fin k → ℤ) (out : List Bool) :
    (clAct i wD wM mv st').apply (ccfg st ip Dt Dp Mt Mp out) =
      ccfg st' ip (Function.update Dt i (wr wD (Dt i) (Dp i)))
        (Function.update Dp i (Dp i + mv)) (Function.update Mt i (wr wM (Mt i) (Mp i)))
        (Function.update Mp i (Mp i + mv)) out := by
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ (by simp [clAct, ccfg])
  · funext j z
    refine Fin.addCases (fun r => ?_) (fun r => ?_) j
    · simp only [clAct, ccfg, Action.apply, Fin.append_left]
      by_cases h : r = i
      · subst h; cases wD <;> simp [wr]
      · simp [h]
    · simp only [clAct, ccfg, Action.apply, Fin.append_right]
      by_cases h : r = i
      · subst h; cases wM <;> simp [wr]
      · simp [h]
  · funext j
    refine Fin.addCases (fun r => ?_) (fun r => ?_) j
    · simp only [clAct, ccfg, Action.apply, Fin.append_left]
      by_cases h : r = i
      · subst h; simp
      · simp [h]
    · simp only [clAct, ccfg, Action.apply, Fin.append_right]
      by_cases h : r = i
      · subst h; simp
      · simp [h]

/-! ## The cleanup sweeps of one tape -/

/-- The mark tape of an interval `[a, b]` around the origin: the origin mark at `0`, plain
marks on the rest of `[a, b]`. -/
def markI (a b : ℤ) (z : ℤ) : Option Bool :=
  if z = 0 then some true else if a ≤ z ∧ z ≤ b then some false else none

/-- All heads of a configuration of the cleaned machine lie in `[-B, B]`. -/
def PB {x : List Bool} (B : ℤ) (g : Cfg (k + k) Bool (CleanSt S k) x) : Prop :=
  ∀ j, |g.workTapePos j| ≤ B

/-- A `ccfg` configuration whose decider and mark heads are within `B` of the origin has all
work heads within `B`. -/
lemma PB_ccfg {x : List Bool} (B : ℤ) (st : Option (CleanSt S k)) (ip : Fin (x.length + 2))
    (Dt : Fin k → ℤ → Option Bool) (Dp : Fin k → ℤ) (Mt : Fin k → ℤ → Option Bool)
    (Mp : Fin k → ℤ) (out : List Bool) (hD : ∀ j, |Dp j| ≤ B) (hM : ∀ j, |Mp j| ≤ B) :
    PB B (ccfg st ip Dt Dp Mt Mp out) := by
  intro j
  refine Fin.addCases (fun r => ?_) (fun r => ?_) j
  · simp only [ccfg, Fin.append_left]; exact hD r
  · simp only [ccfg, Fin.append_right]; exact hM r

/-- Updating one coordinate of a family bounded by `B` with a value bounded by `B` keeps the
family bounded by `B`. -/
lemma abs_update_le (Dp : Fin k → ℤ) (i : Fin k) (v B : ℤ) (h : ∀ j, |Dp j| ≤ B)
    (hv : |v| ≤ B) : ∀ j, |Function.update Dp i v j| ≤ B := by
  intro j
  by_cases hj : j = i
  · subst hj; simpa using hv
  · rw [Function.update_of_ne hj]; exact h j

section Sweeps

variable (M : MultiTapeTM k Bool S) (q₀ : S) {x : List Bool} (i : Fin k)
  (ip : Fin (x.length + 2)) (out : List Bool) (B : ℤ)

/-- The walk right over the marked interval `[a, b]`, ending on `b` in the erase phase.

**Proof sketch.** Induction on `n = b + 1 - Dp i`. Inside the marked interval the mark tape
reads a mark, so both heads of tape `i` move right; just past `b` the mark tape is blank, so
they move back onto `b` and the erase phase begins. All heads stay within `B`. -/
lemma goR_run (a b : ℤ) (Dt : Fin k → ℤ → Option Bool) (Mt : Fin k → ℤ → Option Bool)
    (hMt : Mt i = markI a b) (hb : 0 ≤ b) (hbB : b + 1 ≤ B) :
    ∀ (n : ℕ) (Dp : Fin k → ℤ), b + 1 - Dp i = n → a ≤ Dp i → (∀ j, |Dp j| ≤ B) →
      (∀ t ≤ n + 1, PB B ((cleanTM M q₀).runFrom
          (ccfg (some (.cl i .goR)) ip Dt Dp Mt Dp out) t)) ∧
      (cleanTM M q₀).runFrom (ccfg (some (.cl i .goR)) ip Dt Dp Mt Dp out) (n + 1) =
        ccfg (some (.cl i .erase)) ip Dt (Function.update Dp i b) Mt (Function.update Dp i b)
          out := by
  intro n
  induction n with
  | zero =>
    intro Dp hn _ hB
    have hp : Dp i = b + 1 := by omega
    have hrd : Mt i (Dp i) = none := by
      rw [hMt, hp]; simp only [markI]; split_ifs <;> first | omega | rfl
    have hstep : (cleanTM M q₀).step (ccfg (some (.cl i .goR)) ip Dt Dp Mt Dp out) =
        ccfg (some (.cl i .erase)) ip Dt (Function.update Dp i b) Mt (Function.update Dp i b)
          out := by
      unfold MultiTapeTM.step
      simp only [ccfg_state, cleanTM, ccfg_mark, hrd, Option.isSome_none, Bool.false_eq_true,
        ↓reduceIte]
      rw [apply_clAct]
      simp [wr, hp]
    have hbB' : |b| ≤ B := by have := hB i; rw [hp] at this; rw [abs_le] at this ⊢; omega
    refine ⟨fun t ht => ?_, by simpa using hstep⟩
    rcases Nat.lt_or_ge t 1 with h | h
    · obtain rfl : t = 0 := by omega
      exact PB_ccfg _ _ _ _ _ _ _ _ hB hB
    · obtain rfl : t = 1 := by omega
      rw [show (cleanTM M q₀).runFrom _ 1 = (cleanTM M q₀).step _ from rfl, hstep]
      exact PB_ccfg _ _ _ _ _ _ _ _ (abs_update_le _ _ _ _ hB hbB')
        (abs_update_le _ _ _ _ hB hbB')
  | succ n ih =>
    intro Dp hn ha hB
    have hin : a ≤ Dp i ∧ Dp i ≤ b := ⟨ha, by omega⟩
    have hrd : Mt i (Dp i) ≠ none := by
      rw [hMt]; unfold markI; split_ifs <;> simp_all
    set Dp' := Function.update Dp i (Dp i + 1) with hDp'
    have hstep : (cleanTM M q₀).step (ccfg (some (.cl i .goR)) ip Dt Dp Mt Dp out) =
        ccfg (some (.cl i .goR)) ip Dt Dp' Mt Dp' out := by
      unfold MultiTapeTM.step
      simp only [ccfg_state, cleanTM, ccfg_mark, Option.isSome_iff_ne_none.mpr hrd,
        ↓reduceIte]
      rw [apply_clAct]
      simp [wr, hDp']
    have hB' : ∀ j, |Dp' j| ≤ B := abs_update_le _ _ _ _ hB (by
      have := hB i; rw [abs_le] at this ⊢; constructor <;> omega)
    obtain ⟨ihb, ihr⟩ := ih Dp' (by simp [hDp']; omega) (by simp [hDp']; omega) hB'
    refine ⟨fun t ht => ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos t with h | h
      · subst h; exact PB_ccfg _ _ _ _ _ _ _ _ hB hB
      · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
        rw [MultiTapeTM.runFrom_succ_eq_step, hstep]
        exact ihb t' (by omega)
    · rw [MultiTapeTM.runFrom_succ_eq_step, hstep, ihr]
      simp [hDp']

/-- A tape erased strictly above position `p`. -/
def eraseAbove (f : ℤ → Option Bool) (p : ℤ) : ℤ → Option Bool := fun z => if z ≤ p then f z else none

/-- The walk left over the marked interval, erasing it (keeping the origin mark), ending on
`a` in the back phase.

**Proof sketch.** Induction on `n = Dp i - (a - 1)`. At each marked cell the decider cell is
erased and the mark is erased too, except at the origin mark `true`, and both heads move left.
Past `a` the mark tape is blank, so the heads move back right onto `a` and the back phase
begins. -/
lemma erase_run (a b : ℤ) (f : ℤ → Option Bool) (ha : a ≤ 0) (haB : -B ≤ a - 1) :
    ∀ (n : ℕ) (Dt Mt : Fin k → ℤ → Option Bool) (Dp : Fin k → ℤ), Dp i - (a - 1) = n →
      Dp i ≤ b → Dt i = eraseAbove f (Dp i) → Mt i = markI a (Dp i) → (∀ j, |Dp j| ≤ B) →
      (∀ t ≤ n + 1, PB B ((cleanTM M q₀).runFrom
          (ccfg (some (.cl i .erase)) ip Dt Dp Mt Dp out) t)) ∧
      (cleanTM M q₀).runFrom (ccfg (some (.cl i .erase)) ip Dt Dp Mt Dp out) (n + 1) =
        ccfg (some (.cl i .back)) ip (Function.update Dt i (eraseAbove f (a - 1)))
          (Function.update Dp i a) (Function.update Mt i (markI a (a - 1)))
          (Function.update Dp i a) out := by
  intro n
  induction n with
  | zero =>
    intro Dt Mt Dp hn _ hDt hMt hB
    have hp : Dp i = a - 1 := by omega
    have hrd : Mt i (Dp i) = none := by
      rw [hMt, hp]; simp only [markI]; split_ifs <;> first | omega | rfl
    have hstep : (cleanTM M q₀).step (ccfg (some (.cl i .erase)) ip Dt Dp Mt Dp out) =
        ccfg (some (.cl i .back)) ip (Function.update Dt i (eraseAbove f (a - 1)))
          (Function.update Dp i a) (Function.update Mt i (markI a (a - 1)))
          (Function.update Dp i a) out := by
      unfold MultiTapeTM.step
      simp only [ccfg_state, cleanTM, ccfg_mark, hrd]
      rw [apply_clAct]
      have e1 : Function.update Dt i (Dt i) = Function.update Dt i (eraseAbove f (a - 1)) := by
        rw [hDt, hp]
      have e2 : Function.update Mt i (Mt i) = Function.update Mt i (markI a (a - 1)) := by
        rw [hMt, hp]
      simp only [wr]
      rw [e1, e2, hp]
      congr 2 <;> simp
    have haB' : |a| ≤ B := by
      have := hB i; rw [hp, abs_le] at this; rw [abs_le]; omega
    refine ⟨fun t ht => ?_, by simpa using hstep⟩
    rcases Nat.lt_or_ge t 1 with h | h
    · obtain rfl : t = 0 := by omega
      exact PB_ccfg _ _ _ _ _ _ _ _ hB hB
    · obtain rfl : t = 1 := by omega
      rw [show (cleanTM M q₀).runFrom _ 1 = (cleanTM M q₀).step _ from rfl, hstep]
      exact PB_ccfg _ _ _ _ _ _ _ _ (abs_update_le _ _ _ _ hB haB')
        (abs_update_le _ _ _ _ hB haB')
  | succ n ih =>
    intro Dt Mt Dp hn hpb hDt hMt hB
    set p := Dp i with hpdef
    have hpa : a ≤ p := by omega
    set Dp' := Function.update Dp i (p - 1) with hDp'
    set Dt' := Function.update Dt i (eraseAbove f (p - 1)) with hDt'
    set Mt' := Function.update Mt i (markI a (p - 1)) with hMt'
    have hstep : (cleanTM M q₀).step (ccfg (some (.cl i .erase)) ip Dt Dp Mt Dp out) =
        ccfg (some (.cl i .erase)) ip Dt' Dp' Mt' Dp' out := by
      unfold MultiTapeTM.step
      simp only [ccfg_state, cleanTM, ccfg_mark]
      have hEr : Function.update (Dt i) p none = eraseAbove f (p - 1) := by
        rw [hDt]; funext z; simp only [eraseAbove, Function.update_apply]
        split_ifs <;> first | rfl | omega
      by_cases hp0 : p = 0
      · have hrd : Mt i p = some true := by rw [hMt]; simp [markI, hp0]
        rw [← hpdef, hrd]
        rw [apply_clAct]
        simp only [wr, ← hpdef, hEr]
        have hM : Function.update Mt i (Mt i) = Mt' := by
          rw [hMt', hMt]; congr 1; funext z; simp only [markI]; split_ifs <;> first | rfl | omega
        rw [hM]
        congr 2
      · have hrd : Mt i p = some false := by
          rw [hMt]; simp only [markI]; split_ifs <;> first | rfl | omega
        rw [← hpdef, hrd]
        rw [apply_clAct]
        simp only [wr, ← hpdef, hEr]
        have hM : Function.update (Mt i) p none = markI a (p - 1) := by
          rw [hMt]; funext z; simp only [markI, Function.update_apply]
          split_ifs <;> first | rfl | omega
        rw [hM]
        congr 2
    have hB' : ∀ j, |Dp' j| ≤ B := abs_update_le _ _ _ _ hB (by
      have := hB i; rw [abs_le] at this ⊢; constructor <;> omega)
    obtain ⟨ihb, ihr⟩ := ih Dt' Mt' Dp' (by simp [hDp']; omega) (by simp [hDp']; omega)
      (by simp [hDt', hDp']) (by simp [hMt', hDp']) hB'
    refine ⟨fun t ht => ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos t with h | h
      · subst h; exact PB_ccfg _ _ _ _ _ _ _ _ hB hB
      · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
        rw [MultiTapeTM.runFrom_succ_eq_step, hstep]
        exact ihb t' (by omega)
    · rw [MultiTapeTM.runFrom_succ_eq_step, hstep, ihr]
      simp [hDp', hDt', hMt']

/-- The origin-only mark tape is `markI a (a - 1)`. -/
lemma markI_empty (a : ℤ) (z : ℤ) : markI a (a - 1) z = if z = 0 then some true else none := by
  simp only [markI]; split_ifs <;> first | rfl | omega

/-- The walk right back to the origin mark, which is erased; tape `i` is then clean.

**Proof sketch.** Induction on `n = -Dp i`. The heads walk right over the erased cells until the
origin mark, which is erased; the machine then moves on to the next tape (`clNext i`), with tape
`i`'s heads at `0` and its mark tape blank. -/
lemma back_run (a : ℤ) :
    ∀ (n : ℕ) (Dt Mt : Fin k → ℤ → Option Bool) (Dp : Fin k → ℤ), -Dp i = n → a ≤ Dp i →
      Mt i = markI a (a - 1) → (∀ j, |Dp j| ≤ B) →
      (∀ t ≤ n + 1, PB B ((cleanTM M q₀).runFrom
          (ccfg (some (.cl i .back)) ip Dt Dp Mt Dp out) t)) ∧
      (cleanTM M q₀).runFrom (ccfg (some (.cl i .back)) ip Dt Dp Mt Dp out) (n + 1) =
        ccfg (clNext i) ip Dt (Function.update Dp i 0) (Function.update Mt i (fun _ => none))
          (Function.update Dp i 0) out := by
  intro n
  induction n with
  | zero =>
    intro Dt Mt Dp hn _ hMt hB
    have hp : Dp i = 0 := by omega
    have hrd : Mt i (Dp i) = some true := by rw [hMt, hp, markI_empty]; rfl
    have hstep : (cleanTM M q₀).step (ccfg (some (.cl i .back)) ip Dt Dp Mt Dp out) =
        ccfg (clNext i) ip Dt (Function.update Dp i 0) (Function.update Mt i (fun _ => none))
          (Function.update Dp i 0) out := by
      unfold MultiTapeTM.step
      simp only [ccfg_state, cleanTM, ccfg_mark, hrd]
      rw [apply_clAct]
      simp only [wr]
      have e1 : Function.update (Mt i) (Dp i) none = fun _ => none := by
        rw [hMt, hp]; funext z; rw [Function.update_apply, markI_empty]
        split_ifs <;> rfl
      rw [e1, hp]
      congr 2; simp
    refine ⟨fun t ht => ?_, by simpa using hstep⟩
    rcases Nat.lt_or_ge t 1 with h | h
    · obtain rfl : t = 0 := by omega
      exact PB_ccfg _ _ _ _ _ _ _ _ hB hB
    · obtain rfl : t = 1 := by omega
      rw [show (cleanTM M q₀).runFrom _ 1 = (cleanTM M q₀).step _ from rfl, hstep]
      have h0 : |(0 : ℤ)| ≤ B := by have := hB i; rw [hp] at this; exact this
      exact PB_ccfg _ _ _ _ _ _ _ _ (abs_update_le _ _ _ _ hB h0) (abs_update_le _ _ _ _ hB h0)
  | succ n ih =>
    intro Dt Mt Dp hn hpa hMt hB
    have hrd : Mt i (Dp i) = none := by
      rw [hMt, markI_empty]; split_ifs <;> first | rfl | omega
    set Dp' := Function.update Dp i (Dp i + 1) with hDp'
    have hstep : (cleanTM M q₀).step (ccfg (some (.cl i .back)) ip Dt Dp Mt Dp out) =
        ccfg (some (.cl i .back)) ip Dt Dp' Mt Dp' out := by
      unfold MultiTapeTM.step
      simp only [ccfg_state, cleanTM, ccfg_mark, hrd]
      rw [apply_clAct]
      simp [wr, hDp']
    have hB' : ∀ j, |Dp' j| ≤ B := abs_update_le _ _ _ _ hB (by
      have := hB i; rw [abs_le] at this ⊢; constructor <;> omega)
    obtain ⟨ihb, ihr⟩ := ih Dt Mt Dp' (by simp [hDp']; omega) (by simp [hDp']; omega) hMt hB'
    refine ⟨fun t ht => ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos t with h | h
      · subst h; exact PB_ccfg _ _ _ _ _ _ _ _ hB hB
      · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
        rw [MultiTapeTM.runFrom_succ_eq_step, hstep]
        exact ihb t' (by omega)
    · rw [MultiTapeTM.runFrom_succ_eq_step, hstep, ihr]
      simp [hDp']

/-- **Cleaning one tape.** If, after marking the current cell, the mark tape of tape `i` marks
an interval `[a, b]` around the origin that contains the head and every nonblank cell of
tape `i`, then the cleanup of tape `i` blanks it and its mark tape, returns both heads to the
origin, and moves on; the heads stay in `[a - 1, b + 1]`.

**Proof sketch.** One marking step, then `goR_run`, `erase_run` (every nonblank cell lies in
`[a, b]`, so nothing survives) and `back_run`. -/
lemma clean_tape (a b : ℤ) (Dt Mt : Fin k → ℤ → Option Bool) (Dp : Fin k → ℤ)
    (ha : a ≤ 0) (hb : 0 ≤ b) (haB : -B ≤ a - 1) (hbB : b + 1 ≤ B)
    (hh : a ≤ Dp i ∧ Dp i ≤ b)
    (hMt : wr (if Mt i (Dp i) = some true then none else some (some false)) (Mt i) (Dp i) =
      markI a b)
    (hsupp : ∀ z, Dt i z ≠ none → a ≤ z ∧ z ≤ b) (hB : ∀ j, |Dp j| ≤ B) :
    ∃ T, (∀ t ≤ T, PB B ((cleanTM M q₀).runFrom
        (ccfg (some (.cl i .mark)) ip Dt Dp Mt Dp out) t)) ∧
      (cleanTM M q₀).runFrom (ccfg (some (.cl i .mark)) ip Dt Dp Mt Dp out) T =
        ccfg (clNext i) ip (Function.update Dt i (fun _ => none)) (Function.update Dp i 0)
          (Function.update Mt i (fun _ => none)) (Function.update Dp i 0) out := by
  set Mt1 := Function.update Mt i (markI a b) with hMt1
  have hstep : (cleanTM M q₀).step (ccfg (some (.cl i .mark)) ip Dt Dp Mt Dp out) =
      ccfg (some (.cl i .goR)) ip Dt Dp Mt1 Dp out := by
    unfold MultiTapeTM.step
    simp only [ccfg_state, cleanTM, ccfg_mark]
    rw [apply_clAct]
    simp only [wr, Function.update_eq_self, SignType.coe_zero, add_zero]
    rw [hMt1, ← hMt]
    rfl
  obtain ⟨hb1, hr1⟩ := goR_run M q₀ i ip out B a b Dt Mt1 (by simp [hMt1]) hb hbB
    (b + 1 - Dp i).toNat Dp (by omega) hh.1 hB
  set Dpb := Function.update Dp i b with hDpb
  have hBb : ∀ j, |Dpb j| ≤ B := abs_update_le _ _ _ _ hB (by rw [abs_le]; omega)
  have hDte : Dt i = eraseAbove (Dt i) (Dpb i) := by
    funext z; simp only [eraseAbove, hDpb, Function.update_self]
    split_ifs with h
    · rfl
    · by_contra hne; exact h (hsupp z (fun h0 => hne (by rw [h0]))).2
  obtain ⟨hb2, hr2⟩ := erase_run M q₀ i ip out B a b (Dt i) ha haB (b - (a - 1)).toNat Dt Mt1 Dpb
    (by simp [hDpb]; omega) (by simp [hDpb]) hDte (by simp [hMt1, hDpb]) hBb
  set Dpa := Function.update Dpb i a with hDpa
  have hBa : ∀ j, |Dpa j| ≤ B := abs_update_le _ _ _ _ hBb (by rw [abs_le]; omega)
  have hblank : eraseAbove (Dt i) (a - 1) = fun _ => none := by
    funext z; simp only [eraseAbove]
    split_ifs with h
    · by_contra hne; have := (hsupp z hne).1; omega
    · rfl
  rw [hblank] at hr2
  obtain ⟨hb3, hr3⟩ := back_run M q₀ i ip out B a (-a).toNat (Function.update Dt i fun _ => none)
    (Function.update Mt1 i (markI a (a - 1))) Dpa (by simp [hDpa]; omega) (by simp [hDpa])
    (by simp) hBa
  refine ⟨1 + ((b + 1 - Dp i).toNat + 1 + ((b - (a - 1)).toNat + 1 + ((-a).toNat + 1))),
    ?_, ?_⟩
  · apply Complexity.LogProg.runFrom_forall_append (Q := PB B)
    · intro t ht
      rcases Nat.lt_or_ge t 1 with h | h
      · obtain rfl : t = 0 := by omega
        exact PB_ccfg _ _ _ _ _ _ _ _ hB hB
      · obtain rfl : t = 1 := by omega
        rw [show (cleanTM M q₀).runFrom _ 1 = (cleanTM M q₀).step _ from rfl, hstep]
        exact PB_ccfg _ _ _ _ _ _ _ _ hB hB
    rw [show (cleanTM M q₀).runFrom _ 1 = (cleanTM M q₀).step _ from rfl, hstep]
    apply Complexity.LogProg.runFrom_forall_append (Q := PB B) hb1
    rw [hr1]
    apply Complexity.LogProg.runFrom_forall_append (Q := PB B) hb2
    rw [hr2]
    exact hb3
  · rw [MultiTapeTM.runFrom_add,
      show (cleanTM M q₀).runFrom _ 1 = (cleanTM M q₀).step _ from rfl, hstep,
      MultiTapeTM.runFrom_add, hr1, MultiTapeTM.runFrom_add, hr2, hr3]
    simp [hDpa, hDpb, hMt1]

end Sweeps

end Complexity.LogProg

```


## ===== TCSlib/Complexity/SpaceComplexity/Machines/Clean.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.CleanSweep

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Cleaning up after a computation

A subroutine that is called again and again must leave its work tapes as it found them.
[AB09, §4.1.1] remarks that a space-bounded machine can be modified "to erase all its work
tapes before halting". This file carries that out for the machine model of the campaign:
`Complexity.LogProg.cleanTM M` simulates `M` while marking, on one extra *mark tape* per work
tape, every cell the work head visits (the origin with a distinguished mark); when `M` halts,
each work tape is swept: right to the end of the marked interval, left erasing it (the
visited cells form an interval around the origin, so this erases every nonblank cell), and
right again to the origin mark. The cleaned machine has the same output, twice as many work
tapes, and its heads stay within one cell of `M`'s visited cells
(`Complexity.LogProg.cleanTM_run`).

The definition of `Complexity.LogProg.cleanTM` and the sweeps of one tape are in
`TCSlib.Complexity.SpaceComplexity.Machines.CleanSweep`, which this file re-exports.

## Main definitions

* `Complexity.LogProg.cleanTM` — the cleaned machine.

## Main results

* `Complexity.LogProg.cleanTM_run` — from `init q`, the cleaned machine halts with `M`'s
  output, blank work tapes and heads at the origin, its heads staying within `[-s, s]` when
  `M` (started in `q`) visits at most `s` cells per tape.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.1.)
-/

namespace Complexity.LogProg

open Turing

variable {k : ℕ} {S : Type}

/-! ## The simulation phase and the whole run -/

/-- The mark tape of a set of visited cells (the origin always carries the origin mark). -/
def markSet (F : Finset ℤ) (z : ℤ) : Option Bool :=
  if z = 0 then some true else if z ∈ F then some false else none

/-- The state of the cleaned machine simulating a configuration of `M`. -/
def simSt {x : List Bool} (c : Cfg k Bool S x) : Option (CleanSt S k) :=
  match c.state with
  | some q' => some (.sim q')
  | none => if h : 0 < k then some (.cl ⟨0, h⟩ .mark) else none

section Run

variable (M : MultiTapeTM k Bool S) (q₁ q : S) (V : List Bool)

/-- The positions of work head `i` before time `t`. -/
def visB (t : ℕ) (i : Fin k) : Finset ℤ :=
  (Finset.range t).image fun t' => (M.runFrom (Cfg.init q V) t').workTapePos i

/-- The cleaned machine's configuration simulating `M` at time `t`. -/
def simCfg (t : ℕ) : Cfg (k + k) Bool (CleanSt S k) V :=
  ccfg (simSt (M.runFrom (Cfg.init q V) t)) (M.runFrom (Cfg.init q V) t).inputPos
    (M.runFrom (Cfg.init q V) t).workTapes (M.runFrom (Cfg.init q V) t).workTapePos
    (fun i => markSet (visB M q V t i)) (M.runFrom (Cfg.init q V) t).workTapePos
    (M.runFrom (Cfg.init q V) t).output

/-- The first step writes the origin marks.

**Proof sketch.** Unfold the first step from the initial state `init q`. It writes the origin
mark on every mark tape and enters the simulation state `sim q` without moving, which is `simCfg
M q V 0` (no cell visited yet besides the origin). Compare componentwise. -/
lemma init_step : (cleanTM M q₁).step (Cfg.init (.init q) V) = simCfg M q V 0 := by
  have e : simCfg M q V 0 = ccfg (some (.sim q)) 1 (fun _ _ => none) (fun _ => 0)
      (fun _ => markSet ∅) (fun _ => 0) [] := by
    simp only [simCfg, MultiTapeTM.runFrom_zero, visB, Finset.range_zero, Finset.image_empty]
    try rfl
  rw [e]
  unfold MultiTapeTM.step
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · simp only [Cfg.init, cleanTM, Action.apply, moveInputPos_zero]; rfl
  · funext i z
    refine Fin.addCases (fun r => ?_) (fun r => ?_) i
    · simp only [Cfg.init, cleanTM, Action.apply, ccfg, Fin.append_left, idleK]
    · simp only [Cfg.init, cleanTM, Action.apply, ccfg, Fin.append_right, markSet,
        Finset.notMem_empty, if_false, Function.update_apply]
  · funext i
    refine Fin.addCases (fun r => ?_) (fun r => ?_) i
    · simp only [Cfg.init, cleanTM, Action.apply, ccfg, Fin.append_left, idleK,
        SignType.coe_zero, add_zero]
    · simp only [Cfg.init, cleanTM, Action.apply, ccfg, Fin.append_right,
        SignType.coe_zero, add_zero]

/-- The cells visited by tape `i` in `t + 1` steps are those visited in `t` steps and the head
position after `t` steps. -/
lemma visB_succ (t : ℕ) (i : Fin k) :
    visB M q V (t + 1) i = insert ((M.runFrom (Cfg.init q V) t).workTapePos i) (visB M q V t i) := by
  simp only [visB, Finset.range_add_one, Finset.image_insert]

/-- Writing the mark of the current cell adds it to the marked set. -/
lemma wr_markSet (F : Finset ℤ) (p : ℤ) :
    wr (if markSet F p = some true then none else some (some false)) (markSet F) p =
      markSet (insert p F) := by
  funext z
  by_cases hp : p = 0
  · subst hp
    have h0 : markSet F 0 = some true := by simp [markSet]
    simp only [↓reduceIte, wr, markSet, Finset.mem_insert]
    by_cases hz : z = 0 <;> simp [hz]
  · have hm : markSet F p ≠ some true := by
      unfold markSet; rw [if_neg hp]; split_ifs <;> simp
    simp only [hm, ↓reduceIte, wr]
    by_cases hz : z = p
    · subst hz; simp [markSet, hp]
    · rw [Function.update_of_ne hz]; simp [markSet, Finset.mem_insert, hz]

end Run

/-- One simulated step, for an arbitrary live configuration of `M` and arbitrary marks.

**Proof sketch.** Unfold one step of the cleaned machine in a simulation state: it applies `M`'s
action to the decider block, writes a mark under each decider head (keeping the origin mark),
and moves the mark heads with the decider heads. Compare the configurations componentwise. -/
lemma step_sim {x : List Bool} (M : MultiTapeTM k Bool S) (q₁ : S) (c : Cfg k Bool S x)
    (q' : S) (hq' : c.state = some q') (Mt : Fin k → ℤ → Option Bool) :
    (cleanTM M q₁).step (ccfg (some (.sim q')) c.inputPos c.workTapes c.workTapePos Mt
        c.workTapePos c.output) =
      ccfg (simSt (M.step c)) (M.step c).inputPos (M.step c).workTapes (M.step c).workTapePos
        (fun i => wr (if Mt i (c.workTapePos i) = some true then none else some (some false))
          (Mt i) (c.workTapePos i)) (M.step c).workTapePos (M.step c).output := by
  have hMstep : M.step c = (M.tr q' c.inputSymbol c.workTapeSymbols).apply c := by
    unfold MultiTapeTM.step; rw [hq']
  rw [hMstep]
  unfold MultiTapeTM.step
  simp only [ccfg_state]
  have hin : (ccfg (some (.sim q')) c.inputPos c.workTapes c.workTapePos Mt c.workTapePos
      c.output : Cfg (k + k) Bool (CleanSt S k) x).inputSymbol = c.inputSymbol := rfl
  have hw : (fun i => (ccfg (some (.sim q')) c.inputPos c.workTapes c.workTapePos Mt
      c.workTapePos c.output : Cfg (k + k) Bool (CleanSt S k) x).workTapeSymbols
        (Fin.castAdd k i)) = c.workTapeSymbols := by
    funext i; rw [ccfg_work]; rfl
  simp only [cleanTM, hin, hw, ccfg_mark]
  refine Cfg.ext ?_ rfl ?_ ?_ ?_
  · simp only [Action.apply, ccfg, simSt]
    cases (M.tr q' c.inputSymbol c.workTapeSymbols).state <;> rfl
  · funext i z
    refine Fin.addCases (fun r => ?_) (fun r => ?_) i
    · simp only [Action.apply, ccfg, Fin.append_left]
    · simp only [Action.apply, ccfg, Fin.append_right, wr]
      try (split_ifs <;> rfl)
  · funext i
    refine Fin.addCases (fun r => ?_) (fun r => ?_) i
    · simp only [Action.apply, ccfg, Fin.append_left]
    · simp only [Action.apply, ccfg, Fin.append_right]
  · simp only [Action.apply, ccfg]

/-- **The simulation phase**: one step of the cleaned machine is one step of `M`, the mark
tapes recording the cell each head leaves. -/
lemma sim_step_clean (M : MultiTapeTM k Bool S) (q₁ q : S) (V : List Bool) (t : ℕ)
    (hlive : (M.runFrom (Cfg.init q V) t).state ≠ none) :
    (cleanTM M q₁).step (simCfg M q V t) = simCfg M q V (t + 1) := by
  obtain ⟨q', hq'⟩ := Option.ne_none_iff_exists'.mp hlive
  have e0 : simCfg M q V t = ccfg (some (.sim q')) (M.runFrom (Cfg.init q V) t).inputPos
      (M.runFrom (Cfg.init q V) t).workTapes (M.runFrom (Cfg.init q V) t).workTapePos
      (fun i => markSet (visB M q V t i)) (M.runFrom (Cfg.init q V) t).workTapePos
      (M.runFrom (Cfg.init q V) t).output := by
    simp only [simCfg, simSt, hq']
  rw [e0, step_sim M q₁ _ q' hq']
  simp only [simCfg, MultiTapeTM.runFrom_succ_eq_step', visB_succ, wr_markSet]



/-- The visited cells of a tape form an interval around the origin.

**Proof sketch.** The visited set is finite and contains `0`. Take `a` its minimum and `b` its
maximum. By `abs_pos_lt_card_visited`'s intermediate-value argument, every integer between `0`
and a visited cell is visited, so the set is exactly `[a, b]`. -/
lemma visited_interval (M : MultiTapeTM k Bool S) (q : S) (V : List Bool) (T : ℕ) (j : Fin k) :
    ∃ a b : ℤ, a ≤ 0 ∧ 0 ≤ b ∧ a ∈ M.visitedByTapeHead (Cfg.init q V) T j ∧
      b ∈ M.visitedByTapeHead (Cfg.init q V) T j ∧
      ∀ z, z ∈ M.visitedByTapeHead (Cfg.init q V) T j ↔ a ≤ z ∧ z ≤ b := by
  set U := M.visitedByTapeHead (Cfg.init q V) T j with hU
  have h0 : (0 : ℤ) ∈ U := by
    simp only [hU, MultiTapeTM.visitedByTapeHead, Finset.mem_image, Finset.mem_range]
    exact ⟨0, by omega, by simp [Cfg.init]⟩
  have hne : U.Nonempty := ⟨0, h0⟩
  refine ⟨U.min' hne, U.max' hne, U.min'_le 0 h0, U.le_max' 0 h0, U.min'_mem hne,
    U.max'_mem hne, fun z => ⟨fun hz => ⟨U.min'_le z hz, U.le_max' z hz⟩, fun ⟨h1, h2⟩ => ?_⟩⟩
  set p : ℕ → ℤ := fun t => (M.runFrom (Cfg.init q V) t).workTapePos j with hp
  have hp0 : p 0 = 0 := by simp [hp, Cfg.init]
  have hstep : ∀ t, |p (t + 1) - p t| ≤ 1 := by
    intro t; simp only [hp, MultiTapeTM.runFrom_succ_eq_step']
    exact M.workTapePos_step_le _ j
  have hmem : ∀ y ∈ U, ∃ t ≤ T, p t = y := by
    intro y hy
    simp only [hU, MultiTapeTM.visitedByTapeHead, Finset.mem_image, Finset.mem_range] at hy
    obtain ⟨t, ht, h⟩ := hy
    exact ⟨t, by omega, h⟩
  rcases le_total 0 z with hz | hz
  · obtain ⟨t, ht, hpt⟩ := hmem _ (U.max'_mem hne)
    obtain ⟨t', ht', hpt'⟩ := MultiTapeTM.ConfigCount.exists_eq_of_between p hp0 hstep t z (Or.inl ⟨hz, by rw [hpt]; exact h2⟩)
    simp only [hU, MultiTapeTM.visitedByTapeHead, Finset.mem_image, Finset.mem_range]
    exact ⟨t', by omega, hpt'⟩
  · obtain ⟨t, ht, hpt⟩ := hmem _ (U.min'_mem hne)
    obtain ⟨t', ht', hpt'⟩ := MultiTapeTM.ConfigCount.exists_eq_of_between p hp0 hstep t z (Or.inr ⟨by rw [hpt]; exact h1, hz⟩)
    simp only [hU, MultiTapeTM.visitedByTapeHead, Finset.mem_image, Finset.mem_range]
    exact ⟨t', by omega, hpt'⟩

/-- The state at cleanup stage `i`. -/
def stSt (i : ℕ) : Option (CleanSt S k) := if h : i < k then some (.cl ⟨i, h⟩ .mark) else none

/-- The configuration after cleaning tapes `0, …, i - 1`. -/
def stg {x : List Bool} (i : ℕ) (ip : Fin (x.length + 2)) (Dt Mt : Fin k → ℤ → Option Bool)
    (Dp : Fin k → ℤ) (out : List Bool) : Cfg (k + k) Bool (CleanSt S k) x :=
  ccfg (stSt i) ip (fun j => if j.val < i then (fun _ => none) else Dt j)
    (fun j => if j.val < i then 0 else Dp j) (fun j => if j.val < i then (fun _ => none) else Mt j)
    (fun j => if j.val < i then 0 else Dp j) out

/-- **The cleanup of all tapes**, tape after tape.

**Proof sketch.** Induction on the number `n` of tapes left. Tape `i` is cleaned by the walk
right (`goR_run`), the erasing walk left (`erase_run`) and the walk back (`back_run`), whose
hypotheses come from `htape`. The cleaned tape is blank with heads at `0`, which is the stage
configuration `stg (i + 1)`. -/
lemma stages_run (M : MultiTapeTM k Bool S) (q₁ : S) {x : List Bool} (ip : Fin (x.length + 2))
    (Dt Mt : Fin k → ℤ → Option Bool) (Dp : Fin k → ℤ) (out : List Bool) (B : ℤ)
    (htape : ∀ j : Fin k, ∃ a b : ℤ, a ≤ 0 ∧ 0 ≤ b ∧ -B ≤ a - 1 ∧ b + 1 ≤ B ∧
      a ≤ Dp j ∧ Dp j ≤ b ∧
      wr (if Mt j (Dp j) = some true then none else some (some false)) (Mt j) (Dp j) =
        markI a b ∧ ∀ z, Dt j z ≠ none → a ≤ z ∧ z ≤ b)
    (hB0 : 0 ≤ B) :
    ∀ n i, i + n = k →
      ∃ T, (∀ t ≤ T, PB B ((cleanTM M q₁).runFrom (stg i ip Dt Mt Dp out) t)) ∧
        (cleanTM M q₁).runFrom (stg i ip Dt Mt Dp out) T = stg k ip Dt Mt Dp out := by
  have hBs : ∀ i, ∀ j : Fin k, |(fun j : Fin k => if j.val < i then (0 : ℤ) else Dp j) j| ≤ B := by
    intro i j
    simp only
    split_ifs
    · simpa using hB0
    · obtain ⟨a, b, -, -, h1, h2, h3, h4, -⟩ := htape j
      rw [abs_le]; constructor <;> omega
  intro n
  induction n with
  | zero =>
    intro i hi
    rw [show i = k by omega]
    refine ⟨0, fun t ht => ?_, rfl⟩
    obtain rfl : t = 0 := by omega
    exact PB_ccfg _ _ _ _ _ _ _ _ (hBs k) (hBs k)
  | succ n ih =>
    intro i hi
    have hik : i < k := by omega
    obtain ⟨a, b, ha, hb, haB, hbB, hh1, hh2, hmk, hsupp⟩ := htape ⟨i, hik⟩
    obtain ⟨T₁, hb₁, hr₁⟩ := clean_tape M q₁ ⟨i, hik⟩ ip out B a b
      (fun j => if j.val < i then (fun _ => none) else Dt j)
      (fun j => if j.val < i then (fun _ => none) else Mt j)
      (fun j => if j.val < i then 0 else Dp j) ha hb haB hbB
      (by simp only [lt_self_iff_false, ↓reduceIte]; exact ⟨hh1, hh2⟩)
      (by simp only [lt_self_iff_false, ↓reduceIte]; exact hmk)
      (by simp only [lt_self_iff_false, ↓reduceIte]; exact hsupp) (hBs i)
    have hstg : (ccfg (clNext ⟨i, hik⟩) ip
        (Function.update (fun j : Fin k => if j.val < i then (fun _ => none) else Dt j) ⟨i, hik⟩
          fun _ => none)
        (Function.update (fun j : Fin k => if j.val < i then 0 else Dp j) ⟨i, hik⟩ 0)
        (Function.update (fun j : Fin k => if j.val < i then (fun _ => none) else Mt j) ⟨i, hik⟩
          fun _ => none)
        (Function.update (fun j : Fin k => if j.val < i then 0 else Dp j) ⟨i, hik⟩ 0) out :
          Cfg (k + k) Bool (CleanSt S k) x) =
        stg (i + 1) ip Dt Mt Dp out := by
      have e : ∀ {α : Type} (f : Fin k → α) (v : α),
          Function.update (fun j : Fin k => if j.val < i then v else f j) ⟨i, hik⟩ v =
            fun j => if j.val < i + 1 then v else f j := by
        intro α f v
        funext j
        by_cases hj : j = ⟨i, hik⟩
        · subst hj; simp
        · rw [Function.update_of_ne hj]
          have : j.val ≠ i := fun h => hj (Fin.ext h)
          split_ifs <;> first | rfl | omega
      simp only [stg, e]
      congr 1
    obtain ⟨T₂, hb₂, hr₂⟩ := ih (i + 1) (by omega)
    have hstgi : (stg i ip Dt Mt Dp out : Cfg (k + k) Bool (CleanSt S k) x) =
        ccfg (some (.cl ⟨i, hik⟩ .mark))
          ip (fun j => if j.val < i then (fun _ => none) else Dt j)
          (fun j => if j.val < i then 0 else Dp j) (fun j => if j.val < i then (fun _ => none) else Mt j)
          (fun j => if j.val < i then 0 else Dp j) out := by simp [stg, stSt, hik]
    rw [hstgi]
    refine ⟨T₁ + T₂, ?_, ?_⟩
    · apply Complexity.LogProg.runFrom_forall_append (Q := PB B) hb₁
      rw [hr₁, hstg]; exact hb₂
    · rw [MultiTapeTM.runFrom_add, hr₁, hstg, hr₂]

/-- **The cleaned machine** started in `init q` on `V`: if `M` started in `q` has halted by
time `T`, visiting at most `s` cells of each tape, then the cleaned machine halts with `M`'s
output, blank work tapes and heads at the origin, every head staying in `[-s, s]`.

**Proof sketch.** One step writes the origin marks; `sim_step_clean` simulates `M` up to its
first halting time `T₀ ≤ T`, the mark tapes recording the cells visited. The visited cells
of each tape form an interval `[a, b] ∋ 0` (`visited_interval`) that contains every
nonblank cell (`Turing.MultiTapeTM.mem_visited_of_ne_none`), and every position in it has
absolute value below the number of visited cells, at most `s`
(`Turing.MultiTapeTM.abs_pos_lt_card_visited`); `stages_run` then cleans the tapes. -/
theorem cleanTM_run (M : MultiTapeTM k Bool S) (q₁ q : S) (V : List Bool) (T : ℕ)
    (hT : (M.runFrom (Cfg.init q V) T).state = none) (s : ℕ)
    (hs : ∀ i, (M.visitedByTapeHead (Cfg.init q V) T i).card ≤ s) :
    ∃ T', ((cleanTM M q₁).runFrom (Cfg.init (.init q) V) T').state = none ∧
      ((cleanTM M q₁).runFrom (Cfg.init (.init q) V) T').output =
        (M.runFrom (Cfg.init q V) T).output ∧
      ((cleanTM M q₁).runFrom (Cfg.init (.init q) V) T').workTapes = (fun _ _ => none) ∧
      ((cleanTM M q₁).runFrom (Cfg.init (.init q) V) T').workTapePos = (fun _ => 0) ∧
      ∀ t ≤ T', ∀ j, |((cleanTM M q₁).runFrom (Cfg.init (.init q) V) t).workTapePos j| ≤ s := by
  classical
  -- the machine `M` with start state `q`, to use the results stated for `initCfg`
  set M' : MultiTapeTM k Bool S := { M with q₀ := q } with hM'
  have hinit : M'.initCfg V = Cfg.init q V := rfl
  have hrun : ∀ t, M'.runFrom (Cfg.init q V) t = M.runFrom (Cfg.init q V) t := fun _ => rfl
  have hex : ∃ t, (M.runFrom (Cfg.init q V) t).state = none := ⟨T, hT⟩
  set T0 := Nat.find hex with hT0def
  have hT0 : (M.runFrom (Cfg.init q V) T0).state = none := Nat.find_spec hex
  have hT0le : T0 ≤ T := Nat.find_min' hex hT
  have hlive : ∀ t < T0, (M.runFrom (Cfg.init q V) t).state ≠ none :=
    fun t ht => Nat.find_min hex ht
  have hfinT : M.runFrom (Cfg.init q V) T = M.runFrom (Cfg.init q V) T0 := by
    rw [show T = T0 + (T - T0) by omega, MultiTapeTM.runFrom_add,
      MultiTapeTM.runFrom_of_halt _ hT0]
  -- positions of `M` stay in `[-(s-1), s-1]`
  have hvis : ∀ j (z : ℤ), z ∈ M.visitedByTapeHead (Cfg.init q V) T0 j → |z| + 1 ≤ s := by
    intro j z hz
    have h1 := MultiTapeTM.abs_pos_lt_card_visited M' V T0 j (z := z) hz
    have h2 := Finset.card_le_card (MultiTapeTM.visitedByTapeHead_mono M (Cfg.init q V) hT0le j)
    have h3 := hs j
    change |z| < ((M.visitedByTapeHead (Cfg.init q V) T0 j).card : ℤ) at h1
    omega
  -- the simulation phase
  have hsim : ∀ t ≤ T0, (cleanTM M q₁).runFrom (simCfg M q V 0) t = simCfg M q V t := by
    intro t
    induction t with
    | zero => intro _; rfl
    | succ t ih =>
      intro ht
      rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega), sim_step_clean M q₁ q V t
        (hlive t (by omega))]
  have hstart : (cleanTM M q₁).runFrom (Cfg.init (.init q) V) 1 = simCfg M q V 0 :=
    init_step M q₁ q V
  -- the interval data of every tape at the halt
  set c := M.runFrom (Cfg.init q V) T0 with hc
  have htape : ∀ j : Fin k, ∃ a b : ℤ, a ≤ 0 ∧ 0 ≤ b ∧ -(s : ℤ) ≤ a - 1 ∧ b + 1 ≤ s ∧
      a ≤ c.workTapePos j ∧ c.workTapePos j ≤ b ∧
      wr (if markSet (visB M q V T0 j) (c.workTapePos j) = some true then none
        else some (some false)) (markSet (visB M q V T0 j)) (c.workTapePos j) = markI a b ∧
      ∀ z, c.workTapes j z ≠ none → a ≤ z ∧ z ≤ b := by
    intro j
    obtain ⟨a, b, ha, hb, haU, hbU, hU⟩ := visited_interval M q V T0 j
    have hva := hvis j a haU
    have hvb := hvis j b hbU
    have hpos : c.workTapePos j ∈ M.visitedByTapeHead (Cfg.init q V) T0 j := by
      simp only [MultiTapeTM.visitedByTapeHead, Finset.mem_image, Finset.mem_range]
      exact ⟨T0, by omega, rfl⟩
    have hUeq : insert (c.workTapePos j) (visB M q V T0 j) =
        M.visitedByTapeHead (Cfg.init q V) T0 j := by
      simp only [visB, MultiTapeTM.visitedByTapeHead, Finset.range_add_one, Finset.image_insert, hc]
    have hna := neg_abs_le a
    have hnb := le_abs_self b
    refine ⟨a, b, ha, hb, by omega, by omega,
      ((hU _).mp hpos).1, ((hU _).mp hpos).2, ?_, ?_⟩
    · rw [wr_markSet, hUeq]
      funext z
      simp only [markSet, markI, hU]
    · intro z hz
      have := MultiTapeTM.mem_visited_of_ne_none M' V T0 j z hz
      exact (hU z).mp this
  have hstg0 : simCfg M q V T0 = stg 0 c.inputPos c.workTapes
      (fun j => markSet (visB M q V T0 j)) c.workTapePos c.output := by
    simp only [simCfg, stg, stSt, simSt, ← hc, hT0, Nat.not_lt_zero, ↓reduceIte]
    try rfl
  obtain ⟨T₂, hb₂, hr₂⟩ := stages_run M q₁ c.inputPos c.workTapes
    (fun j => markSet (visB M q V T0 j)) c.workTapePos c.output s htape (by omega) k 0 (by omega)
  have hfinal : (stg k c.inputPos c.workTapes (fun j => markSet (visB M q V T0 j)) c.workTapePos
      c.output : Cfg (k + k) Bool (CleanSt S k) V) = ccfg none c.inputPos (fun _ _ => none)
        (fun _ => 0) (fun _ _ => none) (fun _ => 0) c.output := by
    simp only [stg, stSt, lt_self_iff_false, ↓reduceDIte, Fin.is_lt, ↓reduceIte]
  have hrun_total : (cleanTM M q₁).runFrom (Cfg.init (.init q) V) (1 + (T0 + T₂)) =
      ccfg none c.inputPos (fun _ _ => none) (fun _ => 0) (fun _ _ => none) (fun _ => 0)
        c.output := by
    rw [MultiTapeTM.runFrom_add, hstart, MultiTapeTM.runFrom_add, hsim T0 le_rfl, hstg0, hr₂,
      hfinal]
  refine ⟨1 + (T0 + T₂), ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrun_total]; rfl
  · rw [hrun_total, hfinT]; rfl
  · rw [hrun_total]; funext j z
    refine Fin.addCases (fun r => ?_) (fun r => ?_) j <;>
      simp only [ccfg, Fin.append_left, Fin.append_right]
  · rw [hrun_total]; funext j
    refine Fin.addCases (fun r => ?_) (fun r => ?_) j <;>
      simp only [ccfg, Fin.append_left, Fin.append_right]
  · apply Complexity.LogProg.runFrom_forall_append (Q := PB (s : ℤ))
    · intro t ht
      rcases Nat.lt_or_ge t 1 with h | h
      · obtain rfl : t = 0 := by omega
        intro j; simp [Cfg.init]
      · obtain rfl : t = 1 := by omega
        rw [hstart]
        exact PB_ccfg _ _ _ _ _ _ _ _ (fun j => by simp [Cfg.init]) (fun j => by simp [Cfg.init])
    rw [hstart]
    apply Complexity.LogProg.runFrom_forall_append (Q := PB (s : ℤ))
    · intro t ht
      rw [hsim t ht]
      have hb : ∀ j, |(M.runFrom (Cfg.init q V) t).workTapePos j| ≤ s := by
        intro j
        have : (M.runFrom (Cfg.init q V) t).workTapePos j ∈
            M.visitedByTapeHead (Cfg.init q V) T0 j := by
          simp only [MultiTapeTM.visitedByTapeHead, Finset.mem_image, Finset.mem_range]
          exact ⟨t, by omega, rfl⟩
        have := hvis j _ this
        omega
      exact PB_ccfg _ _ _ _ _ _ _ _ hb hb
    rw [hsim T0 le_rfl, hstg0]
    exact hb₂

/-- A clean run within a head range is a clean run within any larger range. -/
lemma CleanRun.mono {kD : ℕ} {SD : Type} {D : MultiTapeTM kD Bool SD} {q : SD}
    {V : List Bool} {b : Bool} {B B' : ℕ} (h : CleanRun D q V b B) (hB : B ≤ B') :
    CleanRun D q V b B' := by
  obtain ⟨T, h1, h2, h3, h4, h5⟩ := h
  exact ⟨T, h1, h2, h3, h4, fun t ht i => (h5 t ht i).trans (by exact_mod_cast hB)⟩

end Complexity.LogProg

```


## ===== TCSlib/Complexity/SpaceComplexity/Machines/Bank.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.Clean

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A bank of clean deciders

The compiled machine of a register-tape program calls its deciders through one machine
with several start states (`Complexity.LogProg.compileTM` takes a single decider block).
This file builds that machine from finitely many space-bounded deciders: each decider is
padded to the largest number of work tapes, the padded machines are run side by side in one
state space (the start state selects the decider), and the whole is cleaned
(`Complexity.LogProg.cleanTM`).

## Main definitions

* `Complexity.LogProg.padTM` — a machine with extra, unused work tapes.
* `Complexity.LogProg.bankTM`, `Complexity.LogProg.bankStart` — the bank and its start states.

## Main results

* `Complexity.LogProg.bank_cleanRun` — started in `bankStart j` on `V`, the bank answers
  whether `V` belongs to decider `j`'s language, cleanly, with heads in
  `[-max (s j |V|) 1, max (s j |V|) 1]`, where decider `j` runs in space `s j`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.)
-/

namespace Complexity.LogProg

open Turing

/-! ## Padding with unused tapes -/

section Pad

variable {k K : ℕ} {S : Type}

/-- The machine `M` with `K ≥ k` work tapes, the extra ones unused. -/
def padTM (M : MultiTapeTM k Bool S) (K : ℕ) : MultiTapeTM K Bool S where
  q₀ := M.q₀
  tr q a w :=
    let act := M.tr q a (fun i => if h : i.val < K then w ⟨i.val, h⟩ else none)
    ⟨act.inputTape, fun i => if h : i.val < k then act.workTapes ⟨i.val, h⟩ else (none, 0),
      act.output, act.state⟩

/-- The padded configuration. -/
def padCfg {x : List Bool} (K : ℕ) (c : Cfg k Bool S x) : Cfg K Bool S x :=
  ⟨c.state, c.inputPos, fun i z => if h : i.val < k then c.workTapes ⟨i.val, h⟩ z else none,
    fun i => if h : i.val < k then c.workTapePos ⟨i.val, h⟩ else 0, c.output⟩

/-- One step of the padded machine on a padded configuration is the padding of one step of the
original machine.

**Proof sketch.** Unfold one step on both sides: the padded transition reads the original tapes'
symbols (the padding tapes are never read), applies the original action to them, and leaves the
padding tapes and heads unchanged. Compare componentwise, splitting tape indices into original
and padding ones. -/
lemma padTM_step {x : List Bool} (M : MultiTapeTM k Bool S) (hk : k ≤ K) (c : Cfg k Bool S x) :
    (padTM M K).step (padCfg K c) = padCfg K (M.step c) := by
  unfold MultiTapeTM.step
  simp only [padCfg]
  cases hs : c.state with
  | none => simp [hs]
  | some q =>
    simp only
    have hw : (fun i : Fin k => if h : i.val < K then
        (padCfg K c : Cfg K Bool S x).workTapeSymbols ⟨i.val, h⟩ else none) =
          c.workTapeSymbols := by
      funext i
      simp [padCfg, Cfg.workTapeSymbols, show i.val < K by omega]
    have hin : (padCfg K c : Cfg K Bool S x).inputSymbol = c.inputSymbol := rfl
    change ((padTM M K).tr q (padCfg K c).inputSymbol (padCfg K c).workTapeSymbols).apply
      (padCfg K c) = padCfg K ((M.tr q c.inputSymbol c.workTapeSymbols).apply c)
    simp only [padTM, hin, hw]
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    · funext i z
      simp only [Action.apply, padCfg]
      by_cases h : i.val < k
      · simp only [h, ↓reduceDIte]
      · simp [h]
    · funext i
      simp only [Action.apply, padCfg]
      by_cases h : i.val < k <;> simp [h]

/-- Runs of the padded machine on padded configurations are the paddings of the original runs. -/
lemma padTM_runFrom {x : List Bool} (M : MultiTapeTM k Bool S) (hk : k ≤ K) (c : Cfg k Bool S x)
    (n : ℕ) : (padTM M K).runFrom (padCfg K c) n = padCfg K (M.runFrom c n) :=
  MultiTapeTM.runFrom_comm_of_step (padCfg K) (padTM_step M hk) c n

end Pad

/-! ## Machines side by side -/

section Sigma

variable {d K : ℕ} {S : Fin d → Type}

/-- The machines `Ms j` in one state space; the dummy state `none` halts. -/
def sigmaTM (Ms : (j : Fin d) → MultiTapeTM K Bool (S j)) :
    MultiTapeTM K Bool (Option (Σ j, S j)) where
  q₀ := none
  tr
    | none, _, _ => ⟨0, fun _ => (none, 0), none, none⟩
    | some ⟨j, q⟩, a, w =>
      let act := (Ms j).tr q a w
      ⟨act.inputTape, act.workTapes, act.output, act.state.map fun q' => some ⟨j, q'⟩⟩

/-- The configuration of machine `j` inside the side-by-side machine. -/
def sigCfg {x : List Bool} (j : Fin d) (c : Cfg K Bool (S j) x) :
    Cfg K Bool (Option (Σ j, S j)) x :=
  ⟨c.state.map fun q => some ⟨j, q⟩, c.inputPos, c.workTapes, c.workTapePos, c.output⟩

/-- One step of the disjoint union of machines on a configuration of component `j` is that
component's step. -/
lemma sigmaTM_step {x : List Bool} (Ms : (j : Fin d) → MultiTapeTM K Bool (S j)) (j : Fin d)
    (c : Cfg K Bool (S j) x) : (sigmaTM Ms).step (sigCfg j c) = sigCfg j ((Ms j).step c) := by
  unfold MultiTapeTM.step
  cases hs : c.state with
  | none => simp [sigCfg, hs]
  | some q =>
    simp only [sigCfg, hs, Option.map_some]
    rfl

/-- Runs of the disjoint union of machines on configurations of component `j` are that
component's runs. -/
lemma sigmaTM_runFrom {x : List Bool} (Ms : (j : Fin d) → MultiTapeTM K Bool (S j)) (j : Fin d)
    (c : Cfg K Bool (S j) x) (n : ℕ) :
    (sigmaTM Ms).runFrom (sigCfg j c) n = sigCfg j ((Ms j).runFrom c n) :=
  MultiTapeTM.runFrom_comm_of_step (sigCfg j) (sigmaTM_step Ms j) c n

end Sigma

/-! ## The bank -/

section Bank

variable {d : ℕ} (Ms : Fin d → FinTM Bool)

/-- The common number of work tapes. -/
def bankK : ℕ := Finset.univ.sup fun j => (Ms j).k

/-- Every machine of the bank has at most `bankK Ms` work tapes. -/
lemma le_bankK (j : Fin d) : (Ms j).k ≤ bankK Ms :=
  Finset.le_sup (f := fun j => (Ms j).k) (Finset.mem_univ j)

/-- The raw state type of the bank. -/
abbrev BankS : Type := Option (Σ j, (Ms j).State)

/-- **The bank of deciders**: the deciders padded to `bankK` tapes, side by side, cleaned. -/
def bankTM : MultiTapeTM (bankK Ms + bankK Ms) Bool (CleanSt (BankS Ms) (bankK Ms)) :=
  cleanTM (sigmaTM fun j => padTM (Ms j).tm (bankK Ms)) none

/-- The start state of decider `j` in the bank. -/
def bankStart (j : Fin d) : CleanSt (BankS Ms) (bankK Ms) := .init (some ⟨j, (Ms j).tm.q₀⟩)

/-- **The bank answers cleanly.** If decider `j` decides `A j` in space `s j`, then the bank
started in `bankStart j` on any `V` halts with output `[V ∈ A j]`, blank work tapes and heads
at the origin, all heads within `[-B, B]` for `B = max (s j |V|) 1`.

**Proof sketch.** Padding (`padTM_runFrom`) and the side-by-side union (`sigmaTM_runFrom`)
run decider `j` unchanged; its tapes visit at most `s j |V|` cells each and the padding
tapes only the origin; `cleanTM_run` does the rest. -/
theorem bank_cleanRun (A : Fin d → Language Bool) (s : Fin d → ℕ → ℕ)
    (hMs : ∀ j, (Ms j).DecidesInSpace (A j) (s j)) (j : Fin d) (V : List Bool) :
    CleanRun (bankTM Ms) (bankStart Ms j) V
      (MultiTapeTM.indicator (A j : Set (List Bool)) V) (max (s j V.length) 1) := by
  obtain ⟨T, hT, hsp⟩ := hMs j V
  rw [FinTM.computesInTime_iff] at hT
  obtain ⟨hhalt, hout⟩ := hT
  set K := bankK Ms
  have hk : (Ms j).k ≤ K := le_bankK Ms j
  -- the side-by-side padded run
  have hrun : ∀ t, (sigmaTM fun j => padTM (Ms j).tm K).runFrom
      (Cfg.init (some ⟨j, (Ms j).tm.q₀⟩) V) t =
      sigCfg (S := fun j => (Ms j).State) j (padCfg K ((Ms j).tm.runFrom ((Ms j).tm.initCfg V) t)) := by
    intro t
    have e : (Cfg.init (some ⟨j, (Ms j).tm.q₀⟩) V : Cfg K Bool (BankS Ms) V) =
        sigCfg (S := fun j => (Ms j).State) j (padCfg K ((Ms j).tm.initCfg V)) := by
      refine Cfg.ext rfl rfl ?_ ?_ rfl
      · funext i z; simp [sigCfg, padCfg, Cfg.init]
      · funext i; simp [sigCfg, padCfg, Cfg.init]
    rw [e, sigmaTM_runFrom, padTM_runFrom _ hk]
  have hhalt' : ((sigmaTM fun j => padTM (Ms j).tm K).runFrom
      (Cfg.init (some ⟨j, (Ms j).tm.q₀⟩) V) T).state = none := by
    rw [hrun]; simp only [sigCfg, padCfg]; rw [hhalt]; rfl
  -- visited cells per tape
  have hvis : ∀ i : Fin K, ((sigmaTM fun j => padTM (Ms j).tm K).visitedByTapeHead
      (Cfg.init (some ⟨j, (Ms j).tm.q₀⟩) V) T i).card ≤ max (s j V.length) 1 := by
    intro i
    by_cases hi : i.val < (Ms j).k
    · have hsub : (sigmaTM fun j => padTM (Ms j).tm K).visitedByTapeHead
          (Cfg.init (some ⟨j, (Ms j).tm.q₀⟩) V) T i =
          (Ms j).tm.visitedByTapeHead ((Ms j).tm.initCfg V) T ⟨i.val, hi⟩ := by
        simp only [MultiTapeTM.visitedByTapeHead, hrun, sigCfg, padCfg, hi, ↓reduceDIte]
      rw [hsub]
      exact ((Ms j).tm.spaceUsedByTape_le_spaceUsed _ T _).trans (hsp.trans (le_max_left _ _))
    · have hsub : (sigmaTM fun j => padTM (Ms j).tm K).visitedByTapeHead
          (Cfg.init (some ⟨j, (Ms j).tm.q₀⟩) V) T i ⊆ {0} := by
        intro z hz
        simp only [MultiTapeTM.visitedByTapeHead, hrun, sigCfg, padCfg, hi, ↓reduceDIte,
          Finset.mem_image, Finset.mem_range] at hz
        obtain ⟨_, _, rfl⟩ := hz
        simp
      exact (Finset.card_le_card hsub).trans (by simp)
  obtain ⟨T', h1, h2, h3, h4, h5⟩ := cleanTM_run (sigmaTM fun j => padTM (Ms j).tm K) none
    (some ⟨j, (Ms j).tm.q₀⟩) V T hhalt' _ hvis
  unfold CleanRun bankStart bankTM
  refine ⟨T', h1, ?_, h3, h4, fun t ht i => by exact_mod_cast h5 t ht i⟩
  rw [h2, hrun]
  simp only [sigCfg, padCfg]
  exact hout

end Bank

end Complexity.LogProg

```


## ===== TCSlib/Complexity/SpaceComplexity/Machines/Bin.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Ring

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Binary counters as words

Register-tape programs keep counters in little-endian binary, as the words `Nat.bits n`
(least significant bit first, no redundant zeros). This file collects the word-level facts the
counter machines need: the value of a word, injectivity of `Nat.bits`, the carry rule of
the increment (`Complexity.LogProg.bits_succ`), and length bounds.

## Main definitions

* `Complexity.LogProg.bitsVal` — the value of a little-endian word.
* `Complexity.LogProg.incW` — the increment of a little-endian word (carry propagation).

## Main results

* `Complexity.LogProg.bitsVal_bits`, `Complexity.LogProg.bits_injective`.
* `Complexity.LogProg.bits_succ` — `Nat.bits (n + 1) = incW (Nat.bits n)`.
* `Complexity.LogProg.length_bits_le` — `|Nat.bits n| ≤ m` when `n < 2^m`;
  `Complexity.LogProg.length_bits_mono` — `|Nat.bits n|` is monotone in `n`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1: counters in logarithmic space.)
-/

namespace Complexity.LogProg

/-- The value of a little-endian binary word. (Duplicates `BoolCircuit.bitsVal` of
`TCSlib.Complexity.CircuitComplexity.Adder`; to be unified.) -/
def bitsVal : List Bool → ℕ
  | [] => 0
  | b :: w => b.toNat + 2 * bitsVal w

/-- The increment of a little-endian binary word: flip the leading `1`s to `0` and the
first `0` (or the end) to `1`. -/
def incW : List Bool → List Bool
  | [] => [true]
  | false :: w => true :: w
  | true :: w => false :: incW w

/-- `Nat.bits` of an even and an odd number. -/
lemma bits_two_mul_add (n : ℕ) (b : Bool) (h : n = 0 → b = true) :
    Nat.bits (2 * n + b.toNat) = b :: Nat.bits n := by
  cases b with
  | false =>
    have hn : n ≠ 0 := fun h0 => by simpa using h h0
    simpa using Nat.bit0_bits n hn
  | true => simp

/-- The value of `Nat.bits n` is `n`. -/
lemma bitsVal_bits (n : ℕ) : bitsVal (Nat.bits n) = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [bitsVal, Nat.zero_bits]
    · have hdecomp : n = 2 * (n / 2) + (decide (n % 2 = 1)).toNat := by
        rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h] <;> omega
      have hb : n / 2 = 0 → decide (n % 2 = 1) = true := by
        intro h0; simp; omega
      rw [hdecomp, bits_two_mul_add _ _ hb]
      simp only [bitsVal]
      rw [ih (n / 2) (by omega)]
      rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]; omega

/-- `Nat.bits` is injective. -/
lemma bits_injective : Function.Injective Nat.bits := fun a b h => by
  rw [← bitsVal_bits a, ← bitsVal_bits b, h]

/-- **The carry rule**: the binary word of `n + 1` is the increment of that of `n`. -/
lemma bits_succ (n : ℕ) : Nat.bits (n + 1) = incW (Nat.bits n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [Nat.zero_bits, Nat.one_bits, incW]
    · rcases Nat.mod_two_eq_zero_or_one n with h | h
      · -- `n = 2m`, `m ≠ 0`
        obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
        have hm : m ≠ 0 := by omega
        rw [Nat.bit0_bits m hm, show 2 * m + 1 = 2 * m + (true).toNat by rfl,
          bits_two_mul_add m true (fun _ => rfl)]
        rfl
      · -- `n = 2m + 1`
        obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
        rw [Nat.bit1_bits, show 2 * m + 1 + 1 = 2 * (m + 1) + (false).toNat by simp; ring,
          bits_two_mul_add (m + 1) false (by omega), ih m (by omega)]
        rfl

/-- The binary word of `n` has at most `m` letters when `n < 2^m`. -/
lemma length_bits_le {n m : ℕ} (h : n < 2 ^ m) : (Nat.bits n).length ≤ m := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr h

/-- Binary words of larger numbers are not shorter. -/
lemma length_bits_mono {a b : ℕ} (h : a ≤ b) : (Nat.bits a).length ≤ (Nat.bits b).length := by
  rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len]; exact Nat.size_le_size h

/-- The binary word of `n` has at most `⌊log₂ n⌋ + 1` letters. -/
lemma length_bits_le_log (n : ℕ) : (Nat.bits n).length ≤ Nat.log 2 n + 1 :=
  length_bits_le (Nat.lt_pow_succ_log_self (by norm_num) n)

/-- Every letter of `Nat.bits n` is followed by more letters or is a `1`: the word has no
trailing `0`. (The last letter is `true`.) -/
lemma bits_getLast (n : ℕ) (h : Nat.bits n ≠ []) : (Nat.bits n).getLast h = true := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [Nat.zero_bits] at h
    · have hdecomp : n = 2 * (n / 2) + (decide (n % 2 = 1)).toNat := by
        rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h] <;> omega
      have hb : n / 2 = 0 → decide (n % 2 = 1) = true := by
        intro h0; simp; omega
      have e := bits_two_mul_add (n / 2) _ hb
      rw [← hdecomp] at e
      simp only [e]
      by_cases h0 : Nat.bits (n / 2) = []
      · simp only [h0, List.getLast_singleton]
        have : n / 2 = 0 := by
          have := bitsVal_bits (n / 2); rw [h0] at this; simp [bitsVal] at this; omega
        exact hb this
      · rw [List.getLast_cons h0]
        exact ih (n / 2) (by omega) h0

end Complexity.LogProg

namespace Complexity.LogProg

/-- `n + 1 ≤ 2^(⌊log₂ n⌋ + 1)`. -/
lemma succ_le_two_pow_log (n : ℕ) : n + 1 ≤ 2 ^ (Nat.log 2 n + 1) :=
  Nat.lt_pow_succ_log_self (by norm_num) n

/-- **Logarithms of polynomials are logarithmic**: `⌊log₂ (A (n+1)^c + B)⌋ + 1` is at most a
constant times `⌊log₂ n⌋ + 1`.

**Proof sketch.** With `L = ⌊log₂ n⌋`, `n + 1 ≤ 2^{L+1}`, `A < 2^A` and `B < 2^B`, so
`A (n+1)^c + B < 2^{A + B + c(L+1) + 1}`; take `K = A + B + c + 2`. -/
lemma log_poly_bound (A c B : ℕ) :
    ∃ K, ∀ n, Nat.log 2 (A * (n + 1) ^ c + B) + 1 ≤ K * (Nat.log 2 n + 1) := by
  refine ⟨A + B + c + 2, fun n => ?_⟩
  set L := Nat.log 2 n
  have h1 : (n + 1) ^ c ≤ 2 ^ (c * (L + 1)) := by
    rw [pow_mul']; exact Nat.pow_le_pow_left (succ_le_two_pow_log n) c
  have hA : A < 2 ^ A := Nat.lt_two_pow_self
  have hB : B < 2 ^ B := Nat.lt_two_pow_self
  have hy : A * (n + 1) ^ c + B < 2 ^ (A + B + c * (L + 1) + 1) := by
    have e1 : A * (n + 1) ^ c ≤ 2 ^ A * 2 ^ (c * (L + 1)) :=
      Nat.mul_le_mul hA.le h1
    have e2 : 2 ^ A * 2 ^ (c * (L + 1)) ≤ 2 ^ (A + B + c * (L + 1)) := by
      rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have e3 : 2 ^ B ≤ 2 ^ (A + B + c * (L + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_succ]; omega
  have hlog : Nat.log 2 (A * (n + 1) ^ c + B) < A + B + c * (L + 1) + 1 := by
    rcases Nat.eq_zero_or_pos (A * (n + 1) ^ c + B) with h | h
    · rw [h]; simp
    · exact Nat.log_lt_of_lt_pow (by omega) hy
  have hle : A + B + 2 ≤ (A + B + 2) * (L + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have heq : (A + B + c + 2) * (L + 1) = (A + B + 2) * (L + 1) + c * (L + 1) := by ring
  rw [heq]
  generalize c * (L + 1) = P at hlog ⊢
  generalize (A + B + 2) * (L + 1) = Q at hle ⊢
  omega

end Complexity.LogProg

```


## ===== TCSlib/Complexity/SpaceComplexity/Machines/Lib.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.Compile
import TCSlib.Complexity.SpaceComplexity.Machines.Bin

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Program fragments: binary counters

Reusable pieces of register-tape programs (`Complexity.LogProg.RProg`), each specified by the
transitions it needs at a few states and proved once against the program semantics
`Complexity.LogProg.rstep`. The increment fragment adds one to the binary counter
(`Nat.bits n`, from cell `0`) on a register and returns its head to cell `0`.

## Main definitions

* `Complexity.LogProg.regCfg` — a program configuration with one register changed.
* `Complexity.LogProg.incCAct`, `Complexity.LogProg.incBAct` — the transitions of the
  increment fragment.

## Main results

* `Complexity.LogProg.inc_run` — the increment fragment turns `Nat.bits n` into
  `Nat.bits (n + 1)`, its head staying in `[-1, |Nat.bits (n + 1)|]`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.)
-/

namespace Complexity.LogProg

open Turing

variable {m d : ℕ} {Λ : Type} {x : List Bool}

/-- A non-call step of a program is a machine step. -/
lemma rstep_noncall (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (c : Cfg m Bool Λ x)
    (l : Λ) (hl : c.state = some l) (hc : P.call l = none) :
    rstep P oracle c = P.tm.step c := by
  simp [rstep, hl, hc]

/-- Running a program one step is `rstep`. -/
lemma rrun_one (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (c : Cfg m Bool Λ x) :
    rrun P oracle c 1 = rstep P oracle c := rfl

/-- Running a program zero steps leaves the configuration unchanged. -/
lemma rrun_zero (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (c : Cfg m Bool Λ x) :
    rrun P oracle c 0 = c := rfl

/-- Running `a + b` steps is running `a` steps, then `b` steps. -/
lemma rrun_add (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (c : Cfg m Bool Λ x)
    (a b : ℕ) : rrun P oracle c (a + b) = rrun P oracle (rrun P oracle c a) b := by
  simp only [rrun]
  rw [Nat.add_comm, Function.iterate_add_apply]

/-- A configuration with state `s` and register `r` holding tape `f` with its head at `p`,
everything else as in `c`. -/
def regCfg (c : Cfg m Bool Λ x) (s : Λ) (r : Fin m) (f : ℤ → Option Bool) (p : ℤ) :
    Cfg m Bool Λ x :=
  ⟨some s, c.inputPos, Function.update c.workTapes r f, Function.update c.workTapePos r p,
    c.output⟩

/-- The register view `regCfg c s …` is in state `s`. -/
@[simp] lemma regCfg_state (c : Cfg m Bool Λ x) (s : Λ) (r : Fin m) (f : ℤ → Option Bool)
    (p : ℤ) : (regCfg c s r f p).state = some s := rfl

/-- An action touching only register `r`. -/
def regAct (r : Fin m) (w : Option (Option Bool)) (mv : SignType) (s : Λ) : Action m Bool Λ :=
  ⟨0, fun r' => if r' = r then (w, mv) else (none, 0), none, some s⟩

/-- Applying a register action to a register view writes the register cell (if asked), moves
the register head by `mv`, and enters `s'`.

**Proof sketch.** Unfold the action's application on a register view: only register `r`'s cell
under the head is written and only its head moves. Compare the tape and head families pointwise
(`Function.update_apply`). -/
lemma apply_regAct (c : Cfg m Bool Λ x) (s s' : Λ) (r : Fin m) (f : ℤ → Option Bool) (p : ℤ)
    (w : Option (Option Bool)) (mv : SignType) :
    (regAct r w mv s').apply (regCfg c s r f p) =
      regCfg c s' r (match w with | none => f | some b => Function.update f p b) (p + mv) := by
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ (by simp [regAct, regCfg])
  · funext r' z
    simp only [regAct, regCfg, Action.apply]
    by_cases h : r' = r
    · subst h
      cases w with
      | none => simp
      | some b =>
        simp only [Function.update_self, ↓reduceIte]
        rw [Function.update_self]
    · simp [h]
  · funext r'
    simp only [regAct, regCfg, Action.apply]
    by_cases h : r' = r
    · subst h; simp
    · simp [h]

/-- The register view reads register `r` at its head position `p`. -/
lemma regCfg_read (c : Cfg m Bool Λ x) (s : Λ) (r : Fin m) (f : ℤ → Option Bool) (p : ℤ) :
    (regCfg c s r f p).workTapeSymbols r = f p := by
  simp [regCfg, Cfg.workTapeSymbols]

/-- Overwriting the cell right after a prefix. -/
lemma update_bufferTape_cons (pre w : List Bool) (b b' : Bool) :
    Function.update (FinTM.bufferTape (pre ++ b :: w)) (pre.length : ℤ) (some b') =
      FinTM.bufferTape (pre ++ b' :: w) := by
  funext z
  by_cases hz : z = (pre.length : ℤ)
  · subst hz; simp [FinTM.bufferTape]
  · rw [Function.update_of_ne hz]
    simp only [FinTM.bufferTape]
    split_ifs with h0
    · have hne : z.toNat ≠ pre.length := by omega
      rw [List.getElem?_append, List.getElem?_append]
      split_ifs with h3
      · rfl
      · obtain ⟨j, hj⟩ : ∃ j, z.toNat - pre.length = j + 1 :=
          ⟨z.toNat - pre.length - 1, by omega⟩
        rw [hj]; rfl
    · rfl

/-- Writing past the end of a stored word appends. -/
lemma update_bufferTape_end (w : List Bool) (b : Bool) :
    Function.update (FinTM.bufferTape w) (w.length : ℤ) (some b) = FinTM.bufferTape (w ++ [b]) :=
  (FinTM.bufferTape_append w b).symm

/-! ## The increment fragment -/

/-- The carry state of the increment: flip `1`s to `0` moving right; at a `0` or the end
write `1`, step back, and return. -/
def incCAct (r : Fin m) (cC cB : Λ) (rd : Option Bool) : Action m Bool Λ :=
  match rd with
  | some true => regAct r (some (some false)) 1 cC
  | _ => regAct r (some (some true)) (-1) cB

/-- The return state: walk left to the left blank, then step onto cell `0` and continue. -/
def incBAct (r : Fin m) (cB next : Λ) (rd : Option Bool) : Action m Bool Λ :=
  match rd with
  | some _ => regAct r none (-1) cB
  | none => regAct r none 1 next

section Inc

variable (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (r : Fin m) (cC cB next : Λ)
  (hC : ∀ a w, P.tm.tr cC a w = incCAct r cC cB (w r))
  (hB : ∀ a w, P.tm.tr cB a w = incBAct r cB next (w r))
  (hCc : P.call cC = none) (hBc : P.call cB = none)

include hC hCc in
/-- **The carry phase** of the increment: from `cC` at the start of the suffix `w`, the program
reaches `cB` with `w` replaced by its increment `incW w`, the head in range throughout.

**Proof sketch.** Induction on `w`. A `1` becomes `0` and the carry moves right; a `0`, or the
blank after the word, becomes `1` and ends the carry, entering `cB`. The head stays within
`[|pre|, |pre ++ w|]`. -/
lemma incC_run (c : Cfg m Bool Λ x) :
    ∀ (w pre : List Bool), ∃ (T : ℕ) (p : ℤ), -1 ≤ p ∧ p < (pre ++ incW w).length ∧
      rrun P oracle (regCfg c cC r (FinTM.bufferTape (pre ++ w)) pre.length) T =
        regCfg c cB r (FinTM.bufferTape (pre ++ incW w)) p ∧
      ∀ t < T, ∃ f q, rrun P oracle (regCfg c cC r (FinTM.bufferTape (pre ++ w)) pre.length) t =
        regCfg c cC r f q ∧ (pre.length : ℤ) ≤ q ∧ q ≤ (pre ++ w).length := by
  intro w
  induction w with
  | nil =>
    intro pre
    refine ⟨1, (pre.length : ℤ) - 1, by omega, by simp [incW]; omega, ?_, ?_⟩
    · rw [rrun_one]
      rw [rstep_noncall P oracle _ cC rfl hCc]
      unfold MultiTapeTM.step
      simp only [regCfg_state]
      rw [hC, regCfg_read]
      have hrd : FinTM.bufferTape (pre ++ []) (pre.length : ℤ) = none := by simp
      rw [hrd]
      simp only [incCAct]
      rw [apply_regAct]
      dsimp only
      simp only [List.append_nil, incW]
      rw [update_bufferTape_end]
      simp only [SignType.coe_neg_one, sub_eq_add_neg]
    · intro t ht
      obtain rfl : t = 0 := by omega
      exact ⟨_, _, rfl, le_rfl, by simp⟩
  | cons b w ih =>
    intro pre
    cases b with
    | false =>
      refine ⟨1, (pre.length : ℤ) - 1, by omega, by simp [incW]; omega, ?_, ?_⟩
      · rw [rrun_one]
        rw [rstep_noncall P oracle _ cC rfl hCc]
        unfold MultiTapeTM.step
        simp only [regCfg_state]
        rw [hC, regCfg_read]
        have hrd : FinTM.bufferTape (pre ++ false :: w) (pre.length : ℤ) = some false := by simp
        rw [hrd]
        simp only [incCAct]
        rw [apply_regAct]
        dsimp only
        simp only [incW]
        rw [update_bufferTape_cons]
        simp only [SignType.coe_neg_one, sub_eq_add_neg]
      · intro t ht
        obtain rfl : t = 0 := by omega
        exact ⟨_, _, rfl, le_rfl, by simp; omega⟩
    | true =>
      obtain ⟨T, p, hp1, hp2, hrun, hmid⟩ := ih (pre ++ [false])
      have hstep : rrun P oracle (regCfg c cC r (FinTM.bufferTape (pre ++ true :: w)) pre.length) 1 =
          regCfg c cC r (FinTM.bufferTape (pre ++ [false] ++ w)) (pre ++ [false]).length := by
        rw [rrun_one]
        rw [rstep_noncall P oracle _ cC rfl hCc]
        unfold MultiTapeTM.step
        simp only [regCfg_state]
        rw [hC, regCfg_read]
        have hrd : FinTM.bufferTape (pre ++ true :: w) (pre.length : ℤ) = some true := by simp
        rw [hrd]
        simp only [incCAct]
        rw [apply_regAct]
        dsimp only
        rw [update_bufferTape_cons]
        simp
      refine ⟨1 + T, p, hp1, by simpa [incW] using hp2, ?_, ?_⟩
      · rw [rrun_add, hstep, hrun]; simp [incW]
      · intro t ht
        rcases Nat.lt_or_ge t 1 with h | h
        · obtain rfl : t = 0 := by omega
          exact ⟨_, _, rfl, le_rfl, by simp; omega⟩
        · obtain ⟨t', rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
          rw [rrun_add, hstep]
          obtain ⟨f, q, hq, h1, h2⟩ := hmid t' (by omega)
          exact ⟨f, q, hq, by simp at h1 ⊢; omega, by simp at h2 ⊢; omega⟩

include hB hBc in
/-- **The return phase** of the increment: from `cB` at position `p < |w|`, the head walks left to
the left blank and back onto cell `0`, entering `next`.

**Proof sketch.** Induction on `n = p + 1`: on a letter the head moves left; at the left blank
`-1` it moves right onto cell `0` and the state becomes `next`. -/
lemma incB_run (c : Cfg m Bool Λ x) (w : List Bool) :
    ∀ (n : ℕ) (p : ℤ), p + 1 = n → p < w.length →
      rrun P oracle (regCfg c cB r (FinTM.bufferTape w) p) (n + 1) =
        regCfg c next r (FinTM.bufferTape w) 0 ∧
      ∀ t < n + 1, ∃ q, rrun P oracle (regCfg c cB r (FinTM.bufferTape w) p) t =
        regCfg c cB r (FinTM.bufferTape w) q ∧ -1 ≤ q ∧ q ≤ p := by
  intro n
  induction n with
  | zero =>
    intro p hp _
    refine ⟨?_, fun t ht => ?_⟩
    swap
    · obtain rfl : t = 0 := by omega
      exact ⟨p, rfl, by omega, le_rfl⟩
    rw [rrun_one]
    rw [rstep_noncall P oracle _ cB rfl hBc]
    unfold MultiTapeTM.step
    simp only [regCfg_state]
    rw [hB, regCfg_read]
    have hrd : FinTM.bufferTape w p = none := by rw [show p = -1 by omega]; simp
    rw [hrd]
    simp only [incBAct]
    rw [apply_regAct]
    try congr 1
  | succ n ih =>
    intro p hp hpw
    obtain ⟨j, hj⟩ : ∃ j : ℕ, p = j := ⟨p.toNat, by omega⟩
    have hjw : j < w.length := by omega
    have hstep : rrun P oracle (regCfg c cB r (FinTM.bufferTape w) p) 1 =
        regCfg c cB r (FinTM.bufferTape w) (p - 1) := by
      rw [rrun_one]
      rw [rstep_noncall P oracle _ cB rfl hBc]
      unfold MultiTapeTM.step
      simp only [regCfg_state]
      rw [hB, regCfg_read]
      have hrd : FinTM.bufferTape w p = some w[j] := by
        rw [hj]; simp [List.getElem?_eq_getElem hjw]
      rw [hrd]
      simp only [incBAct]
      rw [apply_regAct]
      try congr 1
    obtain ⟨ihr, ihm⟩ := ih (p - 1) (by omega) (by omega)
    refine ⟨?_, fun t ht => ?_⟩
    · rw [show n + 1 + 1 = 1 + (n + 1) by ring, rrun_add, hstep, ihr]
    · rcases Nat.lt_or_ge t 1 with h | h
      · obtain rfl : t = 0 := by omega
        exact ⟨p, rfl, by omega, le_rfl⟩
      · obtain ⟨t', rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
        rw [rrun_add, hstep]
        obtain ⟨q, hq, h1, h2⟩ := ihm t' (by omega)
        exact ⟨q, hq, h1, by omega⟩

include hC hB hCc hBc in
/-- **The increment fragment**: from `cC` with `Nat.bits n` on register `r` and its head on
cell `0`, the program reaches `next` with `Nat.bits (n + 1)` there and its head on cell `0`,
everything else unchanged; on the way it is only in the fragment's (non-call) states, with
the head of `r` in `[-1, |Nat.bits (n + 1)|]`.

**Proof sketch.** Run the carry phase (`incC_run`) from cell `0`, which turns `bits n` into
`incW (bits n) = bits (n + 1)` (`bits_succ`). Then run the return phase (`incB_run`) back to
cell `0`; the head ranges of the two phases combine. -/
lemma inc_run (c : Cfg m Bool Λ x) (n : ℕ) :
    ∃ T, rrun P oracle (regCfg c cC r (FinTM.bufferTape (Nat.bits n)) 0) T =
        regCfg c next r (FinTM.bufferTape (Nat.bits (n + 1))) 0 ∧
      ∀ t < T, ∃ s f q, rrun P oracle (regCfg c cC r (FinTM.bufferTape (Nat.bits n)) 0) t =
        regCfg c s r f q ∧ (s = cC ∨ s = cB) ∧ -1 ≤ q ∧ q ≤ (Nat.bits (n + 1)).length := by
  obtain ⟨T₁, p, hp1, hp2, hr1, hm1⟩ := incC_run P oracle r cC cB hC hCc c (Nat.bits n) []
  simp only [List.nil_append, List.length_nil, Nat.cast_zero] at hp2 hr1 hm1
  rw [← bits_succ] at hp2 hr1
  obtain ⟨hr2, hm2⟩ := incB_run P oracle r cB next hB hBc c (Nat.bits (n + 1)) (p + 1).toNat p
    (by omega) hp2
  refine ⟨T₁ + ((p + 1).toNat + 1), by rw [rrun_add, hr1, hr2], fun t ht => ?_⟩
  rcases Nat.lt_or_ge t T₁ with h | h
  · obtain ⟨f, q, hq, h1, h2⟩ := hm1 t h
    have hl : (Nat.bits n).length ≤ (Nat.bits (n + 1)).length := by
      rw [bits_succ]
      generalize Nat.bits n = w
      induction w with
      | nil => simp [incW]
      | cons b w ih => cases b <;> simp [incW, ih]
    exact ⟨cC, f, q, hq, Or.inl rfl, by omega, by omega⟩
  · obtain ⟨t', rfl⟩ : ∃ t', t = T₁ + t' := ⟨t - T₁, by omega⟩
    rw [rrun_add, hr1]
    obtain ⟨q, hq, h1, h2⟩ := hm2 t' (by omega)
    exact ⟨cB, _, q, hq, Or.inr rfl, h1, by omega⟩

end Inc

end Complexity.LogProg

```


## ===== TCSlib/Complexity/SpaceComplexity/Machines/FragDec.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.Lib

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Program fragments: decrement and clear

The first half of `TCSlib.Complexity.SpaceComplexity.Machines.Frag`: words without trailing
`0`, the decrement fragment, the walk to the right end of a register word and the clear
fragment.

## Main definitions

* `Complexity.LogProg.decW` — the decrement of a little-endian word.

## Main results

* `Complexity.LogProg.dec_run` — `Nat.bits n ↦ Nat.bits (n - 1)`.
* `Complexity.LogProg.toEnd_run` — the walk to the right end of a word.
* `Complexity.LogProg.clr_run` — `Nat.bits n ↦ Nat.bits 0`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.)
-/

namespace Complexity.LogProg

open Turing

/-! ## Words -/

/-- The decrement of a little-endian word (borrow propagation, dropping a final `0`). -/
def decW : List Bool → List Bool
  | [] => []
  | false :: w => true :: decW w
  | [true] => []
  | true :: b :: w => false :: b :: w

/-- A word without a trailing `0`. -/
def Canon (w : List Bool) : Prop := ∀ h : w ≠ [], w.getLast h = true

/-- The binary word of a number has no trailing `0`. -/
lemma canon_bits (n : ℕ) : Canon (Nat.bits n) := fun h => bits_getLast n h

/-- A word without trailing `0` keeps that property when its first letter is dropped. -/
lemma canon_tail {b : Bool} {w : List Bool} (h : Canon (b :: w)) : Canon w := by
  intro hw
  have := h (by simp)
  rwa [List.getLast_cons hw] at this

/-- Decrementing the increment of a word without trailing `0` gives the word back. -/
lemma decW_incW (w : List Bool) (h : Canon w) : decW (incW w) = w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b with
    | false =>
      cases w with
      | nil => have := h (by simp); simp at this
      | cons c w => rfl
    | true => simp only [incW, decW]; rw [ih (canon_tail h)]

/-- The binary word of `n - 1` is the decrement of that of `n`. -/
lemma bits_pred (n : ℕ) : Nat.bits (n - 1) = decW (Nat.bits n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Nat.zero_bits, decW]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, bits_succ, decW_incW _ (canon_bits k)]

/-- The binary word of `n / 2` is the tail of that of `n`. -/
lemma bits_half (n : ℕ) : Nat.bits (n / 2) = (Nat.bits n).tail := by
  rw [← Nat.div2_val, Nat.div2_bits_eq_tail]

/-- The parity of `n` is its first binary digit. -/
lemma bits_head_odd (n : ℕ) : (Nat.bits n).head? = if n = 0 then none else some (decide (n % 2 = 1)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Nat.zero_bits]
  · have hdecomp : n = 2 * (n / 2) + (decide (n % 2 = 1)).toNat := by
      rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h] <;> omega
    have hb : n / 2 = 0 → decide (n % 2 = 1) = true := by intro h0; simp; omega
    have e := bits_two_mul_add (n / 2) _ hb
    rw [← hdecomp] at e
    rw [e]; simp [show n ≠ 0 by omega]

/-- Erasing the last cell of a buffer tape holding `pre ++ [b]` leaves a buffer tape holding
`pre`. -/
lemma bufferTape_erase_last (pre : List Bool) (b : Bool) :
    Function.update (FinTM.bufferTape (pre ++ [b])) (pre.length : ℤ) none =
      FinTM.bufferTape pre := by
  funext z
  by_cases hz : z = (pre.length : ℤ)
  · subst hz; simp [FinTM.bufferTape]
  · rw [Function.update_of_ne hz]
    simp only [FinTM.bufferTape]
    split_ifs with h0
    · by_cases h1 : z.toNat < pre.length
      · rw [List.getElem?_append_left h1]
      · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]
    · rfl

/-! ## The decrement fragment -/

/-- The borrow state: `0`s become `1`s moving right; the first `1` becomes `0` and the next
cell decides whether it was the last bit. -/
def decDAct {m : ℕ} {Λ : Type} (r : Fin m) (dD dL dB : Λ) (rd : Option Bool) :
    Action m Bool Λ :=
  match rd with
  | some false => regAct r (some (some true)) 1 dD
  | some true => regAct r (some (some false)) 1 dL
  | none => regAct r none (-1) dB

/-- The lookahead after the borrow: a blank means the new `0` is a trailing zero. -/
def decLAct {m : ℕ} {Λ : Type} (r : Fin m) (dE dB : Λ) (rd : Option Bool) :
    Action m Bool Λ :=
  match rd with
  | none => regAct r none (-1) dE
  | some _ => regAct r none (-1) dB

/-- Erase the trailing zero. -/
def decEAct {m : ℕ} {Λ : Type} (r : Fin m) (dB : Λ) : Action m Bool Λ :=
  regAct r (some none) (-1) dB

section Dec

variable {m d : ℕ} {Λ : Type} {x : List Bool} (P : RProg m d Λ)
  (oracle : Fin d → List Bool → Bool) (r : Fin m) (dD dL dE dB next : Λ)
  (hD : ∀ a w, P.tm.tr dD a w = decDAct r dD dL dB (w r))
  (hL : ∀ a w, P.tm.tr dL a w = decLAct r dE dB (w r))
  (hE : ∀ a w, P.tm.tr dE a w = decEAct r dB)
  (hB : ∀ a w, P.tm.tr dB a w = incBAct r dB next (w r))
  (hDc : P.call dD = none) (hLc : P.call dL = none) (hEc : P.call dE = none)
  (hBc : P.call dB = none)

/-- Peel the first step off a run. -/
lemma rrun_succ_left (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (c : Cfg m Bool Λ x)
    (n : ℕ) : rrun P oracle c (n + 1) = rrun P oracle (rrun P oracle c 1) n := by
  rw [Nat.add_comm, rrun_add]

/-- One ordinary step of a program from a `regCfg`. -/
lemma rrun_one_reg (c : Cfg m Bool Λ x) (s : Λ) (f : ℤ → Option Bool) (p : ℤ)
    (hs : P.call s = none) :
    rrun P oracle (regCfg c s r f p) 1 =
      (P.tm.tr s (regCfg c s r f p).inputSymbol (regCfg c s r f p).workTapeSymbols).apply
        (regCfg c s r f p) := by
  rw [rrun_one, rstep_noncall P oracle _ s rfl hs]
  unfold MultiTapeTM.step
  simp only [regCfg_state]

include hD hL hE hDc hLc hEc in
/-- **The borrow phase** of the decrement: from `dD` with the head at the start of the suffix `w`
(no trailing `0`), the program reaches `dB` with `w` replaced by its decrement `decW w`, the
head in range throughout.

**Proof sketch.** Induction on `w`. A leading `0` becomes `1` and the borrow moves right; a
leading `1` becomes `0` and ends the borrow. If that `1` was the last letter, the trailing `0`
is erased through `dL`/`dE`. The head stays within `[|pre|, |pre ++ w|]`. -/
lemma decD_run (c : Cfg m Bool Λ x) :
    ∀ (w pre : List Bool), Canon w → ∃ (T : ℕ) (p : ℤ), -1 ≤ p ∧ p < (pre ++ decW w).length ∧
      rrun P oracle (regCfg c dD r (FinTM.bufferTape (pre ++ w)) pre.length) T =
        regCfg c dB r (FinTM.bufferTape (pre ++ decW w)) p ∧
      ∀ t < T, ∃ s f q, rrun P oracle (regCfg c dD r (FinTM.bufferTape (pre ++ w)) pre.length) t =
        regCfg c s r f q ∧ (s = dD ∨ s = dL ∨ s = dE) ∧ (pre.length : ℤ) ≤ q ∧
          q ≤ (pre ++ w).length := by
  intro w
  induction w with
  | nil =>
    intro pre _
    refine ⟨1, (pre.length : ℤ) - 1, by omega, by simp [decW], ?_, ?_⟩
    · rw [rrun_one_reg P oracle r c dD _ _ hDc, hD, regCfg_read]
      have hrd : FinTM.bufferTape (pre ++ []) (pre.length : ℤ) = none := by simp
      rw [hrd]
      simp only [decDAct]
      rw [apply_regAct]
      simp [decW, sub_eq_add_neg]
    · intro t ht
      obtain rfl : t = 0 := by omega
      exact ⟨_, _, _, rfl, Or.inl rfl, le_rfl, by simp⟩
  | cons b w ih =>
    intro pre hcan
    cases b with
    | false =>
      obtain ⟨T, p, hp1, hp2, hrun, hmid⟩ := ih (pre ++ [true]) (canon_tail hcan)
      have hstep : rrun P oracle (regCfg c dD r (FinTM.bufferTape (pre ++ false :: w))
          pre.length) 1 =
          regCfg c dD r (FinTM.bufferTape (pre ++ [true] ++ w)) (pre ++ [true]).length := by
        rw [rrun_one_reg P oracle r c dD _ _ hDc, hD, regCfg_read]
        have hrd : FinTM.bufferTape (pre ++ false :: w) (pre.length : ℤ) = some false := by
          simp
        rw [hrd]
        simp only [decDAct]
        rw [apply_regAct]
        dsimp only
        rw [update_bufferTape_cons]
        simp
      refine ⟨1 + T, p, hp1, by simpa [decW] using hp2, ?_, ?_⟩
      · rw [rrun_add, hstep, hrun]; simp [decW]
      · intro t ht
        rcases Nat.lt_or_ge t 1 with h | h
        · obtain rfl : t = 0 := by omega
          exact ⟨_, _, _, rfl, Or.inl rfl, le_rfl, by simp; omega⟩
        · obtain ⟨t', rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
          rw [rrun_add, hstep]
          obtain ⟨s, f, q, hq, hs, h1, h2⟩ := hmid t' (by omega)
          exact ⟨s, f, q, hq, hs, by simp at h1 ⊢; omega, by simp at h2 ⊢; omega⟩
    | true =>
      have hstep : rrun P oracle (regCfg c dD r (FinTM.bufferTape (pre ++ true :: w))
          pre.length) 1 =
          regCfg c dL r (FinTM.bufferTape (pre ++ false :: w)) ((pre.length : ℤ) + 1) := by
        rw [rrun_one_reg P oracle r c dD _ _ hDc, hD, regCfg_read]
        have hrd : FinTM.bufferTape (pre ++ true :: w) (pre.length : ℤ) = some true := by simp
        rw [hrd]
        simp only [decDAct]
        rw [apply_regAct]
        dsimp only
        rw [update_bufferTape_cons]
        simp
      cases w with
      | nil =>
        -- the last bit: erase it
        have hstep2 : rrun P oracle (regCfg c dL r (FinTM.bufferTape (pre ++ [false]))
            ((pre.length : ℤ) + 1)) 1 =
            regCfg c dE r (FinTM.bufferTape (pre ++ [false])) pre.length := by
          rw [rrun_one_reg P oracle r c dL _ _ hLc, hL, regCfg_read]
          have hrd : FinTM.bufferTape (pre ++ [false]) ((pre.length : ℤ) + 1) = none := by
            simp [FinTM.bufferTape]
          rw [hrd]
          simp only [decLAct]
          rw [apply_regAct]
          simp
        have hstep3 : rrun P oracle (regCfg c dE r (FinTM.bufferTape (pre ++ [false]))
            pre.length) 1 = regCfg c dB r (FinTM.bufferTape pre) ((pre.length : ℤ) - 1) := by
          rw [rrun_one_reg P oracle r c dE _ _ hEc, hE]
          simp only [decEAct]
          rw [apply_regAct]
          dsimp only
          rw [bufferTape_erase_last]
          simp [sub_eq_add_neg]
        refine ⟨1 + (1 + 1), (pre.length : ℤ) - 1, by omega, by simp [decW], ?_, ?_⟩
        · rw [rrun_add, hstep, rrun_add, hstep2, hstep3]; simp [decW]
        · intro t ht
          rcases Nat.lt_or_ge t 1 with h | h
          · obtain rfl : t = 0 := by omega
            exact ⟨_, _, _, rfl, Or.inl rfl, le_rfl, by simp⟩
          rw [show t = 1 + (t - 1) by omega, rrun_add, hstep]
          rcases Nat.lt_or_ge (t - 1) 1 with h' | h'
          · rw [show t - 1 = 0 by omega]
            exact ⟨_, _, _, rfl, Or.inr (Or.inl rfl), by omega, by simp⟩
          · rw [show t - 1 = 1 + 0 by omega, rrun_add, hstep2]
            exact ⟨_, _, _, rfl, Or.inr (Or.inr rfl), le_rfl, by simp⟩
      | cons b' w' =>
        have hstep2 : rrun P oracle (regCfg c dL r (FinTM.bufferTape (pre ++ false :: b' :: w'))
            ((pre.length : ℤ) + 1)) 1 =
            regCfg c dB r (FinTM.bufferTape (pre ++ false :: b' :: w')) pre.length := by
          rw [rrun_one_reg P oracle r c dL _ _ hLc, hL, regCfg_read]
          have hrd : FinTM.bufferTape (pre ++ false :: b' :: w') ((pre.length : ℤ) + 1) =
              some b' := by
            simp only [FinTM.bufferTape]
            rw [if_pos (by omega), show ((pre.length : ℤ) + 1).toNat = pre.length + 1 by omega]
            simp
          rw [hrd]
          simp only [decLAct]
          rw [apply_regAct]
          simp
        refine ⟨1 + 1, pre.length, by omega, by simp [decW]; omega, ?_, ?_⟩
        · rw [rrun_add, hstep, hstep2]; simp [decW]
        · intro t ht
          rcases Nat.lt_or_ge t 1 with h | h
          · obtain rfl : t = 0 := by omega
            exact ⟨_, _, _, rfl, Or.inl rfl, le_rfl, by simp; omega⟩
          · obtain rfl : t = 1 := by omega
            rw [hstep]
            exact ⟨_, _, _, rfl, Or.inr (Or.inl rfl), by omega, by simp; omega⟩

include hD hL hE hB hDc hLc hEc hBc in
/-- **The decrement fragment**: `Nat.bits n ↦ Nat.bits (n - 1)` on register `r`, head back on
cell `0`, head in `[-1, |Nat.bits n|]` throughout.

**Proof sketch.** For `n = 0` the word is empty and the fragment returns at once. Otherwise run
the borrow phase (`decD_run`), which replaces `bits n` by `decW (bits n) = bits (n - 1)`
(`decW_incW`, `bits_succ`). Then run the return walk to cell `0`; the head ranges combine. -/
lemma dec_run (c : Cfg m Bool Λ x) (n : ℕ) :
    ∃ T, rrun P oracle (regCfg c dD r (FinTM.bufferTape (Nat.bits n)) 0) T =
        regCfg c next r (FinTM.bufferTape (Nat.bits (n - 1))) 0 ∧
      ∀ t < T, ∃ s f q, rrun P oracle (regCfg c dD r (FinTM.bufferTape (Nat.bits n)) 0) t =
        regCfg c s r f q ∧ P.call s = none ∧ -1 ≤ q ∧ q ≤ (Nat.bits n).length := by
  obtain ⟨T₁, p, hp1, hp2, hr1, hm1⟩ := decD_run P oracle r dD dL dE dB hD hL hE hDc hLc hEc c
    (Nat.bits n) [] (canon_bits n)
  simp only [List.nil_append, List.length_nil, Nat.cast_zero] at hp2 hr1 hm1
  rw [← bits_pred] at hp2 hr1
  obtain ⟨hr2, hm2⟩ := incB_run P oracle r dB next hB hBc c (Nat.bits (n - 1)) (p + 1).toNat p
    (by omega) hp2
  have hlen : (Nat.bits (n - 1)).length ≤ (Nat.bits n).length := by
    exact length_bits_mono (by omega)
  refine ⟨T₁ + ((p + 1).toNat + 1), by rw [rrun_add, hr1, hr2], fun t ht => ?_⟩
  rcases Nat.lt_or_ge t T₁ with h | h
  · obtain ⟨s, f, q, hq, hs, h1, h2⟩ := hm1 t h
    exact ⟨s, f, q, hq, by rcases hs with rfl | rfl | rfl <;> assumption, by omega, h2⟩
  · obtain ⟨t', rfl⟩ : ∃ t', t = T₁ + t' := ⟨t - T₁, by omega⟩
    rw [rrun_add, hr1]
    obtain ⟨q, hq, h1, h2⟩ := hm2 t' (by omega)
    exact ⟨dB, _, q, hq, hBc, h1, by omega⟩

end Dec

/-! ## Walking to the right end -/

/-- Walk right over the word; at its right end step back and continue in `nx`. -/
def toEndAct {m : ℕ} {Λ : Type} (r : Fin m) (cR nx : Λ) (rd : Option Bool) : Action m Bool Λ :=
  match rd with
  | some _ => regAct r none 1 cR
  | none => regAct r none (-1) nx

section ToEnd

variable {m d : ℕ} {Λ : Type} {x : List Bool} (P : RProg m d Λ)
  (oracle : Fin d → List Bool → Bool) (r : Fin m) (cR nx : Λ)
  (hR : ∀ a w, P.tm.tr cR a w = toEndAct r cR nx (w r)) (hRc : P.call cR = none)

include hR hRc in
/-- **The walk to the right end** of a register word: from `cR` at position `p ≥ 0` the head moves
right to the blank after `w`, then back onto the last letter, entering `nx`.

**Proof sketch.** Induction on `n = |w| - p`: on a letter the head moves right; on the blank at
`|w|` it moves left and the state becomes `nx`. The head stays in `[p, |w|]`. -/
lemma toEnd_run (c : Cfg m Bool Λ x) (w : List Bool) :
    ∀ (n : ℕ) (p : ℤ), (w.length : ℤ) - p = n → 0 ≤ p →
      rrun P oracle (regCfg c cR r (FinTM.bufferTape w) p) (n + 1) =
        regCfg c nx r (FinTM.bufferTape w) ((w.length : ℤ) - 1) ∧
      ∀ t < n + 1, ∃ q, rrun P oracle (regCfg c cR r (FinTM.bufferTape w) p) t =
        regCfg c cR r (FinTM.bufferTape w) q ∧ p ≤ q ∧ q ≤ w.length := by
  intro n
  induction n with
  | zero =>
    intro p hp _
    have hpw : p = w.length := by omega
    refine ⟨?_, fun t ht => ⟨p, by obtain rfl : t = 0 := by omega
                                   rfl, le_rfl, by omega⟩⟩
    rw [rrun_one_reg P oracle r c cR _ _ hRc, hR, regCfg_read]
    have hrd : FinTM.bufferTape w p = none := by rw [hpw]; simp
    rw [hrd]
    simp only [toEndAct]
    rw [apply_regAct]
    simp [hpw, sub_eq_add_neg]
  | succ n ih =>
    intro p hp h0
    obtain ⟨j, hj⟩ : ∃ j : ℕ, p = j := ⟨p.toNat, by omega⟩
    have hjw : j < w.length := by omega
    have hstep : rrun P oracle (regCfg c cR r (FinTM.bufferTape w) p) 1 =
        regCfg c cR r (FinTM.bufferTape w) (p + 1) := by
      rw [rrun_one_reg P oracle r c cR _ _ hRc, hR, regCfg_read]
      have hrd : FinTM.bufferTape w p = some w[j] := by
        rw [hj]; simp [List.getElem?_eq_getElem hjw]
      rw [hrd]
      simp only [toEndAct]
      rw [apply_regAct]
      simp
    obtain ⟨ihr, ihm⟩ := ih (p + 1) (by omega) (by omega)
    refine ⟨?_, fun t ht => ?_⟩
    · rw [show n + 1 + 1 = 1 + (n + 1) by ring, rrun_add, hstep, ihr]
    · rcases Nat.lt_or_ge t 1 with h | h
      · obtain rfl : t = 0 := by omega
        exact ⟨p, rfl, le_rfl, by omega⟩
      · obtain ⟨t', rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
        rw [rrun_add, hstep]
        obtain ⟨q, hq, h1, h2⟩ := ihm t' (by omega)
        exact ⟨q, hq, by omega, h2⟩

end ToEnd

/-! ## The clear fragment -/

/-- Erase walking left; at the left blank step onto cell `0` and continue. -/
def clrEAct {m : ℕ} {Λ : Type} (r : Fin m) (cE next : Λ) (rd : Option Bool) :
    Action m Bool Λ :=
  match rd with
  | some _ => regAct r (some none) (-1) cE
  | none => regAct r none 1 next

section Clr

variable {m d : ℕ} {Λ : Type} {x : List Bool} (P : RProg m d Λ)
  (oracle : Fin d → List Bool → Bool) (r : Fin m) (cR cE next : Λ)
  (hR : ∀ a w, P.tm.tr cR a w = toEndAct r cR cE (w r))
  (hE : ∀ a w, P.tm.tr cE a w = clrEAct r cE next (w r))
  (hRc : P.call cR = none) (hEc : P.call cE = none)

include hE hEc in
/-- **The erasing walk** of the clear fragment: from `cE` on the last letter of `w.take k`, the
program erases the word right to left and reaches `next` on cell `0` of a blank register.

**Proof sketch.** Induction on `k`. Each step erases the cell under the head and moves left; at
the left blank `-1` the head moves right onto cell `0` and the state becomes `next`. -/
lemma clrE_run (c : Cfg m Bool Λ x) (w : List Bool) :
    ∀ k ≤ w.length,
      rrun P oracle (regCfg c cE r (FinTM.bufferTape (w.take k)) ((k : ℤ) - 1)) (k + 1) =
        regCfg c next r (FinTM.bufferTape []) 0 ∧
      ∀ t < k + 1, ∃ f q, rrun P oracle
        (regCfg c cE r (FinTM.bufferTape (w.take k)) ((k : ℤ) - 1)) t =
          regCfg c cE r f q ∧ -1 ≤ q ∧ q ≤ (k : ℤ) - 1 := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨?_, fun t ht => ⟨_, _, by obtain rfl : t = 0 := by omega
                                      rfl, by omega, le_rfl⟩⟩
    rw [rrun_one_reg P oracle r c cE _ _ hEc, hE, regCfg_read]
    have hrd : FinTM.bufferTape (w.take 0) (((0 : ℕ) : ℤ) - 1) = none := by simp
    rw [hrd]
    simp only [clrEAct]
    rw [apply_regAct]
    simp
  | succ k ih =>
    intro hk
    have hkw : k < w.length := by omega
    have htake : w.take (k + 1) = w.take k ++ [w[k]] := by
      rw [List.take_succ, List.getElem?_eq_getElem hkw]; rfl
    have hlen : (w.take k).length = k := List.length_take_of_le (by omega)
    have hstep : rrun P oracle (regCfg c cE r (FinTM.bufferTape (w.take (k + 1)))
        (((k + 1 : ℕ) : ℤ) - 1)) 1 =
        regCfg c cE r (FinTM.bufferTape (w.take k)) ((k : ℤ) - 1) := by
      rw [rrun_one_reg P oracle r c cE _ _ hEc, hE, regCfg_read]
      have hrd : FinTM.bufferTape (w.take (k + 1)) (((k + 1 : ℕ) : ℤ) - 1) = some w[k] := by
        rw [htake]; simp only [FinTM.bufferTape]
        rw [if_pos (by omega), show (((k + 1 : ℕ) : ℤ) - 1).toNat = (w.take k).length by
          rw [hlen]; omega]
        simp only [List.getElem?_append_right (le_refl _), Nat.sub_self]
        rfl
      rw [hrd]
      simp only [clrEAct]
      rw [apply_regAct]
      dsimp only
      rw [show (((k + 1 : ℕ) : ℤ) - 1) = ((w.take k).length : ℤ) by rw [hlen]; push_cast; ring,
        htake, bufferTape_erase_last, hlen]
      simp [sub_eq_add_neg]
    obtain ⟨ihr, ihm⟩ := ih (by omega)
    refine ⟨?_, fun t ht => ?_⟩
    · rw [show k + 1 + 1 = 1 + (k + 1) by ring, rrun_add, hstep, ihr]
    · rcases Nat.lt_or_ge t 1 with h | h
      · obtain rfl : t = 0 := by omega
        exact ⟨_, _, rfl, by omega, le_rfl⟩
      · obtain ⟨t', rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
        rw [rrun_add, hstep]
        obtain ⟨f, q, hq, h1, h2⟩ := ihm t' (by omega)
        exact ⟨f, q, hq, h1, by push_cast at h2 ⊢; omega⟩

include hR hE hRc hEc in
/-- **The clear fragment**: `Nat.bits n ↦ Nat.bits 0` on register `r`, head back on cell `0`,
head in `[-1, |Nat.bits n|]` throughout. -/
lemma clr_run (c : Cfg m Bool Λ x) (n : ℕ) :
    ∃ T, rrun P oracle (regCfg c cR r (FinTM.bufferTape (Nat.bits n)) 0) T =
        regCfg c next r (FinTM.bufferTape (Nat.bits 0)) 0 ∧
      ∀ t < T, ∃ s f q, rrun P oracle (regCfg c cR r (FinTM.bufferTape (Nat.bits n)) 0) t =
        regCfg c s r f q ∧ P.call s = none ∧ -1 ≤ q ∧ q ≤ (Nat.bits n).length := by
  set w := Nat.bits n
  obtain ⟨h1, hm1⟩ := toEnd_run P oracle r cR cE hR hRc c w w.length 0 (by simp) le_rfl
  obtain ⟨h2, hm2⟩ := clrE_run P oracle r cE next hE hEc c w w.length le_rfl
  rw [List.take_length] at h2 hm2
  refine ⟨w.length + 1 + (w.length + 1), ?_, fun t ht => ?_⟩
  · rw [rrun_add, h1, h2, Nat.zero_bits]
  · rcases Nat.lt_or_ge t (w.length + 1) with h | h
    · obtain ⟨q, hq, hq1, hq2⟩ := hm1 t h
      exact ⟨cR, _, q, hq, hRc, by omega, hq2⟩
    · obtain ⟨t', rfl⟩ : ∃ t', t = w.length + 1 + t' := ⟨t - (w.length + 1), by omega⟩
      rw [rrun_add, h1]
      obtain ⟨f, q, hq, hq1, hq2⟩ := hm2 t' (by omega)
      exact ⟨cE, f, q, hq, hEc, hq1, by omega⟩

end Clr

end Complexity.LogProg

```


## ===== TCSlib/Complexity/SpaceComplexity/Machines/Frag.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.FragDec

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Program fragments: decrement, clear, halve

More single-register fragments of register-tape programs, in the style of
`Complexity.LogProg.inc_run`: each is specified by its transitions and proved once against
the program semantics. Counters are the words `Nat.bits n` from cell `0`.

The decrement and clear fragments are in
`TCSlib.Complexity.SpaceComplexity.Machines.FragDec`, which this file re-exports; this file
has the halving and equality fragments.

## Main definitions

* `Complexity.LogProg.decW` — the decrement of a little-endian word.

## Main results

* `Complexity.LogProg.dec_run` — `Nat.bits n ↦ Nat.bits (n - 1)`.
* `Complexity.LogProg.clr_run` — `Nat.bits n ↦ Nat.bits 0`.
* `Complexity.LogProg.half_run` — `Nat.bits n ↦ Nat.bits (n / 2)`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.)
-/

namespace Complexity.LogProg

open Turing

/-! ## The halving fragment -/

/-- The left walk of the halving: write the carried symbol (the cell to the right), carry the
current one; at the left blank step onto cell `0` and continue. -/
def halfLAct {m : ℕ} {Λ : Type} (r : Fin m) (carry : Option Bool) (hF hT next : Λ)
    (rd : Option Bool) : Action m Bool Λ :=
  match rd with
  | some b => regAct r (some carry) (-1) (if b then hT else hF)
  | none => regAct r none 1 next

section Half

variable {m d : ℕ} {Λ : Type} {x : List Bool} (P : RProg m d Λ)
  (oracle : Fin d → List Bool → Bool) (r : Fin m) (hR h0 hF hT next : Λ)
  (hRt : ∀ a w, P.tm.tr hR a w = toEndAct r hR h0 (w r))
  (h0t : ∀ a w, P.tm.tr h0 a w = halfLAct r none hF hT next (w r))
  (hFt : ∀ a w, P.tm.tr hF a w = halfLAct r (some false) hF hT next (w r))
  (hTt : ∀ a w, P.tm.tr hT a w = halfLAct r (some true) hF hT next (w r))
  (hRc : P.call hR = none) (h0c : P.call h0 = none) (hFc : P.call hF = none)
  (hTc : P.call hT = none)

/-- The left-walk state carrying a given optional symbol. -/
def halfSt (h0 hF hT : Λ) : Option Bool → Λ
  | none => h0
  | some false => hF
  | some true => hT

include h0t hFt hTt h0c hFc hTc in
/-- **The shifting walk** of the halving fragment: from the position `k - 1` after the first `k`
letters have been shifted, carrying `w[k]` in the state, the program shifts the remaining
letters one cell left and returns to cell `0` with `w.tail` written.

**Proof sketch.** Induction on `k`. Each step writes the carried letter, picks up the letter
under the head and moves left. At the left blank the head moves right onto cell `0`, and the
tape holds `w` with its first letter dropped. -/
lemma halfL_run (c : Cfg m Bool Λ x) (w : List Bool) :
    ∀ k ≤ w.length,
      rrun P oracle (regCfg c (halfSt h0 hF hT w[k]?) r (FinTM.bufferTape (w.take k ++ w.drop (k + 1)))
          ((k : ℤ) - 1)) (k + 1) =
        regCfg c next r (FinTM.bufferTape w.tail) 0 ∧
      ∀ t < k + 1, ∃ s f q, rrun P oracle (regCfg c (halfSt h0 hF hT w[k]?) r
          (FinTM.bufferTape (w.take k ++ w.drop (k + 1))) ((k : ℤ) - 1)) t =
          regCfg c s r f q ∧ P.call s = none ∧ -1 ≤ q ∧ q ≤ (k : ℤ) - 1 := by
  have htr : ∀ (cr : Option Bool) a ww, P.tm.tr (halfSt h0 hF hT cr) a ww =
      halfLAct r cr hF hT next (ww r) := by
    intro cr a ww; rcases cr with _ | _ | _
    · exact h0t a ww
    · exact hFt a ww
    · exact hTt a ww
  have hc : ∀ cr, P.call (halfSt h0 hF hT cr) = none := by
    intro cr; rcases cr with _ | _ | _
    · exact h0c
    · exact hFc
    · exact hTc
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨?_, fun t ht => ?_⟩
    swap
    · obtain rfl : t = 0 := by omega
      exact ⟨_, _, _, rfl, hc _, by omega, le_rfl⟩
    rw [rrun_one_reg P oracle r c _ _ _ (hc _), htr, regCfg_read]
    have hrd : FinTM.bufferTape (w.take 0 ++ w.drop (0 + 1)) (((0 : ℕ) : ℤ) - 1) = none := by
      simp
    rw [hrd]
    simp only [halfLAct]
    rw [apply_regAct]
    simp [List.drop_one]
  | succ k ih =>
    intro hk
    have hkw : k < w.length := by omega
    have hlen : (w.take k).length = k := List.length_take_of_le (by omega)
    have hsplit : w.take (k + 1) ++ w.drop (k + 1 + 1) = w.take k ++ w[k] :: w.drop (k + 2) := by
      have h1 : w.take (k + 1) = w.take k ++ [w[k]] := by
        rw [List.take_succ, List.getElem?_eq_getElem hkw]; rfl
      rw [h1, List.append_assoc]; rfl
    have hstep : rrun P oracle (regCfg c (halfSt h0 hF hT w[k + 1]?) r
        (FinTM.bufferTape (w.take (k + 1) ++ w.drop (k + 1 + 1))) (((k + 1 : ℕ) : ℤ) - 1)) 1 =
        regCfg c (halfSt h0 hF hT w[k]?) r (FinTM.bufferTape (w.take k ++ w.drop (k + 1)))
          ((k : ℤ) - 1) := by
      rw [rrun_one_reg P oracle r c _ _ _ (hc _), htr, regCfg_read, hsplit]
      have hpos : (((k + 1 : ℕ) : ℤ) - 1) = ((w.take k).length : ℤ) := by
        rw [hlen]; push_cast; ring
      have hrd : FinTM.bufferTape (w.take k ++ w[k] :: w.drop (k + 2))
          (((k + 1 : ℕ) : ℤ) - 1) = some w[k] := by
        rw [hpos]; simp
      rw [hrd]
      simp only [halfLAct]
      rw [apply_regAct]
      dsimp only
      rw [List.getElem?_eq_getElem hkw]
      congr 1
      · cases w[k] <;> rfl
      · rw [hpos]
        rcases hk2 : w[k + 1]? with _ | v
        · -- `k + 1 = |w|`: erase the last cell
          have hkl : k + 1 = w.length := by
            by_contra hne; rw [List.getElem?_eq_getElem (by omega)] at hk2; simp at hk2
          have hd1 : w.drop (k + 2) = [] := List.drop_eq_nil_of_le (by omega)
          have hd2 : w.drop (k + 1) = [] := List.drop_eq_nil_of_le (by omega)
          rw [hd1, hd2, bufferTape_erase_last]; simp
        · have hd : w.drop (k + 1) = v :: w.drop (k + 2) := by
            rw [List.drop_eq_getElem_cons (by
              by_contra hne; rw [List.getElem?_eq_none (by omega)] at hk2; simp at hk2)]
            congr 1
            rw [List.getElem?_eq_getElem (by
              by_contra hne; rw [List.getElem?_eq_none (by omega)] at hk2; simp at hk2)] at hk2
            simpa using hk2
          rw [hd, update_bufferTape_cons]
      · simp [sub_eq_add_neg]
    obtain ⟨ihr, ihm⟩ := ih (by omega)
    refine ⟨?_, fun t ht => ?_⟩
    · rw [rrun_succ_left, hstep, ihr]
    · rcases Nat.lt_or_ge t 1 with h | h
      · obtain rfl : t = 0 := by omega
        exact ⟨_, _, _, rfl, hc _, by omega, le_rfl⟩
      · obtain ⟨t', rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
        rw [rrun_add, hstep]
        obtain ⟨s', f, q, hq, hs', h1, h2⟩ := ihm t' (by omega)
        exact ⟨s', f, q, hq, hs', h1, by push_cast at h2 ⊢; omega⟩

include hRt hRc h0t hFt hTt h0c hFc hTc in
/-- **The halving fragment**: `Nat.bits n ↦ Nat.bits (n / 2)` on register `r` (drop the
first binary digit), head back on cell `0`, head in `[-1, |Nat.bits n|]` throughout.

**Proof sketch.** Walk to the right end of `bits n` (`toEnd_run`), then shift every letter one
cell left while walking back (`halfL_run`), which drops the first letter. Since `bits (n / 2)`
is the tail of `bits n` (`bits_half`), the register holds `bits (n / 2)`. -/
lemma half_run (c : Cfg m Bool Λ x) (n : ℕ) :
    ∃ T, rrun P oracle (regCfg c hR r (FinTM.bufferTape (Nat.bits n)) 0) T =
        regCfg c next r (FinTM.bufferTape (Nat.bits (n / 2))) 0 ∧
      ∀ t < T, ∃ s f q, rrun P oracle (regCfg c hR r (FinTM.bufferTape (Nat.bits n)) 0) t =
        regCfg c s r f q ∧ P.call s = none ∧ -1 ≤ q ∧ q ≤ (Nat.bits n).length := by
  set w := Nat.bits n
  obtain ⟨h1, hm1⟩ := toEnd_run P oracle r hR h0 hRt hRc c w w.length 0 (by simp) le_rfl
  obtain ⟨h2, hm2⟩ := halfL_run P oracle r h0 hF hT next h0t hFt hTt h0c hFc hTc c w w.length
    le_rfl
  have he : w.take w.length ++ w.drop (w.length + 1) = w := by simp
  have hn : w[w.length]? = none := by simp
  rw [he, hn] at h2 hm2
  refine ⟨w.length + 1 + (w.length + 1), ?_, fun t ht => ?_⟩
  · rw [rrun_add, h1]
    convert h2 using 3
    · rw [bits_half]
  · rcases Nat.lt_or_ge t (w.length + 1) with h | h
    · obtain ⟨q, hq, hq1, hq2⟩ := hm1 t h
      exact ⟨hR, _, q, hq, hRc, by omega, hq2⟩
    · obtain ⟨t', rfl⟩ : ∃ t', t = w.length + 1 + t' := ⟨t - (w.length + 1), by omega⟩
      rw [rrun_add, h1]
      obtain ⟨s', f, q, hq, hs', hq1, hq2⟩ := hm2 t' (by omega)
      exact ⟨s', f, q, hq, hs', hq1, by omega⟩

end Half

/-! ## The equality test of two registers -/

section Eq

variable {m d : ℕ} {Λ : Type} {x : List Bool}

/-- A configuration with state `s` and the heads of registers `r₁`, `r₂` at `k`. -/
def eqCfg (c : Cfg m Bool Λ x) (s : Λ) (r₁ r₂ : Fin m) (k : ℤ) : Cfg m Bool Λ x :=
  ⟨some s, c.inputPos, c.workTapes,
    Function.update (Function.update c.workTapePos r₁ k) r₂ k, c.output⟩

/-- Move the heads of `r₁` and `r₂` together. -/
def mv2Act (r₁ r₂ : Fin m) (mv : SignType) (s : Λ) : Action m Bool Λ :=
  ⟨0, fun r => if r = r₁ ∨ r = r₂ then (none, mv) else (none, 0), none, some s⟩

/-- Applying the two-register move action moves both register heads by `mv` and enters `s'`. -/
lemma apply_mv2Act (c : Cfg m Bool Λ x) (s s' : Λ) (r₁ r₂ : Fin m) (k : ℤ) (mv : SignType) :
    (mv2Act r₁ r₂ mv s').apply (eqCfg c s r₁ r₂ k) = eqCfg c s' r₁ r₂ (k + mv) := by
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ (by simp [mv2Act, eqCfg])
  · funext r z
    simp only [mv2Act, eqCfg, Action.apply]
    split_ifs <;> rfl
  · funext r
    simp only [mv2Act, eqCfg, Action.apply, Function.update_apply]
    by_cases h2 : r = r₂
    · simp [h2]
    · by_cases h1 : r = r₁
      · simp [h1]
      · simp [h1, h2]

/-- The comparison step. -/
def eqCAct (r₁ r₂ : Fin m) (eC eBy eBn : Λ) (a b : Option Bool) : Action m Bool Λ :=
  if a = b then (if a = none then mv2Act r₁ r₂ (-1) eBy else mv2Act r₁ r₂ 1 eC)
  else mv2Act r₁ r₂ (-1) eBn

/-- The return step (reading register `r₁`). -/
def eqBAct (r₁ r₂ : Fin m) (eB l : Λ) (a : Option Bool) : Action m Bool Λ :=
  match a with
  | some _ => mv2Act r₁ r₂ (-1) eB
  | none => mv2Act r₁ r₂ 1 l

variable (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (r₁ r₂ : Fin m)
  (hne : r₁ ≠ r₂) (eC eBy eBn yes no : Λ)
  (hC : ∀ a w, P.tm.tr eC a w = eqCAct r₁ r₂ eC eBy eBn (w r₁) (w r₂))
  (hBy : ∀ a w, P.tm.tr eBy a w = eqBAct r₁ r₂ eBy yes (w r₁))
  (hBn : ∀ a w, P.tm.tr eBn a w = eqBAct r₁ r₂ eBn no (w r₁))
  (hCc : P.call eC = none) (hByc : P.call eBy = none) (hBnc : P.call eBn = none)

include hne in
/-- The two-register view reads register `r₁` at its head position `k`. -/
lemma eqCfg_read₁ (c : Cfg m Bool Λ x) (s : Λ) (k : ℤ) :
    (eqCfg c s r₁ r₂ k).workTapeSymbols r₁ = c.workTapes r₁ k := by
  simp [eqCfg, Cfg.workTapeSymbols, hne]

/-- The two-register view reads register `r₂` at its head position `k`. -/
lemma eqCfg_read₂ (c : Cfg m Bool Λ x) (s : Λ) (k : ℤ) :
    (eqCfg c s r₁ r₂ k).workTapeSymbols r₂ = c.workTapes r₂ k := by
  simp [eqCfg, Cfg.workTapeSymbols]

/-- One step of the program from a two-register view at a non-call state is the transition's
action applied to it. -/
lemma rrun_one_eq (c : Cfg m Bool Λ x) (s : Λ) (k : ℤ) (hs : P.call s = none) :
    rrun P oracle (eqCfg c s r₁ r₂ k) 1 =
      (P.tm.tr s (eqCfg c s r₁ r₂ k).inputSymbol (eqCfg c s r₁ r₂ k).workTapeSymbols).apply
        (eqCfg c s r₁ r₂ k) := by
  rw [rrun_one, rstep_noncall P oracle _ s rfl hs]
  unfold MultiTapeTM.step
  rfl

include hne hC hCc in
/-- **The comparison walk** of the equality test: from `eC` with both heads after the common prefix
`pre` of `w₁` and `w₂`, the program reaches `eBy` if `w₁ = w₂` and `eBn` otherwise, the heads
within `w₁`'s range.

**Proof sketch.** Induction on `u₁`. Equal letters move both heads right and extend the common
prefix. A mismatch, or one word ending before the other, enters `eBn`; both words ending
together enters `eBy`. -/
lemma eqC_run (c : Cfg m Bool Λ x) (w₁ w₂ : List Bool)
    (h₁ : c.workTapes r₁ = FinTM.bufferTape w₁) (h₂ : c.workTapes r₂ = FinTM.bufferTape w₂) :
    ∀ (u₁ u₂ pre : List Bool), w₁ = pre ++ u₁ → w₂ = pre ++ u₂ →
      ∃ (T : ℕ) (p : ℤ), (pre.length : ℤ) - 1 ≤ p ∧ p < w₁.length ∧
        rrun P oracle (eqCfg c eC r₁ r₂ pre.length) T =
          eqCfg c (if w₁ = w₂ then eBy else eBn) r₁ r₂ p ∧
        ∀ t < T, ∃ q, rrun P oracle (eqCfg c eC r₁ r₂ pre.length) t = eqCfg c eC r₁ r₂ q ∧
          (pre.length : ℤ) ≤ q ∧ q ≤ w₁.length := by
  intro u₁
  induction u₁ with
  | nil =>
    intro u₂ pre e1 e2
    refine ⟨1, (pre.length : ℤ) - 1, le_rfl, by rw [e1]; simp, ?_, ?_⟩
    · rw [rrun_one_eq P oracle r₁ r₂ c eC _ hCc, hC, eqCfg_read₁ r₁ r₂ hne, eqCfg_read₂, h₁, h₂]
      have ha : FinTM.bufferTape w₁ pre.length = none := by rw [e1]; simp
      rw [ha]
      cases u₂ with
      | nil =>
        have hb : FinTM.bufferTape w₂ pre.length = none := by rw [e2]; simp
        rw [hb]
        simp only [eqCAct, ↓reduceIte]
        rw [apply_mv2Act]
        simp [e1, e2, sub_eq_add_neg]
      | cons b u₂' =>
        have hb : FinTM.bufferTape w₂ pre.length = some b := by rw [e2]; simp
        rw [hb]
        simp only [eqCAct, reduceCtorEq, ↓reduceIte]
        rw [apply_mv2Act]
        have hneq : w₁ ≠ w₂ := by rw [e1, e2]; simp
        simp [hneq, sub_eq_add_neg]
    · intro t ht
      obtain rfl : t = 0 := by omega
      exact ⟨_, rfl, le_rfl, by rw [e1]; simp⟩
  | cons a u₁' ih =>
    intro u₂ pre e1 e2
    have ha : FinTM.bufferTape w₁ pre.length = some a := by rw [e1]; simp
    cases u₂ with
    | nil =>
      refine ⟨1, (pre.length : ℤ) - 1, le_rfl, by rw [e1]; simp; omega, ?_, ?_⟩
      · rw [rrun_one_eq P oracle r₁ r₂ c eC _ hCc, hC, eqCfg_read₁ r₁ r₂ hne, eqCfg_read₂, h₁, h₂,
          ha]
        have hb : FinTM.bufferTape w₂ pre.length = none := by rw [e2]; simp
        rw [hb]
        simp only [eqCAct, reduceCtorEq, ↓reduceIte]
        rw [apply_mv2Act]
        have hneq : w₁ ≠ w₂ := by rw [e1, e2]; simp
        simp [hneq, sub_eq_add_neg]
      · intro t ht
        obtain rfl : t = 0 := by omega
        exact ⟨_, rfl, le_rfl, by rw [e1]; simp; omega⟩
    | cons b u₂' =>
      have hb : FinTM.bufferTape w₂ pre.length = some b := by rw [e2]; simp
      by_cases hab : a = b
      · subst hab
        obtain ⟨T, p, hp1, hp2, hr, hm⟩ := ih u₂' (pre ++ [a]) (by rw [e1]; simp)
          (by rw [e2]; simp)
        have hstep : rrun P oracle (eqCfg c eC r₁ r₂ pre.length) 1 =
            eqCfg c eC r₁ r₂ (pre ++ [a]).length := by
          rw [rrun_one_eq P oracle r₁ r₂ c eC _ hCc, hC, eqCfg_read₁ r₁ r₂ hne, eqCfg_read₂, h₁,
            h₂, ha, hb]
          simp only [eqCAct, reduceCtorEq, ↓reduceIte]
          rw [apply_mv2Act]
          simp
        refine ⟨1 + T, p, by simp at hp1; omega, hp2, by rw [rrun_add, hstep, hr], ?_⟩
        intro t ht
        rcases Nat.lt_or_ge t 1 with h | h
        · obtain rfl : t = 0 := by omega
          exact ⟨_, rfl, le_rfl, by rw [e1]; simp; omega⟩
        · obtain ⟨t', rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
          rw [rrun_add, hstep]
          obtain ⟨q, hq, hq1, hq2⟩ := hm t' (by omega)
          exact ⟨q, hq, by simp at hq1; omega, hq2⟩
      · refine ⟨1, (pre.length : ℤ) - 1, le_rfl, by rw [e1]; simp; omega, ?_, ?_⟩
        · rw [rrun_one_eq P oracle r₁ r₂ c eC _ hCc, hC, eqCfg_read₁ r₁ r₂ hne, eqCfg_read₂, h₁,
            h₂, ha, hb]
          have hab' : (some a : Option Bool) ≠ some b := by simpa using hab
          simp only [eqCAct, hab', ↓reduceIte]
          rw [apply_mv2Act]
          have hneq : w₁ ≠ w₂ := by rw [e1, e2]; simp; intro h; exact absurd h hab
          simp [hneq, sub_eq_add_neg]
        · intro t ht
          obtain rfl : t = 0 := by omega
          exact ⟨_, rfl, le_rfl, by rw [e1]; simp; omega⟩

include hne in
/-- The return walk of the equality test (reading register `r₁`, whose cells left of the
start are nonblank).

**Proof sketch.** Induction on `n = p + 1`: on a letter of `w₁` both heads move left; at the
left blank both move right onto cell `0` and the state becomes `l`. The heads stay in `[-1, p]`. -/
lemma eqB_run (c : Cfg m Bool Λ x) (w₁ : List Bool) (h₁ : c.workTapes r₁ = FinTM.bufferTape w₁)
    (eB l : Λ) (hBt : ∀ a w, P.tm.tr eB a w = eqBAct r₁ r₂ eB l (w r₁))
    (hBc : P.call eB = none) :
    ∀ (n : ℕ) (p : ℤ), p + 1 = n → p < w₁.length →
      rrun P oracle (eqCfg c eB r₁ r₂ p) (n + 1) = eqCfg c l r₁ r₂ 0 ∧
      ∀ t < n + 1, ∃ q, rrun P oracle (eqCfg c eB r₁ r₂ p) t = eqCfg c eB r₁ r₂ q ∧
        -1 ≤ q ∧ q ≤ p := by
  intro n
  induction n with
  | zero =>
    intro p hp _
    refine ⟨?_, fun t ht => ?_⟩
    swap
    · obtain rfl : t = 0 := by omega
      exact ⟨p, rfl, by omega, le_rfl⟩
    rw [rrun_one_eq P oracle r₁ r₂ c eB _ hBc, hBt, eqCfg_read₁ r₁ r₂ hne, h₁]
    have hrd : FinTM.bufferTape w₁ p = none := by rw [show p = -1 by omega]; simp
    rw [hrd]
    simp only [eqBAct]
    rw [apply_mv2Act]
    congr 1
  | succ n ih =>
    intro p hp hpw
    obtain ⟨j, hj⟩ : ∃ j : ℕ, p = j := ⟨p.toNat, by omega⟩
    have hjw : j < w₁.length := by omega
    have hstep : rrun P oracle (eqCfg c eB r₁ r₂ p) 1 = eqCfg c eB r₁ r₂ (p - 1) := by
      rw [rrun_one_eq P oracle r₁ r₂ c eB _ hBc, hBt, eqCfg_read₁ r₁ r₂ hne, h₁]
      have hrd : FinTM.bufferTape w₁ p = some w₁[j] := by
        rw [hj]; simp [List.getElem?_eq_getElem hjw]
      rw [hrd]
      simp only [eqBAct]
      rw [apply_mv2Act]
      simp [sub_eq_add_neg]
    obtain ⟨ihr, ihm⟩ := ih (p - 1) (by omega) (by omega)
    refine ⟨by rw [rrun_succ_left, hstep, ihr], fun t ht => ?_⟩
    rcases Nat.lt_or_ge t 1 with h | h
    · obtain rfl : t = 0 := by omega
      exact ⟨p, rfl, by omega, le_rfl⟩
    · obtain ⟨t', rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
      rw [rrun_add, hstep]
      obtain ⟨q, hq, h1, h2⟩ := ihm t' (by omega)
      exact ⟨q, hq, h1, by omega⟩

include hne hC hBy hBn hCc hByc hBnc in
/-- **The equality test**: from `eC` with `Nat.bits a` on `r₁` and `Nat.bits b` on `r₂`, both
heads on cell `0`, the program reaches `yes` if `a = b` and `no` otherwise, heads back on
cell `0`, tapes unchanged; both heads stay in `[-1, |Nat.bits a|]`.

**Proof sketch.** Run the comparison walk (`eqC_run`) from the empty common prefix, reaching
`eBy` or `eBn` according to `bits a = bits b`, which is `a = b` by injectivity of `Nat.bits`.
Then run the return walk (`eqB_run`) back to cell `0`, ending in `yes` or `no`. -/
lemma eq_run (c : Cfg m Bool Λ x) (a b : ℕ)
    (h₁ : c.workTapes r₁ = FinTM.bufferTape (Nat.bits a))
    (h₂ : c.workTapes r₂ = FinTM.bufferTape (Nat.bits b)) :
    ∃ T, rrun P oracle (eqCfg c eC r₁ r₂ 0) T = eqCfg c (if a = b then yes else no) r₁ r₂ 0 ∧
      ∀ t < T, ∃ s q, rrun P oracle (eqCfg c eC r₁ r₂ 0) t = eqCfg c s r₁ r₂ q ∧
        P.call s = none ∧ -1 ≤ q ∧ q ≤ (Nat.bits a).length := by
  obtain ⟨T₁, p, hp1, hp2, hr1, hm1⟩ := eqC_run P oracle r₁ r₂ hne eC eBy eBn hC hCc c _ _ h₁ h₂
    (Nat.bits a) (Nat.bits b) [] rfl rfl
  simp only [List.length_nil, Nat.cast_zero] at hp1 hr1 hm1
  have hiff : (Nat.bits a = Nat.bits b) ↔ a = b :=
    ⟨fun h => bits_injective h, fun h => by rw [h]⟩
  by_cases hab : a = b
  · have hw : Nat.bits a = Nat.bits b := hiff.mpr hab
    rw [if_pos hw] at hr1
    obtain ⟨hr2, hm2⟩ := eqB_run P oracle r₁ r₂ hne c _ h₁ eBy yes hBy hByc (p + 1).toNat p
      (by omega) hp2
    refine ⟨T₁ + ((p + 1).toNat + 1), by rw [rrun_add, hr1, hr2, if_pos hab], fun t ht => ?_⟩
    rcases Nat.lt_or_ge t T₁ with h | h
    · obtain ⟨q, hq, hq1, hq2⟩ := hm1 t h
      exact ⟨eC, q, hq, hCc, by omega, hq2⟩
    · obtain ⟨t', rfl⟩ : ∃ t', t = T₁ + t' := ⟨t - T₁, by omega⟩
      rw [rrun_add, hr1]
      obtain ⟨q, hq, hq1, hq2⟩ := hm2 t' (by omega)
      exact ⟨eBy, q, hq, hByc, hq1, by omega⟩
  · have hw : Nat.bits a ≠ Nat.bits b := fun h => hab (hiff.mp h)
    rw [if_neg hw] at hr1
    obtain ⟨hr2, hm2⟩ := eqB_run P oracle r₁ r₂ hne c _ h₁ eBn no hBn hBnc (p + 1).toNat p
      (by omega) hp2
    refine ⟨T₁ + ((p + 1).toNat + 1), by rw [rrun_add, hr1, hr2, if_neg hab], fun t ht => ?_⟩
    rcases Nat.lt_or_ge t T₁ with h | h
    · obtain ⟨q, hq, hq1, hq2⟩ := hm1 t h
      exact ⟨eC, q, hq, hCc, by omega, hq2⟩
    · obtain ⟨t', rfl⟩ : ∃ t', t = T₁ + t' := ⟨t - T₁, by omega⟩
      rw [rrun_add, hr1]
      obtain ⟨q, hq, hq1, hq2⟩ := hm2 t' (by omega)
      exact ⟨eBn, q, hq, hBnc, hq1, by omega⟩

end Eq

end Complexity.LogProg

```


## ===== TCSlib/Complexity/SpaceComplexity/Machines/ParsePlain.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.Frag

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Input shapes and the plain format check

The first half of `TCSlib.Complexity.SpaceComplexity.Machines.Parse`: the input shapes
`⟨1ⁿ, w⟩` and `⟨1ⁿ, ⟨u, w⟩⟩`, input-scanning configurations, the input rewind, and the
format check of plain inputs `⟨1ⁿ, w⟩`.

## Main definitions

* `Complexity.LogProg.ValidPlain`, `Complexity.LogProg.ValidPair` — the input shapes.
* `Complexity.LogProg.xCfg` — a configuration with the input head and one register head
  moved.

## Main results

* `Complexity.LogProg.rewind_x` — the input rewind.
* `Complexity.LogProg.validPlain_iff` — the plain format, read off the leading run.
* `Complexity.LogProg.valPlain_run` — the plain format check.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1: logspace machines read their input in place.)
-/

namespace Complexity.LogProg

open Turing

variable {m d : ℕ} {Λ : Type} {x : List Bool}

/-! ## Input shapes -/

/-- The input is `⟨1ⁿ, w⟩` with `w` without trailing `0`. -/
def ValidPlain (y : List Bool) : Prop :=
  ∃ n w, y = pairEncode (List.replicate n true) w ∧ Canon w

/-- The input is `⟨1ⁿ, ⟨u, w⟩⟩` with `u`, `w` without trailing `0`. -/
def ValidPair (y : List Bool) : Prop :=
  ∃ n u w, y = pairEncode (List.replicate n true) (pairEncode u w) ∧ Canon u ∧ Canon w

/-- Doubling `1ⁿ` gives `1²ⁿ`. -/
lemma dbl_replicate (n : ℕ) : dbl (List.replicate n true) = List.replicate (2 * n) true := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih, Nat.mul_succ]

/-! ## Configurations -/

/-- A configuration with state `s`, input head `ip`, and the head of register `r` at `p`
(tapes as in `c`). -/
def xCfg (c : Cfg m Bool Λ x) (s : Λ) (ip : Fin (x.length + 2)) (r : Fin m) (p : ℤ) :
    Cfg m Bool Λ x :=
  ⟨some s, ip, c.workTapes, Function.update c.workTapePos r p, c.output⟩

/-- The input-scanning view `xCfg c s …` is in state `s`. -/
@[simp] lemma xCfg_state (c : Cfg m Bool Λ x) (s : Λ) (ip : Fin (x.length + 2)) (r : Fin m)
    (p : ℤ) : (xCfg c s ip r p).state = some s := rfl

/-- An action moving the input head and the head of register `r`. -/
def xAct (r : Fin m) (mvI mvR : SignType) (s : Λ) : Action m Bool Λ :=
  ⟨mvI, fun r' => if r' = r then (none, mvR) else (none, 0), none, some s⟩

/-- Reject: write `0` and halt. -/
def rejAct : Action m Bool Λ := ⟨0, fun _ => (none, 0), some false, none⟩

/-- Applying an input-scanning action moves the input head by `mvI`, the register head by
`mvR`, and enters `s'`. -/
lemma apply_xAct (c : Cfg m Bool Λ x) (s s' : Λ) (ip : Fin (x.length + 2)) (r : Fin m) (p : ℤ)
    (mvI mvR : SignType) :
    (xAct r mvI mvR s').apply (xCfg c s ip r p) = xCfg c s' (moveInputPos ip mvI) r (p + mvR) := by
  refine Cfg.ext rfl rfl ?_ ?_ (by simp [xAct, xCfg])
  · funext r' z
    simp only [xAct, xCfg, Action.apply]
    split_ifs <;> rfl
  · funext r'
    simp only [xAct, xCfg, Action.apply]
    by_cases h : r' = r
    · subst h; simp
    · simp [h]

/-- The input-scanning view reads register `r` at its head position `p`. -/
lemma xCfg_read (c : Cfg m Bool Λ x) (s : Λ) (ip : Fin (x.length + 2)) (r : Fin m) (p : ℤ) :
    (xCfg c s ip r p).workTapeSymbols r = c.workTapes r p := by
  simp [xCfg, Cfg.workTapeSymbols]

/-- The input symbol at input position `q` (`0` and `|x| + 1` are the blanks). -/
def inSym (x : List Bool) (q : ℕ) : Option Bool := if q = 0 then none else x[q - 1]?

/-- The input-scanning view reads the input symbol at its input head position. -/
lemma xCfg_inSym (c : Cfg m Bool Λ x) (s : Λ) (ip : Fin (x.length + 2)) (r : Fin m) (p : ℤ) :
    (xCfg c s ip r p).inputSymbol = inSym x ip.val := by
  rw [inputSymbol_eq]; rfl

section Run

variable (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool)

/-- One step of the program from an input-scanning view at a non-call state is the
transition's action applied to it. -/
lemma rrun_one_x (c : Cfg m Bool Λ x) (s : Λ) (ip : Fin (x.length + 2)) (r : Fin m) (p : ℤ)
    (hs : P.call s = none) :
    rrun P oracle (xCfg c s ip r p) 1 =
      (P.tm.tr s (inSym x ip.val) (xCfg c s ip r p).workTapeSymbols).apply (xCfg c s ip r p) := by
  rw [rrun_one, rstep_noncall P oracle _ s rfl hs, ← xCfg_inSym c s ip r p]
  unfold MultiTapeTM.step
  rfl

/-- The input head moves by one inside the tape. -/
lemma moveInputPos_pos_val (ip : Fin (x.length + 2)) (h : ip.val ≤ x.length) :
    (moveInputPos ip 1).val = ip.val + 1 := by
  rw [moveInputPos_val]; simp; omega

/-- Moving the input head left decrements its position (truncated at `0`). -/
lemma moveInputPos_neg_val' (ip : Fin (x.length + 2)) :
    (moveInputPos ip (-1)).val = ip.val - 1 := by
  rw [moveInputPos_val]

/-- **A right scan of the input** through a family of states `st j`: for `k` steps the state
`st j` reads the input at position `q₀ + j` and moves right into `st (j + 1)`, leaving the
registers alone. -/
lemma scanR (c : Cfg m Bool Λ x) (r : Fin m) (p : ℤ) (st : ℕ → Λ) (q₀ k : ℕ)
    (hk : q₀ + k ≤ x.length + 1)
    (htr : ∀ j < k, ∀ w, P.tm.tr (st j) (inSym x (q₀ + j)) w = xAct r 1 0 (st (j + 1)))
    (hc : ∀ j < k, P.call (st j) = none) :
    ∀ (j : ℕ) (hj : j ≤ k), rrun P oracle (xCfg c (st 0) ⟨q₀, by omega⟩ r p) j =
      xCfg c (st j) ⟨q₀ + j, by omega⟩ r p := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    rw [rrun_succ, ih (by omega), ← rrun_one, rrun_one_x P oracle c _ _ r p (hc j (by omega))]
    simp only
    rw [htr j (by omega), apply_xAct]
    congr 1
    · exact Fin.ext (by rw [moveInputPos_pos_val _ (by simp; omega)]; simp; omega)
    · simp

/-- **The input rewind**: from `rw₁` one unconditional left move into `rw₂`, which moves left
over input symbols and, at the left blank, steps onto position `1` into `nx`.

**Proof sketch.** After the first left move, induction on the input head position: on an input
letter the head moves left, and at the left blank (position `0`) it moves right onto position
`1` and the state becomes `nx`. The register head never moves. -/
lemma rewind_x (c : Cfg m Bool Λ x) (r : Fin m) (p : ℤ) (rw₁ rw₂ nx : Λ)
    (h₁ : ∀ a w, P.tm.tr rw₁ a w = xAct r (-1) 0 rw₂)
    (h₂ : ∀ a w, P.tm.tr rw₂ a w = match a with
      | some _ => xAct r (-1) 0 rw₂
      | none => xAct r 1 0 nx)
    (h₁c : P.call rw₁ = none) (h₂c : P.call rw₂ = none) (ip : Fin (x.length + 2)) :
    ∃ T, rrun P oracle (xCfg c rw₁ ip r p) T = xCfg c nx ⟨1, by omega⟩ r p ∧
      ∀ t < T, ∃ s ip', rrun P oracle (xCfg c rw₁ ip r p) t = xCfg c s ip' r p ∧
        P.call s = none := by
  -- the scan phase, by induction on the position
  have scan : ∀ (j : ℕ) (ip' : Fin (x.length + 2)), ip'.val = j → j ≤ x.length →
      rrun P oracle (xCfg c rw₂ ip' r p) (j + 1) = xCfg c nx ⟨1, by omega⟩ r p ∧
      ∀ t < j + 1, ∃ ip'', rrun P oracle (xCfg c rw₂ ip' r p) t = xCfg c rw₂ ip'' r p := by
    intro j
    induction j with
    | zero =>
      intro ip' hip _
      refine ⟨?_, fun t ht => ⟨ip', by obtain rfl : t = 0 := by omega
                                       rfl⟩⟩
      rw [rrun_one_x P oracle c rw₂ ip' r p h₂c, h₂]
      have : inSym x ip'.val = none := by simp [inSym, hip]
      rw [this]
      simp only
      rw [apply_xAct]
      congr 1
      · exact Fin.ext (by rw [moveInputPos_pos_val ip' (by omega)]; show ip'.val + 1 = 1; omega)
      · simp
    | succ j ih =>
      intro ip' hip hj
      have hsym : inSym x ip'.val = some x[j] := by
        simp [inSym, hip, List.getElem?_eq_getElem (show j < x.length by omega)]
      have hstep : rrun P oracle (xCfg c rw₂ ip' r p) 1 =
          xCfg c rw₂ (moveInputPos ip' (-1)) r p := by
        rw [rrun_one_x P oracle c rw₂ ip' r p h₂c, h₂, hsym]
        simp only
        rw [apply_xAct]; simp
      obtain ⟨ihr, ihm⟩ := ih (moveInputPos ip' (-1)) (by rw [moveInputPos_neg_val']; omega)
        (by omega)
      refine ⟨by rw [rrun_succ_left, hstep, ihr], fun t ht => ?_⟩
      rcases Nat.lt_or_ge t 1 with h | h
      · obtain rfl : t = 0 := by omega
        exact ⟨ip', rfl⟩
      · obtain ⟨t', rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
        rw [rrun_add, hstep]
        exact ihm t' (by omega)
  have hstep : rrun P oracle (xCfg c rw₁ ip r p) 1 = xCfg c rw₂ (moveInputPos ip (-1)) r p := by
    rw [rrun_one_x P oracle c rw₁ ip r p h₁c, h₁, apply_xAct]; simp
  obtain ⟨hr, hm⟩ := scan (moveInputPos ip (-1)).val (moveInputPos ip (-1)) rfl
    (by rw [moveInputPos_neg_val']; have := ip.isLt; omega)
  refine ⟨1 + ((moveInputPos ip (-1)).val + 1), by rw [rrun_add, hstep, hr], fun t ht => ?_⟩
  rcases Nat.lt_or_ge t 1 with h | h
  · obtain rfl : t = 0 := by omega
    exact ⟨rw₁, ip, rfl, h₁c⟩
  · obtain ⟨t', rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
    rw [rrun_add, hstep]
    obtain ⟨ip'', h⟩ := hm t' (by omega)
    exact ⟨rw₂, ip'', h, h₂c⟩

end Run

/-! ## The plain format check -/

/-- The leading run of `1`s of `x`. -/
def tRun (x : List Bool) : ℕ := (x.takeWhile (· = true)).length

/-- The leading run of `1`s is no longer than the word. -/
lemma tRun_le (x : List Bool) : tRun x ≤ x.length := (List.takeWhile_prefix _).length_le

/-- The letters before the end of the leading run of `1`s are `1`s. -/
lemma getElem?_lt_tRun (x : List Bool) (j : ℕ) (hj : j < tRun x) : x[j]? = some true :=
  takeWhile_true_getElem? x j hj

/-- The letter ending the leading run of `1`s (if any) is not a `1`. -/
lemma getElem?_tRun (x : List Bool) : x[tRun x]? ≠ some true := takeWhile_true_end x

/-- The plain format, read off the leading run: an even run of `1`s, then `0 1`, then a word
without trailing `0`.

**Proof sketch.** (⇒) On `pairEncode 1ⁿ w` the leading run is `1²ⁿ` (`dbl_replicate`), followed
by `0 1 w`. (⇐) Split the word at its leading run of even length `2n` and at the following `0
1`: the prefix is `dbl 1ⁿ`, so the word is `⟨1ⁿ, rest⟩` with `rest` without trailing `0`. -/
lemma validPlain_iff (y : List Bool) :
    ValidPlain y ↔ tRun y % 2 = 0 ∧ y[tRun y]? = some false ∧ y[tRun y + 1]? = some true ∧
      Canon (y.drop (tRun y + 2)) := by
  constructor
  · rintro ⟨n, w, rfl, hw⟩
    have ht : tRun (pairEncode (List.replicate n true) w) = 2 * n := by
      simp only [tRun, pairEncode_eq_dbl, dbl_replicate, List.append_assoc]
      rw [List.takeWhile_append_of_pos (by simp)]
      simp
    rw [ht]
    refine ⟨by omega, ?_, ?_, ?_⟩
    · simp [pairEncode_eq_dbl, dbl_replicate]
    · simp [pairEncode_eq_dbl, dbl_replicate]
    · simp [pairEncode_eq_dbl, dbl_replicate, List.drop_append, hw]
  · rintro ⟨h0, h1, h2, h3⟩
    refine ⟨tRun y / 2, y.drop (tRun y + 2), ?_, h3⟩
    have htake : y.take (tRun y) = List.replicate (tRun y) true := by
      apply List.ext_getElem?
      intro i
      by_cases hi : i < tRun y
      · rw [List.getElem?_take, if_pos hi, getElem?_lt_tRun y i hi]; simp [hi]
      · rw [List.getElem?_take, if_neg hi]; simp [hi]
    have hlen : tRun y + 2 ≤ y.length := by
      by_contra h; rw [List.getElem?_eq_none (by omega)] at h2; simp at h2
    have hsplit : y = y.take (tRun y) ++ [false, true] ++ y.drop (tRun y + 2) := by
      apply List.ext_getElem?
      intro i
      rw [List.getElem?_append, List.getElem?_append]
      by_cases ha : i < tRun y
      · simp [ha, List.length_take, show tRun y ≤ y.length from tRun_le y,
          show i < tRun y + 2 by omega, List.getElem?_eq_getElem (show i < y.length by omega)]
      · by_cases hb : i < tRun y + 2
        · have : i = tRun y ∨ i = tRun y + 1 := by omega
          rcases this with rfl | rfl
          · simp [h1, show tRun y ≤ y.length from tRun_le y]
          · simp [h2, show tRun y ≤ y.length from tRun_le y]
        · simp [hb, show tRun y ≤ y.length from tRun_le y, List.getElem?_drop]
          congr 1; omega
    rw [pairEncode_eq_dbl, dbl_replicate, show 2 * (tRun y / 2) = tRun y by omega, ← htake]
    exact hsplit

/-- The run of `1`s: count parity. -/
def valUAct (r : Fin m) (vU0 vU1 vS : Λ) (par : Bool) (a : Option Bool) : Action m Bool Λ :=
  match a with
  | some true => xAct r 1 0 (if par then vU0 else vU1)
  | some false => if par then rejAct else xAct r 1 0 vS
  | none => rejAct

/-- The `1` of the separator. -/
def valSAct (r : Fin m) (vW0 : Λ) (a : Option Bool) : Action m Bool Λ :=
  match a with
  | some true => xAct r 1 0 vW0
  | _ => rejAct

/-- The final word: remember the last bit; at the end reject a trailing `0`, else rewind. -/
def valWAct (r : Fin m) (vWF vWT rw₁ : Λ) (last : Option Bool) (a : Option Bool) :
    Action m Bool Λ :=
  match a with
  | some b => xAct r 1 0 (if b then vWT else vWF)
  | none => if last = some false then rejAct else xAct r 0 0 rw₁

/-- The input symbol at cell `j + 1` is the `j`-th letter of the input (cell `0` is the left
end marker). -/
lemma inSym_succ (x : List Bool) (j : ℕ) : inSym x (j + 1) = x[j]? := by simp [inSym]

/-- **The rejecting step**: from an input-scanning view at a non-call state whose transition on the
current input symbol is `rejAct`, one step halts with output `0` appended and the register head
where it was.

**Proof sketch.** Rewrite the one-step run with `rrun_one_x` and the transition with `htr`;
`rejAct` writes `false` to the output, moves no head and halts. Compare the components of the
resulting configuration. -/
lemma rrun_one_rej (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (c : Cfg m Bool Λ x)
    (s : Λ) (ip : Fin (x.length + 2)) (r : Fin m) (p : ℤ) (hs : P.call s = none)
    (htr : ∀ w, P.tm.tr s (inSym x ip.val) w = rejAct) :
    (rrun P oracle (xCfg c s ip r p) 1).state = none ∧
      (rrun P oracle (xCfg c s ip r p) 1).output = c.output ++ [false] ∧
      (rrun P oracle (xCfg c s ip r p) 1).workTapePos = Function.update c.workTapePos r p := by
  rw [rrun_one_x P oracle c s ip r p hs, htr]
  simp [rejAct, Action.apply, xCfg]

section ValPlain

variable (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (r : Fin m)
  (vU0 vU1 vS vW0 vWF vWT rw₁ rw₂ next : Λ)
  (hU0 : ∀ a w, P.tm.tr vU0 a w = valUAct r vU0 vU1 vS false a)
  (hU1 : ∀ a w, P.tm.tr vU1 a w = valUAct r vU0 vU1 vS true a)
  (hS : ∀ a w, P.tm.tr vS a w = valSAct r vW0 a)
  (hW0 : ∀ a w, P.tm.tr vW0 a w = valWAct r vWF vWT rw₁ none a)
  (hWF : ∀ a w, P.tm.tr vWF a w = valWAct r vWF vWT rw₁ (some false) a)
  (hWT : ∀ a w, P.tm.tr vWT a w = valWAct r vWF vWT rw₁ (some true) a)
  (h₁ : ∀ a w, P.tm.tr rw₁ a w = xAct r (-1) 0 rw₂)
  (h₂ : ∀ a w, P.tm.tr rw₂ a w = match a with
    | some _ => xAct r (-1) 0 rw₂
    | none => xAct r 1 0 next)
  (cU0 : P.call vU0 = none) (cU1 : P.call vU1 = none) (cS : P.call vS = none)
  (cW0 : P.call vW0 = none) (cWF : P.call vWF = none) (cWT : P.call vWT = none)
  (c₁ : P.call rw₁ = none) (c₂ : P.call rw₂ = none)

/-- The outcome of a fragment run: either it reaches `next` with the input head on position
`1`, or it rejects; on the way only non-call states, the registers' heads unchanged. -/
def FragOK (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (c : Cfg m Bool Λ x) (s₀ : Λ)
    (r : Fin m) (p : ℤ) (good : Prop) (next : Λ) : Prop :=
  (good → ∃ T, rrun P oracle (xCfg c s₀ ⟨1, by omega⟩ r p) T = xCfg c next ⟨1, by omega⟩ r p ∧
      ∀ t < T, ∃ s ip, rrun P oracle (xCfg c s₀ ⟨1, by omega⟩ r p) t = xCfg c s ip r p ∧
        P.call s = none) ∧
  (¬ good → ∃ T, (rrun P oracle (xCfg c s₀ ⟨1, by omega⟩ r p) T).state = none ∧
      (rrun P oracle (xCfg c s₀ ⟨1, by omega⟩ r p) T).output = c.output ++ [false] ∧
      (rrun P oracle (xCfg c s₀ ⟨1, by omega⟩ r p) T).workTapePos =
        Function.update c.workTapePos r p ∧
      ∀ t < T, ∃ s ip, rrun P oracle (xCfg c s₀ ⟨1, by omega⟩ r p) t = xCfg c s ip r p ∧
        P.call s = none)

include hU0 hU1 hS hW0 hWF hWT h₁ h₂ cU0 cU1 cS cW0 cWF cWT c₁ c₂ in
/-- **The plain format check**: it reaches `next` (input head back on position `1`) exactly
on inputs `⟨1ⁿ, w⟩` with `w` free of trailing `0`s, and rejects otherwise.

**Proof sketch.** The run of `1`s is scanned with its parity (`scanR`); then the separator
`0 1`; then the final word with its last bit (`scanR`); finally `rewind_x`. Every failure
rejects in one step. `validPlain_iff` identifies acceptance with the shape. -/
lemma valPlain_run (c : Cfg m Bool Λ x) (p : ℤ) :
    FragOK P oracle c vU0 r p (ValidPlain x) next := by
  set t := tRun x with ht
  have htx : t ≤ x.length := tRun_le x
  -- the run of `1`s
  let st : ℕ → Λ := fun j => if j % 2 = 0 then vU0 else vU1
  have hscan := scanR P oracle c r p st 1 t (by omega) (fun j hj w => by
      rw [show 1 + j = j + 1 by ring, inSym_succ, getElem?_lt_tRun x j hj]
      simp only [st]
      split_ifs with h1 h2 h2
      · omega
      · rw [hU0]; simp [valUAct]
      · rw [hU1]; simp [valUAct]
      · omega)
    (fun j hj => by simp only [st]; split_ifs <;> assumption)
  have hs0 : st 0 = vU0 := rfl
  have hst : ∀ j, P.call (st j) = none := fun j => by simp only [st]; split_ifs <;> assumption
  have hmidU : ∀ j ≤ t, ∃ s ip, rrun P oracle (xCfg c vU0 ⟨1, by omega⟩ r p) j = xCfg c s ip r p ∧
      P.call s = none := fun j hj => ⟨st j, _, by rw [← hs0]; exact hscan j hj, hst j⟩
  have hU : rrun P oracle (xCfg c vU0 ⟨1, by omega⟩ r p) t = xCfg c (st t) ⟨1 + t, by omega⟩ r p :=
    by rw [← hs0]; exact hscan t le_rfl
  have hsym1 : inSym x (1 + t) = x[t]? := by rw [show 1 + t = t + 1 by ring, inSym_succ]
  -- a rejecting continuation
  have rejAt : ∀ (T₀ : ℕ) (s : Λ) (ip : Fin (x.length + 2)), P.call s = none →
      (∀ w, P.tm.tr s (inSym x ip.val) w = rejAct) →
      rrun P oracle (xCfg c vU0 ⟨1, by omega⟩ r p) T₀ = xCfg c s ip r p →
      (∀ t' < T₀, ∃ s ip, rrun P oracle (xCfg c vU0 ⟨1, by omega⟩ r p) t' = xCfg c s ip r p ∧
        P.call s = none) →
      ∃ T, (rrun P oracle (xCfg c vU0 ⟨1, by omega⟩ r p) T).state = none ∧
        (rrun P oracle (xCfg c vU0 ⟨1, by omega⟩ r p) T).output = c.output ++ [false] ∧
        (rrun P oracle (xCfg c vU0 ⟨1, by omega⟩ r p) T).workTapePos =
          Function.update c.workTapePos r p ∧
        ∀ t < T, ∃ s ip, rrun P oracle (xCfg c vU0 ⟨1, by omega⟩ r p) t = xCfg c s ip r p ∧
          P.call s = none := by
    intro T₀ s ip hs htr hrun hmid
    obtain ⟨e1, e2, e3⟩ := rrun_one_rej P oracle c s ip r p hs htr
    refine ⟨T₀ + 1, by rw [rrun_add, hrun]; exact e1, by rw [rrun_add, hrun]; exact e2,
      by rw [rrun_add, hrun]; exact e3, fun t' ht' => ?_⟩
    rcases Nat.lt_or_ge t' T₀ with h | h
    · exact hmid t' h
    · obtain rfl : t' = T₀ := by omega
      exact ⟨s, ip, hrun, hs⟩
  have hvalid := validPlain_iff x
  rw [← ht] at hvalid
  have hnotT := getElem?_tRun x
  rw [← ht] at hnotT
  -- the symbol after the run
  rcases hxt : x[t]? with _ | b
  · -- end of input: reject
    have hbad : ¬ ValidPlain x := by rw [hvalid, hxt]; simp
    refine ⟨fun h => absurd h hbad, fun _ => rejAt t (st t) _ (hst t) (fun w => ?_) hU
      (fun t' ht' => hmidU t' ht'.le)⟩
    rw [hsym1, hxt]
    simp only [st]; split_ifs
    · rw [hU0]; rfl
    · rw [hU1]; rfl
  cases b with
  | true => exact absurd hxt hnotT
  | false =>
  have htlt : t < x.length := by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at hxt; simp at hxt
  by_cases hpar : t % 2 = 0
  swap
  · -- odd run: reject
    have hbad : ¬ ValidPlain x := by rw [hvalid]; omega
    refine ⟨fun h => absurd h hbad, fun _ => rejAt t (st t) _ (hst t) (fun w => ?_) hU
      (fun t' ht' => hmidU t' ht'.le)⟩
    rw [hsym1, hxt]
    simp only [st, hpar, ↓reduceIte]
    rw [hU1]; rfl
  -- even run: the separator
  have hS1 : rrun P oracle (xCfg c (st t) ⟨1 + t, by omega⟩ r p) 1 =
      xCfg c vS ⟨2 + t, by omega⟩ r p := by
    rw [rrun_one_x P oracle c _ _ r p (hst t)]
    simp only [st, hpar, ↓reduceIte]
    rw [hU0, hsym1, hxt]
    simp only [valUAct, Bool.false_eq_true, ↓reduceIte]
    rw [apply_xAct]
    congr 1
    · exact Fin.ext (by rw [moveInputPos_pos_val _ (by simp; omega)]; simp; omega)
    · simp
  have hsym2 : inSym x (2 + t) = x[t + 1]? := by rw [show 2 + t = (t + 1) + 1 by ring, inSym_succ]
  have hmidS : ∀ j ≤ t + 1, ∃ s ip, rrun P oracle (xCfg c vU0 ⟨1, by omega⟩ r p) j =
      xCfg c s ip r p ∧ P.call s = none := by
    intro j hj
    rcases Nat.lt_or_ge j (t + 1) with h | h
    · exact hmidU j (by omega)
    · obtain rfl : j = t + 1 := by omega
      exact ⟨vS, _, by rw [rrun_add, hU, hS1], cS⟩
  have hSrun : rrun P oracle (xCfg c vU0 ⟨1, by omega⟩ r p) (t + 1) =
      xCfg c vS ⟨2 + t, by omega⟩ r p := by rw [rrun_add, hU, hS1]
  rcases hxt1 : x[t + 1]? with _ | b'
  · have hbad : ¬ ValidPlain x := by rw [hvalid, hxt1]; simp
    refine ⟨fun h => absurd h hbad, fun _ => rejAt (t + 1) vS _ cS (fun w => ?_) hSrun
      (fun t' ht' => hmidS t' ht'.le)⟩
    rw [hsym2, hxt1, hS]; rfl
  cases b' with
  | false =>
    have hbad : ¬ ValidPlain x := by rw [hvalid, hxt1]; simp
    refine ⟨fun h => absurd h hbad, fun _ => rejAt (t + 1) vS _ cS (fun w => ?_) hSrun
      (fun t' ht' => hmidS t' ht'.le)⟩
    rw [hsym2, hxt1, hS]; rfl
  | true =>
  have htlt1 : t + 1 < x.length := by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at hxt1; simp at hxt1
  have hS2 : rrun P oracle (xCfg c vS ⟨2 + t, by omega⟩ r p) 1 =
      xCfg c vW0 ⟨3 + t, by omega⟩ r p := by
    have hlen : t + 2 ≤ x.length := by
      by_contra h; rw [List.getElem?_eq_none (by omega)] at hxt1; simp at hxt1
    rw [rrun_one_x P oracle c _ _ r p cS, hS, hsym2, hxt1]
    simp only [valSAct]
    rw [apply_xAct]
    congr 1
    · exact Fin.ext (by rw [moveInputPos_pos_val _ (by simp; omega)]; simp; omega)
    · simp
  -- the final word
  set w := x.drop (t + 2) with hw
  have hwlen : w.length + t + 2 = x.length := by
    have : t + 2 ≤ x.length := by
      by_contra h; rw [List.getElem?_eq_none (by omega)] at hxt1; simp at hxt1
    simp [hw]; omega
  let st' : ℕ → Λ := fun j => match (w.take j).getLast? with
    | none => vW0
    | some false => vWF
    | some true => vWT
  have htake_last : ∀ (j : ℕ) (hj : j < w.length), (w.take (j + 1)).getLast? = some w[j] := by
    intro j hj
    have h : List.take (j + 1) w = List.take j w ++ [w[j]] := by
      rw [List.take_succ, List.getElem?_eq_getElem hj]; rfl
    rw [h, List.getLast?_append]
    simp
  have hst'c : ∀ j, P.call (st' j) = none := by
    intro j; simp only [st']; split <;> assumption
  have hscanW := scanR P oracle c r p st' (3 + t) w.length (by omega) (fun j hj ww => by
      rw [show 3 + t + j = (t + 2 + j) + 1 by ring, inSym_succ]
      have hx : x[t + 2 + j]? = some w[j] := by
        rw [← List.getElem?_eq_getElem hj, hw, List.getElem?_drop]
      rw [hx]
      have e : st' (j + 1) = if w[j] then vWT else vWF := by
        simp only [st', htake_last j hj]; cases w[j] <;> rfl
      rw [e]
      simp only [st']
      split
      · rw [hW0]; rfl
      · rw [hWF]; rfl
      · rw [hWT]; rfl)
    (fun j hj => hst'c j)
  have hs'0 : st' 0 = vW0 := by simp [st']
  have hWrun : rrun P oracle (xCfg c vU0 ⟨1, by omega⟩ r p) (t + 1 + 1 + w.length) =
      xCfg c (st' w.length) ⟨3 + t + w.length, by omega⟩ r p := by
    rw [rrun_add, rrun_add, hSrun, hS2, ← hs'0]
    exact hscanW w.length le_rfl
  have hmidW : ∀ j ≤ t + 1 + 1 + w.length, ∃ s ip, rrun P oracle (xCfg c vU0 ⟨1, by omega⟩ r p) j =
      xCfg c s ip r p ∧ P.call s = none := by
    intro j hj
    rcases Nat.lt_or_ge j (t + 1 + 1) with h | h
    · exact hmidS j (by omega)
    · obtain ⟨j', rfl⟩ : ∃ j', j = t + 1 + 1 + j' := ⟨j - (t + 2), by omega⟩
      refine ⟨st' j', ⟨3 + t + j', by omega⟩, ?_, hst'c j'⟩
      rw [rrun_add, rrun_add, hSrun, hS2, ← hs'0]
      exact hscanW j' (by omega)
  have hlast : (w.take w.length).getLast? = w.getLast? := by rw [List.take_length]
  have hendSym : inSym x (3 + t + w.length) = none := by
    rw [show 3 + t + w.length = x.length + 1 by omega, inSym_succ]; simp
  by_cases hcan : w.getLast? = some false
  · -- trailing zero: reject
    have hbad : ¬ ValidPlain x := by
      rw [hvalid]; rintro ⟨-, -, -, h3⟩
      have hne : w ≠ [] := by rintro h; rw [h] at hcan; simp at hcan
      have := h3 hne
      rw [List.getLast?_eq_getLast hne] at hcan
      simp [this] at hcan
    refine ⟨fun h => absurd h hbad, fun _ => rejAt _ (st' w.length) _ (hst'c _) (fun ww => ?_)
      hWrun (fun t' ht' => hmidW t' ht'.le)⟩
    rw [hendSym]
    simp only [st', hlast, hcan]
    rw [hWF]; simp [valWAct]
  · have hgood : ValidPlain x := by
      rw [hvalid]
      refine ⟨hpar, hxt, hxt1, fun hne => ?_⟩
      have := List.getLast?_eq_getLast hne
      cases h : w.getLast hne
      · rw [h] at this; exact absurd this hcan
      · rfl
    refine ⟨fun _ => ?_, fun h => absurd hgood h⟩
    have hE : rrun P oracle (xCfg c (st' w.length) ⟨3 + t + w.length, by omega⟩ r p) 1 =
        xCfg c rw₁ ⟨3 + t + w.length, by omega⟩ r p := by
      rw [rrun_one_x P oracle c _ _ r p (hst'c _), hendSym]
      have e : ∀ ww, P.tm.tr (st' w.length) none ww = xAct r 0 0 rw₁ := by
        intro ww
        simp only [st', hlast]
        split
        · rw [hW0]; rfl
        · rename_i h; rw [h] at hcan; exact absurd rfl hcan
        · rw [hWT]; rfl
      rw [e, apply_xAct]
      simp
    obtain ⟨T₄, hr4, hm4⟩ := rewind_x P oracle c r p rw₁ rw₂ next h₁ h₂ c₁ c₂
      ⟨3 + t + w.length, by omega⟩
    refine ⟨t + 1 + 1 + w.length + 1 + T₄, by rw [rrun_add, rrun_add, hWrun, hE, hr4],
      fun t' ht' => ?_⟩
    rcases Nat.lt_or_ge t' (t + 1 + 1 + w.length + 1) with h | h
    · rcases Nat.lt_or_ge t' (t + 1 + 1 + w.length) with h' | h'
      · exact hmidW t' h'.le
      · obtain rfl : t' = t + 1 + 1 + w.length := by omega
        exact hmidW _ le_rfl
    · obtain ⟨t'', rfl⟩ : ∃ t'', t' = t + 1 + 1 + w.length + 1 + t'' :=
        ⟨t' - (t + 1 + 1 + w.length + 1), by omega⟩
      rw [rrun_add, rrun_add, hWrun, hE]
      exact hm4 t'' (by omega)

end ValPlain

end Complexity.LogProg

```


## ===== TCSlib/Complexity/SpaceComplexity/Machines/Parse.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.ParsePlain

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Program fragments reading the input

Logspace programs cannot copy their input into work space; they read it in place. This file
provides the input-reading fragments of register-tape programs whose inputs have the shape
`⟨1ⁿ, w⟩` (`Turing.pairEncode (1ⁿ) w`, i.e. `1²ⁿ 0 1 w`) or `⟨1ⁿ, ⟨u, w⟩⟩`:

* the *format checks* `valPlain`/`valPair` accept exactly the inputs of that shape whose
  binary components have no trailing `0` (the words `Nat.bits i`), and otherwise reject
  (write `0` and halt);
* the *comparisons* test whether a register's counter equals the index written on the input,
  walking the register and the input in lockstep — no copying.

The input shapes, input-scanning configurations and the plain format check are in
`TCSlib.Complexity.SpaceComplexity.Machines.ParsePlain`, which this file re-exports; this file
has the comparison of a register with the index of a plain input (`jeqPlain_run`).

## Main definitions

* `Complexity.LogProg.ValidPlain`, `Complexity.LogProg.ValidPair` — the input shapes.
* `Complexity.LogProg.xCfg` — a configuration with the input head and one register head
  moved.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1: logspace machines read their input in place.)
-/

namespace Complexity.LogProg

open Turing

variable {m d : ℕ} {Λ : Type} {x : List Bool}

/-! ## Comparing a register with the index on the input -/

/-- A word without trailing `0` is the binary word of its value. -/
lemma canon_eq_bits (w : List Bool) (h : Canon w) : w = Nat.bits (bitsVal w) := by
  induction w with
  | nil => simp [bitsVal, Nat.zero_bits]
  | cons b w ih =>
    have hw := ih (canon_tail h)
    simp only [bitsVal]
    rw [show b.toNat + 2 * bitsVal w = 2 * bitsVal w + b.toNat by ring,
      bits_two_mul_add _ _ (fun h0 => ?_), ← hw]
    -- `w = []`: then `b` is the last bit
    have : w = [] := by
      rw [hw, h0]; simp [Nat.zero_bits]
    subst this
    simpa using h (by simp)

/-- The return walk of a register in an input fragment: left over the word, then onto cell
`0`.

**Proof sketch.** Induction on `n = q + 1`: on a letter of the register word the register head
moves left; at the left blank it moves right onto cell `0` and the state becomes `nx`. The input
head never moves. -/
lemma regBack_x (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (c : Cfg m Bool Λ x)
    (r : Fin m) (w : List Bool) (hw : c.workTapes r = FinTM.bufferTape w) (s₀ nx : Λ)
    (htr : ∀ a ww, P.tm.tr s₀ a ww = match ww r with
      | some _ => xAct r 0 (-1) s₀
      | none => xAct r 0 1 nx)
    (hc : P.call s₀ = none) (ip : Fin (x.length + 2)) :
    ∀ (n : ℕ) (q : ℤ), q + 1 = n → q < w.length →
      rrun P oracle (xCfg c s₀ ip r q) (n + 1) = xCfg c nx ip r 0 ∧
      ∀ t < n + 1, ∃ q', rrun P oracle (xCfg c s₀ ip r q) t = xCfg c s₀ ip r q' ∧
        -1 ≤ q' ∧ q' ≤ q := by
  intro n
  induction n with
  | zero =>
    intro q hq _
    refine ⟨?_, fun t ht => ?_⟩
    swap
    · obtain rfl : t = 0 := by omega
      exact ⟨q, rfl, by omega, le_rfl⟩
    rw [rrun_one_x P oracle c s₀ ip r q hc, htr, xCfg_read, hw]
    have hrd : FinTM.bufferTape w q = none := by rw [show q = -1 by omega]; simp
    rw [hrd]
    simp only
    rw [apply_xAct]
    congr 1; simp
  | succ n ih =>
    intro q hq hqw
    obtain ⟨j, hj⟩ : ∃ j : ℕ, q = j := ⟨q.toNat, by omega⟩
    have hjw : j < w.length := by omega
    have hstep : rrun P oracle (xCfg c s₀ ip r q) 1 = xCfg c s₀ ip r (q - 1) := by
      rw [rrun_one_x P oracle c s₀ ip r q hc, htr, xCfg_read, hw]
      have hrd : FinTM.bufferTape w q = some w[j] := by
        rw [hj]; simp [List.getElem?_eq_getElem hjw]
      rw [hrd]
      simp only
      rw [apply_xAct]
      simp [sub_eq_add_neg]
    obtain ⟨ihr, ihm⟩ := ih (q - 1) (by omega) (by omega)
    refine ⟨by rw [rrun_succ_left, hstep, ihr], fun t ht => ?_⟩
    rcases Nat.lt_or_ge t 1 with h | h
    · obtain rfl : t = 0 := by omega
      exact ⟨q, rfl, by omega, le_rfl⟩
    · obtain ⟨t', rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
      rw [rrun_add, hstep]
      obtain ⟨q', hq', h1, h2⟩ := ihm t' (by omega)
      exact ⟨q', hq', h1, by omega⟩

/-- Skip the run of `1`s and the separator `0`. -/
def skipAct (r : Fin m) (jK jK2 : Λ) (a : Option Bool) : Action m Bool Λ :=
  match a with
  | some true => xAct r 1 0 jK
  | _ => xAct r 1 0 jK2

/-- Compare the input symbol `a` with the register symbol `c`. -/
def cmpAct (r : Fin m) (jC : Λ) (jRB : Bool → Λ) (a c : Option Bool) : Action m Bool Λ :=
  if a = c then (if a = none then xAct r 0 (-1) (jRB true) else xAct r 1 1 jC)
  else xAct r 0 (-1) (jRB false)

/-- The register return of a comparison. -/
def backAct (r : Fin m) (s₀ nx : Λ) (c : Option Bool) : Action m Bool Λ :=
  match c with
  | some _ => xAct r 0 (-1) s₀
  | none => xAct r 0 1 nx

/-- The input rewind of a comparison: scan. -/
def rewAct (r : Fin m) (s₀ nx : Λ) (a : Option Bool) : Action m Bool Λ :=
  match a with
  | some _ => xAct r (-1) 0 s₀
  | none => xAct r 1 0 nx

section JeqPlain

variable (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (r : Fin m)
  (jK jK2 jC : Λ) (jRB jI1 jI2 : Bool → Λ) (yes no : Λ)
  (hK : ∀ a w, P.tm.tr jK a w = skipAct r jK jK2 a)
  (hK2 : ∀ a w, P.tm.tr jK2 a w = xAct r 1 0 jC)
  (hC : ∀ a w, P.tm.tr jC a w = cmpAct r jC jRB a (w r))
  (hRB : ∀ b a w, P.tm.tr (jRB b) a w = backAct r (jRB b) (jI1 b) (w r))
  (hI1 : ∀ b a w, P.tm.tr (jI1 b) a w = xAct r (-1) 0 (jI2 b))
  (hI2 : ∀ b a w, P.tm.tr (jI2 b) a w = rewAct r (jI2 b) (if b then yes else no) a)
  (cK : P.call jK = none) (cK2 : P.call jK2 = none) (cC : P.call jC = none)
  (cRB : ∀ b, P.call (jRB b) = none) (cI1 : ∀ b, P.call (jI1 b) = none)
  (cI2 : ∀ b, P.call (jI2 b) = none)

include hRB hI1 hI2 cRB cI1 cI2 in
/-- **The return after a comparison** that decided `b` with the register head at `k - 1`: the
register head walks back to cell `0` and the input head to position `1`, ending in `yes` or `no`
according to `b`.

**Proof sketch.** Walk the register head back (`regBack_x`), then rewind the input head
(`rewind_x`), and concatenate the runs (`rrun_add`). The register head stays in `[-1, k - 1]`
during the first walk and at `0` during the second. -/
lemma cmpReturn (c : Cfg m Bool Λ x) (wr : List Bool) (hw : c.workTapes r = FinTM.bufferTape wr)
    (b : Bool) (ip : Fin (x.length + 2)) (k : ℤ) (hk0 : 0 ≤ k) (hk : k ≤ wr.length) :
    ∃ T, rrun P oracle (xCfg c (jRB b) ip r (k - 1)) T =
        xCfg c (if b then yes else no) ⟨1, by omega⟩ r 0 ∧
      ∀ t < T, ∃ s ip' q, rrun P oracle (xCfg c (jRB b) ip r (k - 1)) t = xCfg c s ip' r q ∧
        P.call s = none ∧ -1 ≤ q ∧ q ≤ wr.length := by
  obtain ⟨h1, hm1⟩ := regBack_x P oracle c r wr hw (jRB b) (jI1 b)
    (fun a ww => by rw [hRB]; simp only [backAct]) (cRB b) ip k.toNat (k - 1)
    (by omega) (by omega)
  have hrw := rewind_x P oracle c r 0 (jI1 b) (jI2 b) (if b then yes else no) (hI1 b)
    (fun a ww => by rw [hI2]; simp only [rewAct]; cases a <;> rfl) (cI1 b) (cI2 b) ip
  obtain ⟨T₂, h2, hm2⟩ := hrw
  refine ⟨k.toNat + 1 + T₂, by rw [rrun_add, h1, h2], fun t ht => ?_⟩
  rcases Nat.lt_or_ge t (k.toNat + 1) with h | h
  · obtain ⟨q, hq, hq1, hq2⟩ := hm1 t h
    exact ⟨jRB b, ip, q, hq, cRB b, hq1, by omega⟩
  · obtain ⟨t', rfl⟩ : ∃ t', t = k.toNat + 1 + t' := ⟨t - (k.toNat + 1), by omega⟩
    rw [rrun_add, h1]
    obtain ⟨s', ip', hs', hc'⟩ := hm2 t' (by omega)
    exact ⟨s', ip', 0, hs', hc', by omega, by omega⟩

include hC cC in
/-- The comparison walk of the plain mode: the input word starting at input position `q₀`
runs to the end of the input.

**Proof sketch.** Induction on `u₁`. Equal letters on the input and the register move both heads
right, extending the common prefix. A mismatch, or one word ending before the other, branches to
`jRB false`; both ending together branches to `jRB true`. The register head stays within `[0,
|wr|]`. -/
lemma cmpPlain_run (c : Cfg m Bool Λ x) (wr wi : List Bool)
    (hw : c.workTapes r = FinTM.bufferTape wr) (q₀ : ℕ)
    (hin : ∀ k, inSym x (q₀ + k) = wi[k]?) (hq : q₀ + wi.length ≤ x.length + 1) :
    ∀ (u₁ u₂ pre : List Bool) (ip : Fin (x.length + 2)), wi = pre ++ u₁ → wr = pre ++ u₂ →
      ip.val = q₀ + pre.length →
      ∃ (T k : ℕ) (ipk : Fin (x.length + 2)), ipk.val = q₀ + k ∧ pre.length ≤ k ∧
        k ≤ wr.length ∧ k ≤ wi.length ∧
        rrun P oracle (xCfg c jC ip r pre.length) T =
          xCfg c (jRB (decide (wi = wr))) ipk r ((k : ℤ) - 1) ∧
        ∀ t < T, ∃ ip' q, rrun P oracle (xCfg c jC ip r pre.length) t = xCfg c jC ip' r q ∧
          0 ≤ q ∧ q ≤ wr.length := by
  intro u₁
  induction u₁ with
  | nil =>
    intro u₂ pre ip e1 e2 hip
    have ha : inSym x ip.val = none := by rw [hip, hin, e1]; simp
    cases u₂ with
    | nil =>
      have hc : c.workTapes r pre.length = none := by rw [hw, e2]; simp
      refine ⟨1, pre.length, ip, hip, le_rfl, by rw [e2]; simp, by rw [e1]; simp, ?_, ?_⟩
      · rw [rrun_one_x P oracle c jC ip r _ cC, hC, xCfg_read, hc, ha]
        simp only [cmpAct, ↓reduceIte]
        rw [apply_xAct]
        have : decide (wi = wr) = true := by simp [e1, e2]
        rw [this]; simp [sub_eq_add_neg]
      · intro t ht
        obtain rfl : t = 0 := by omega
        exact ⟨ip, _, rfl, by omega, by rw [e2]; simp⟩
    | cons b u₂' =>
      have hc : c.workTapes r pre.length = some b := by rw [hw, e2]; simp
      refine ⟨1, pre.length, ip, hip, le_rfl, by rw [e2]; simp, by rw [e1]; simp, ?_, ?_⟩
      · rw [rrun_one_x P oracle c jC ip r _ cC, hC, xCfg_read, hc, ha]
        simp only [cmpAct, reduceCtorEq, ↓reduceIte]
        rw [apply_xAct]
        have : decide (wi = wr) = false := by simp [e1, e2]
        rw [this]; simp [sub_eq_add_neg]
      · intro t ht
        obtain rfl : t = 0 := by omega
        exact ⟨ip, _, rfl, by omega, by rw [e2]; simp; omega⟩
  | cons a u₁' ih =>
    intro u₂ pre ip e1 e2 hip
    have ha : inSym x ip.val = some a := by rw [hip, hin, e1]; simp
    cases u₂ with
    | nil =>
      have hc : c.workTapes r pre.length = none := by rw [hw, e2]; simp
      refine ⟨1, pre.length, ip, hip, le_rfl, by rw [e2]; simp, by rw [e1]; simp, ?_, ?_⟩
      · rw [rrun_one_x P oracle c jC ip r _ cC, hC, xCfg_read, hc, ha]
        simp only [cmpAct, reduceCtorEq, ↓reduceIte]
        rw [apply_xAct]
        have : decide (wi = wr) = false := by simp [e1, e2]
        rw [this]; simp [sub_eq_add_neg]
      · intro t ht
        obtain rfl : t = 0 := by omega
        exact ⟨ip, _, rfl, by omega, by rw [e2]; simp⟩
    | cons b u₂' =>
      have hc : c.workTapes r pre.length = some b := by rw [hw, e2]; simp
      by_cases hab : a = b
      · subst hab
        have hlen : q₀ + (pre.length + 1) ≤ x.length + 1 := by
          have := congrArg List.length e1; simp at this; omega
        have hstep : rrun P oracle (xCfg c jC ip r pre.length) 1 =
            xCfg c jC ⟨q₀ + (pre ++ [a]).length, by simp; omega⟩ r (pre ++ [a]).length := by
          rw [rrun_one_x P oracle c jC ip r _ cC, hC, xCfg_read, hc, ha]
          simp only [cmpAct, reduceCtorEq, ↓reduceIte]
          rw [apply_xAct]
          congr 1
          · exact Fin.ext (by rw [moveInputPos_pos_val _ (by omega)]; simp; omega)
          · simp
        obtain ⟨T, k, ipk, hipk, hk1, hk2, hk3, hr, hm⟩ := ih u₂' (pre ++ [a])
          ⟨q₀ + (pre ++ [a]).length, by simp; omega⟩ (by rw [e1]; simp) (by rw [e2]; simp) rfl
        refine ⟨1 + T, k, ipk, hipk, by simp at hk1; omega, hk2, hk3,
          by rw [rrun_add, hstep, hr], fun t ht => ?_⟩
        rcases Nat.lt_or_ge t 1 with h | h
        · obtain rfl : t = 0 := by omega
          exact ⟨ip, _, rfl, by omega, by rw [e2]; simp; omega⟩
        · obtain ⟨t', rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
          rw [rrun_add, hstep]
          exact hm t' (by omega)
      · refine ⟨1, pre.length, ip, hip, le_rfl, by rw [e2]; simp, by rw [e1]; simp, ?_, ?_⟩
        · rw [rrun_one_x P oracle c jC ip r _ cC, hC, xCfg_read, hc, ha]
          have hab' : (some a : Option Bool) ≠ some b := by simpa using hab
          simp only [cmpAct, hab', ↓reduceIte]
          rw [apply_xAct]
          have : decide (wi = wr) = false := by
            simp [e1, e2]; intro h; exact absurd h hab
          rw [this]; simp [sub_eq_add_neg]
        · intro t ht
          obtain rfl : t = 0 := by omega
          exact ⟨ip, _, rfl, by omega, by rw [e2]; simp; omega⟩

include hK hK2 hC hRB hI1 hI2 cK cK2 cC cRB cI1 cI2 in
/-- **Comparing a register with the index of a plain input**: on the input `⟨1ⁿ, w⟩`, with
`Nat.bits a` on register `r` (head on cell `0`), the fragment reaches `yes` if `w = Nat.bits a`
and `no` otherwise, input head and register head back home, the register head in
`[-1, |Nat.bits a|]` throughout.

**Proof sketch.** Skip the prefix `1²ⁿ 0 1` on the input (`skipPrefix_run`), compare `w` with
the register in lockstep (`cmpPlain_run`), then walk the register head back to cell `0`
(`regBack_x`) and rewind the input head (`rewind_x`). The outcome label is `yes` or `no`
according to `w = bits a`. -/
lemma jeqPlain_run (c : Cfg m Bool Λ x) (n : ℕ) (w : List Bool)
    (hx : x = pairEncode (List.replicate n true) w) (a : ℕ)
    (hreg : c.workTapes r = FinTM.bufferTape (Nat.bits a)) :
    ∃ T, rrun P oracle (xCfg c jK ⟨1, by omega⟩ r 0) T =
        xCfg c (if w = Nat.bits a then yes else no) ⟨1, by omega⟩ r 0 ∧
      ∀ t < T, ∃ s ip q, rrun P oracle (xCfg c jK ⟨1, by omega⟩ r 0) t = xCfg c s ip r q ∧
        P.call s = none ∧ -1 ≤ q ∧ q ≤ (Nat.bits a).length := by
  have hxlen : x.length = 2 * n + 2 + w.length := by
    rw [hx]; simp [pairEncode_eq_dbl, dbl_replicate]; omega
  have hxg : ∀ k, x[k]? = if k < 2 * n then some true else if k = 2 * n then some false
      else if k = 2 * n + 1 then some true else w[k - (2 * n + 2)]? := by
    intro k
    rw [hx, pairEncode_eq_dbl, dbl_replicate, List.append_assoc]
    by_cases h1 : k < 2 * n
    · rw [List.getElem?_append_left (by simp; omega)]; simp [h1]
    · rw [List.getElem?_append_right (by simp; omega)]
      simp only [List.length_replicate]
      obtain ⟨j, rfl⟩ : ∃ j, k = 2 * n + j := ⟨k - 2 * n, by omega⟩
      simp only [Nat.add_sub_cancel_left, h1, ↓reduceIte]
      rcases j with _ | _ | j
      · simp
      · simp
      · simp only [List.cons_append, List.nil_append, List.getElem?_cons_succ]
        rw [if_neg (by omega), if_neg (by omega)]
        congr 1; omega
  -- the run of `1`s
  have hscan := scanR P oracle c r 0 (fun _ => jK) 1 (2 * n) (by omega) (fun j hj ww => by
      rw [show 1 + j = j + 1 by ring, inSym_succ, hxg, if_pos hj, hK]; rfl)
    (fun j hj => cK)
  have h1 := hscan (2 * n) le_rfl
  have hs1 : rrun P oracle (xCfg c jK ⟨1 + 2 * n, by omega⟩ r 0) 1 =
      xCfg c jK2 ⟨2 + 2 * n, by omega⟩ r 0 := by
    rw [rrun_one_x P oracle c jK _ r 0 cK, hK]
    rw [show (⟨1 + 2 * n, _⟩ : Fin (x.length + 2)).val = 2 * n + 1 from by simp; ring, inSym_succ,
      hxg, if_neg (by omega), if_pos rfl]
    simp only [skipAct]
    rw [apply_xAct]
    congr 1
    exact Fin.ext (by rw [moveInputPos_pos_val _ (by simp; omega)]; simp; omega)
  have hs2 : rrun P oracle (xCfg c jK2 ⟨2 + 2 * n, by omega⟩ r 0) 1 =
      xCfg c jC ⟨3 + 2 * n, by omega⟩ r 0 := by
    rw [rrun_one_x P oracle c jK2 _ r 0 cK2, hK2, apply_xAct]
    congr 1
    exact Fin.ext (by rw [moveInputPos_pos_val _ (by simp; omega)]; simp; omega)
  have hin : ∀ k, inSym x (3 + 2 * n + k) = w[k]? := by
    intro k
    rw [show 3 + 2 * n + k = (2 * n + 2 + k) + 1 by ring, inSym_succ, hxg,
      if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    congr 1; omega
  obtain ⟨T₃, k, ipk, hipk, -, hk2, hk3, h3, hm3⟩ := cmpPlain_run P oracle r jC jRB hC cC c
    (Nat.bits a) w hreg (3 + 2 * n) hin (by omega) w (Nat.bits a) [] ⟨3 + 2 * n, by omega⟩
    rfl rfl (by simp)
  obtain ⟨T₄, h4, hm4⟩ := cmpReturn P oracle r jRB jI1 jI2 yes no hRB hI1 hI2 cRB cI1 cI2 c
    (Nat.bits a) hreg (decide (w = Nat.bits a)) ipk k (by omega) (by omega)
  have hend : (if decide (w = Nat.bits a) = true then yes else no) =
      (if w = Nat.bits a then yes else no) := by simp
  rw [hend] at h4
  have hrun : rrun P oracle (xCfg c jK ⟨1, by omega⟩ r 0) (2 * n + 1 + 1) =
      xCfg c jC ⟨3 + 2 * n, by omega⟩ r 0 := by
    rw [rrun_add, rrun_add, h1, hs1, hs2]
  refine ⟨2 * n + 1 + 1 + T₃ + T₄, ?_, fun t ht => ?_⟩
  · simp only [List.length_nil, Nat.cast_zero] at h3
    rw [rrun_add, rrun_add, hrun, h3, h4]
  · simp only [List.length_nil, Nat.cast_zero] at h3 hm3
    rcases Nat.lt_or_ge t (2 * n + 1 + 1) with h | h
    · rcases Nat.lt_or_ge t (2 * n) with h' | h'
      · rw [hscan t h'.le]
        exact ⟨jK, _, 0, rfl, cK, by omega, by omega⟩
      · rcases Nat.lt_or_ge t (2 * n + 1) with h'' | h''
        · obtain rfl : t = 2 * n := by omega
          exact ⟨jK, _, 0, by rw [h1], cK, by omega, by omega⟩
        · obtain rfl : t = 2 * n + 1 := by omega
          exact ⟨jK2, _, 0, by rw [rrun_add, h1, hs1], cK2, by omega, by omega⟩
    · rcases Nat.lt_or_ge t (2 * n + 1 + 1 + T₃) with h' | h'
      · obtain ⟨t', rfl⟩ : ∃ t', t = 2 * n + 1 + 1 + t' := ⟨t - (2 * n + 2), by omega⟩
        rw [rrun_add, hrun]
        obtain ⟨ip', q, hq, hq1, hq2⟩ := hm3 t' (by omega)
        exact ⟨jC, ip', q, hq, cC, by omega, hq2⟩
      · obtain ⟨t', rfl⟩ : ∃ t', t = 2 * n + 1 + 1 + T₃ + t' :=
          ⟨t - (2 * n + 2 + T₃), by omega⟩
        rw [rrun_add, rrun_add, hrun, h3]
        obtain ⟨s', ip', q, hq, hs', hq1, hq2⟩ := hm4 t' (by omega)
        exact ⟨s', ip', q, hq, hs', hq1, hq2⟩

end JeqPlain

end Complexity.LogProg

```


## ===== TCSlib/Complexity/SpaceComplexity/Machines/Parse2.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.Parse

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Format check of inputs `⟨1ⁿ, ⟨u, w⟩⟩`

The pair-format companion of `TCSlib.Complexity.SpaceComplexity.Machines.Parse`: the format
check of inputs `⟨1ⁿ, ⟨u, w⟩⟩`. The comparisons of a register with `u` and `w` are in
`TCSlib.Complexity.SpaceComplexity.Machines.ParseCmp`.

## Main definitions

* `Complexity.LogProg.scanPairs` — the pair scan of the format check, as a function.

## Main results

* `Complexity.LogProg.valPair_run` — the pair format check.

File size: about 650 lines, over the 600-line target. The pair format check is a single
fragment whose phases share their transition hypotheses, and the comparisons on pair inputs
are already split off into `TCSlib.Complexity.SpaceComplexity.Machines.ParseCmp`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.)
-/

namespace Complexity.LogProg

open Turing

variable {m d : ℕ} {Λ : Type} {x : List Bool}

/-! ## The pair scan as a function -/

/-- Scan aligned pairs `bb` until the separator `01`, remembering the last bit; succeed with
the rest of the word if the separator comes and the last bit was not `0`. -/
def scanPairs : Option Bool → List Bool → Option (List Bool)
  | last, false :: true :: rest => if last = some false then none else some rest
  | _, false :: false :: rest => scanPairs (some false) rest
  | _, true :: true :: rest => scanPairs (some true) rest
  | _, _ => none

/-- Prepending a letter does not change the last letter of a nonempty word. -/
lemma getLast?_cons_of {b v : Bool} {u : List Bool} (h : u.getLast? = some v) :
    (b :: u).getLast? = some v := by
  cases u with
  | nil => simp at h
  | cons c u => rw [List.getLast?_cons_cons]; exact h

/-- The pair scan from state `last` succeeds with rest `w` exactly when the word is `dbl u`,
the separator `01`, then `w`, and the last letter of `u` (or `last` if `u` is empty) is not
`0`.

**Proof sketch.** Induction on `z` following the definition of `scanPairs`. On `0 1` the scan
stops with `u = []`. On `b b` it continues with `b` remembered, and the decomposition of the
rest extends `u` by `b` (`getLast?_cons_of`). Any other start fails on both sides. -/
lemma scanPairs_iff (last : Option Bool) (z w : List Bool) :
    scanPairs last z = some w ↔
      ∃ u, z = dbl u ++ [false, true] ++ w ∧ (u.getLast? <|> last) ≠ some false := by
  constructor
  · intro h
    induction z using List.twoStepInduction generalizing last with
    | nil => simp [scanPairs] at h
    | singleton b => cases b <;> simp [scanPairs] at h
    | cons_cons b b' rest ih _ =>
      cases b <;> cases b' <;> simp only [scanPairs] at h
      · obtain ⟨u, rfl, hu⟩ := ih (some false) h
        refine ⟨false :: u, by simp, ?_⟩
        cases hl : u.getLast? with
        | none => simp_all
        | some v => rw [getLast?_cons_of hl]; simp_all
      · split_ifs at h with hl
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨[], by simp, by simpa using hl⟩
      · simp at h
      · obtain ⟨u, rfl, hu⟩ := ih (some true) h
        refine ⟨true :: u, by simp, ?_⟩
        cases hl : u.getLast? with
        | none => simp_all
        | some v => rw [getLast?_cons_of hl]; simp_all
  · rintro ⟨u, rfl, hu⟩
    induction u generalizing last with
    | nil => simp only [dbl_nil, List.nil_append, List.cons_append, scanPairs]; simpa using hu
    | cons b u ih =>
      cases b <;> simp only [dbl_cons, List.cons_append, scanPairs] <;> apply ih <;>
        (cases hl : u.getLast? with
          | none => simp_all
          | some v => rw [getLast?_cons_of hl] at hu; simp_all)

/-! ## Machine phases of the format checks -/

/-- A rejected run: halted with `0` appended, the register head of `r` at `p`, through non-call
states of shape `xCfg`. -/
def Rejects (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (c₀ c : Cfg m Bool Λ x)
    (r : Fin m) (p : ℤ) : Prop :=
  ∃ T, (rrun P oracle c₀ T).state = none ∧ (rrun P oracle c₀ T).output = c.output ++ [false] ∧
    (rrun P oracle c₀ T).workTapePos = Function.update c.workTapePos r p ∧
    ∀ t < T, ∃ s ip, rrun P oracle c₀ t = xCfg c s ip r p ∧ P.call s = none

/-- A run reaching a configuration, through non-call states of shape `xCfg`. -/
def Reaches (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (c₀ c₁ c : Cfg m Bool Λ x)
    (r : Fin m) (p : ℤ) : Prop :=
  ∃ T, rrun P oracle c₀ T = c₁ ∧
    ∀ t < T, ∃ s ip, rrun P oracle c₀ t = xCfg c s ip r p ∧ P.call s = none

section Phases

variable (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (r : Fin m)

/-- Prepend a step to a reaching run. -/
lemma Reaches.step {c₀ c₁ c₂ c : Cfg m Bool Λ x} {p : ℤ} (s : Λ) (ip : Fin (x.length + 2))
    (h₀ : c₀ = xCfg c s ip r p) (hs : P.call s = none) (h1 : rrun P oracle c₀ 1 = c₁)
    (h : Reaches P oracle c₁ c₂ c r p) : Reaches P oracle c₀ c₂ c r p := by
  obtain ⟨T, hT, hm⟩ := h
  refine ⟨1 + T, by rw [rrun_add, h1, hT], fun t ht => ?_⟩
  rcases Nat.lt_or_ge t 1 with h' | h'
  · obtain rfl : t = 0 := by omega
    exact ⟨s, ip, h₀, hs⟩
  · obtain ⟨t', rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
    rw [rrun_add, h1]; exact hm t' (by omega)

/-- Prepend a step to a rejecting run. -/
lemma Rejects.step {c₀ c₁ c : Cfg m Bool Λ x} {p : ℤ} (s : Λ) (ip : Fin (x.length + 2))
    (h₀ : c₀ = xCfg c s ip r p) (hs : P.call s = none) (h1 : rrun P oracle c₀ 1 = c₁)
    (h : Rejects P oracle c₁ c r p) : Rejects P oracle c₀ c r p := by
  obtain ⟨T, e1, e2, e3, hm⟩ := h
  refine ⟨1 + T, by rw [rrun_add, h1]; exact e1, by rw [rrun_add, h1]; exact e2,
    by rw [rrun_add, h1]; exact e3, fun t ht => ?_⟩
  rcases Nat.lt_or_ge t 1 with h' | h'
  · obtain rfl : t = 0 := by omega
    exact ⟨s, ip, h₀, hs⟩
  · obtain ⟨t', rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
    rw [rrun_add, h1]; exact hm t' (by omega)

/-- Concatenate reaching runs. -/
lemma Reaches.trans {c₀ c₁ c₂ c : Cfg m Bool Λ x} {p : ℤ} (h₁ : Reaches P oracle c₀ c₁ c r p)
    (h₂ : Reaches P oracle c₁ c₂ c r p) : Reaches P oracle c₀ c₂ c r p := by
  obtain ⟨T₁, e1, m1⟩ := h₁
  obtain ⟨T₂, e2, m2⟩ := h₂
  refine ⟨T₁ + T₂, by rw [rrun_add, e1, e2], fun t ht => ?_⟩
  rcases Nat.lt_or_ge t T₁ with h | h
  · exact m1 t h
  · obtain ⟨t', rfl⟩ : ∃ t', t = T₁ + t' := ⟨t - T₁, by omega⟩
    rw [rrun_add, e1]; exact m2 t' (by omega)

/-- A reaching run followed by a rejecting one rejects. -/
lemma Reaches.rejects {c₀ c₁ c : Cfg m Bool Λ x} {p : ℤ} (h₁ : Reaches P oracle c₀ c₁ c r p)
    (h₂ : Rejects P oracle c₁ c r p) : Rejects P oracle c₀ c r p := by
  obtain ⟨T₁, e1, m1⟩ := h₁
  obtain ⟨T₂, f1, f2, f3, m2⟩ := h₂
  refine ⟨T₁ + T₂, by rw [rrun_add, e1]; exact f1, by rw [rrun_add, e1]; exact f2,
    by rw [rrun_add, e1]; exact f3, fun t ht => ?_⟩
  rcases Nat.lt_or_ge t T₁ with h | h
  · exact m1 t h
  · obtain ⟨t', rfl⟩ : ∃ t', t = T₁ + t' := ⟨t - T₁, by omega⟩
    rw [rrun_add, e1]; exact m2 t' (by omega)

/-- A one-step rejection. -/
lemma rejects_one {c : Cfg m Bool Λ x} {p : ℤ} (s : Λ) (ip : Fin (x.length + 2))
    (hs : P.call s = none) (htr : ∀ w, P.tm.tr s (inSym x ip.val) w = rejAct) :
    Rejects P oracle (xCfg c s ip r p) c r p := by
  obtain ⟨e1, e2, e3⟩ := rrun_one_rej P oracle c s ip r p hs htr
  refine ⟨1, e1, e2, e3, fun t ht => ?_⟩
  obtain rfl : t = 0 := by omega
  exact ⟨s, ip, rfl, hs⟩

/-- A reflexive reaching run. -/
lemma Reaches.refl (c₀ c : Cfg m Bool Λ x) (p : ℤ) : Reaches P oracle c₀ c₀ c r p :=
  ⟨0, rfl, fun t ht => absurd ht (by omega)⟩

/-- One right move of the input head, as a reaching step. -/
lemma reaches_right {c : Cfg m Bool Λ x} {p : ℤ} (s s' : Λ) (q : ℕ) (hq : q ≤ x.length)
    (hs : P.call s = none) (htr : ∀ w, P.tm.tr s (inSym x q) w = xAct r 1 0 s') :
    rrun P oracle (xCfg c s ⟨q, by omega⟩ r p) 1 = xCfg c s' ⟨q + 1, by omega⟩ r p := by
  rw [rrun_one_x P oracle c s _ r p hs]
  simp only
  rw [htr, apply_xAct]
  congr 1
  · exact Fin.ext (by rw [moveInputPos_pos_val _ (by simp; omega)])
  · simp

end Phases

/-- A word has no trailing `0` iff its last letter (if any) is not `0`. -/
lemma canon_iff (u : List Bool) : Canon u ↔ u.getLast? ≠ some false := by
  constructor
  · intro h hl
    have hne : u ≠ [] := by rintro rfl; simp at hl
    rw [List.getLast?_eq_getLast hne, h hne] at hl; simp at hl
  · intro h hne
    have := List.getLast?_eq_getLast hne
    cases hb : u.getLast hne
    · rw [hb] at this; exact absurd this h
    · rfl

/-- Choosing between `none` and `o` gives `o`. -/
lemma none_orElse' (o : Option Bool) : ((none : Option Bool) <|> o) = o := rfl

section Phases2

variable (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (r : Fin m)

/-- The word state remembering the last bit. -/
def wSt (vW0 vWF vWT : Λ) : Option Bool → Λ
  | none => vW0
  | some false => vWF
  | some true => vWT

include P in
/-- **The final-word phase** of a format check: from `vW` at input position `q`, the rest of
the input being `w`, reach `next` (input rewound) if the last bit read (of `w`, else `last`)
is not `0`, and reject otherwise.

**Proof sketch.** Induction on `w`. Each letter moves the input head right and records it as the
last letter (`wSt`). At the end of the input, the state is accepting exactly when the last
letter is not `0`; it then rewinds the input head (`rewind_x`), and otherwise rejects. -/
lemma valWord_run (vW0 vWF vWT rw₁ rw₂ next : Λ)
    (hW0 : ∀ a w, P.tm.tr vW0 a w = valWAct r vWF vWT rw₁ none a)
    (hWF : ∀ a w, P.tm.tr vWF a w = valWAct r vWF vWT rw₁ (some false) a)
    (hWT : ∀ a w, P.tm.tr vWT a w = valWAct r vWF vWT rw₁ (some true) a)
    (h₁ : ∀ a w, P.tm.tr rw₁ a w = xAct r (-1) 0 rw₂)
    (h₂ : ∀ a w, P.tm.tr rw₂ a w = match a with
      | some _ => xAct r (-1) 0 rw₂
      | none => xAct r 1 0 next)
    (cW0 : P.call vW0 = none) (cWF : P.call vWF = none) (cWT : P.call vWT = none)
    (c₁ : P.call rw₁ = none) (c₂ : P.call rw₂ = none) (c : Cfg m Bool Λ x) (p : ℤ) :
    ∀ (w : List Bool) (last : Option Bool) (q : ℕ) (hq : q + w.length = x.length + 1),
      (∀ k, inSym x (q + k) = w[k]?) →
      ((w.getLast? <|> last) ≠ some false →
        Reaches P oracle (xCfg c (wSt vW0 vWF vWT last) ⟨q, by omega⟩ r p)
          (xCfg c next ⟨1, by omega⟩ r p) c r p) ∧
      ((w.getLast? <|> last) = some false →
        Rejects P oracle (xCfg c (wSt vW0 vWF vWT last) ⟨q, by omega⟩ r p) c r p) := by
  have htr : ∀ (l : Option Bool) a ww, P.tm.tr (wSt vW0 vWF vWT l) a ww =
      valWAct r vWF vWT rw₁ l a := by
    intro l a ww; rcases l with _ | _ | _
    · exact hW0 a ww
    · exact hWF a ww
    · exact hWT a ww
  have hcall : ∀ l, P.call (wSt vW0 vWF vWT l) = none := by
    intro l; rcases l with _ | _ | _
    · exact cW0
    · exact cWF
    · exact cWT
  intro w
  induction w with
  | nil =>
    intro last q hq hin
    have hsym : inSym x q = none := by simpa using hin 0
    constructor
    · intro hl
      simp only [List.getLast?_nil, none_orElse'] at hl
      have hstep : rrun P oracle (xCfg c (wSt vW0 vWF vWT last) ⟨q, by omega⟩ r p) 1 =
          xCfg c rw₁ ⟨q, by omega⟩ r p := by
        rw [rrun_one_x P oracle c _ _ r p (hcall last)]
        simp only
        rw [htr, hsym]
        simp only [valWAct, if_neg hl]
        rw [apply_xAct]; simp
      obtain ⟨T, hT, hm⟩ := rewind_x P oracle c r p rw₁ rw₂ next h₁ h₂ c₁ c₂ ⟨q, by omega⟩
      exact Reaches.step P oracle r _ _ rfl (hcall last) hstep
        ⟨T, hT, fun t ht => by obtain ⟨s', ip', h, hc⟩ := hm t ht; exact ⟨s', ip', h, hc⟩⟩
    · intro hl
      simp only [List.getLast?_nil, none_orElse'] at hl
      exact rejects_one P oracle r _ _ (hcall last) (fun ww => by
        rw [htr]; simp only; rw [hsym]; simp [valWAct, hl])
  | cons b w ih =>
    intro last q hq hin
    have hsym : inSym x q = some b := by simpa using hin 0
    have hstep : rrun P oracle (xCfg c (wSt vW0 vWF vWT last) ⟨q, by omega⟩ r p) 1 =
        xCfg c (wSt vW0 vWF vWT (some b)) ⟨q + 1, by simp at hq; omega⟩ r p := by
      rw [reaches_right P oracle r _ (wSt vW0 vWF vWT (some b)) q (by simp at hq; omega)
        (hcall last) (fun ww => by rw [htr, hsym]; simp only [valWAct]; cases b <;> rfl)]
    have hin' : ∀ k, inSym x (q + 1 + k) = w[k]? := fun k => by
      rw [show q + 1 + k = q + (k + 1) by ring, hin]; simp
    obtain ⟨ih1, ih2⟩ := ih (some b) (q + 1) (by simp at hq; omega) hin'
    have hlast : ((b :: w).getLast? <|> last) = (w.getLast? <|> some b) := by
      cases hw : w.getLast? with
      | none =>
        have : w = [] := by simpa using hw
        subst this; simp
      | some v => rw [getLast?_cons_of hw]; simp
    rw [hlast]
    exact ⟨fun h => Reaches.step P oracle r _ _ rfl (hcall last) hstep (ih1 h),
      fun h => Rejects.step P oracle r _ _ rfl (hcall last) hstep (ih2 h)⟩

end Phases2

/-- First symbol of a pair. -/
def valP1Act (r : Fin m) (vP2 : Bool → Λ) (a : Option Bool) : Action m Bool Λ :=
  match a with
  | some b => xAct r 1 0 (vP2 b)
  | none => rejAct

/-- Second symbol of a pair: `bb` continues, `01` ends the pairs (if the last bit was not `0`). -/
def valP2Act (r : Fin m) (vP1F vP1T vW0 : Λ) (last : Option Bool) (b₁ : Bool) (a : Option Bool) :
    Action m Bool Λ :=
  match a with
  | some b₂ =>
    if b₁ = false ∧ b₂ = true then (if last = some false then rejAct else xAct r 1 0 vW0)
    else if b₁ = b₂ then xAct r 1 0 (if b₁ then vP1T else vP1F) else rejAct
  | none => rejAct

section Pairs

variable (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (r : Fin m)
  (vP1 : Option Bool → Λ) (vP2 : Bool → Option Bool → Λ) (vW0 : Λ)
  (hP1 : ∀ l a w, P.tm.tr (vP1 l) a w = valP1Act r (fun b => vP2 b l) a)
  (hP2 : ∀ b l a w, P.tm.tr (vP2 b l) a w =
    valP2Act r (vP1 (some false)) (vP1 (some true)) vW0 l b a)
  (cP1 : ∀ l, P.call (vP1 l) = none) (cP2 : ∀ b l, P.call (vP2 b l) = none)

include hP1 hP2 cP1 cP2 in
/-- **The pair phase** of the pair format check follows `scanPairs`.

**Proof sketch.** Induction on `z` following `scanPairs`. The phase reads two input letters at a
time: `b b` continues with `b` remembered, `0 1` ends the pairs (accepting only if the last
letter was not `0`) and moves to the final word, and anything else, or the end of the input,
rejects. -/
lemma valPairs_run (c : Cfg m Bool Λ x) (p : ℤ) :
    ∀ (z : List Bool) (last : Option Bool) (q : ℕ) (hq : q + z.length = x.length + 1),
      (∀ k, inSym x (q + k) = z[k]?) →
      (∀ w, scanPairs last z = some w →
        ∃ hw : q + z.length - w.length < x.length + 2,
          Reaches P oracle (xCfg c (vP1 last) ⟨q, by omega⟩ r p)
            (xCfg c vW0 ⟨q + z.length - w.length, hw⟩ r p) c r p) ∧
      (scanPairs last z = none → Rejects P oracle (xCfg c (vP1 last) ⟨q, by omega⟩ r p) c r p) := by
  intro z
  induction z using List.twoStepInduction with
  | nil =>
    intro last q hq hin
    refine ⟨fun w h => by simp [scanPairs] at h, fun _ => ?_⟩
    exact rejects_one P oracle r _ _ (cP1 last) (fun ww => by
      rw [hP1]; have := hin 0; simp at this; rw [this]; rfl)
  | singleton b =>
    intro last q hq hin
    refine ⟨fun w h => by cases b <;> simp [scanPairs] at h, fun _ => ?_⟩
    have h0 : inSym x q = some b := by simpa using hin 0
    have h1 : inSym x (q + 1) = none := by simpa using hin 1
    have hstep : rrun P oracle (xCfg c (vP1 last) ⟨q, by omega⟩ r p) 1 =
        xCfg c (vP2 b last) ⟨q + 1, by simp at hq; omega⟩ r p :=
      reaches_right P oracle r _ _ q (by simp at hq; omega) (cP1 last)
        (fun ww => by rw [hP1, h0]; rfl)
    exact Rejects.step P oracle r _ _ rfl (cP1 last) hstep
      (rejects_one P oracle r _ _ (cP2 b last) (fun ww => by
        rw [hP2]; simp only; rw [h1]; rfl))
  | cons_cons b b' rest ih _ =>
    intro last q hq hin
    simp only [List.length_cons] at hq
    have h0 : inSym x q = some b := by simpa using hin 0
    have h1 : inSym x (q + 1) = some b' := by simpa using hin 1
    have hstep : rrun P oracle (xCfg c (vP1 last) ⟨q, by omega⟩ r p) 1 =
        xCfg c (vP2 b last) ⟨q + 1, by omega⟩ r p :=
      reaches_right P oracle r _ _ q (by omega) (cP1 last) (fun ww => by rw [hP1, h0]; rfl)
    have hin' : ∀ k, inSym x (q + 2 + k) = rest[k]? := fun k => by
      rw [show q + 2 + k = q + (k + 2) by ring, hin]; simp
    cases b <;> cases b'
    · -- `00`
      have hstep2 : rrun P oracle (xCfg c (vP2 false last) ⟨q + 1, by omega⟩ r p) 1 =
          xCfg c (vP1 (some false)) ⟨q + 1 + 1, by omega⟩ r p :=
        reaches_right P oracle r _ _ (q + 1) (by omega) (cP2 false last)
          (fun ww => by rw [hP2, h1]; simp [valP2Act])
      obtain ⟨ih1, ih2⟩ := ih (some false) (q + 2) (by omega) hin'
      simp only [scanPairs]
      refine ⟨fun w h => ?_, fun h => ?_⟩
      · obtain ⟨hw, hr⟩ := ih1 w h
        refine ⟨by simp; omega, ?_⟩
        refine Reaches.step P oracle r _ _ rfl (cP1 last) hstep
          (Reaches.step P oracle r _ _ rfl (cP2 false last) hstep2 ?_)
        convert hr using 3
        simp; omega
      · exact Rejects.step P oracle r _ _ rfl (cP1 last) hstep
          (Rejects.step P oracle r _ _ rfl (cP2 false last) hstep2 (ih2 h))
    · -- `01`: the separator
      simp only [scanPairs]
      by_cases hl : last = some false
      · rw [if_pos hl]
        refine ⟨fun w h => by simp at h, fun _ => ?_⟩
        exact Rejects.step P oracle r _ _ rfl (cP1 last) hstep
          (rejects_one P oracle r _ _ (cP2 false last) (fun ww => by
            rw [hP2, h1]; simp only [valP2Act, and_self, ↓reduceIte, if_pos hl]))
      · rw [if_neg hl]
        have hstep2 : rrun P oracle (xCfg c (vP2 false last) ⟨q + 1, by omega⟩ r p) 1 =
            xCfg c vW0 ⟨q + 1 + 1, by omega⟩ r p :=
          reaches_right P oracle r _ _ (q + 1) (by omega) (cP2 false last)
            (fun ww => by rw [hP2, h1]; simp [valP2Act, hl])
        refine ⟨fun w h => ?_, fun h => by simp at h⟩
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨by simp; omega, ?_⟩
        refine Reaches.step P oracle r _ _ rfl (cP1 last) hstep
          (Reaches.step P oracle r _ _ rfl (cP2 false last) hstep2 ?_)
        convert Reaches.refl P oracle r _ c p using 3
        simp; omega
    · -- `10`: malformed
      simp only [scanPairs]
      refine ⟨fun w h => by simp at h, fun _ => ?_⟩
      exact Rejects.step P oracle r _ _ rfl (cP1 last) hstep
        (rejects_one P oracle r _ _ (cP2 true last) (fun ww => by
          rw [hP2]; simp only; rw [h1]; simp [valP2Act]))
    · -- `11`
      have hstep2 : rrun P oracle (xCfg c (vP2 true last) ⟨q + 1, by omega⟩ r p) 1 =
          xCfg c (vP1 (some true)) ⟨q + 1 + 1, by omega⟩ r p :=
        reaches_right P oracle r _ _ (q + 1) (by omega) (cP2 true last)
          (fun ww => by rw [hP2, h1]; simp [valP2Act])
      obtain ⟨ih1, ih2⟩ := ih (some true) (q + 2) (by omega) hin'
      simp only [scanPairs]
      refine ⟨fun w h => ?_, fun h => ?_⟩
      · obtain ⟨hw, hr⟩ := ih1 w h
        refine ⟨by simp; omega, ?_⟩
        refine Reaches.step P oracle r _ _ rfl (cP1 last) hstep
          (Reaches.step P oracle r _ _ rfl (cP2 true last) hstep2 ?_)
        convert hr using 3
        simp; omega
      · exact Rejects.step P oracle r _ _ rfl (cP1 last) hstep
          (Rejects.step P oracle r _ _ rfl (cP2 true last) hstep2 (ih2 h))

end Pairs

section Prefix

variable (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (r : Fin m)
  (vU0 vU1 vS vX : Λ)
  (hU0 : ∀ a w, P.tm.tr vU0 a w = valUAct r vU0 vU1 vS false a)
  (hU1 : ∀ a w, P.tm.tr vU1 a w = valUAct r vU0 vU1 vS true a)
  (hS : ∀ a w, P.tm.tr vS a w = valSAct r vX a)
  (cU0 : P.call vU0 = none) (cU1 : P.call vU1 = none) (cS : P.call vS = none)

include hU0 hU1 hS cU0 cU1 cS in
/-- **The prefix phase** of the format checks: an even run of `1`s, then `0 1`.

**Proof sketch.** Scan the leading run of `1`s keeping its parity in the state (`tRun` letters),
then require `0` and then `1`. If all three conditions hold the run reaches `vX` after `tRun x +
2` letters; otherwise the parity test or one of the two letter tests rejects. -/
lemma valPrefix_run (c : Cfg m Bool Λ x) (p : ℤ) :
    (∀ _h : tRun x % 2 = 0 ∧ x[tRun x]? = some false ∧ x[tRun x + 1]? = some true,
      ∃ hb : 3 + tRun x < x.length + 2,
        Reaches P oracle (xCfg c vU0 ⟨1, by omega⟩ r p) (xCfg c vX ⟨3 + tRun x, hb⟩ r p) c r p) ∧
    (¬ (tRun x % 2 = 0 ∧ x[tRun x]? = some false ∧ x[tRun x + 1]? = some true) →
      Rejects P oracle (xCfg c vU0 ⟨1, by omega⟩ r p) c r p) := by
  set t := tRun x with ht
  have htx : t ≤ x.length := tRun_le x
  let st : ℕ → Λ := fun j => if j % 2 = 0 then vU0 else vU1
  have hst : ∀ j, P.call (st j) = none := fun j => by simp only [st]; split_ifs <;> assumption
  have hscan := scanR P oracle c r p st 1 t (by omega) (fun j hj w => by
      rw [show 1 + j = j + 1 by ring, inSym_succ, getElem?_lt_tRun x j hj]
      simp only [st]
      split_ifs with h1 h2 h2
      · omega
      · rw [hU0]; simp [valUAct]
      · rw [hU1]; simp [valUAct]
      · omega)
    (fun j hj => hst j)
  have hU : Reaches P oracle (xCfg c vU0 ⟨1, by omega⟩ r p) (xCfg c (st t) ⟨1 + t, by omega⟩ r p)
      c r p :=
    ⟨t, hscan t le_rfl, fun j hj => ⟨st j, _, hscan j hj.le, hst j⟩⟩
  have hsym1 : inSym x (1 + t) = x[t]? := by rw [show 1 + t = t + 1 by ring, inSym_succ]
  have hnotT := getElem?_tRun x
  rw [← ht] at hnotT
  rcases hxt : x[t]? with _ | b
  · refine ⟨fun h => by simp at h, fun _ => hU.rejects P oracle r
      (rejects_one P oracle r _ _ (hst t) (fun w => ?_))⟩
    rw [hsym1, hxt]; simp only [st]; split_ifs
    · rw [hU0]; rfl
    · rw [hU1]; rfl
  cases b with
  | true => exact absurd hxt hnotT
  | false =>
  have htlt : t < x.length := by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at hxt; simp at hxt
  by_cases hpar : t % 2 = 0
  swap
  · refine ⟨fun h => absurd h.1 hpar, fun _ => hU.rejects P oracle r
      (rejects_one P oracle r _ _ (hst t) (fun w => ?_))⟩
    rw [hsym1, hxt]; simp only [st, hpar, ↓reduceIte]; rw [hU1]; rfl
  have hS1 : rrun P oracle (xCfg c (st t) ⟨1 + t, by omega⟩ r p) 1 =
      xCfg c vS ⟨1 + t + 1, by omega⟩ r p :=
    reaches_right P oracle r _ _ (1 + t) (by omega) (hst t) (fun w => by
      rw [hsym1, hxt]; simp only [st, hpar, ↓reduceIte]; rw [hU0]; rfl)
  have hUS := hU.trans P oracle r (Reaches.step P oracle r _ _ rfl (hst t) hS1
    (Reaches.refl P oracle r _ c p))
  have hsym2 : inSym x (1 + t + 1) = x[t + 1]? := by rw [show 1 + t + 1 = (t + 1) + 1 by ring,
    inSym_succ]
  rcases hxt1 : x[t + 1]? with _ | b'
  · refine ⟨fun h => by simp at h, fun _ => hUS.rejects P oracle r
      (rejects_one P oracle r _ _ cS (fun w => by rw [hsym2, hxt1, hS]; rfl))⟩
  cases b' with
  | false =>
    refine ⟨fun h => by simp at h, fun _ => hUS.rejects P oracle r
      (rejects_one P oracle r _ _ cS (fun w => by rw [hsym2, hxt1, hS]; rfl))⟩
  | true =>
  have htlt1 : t + 1 < x.length := by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at hxt1; simp at hxt1
  have hS2 : rrun P oracle (xCfg c vS ⟨1 + t + 1, by omega⟩ r p) 1 =
      xCfg c vX ⟨1 + t + 1 + 1, by omega⟩ r p :=
    reaches_right P oracle r _ _ (1 + t + 1) (by omega) cS (fun w => by
      rw [hsym2, hxt1, hS]; rfl)
  refine ⟨fun _ => ⟨by omega, ?_⟩, fun h => absurd ⟨hpar, rfl, rfl⟩ h⟩
  have := hUS.trans P oracle r (Reaches.step P oracle r _ _ rfl cS hS2
    (Reaches.refl P oracle r _ c p))
  convert this using 3
  omega

end Prefix

/-- An input with a good prefix splits as `⟨1ⁿ, z⟩`.

**Proof sketch.** Split `y` as its leading run `1^{tRun y}`, then `0 1`, then the rest. The run
has even length `2 (tRun y / 2)`, so it is `dbl 1^{tRun y / 2}` (`dbl_replicate`), and the
decomposition is `pairEncode`'s definition. -/
lemma prefix_decomp (y : List Bool) (h0 : tRun y % 2 = 0) (h1 : y[tRun y]? = some false)
    (h2 : y[tRun y + 1]? = some true) :
    y = pairEncode (List.replicate (tRun y / 2) true) (y.drop (tRun y + 2)) := by
  have htake : y.take (tRun y) = List.replicate (tRun y) true := by
    apply List.ext_getElem?
    intro i
    by_cases hi : i < tRun y
    · rw [List.getElem?_take, if_pos hi, getElem?_lt_tRun y i hi]; simp [hi]
    · rw [List.getElem?_take, if_neg hi]; simp [hi]
  have hsplit : y = y.take (tRun y) ++ [false, true] ++ y.drop (tRun y + 2) := by
    apply List.ext_getElem?
    intro i
    rw [List.getElem?_append, List.getElem?_append]
    have hle : tRun y ≤ y.length := tRun_le y
    have hlen : tRun y + 2 ≤ y.length := by
      by_contra h; rw [List.getElem?_eq_none (by omega)] at h2; simp at h2
    by_cases ha : i < tRun y
    · simp [ha, List.length_take, hle, show i < tRun y + 2 by omega,
        List.getElem?_eq_getElem (show i < y.length by omega)]
    · by_cases hb : i < tRun y + 2
      · have : i = tRun y ∨ i = tRun y + 1 := by omega
        rcases this with rfl | rfl
        · simp [h1, hle]
        · simp [h2, hle]
      · simp [hb, hle, List.getElem?_drop]
        congr 1; omega
  rw [pairEncode_eq_dbl, dbl_replicate, show 2 * (tRun y / 2) = tRun y by omega, ← htake]
  exact hsplit

/-- The leading run of `1`s of `⟨1ⁿ, z⟩` has length `2n`. -/
lemma tRun_pairEncode (n : ℕ) (z : List Bool) :
    tRun (pairEncode (List.replicate n true) z) = 2 * n := by
  simp only [tRun, pairEncode_eq_dbl, dbl_replicate, List.append_assoc]
  rw [List.takeWhile_append_of_pos (by simp)]
  simp

/-- The pair format, read off the prefix and the pair scan.

**Proof sketch.** (⇒) On `⟨1ⁿ, ⟨u, w⟩⟩` the prefix is `1²ⁿ 0 1` and the rest is `dbl u 01 w`,
which the pair scan accepts with rest `w` (`scanPairs_iff`). (⇐) Decompose the prefix
(`prefix_decomp`) and the rest (`scanPairs_iff`). The last letter of `u` is not `0`, so `u` has
no trailing `0` (`canon_iff`). -/
lemma validPair_iff (y : List Bool) :
    ValidPair y ↔ (tRun y % 2 = 0 ∧ y[tRun y]? = some false ∧ y[tRun y + 1]? = some true) ∧
      ∃ w, scanPairs none (y.drop (tRun y + 2)) = some w ∧ Canon w := by
  constructor
  · rintro ⟨n, u, w, rfl, hu, hw⟩
    rw [tRun_pairEncode]
    refine ⟨⟨by omega, by simp [pairEncode_eq_dbl, dbl_replicate],
      by simp [pairEncode_eq_dbl, dbl_replicate]⟩, w, ?_, hw⟩
    have hd : (pairEncode (List.replicate n true) (pairEncode u w)).drop (2 * n + 2) =
        dbl u ++ [false, true] ++ w := by
      simp [pairEncode_eq_dbl, dbl_replicate, List.drop_append]
    rw [hd, scanPairs_iff]
    exact ⟨u, rfl, by simpa [none_orElse'] using (canon_iff u).mp hu⟩
  · rintro ⟨⟨h0, h1, h2⟩, w, hs, hw⟩
    obtain ⟨u, hz, hu⟩ := (scanPairs_iff none _ w).mp hs
    refine ⟨tRun y / 2, u, w, ?_, (canon_iff u).mpr (by
      cases hl : u.getLast? <;> simp_all [none_orElse']), hw⟩
    rw [← pairEncode_eq_dbl] at hz
    rw [← hz]
    exact prefix_decomp y h0 h1 h2

section ValPair

variable (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (r : Fin m)
  (vU0 vU1 vS : Λ) (vP1 : Option Bool → Λ) (vP2 : Bool → Option Bool → Λ)
  (vW0 vWF vWT rw₁ rw₂ next : Λ)
  (hU0 : ∀ a w, P.tm.tr vU0 a w = valUAct r vU0 vU1 vS false a)
  (hU1 : ∀ a w, P.tm.tr vU1 a w = valUAct r vU0 vU1 vS true a)
  (hS : ∀ a w, P.tm.tr vS a w = valSAct r (vP1 none) a)
  (hP1 : ∀ l a w, P.tm.tr (vP1 l) a w = valP1Act r (fun b => vP2 b l) a)
  (hP2 : ∀ b l a w, P.tm.tr (vP2 b l) a w =
    valP2Act r (vP1 (some false)) (vP1 (some true)) vW0 l b a)
  (hW0 : ∀ a w, P.tm.tr vW0 a w = valWAct r vWF vWT rw₁ none a)
  (hWF : ∀ a w, P.tm.tr vWF a w = valWAct r vWF vWT rw₁ (some false) a)
  (hWT : ∀ a w, P.tm.tr vWT a w = valWAct r vWF vWT rw₁ (some true) a)
  (h₁ : ∀ a w, P.tm.tr rw₁ a w = xAct r (-1) 0 rw₂)
  (h₂ : ∀ a w, P.tm.tr rw₂ a w = match a with
    | some _ => xAct r (-1) 0 rw₂
    | none => xAct r 1 0 next)
  (cU0 : P.call vU0 = none) (cU1 : P.call vU1 = none) (cS : P.call vS = none)
  (cP1 : ∀ l, P.call (vP1 l) = none) (cP2 : ∀ b l, P.call (vP2 b l) = none)
  (cW0 : P.call vW0 = none) (cWF : P.call vWF = none) (cWT : P.call vWT = none)
  (c₁ : P.call rw₁ = none) (c₂ : P.call rw₂ = none)

include hU0 hU1 hS hP1 hP2 hW0 hWF hWT h₁ h₂ cU0 cU1 cS cP1 cP2 cW0 cWF cWT c₁ c₂ in
/-- **The pair format check**: it reaches `next` (input head back on position `1`) exactly on
inputs `⟨1ⁿ, ⟨u, w⟩⟩` with `u`, `w` free of trailing `0`s, and rejects otherwise.

**Proof sketch.** `valPrefix_run`, then the pair scan `valPairs_run` (which follows
`scanPairs`), then the final word `valWord_run`; `validPair_iff` identifies acceptance. -/
lemma valPair_run (c : Cfg m Bool Λ x) (p : ℤ) :
    (ValidPair x → Reaches P oracle (xCfg c vU0 ⟨1, by omega⟩ r p) (xCfg c next ⟨1, by omega⟩ r p)
      c r p) ∧
    (¬ ValidPair x → Rejects P oracle (xCfg c vU0 ⟨1, by omega⟩ r p) c r p) := by
  have hv := validPair_iff x
  obtain ⟨pre1, pre2⟩ := valPrefix_run P oracle r vU0 vU1 vS (vP1 none) hU0 hU1 hS cU0 cU1 cS c p
  by_cases hpre : tRun x % 2 = 0 ∧ x[tRun x]? = some false ∧ x[tRun x + 1]? = some true
  swap
  · exact ⟨fun h => absurd ((hv.mp h).1) hpre, fun _ => pre2 hpre⟩
  obtain ⟨hb, hr1⟩ := pre1 hpre
  set t := tRun x
  set z := x.drop (t + 2) with hz
  have hlen : t + 2 ≤ x.length := by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at hpre; simp at hpre
  have hzlen : 3 + t + z.length = x.length + 1 := by simp [hz]; omega
  have hinz : ∀ k, inSym x (3 + t + k) = z[k]? := by
    intro k; rw [show 3 + t + k = (t + 2 + k) + 1 by ring, inSym_succ, hz, List.getElem?_drop]
  obtain ⟨pp1, pp2⟩ := valPairs_run P oracle r vP1 vP2 vW0 hP1 hP2 cP1 cP2 c p z none (3 + t)
    hzlen hinz
  rcases hs : scanPairs none z with _ | w
  · refine ⟨fun h => ?_, fun _ => hr1.rejects P oracle r (pp2 hs)⟩
    obtain ⟨-, w, hw, -⟩ := hv.mp h
    rw [hs] at hw; simp at hw
  · obtain ⟨hb2, hr2⟩ := pp1 w hs
    obtain ⟨u, hzu, -⟩ := (scanPairs_iff none z w).mp hs
    have hzl : z.length = (dbl u ++ [false, true]).length + w.length := by
      rw [hzu]; simp; omega
    have hinw : ∀ k, inSym x (3 + t + z.length - w.length + k) = w[k]? := by
      intro k
      rw [show 3 + t + z.length - w.length + k = 3 + t + ((dbl u ++ [false, true]).length + k) by
        omega, hinz, hzu, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
    obtain ⟨ww1, ww2⟩ := valWord_run P oracle r vW0 vWF vWT rw₁ rw₂ next hW0 hWF hWT h₁ h₂
      cW0 cWF cWT c₁ c₂ c p w none (3 + t + z.length - w.length) (by omega) hinw
    simp only [wSt] at ww1 ww2
    by_cases hcw : Canon w
    · have hok : (w.getLast? <|> none) ≠ some false := by
        cases hl : w.getLast? <;> simp_all [(canon_iff w)]
      refine ⟨fun _ => (hr1.trans P oracle r hr2).trans P oracle r (ww1 hok),
        fun h => absurd (hv.mpr ⟨hpre, w, hs, hcw⟩) h⟩
    · have hbad : (w.getLast? <|> none) = some false := by
        rw [canon_iff] at hcw; push_neg at hcw
        cases hl : w.getLast? <;> simp_all
      refine ⟨fun h => ?_, fun _ => (hr1.trans P oracle r hr2).rejects P oracle r (ww2 hbad)⟩
      obtain ⟨-, w', hw', hc'⟩ := hv.mp h
      rw [hs] at hw'; simp at hw'; subst hw'; exact absurd hc' hcw

end ValPair

end Complexity.LogProg

```


## ===== TCSlib/Complexity/SpaceComplexity/Machines/ParseCmp.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.Parse2

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Comparisons on inputs `⟨1ⁿ, ⟨u, w⟩⟩`

Program fragments comparing a register with the components of an input `⟨1ⁿ, ⟨u, w⟩⟩`:
with `w` (`Complexity.LogProg.jeqPairSnd_run`, after skipping the doubled `u`) and with `u`
(`Complexity.LogProg.jeqPairFst_run`, reading `u` doubled), in lockstep and without copying.

## Main definitions

* `Complexity.LogProg.ReachesB` — runs ending in one of two configurations.

## Main results

* `Complexity.LogProg.jeqPairSnd_run`, `Complexity.LogProg.jeqPairFst_run` — the comparisons.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.)
-/

namespace Complexity.LogProg

open Turing

variable {m d : ℕ} {Λ : Type} {x : List Bool}

/-! ## Comparisons on pair inputs -/

/-- First symbol of a skipped pair. -/
def pskip1Act (r : Fin m) (jP2F jP2T : Λ) (a : Option Bool) : Action m Bool Λ :=
  match a with
  | some true => xAct r 1 0 jP2T
  | _ => xAct r 1 0 jP2F

/-- Second symbol of a skipped pair: `01` ends the pairs. -/
def pskip2Act (r : Fin m) (jP1 jC : Λ) (b₁ : Bool) (a : Option Bool) : Action m Bool Λ :=
  if b₁ = false ∧ a = some true then xAct r 1 0 jC else xAct r 1 0 jP1

/-- The input symbols of `⟨1ⁿ, ⟨u, w⟩⟩` after the end marker spell `1²ⁿ 01 dbl u 01 w`. -/
lemma inSym_pairInput (n : ℕ) (u w : List Bool) (k : ℕ) :
    inSym (pairEncode (List.replicate n true) (pairEncode u w)) (k + 1) =
      (List.replicate (2 * n) true ++ [false, true] ++ dbl u ++ [false, true] ++ w)[k]? := by
  rw [inSym_succ]; simp [pairEncode_eq_dbl, dbl_replicate]

section PairSkip

variable (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (r : Fin m)
  (jP1 jP2F jP2T jC : Λ)
  (hP1 : ∀ a w, P.tm.tr jP1 a w = pskip1Act r jP2F jP2T a)
  (hP2F : ∀ a w, P.tm.tr jP2F a w = pskip2Act r jP1 jC false a)
  (hP2T : ∀ a w, P.tm.tr jP2T a w = pskip2Act r jP1 jC true a)
  (cP1 : P.call jP1 = none) (cP2F : P.call jP2F = none) (cP2T : P.call jP2T = none)

include hP1 hP2F hP2T cP1 cP2F cP2T in
/-- Skipping the doubled word and its separator.

**Proof sketch.** Induction on `u`: each doubled letter `b b` is skipped in two steps
(`pskip1Act`, `pskip2Act`), and the separator `0 1` moves to `jC`. The input head ends just
after the separator; the register head never moves. -/
lemma pairSkip_run (c : Cfg m Bool Λ x) (p : ℤ) :
    ∀ (u : List Bool) (q : ℕ) (hq : q + 2 * u.length + 2 ≤ x.length + 1),
      (∀ k < 2 * u.length + 2, inSym x (q + k) = (dbl u ++ [false, true])[k]?) →
      Reaches P oracle (xCfg c jP1 ⟨q, by omega⟩ r p)
        (xCfg c jC ⟨q + 2 * u.length + 2, by omega⟩ r p) c r p := by
  intro u
  induction u with
  | nil =>
    intro q hq hin
    have h0 : inSym x q = some false := by simpa using hin 0 (by simp)
    have h1 : inSym x (q + 1) = some true := by simpa using hin 1 (by simp)
    have s1 : rrun P oracle (xCfg c jP1 ⟨q, by omega⟩ r p) 1 = xCfg c jP2F ⟨q + 1, by simp at hq; omega⟩ r p :=
      reaches_right P oracle r _ _ q (by simp at hq; omega) cP1 (fun w => by rw [hP1, h0]; rfl)
    have s2 : rrun P oracle (xCfg c jP2F ⟨q + 1, by simp at hq; omega⟩ r p) 1 =
        xCfg c jC ⟨q + 1 + 1, by simp at hq; omega⟩ r p :=
      reaches_right P oracle r _ _ (q + 1) (by simp at hq; omega) cP2F
        (fun w => by rw [hP2F, h1]; simp [pskip2Act])
    refine Reaches.step P oracle r _ _ rfl cP1 s1 (Reaches.step P oracle r _ _ rfl cP2F s2 ?_)
    convert Reaches.refl P oracle r _ c p using 3
  | cons b u ih =>
    intro q hq hin
    simp only [List.length_cons] at hq
    have h0 : inSym x q = some b := by simpa using hin 0 (by simp)
    have h1 : inSym x (q + 1) = some b := by simpa using hin 1 (by simp)
    have s1 : rrun P oracle (xCfg c jP1 ⟨q, by omega⟩ r p) 1 =
        xCfg c (if b then jP2T else jP2F) ⟨q + 1, by omega⟩ r p :=
      reaches_right P oracle r _ _ q (by omega) cP1 (fun w => by rw [hP1, h0]; cases b <;> rfl)
    have s2 : rrun P oracle (xCfg c (if b then jP2T else jP2F) ⟨q + 1, by omega⟩ r p) 1 =
        xCfg c jP1 ⟨q + 1 + 1, by omega⟩ r p :=
      reaches_right P oracle r _ _ (q + 1) (by omega) (by cases b <;> assumption)
        (fun w => by cases b <;> simp [hP2T, hP2F, h1, pskip2Act])
    have hin' : ∀ k < 2 * u.length + 2, inSym x (q + 2 + k) = (dbl u ++ [false, true])[k]? := by
      intro k hk
      rw [show q + 2 + k = q + (k + 2) by ring, hin (k + 2) (by simp; omega)]
      simp
    have := ih (q + 2) (by omega) hin'
    refine Reaches.step P oracle r _ _ rfl cP1 s1
      (Reaches.step P oracle r _ _ rfl (by cases b <;> assumption) s2 ?_)
    convert this using 3
    try (simp; omega)

end PairSkip

/-- Compare a doubled input word with a register: the first copy. -/
def dcmp1Act (r : Fin m) (jD2F jD2T : Λ) (a : Option Bool) : Action m Bool Λ :=
  match a with
  | some true => xAct r 1 0 jD2T
  | _ => xAct r 1 0 jD2F

/-- Compare a doubled input word with a register: the second copy (or the separator). -/
def dcmp2Act (r : Fin m) (jD1 : Λ) (jRB : Bool → Λ) (b₁ : Bool) (a c : Option Bool) :
    Action m Bool Λ :=
  if b₁ = false ∧ a = some true then xAct r 0 (-1) (jRB (decide (c = none)))
  else if c = some b₁ then xAct r 1 1 jD1 else xAct r 0 (-1) (jRB false)

section DblCmp

variable (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (r : Fin m)
  (jD1 jD2F jD2T : Λ) (jRB : Bool → Λ)
  (hD1 : ∀ a w, P.tm.tr jD1 a w = dcmp1Act r jD2F jD2T a)
  (hD2F : ∀ a w, P.tm.tr jD2F a w = dcmp2Act r jD1 jRB false a (w r))
  (hD2T : ∀ a w, P.tm.tr jD2T a w = dcmp2Act r jD1 jRB true a (w r))
  (cD1 : P.call jD1 = none) (cD2F : P.call jD2F = none) (cD2T : P.call jD2T = none)

include hD1 hD2F hD2T cD1 cD2F cD2T in
/-- The comparison walk of the doubled mode.

**Proof sketch.** Induction on `u₁`. A doubled input letter `b b` equal to the register letter
moves the input head two cells and the register head one cell. A mismatch, or reaching the
separator `0 1` before or after the register word ends, branches to `jRB false`; reaching both
ends together branches to `jRB true`. -/
lemma cmpDbl_run (c : Cfg m Bool Λ x) (wr : List Bool) (hw : c.workTapes r = FinTM.bufferTape wr)
    (wi : List Bool) (q₀ : ℕ) (hq : q₀ + 2 * wi.length + 2 ≤ x.length + 1)
    (hin : ∀ k < 2 * wi.length + 2, inSym x (q₀ + k) = (dbl wi ++ [false, true])[k]?) :
    ∀ (u₁ u₂ pre : List Bool) (ip : Fin (x.length + 2)), wi = pre ++ u₁ → wr = pre ++ u₂ →
      ip.val = q₀ + 2 * pre.length →
      ∃ (T k : ℕ) (ipk : Fin (x.length + 2)), pre.length ≤ k ∧ k ≤ wr.length ∧
        rrun P oracle (xCfg c jD1 ip r pre.length) T =
          xCfg c (jRB (decide (wi = wr))) ipk r ((k : ℤ) - 1) ∧
        ∀ t < T, ∃ s ip' q, rrun P oracle (xCfg c jD1 ip r pre.length) t = xCfg c s ip' r q ∧
          P.call s = none ∧ 0 ≤ q ∧ q ≤ wr.length := by
  intro u₁
  induction u₁ with
  | nil =>
    intro u₂ pre ip e1 e2 hip
    subst e1
    have h0 : inSym x ip.val = some false := by
      rw [hip, show q₀ + 2 * pre.length = q₀ + 2 * (pre ++ []).length by simp]
      rw [hin _ (by simp)]; simp
    have h1 : inSym x (ip.val + 1) = some true := by
      rw [hip, show q₀ + 2 * pre.length + 1 = q₀ + (2 * (pre ++ []).length + 1) by simp; ring]
      rw [hin _ (by simp)]; simp
    have s1 : rrun P oracle (xCfg c jD1 ip r pre.length) 1 =
        xCfg c jD2F ⟨ip.val + 1, by simp at hq; omega⟩ r pre.length := by
      have := reaches_right P oracle (c := c) (p := (pre.length : ℤ)) r jD1 jD2F ip.val
        (by simp at hq; omega) cD1 (fun w => by rw [hD1, h0]; rfl)
      simpa using this
    have hcr : c.workTapes r pre.length = u₂.head? := by rw [hw, e2]; cases u₂ <;> simp
    have s2 : rrun P oracle (xCfg c jD2F ⟨ip.val + 1, by simp at hq; omega⟩ r pre.length) 1 =
        xCfg c (jRB (decide (pre ++ [] = wr))) ⟨ip.val + 1, by simp at hq; omega⟩ r
          ((pre.length : ℤ) - 1) := by
      rw [rrun_one_x P oracle c _ _ r _ cD2F, hD2F, xCfg_read, hcr]
      simp only
      rw [h1]
      simp only [dcmp2Act, and_self, ↓reduceIte]
      rw [apply_xAct]
      have : decide (u₂.head? = none) = decide (pre ++ [] = wr) := by
        rw [e2]; cases u₂ <;> simp
      rw [this]; simp [sub_eq_add_neg]
    refine ⟨1 + 1, pre.length, _, le_rfl, by rw [e2]; simp, by rw [rrun_add, s1, s2], ?_⟩
    intro t ht
    rcases Nat.lt_or_ge t 1 with h | h
    · obtain rfl : t = 0 := by omega
      exact ⟨jD1, ip, _, rfl, cD1, by omega, by rw [e2]; simp⟩
    · obtain rfl : t = 1 := by omega
      exact ⟨jD2F, _, _, s1, cD2F, by omega, by rw [e2]; simp⟩
  | cons b u₁' ih =>
    intro u₂ pre ip e1 e2 hip
    have hlen1 : wi.length = pre.length + 1 + u₁'.length := by rw [e1]; simp; ring
    have h0 : inSym x ip.val = some b := by
      rw [hip, hin _ (by omega), e1]
      rw [List.getElem?_append_left (by simp)]
      simp only [dbl]
      rw [List.flatMap_append, List.getElem?_append_right (by simp; omega)]
      simp [show 2 * pre.length - pre.length * 2 = 0 by omega]
    have h1 : inSym x (ip.val + 1) = some b := by
      rw [hip, show q₀ + 2 * pre.length + 1 = q₀ + (2 * pre.length + 1) by ring,
        hin _ (by omega), e1]
      rw [List.getElem?_append_left (by simp; omega)]
      simp only [dbl]
      rw [List.flatMap_append, List.getElem?_append_right (by simp; omega)]
      simp [show 2 * pre.length + 1 - pre.length * 2 = 1 by omega]
    have s1 : rrun P oracle (xCfg c jD1 ip r pre.length) 1 =
        xCfg c (if b then jD2T else jD2F) ⟨ip.val + 1, by omega⟩ r pre.length := by
      have := reaches_right P oracle (c := c) (p := (pre.length : ℤ)) r jD1
        (if b then jD2T else jD2F) ip.val (by omega) cD1
        (fun w => by rw [hD1, h0]; cases b <;> rfl)
      simpa using this
    have cb : P.call (if b then jD2T else jD2F) = none := by cases b <;> assumption
    have htr2 : ∀ a w, P.tm.tr (if b then jD2T else jD2F) a w = dcmp2Act r jD1 jRB b a (w r) := by
      intro a w; cases b
      · exact hD2F a w
      · exact hD2T a w
    by_cases hc : u₂.head? = some b
    · obtain ⟨u₂', rfl⟩ : ∃ u₂', u₂ = b :: u₂' := by
        cases u₂ with
        | nil => simp at hc
        | cons b' u₂' => simp at hc; exact ⟨u₂', by rw [hc]⟩
      have hcr : c.workTapes r pre.length = some b := by rw [hw, e2]; simp
      have s2 : rrun P oracle (xCfg c (if b then jD2T else jD2F) ⟨ip.val + 1, by omega⟩ r
          pre.length) 1 = xCfg c jD1 ⟨ip.val + 1 + 1, by omega⟩ r (pre ++ [b]).length := by
        rw [rrun_one_x P oracle c _ _ r _ cb, htr2, xCfg_read, hcr]
        simp only
        rw [h1]
        simp only [dcmp2Act]
        rw [if_neg (by cases b <;> simp)]
        simp only [↓reduceIte]
        rw [apply_xAct]
        congr 1
        · exact Fin.ext (by rw [moveInputPos_pos_val _ (by simp; omega)]; try simp)
        · simp
      obtain ⟨T, k, ipk, hk1, hk2, hr, hm⟩ := ih u₂' (pre ++ [b]) ⟨ip.val + 1 + 1, by omega⟩
        (by rw [e1]; simp) (by rw [e2]; simp) (by simp; omega)
      refine ⟨1 + 1 + T, k, ipk, by simp at hk1; omega, hk2, by rw [rrun_add, rrun_add, s1, s2, hr],
        fun t ht => ?_⟩
      rcases Nat.lt_or_ge t (1 + 1) with h | h
      · rcases Nat.lt_or_ge t 1 with h' | h'
        · obtain rfl : t = 0 := by omega
          exact ⟨jD1, ip, _, rfl, cD1, by omega, by rw [e2]; simp; omega⟩
        · obtain rfl : t = 1 := by omega
          exact ⟨_, _, _, s1, cb, by omega, by rw [e2]; simp; omega⟩
      · obtain ⟨t', rfl⟩ : ∃ t', t = 1 + 1 + t' := ⟨t - 2, by omega⟩
        rw [rrun_add, rrun_add, s1, s2]
        exact hm t' (by omega)
    · have hcr : c.workTapes r pre.length = u₂.head? := by rw [hw, e2]; cases u₂ <;> simp
      have hne : decide (wi = wr) = false := by
        rw [e1, e2]; simp; intro h; rw [← h] at hc; simp at hc
      have s2 : rrun P oracle (xCfg c (if b then jD2T else jD2F) ⟨ip.val + 1, by omega⟩ r
          pre.length) 1 = xCfg c (jRB (decide (wi = wr))) ⟨ip.val + 1, by omega⟩ r
            ((pre.length : ℤ) - 1) := by
        rw [rrun_one_x P oracle c _ _ r _ cb, htr2, xCfg_read, hcr]
        simp only
        rw [h1]
        simp only [dcmp2Act]
        rw [if_neg (by cases b <;> simp), if_neg hc, apply_xAct, hne]
        simp [sub_eq_add_neg]
      refine ⟨1 + 1, pre.length, _, le_rfl, by rw [e2]; simp, by rw [rrun_add, s1, s2], ?_⟩
      intro t ht
      rcases Nat.lt_or_ge t 1 with h | h
      · obtain rfl : t = 0 := by omega
        exact ⟨jD1, ip, _, rfl, cD1, by omega, by rw [e2]; simp⟩
      · obtain rfl : t = 1 := by omega
        exact ⟨_, _, _, s1, cb, by omega, by rw [e2]; simp⟩

end DblCmp

/-- Skipping the prefix `1²ⁿ 0 1`.

**Proof sketch.** The input head walks right over the `2n` leading `1`s with the state `jK`,
then over the `0` into `jK2`, which steps over the `1` into `nx` (`reaches_right` then two
single steps). The register head never moves. -/
lemma skipPrefix_run (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (r : Fin m)
    (jK jK2 nx : Λ) (hK : ∀ a w, P.tm.tr jK a w = skipAct r jK jK2 a)
    (hK2 : ∀ a w, P.tm.tr jK2 a w = xAct r 1 0 nx) (cK : P.call jK = none)
    (cK2 : P.call jK2 = none) (c : Cfg m Bool Λ x) (p : ℤ) (n : ℕ) (rest : List Bool)
    (hx : x = List.replicate (2 * n) true ++ [false, true] ++ rest) :
    Reaches P oracle (xCfg c jK ⟨1, by omega⟩ r p)
      (xCfg c nx ⟨3 + 2 * n, by rw [hx]; simp; omega⟩ r p) c r p := by
  have hxl : x.length = 2 * n + 2 + rest.length := by rw [hx]; simp; ring
  have hscan := scanR P oracle c r p (fun _ => jK) 1 (2 * n) (by omega) (fun j hj ww => by
      rw [show 1 + j = j + 1 by ring, inSym_succ, hx, List.append_assoc,
        List.getElem?_append_left (by simp; omega)]
      simp [hj, hK, skipAct])
    (fun j hj => cK)
  have h1 : inSym x (1 + 2 * n) = some false := by
    rw [show 1 + 2 * n = 2 * n + 1 by ring, inSym_succ, hx, List.append_assoc,
      List.getElem?_append_right (by simp)]; simp
  have s1 : rrun P oracle (xCfg c jK ⟨1 + 2 * n, by omega⟩ r p) 1 =
      xCfg c jK2 ⟨1 + 2 * n + 1, by omega⟩ r p :=
    reaches_right P oracle r _ _ (1 + 2 * n) (by omega) cK (fun w => by rw [hK, h1]; rfl)
  have s2 : rrun P oracle (xCfg c jK2 ⟨1 + 2 * n + 1, by omega⟩ r p) 1 =
      xCfg c nx ⟨1 + 2 * n + 1 + 1, by omega⟩ r p :=
    reaches_right P oracle r _ _ (1 + 2 * n + 1) (by omega) cK2 (fun w => hK2 _ w)
  have hr : Reaches P oracle (xCfg c jK ⟨1, by omega⟩ r p) (xCfg c jK ⟨1 + 2 * n, by omega⟩ r p)
      c r p := ⟨2 * n, hscan (2 * n) le_rfl, fun j hj => ⟨jK, _, hscan j hj.le, cK⟩⟩
  have := Reaches.trans P oracle r hr (Reaches.step P oracle r _ _ rfl cK s1
    (Reaches.step P oracle r _ _ rfl cK2 s2 (Reaches.refl P oracle r _ c p)))
  convert this using 3
  omega

/-- A run reaching a configuration with the head of register `r` in `[-1, L]` throughout. -/
def ReachesB (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (c₀ c₁ c : Cfg m Bool Λ x)
    (r : Fin m) (L : ℤ) : Prop :=
  ∃ T, rrun P oracle c₀ T = c₁ ∧
    ∀ t < T, ∃ s ip q, rrun P oracle c₀ t = xCfg c s ip r q ∧ P.call s = none ∧ -1 ≤ q ∧ q ≤ L

/-- A run ending with the register head at `p ∈ [-1, L]` is a run ending with the register
head within `[-1, L]`. -/
lemma Reaches.toB {P : RProg m d Λ} {oracle : Fin d → List Bool → Bool} {c₀ c₁ c : Cfg m Bool Λ x}
    {r : Fin m} {p L : ℤ} (h : Reaches P oracle c₀ c₁ c r p) (hp : -1 ≤ p ∧ p ≤ L) :
    ReachesB P oracle c₀ c₁ c r L := by
  obtain ⟨T, hT, hm⟩ := h
  exact ⟨T, hT, fun t ht => by obtain ⟨s, ip, h1, h2⟩ := hm t ht; exact ⟨s, ip, p, h1, h2, hp⟩⟩

/-- Runs with register heads within `[-1, L]` compose. -/
lemma ReachesB.trans {P : RProg m d Λ} {oracle : Fin d → List Bool → Bool}
    {c₀ c₁ c₂ c : Cfg m Bool Λ x} {r : Fin m} {L : ℤ} (h₁ : ReachesB P oracle c₀ c₁ c r L)
    (h₂ : ReachesB P oracle c₁ c₂ c r L) : ReachesB P oracle c₀ c₂ c r L := by
  obtain ⟨T₁, e1, m1⟩ := h₁
  obtain ⟨T₂, e2, m2⟩ := h₂
  refine ⟨T₁ + T₂, by rw [rrun_add, e1, e2], fun t ht => ?_⟩
  rcases Nat.lt_or_ge t T₁ with h | h
  · exact m1 t h
  · obtain ⟨t', rfl⟩ : ∃ t', t = T₁ + t' := ⟨t - T₁, by omega⟩
    rw [rrun_add, e1]; exact m2 t' (by omega)

/-- Indexing `pre ++ rest` past `pre` indexes `rest`. -/
lemma getElem?_append_len (pre rest : List Bool) (k : ℕ) :
    (pre ++ rest)[pre.length + k]? = rest[k]? := by
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]

section JeqPair

variable (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (r : Fin m)
  (jK jK2 jC : Λ) (jRB jI1 jI2 : Bool → Λ) (yes no : Λ)
  (hK : ∀ a w, P.tm.tr jK a w = skipAct r jK jK2 a)
  (hC : ∀ a w, P.tm.tr jC a w = cmpAct r jC jRB a (w r))
  (hRB : ∀ b a w, P.tm.tr (jRB b) a w = backAct r (jRB b) (jI1 b) (w r))
  (hI1 : ∀ b a w, P.tm.tr (jI1 b) a w = xAct r (-1) 0 (jI2 b))
  (hI2 : ∀ b a w, P.tm.tr (jI2 b) a w = rewAct r (jI2 b) (if b then yes else no) a)
  (cK : P.call jK = none) (cK2 : P.call jK2 = none) (cC : P.call jC = none)
  (cRB : ∀ b, P.call (jRB b) = none) (cI1 : ∀ b, P.call (jI1 b) = none)
  (cI2 : ∀ b, P.call (jI2 b) = none)

include hK hC hRB hI1 hI2 cK cK2 cC cRB cI1 cI2 in
/-- **Comparing a register with the second index of a pair input** `⟨1ⁿ, ⟨u, w⟩⟩`: reach `yes`
if `w = Nat.bits a`, `no` otherwise.

**Proof sketch.** Skip the prefix `1²ⁿ 0 1` (`skipPrefix_run`) and the doubled `u` with its
separator (`pairSkip_run`). Then compare `w` with the register (`cmpPlain_run`), walk the
register head back (`regBack_x`) and rewind the input head (`rewind_x`). -/
lemma jeqPairSnd_run (jP1 jP2F jP2T : Λ)
    (hK2 : ∀ a w, P.tm.tr jK2 a w = xAct r 1 0 jP1)
    (hP1 : ∀ a w, P.tm.tr jP1 a w = pskip1Act r jP2F jP2T a)
    (hP2F : ∀ a w, P.tm.tr jP2F a w = pskip2Act r jP1 jC false a)
    (hP2T : ∀ a w, P.tm.tr jP2T a w = pskip2Act r jP1 jC true a)
    (cP1 : P.call jP1 = none) (cP2F : P.call jP2F = none) (cP2T : P.call jP2T = none)
    (c : Cfg m Bool Λ x) (n : ℕ) (u w : List Bool)
    (hx : x = pairEncode (List.replicate n true) (pairEncode u w)) (a : ℕ)
    (hreg : c.workTapes r = FinTM.bufferTape (Nat.bits a)) :
    ReachesB P oracle (xCfg c jK ⟨1, by omega⟩ r 0)
      (xCfg c (if w = Nat.bits a then yes else no) ⟨1, by omega⟩ r 0) c r (Nat.bits a).length := by
  have hx' : x = List.replicate (2 * n) true ++ [false, true] ++ (dbl u ++ [false, true] ++ w) := by
    rw [hx]; simp [pairEncode_eq_dbl, dbl_replicate]
  have hxl : x.length = 2 * n + 2 + (2 * u.length + 2 + w.length) := by rw [hx']; simp; ring
  have h1 := skipPrefix_run P oracle r jK jK2 jP1 hK hK2 cK cK2 c 0 n _ hx'
  have h2 := pairSkip_run P oracle r jP1 jP2F jP2T jC hP1 hP2F hP2T cP1 cP2F cP2T c 0 u (3 + 2 * n)
    (by omega) (fun k hk => by
      have e : 3 + 2 * n + k = (List.replicate (2 * n) true ++ [false, true]).length + k + 1 := by
        simp; ring
      rw [e, inSym_succ, hx', getElem?_append_len, List.getElem?_append_left (by simp; omega)])
  have hin : ∀ k, inSym x (3 + 2 * n + 2 * u.length + 2 + k) = w[k]? := by
    intro k
    have e : 3 + 2 * n + 2 * u.length + 2 + k = (List.replicate (2 * n) true ++
        [false, true]).length + ((dbl u ++ [false, true]).length + k) + 1 := by simp; ring
    rw [e, inSym_succ, hx', getElem?_append_len, getElem?_append_len]
  obtain ⟨T₃, k, ipk, hipk, -, hk2, hk3, h3, hm3⟩ := cmpPlain_run P oracle r jC jRB hC cC c
    (Nat.bits a) w hreg (3 + 2 * n + 2 * u.length + 2) hin (by omega) w (Nat.bits a) []
    ⟨3 + 2 * n + 2 * u.length + 2, by omega⟩ rfl rfl (by simp)
  obtain ⟨T₄, h4, hm4⟩ := cmpReturn P oracle r jRB jI1 jI2 yes no hRB hI1 hI2 cRB cI1 cI2 c
    (Nat.bits a) hreg (decide (w = Nat.bits a)) ipk k (by omega) (by omega)
  simp only [List.length_nil, Nat.cast_zero, decide_eq_true_eq] at h3 hm3 h4
  have hb : ((-1 : ℤ) ≤ 0 ∧ (0 : ℤ) ≤ (Nat.bits a).length) := ⟨by omega, by omega⟩
  refine ((h1.toB hb).trans (h2.toB hb)).trans ?_
  refine ⟨T₃ + T₄, by rw [rrun_add, h3, h4], fun t ht => ?_⟩
  rcases Nat.lt_or_ge t T₃ with h | h
  · obtain ⟨ip', q, hq, hq1, hq2⟩ := hm3 t h
    exact ⟨jC, ip', q, hq, cC, by omega, hq2⟩
  · obtain ⟨t', rfl⟩ : ∃ t', t = T₃ + t' := ⟨t - T₃, by omega⟩
    rw [rrun_add, h3]
    exact hm4 t' (by omega)

include hK hRB hI1 hI2 cK cK2 cRB cI1 cI2 in
/-- **Comparing a register with the first index of a pair input** `⟨1ⁿ, ⟨u, w⟩⟩`: reach
`yes` if `u = Nat.bits a`, `no` otherwise.

**Proof sketch.** Skip the prefix `1²ⁿ 0 1` (`skipPrefix_run`). Then compare the doubled `u`
with the register (`cmpDbl_run`), walk the register head back (`regBack_x`) and rewind the input
head (`rewind_x`). -/
lemma jeqPairFst_run (jD1 jD2F jD2T : Λ)
    (hK2 : ∀ a w, P.tm.tr jK2 a w = xAct r 1 0 jD1)
    (hD1 : ∀ a w, P.tm.tr jD1 a w = dcmp1Act r jD2F jD2T a)
    (hD2F : ∀ a w, P.tm.tr jD2F a w = dcmp2Act r jD1 jRB false a (w r))
    (hD2T : ∀ a w, P.tm.tr jD2T a w = dcmp2Act r jD1 jRB true a (w r))
    (cD1 : P.call jD1 = none) (cD2F : P.call jD2F = none) (cD2T : P.call jD2T = none)
    (c : Cfg m Bool Λ x) (n : ℕ) (u w : List Bool)
    (hx : x = pairEncode (List.replicate n true) (pairEncode u w)) (a : ℕ)
    (hreg : c.workTapes r = FinTM.bufferTape (Nat.bits a)) :
    ReachesB P oracle (xCfg c jK ⟨1, by omega⟩ r 0)
      (xCfg c (if u = Nat.bits a then yes else no) ⟨1, by omega⟩ r 0) c r (Nat.bits a).length := by
  have hx' : x = List.replicate (2 * n) true ++ [false, true] ++ (dbl u ++ [false, true] ++ w) := by
    rw [hx]; simp [pairEncode_eq_dbl, dbl_replicate]
  have hxl : x.length = 2 * n + 2 + (2 * u.length + 2 + w.length) := by rw [hx']; simp; ring
  have h1 := skipPrefix_run P oracle r jK jK2 jD1 hK hK2 cK cK2 c 0 n _ hx'
  obtain ⟨T₂, k, ipk, -, hk2, h2, hm2⟩ := cmpDbl_run P oracle r jD1 jD2F jD2T jRB hD1 hD2F hD2T
    cD1 cD2F cD2T c (Nat.bits a) hreg u (3 + 2 * n) (by omega) (fun k hk => by
      have e : 3 + 2 * n + k = (List.replicate (2 * n) true ++ [false, true]).length + k + 1 := by
        simp; ring
      rw [e, inSym_succ, hx', getElem?_append_len, List.getElem?_append_left (by simp; omega)])
    u (Nat.bits a) [] ⟨3 + 2 * n, by omega⟩ rfl rfl (by simp)
  have hk0 : (0 : ℤ) ≤ k := by omega
  obtain ⟨T₄, h4, hm4⟩ := cmpReturn P oracle r jRB jI1 jI2 yes no hRB hI1 hI2 cRB cI1 cI2 c
    (Nat.bits a) hreg (decide (u = Nat.bits a)) ipk k hk0 (by omega)
  simp only [List.length_nil, Nat.cast_zero, decide_eq_true_eq] at h2 hm2 h4
  have hb : ((-1 : ℤ) ≤ 0 ∧ (0 : ℤ) ≤ (Nat.bits a).length) := ⟨by omega, by omega⟩
  refine (h1.toB hb).trans ?_
  refine ⟨T₂ + T₄, by rw [rrun_add, h2, h4], fun t ht => ?_⟩
  rcases Nat.lt_or_ge t T₂ with h | h
  · obtain ⟨s', ip', q, hq, hs', hq1, hq2⟩ := hm2 t h
    exact ⟨s', ip', q, hq, hs', by omega, hq2⟩
  · obtain ⟨t', rfl⟩ : ∃ t', t = T₂ + t' := ⟨t - T₂, by omega⟩
    rw [rrun_add, h2]
    exact hm4 t' (by omega)

end JeqPair

end Complexity.LogProg

```


## ===== TCSlib/Complexity/SpaceComplexity/Machines/ARM.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.ParseCmp

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Abstract register machines

Logspace algorithms are usually described with a constant number of counters of logarithmic
size [AB09, §4.1]. An *abstract register machine* (`Complexity.LogProg.ARM`) is a flowchart
over finitely many labels whose registers hold natural numbers, with the instructions:
increment, decrement, clear, halve, zero/parity/equality tests, the input-format checks and
index comparisons of `TCSlib.Complexity.SpaceComplexity.Machines.Parse`, subroutine calls,
and `ret b` (answer `b`). Its semantics (`Complexity.LogProg.astep`) is over values; the
compilation `Complexity.LogProg.armProg` into a register-tape program stores each register
in binary (`Nat.bits`) and implements each instruction by the fragment proved for it.

Related model: `Complexity.CounterProg` (`TCSlib.Complexity.TuringMachine.CounterProg`) is a
goto program over unary counters for the polynomial-time emitters of [AB09, §6.2]. It overlaps
in spirit with the programs here, which store registers in binary (as logarithmic space
requires) and call deciders on virtual inputs; the two are kept separate, and a polynomially
running counter program is simulated by an abstract register machine in
`TCSlib.Complexity.SpaceComplexity.CounterProgSim`.

## Main definitions

* `Complexity.LogProg.Ins`, `Complexity.LogProg.ARM` — instructions and machines.
* `Complexity.LogProg.astep` — the value semantics.
* `Complexity.LogProg.armProg` — the compiled register-tape program.
* `Complexity.LogProg.aseam` — the program configuration of an abstract configuration.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.)
-/

namespace Complexity.LogProg

open Turing

/-- The instructions of an abstract register machine over `m` registers calling `d` deciders,
with labels `Λ`. -/
inductive Ins (m d : ℕ) (Λ : Type) where
  /-- `r := r + 1` -/
  | inc (r : Fin m) (l : Λ)
  /-- `r := r - 1` (truncated) -/
  | dec (r : Fin m) (l : Λ)
  /-- `r := 0` -/
  | clr (r : Fin m) (l : Λ)
  /-- `r := r / 2` -/
  | half (r : Fin m) (l : Λ)
  /-- branch on `r = 0` -/
  | jz (r : Fin m) (l₁ l₀ : Λ)
  /-- branch on `r` odd -/
  | jodd (r : Fin m) (l₁ l₀ : Λ)
  /-- branch on `r = s` (distinct registers) -/
  | jeq (r s : Fin m) (l₁ l₀ : Λ)
  /-- call decider `j` on the virtual input of `mode` and `args` -/
  | call (j : Fin d) (mode : Mode) (args : List (Fin m)) (l₁ l₀ : Λ)
  /-- answer `b` and halt -/
  | ret (b : Bool)
  /-- check that the input is `⟨1ⁿ, w⟩` (else answer `0`); `r` is any register -/
  | valP (r : Fin m) (l : Λ)
  /-- check that the input is `⟨1ⁿ, ⟨u, w⟩⟩` (else answer `0`) -/
  | valQ (r : Fin m) (l : Λ)
  /-- branch on `Nat.bits r = w` for the input `⟨1ⁿ, w⟩` -/
  | jeqIn (r : Fin m) (l₁ l₀ : Λ)
  /-- branch on `Nat.bits r = u` for the input `⟨1ⁿ, ⟨u, w⟩⟩` -/
  | jeqFst (r : Fin m) (l₁ l₀ : Λ)
  /-- branch on `Nat.bits r = w` for the input `⟨1ⁿ, ⟨u, w⟩⟩` -/
  | jeqSnd (r : Fin m) (l₁ l₀ : Λ)

/-- An abstract register machine: an instruction at every label. -/
abbrev ARM (m d : ℕ) (Λ : Type) := Λ → Ins m d Λ

/-- The word `w` of an input `⟨1ⁿ, w⟩`. -/
def plainWord (x : List Bool) : List Bool := x.drop (tRun x + 2)

/-- The words `u`, `w` of an input `⟨1ⁿ, ⟨u, w⟩⟩`. -/
def pairWords (x : List Bool) : List Bool × List Bool :=
  (pairDecode (x.drop (tRun x + 2))).getD ([], [])

/-- The word of the input `⟨1ⁿ, w⟩` is `w`. -/
lemma plainWord_pairEncode (n : ℕ) (w : List Bool) :
    plainWord (pairEncode (List.replicate n true) w) = w := by
  unfold plainWord
  rw [tRun_pairEncode]
  simp [pairEncode_eq_dbl, dbl_replicate, List.drop_append]

/-- The words of the input `⟨1ⁿ, ⟨u, w⟩⟩` are `u` and `w`. -/
lemma pairWords_pairEncode (n : ℕ) (u w : List Bool) :
    pairWords (pairEncode (List.replicate n true) (pairEncode u w)) = (u, w) := by
  have : (pairEncode (List.replicate n true) (pairEncode u w)).drop
      (tRun (pairEncode (List.replicate n true) (pairEncode u w)) + 2) = pairEncode u w := by
    rw [tRun_pairEncode]; simp [pairEncode_eq_dbl, dbl_replicate, List.drop_append]
  simp [pairWords, this, pairDecode_pairEncode]

/-- An abstract configuration: the current label (`none` when halted), the register values,
and the answer once halted. -/
abbrev AConf (m : ℕ) (Λ : Type) := Option Λ × (Fin m → ℕ) × Option Bool

open Classical in
/-- **One step of an abstract register machine** on input `x`, deciders answering `oracle`. -/
noncomputable def astep {m d : ℕ} {Λ : Type} (A : ARM m d Λ) (oracle : Fin d → List Bool → Bool)
    (x : List Bool) : AConf m Λ → AConf m Λ
  | (none, v, res) => (none, v, res)
  | (some l, v, res) =>
    match A l with
    | .inc r l' => (some l', Function.update v r (v r + 1), res)
    | .dec r l' => (some l', Function.update v r (v r - 1), res)
    | .clr r l' => (some l', Function.update v r 0, res)
    | .half r l' => (some l', Function.update v r (v r / 2), res)
    | .jz r l₁ l₀ => (some (if v r = 0 then l₁ else l₀), v, res)
    | .jodd r l₁ l₀ => (some (if v r % 2 = 1 then l₁ else l₀), v, res)
    | .jeq r s l₁ l₀ => (some (if v r = v s then l₁ else l₀), v, res)
    | .call j md args l₁ l₀ =>
      (some (if oracle j (vword (callSegs ⟨j, md, args, l₁, l₀⟩ x (fun r => Nat.bits (v r))))
        then l₁ else l₀), v, res)
    | .ret b => (none, v, some b)
    | .valP _ l' => if ValidPlain x then (some l', v, res) else (none, v, some false)
    | .valQ _ l' => if ValidPair x then (some l', v, res) else (none, v, some false)
    | .jeqIn r l₁ l₀ => (some (if Nat.bits (v r) = plainWord x then l₁ else l₀), v, res)
    | .jeqFst r l₁ l₀ => (some (if Nat.bits (v r) = (pairWords x).1 then l₁ else l₀), v, res)
    | .jeqSnd r l₁ l₀ => (some (if Nat.bits (v r) = (pairWords x).2 then l₁ else l₀), v, res)

/-- The run of an abstract register machine. -/
noncomputable def arun {m d : ℕ} {Λ : Type} (A : ARM m d Λ) (oracle : Fin d → List Bool → Bool)
    (x : List Bool) (a : AConf m Λ) (n : ℕ) : AConf m Λ :=
  (astep A oracle x)^[n] a

/-! ## Compilation -/

/-- The phases of the instruction fragments. -/
inductive Ph where
  | start
  | incB
  | decL | decE | decB
  | clrE
  | h0 | hF | hT
  | eqBy | eqBn
  | vU1 | vS | vW0 | vWF | vWT | vrw1 | vrw2
  | vP1 (l : Option Bool) | vP2 (b : Bool) (l : Option Bool)
  | jK2 | jC | jRB (b : Bool) | jI1 (b : Bool) | jI2 (b : Bool)
  | jP1 | jP2F | jP2T | jD1 | jD2F | jD2T
  deriving DecidableEq, Fintype

/-- A control action: change state, move nothing. -/
def goAct {m : ℕ} {S : Type} (s : S) : Action m Bool S := ⟨0, fun _ => (none, 0), none, some s⟩

/-- Halt with output `b`. -/
def retAct {m : ℕ} {S : Type} (b : Bool) : Action m Bool S := ⟨0, fun _ => (none, 0), some b, none⟩

/-- The input rewind scan (moving nothing else): left over symbols, then right into `nx`. -/
def rw2Act {m : ℕ} {S : Type} (r : Fin m) (s₀ nx : S) (a : Option Bool) : Action m Bool S :=
  match a with
  | some _ => xAct r (-1) 0 s₀
  | none => xAct r 1 0 nx

/-- The halting junk action. -/
def junkAct {m : ℕ} {S : Type} : Action m Bool S := ⟨0, fun _ => (none, 0), none, none⟩

/-- **The transition table of one instruction's fragment**: phase `start` is the fragment's
first state. -/
def insTr {m d : ℕ} {Λ : Type} (i : Ins m d Λ) (l : Λ) (ph : Ph) (a : Option Bool)
    (w : Fin m → Option Bool) : Action m Bool (Λ × Ph) :=
  match i with
  | .inc r l' =>
    match ph with
    | .start => incCAct r (l, .start) (l, .incB) (w r)
    | .incB => incBAct r (l, .incB) (l', .start) (w r)
    | _ => junkAct
  | .dec r l' =>
    match ph with
    | .start => decDAct r (l, .start) (l, .decL) (l, .decB) (w r)
    | .decL => decLAct r (l, .decE) (l, .decB) (w r)
    | .decE => decEAct r (l, .decB)
    | .decB => incBAct r (l, .decB) (l', .start) (w r)
    | _ => junkAct
  | .clr r l' =>
    match ph with
    | .start => toEndAct r (l, .start) (l, .clrE) (w r)
    | .clrE => clrEAct r (l, .clrE) (l', .start) (w r)
    | _ => junkAct
  | .half r l' =>
    match ph with
    | .start => toEndAct r (l, .start) (l, .h0) (w r)
    | .h0 => halfLAct r none (l, .hF) (l, .hT) (l', .start) (w r)
    | .hF => halfLAct r (some false) (l, .hF) (l, .hT) (l', .start) (w r)
    | .hT => halfLAct r (some true) (l, .hF) (l, .hT) (l', .start) (w r)
    | _ => junkAct
  | .jz r l₁ l₀ =>
    match ph with
    | .start => goAct (if w r = none then (l₁, .start) else (l₀, .start))
    | _ => junkAct
  | .jodd r l₁ l₀ =>
    match ph with
    | .start => goAct (if w r = some true then (l₁, .start) else (l₀, .start))
    | _ => junkAct
  | .jeq r s l₁ l₀ =>
    match ph with
    | .start => eqCAct r s (l, .start) (l, .eqBy) (l, .eqBn) (w r) (w s)
    | .eqBy => eqBAct r s (l, .eqBy) (l₁, .start) (w r)
    | .eqBn => eqBAct r s (l, .eqBn) (l₀, .start) (w r)
    | _ => junkAct
  | .call _ _ _ _ _ => junkAct
  | .ret b =>
    match ph with
    | .start => retAct b
    | _ => junkAct
  | .valP r l' =>
    match ph with
    | .start => valUAct r (l, .start) (l, .vU1) (l, .vS) false a
    | .vU1 => valUAct r (l, .start) (l, .vU1) (l, .vS) true a
    | .vS => valSAct r (l, .vW0) a
    | .vW0 => valWAct r (l, .vWF) (l, .vWT) (l, .vrw1) none a
    | .vWF => valWAct r (l, .vWF) (l, .vWT) (l, .vrw1) (some false) a
    | .vWT => valWAct r (l, .vWF) (l, .vWT) (l, .vrw1) (some true) a
    | .vrw1 => xAct r (-1) 0 (l, .vrw2)
    | .vrw2 => rw2Act r (l, .vrw2) (l', .start) a
    | _ => junkAct
  | .valQ r l' =>
    match ph with
    | .start => valUAct r (l, .start) (l, .vU1) (l, .vS) false a
    | .vU1 => valUAct r (l, .start) (l, .vU1) (l, .vS) true a
    | .vS => valSAct r (l, .vP1 none) a
    | .vP1 lst => valP1Act r (fun b => (l, .vP2 b lst)) a
    | .vP2 b lst => valP2Act r (l, .vP1 (some false)) (l, .vP1 (some true)) (l, .vW0) lst b a
    | .vW0 => valWAct r (l, .vWF) (l, .vWT) (l, .vrw1) none a
    | .vWF => valWAct r (l, .vWF) (l, .vWT) (l, .vrw1) (some false) a
    | .vWT => valWAct r (l, .vWF) (l, .vWT) (l, .vrw1) (some true) a
    | .vrw1 => xAct r (-1) 0 (l, .vrw2)
    | .vrw2 => rw2Act r (l, .vrw2) (l', .start) a
    | _ => junkAct
  | .jeqIn r l₁ l₀ =>
    match ph with
    | .start => skipAct r (l, .start) (l, .jK2) a
    | .jK2 => xAct r 1 0 (l, .jC)
    | .jC => cmpAct r (l, .jC) (fun b => (l, .jRB b)) a (w r)
    | .jRB b => backAct r (l, .jRB b) (l, .jI1 b) (w r)
    | .jI1 b => xAct r (-1) 0 (l, .jI2 b)
    | .jI2 b => rewAct r (l, .jI2 b) (if b then (l₁, .start) else (l₀, .start)) a
    | _ => junkAct
  | .jeqSnd r l₁ l₀ =>
    match ph with
    | .start => skipAct r (l, .start) (l, .jK2) a
    | .jK2 => xAct r 1 0 (l, .jP1)
    | .jP1 => pskip1Act r (l, .jP2F) (l, .jP2T) a
    | .jP2F => pskip2Act r (l, .jP1) (l, .jC) false a
    | .jP2T => pskip2Act r (l, .jP1) (l, .jC) true a
    | .jC => cmpAct r (l, .jC) (fun b => (l, .jRB b)) a (w r)
    | .jRB b => backAct r (l, .jRB b) (l, .jI1 b) (w r)
    | .jI1 b => xAct r (-1) 0 (l, .jI2 b)
    | .jI2 b => rewAct r (l, .jI2 b) (if b then (l₁, .start) else (l₀, .start)) a
    | _ => junkAct
  | .jeqFst r l₁ l₀ =>
    match ph with
    | .start => skipAct r (l, .start) (l, .jK2) a
    | .jK2 => xAct r 1 0 (l, .jD1)
    | .jD1 => dcmp1Act r (l, .jD2F) (l, .jD2T) a
    | .jD2F => dcmp2Act r (l, .jD1) (fun b => (l, .jRB b)) false a (w r)
    | .jD2T => dcmp2Act r (l, .jD1) (fun b => (l, .jRB b)) true a (w r)
    | .jRB b => backAct r (l, .jRB b) (l, .jI1 b) (w r)
    | .jI1 b => xAct r (-1) 0 (l, .jI2 b)
    | .jI2 b => rewAct r (l, .jI2 b) (if b then (l₁, .start) else (l₀, .start)) a
    | _ => junkAct

/-- The transition table of the compiled program. -/
def armTr {m d : ℕ} {Λ : Type} (A : ARM m d Λ) (l : Λ) (ph : Ph) (a : Option Bool)
    (w : Fin m → Option Bool) : Action m Bool (Λ × Ph) :=
  insTr (A l) l ph a w

/-- The call node of one instruction. -/
def insCall {m d : ℕ} {Λ : Type} (i : Ins m d Λ) (ph : Ph) : Option (CallSpec m d (Λ × Ph)) :=
  match i with
  | .call j md args l₁ l₀ =>
    match ph with
    | .start => some ⟨j, md, args, (l₁, .start), (l₀, .start)⟩
    | _ => none
  | _ => none

/-- The call nodes of the compiled program. -/
def armCall {m d : ℕ} {Λ : Type} (A : ARM m d Λ) (q : Λ × Ph) :
    Option (CallSpec m d (Λ × Ph)) :=
  insCall (A q.1) q.2

/-- **The compiled register-tape program** of an abstract register machine. -/
def armProg {m d : ℕ} {Λ : Type} (A : ARM m d Λ) (l₀ : Λ) : RProg m d (Λ × Ph) where
  tm := ⟨(l₀, .start), fun q a w => armTr A q.1 q.2 a w⟩
  call := armCall A

/-- The program configuration representing the abstract configuration at label `l` with
values `v`, having written `out`. -/
def aseam {m : ℕ} {Λ : Type} (x : List Bool) (l : Λ) (v : Fin m → ℕ) (out : List Bool) :
    Cfg m Bool (Λ × Ph) x :=
  ⟨some (l, .start), ⟨1, by omega⟩, fun r => FinTM.bufferTape (Nat.bits (v r)), fun _ => 0, out⟩

end Complexity.LogProg

```


## ===== TCSlib/Complexity/SpaceComplexity/Machines/ARMSim.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.ARM

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Simulating abstract register machines

Each instruction of an abstract register machine (`Complexity.LogProg.ARM`) is simulated by its
fragment in the compiled program (`Complexity.LogProg.armProg`): from the representation
`Complexity.LogProg.aseam` of an abstract configuration the program reaches the
representation of the next one (or halts with the answer), through ordinary states, every
register head in `[-1, W]` when `W` bounds the binary lengths of the values involved.

## Main definitions

* `Complexity.LogProg.Mid` — an ordinary configuration with register heads in `[-1, W]`.
* `Complexity.LogProg.Pre` — the preconditions of an abstract step (distinct registers in
  equality tests, valid inputs for index comparisons, distinct call arguments).

## Main results

* `Complexity.LogProg.arm_step` — one abstract step is simulated.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.)
-/

namespace Complexity.LogProg

open Turing

variable {m d : ℕ} {Λ : Type} {x : List Bool}

/-- An ordinary configuration (not at a call node) with every register head in `[-1, W]`. -/
def Mid (P : RProg m d (Λ × Ph)) (W : ℤ) (c : Cfg m Bool (Λ × Ph) x) : Prop :=
  (∀ s, c.state = some s → P.call s = none) ∧
    ∀ r, -1 ≤ c.workTapePos r ∧ c.workTapePos r ≤ W

/-- The transitions of the compiled program at label `l` are those of the instruction `A l`. -/
lemma armProg_tr (A : ARM m d Λ) (l₀ l : Λ) (ph : Ph) (a : Option Bool) (w : Fin m → Option Bool) :
    (armProg A l₀).tm.tr (l, ph) a w = insTr (A l) l ph a w := rfl

/-- The call nodes of the compiled program at label `l` are those of the instruction `A l`. -/
lemma armProg_call (A : ARM m d Λ) (l₀ l : Λ) (ph : Ph) :
    (armProg A l₀).call (l, ph) = insCall (A l) ph := rfl

/-- The program configuration of values `v` is the register-`r` view of itself, with register
`r` holding the binary word of `v r` and the head at its first cell. -/
lemma aseam_eq_regCfg (l : Λ) (v : Fin m → ℕ) (out : List Bool) (r : Fin m) :
    aseam x l v out = regCfg (aseam x l v out) (l, .start) r
      (FinTM.bufferTape (Nat.bits (v r))) 0 := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext r'; by_cases h : r' = r
    · subst h; simp [regCfg, aseam]
    · simp [regCfg, aseam]
  · funext r'; by_cases h : r' = r
    · subst h; simp [regCfg, aseam]
    · simp [regCfg, aseam]

/-- Writing the binary word of `n` into register `r` of the program configuration at `l`, with
the head back at the first cell, gives the program configuration at `l'` with `v r` set to
`n`. -/
lemma regCfg_aseam (l l' : Λ) (v : Fin m → ℕ) (out : List Bool) (r : Fin m) (n : ℕ) :
    regCfg (aseam x l v out) (l', .start) r (FinTM.bufferTape (Nat.bits n)) 0 =
      aseam x l' (Function.update v r n) out := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext r'; by_cases h : r' = r
    · subst h; simp [regCfg, aseam]
    · simp [regCfg, aseam, h]
  · funext r'; by_cases h : r' = r
    · subst h; simp [regCfg, aseam]
    · simp [regCfg, aseam]

/-- A register view of a program configuration, in a non-call phase with the register head
within the register's range, is in the middle of an instruction fragment. -/
lemma mid_regCfg (A : ARM m d Λ) (l₀ : Λ) (l : Λ) (v : Fin m → ℕ) (out : List Bool) (r : Fin m)
    (s : Λ × Ph) (f : ℤ → Option Bool) (q W : ℤ) (hs : (armProg A l₀).call s = none)
    (hq : -1 ≤ q ∧ q ≤ W) (hW : 0 ≤ W) :
    Mid (armProg A l₀) W (regCfg (aseam x l v out) s r f q) := by
  refine ⟨fun s' h => ?_, fun r' => ?_⟩
  · simp only [regCfg, Option.some.injEq] at h; rw [← h]; exact hs
  · by_cases h : r' = r
    · subst h; simpa [regCfg] using hq
    · simp [regCfg, aseam, h]; omega

/-- An input-scanning view of a program configuration, in a non-call phase with the register
head within the register's range, is in the middle of an instruction fragment. -/
lemma mid_xCfg (A : ARM m d Λ) (l₀ : Λ) (l : Λ) (v : Fin m → ℕ) (out : List Bool) (r : Fin m)
    (s : Λ × Ph) (ip : Fin (x.length + 2)) (q W : ℤ) (hs : (armProg A l₀).call s = none)
    (hq : -1 ≤ q ∧ q ≤ W) (hW : 0 ≤ W) :
    Mid (armProg A l₀) W (xCfg (aseam x l v out) s ip r q) := by
  refine ⟨fun s' h => ?_, fun r' => ?_⟩
  · simp only [xCfg, Option.some.injEq] at h; rw [← h]; exact hs
  · by_cases h : r' = r
    · subst h; simpa [xCfg] using hq
    · simp [xCfg, aseam, h]; omega

/-- The input-scanning view of a program configuration with the input head at the first cell
and the register head at `0` is the program configuration at the new label. -/
lemma xCfg_aseam (l l' : Λ) (v : Fin m → ℕ) (out : List Bool) (r : Fin m) :
    xCfg (aseam x l v out) (l', .start) ⟨1, by omega⟩ r 0 = aseam x l' v out := by
  refine Cfg.ext rfl rfl rfl ?_ rfl
  funext r'; by_cases h : r' = r
  · subst h; simp [xCfg, aseam]
  · simp [xCfg, aseam]

/-- A program configuration is its own input-scanning view at the first input cell. -/
lemma xCfg_aseam_self (l : Λ) (v : Fin m → ℕ) (out : List Bool) (r : Fin m) :
    aseam x l v out = xCfg (aseam x l v out) (l, .start) ⟨1, by omega⟩ r 0 :=
  (xCfg_aseam l l v out r).symm

/-- The two-register view of a program configuration with both heads at `0` is the program
configuration at the new label. -/
lemma eqCfg_aseam (l l' : Λ) (v : Fin m → ℕ) (out : List Bool) (r s : Fin m) :
    eqCfg (aseam x l v out) (l', .start) r s 0 = aseam x l' v out := by
  refine Cfg.ext rfl rfl rfl ?_ rfl
  funext r'
  simp only [eqCfg, aseam, Function.update_apply]
  split_ifs <;> rfl

/-- A simulated run from `c` to `c'` through `Mid` configurations. -/
def SimTo (P : RProg m d (Λ × Ph)) (oracle : Fin d → List Bool → Bool) (W : ℤ)
    (c c' : Cfg m Bool (Λ × Ph) x) : Prop :=
  ∃ T, rrun P oracle c T = c' ∧ ∀ t < T, Mid P W (rrun P oracle c t)

/-- A simulated run from `c` that halts with output `c.output ++ [b]`. -/
def HaltsWith (P : RProg m d (Λ × Ph)) (oracle : Fin d → List Bool → Bool) (W : ℤ)
    (c : Cfg m Bool (Λ × Ph) x) (b : Bool) : Prop :=
  ∃ T, (rrun P oracle c T).state = none ∧ (rrun P oracle c T).output = c.output ++ [b] ∧
    (∀ r, -1 ≤ (rrun P oracle c T).workTapePos r ∧ (rrun P oracle c T).workTapePos r ≤ W) ∧
    ∀ t < T, Mid P W (rrun P oracle c t)

section Steps

variable (A : ARM m d Λ) (l₀ : Λ) (oracle : Fin d → List Bool → Bool)

/-- **Simulating `inc r`**: the compiled increment fragment takes the program configuration at `l`
to the one at `l'` with `v r` replaced by `v r + 1`, the register head within `[-1, W]`.

**Proof sketch.** Apply `inc_run` to register `r` holding `bits (v r)`; its end view is the
program configuration at `l'` with `bits (v r + 1)` written (`regCfg_aseam`), and its
intermediate views are register views with the head in range, hence in the middle of a fragment
(`mid_regCfg`). -/
lemma sim_inc (l l' : Λ) (r : Fin m) (hA : A l = .inc r l') (v : Fin m → ℕ) (out : List Bool)
    (W : ℤ) (hW : ((Nat.bits (v r + 1)).length : ℤ) ≤ W) :
    SimTo (armProg A l₀) oracle W (aseam x l v out)
      (aseam x l' (Function.update v r (v r + 1)) out) := by
  obtain ⟨T, h1, hm⟩ := inc_run (armProg A l₀) oracle r (l, .start) (l, .incB) (l', .start)
    (fun a w => by rw [armProg_tr, hA]; rfl) (fun a w => by rw [armProg_tr, hA]; rfl)
    (by rw [armProg_call, hA]; rfl) (by rw [armProg_call, hA]; rfl) (aseam x l v out) (v r)
  rw [← aseam_eq_regCfg, regCfg_aseam] at h1
  refine ⟨T, h1, fun t ht => ?_⟩
  obtain ⟨s, f, q, hq, hs, hq1, hq2⟩ := hm t ht
  rw [← aseam_eq_regCfg] at hq
  rw [hq]
  exact mid_regCfg A l₀ l v out r s f q W
    (by rcases hs with rfl | rfl <;> (rw [armProg_call, hA]; rfl)) ⟨hq1, hq2.trans hW⟩
    (by omega)

/-- **Simulating `dec r`**: the compiled decrement fragment takes the program configuration at `l`
to the one at `l'` with `v r` replaced by `v r - 1`, the register head within `[-1, W]`.

**Proof sketch.** Apply `dec_run` to register `r` holding `bits (v r)`; its end view is the
program configuration at `l'` with `bits (v r - 1)` written (`regCfg_aseam`), and its
intermediate views are register views with the head in range, hence in the middle of a fragment
(`mid_regCfg`). -/
lemma sim_dec (l l' : Λ) (r : Fin m) (hA : A l = .dec r l') (v : Fin m → ℕ) (out : List Bool)
    (W : ℤ) (hW : ((Nat.bits (v r)).length : ℤ) ≤ W) :
    SimTo (armProg A l₀) oracle W (aseam x l v out)
      (aseam x l' (Function.update v r (v r - 1)) out) := by
  obtain ⟨T, h1, hm⟩ := dec_run (armProg A l₀) oracle r (l, .start) (l, .decL) (l, .decE)
    (l, .decB) (l', .start) (fun a w => by rw [armProg_tr, hA]; rfl)
    (fun a w => by rw [armProg_tr, hA]; rfl) (fun a w => by rw [armProg_tr, hA]; rfl)
    (fun a w => by rw [armProg_tr, hA]; rfl) (by rw [armProg_call, hA]; rfl)
    (by rw [armProg_call, hA]; rfl) (by rw [armProg_call, hA]; rfl)
    (by rw [armProg_call, hA]; rfl) (aseam x l v out) (v r)
  rw [← aseam_eq_regCfg, regCfg_aseam] at h1
  refine ⟨T, h1, fun t ht => ?_⟩
  obtain ⟨s, f, q, hq, hs, hq1, hq2⟩ := hm t ht
  rw [← aseam_eq_regCfg] at hq
  rw [hq]
  exact mid_regCfg A l₀ l v out r s f q W hs ⟨hq1, hq2.trans hW⟩ (by omega)

/-- **Simulating `clr r`**: the compiled clear fragment takes the program configuration at `l` to
the one at `l'` with `v r` replaced by `0`, the register head within `[-1, W]`.

**Proof sketch.** Apply `clr_run` to register `r` holding `bits (v r)`; its end view is the
program configuration at `l'` with the empty word `bits 0` (`regCfg_aseam`), and its
intermediate views are register views with the head in range, hence in the middle of a fragment
(`mid_regCfg`). -/
lemma sim_clr (l l' : Λ) (r : Fin m) (hA : A l = .clr r l') (v : Fin m → ℕ) (out : List Bool)
    (W : ℤ) (hW : ((Nat.bits (v r)).length : ℤ) ≤ W) :
    SimTo (armProg A l₀) oracle W (aseam x l v out) (aseam x l' (Function.update v r 0) out) := by
  obtain ⟨T, h1, hm⟩ := clr_run (armProg A l₀) oracle r (l, .start) (l, .clrE) (l', .start)
    (fun a w => by rw [armProg_tr, hA]; rfl) (fun a w => by rw [armProg_tr, hA]; rfl)
    (by rw [armProg_call, hA]; rfl) (by rw [armProg_call, hA]; rfl) (aseam x l v out) (v r)
  rw [← aseam_eq_regCfg, regCfg_aseam] at h1
  refine ⟨T, h1, fun t ht => ?_⟩
  obtain ⟨s, f, q, hq, hs, hq1, hq2⟩ := hm t ht
  rw [← aseam_eq_regCfg] at hq
  rw [hq]
  exact mid_regCfg A l₀ l v out r s f q W hs ⟨hq1, hq2.trans hW⟩ (by omega)

/-- **Simulating `half r`**: the compiled halving fragment takes the program configuration at `l` to
the one at `l'` with `v r` replaced by `v r / 2`, the register head within `[-1, W]`.

**Proof sketch.** Apply `half_run` to register `r` holding `bits (v r)`; its end view is the
program configuration at `l'` with `bits (v r / 2)` written (`regCfg_aseam`), and its
intermediate views are register views with the head in range, hence in the middle of a fragment
(`mid_regCfg`). -/
lemma sim_half (l l' : Λ) (r : Fin m) (hA : A l = .half r l') (v : Fin m → ℕ) (out : List Bool)
    (W : ℤ) (hW : ((Nat.bits (v r)).length : ℤ) ≤ W) :
    SimTo (armProg A l₀) oracle W (aseam x l v out)
      (aseam x l' (Function.update v r (v r / 2)) out) := by
  obtain ⟨T, h1, hm⟩ := half_run (armProg A l₀) oracle r (l, .start) (l, .h0) (l, .hF) (l, .hT)
    (l', .start) (fun a w => by rw [armProg_tr, hA]; rfl)
    (fun a w => by rw [armProg_tr, hA]; rfl) (fun a w => by rw [armProg_tr, hA]; rfl)
    (fun a w => by rw [armProg_tr, hA]; rfl) (by rw [armProg_call, hA]; rfl)
    (by rw [armProg_call, hA]; rfl) (by rw [armProg_call, hA]; rfl)
    (by rw [armProg_call, hA]; rfl) (aseam x l v out) (v r)
  rw [← aseam_eq_regCfg, regCfg_aseam] at h1
  refine ⟨T, h1, fun t ht => ?_⟩
  obtain ⟨s, f, q, hq, hs, hq1, hq2⟩ := hm t ht
  rw [← aseam_eq_regCfg] at hq
  rw [hq]
  exact mid_regCfg A l₀ l v out r s f q W hs ⟨hq1, hq2.trans hW⟩ (by omega)

/-- A one-step control transition between seams. -/
lemma sim_go (l : Λ) (v : Fin m → ℕ) (out : List Bool) (W : ℤ) (hW : 0 ≤ W) (target : Λ)
    (hc : (armProg A l₀).call (l, .start) = none)
    (htr : ∀ a, (armProg A l₀).tm.tr (l, .start) a
      (fun r => FinTM.bufferTape (Nat.bits (v r)) 0) = goAct (target, .start)) :
    SimTo (armProg A l₀) oracle W (aseam x l v out) (aseam x target v out) := by
  refine ⟨1, ?_, fun t ht => ?_⟩
  · rw [rrun_one, rstep_noncall _ oracle _ (l, .start) rfl hc]
    unfold MultiTapeTM.step
    have hw : (aseam x l v out).workTapeSymbols = fun r => FinTM.bufferTape (Nat.bits (v r)) 0 := by
      funext r; simp [aseam, Cfg.workTapeSymbols]
    simp only [aseam]
    rw [show (⟨some (l, Ph.start), ⟨1, by omega⟩, fun r => FinTM.bufferTape (Nat.bits (v r)),
      fun _ => 0, out⟩ : Cfg m Bool (Λ × Ph) x) = aseam x l v out from rfl, hw, htr]
    simp [goAct, Action.apply, aseam]
  · obtain rfl : t = 0 := by omega
    refine ⟨fun s h => ?_, fun r => ?_⟩
    · simp [rrun_zero, aseam] at h; rw [← h]; exact hc
    · simp [rrun_zero, aseam]; omega

/-- **Simulating `jz r`**: one step takes the program configuration at `l` to the one at `l₁` if `v
r = 0` and at `l₀'` otherwise. -/
lemma sim_jz (l l₁ l₀' : Λ) (r : Fin m) (hA : A l = .jz r l₁ l₀') (v : Fin m → ℕ)
    (out : List Bool) (W : ℤ) (hW : 0 ≤ W) :
    SimTo (armProg A l₀) oracle W (aseam x l v out)
      (aseam x (if v r = 0 then l₁ else l₀') v out) := by
  refine sim_go A l₀ oracle l v out W hW _ (by rw [armProg_call, hA]; rfl) (fun a => ?_)
  rw [armProg_tr, hA]
  simp only [insTr]
  congr 2
  have : FinTM.bufferTape (Nat.bits (v r)) 0 = (Nat.bits (v r)).head? := by
    simp [FinTM.bufferTape, List.head?_eq_getElem?]
  simp only [this, bits_head_odd]
  by_cases h : v r = 0 <;> simp [h]

/-- **Simulating `jodd r`**: one step takes the program configuration at `l` to the one at `l₁` if
`v r` is odd and at `l₀'` otherwise. -/
lemma sim_jodd (l l₁ l₀' : Λ) (r : Fin m) (hA : A l = .jodd r l₁ l₀') (v : Fin m → ℕ)
    (out : List Bool) (W : ℤ) (hW : 0 ≤ W) :
    SimTo (armProg A l₀) oracle W (aseam x l v out)
      (aseam x (if v r % 2 = 1 then l₁ else l₀') v out) := by
  refine sim_go A l₀ oracle l v out W hW _ (by rw [armProg_call, hA]; rfl) (fun a => ?_)
  rw [armProg_tr, hA]
  simp only [insTr]
  congr 2
  have : FinTM.bufferTape (Nat.bits (v r)) 0 = (Nat.bits (v r)).head? := by
    simp [FinTM.bufferTape, List.head?_eq_getElem?]
  simp only [this, bits_head_odd]
  by_cases h : v r = 0
  · simp [h]
  · by_cases h' : v r % 2 = 1 <;> simp [h, h']

/-- **Simulating `jeq r s`**: the compiled equality fragment takes the program configuration at `l`
to the one at `l₁` if `v r = v s` and at `l₀'` otherwise, registers unchanged, register heads
within `[-1, W]`.

**Proof sketch.** Unfold the compiled instruction to the two-register comparison fragment and
apply `eq_run` with the binary words of `v r` and `v s` on the two registers; its final view at
the outcome label is the program configuration there (`eqCfg_aseam`), and its intermediate views
are in the middle of a fragment (`Mid`). -/
lemma sim_jeq (l l₁ l₀' : Λ) (r s : Fin m) (hrs : r ≠ s) (hA : A l = .jeq r s l₁ l₀')
    (v : Fin m → ℕ) (out : List Bool) (W : ℤ) (hW : ((Nat.bits (v r)).length : ℤ) ≤ W) :
    SimTo (armProg A l₀) oracle W (aseam x l v out)
      (aseam x (if v r = v s then l₁ else l₀') v out) := by
  obtain ⟨T, h1, hm⟩ := eq_run (armProg A l₀) oracle r s hrs (l, .start) (l, .eqBy) (l, .eqBn)
    (l₁, .start) (l₀', .start) (fun a w => by rw [armProg_tr, hA]; rfl)
    (fun a w => by rw [armProg_tr, hA]; rfl) (fun a w => by rw [armProg_tr, hA]; rfl)
    (by rw [armProg_call, hA]; rfl) (by rw [armProg_call, hA]; rfl)
    (by rw [armProg_call, hA]; rfl) (aseam x l v out) (v r) (v s) rfl rfl
  have e0 : eqCfg (aseam x l v out) (l, .start) r s 0 = aseam x l v out := eqCfg_aseam l l v out r s
  rw [e0] at h1 hm
  have e1 : eqCfg (aseam x l v out) (if v r = v s then (l₁, Ph.start) else (l₀', Ph.start)) r s 0 =
      aseam x (if v r = v s then l₁ else l₀') v out := by
    split_ifs <;> exact eqCfg_aseam _ _ v out r s
  rw [e1] at h1
  refine ⟨T, h1, fun t ht => ?_⟩
  obtain ⟨st, q, hq, hs, hq1, hq2⟩ := hm t ht
  rw [hq]
  refine ⟨fun s' h => ?_, fun r' => ?_⟩
  · simp only [eqCfg, Option.some.injEq] at h; rw [← h]; exact hs
  · simp only [eqCfg, aseam, Function.update_apply]
    split_ifs <;> omega

/-- **Simulating `call`**: one step of the program at a call node takes the program configuration at
`l` to the one at `l₁` if the decider accepts the virtual input built from the input and the
argument registers' words, and at `l₀'` otherwise. -/
lemma sim_call (l l₁ l₀' : Λ) (j : Fin d) (md : Mode) (args : List (Fin m))
    (hA : A l = .call j md args l₁ l₀') (v : Fin m → ℕ) (out : List Bool) :
    rrun (armProg A l₀) oracle (aseam x l v out) 1 =
      aseam x (if oracle j (vword (callSegs ⟨j, md, args, l₁, l₀'⟩ x (fun r => Nat.bits (v r))))
        then l₁ else l₀') v out := by
  rw [rrun_one]
  have hc : (armProg A l₀).call (l, .start) = some ⟨j, md, args, (l₁, .start), (l₀', .start)⟩ := by
    rw [armProg_call, hA]; rfl
  have hw : regWords (aseam x l v out) = fun r => Nat.bits (v r) := by
    funext r; simp [regWords, aseam, tapeWord_bufferTape]
  simp only [rstep, aseam, hc]
  rw [show (⟨some (l, Ph.start), ⟨1, by omega⟩, fun r => FinTM.bufferTape (Nat.bits (v r)),
      fun _ => 0, out⟩ : Cfg m Bool (Λ × Ph) x) = aseam x l v out from rfl, hw]
  have hseg : callSegs (⟨j, md, args, (l₁, Ph.start), (l₀', Ph.start)⟩ : CallSpec m d (Λ × Ph)) x
      (fun r => Nat.bits (v r)) = callSegs ⟨j, md, args, l₁, l₀'⟩ x (fun r => Nat.bits (v r)) := rfl
  rw [hseg]
  split_ifs <;> rfl

/-- **Simulating `ret b`**: one step from the program configuration at `l` halts with `b` appended
to the output, the register heads at `0`. -/
lemma sim_ret (l : Λ) (b : Bool) (hA : A l = .ret b) (v : Fin m → ℕ) (out : List Bool) (W : ℤ)
    (hW : 0 ≤ W) : HaltsWith (armProg A l₀) oracle W (aseam x l v out) b := by
  have hc : (armProg A l₀).call (l, .start) = none := by rw [armProg_call, hA]; rfl
  have h1 : rrun (armProg A l₀) oracle (aseam x l v out) 1 =
      ⟨none, ⟨1, by omega⟩, fun r => FinTM.bufferTape (Nat.bits (v r)), fun _ => 0, out ++ [b]⟩ := by
    rw [rrun_one, rstep_noncall _ oracle _ (l, .start) rfl hc]
    unfold MultiTapeTM.step
    simp only [aseam]
    rw [armProg_tr, hA]
    simp [insTr, retAct, Action.apply]
  refine ⟨1, by rw [h1], by rw [h1]; rfl, fun r => by rw [h1]; simp; omega, fun t ht => ?_⟩
  obtain rfl : t = 0 := by omega
  refine ⟨fun s h => ?_, fun r => ?_⟩
  · simp [rrun_zero, aseam] at h; rw [← h]; exact hc
  · simp [rrun_zero, aseam]; omega

/-- A rejecting xCfg run is a halting simulated run. -/
lemma haltsWith_of_rejects (l : Λ) (v : Fin m → ℕ) (out : List Bool) (r : Fin m) (W : ℤ)
    (hW : 0 ≤ W) (h : Rejects (armProg A l₀) oracle (aseam x l v out) (aseam x l v out) r 0) :
    HaltsWith (armProg A l₀) oracle W (aseam x l v out) false := by
  obtain ⟨T, e1, e2, e3, hm⟩ := h
  refine ⟨T, e1, e2, fun r' => ?_, fun t ht => ?_⟩
  · rw [e3]; simp only [aseam, Function.update_apply]; split_ifs <;> omega
  · obtain ⟨s, ip, hs, hc⟩ := hm t ht
    rw [hs]; exact mid_xCfg A l₀ l v out r s ip 0 W hc ⟨by omega, hW⟩ hW

/-- A reaching xCfg run is a simulated run. -/
lemma simTo_of_reaches (l l' : Λ) (v : Fin m → ℕ) (out : List Bool) (r : Fin m) (W : ℤ)
    (hW : 0 ≤ W)
    (h : Reaches (armProg A l₀) oracle (aseam x l v out) (aseam x l' v out) (aseam x l v out) r 0) :
    SimTo (armProg A l₀) oracle W (aseam x l v out) (aseam x l' v out) := by
  obtain ⟨T, e1, hm⟩ := h
  refine ⟨T, e1, fun t ht => ?_⟩
  obtain ⟨s, ip, hs, hc⟩ := hm t ht
  rw [hs]; exact mid_xCfg A l₀ l v out r s ip 0 W hc ⟨by omega, hW⟩ hW

/-- A bounded reaching xCfg run is a simulated run. -/
lemma simTo_of_reachesB (l l' : Λ) (v : Fin m → ℕ) (out : List Bool) (r : Fin m) (L W : ℤ)
    (hW : 0 ≤ W) (hL : L ≤ W)
    (h : ReachesB (armProg A l₀) oracle (aseam x l v out) (aseam x l' v out) (aseam x l v out) r L) :
    SimTo (armProg A l₀) oracle W (aseam x l v out) (aseam x l' v out) := by
  obtain ⟨T, e1, hm⟩ := h
  refine ⟨T, e1, fun t ht => ?_⟩
  obtain ⟨s, ip, q, hs, hc, hq1, hq2⟩ := hm t ht
  rw [hs]; exact mid_xCfg A l₀ l v out r s ip q W hc ⟨hq1, hq2.trans hL⟩ hW

/-- **Simulating `valP`**: on a well-formed plain input `⟨1ⁿ, w⟩` the compiled plain format check
moves from `l` to `l'` with nothing else changed; otherwise it halts answering `false`.

**Proof sketch.** The compiled check is the plain format-check fragment; `valPlain_run` gives
either a run reaching the rewound start configuration at `l'` (identified with the program
configuration by `xCfg_aseam`) or a rejecting run, turned into the two conclusions by
`simTo_of_reaches` and `haltsWith_of_rejects`. -/
lemma sim_valP (l l' : Λ) (r : Fin m) (hA : A l = .valP r l') (v : Fin m → ℕ) (out : List Bool)
    (W : ℤ) (hW : 0 ≤ W) :
    (ValidPlain x → SimTo (armProg A l₀) oracle W (aseam x l v out) (aseam x l' v out)) ∧
    (¬ ValidPlain x → HaltsWith (armProg A l₀) oracle W (aseam x l v out) false) := by
  have hrun := valPlain_run (armProg A l₀) oracle r (l, .start) (l, .vU1) (l, .vS) (l, .vW0)
    (l, .vWF) (l, .vWT) (l, .vrw1) (l, .vrw2) (l', .start)
    (fun a w => by rw [armProg_tr, hA]; rfl) (fun a w => by rw [armProg_tr, hA]; rfl)
    (fun a w => by rw [armProg_tr, hA]; rfl) (fun a w => by rw [armProg_tr, hA]; rfl)
    (fun a w => by rw [armProg_tr, hA]; rfl) (fun a w => by rw [armProg_tr, hA]; rfl)
    (fun a w => by rw [armProg_tr, hA]; rfl) (fun a w => by rw [armProg_tr, hA]; rfl)
    (by rw [armProg_call, hA]; rfl) (by rw [armProg_call, hA]; rfl)
    (by rw [armProg_call, hA]; rfl) (by rw [armProg_call, hA]; rfl)
    (by rw [armProg_call, hA]; rfl) (by rw [armProg_call, hA]; rfl)
    (by rw [armProg_call, hA]; rfl) (by rw [armProg_call, hA]; rfl) (aseam x l v out) 0
  obtain ⟨h1, h2⟩ := hrun
  rw [← xCfg_aseam_self] at h1 h2
  rw [xCfg_aseam] at h1
  exact ⟨fun h => simTo_of_reaches A l₀ oracle l l' v out r W hW (h1 h),
    fun h => haltsWith_of_rejects A l₀ oracle l v out r W hW (h2 h)⟩

/-- **Simulating `valQ`**: on a well-formed pair input `⟨1ⁿ, ⟨u, w⟩⟩` the compiled pair format check
moves from `l` to `l'` with nothing else changed; otherwise it halts answering `false`.

**Proof sketch.** The compiled check is the pair format-check fragment; `valPair_run` gives
either a run reaching the rewound start configuration at `l'` (identified with the program
configuration by `xCfg_aseam`) or a rejecting run. Intermediate configurations are
input-scanning views, hence in the middle of a fragment (`mid_xCfg`). -/
lemma sim_valQ (l l' : Λ) (r : Fin m) (hA : A l = .valQ r l') (v : Fin m → ℕ) (out : List Bool)
    (W : ℤ) (hW : 0 ≤ W) :
    (ValidPair x → SimTo (armProg A l₀) oracle W (aseam x l v out) (aseam x l' v out)) ∧
    (¬ ValidPair x → HaltsWith (armProg A l₀) oracle W (aseam x l v out) false) := by
  have hrun := valPair_run (armProg A l₀) oracle r (l, .start) (l, .vU1) (l, .vS)
    (fun lst => (l, .vP1 lst)) (fun b lst => (l, .vP2 b lst)) (l, .vW0) (l, .vWF) (l, .vWT)
    (l, .vrw1) (l, .vrw2) (l', .start)
    (fun a w => by rw [armProg_tr, hA]; rfl) (fun a w => by rw [armProg_tr, hA]; rfl)
    (fun a w => by rw [armProg_tr, hA]; rfl) (fun lst a w => by rw [armProg_tr, hA]; rfl)
    (fun b lst a w => by rw [armProg_tr, hA]; rfl) (fun a w => by rw [armProg_tr, hA]; rfl)
    (fun a w => by rw [armProg_tr, hA]; rfl) (fun a w => by rw [armProg_tr, hA]; rfl)
    (fun a w => by rw [armProg_tr, hA]; rfl) (fun a w => by rw [armProg_tr, hA]; rfl)
    (by rw [armProg_call, hA]; rfl) (by rw [armProg_call, hA]; rfl)
    (by rw [armProg_call, hA]; rfl) (fun lst => by rw [armProg_call, hA]; rfl)
    (fun b lst => by rw [armProg_call, hA]; rfl) (by rw [armProg_call, hA]; rfl)
    (by rw [armProg_call, hA]; rfl) (by rw [armProg_call, hA]; rfl)
    (by rw [armProg_call, hA]; rfl) (by rw [armProg_call, hA]; rfl) (aseam x l v out) 0
  obtain ⟨h1, h2⟩ := hrun
  rw [← xCfg_aseam_self] at h1 h2
  rw [xCfg_aseam] at h1
  exact ⟨fun h => simTo_of_reaches A l₀ oracle l l' v out r W hW (h1 h),
    fun h => haltsWith_of_rejects A l₀ oracle l v out r W hW (h2 h)⟩

/-- **Simulating `jeqIn r`** on a well-formed plain input `⟨1ⁿ, w⟩`: the compiled comparison moves
from `l` to `l₁` if `bits (v r) = w` and to `l₀'` otherwise, with nothing else changed.

**Proof sketch.** Decompose the input as `⟨1ⁿ, w⟩` and apply `jeqPlain_run` to the register
holding `bits (v r)`; its end view is the program configuration at the outcome label
(`xCfg_aseam`) and `plainWord_pairEncode` identifies `w`. Intermediate configurations are
input-scanning views with the register head in range (`mid_xCfg`). -/
lemma sim_jeqIn (l l₁ l₀' : Λ) (r : Fin m) (hA : A l = .jeqIn r l₁ l₀') (v : Fin m → ℕ)
    (out : List Bool) (W : ℤ) (hW : ((Nat.bits (v r)).length : ℤ) ≤ W) (hx : ValidPlain x) :
    SimTo (armProg A l₀) oracle W (aseam x l v out)
      (aseam x (if Nat.bits (v r) = plainWord x then l₁ else l₀') v out) := by
  obtain ⟨n, w, rfl, -⟩ := hx
  obtain ⟨T, h1, hm⟩ := jeqPlain_run (armProg A l₀) oracle r (l, .start) (l, .jK2) (l, .jC)
    (fun b => (l, .jRB b)) (fun b => (l, .jI1 b)) (fun b => (l, .jI2 b)) (l₁, .start)
    (l₀', .start) (fun a w => by rw [armProg_tr, hA]; rfl) (fun a w => by rw [armProg_tr, hA]; rfl)
    (fun a w => by rw [armProg_tr, hA]; rfl) (fun b a w => by rw [armProg_tr, hA]; rfl)
    (fun b a w => by rw [armProg_tr, hA]; rfl) (fun b a w => by rw [armProg_tr, hA]; rfl)
    (by rw [armProg_call, hA]; rfl) (by rw [armProg_call, hA]; rfl)
    (by rw [armProg_call, hA]; rfl) (fun b => by rw [armProg_call, hA]; rfl)
    (fun b => by rw [armProg_call, hA]; rfl) (fun b => by rw [armProg_call, hA]; rfl)
    (aseam _ l v out) n w rfl (v r) rfl
  rw [← xCfg_aseam_self] at h1 hm
  rw [plainWord_pairEncode]
  have e : (if w = Nat.bits (v r) then ((l₁, Ph.start) : Λ × Ph) else (l₀', Ph.start)) =
      ((if Nat.bits (v r) = w then l₁ else l₀'), Ph.start) := by
    by_cases h : w = Nat.bits (v r)
    · simp [h]
    · simp [h, Ne.symm h]
  rw [e, xCfg_aseam] at h1
  exact simTo_of_reachesB A l₀ oracle l _ v out r _ W (by omega) hW ⟨T, h1, hm⟩

/-- **Simulating `jeqSnd r`** on a well-formed pair input `⟨1ⁿ, ⟨u, w⟩⟩`: the compiled comparison
moves from `l` to `l₁` if `bits (v r) = w` and to `l₀'` otherwise, with nothing else changed.

**Proof sketch.** Decompose the input and apply `jeqPairSnd_run` (skip `1²ⁿ01` and the doubled
`u`, then compare in lockstep). Its end view is the program configuration at the outcome label,
`pairWords_pairEncode` identifies `w`, and the run stays in the middle of a fragment. -/
lemma sim_jeqSnd (l l₁ l₀' : Λ) (r : Fin m) (hA : A l = .jeqSnd r l₁ l₀') (v : Fin m → ℕ)
    (out : List Bool) (W : ℤ) (hW : ((Nat.bits (v r)).length : ℤ) ≤ W) (hx : ValidPair x) :
    SimTo (armProg A l₀) oracle W (aseam x l v out)
      (aseam x (if Nat.bits (v r) = (pairWords x).2 then l₁ else l₀') v out) := by
  obtain ⟨n, u, w, rfl, -, -⟩ := hx
  have h := jeqPairSnd_run (armProg A l₀) oracle r (l, .start) (l, .jK2) (l, .jC)
    (fun b => (l, .jRB b)) (fun b => (l, .jI1 b)) (fun b => (l, .jI2 b)) (l₁, .start)
    (l₀', .start) (fun a w => by rw [armProg_tr, hA]; rfl) (fun a w => by rw [armProg_tr, hA]; rfl)
    (fun b a w => by rw [armProg_tr, hA]; rfl) (fun b a w => by rw [armProg_tr, hA]; rfl)
    (fun b a w => by rw [armProg_tr, hA]; rfl)
    (by rw [armProg_call, hA]; rfl) (by rw [armProg_call, hA]; rfl)
    (by rw [armProg_call, hA]; rfl) (fun b => by rw [armProg_call, hA]; rfl)
    (fun b => by rw [armProg_call, hA]; rfl) (fun b => by rw [armProg_call, hA]; rfl)
    (l, .jP1) (l, .jP2F) (l, .jP2T) (fun a w => by rw [armProg_tr, hA]; rfl)
    (fun a w => by rw [armProg_tr, hA]; rfl) (fun a w => by rw [armProg_tr, hA]; rfl)
    (fun a w => by rw [armProg_tr, hA]; rfl) (by rw [armProg_call, hA]; rfl)
    (by rw [armProg_call, hA]; rfl) (by rw [armProg_call, hA]; rfl)
    (aseam _ l v out) n u w rfl (v r) rfl
  rw [← xCfg_aseam_self] at h
  rw [pairWords_pairEncode]
  have e : (if w = Nat.bits (v r) then ((l₁, Ph.start) : Λ × Ph) else (l₀', Ph.start)) =
      ((if Nat.bits (v r) = w then l₁ else l₀'), Ph.start) := by
    by_cases h : w = Nat.bits (v r)
    · simp [h]
    · simp [h, Ne.symm h]
  rw [e, xCfg_aseam] at h
  exact simTo_of_reachesB A l₀ oracle l _ v out r _ W (by omega) hW h

/-- **Simulating `jeqFst r`** on a well-formed pair input `⟨1ⁿ, ⟨u, w⟩⟩`: the compiled comparison
moves from `l` to `l₁` if `bits (v r) = u` and to `l₀'` otherwise, with nothing else changed.

**Proof sketch.** Decompose the input and apply `jeqPairFst_run` (skip `1²ⁿ01`, then compare the
register with the doubled `u` in lockstep). Its end view is the program configuration at the
outcome label, `pairWords_pairEncode` identifies `u`, and the run stays in the middle of a
fragment. -/
lemma sim_jeqFst (l l₁ l₀' : Λ) (r : Fin m) (hA : A l = .jeqFst r l₁ l₀') (v : Fin m → ℕ)
    (out : List Bool) (W : ℤ) (hW : ((Nat.bits (v r)).length : ℤ) ≤ W) (hx : ValidPair x) :
    SimTo (armProg A l₀) oracle W (aseam x l v out)
      (aseam x (if Nat.bits (v r) = (pairWords x).1 then l₁ else l₀') v out) := by
  obtain ⟨n, u, w, rfl, -, -⟩ := hx
  have h := jeqPairFst_run (armProg A l₀) oracle r (l, .start) (l, .jK2)
    (fun b => (l, .jRB b)) (fun b => (l, .jI1 b)) (fun b => (l, .jI2 b)) (l₁, .start)
    (l₀', .start) (fun a w => by rw [armProg_tr, hA]; rfl)
    (fun b a w => by rw [armProg_tr, hA]; rfl) (fun b a w => by rw [armProg_tr, hA]; rfl)
    (fun b a w => by rw [armProg_tr, hA]; rfl)
    (by rw [armProg_call, hA]; rfl) (by rw [armProg_call, hA]; rfl)
    (fun b => by rw [armProg_call, hA]; rfl)
    (fun b => by rw [armProg_call, hA]; rfl) (fun b => by rw [armProg_call, hA]; rfl)
    (l, .jD1) (l, .jD2F) (l, .jD2T) (fun a w => by rw [armProg_tr, hA]; rfl)
    (fun a w => by rw [armProg_tr, hA]; rfl) (fun a w => by rw [armProg_tr, hA]; rfl)
    (fun a w => by rw [armProg_tr, hA]; rfl) (by rw [armProg_call, hA]; rfl)
    (by rw [armProg_call, hA]; rfl) (by rw [armProg_call, hA]; rfl)
    (aseam _ l v out) n u w rfl (v r) rfl
  rw [← xCfg_aseam_self] at h
  rw [pairWords_pairEncode]
  have e : (if u = Nat.bits (v r) then ((l₁, Ph.start) : Λ × Ph) else (l₀', Ph.start)) =
      ((if Nat.bits (v r) = u then l₁ else l₀'), Ph.start) := by
    by_cases h : u = Nat.bits (v r)
    · simp [h]
    · simp [h, Ne.symm h]
  rw [e, xCfg_aseam] at h
  exact simTo_of_reachesB A l₀ oracle l _ v out r _ W (by omega) hW h

end Steps

end Complexity.LogProg

```


## ===== TCSlib/Complexity/SpaceComplexity/Machines/ARMRun.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.ARMSim

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Abstract register machines decide in logarithmic space

The run theorem for abstract register machines (`Complexity.LogProg.arm_run`): if the
abstract machine answers `b`, with register values of at most `W` binary digits and the
preconditions of its instructions met, then the compiled machine
(`Complexity.LogProg.compileFinTM` of `Complexity.LogProg.armProg`) answers `b` visiting at
most `m (W + 2) + kD (2B + 1)` work cells (`Complexity.LogProg.arm_space`).

## Main definitions

* `Complexity.LogProg.Pre` — the preconditions of an abstract step.

## Main results

* `Complexity.LogProg.arm_run`, `Complexity.LogProg.arm_space`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.)
-/

namespace Complexity.LogProg

open Turing

variable {m d kD : ℕ} {Λ SD : Type} {x : List Bool}

/-- The preconditions of the abstract step at a configuration: equality tests compare distinct
registers, index comparisons happen on inputs of the right shape, and a call has distinct
arguments and a decider answering it cleanly within head range `B`. -/
def Pre (A : ARM m d Λ) (oracle : Fin d → List Bool → Bool) (D : MultiTapeTM kD Bool SD)
    (q0 : Fin d → SD) (B : ℕ) (x : List Bool) : AConf m Λ → Prop
  | (some l, v, _) =>
    match A l with
    | .jeq r s _ _ => r ≠ s
    | .jeqIn _ _ _ => ValidPlain x
    | .jeqFst _ _ _ => ValidPair x
    | .jeqSnd _ _ _ => ValidPair x
    | .call j md args l₁ l₀ => args.Nodup ∧
        CleanRun D (q0 j) (vword (callSegs ⟨j, md, args, l₁, l₀⟩ x (fun r => Nat.bits (v r))))
          (oracle j (vword (callSegs ⟨j, md, args, l₁, l₀⟩ x (fun r => Nat.bits (v r))))) B
    | _ => True
  | _ => True

/-- Running `n + 1` steps is one step followed by `n` steps. -/
lemma arun_succ (A : ARM m d Λ) (oracle : Fin d → List Bool → Bool) (a : AConf m Λ) (n : ℕ) :
    arun A oracle x a (n + 1) = arun A oracle x (astep A oracle x a) n := by
  simp [arun, Function.iterate_succ_apply]

/-- A halted abstract configuration stays put. -/
lemma arun_halted (A : ARM m d Λ) (oracle : Fin d → List Bool → Bool) (v : Fin m → ℕ)
    (res : Option Bool) (n : ℕ) : arun A oracle x (none, v, res) n = (none, v, res) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [arun_succ]; exact ih

/-- The invariant of the compiled run: register heads in `[-1, W]`, and the preconditions of
a call at call nodes. -/
def Inv (A : ARM m d Λ) (l₀ : Λ) (oracle : Fin d → List Bool → Bool) (D : MultiTapeTM kD Bool SD)
    (q0 : Fin d → SD) (B : ℕ) (W : ℕ) (c : Cfg m Bool (Λ × Ph) x) : Prop :=
  (∀ r, (-1 : ℤ) ≤ c.workTapePos r ∧ c.workTapePos r ≤ W) ∧
    CallOK (armProg A l₀) D q0 oracle (fun _ => -1) (fun _ => (W : ℤ)) B c

/-- A configuration in the middle of an instruction fragment satisfies the run invariant. -/
lemma inv_of_mid (A : ARM m d Λ) (l₀ : Λ) (oracle : Fin d → List Bool → Bool)
    (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD) (B W : ℕ) (c : Cfg m Bool (Λ × Ph) x)
    (h : Mid (armProg A l₀) W c) : Inv A l₀ oracle D q0 B W c := by
  refine ⟨h.2, fun l cs hl hcs => ?_⟩
  rw [h.1 l hl] at hcs; simp at hcs

/-- Compose a simulated run with a continuation.

**Proof sketch.** Concatenate the two runs (`rrun_add`). Times before the end of the simulated
run satisfy the invariant by `inv_of_mid` (they are in the middle of a fragment), and later
times by the continuation's hypothesis. -/
lemma inv_append (A : ARM m d Λ) (l₀ : Λ) (oracle : Fin d → List Bool → Bool)
    (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD) (B W : ℕ) (c c' : Cfg m Bool (Λ × Ph) x)
    (h₁ : SimTo (armProg A l₀) oracle W c c') (out : List Bool) (b : Bool)
    (h₂ : ∃ T, (rrun (armProg A l₀) oracle c' T).state = none ∧
      (rrun (armProg A l₀) oracle c' T).output = out ++ [b] ∧
      (∀ r, (-1 : ℤ) ≤ (rrun (armProg A l₀) oracle c' T).workTapePos r ∧
        (rrun (armProg A l₀) oracle c' T).workTapePos r ≤ W) ∧
      ∀ t < T, Inv A l₀ oracle D q0 B W (rrun (armProg A l₀) oracle c' t)) :
    ∃ T, (rrun (armProg A l₀) oracle c T).state = none ∧
      (rrun (armProg A l₀) oracle c T).output = out ++ [b] ∧
      (∀ r, (-1 : ℤ) ≤ (rrun (armProg A l₀) oracle c T).workTapePos r ∧
        (rrun (armProg A l₀) oracle c T).workTapePos r ≤ W) ∧
      ∀ t < T, Inv A l₀ oracle D q0 B W (rrun (armProg A l₀) oracle c t) := by
  obtain ⟨T₁, e1, m1⟩ := h₁
  obtain ⟨T₂, f1, f2, f3, m2⟩ := h₂
  refine ⟨T₁ + T₂, by rw [rrun_add, e1]; exact f1, by rw [rrun_add, e1]; exact f2,
    by rw [rrun_add, e1]; exact f3, fun t ht => ?_⟩
  rcases Nat.lt_or_ge t T₁ with h | h
  · exact inv_of_mid A l₀ oracle D q0 B W _ (m1 t h)
  · obtain ⟨t', rfl⟩ : ∃ t', t = T₁ + t' := ⟨t - T₁, by omega⟩
    rw [rrun_add, e1]; exact m2 t' (by omega)

/-- **The run theorem for abstract register machines.** If, from `l` with values `v`, the
abstract machine halts after `N` steps with answer `b`, every configuration before has the
preconditions `Pre` and values of at most `W` binary digits (counting one increment), then
the compiled program, from the representation of `(l, v)` having written `out`, halts with
`out ++ [b]`, its register heads in `[-1, W]` and its calls meeting `CallOK`.

**Proof sketch.** Induction on `N`; each abstract step is one of the simulation lemmas
`sim_inc`, …, `sim_jeqFst` of `TCSlib.Complexity.SpaceComplexity.Machines.ARMSim`. -/
theorem arm_run (A : ARM m d Λ) (l₀ : Λ) (oracle : Fin d → List Bool → Bool)
    (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD) (B W : ℕ) :
    ∀ (N : ℕ) (l : Λ) (v : Fin m → ℕ) (out : List Bool) (b : Bool),
      (arun A oracle x (some l, v, none) N).1 = none →
      (arun A oracle x (some l, v, none) N).2.2 = some b →
      (∀ t < N, Pre A oracle D q0 B x (arun A oracle x (some l, v, none) t) ∧
        ∀ r, ((Nat.bits ((arun A oracle x (some l, v, none) t).2.1 r + 1)).length : ℤ) ≤ W) →
      ∃ T, (rrun (armProg A l₀) oracle (aseam x l v out) T).state = none ∧
        (rrun (armProg A l₀) oracle (aseam x l v out) T).output = out ++ [b] ∧
        (∀ r, (-1 : ℤ) ≤ (rrun (armProg A l₀) oracle (aseam x l v out) T).workTapePos r ∧
          (rrun (armProg A l₀) oracle (aseam x l v out) T).workTapePos r ≤ W) ∧
        ∀ t < T, Inv A l₀ oracle D q0 B W (rrun (armProg A l₀) oracle (aseam x l v out) t) := by
  intro N
  induction N with
  | zero => intro l v out b h1 _ _; simp [arun] at h1
  | succ N ih =>
    intro l v out b h1 h2 hpre
    obtain ⟨hp0, hb0⟩ := hpre 0 (by omega)
    simp only [arun, Function.iterate_zero, id] at hp0 hb0
    have hW0 : (0 : ℤ) ≤ W := by omega
    have hlen : ∀ r, ((Nat.bits (v r)).length : ℤ) ≤ W := by
      intro r
      have := hb0 r
      have hle : (Nat.bits (v r)).length ≤ (Nat.bits (v r + 1)).length := by
        exact length_bits_mono (by omega)
      omega
    -- the continuation after the first abstract step
    have cont : ∀ (l' : Λ) (v' : Fin m → ℕ), astep A oracle x (some l, v, none) = (some l', v', none) →
        ∃ T, (rrun (armProg A l₀) oracle (aseam x l' v' out) T).state = none ∧
          (rrun (armProg A l₀) oracle (aseam x l' v' out) T).output = out ++ [b] ∧
          (∀ r, (-1 : ℤ) ≤ (rrun (armProg A l₀) oracle (aseam x l' v' out) T).workTapePos r ∧
            (rrun (armProg A l₀) oracle (aseam x l' v' out) T).workTapePos r ≤ W) ∧
          ∀ t < T, Inv A l₀ oracle D q0 B W
            (rrun (armProg A l₀) oracle (aseam x l' v' out) t) := by
      intro l' v' hs
      rw [arun_succ, hs] at h1 h2
      exact ih l' v' out b h1 h2 (fun t ht => by
        have := hpre (t + 1) (by omega); rwa [arun_succ, hs] at this)
    -- a halting first step
    have halt : ∀ (b' : Bool), astep A oracle x (some l, v, none) = (none, v, some b') → b' = b := by
      intro b' hs
      rw [arun_succ, hs, arun_halted] at h2
      simpa using h2
    have haltW : ∀ (b' : Bool), HaltsWith (armProg A l₀) oracle W (aseam x l v out) b' →
        b' = b → ∃ T, (rrun (armProg A l₀) oracle (aseam x l v out) T).state = none ∧
          (rrun (armProg A l₀) oracle (aseam x l v out) T).output = out ++ [b] ∧
          (∀ r, (-1 : ℤ) ≤ (rrun (armProg A l₀) oracle (aseam x l v out) T).workTapePos r ∧
            (rrun (armProg A l₀) oracle (aseam x l v out) T).workTapePos r ≤ W) ∧
          ∀ t < T, Inv A l₀ oracle D q0 B W (rrun (armProg A l₀) oracle (aseam x l v out) t) := by
      rintro b' ⟨T, e1, e2, e3, hm⟩ rfl
      exact ⟨T, e1, e2, e3, fun t ht => inv_of_mid A l₀ oracle D q0 B W _ (hm t ht)⟩
    have step : ∀ (l' : Λ) (v' : Fin m → ℕ), astep A oracle x (some l, v, none) = (some l', v', none) →
        SimTo (armProg A l₀) oracle W (aseam x l v out) (aseam x l' v' out) →
        ∃ T, (rrun (armProg A l₀) oracle (aseam x l v out) T).state = none ∧
          (rrun (armProg A l₀) oracle (aseam x l v out) T).output = out ++ [b] ∧
          (∀ r, (-1 : ℤ) ≤ (rrun (armProg A l₀) oracle (aseam x l v out) T).workTapePos r ∧
            (rrun (armProg A l₀) oracle (aseam x l v out) T).workTapePos r ≤ W) ∧
          ∀ t < T, Inv A l₀ oracle D q0 B W (rrun (armProg A l₀) oracle (aseam x l v out) t) :=
      fun l' v' hs hsim => inv_append A l₀ oracle D q0 B W _ _ hsim out b (cont l' v' hs)
    cases hA : A l with
    | inc r l' =>
      exact step _ _ (by simp [astep, hA]) (sim_inc A l₀ oracle l l' r hA v out W (hb0 r))
    | dec r l' =>
      exact step _ _ (by simp [astep, hA]) (sim_dec A l₀ oracle l l' r hA v out W (hlen r))
    | clr r l' =>
      exact step _ _ (by simp [astep, hA]) (sim_clr A l₀ oracle l l' r hA v out W (hlen r))
    | half r l' =>
      exact step _ _ (by simp [astep, hA]) (sim_half A l₀ oracle l l' r hA v out W (hlen r))
    | jz r l₁ l₀' =>
      exact step _ _ (by simp [astep, hA]) (sim_jz A l₀ oracle l l₁ l₀' r hA v out W hW0)
    | jodd r l₁ l₀' =>
      exact step _ _ (by simp [astep, hA]) (sim_jodd A l₀ oracle l l₁ l₀' r hA v out W hW0)
    | jeq r s' l₁ l₀' =>
      have hrs : r ≠ s' := by simpa [Pre, hA] using hp0
      exact step _ _ (by simp [astep, hA])
        (sim_jeq A l₀ oracle l l₁ l₀' r s' hrs hA v out W (hlen r))
    | jeqIn r l₁ l₀' =>
      have hx : ValidPlain x := by simpa [Pre, hA] using hp0
      exact step _ _ (by simp [astep, hA]) (sim_jeqIn A l₀ oracle l l₁ l₀' r hA v out W (hlen r) hx)
    | jeqFst r l₁ l₀' =>
      have hx : ValidPair x := by simpa [Pre, hA] using hp0
      exact step _ _ (by simp [astep, hA])
        (sim_jeqFst A l₀ oracle l l₁ l₀' r hA v out W (hlen r) hx)
    | jeqSnd r l₁ l₀' =>
      have hx : ValidPair x := by simpa [Pre, hA] using hp0
      exact step _ _ (by simp [astep, hA])
        (sim_jeqSnd A l₀ oracle l l₁ l₀' r hA v out W (hlen r) hx)
    | ret b' =>
      exact haltW b' (sim_ret A l₀ oracle l b' hA v out W hW0) (halt b' (by simp [astep, hA]))
    | valP r l' =>
      obtain ⟨s1, s2⟩ := sim_valP A l₀ oracle l l' r hA v out W hW0
      by_cases hv : ValidPlain x
      · exact step _ _ (by simp [astep, hA, hv]) (s1 hv)
      · exact haltW false (s2 hv) (halt false (by simp [astep, hA, hv]))
    | valQ r l' =>
      obtain ⟨s1, s2⟩ := sim_valQ A l₀ oracle l l' r hA v out W hW0
      by_cases hv : ValidPair x
      · exact step _ _ (by simp [astep, hA, hv]) (s1 hv)
      · exact haltW false (s2 hv) (halt false (by simp [astep, hA, hv]))
    | call j md args l₁ l₀' =>
      have hpc : args.Nodup ∧ CleanRun D (q0 j)
          (vword (callSegs ⟨j, md, args, l₁, l₀'⟩ x (fun r => Nat.bits (v r))))
          (oracle j (vword (callSegs ⟨j, md, args, l₁, l₀'⟩ x (fun r => Nat.bits (v r))))) B := by
        simpa [Pre, hA] using hp0
      have h1s := sim_call (x := x) A l₀ oracle l l₁ l₀' j md args hA v out
      obtain ⟨T, f1, f2, f3, hm⟩ := cont (if oracle j (vword (callSegs ⟨j, md, args, l₁, l₀'⟩ x
        (fun r => Nat.bits (v r)))) then l₁ else l₀') v (by simp [astep, hA])
      refine ⟨1 + T, by rw [rrun_add, h1s]; exact f1, by rw [rrun_add, h1s]; exact f2,
        by rw [rrun_add, h1s]; exact f3, fun t ht => ?_⟩
      rcases Nat.lt_or_ge t 1 with h | h
      · obtain rfl : t = 0 := by omega
        rw [rrun_zero]
        refine ⟨fun r => by simp [aseam], fun l' cs hl hcs => ?_⟩
        simp only [aseam, Option.some.injEq] at hl
        subst hl
        rw [armProg_call, hA] at hcs
        simp only [insCall, Option.some.injEq] at hcs
        subst hcs
        have hw : regWords (aseam x l v out) = fun r => Nat.bits (v r) := by
          funext r; simp [regWords, aseam, tapeWord_bufferTape]
        refine ⟨hpc.1, rfl, fun r _ => ?_, ?_⟩
        · rw [hw]; exact ⟨rfl, rfl, le_rfl, hlen r⟩
        · rw [hw]; exact hpc.2
      · obtain ⟨t', rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
        rw [rrun_add, h1s]; exact hm t' (by omega)

/-- The initial configuration of the compiled program is the program configuration of the
start label with all registers `0` and empty output. -/
lemma init_eq_aseam (l₀ : Λ) : (Cfg.init (k := m) (l₀, Ph.start) x) = aseam x l₀ (fun _ => 0) [] := by
  refine Cfg.ext rfl rfl ?_ rfl rfl
  funext r z; simp [aseam, Nat.zero_bits]

/-- **Abstract register machines decide in small space.** If the abstract machine, started at
`l₀` with all registers `0`, answers `b` on input `x` after `N` steps, with the
preconditions met and all values of at most `W` binary digits (counting one increment), then
the compiled machine outputs `[b]` on `x`, visiting at most `m (W + 2) + kD (2B + 1)` work
cells.

**Proof sketch.** `arm_run` from the initial configuration (`init_eq_aseam`), then
`compile_space` with register ranges `[-1, W]`. -/
theorem arm_space [Fintype Λ] [DecidableEq Λ] [Fintype SD] [DecidableEq SD] (A : ARM m d Λ)
    (l₀ : Λ) (oracle : Fin d → List Bool → Bool) (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD)
    (B W N : ℕ) (b : Bool)
    (h1 : (arun A oracle x (some l₀, fun _ => 0, none) N).1 = none)
    (h2 : (arun A oracle x (some l₀, fun _ => 0, none) N).2.2 = some b)
    (hpre : ∀ t < N, Pre A oracle D q0 B x (arun A oracle x (some l₀, fun _ => 0, none) t) ∧
      ∀ r, ((Nat.bits ((arun A oracle x (some l₀, fun _ => 0, none) t).2.1 r + 1)).length : ℤ) ≤ W) :
    ∃ T, (compileFinTM (armProg A l₀) (l₀, .start) D q0).ComputesInTime x [b] T ∧
      (compileFinTM (armProg A l₀) (l₀, .start) D q0).tm.spaceUsed
        ((compileFinTM (armProg A l₀) (l₀, .start) D q0).tm.initCfg x) T ≤
        m * (W + 2) + kD * (2 * B + 1) := by
  obtain ⟨T, e1, e2, e3, hm⟩ := arm_run A l₀ oracle D q0 B W N l₀ (fun _ => 0) [] b h1 h2 hpre
  rw [← init_eq_aseam] at e1 e2 e3 hm
  simp only [List.nil_append] at e2
  obtain ⟨T', hT', hsp⟩ := compile_space (armProg A l₀) (l₀, .start) D q0 oracle (fun _ => -1)
    (fun _ => (W : ℤ)) B T [b] e1 e2
    (fun t ht r => by
      rcases Nat.lt_or_ge t T with h | h
      · exact (hm t h).1 r
      · obtain rfl : t = T := by omega
        exact e3 r)
    (fun t ht => (hm t ht).2)
  refine ⟨T', hT', hsp.trans (le_of_eq ?_)⟩
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  congr 2

end Complexity.LogProg

```


## ===== TCSlib/Complexity/SpaceComplexity/Machines/ARMProof.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.ARMRun
import TCSlib.Complexity.SpaceComplexity.Machines.Bank
import TCSlib.Complexity.SpaceComplexity.ConfigCount

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Proving abstract register machines correct

Reasoning about abstract register machines (`Complexity.LogProg.ARM`) happens on values: runs
`Complexity.LogProg.AReach` between abstract configurations through configurations satisfying
an invariant, composed sequentially. `Complexity.LogProg.arm_decides` turns a correct
abstract machine — one answering membership in a language on every input, with values of
logarithmically many binary digits — into a logspace decider.

## Main definitions

* `Complexity.LogProg.AReach`, `Complexity.LogProg.AHalt` — runs of abstract machines.

## Main results

* `Complexity.LogProg.arm_decides` — a correct abstract machine with logarithmic register
  values, calling logspace deciders on short virtual inputs, decides its language in `L`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.)
-/

namespace Complexity.LogProg

open Turing

variable {m d : ℕ} {Λ : Type} {x : List Bool}

/-- A run of an abstract machine from `a` to `a'` through configurations satisfying `G`. -/
def AReach (A : ARM m d Λ) (oracle : Fin d → List Bool → Bool) (x : List Bool)
    (G : AConf m Λ → Prop) (a a' : AConf m Λ) : Prop :=
  ∃ T, arun A oracle x a T = a' ∧ ∀ t < T, G (arun A oracle x a t)

/-- A run of an abstract machine from `a` answering `b`, through configurations satisfying `G`. -/
def AHalt (A : ARM m d Λ) (oracle : Fin d → List Bool → Bool) (x : List Bool)
    (G : AConf m Λ → Prop) (a : AConf m Λ) (b : Bool) : Prop :=
  ∃ T, (arun A oracle x a T).1 = none ∧ (arun A oracle x a T).2.2 = some b ∧
    ∀ t < T, G (arun A oracle x a t)

section Combinators

variable {A : ARM m d Λ} {oracle : Fin d → List Bool → Bool} {G : AConf m Λ → Prop}

/-- Running `s + t` steps is running `s` steps, then `t` steps. -/
lemma arun_add (a : AConf m Λ) (s t : ℕ) :
    arun A oracle x a (s + t) = arun A oracle x (arun A oracle x a s) t := by
  simp only [arun]; rw [Nat.add_comm, Function.iterate_add_apply]

/-- Every configuration reaches itself (in zero steps). -/
lemma AReach.refl (a : AConf m Λ) : AReach A oracle x G a a := ⟨0, rfl, fun t h => by omega⟩

/-- Runs compose: a run from `a` to `b` followed by one from `b` to `c` is a run from `a` to `c`. -/
lemma AReach.trans {a b c : AConf m Λ} (h₁ : AReach A oracle x G a b)
    (h₂ : AReach A oracle x G b c) : AReach A oracle x G a c := by
  obtain ⟨T₁, e1, m1⟩ := h₁
  obtain ⟨T₂, e2, m2⟩ := h₂
  refine ⟨T₁ + T₂, by rw [arun_add, e1, e2], fun t ht => ?_⟩
  rcases Nat.lt_or_ge t T₁ with h | h
  · exact m1 t h
  · obtain ⟨t', rfl⟩ : ∃ t', t = T₁ + t' := ⟨t - T₁, by omega⟩
    rw [arun_add, e1]; exact m2 t' (by omega)

/-- A run from `a` to `b` followed by a halting run from `b` is a halting run from `a`, with
the same answer. -/
lemma AReach.halt {a b : AConf m Λ} {r : Bool} (h₁ : AReach A oracle x G a b)
    (h₂ : AHalt A oracle x G b r) : AHalt A oracle x G a r := by
  obtain ⟨T₁, e1, m1⟩ := h₁
  obtain ⟨T₂, f1, f2, m2⟩ := h₂
  refine ⟨T₁ + T₂, by rw [arun_add, e1]; exact f1, by rw [arun_add, e1]; exact f2, fun t ht => ?_⟩
  rcases Nat.lt_or_ge t T₁ with h | h
  · exact m1 t h
  · obtain ⟨t', rfl⟩ : ∃ t', t = T₁ + t' := ⟨t - T₁, by omega⟩
    rw [arun_add, e1]; exact m2 t' (by omega)

/-- A configuration satisfying the guard reaches its successor in one step. -/
lemma AReach.single {a : AConf m Λ} (hG : G a) :
    AReach A oracle x G a (astep A oracle x a) := ⟨1, rfl, fun t ht => by
  obtain rfl : t = 0 := by omega
  exact hG⟩

/-- A step followed by a run. -/
lemma AReach.step {a c : AConf m Λ} (hG : G a) (h : AReach A oracle x G (astep A oracle x a) c) :
    AReach A oracle x G a c := (AReach.single hG).trans h

/-- A step followed by a halting run. -/
lemma AHalt.step {a : AConf m Λ} {r : Bool} (hG : G a)
    (h : AHalt A oracle x G (astep A oracle x a) r) : AHalt A oracle x G a r :=
  (AReach.single hG).halt h

/-- Answering in one step. -/
lemma AHalt.ret {l : Λ} {v : Fin m → ℕ} {r : Bool} (hA : A l = .ret r)
    (hG : G (some l, v, none)) : AHalt A oracle x G (some l, v, none) r :=
  ⟨1, by simp [arun, astep, hA], by simp [arun, astep, hA], fun t ht => by
    obtain rfl : t = 0 := by omega
    exact hG⟩

/-- A run through configurations satisfying `G` also runs through configurations satisfying any
weaker `G'`. -/
lemma AReach.mono {G' : AConf m Λ → Prop} {a b : AConf m Λ} (h : AReach A oracle x G a b)
    (hG : ∀ c, G c → G' c) : AReach A oracle x G' a b := by
  obtain ⟨T, e, hm⟩ := h; exact ⟨T, e, fun t ht => hG _ (hm t ht)⟩

/-- A halting run through configurations satisfying `G` also runs through configurations
satisfying any weaker `G'`. -/
lemma AHalt.mono {G' : AConf m Λ → Prop} {a : AConf m Λ} {r : Bool} (h : AHalt A oracle x G a r)
    (hG : ∀ c, G c → G' c) : AHalt A oracle x G' a r := by
  obtain ⟨T, e1, e2, hm⟩ := h; exact ⟨T, e1, e2, fun t ht => hG _ (hm t ht)⟩

end Combinators

/-! ## From abstract machines to `L` -/

/-- A clean run within a head range is a clean run within any larger range. -/
lemma cleanRun_mono {kD : ℕ} {SD : Type} {D : MultiTapeTM kD Bool SD} {q : SD}
    {V : List Bool} {b : Bool} {B B' : ℕ} (h : CleanRun D q V b B) (hB : B ≤ B') :
    CleanRun D q V b B' := by
  obtain ⟨T, h1, h2, h3, h4, h5⟩ := h
  exact ⟨T, h1, h2, h3, h4, fun t ht i => (h5 t ht i).trans (by exact_mod_cast hB)⟩

/-- The syntactic preconditions of an abstract step (the decider part of `Pre` is discharged
by `arm_decides`). -/
def PreS (A : ARM m d Λ) (x : List Bool) : AConf m Λ → Prop
  | (some l, _, _) =>
    match A l with
    | .jeq r s _ _ => r ≠ s
    | .jeqIn _ _ _ => ValidPlain x
    | .jeqFst _ _ _ => ValidPair x
    | .jeqSnd _ _ _ => ValidPair x
    | .call _ _ args _ _ => args.Nodup
    | _ => True
  | _ => True

/-- A virtual input is at most as long as its segments' renderings plus two separator symbols
per segment. -/
lemma length_vword_le (segs : List Seg) :
    (vword segs).length ≤ (segs.map rlen).sum + 2 * segs.length := by
  induction segs with
  | nil => simp [vword]
  | cons s rest ih =>
    cases rest with
    | nil => simp [vword]
    | cons t rest' =>
      simp only [vword, List.length_append, length_render, List.length_cons, List.length_nil,
        List.map_cons, List.sum_cons] at ih ⊢
      omega

/-- Every register segment of a call comes from one of the argument words. -/
lemma mem_argSegs {ws : List (List Bool)} {sg : Seg} (h : sg ∈ argSegs ws) : sg.1 ∈ ws := by
  induction ws with
  | nil => simp [argSegs] at h
  | cons w ws ih =>
    cases ws with
    | nil => simp [argSegs] at h; simp [h]
    | cons v ws' =>
      simp only [argSegs, List.mem_cons] at h
      rcases h with rfl | h
      · simp
      · exact List.mem_cons_of_mem _ (ih h)

/-- The renderings of the register segments of argument words of length at most `W` have total
length at most `2W` per word. -/
lemma sum_rlen_argSegs_le (ws : List (List Bool)) (W : ℕ) (h : ∀ w ∈ ws, w.length ≤ W) :
    ((argSegs ws).map rlen).sum ≤ ws.length * (2 * W) := by
  have hle : ∀ y ∈ (argSegs ws).map rlen, y ≤ 2 * W := by
    intro y hy
    obtain ⟨sg, hs, rfl⟩ := List.mem_map.mp hy
    have := h _ (mem_argSegs hs)
    obtain ⟨w', bb⟩ := sg
    cases bb <;> simp [rlen] at this ⊢ <;> omega
  have := List.sum_le_card_nsmul _ _ hle
  simpa using this

/-- The virtual input of a call is short when the registers are.

**Proof sketch.** The virtual input is the leading segment (the input doubled, or its leading
run of `1`s, of rendered length at most `2|x|`) and one segment per argument register. There are
at most `m` arguments since they are distinct (`hnd`), each rendered with length at most `2W`,
plus two separator symbols per segment (`length_vword_le`, `sum_rlen_argSegs_le`). -/
lemma length_callSegs_le (cs : CallSpec m d Λ) (W : ℕ) (V : Fin m → List Bool)
    (hV : ∀ r, (V r).length ≤ W) (hnd : cs.args.Nodup) :
    (vword (callSegs cs x V)).length ≤ 2 * x.length + 2 + m * (2 * W + 2) := by
  have h1 := length_vword_le (callSegs cs x V)
  have hlen : cs.args.length ≤ m := by simpa using hnd.length_le_card
  have h0 : rlen (cs.mode.seg0 x) ≤ 2 * x.length := by
    cases cs.mode
    · simp [Mode.seg0, rlen]
    · simp only [Mode.seg0, rlen, Bool.false_eq_true, ↓reduceIte]
      have := (List.takeWhile_prefix (fun b => decide (b = true)) (l := x)).length_le; omega
  have h2 := sum_rlen_argSegs_le (cs.args.map V) W (by simp; intro r _; exact hV r)
  simp only [callSegs, List.map_cons, List.sum_cons, List.length_cons, length_argSegs,
    List.length_map] at h1 h2 ⊢
  have h3 : cs.args.length * (2 * W) ≤ m * (2 * W) := Nat.mul_le_mul_right _ hlen
  have h4 : m * (2 * W + 2) = m * (2 * W) + 2 * m := by ring
  rw [h4]
  generalize m * (2 * W) = P at h3 ⊢
  generalize cs.args.length * (2 * W) = Q at h2 h3
  omega

/-- **Abstract register machines with logarithmic registers decide languages in `L`**: if, on
every input `x`, the abstract machine `A` (calling deciders for languages in `L`) answers
`x ∈ L`, through configurations meeting the syntactic preconditions with every register value
of at most `K · logSpace |x|` binary digits (counting one increment), then `L ∈ L`.

**Proof sketch.** The deciders are collected in a clean bank (`bank_cleanRun`). Virtual inputs
of calls have length at most `2|x| + 2 + m (2W + 2)` (`length_callSegs_le`), linear in `|x|`,
so the deciders' head ranges are `O(log |x|)` (`log_poly_bound`). `arm_space` then gives a
machine answering `x ∈ L` within `m (W + 2) + kD (2B + 1) = O(log |x|)` cells. -/
theorem arm_decides {L : Language Bool} [Fintype Λ] [DecidableEq Λ] (A : ARM m d Λ) (l₀ : Λ)
    (As : Fin d → Language Bool) (hAs : ∀ j, As j ∈ LOGSPACE) (K : ℕ)
    (hcorr : ∀ x, AHalt A (fun j V => MultiTapeTM.indicator (As j : Set (List Bool)) V) x
      (fun a => PreS A x a ∧ ∀ r, (Nat.bits (a.2.1 r + 1)).length ≤ K * logSpace x.length)
      (some l₀, fun _ => 0, none) (MultiTapeTM.indicator (L : Set (List Bool)) x)) :
    L ∈ LOGSPACE := by
  classical
  have hc : ∀ j, ∃ (c : ℕ) (M : FinTM Bool), M.DecidesInSpace (As j) fun n => c * logSpace n :=
    fun j => hAs j
  let c : Fin d → ℕ := fun j => Classical.choose (hc j)
  let Ms : Fin d → FinTM Bool := fun j => Classical.choose (Classical.choose_spec (hc j))
  have hMs : ∀ j, (Ms j).DecidesInSpace (As j) fun n => c j * logSpace n :=
    fun j => Classical.choose_spec (Classical.choose_spec (hc j))
  set cs := ∑ j, c j with hcs
  have hcj : ∀ j, c j ≤ cs := fun j =>
    Finset.single_le_sum (f := c) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  set Q := 4 + 2 * m + 2 * m * K with hQ
  obtain ⟨K2, hK2⟩ := log_poly_bound Q 1 0
  set kD := bankK Ms + bankK Ms with hkD
  set oracle : Fin d → List Bool → Bool :=
    fun j V => MultiTapeTM.indicator (As j : Set (List Bool)) V with horacle
  refine ⟨m * K + 2 * m + kD * (2 * cs * K2 + 3),
    compileFinTM (armProg A l₀) (l₀, .start) (bankTM Ms) (bankStart Ms), fun x => ?_⟩
  set n := x.length with hn
  set Ls := logSpace n with hLs
  have hL1 : 1 ≤ Ls := by simp [hLs, logSpace]
  have hLn : Ls ≤ n + 1 := by
    simp only [hLs, logSpace]
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h]; simp
    · have := Nat.log_lt_self 2 (show n ≠ 0 by omega); omega
  set W := K * Ls with hW
  set B := cs * K2 * Ls + 1 with hB
  obtain ⟨N, h1, h2, hm⟩ := hcorr x
  have hpre : ∀ t < N, Pre A oracle (bankTM Ms) (bankStart Ms) B x
      (arun A oracle x (some l₀, fun _ => 0, none) t) ∧
      ∀ r, ((Nat.bits ((arun A oracle x (some l₀, fun _ => 0, none) t).2.1 r + 1)).length : ℤ)
        ≤ (W : ℤ) := by
    intro t ht
    obtain ⟨hps, hbd⟩ := hm t ht
    refine ⟨?_, fun r => by exact_mod_cast hbd r⟩
    generalize hat : arun A oracle x (some l₀, fun _ => 0, none) t = a at hps hbd
    rcases a with ⟨_ | l, v, res⟩
    · trivial
    · simp only [Pre]
      cases hA : A l with
      | jeq r s' l₁ l₀' => simpa [PreS, hA] using hps
      | jeqIn r l₁ l₀' => simpa [PreS, hA] using hps
      | jeqFst r l₁ l₀' => simpa [PreS, hA] using hps
      | jeqSnd r l₁ l₀' => simpa [PreS, hA] using hps
      | inc => trivial
      | dec => trivial
      | clr => trivial
      | half => trivial
      | jz => trivial
      | jodd => trivial
      | ret => trivial
      | valP => trivial
      | valQ => trivial
      | call j md args l₁ l₀' =>
      simp only [PreS, hA] at hps
      refine ⟨hps, ?_⟩
      refine cleanRun_mono (bank_cleanRun Ms As (fun j n => c j * logSpace n) hMs j _) ?_
      have hVl := length_callSegs_le (x := x) ⟨j, md, args, l₁, l₀'⟩ W (fun r => Nat.bits (v r))
        (fun r => by
          show (Nat.bits (v r)).length ≤ W
          have h0 : (Nat.bits (v r + 1)).length ≤ W := hbd r
          have hle : (Nat.bits (v r)).length ≤ (Nat.bits (v r + 1)).length := by
            exact length_bits_mono (by omega)
          omega) hps
      have hVQ : (vword (callSegs ⟨j, md, args, l₁, l₀'⟩ x fun r => Nat.bits (v r))).length ≤
          Q * (n + 1) ^ 1 + 0 := by
        have : W ≤ K * (n + 1) := Nat.mul_le_mul_left K hLn
        have e : Q * (n + 1) ^ 1 + 0 = (4 + 2 * m) * (n + 1) + 2 * m * (K * (n + 1)) := by
          simp only [hQ]; ring
        rw [e]
        have h5 : m * (2 * W + 2) ≤ 2 * m * (K * (n + 1)) + 2 * m := by
          have := Nat.mul_le_mul_left (2 * m) this
          calc m * (2 * W + 2) = 2 * m * W + 2 * m := by ring
            _ ≤ 2 * m * (K * (n + 1)) + 2 * m := by omega
        have h6 : 2 * m ≤ 2 * m * (n + 1) := Nat.le_mul_of_pos_right _ (by omega)
        have h7 : (4 + 2 * m) * (n + 1) = 4 * (n + 1) + 2 * m * (n + 1) := by ring
        omega
      have hlog : logSpace (vword (callSegs ⟨j, md, args, l₁, l₀'⟩ x fun r => Nat.bits (v r))).length
          ≤ K2 * Ls := by
        have h := hK2 n
        have hm' := Nat.log_mono_right (b := 2) hVQ
        simp only [logSpace, hLs] at h hm' ⊢
        omega
      have hcm : c j * logSpace (vword (callSegs ⟨j, md, args, l₁, l₀'⟩ x
          fun r => Nat.bits (v r))).length ≤ cs * K2 * Ls := by
        calc _ ≤ c j * (K2 * Ls) := Nat.mul_le_mul_left _ hlog
          _ ≤ cs * (K2 * Ls) := Nat.mul_le_mul_right _ (hcj j)
          _ = cs * K2 * Ls := by ring
      simp only [hB]
      exact max_le (by omega) (by omega)
  obtain ⟨T, hT, hsp⟩ := arm_space A l₀ oracle (bankTM Ms) (bankStart Ms) B W N
    (MultiTapeTM.indicator (L : Set (List Bool)) x) h1 h2 hpre
  refine ⟨T, hT, hsp.trans ?_⟩
  · -- the arithmetic
    show _ ≤ (m * K + 2 * m + kD * (2 * cs * K2 + 3)) * Ls
    have e1 : m * (W + 2) = m * K * Ls + 2 * m := by simp only [hW]; ring
    have e2 : kD * (2 * B + 1) = 2 * kD * cs * K2 * Ls + 3 * kD := by simp only [hB]; ring
    have e3 : (m * K + 2 * m + kD * (2 * cs * K2 + 3)) * Ls =
        m * K * Ls + 2 * m * Ls + 2 * kD * cs * K2 * Ls + 3 * kD * Ls := by ring
    rw [e1, e2, e3]
    have f1 : 2 * m ≤ 2 * m * Ls := Nat.le_mul_of_pos_right _ (by omega)
    have f2 : 3 * kD ≤ 3 * kD * Ls := Nat.le_mul_of_pos_right _ (by omega)
    omega

end Complexity.LogProg

```


## ===== TCSlib/Complexity/SpaceComplexity/ImplicitPoly.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.Lib
import TCSlib.Complexity.SpaceComplexity.Machines.Bank
import TCSlib.Complexity.SpaceComplexity.ConfigCount

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Implicitly logspace computable functions are computable in logspace and in polynomial time

[AB09, Def 4.16 and p. 112]: an implicitly logspace computable function can be computed by a
machine with a write-once output tape in logarithmic space — for `i = 0, 1, 2, …` ask the
length language whether `i` is a position of `f(x)` and, if so, ask the bit language for
`f(x)ᵢ` and write it — and logspace computations run in polynomial time, so the function is
polynomial-time computable.

The enumeration is a register-tape program (`Complexity.LogProg.RProg`) with one register,
the binary counter `i`, calling the two deciders on the virtual input `⟨x, i⟩`; it is
compiled with `Complexity.LogProg.compile_space` against the decider bank
`Complexity.LogProg.bankTM`.

## Main results

* `Complexity.ImplicitlyLogspaceComputable.computesInSpace` — some machine computes `f` in
  space `O(log n)`. [AB09, Def 4.16; Exercise 4.8, one direction]
* `Complexity.ImplicitlyLogspaceComputable.polyTimeComputable` — `f` is polynomial-time
  computable. [AB09, p. 112: "logspace computations run in polynomial time"]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.3, Definition 4.16; §6.2.1, p. 112.)
-/

namespace Complexity

open Turing LogProg

/-- Membership of a pair in an index language. -/
lemma pairEncode_mem_indexLang (p : List Bool → ℕ → Prop) (x : List Bool) (i : ℕ) :
    pairEncode x (Nat.bits i) ∈ indexLang p ↔ p x i := by
  constructor
  · rintro ⟨x', i', h, hp⟩
    have := pairEncode_injective (a₁ := (x, Nat.bits i)) (a₂ := (x', Nat.bits i')) h
    simp only [Prod.mk.injEq] at this
    obtain ⟨rfl, hb⟩ := this
    rw [bits_injective hb]; exact hp
  · intro h; exact ⟨x, i, rfl, h⟩

namespace ImplicitEnum

/-- The states of the enumeration program. -/
inductive St where
  | ask | bit | emitT | emitF | incC | incB | done
  deriving DecidableEq, Fintype

/-- The ordinary transitions: emit a bit, increment the counter, halt. -/
def tm : MultiTapeTM 1 Bool St where
  q₀ := .ask
  tr
    | .emitT, _, _ => ⟨0, fun _ => (none, 0), some true, some .incC⟩
    | .emitF, _, _ => ⟨0, fun _ => (none, 0), some false, some .incC⟩
    | .incC, _, w => incCAct 0 .incC .incB (w 0)
    | .incB, _, w => incBAct 0 .incB .ask (w 0)
    | _, _, _ => ⟨0, fun _ => (none, 0), none, none⟩

/-- **The enumeration program**: at `ask`, ask decider `0` (the length language) about
`⟨x, i⟩`; at `bit`, ask decider `1` (the bit language); emit the answer; increment `i`. -/
def prog : RProg 1 2 St where
  tm := tm
  call
    | .ask => some ⟨0, .whole, [0], .bit, .done⟩
    | .bit => some ⟨1, .whole, [0], .emitT, .emitF⟩
    | _ => none

/-- The program configuration at the start of round `i`, having written `out`. -/
def cfg (x out : List Bool) (s : St) (i : ℕ) : Cfg 1 Bool St x :=
  ⟨some s, 1, fun _ => FinTM.bufferTape (Nat.bits i), fun _ => 0, out⟩

/-- The virtual input of both calls in round `i` is `⟨x, i⟩`. -/
lemma vword_call (x out : List Bool) (s : St) (i : ℕ) (dec : Fin 2) (yes no : St) :
    vword (callSegs ⟨dec, .whole, [0], yes, no⟩ x (regWords (cfg x out s i))) =
      pairEncode x (Nat.bits i) := by
  simp [callSegs, argSegs, regWords, cfg, tapeWord_bufferTape, vword, Mode.seg0, render,
    pairEncode_eq_dbl]

/-- The enumerator configuration `cfg x out s i` is in state `s`. -/
@[simp] lemma cfg_state (x out : List Bool) (s : St) (i : ℕ) : (cfg x out s i).state = some s :=
  rfl

/-- The call at `ask`. -/
lemma rstep_ask (o : Fin 2 → List Bool → Bool) (x out : List Bool) (i : ℕ) :
    rstep prog o (cfg x out .ask i) =
      cfg x out (if o 0 (pairEncode x (Nat.bits i)) then .bit else .done) i := by
  have h := vword_call x out .ask i 0 .bit .done
  have hc : prog.call .ask = some ⟨0, .whole, [0], .bit, .done⟩ := rfl
  simp only [rstep, cfg_state, hc]
  rw [h]; rfl

/-- The call at `bit`. -/
lemma rstep_bit (o : Fin 2 → List Bool → Bool) (x out : List Bool) (i : ℕ) :
    rstep prog o (cfg x out .bit i) =
      cfg x out (if o 1 (pairEncode x (Nat.bits i)) then .emitT else .emitF) i := by
  have h := vword_call x out .bit i 1 .emitT .emitF
  have hc : prog.call .bit = some ⟨1, .whole, [0], .emitT, .emitF⟩ := rfl
  simp only [rstep, cfg_state, hc]
  rw [h]; rfl

section Run

variable (f : List Bool → List Bool) (o : Fin 2 → List Bool → Bool)
  (ho0 : ∀ x i, o 0 (pairEncode x (Nat.bits i)) = decide (i < (f x).length))
  (ho1 : ∀ x i, o 1 (pairEncode x (Nat.bits i)) = (f x).getD i false)

/-- The configurations met along the run: a call configuration of some round, or an ordinary
configuration with the counter head in `[-1, W]`. -/
def Shape (x : List Bool) (F W : ℕ) (c : Cfg 1 Bool St x) : Prop :=
  (∃ out s i, i ≤ F ∧ (s = .ask ∨ s = .bit) ∧ c = cfg x out s i) ∨
  ((∀ l, c.state = some l → prog.call l = none) ∧ -1 ≤ c.workTapePos 0 ∧
    c.workTapePos 0 ≤ W)

/-- Writing the binary word of `n` on the counter of an enumerator configuration gives the
enumerator configuration with counter `n`. -/
lemma regCfg_cfg (x out : List Bool) (s s' : St) (i : ℕ) (n : ℕ) :
    regCfg (cfg x out s i) s' 0 (FinTM.bufferTape (Nat.bits n)) 0 = cfg x out s' n := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext r; rw [Fin.fin_one_eq_zero r]; simp [regCfg, cfg]
  · funext r; rw [Fin.fin_one_eq_zero r]; simp [regCfg, cfg]

include ho0 ho1 in
/-- **One round**: from round `i < |f x|` with `f(x)₀ … f(x)ᵢ₋₁` written, the program
writes `f(x)ᵢ` and reaches round `i + 1`.

**Proof sketch.** The round asks the bit decider (a call on `⟨x, bits i⟩`), emits the answer
`f(x)ᵢ` (`rstep_bit`), then increments the counter `i` with the increment fragment (`inc_run`).
Every intermediate configuration has the counter in binary of length at most `W` and output a
prefix of `f x`, which is `Shape`. -/
lemma round (x : List Bool) (i : ℕ) (hi : i < (f x).length) (F W : ℕ) (hF : (f x).length ≤ F)
    (hW : (Nat.bits (i + 1)).length ≤ W) :
    ∃ T, rrun prog o (cfg x ((f x).take i) .ask i) T = cfg x ((f x).take (i + 1)) .ask (i + 1) ∧
      ∀ t < T, Shape x F W (rrun prog o (cfg x ((f x).take i) .ask i) t) := by
  set b := (f x)[i] with hb
  have h1 : rrun prog o (cfg x ((f x).take i) .ask i) 1 = cfg x ((f x).take i) .bit i := by
    rw [rrun_one, rstep_ask, ho0]
    simp [hi]
  have h2 : rrun prog o (cfg x ((f x).take i) .bit i) 1 =
      cfg x ((f x).take i) (if b then .emitT else .emitF) i := by
    rw [rrun_one, rstep_bit, ho1]
    simp [hb, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  have h3 : rrun prog o (cfg x ((f x).take i) (if b then .emitT else .emitF) i) 1 =
      cfg x ((f x).take (i + 1)) .incC i := by
    rw [rrun_one, rstep_noncall prog o _ (if b then .emitT else .emitF) rfl (by cases b <;> rfl)]
    unfold MultiTapeTM.step
    simp only [cfg]
    have ht : (f x).take (i + 1) = (f x).take i ++ [b] := by
      rw [hb, List.take_succ, List.getElem?_eq_getElem hi]; rfl
    rw [ht]
    cases b <;> (refine Cfg.ext rfl ?_ ?_ ?_ ?_) <;> simp [prog, tm, Action.apply]
  obtain ⟨T₄, h4, hm4⟩ := inc_run prog o 0 .incC .incB .ask (fun _ _ => rfl) (fun _ _ => rfl)
    rfl rfl (cfg x ((f x).take (i + 1)) .incC i) i
  rw [regCfg_cfg, regCfg_cfg] at h4
  refine ⟨1 + (1 + (1 + T₄)), ?_, fun t ht => ?_⟩
  · rw [rrun_add, h1, rrun_add, h2, rrun_add, h3, h4]
  · rcases Nat.lt_or_ge t 1 with h | h
    · obtain rfl : t = 0 := by omega
      exact Or.inl ⟨_, .ask, i, by omega, Or.inl rfl, rfl⟩
    obtain ⟨t, rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
    rw [rrun_add, h1]
    rcases Nat.lt_or_ge t 1 with h | h
    · obtain rfl : t = 0 := by omega
      exact Or.inl ⟨_, .bit, i, by omega, Or.inr rfl, rfl⟩
    obtain ⟨t, rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
    rw [rrun_add, h2]
    rcases Nat.lt_or_ge t 1 with h | h
    · obtain rfl : t = 0 := by omega
      refine Or.inr ⟨fun l hl => ?_, by simp [rrun_zero, cfg], by simp [rrun_zero, cfg]⟩
      simp only [rrun_zero, cfg, Option.some.injEq] at hl
      subst hl; cases b <;> rfl
    obtain ⟨t, rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
    rw [rrun_add, h3]
    obtain ⟨s', f', q, hq, hs', hq1, hq2⟩ := hm4 t (by omega)
    rw [regCfg_cfg] at hq
    rw [hq]
    refine Or.inr ⟨fun l hl => ?_, ?_, ?_⟩
    · simp only [regCfg, Option.some.injEq] at hl
      subst hl; rcases hs' with rfl | rfl <;> rfl
    · simpa [regCfg] using hq1
    · simp only [regCfg, Function.update_self]; omega

include ho0 ho1 in
/-- All rounds: from the start the program reaches round `i ≤ |f x|`. -/
lemma rounds (x : List Bool) (F W : ℕ) (hF : (f x).length ≤ F)
    (hW : ∀ i < (f x).length, (Nat.bits (i + 1)).length ≤ W) :
    ∀ i ≤ (f x).length, ∃ T, rrun prog o (cfg x [] .ask 0) T = cfg x ((f x).take i) .ask i ∧
      ∀ t < T, Shape x F W (rrun prog o (cfg x [] .ask 0) t) := by
  intro i
  induction i with
  | zero => intro _; exact ⟨0, by simp [rrun_zero], fun t ht => absurd ht (by omega)⟩
  | succ i ih =>
    intro hi
    obtain ⟨T₁, h1, hm1⟩ := ih (by omega)
    obtain ⟨T₂, h2, hm2⟩ := round f o ho0 ho1 x i (by omega) F W hF (hW i (by omega))
    refine ⟨T₁ + T₂, by rw [rrun_add, h1, h2], fun t ht => ?_⟩
    rcases Nat.lt_or_ge t T₁ with h | h
    · exact hm1 t h
    · obtain ⟨t', rfl⟩ : ∃ t', t = T₁ + t' := ⟨t - T₁, by omega⟩
      rw [rrun_add, h1]; exact hm2 t' (by omega)

include ho0 ho1 in
/-- **The whole run**: the program halts with output `f x`, every configuration before the
halt having the shape `Shape`.

**Proof sketch.** Induction on the number of rounds: `round` takes round `i` to round `i + 1`
for `i < |f x|`; at `i = |f x|` the length decider answers no and the program halts with output
`f x` and counter head home. The shape invariant is collected round by round. -/
lemma run (x : List Bool) (F W : ℕ) (hF : (f x).length ≤ F)
    (hW : ∀ i < (f x).length, (Nat.bits (i + 1)).length ≤ W) :
    ∃ N, (rrun prog o (Cfg.init .ask x) N).state = none ∧
      (rrun prog o (Cfg.init .ask x) N).output = f x ∧
      (rrun prog o (Cfg.init .ask x) N).workTapePos 0 = 0 ∧
      ∀ t < N, Shape x F W (rrun prog o (Cfg.init .ask x) t) := by
  have hinit : (Cfg.init .ask x : Cfg 1 Bool St x) = cfg x [] .ask 0 := by
    refine Cfg.ext rfl rfl ?_ rfl rfl
    funext r z; simp [cfg, Nat.zero_bits]
  rw [hinit]
  obtain ⟨T, h1, hm1⟩ := rounds f o ho0 ho1 x F W hF hW (f x).length le_rfl
  rw [List.take_length] at h1
  have h2 : rrun prog o (cfg x (f x) .ask (f x).length) 1 = cfg x (f x) .done (f x).length := by
    rw [rrun_one, rstep_ask, ho0]; simp
  have h3 : (rrun prog o (cfg x (f x) .done (f x).length) 1).state = none ∧
      (rrun prog o (cfg x (f x) .done (f x).length) 1).output = f x ∧
      (rrun prog o (cfg x (f x) .done (f x).length) 1).workTapePos 0 = 0 := by
    rw [rrun_one, rstep_noncall prog o _ .done rfl rfl]
    simp [MultiTapeTM.step, cfg, prog, tm, Action.apply]
  refine ⟨T + (1 + 1), ?_, ?_, ?_, fun t ht => ?_⟩
  · rw [rrun_add, h1, rrun_add, h2]; exact h3.1
  · rw [rrun_add, h1, rrun_add, h2]; exact h3.2.1
  · rw [rrun_add, h1, rrun_add, h2]; exact h3.2.2
  · rcases Nat.lt_or_ge t T with h | h
    · exact hm1 t h
    · obtain ⟨t', rfl⟩ : ∃ t', t = T + t' := ⟨t - T, by omega⟩
      rw [rrun_add, h1]
      rcases Nat.lt_or_ge t' 1 with h' | h'
      · obtain rfl : t' = 0 := by omega
        exact Or.inl ⟨_, .ask, _, hF, Or.inl rfl, rfl⟩
      · obtain rfl : t' = 1 := by omega
        rw [h2]
        refine Or.inr ⟨fun l hl => ?_, by simp [cfg], by simp [cfg]⟩
        simp only [cfg_state, Option.some.injEq] at hl
        subst hl; rfl

end Run

end ImplicitEnum

/-- **Implicitly logspace computable functions are computable in logspace** [AB09, Def 4.16;
one direction of Exercise 4.8]: some machine computes `f` visiting `O(log n)` work cells.

**Proof sketch.** The enumeration program `ImplicitEnum.prog` keeps `i` in binary on one
register and, for `i = 0, 1, …`, asks the length language and the bit language about `⟨x, i⟩`
and writes the answer (`ImplicitEnum.run`). `i ≤ |f(x)| ≤ C (n+1)^e`, so the counter has
`O(log n)` bits, and the deciders run on inputs of length `2n + 2 + O(log n)`, in space
`O(log n)`. `compile_space` turns the program into a machine computing `f` within the
register range plus `kD (2B + 1)` cells, which `log_poly_bound` shows to be `O(log n)`. -/
theorem ImplicitlyLogspaceComputable.computesInSpace {f : List Bool → List Bool}
    (hf : ImplicitlyLogspaceComputable f) :
    ∃ (M : FinTM Bool) (c : ℕ), M.ComputesInSpace f fun n => c * logSpace n := by
  classical
  obtain ⟨⟨C, e, hlen⟩, ⟨c1, M1, hM1⟩, ⟨c0, M0, hM0⟩⟩ := hf
  let Ms : Fin 2 → FinTM Bool := fun j => if j = 0 then M0 else M1
  let A : Fin 2 → Language Bool := fun j => if j = 0 then
    indexLang (fun x i => i < (f x).length) else indexLang (fun x i => (f x).getD i false = true)
  let s : Fin 2 → ℕ → ℕ := fun j n => if j = 0 then c0 * logSpace n else c1 * logSpace n
  have hMs : ∀ j, (Ms j).DecidesInSpace (A j) (s j) := by
    intro j
    by_cases hj : j = 0
    · subst hj; simpa [Ms, A, s] using hM0
    · have hj1 : j = 1 := Fin.ext (by
        have := j.isLt; have : j.val ≠ 0 := fun h => hj (Fin.ext h); simp; omega)
      subst hj1; simpa [Ms, A, s] using hM1
  let o : Fin 2 → List Bool → Bool := fun j V => MultiTapeTM.indicator (A j : Set (List Bool)) V
  have ho0 : ∀ x i, o 0 (pairEncode x (Nat.bits i)) = decide (i < (f x).length) := by
    intro x i
    have := pairEncode_mem_indexLang (fun x i => i < (f x).length) x i
    by_cases h : i < (f x).length <;>
      simp_all [o, A, MultiTapeTM.indicator]
  have ho1 : ∀ x i, o 1 (pairEncode x (Nat.bits i)) = (f x).getD i false := by
    intro x i
    have := pairEncode_mem_indexLang (fun x i => (f x).getD i false = true) x i
    cases h : (f x).getD i false <;> simp_all [o, A, MultiTapeTM.indicator]
  obtain ⟨K1, hK1⟩ := LogProg.log_poly_bound C e 1
  obtain ⟨K2, hK2⟩ := LogProg.log_poly_bound (C + 2) (e + 1) 2
  set kD := bankK Ms + bankK Ms with hkD
  refine ⟨compileFinTM ImplicitEnum.prog .ask (bankTM Ms) (bankStart Ms),
    K1 + 2 + kD * (2 * ((c0 + c1) * K2 + 1) + 1), fun x => ?_⟩
  set n := x.length with hn
  set F := C * (n + 1) ^ e with hFdef
  set W := Nat.log 2 (F + 1) + 1 with hWdef
  set B := (c0 + c1) * logSpace (2 * n + 2 + W) + 1 with hBdef
  have hF : (f x).length ≤ F := hlen x
  have hbitsW : ∀ i ≤ F + 1, (Nat.bits i).length ≤ W := fun i hi =>
    (LogProg.length_bits_le_log i).trans (by have := Nat.log_mono_right (b := 2) hi; omega)
  obtain ⟨N, hN1, hN2, hN3, hNs⟩ := ImplicitEnum.run f o ho0 ho1 x F W hF
    (fun i hi => hbitsW (i + 1) (by omega))
  have hbox : ∀ t ≤ N, ∀ r : Fin 1, (-1 : ℤ) ≤ (rrun ImplicitEnum.prog o (Cfg.init .ask x) t).workTapePos r ∧
      (rrun ImplicitEnum.prog o (Cfg.init .ask x) t).workTapePos r ≤ (W : ℤ) := by
    intro t ht r
    rw [Fin.fin_one_eq_zero r]
    rcases Nat.lt_or_ge t N with h | h
    · rcases hNs t h with ⟨out, s', i, -, -, hc⟩ | ⟨-, h1, h2⟩
      · rw [hc]; simp [ImplicitEnum.cfg]
      · exact ⟨h1, h2⟩
    · obtain rfl : t = N := by omega
      rw [hN3]; simp
  have hcalls : ∀ t < N, CallOK ImplicitEnum.prog (bankTM Ms) (bankStart Ms) o (fun _ => -1)
      (fun _ => (W : ℤ)) B (rrun ImplicitEnum.prog o (Cfg.init .ask x) t) := by
    intro t ht l cs hl hcs
    rcases hNs t ht with ⟨out, s', i, hi, hs', hc⟩ | ⟨hnc, -, -⟩
    · rw [hc] at hl ⊢
      simp only [ImplicitEnum.cfg_state, Option.some.injEq] at hl
      subst hl
      have hreg : regWords (ImplicitEnum.cfg x out s' i) = fun _ => Nat.bits i := by
        funext r; simp [regWords, ImplicitEnum.cfg, tapeWord_bufferTape]
      have hV : vword (callSegs cs x (regWords (ImplicitEnum.cfg x out s' i))) =
          pairEncode x (Nat.bits i) := by
        rcases hs' with rfl | rfl <;> simp only [ImplicitEnum.prog, Option.some.injEq] at hcs <;>
          (subst hcs; exact ImplicitEnum.vword_call _ _ _ _ _ _ _)
      have hargs : cs.args = [0] := by
        rcases hs' with rfl | rfl <;> simp only [ImplicitEnum.prog, Option.some.injEq] at hcs <;>
          (subst hcs; rfl)
      refine ⟨by rw [hargs]; simp, rfl, ?_, ?_⟩
      · intro r hr
        rw [hargs] at hr
        simp only [List.mem_singleton] at hr
        subst hr
        rw [hreg]
        refine ⟨rfl, rfl, le_rfl, ?_⟩
        beta_reduce
        exact_mod_cast hbitsW i (by omega)
      · rw [hV]
        refine (bank_cleanRun Ms A s hMs cs.dec _).mono ?_
        have hlenV : (pairEncode x (Nat.bits i)).length ≤ 2 * n + 2 + W := by
          have := hbitsW i (by omega)
          simp [pairEncode, hn]; omega
        have hsj : s cs.dec (pairEncode x (Nat.bits i)).length ≤
            (c0 + c1) * logSpace (2 * n + 2 + W) := by
          have hm := logSpace_mono hlenV
          simp only [s]
          split_ifs
          · exact (Nat.mul_le_mul_left c0 hm).trans (Nat.mul_le_mul_right _ (by omega))
          · exact (Nat.mul_le_mul_left c1 hm).trans (Nat.mul_le_mul_right _ (by omega))
        simp only [hBdef]
        omega
    · exact absurd hcs (by rw [hnc l hl]; simp)
  obtain ⟨T, hT, hTs⟩ := compile_space ImplicitEnum.prog .ask (bankTM Ms) (bankStart Ms) o
    (fun _ => -1) (fun _ => (W : ℤ)) B N (f x) hN1 hN2 hbox hcalls
  refine ⟨T, hT, hTs.trans ?_⟩
  -- the arithmetic
  simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
  have hW2 : (((W : ℤ) - -1 + 1).toNat) = W + 2 := by omega
  rw [hW2]
  set L := logSpace n with hL
  have hL1 : 1 ≤ L := by simp [hL, logSpace]
  have hWL : W + 2 ≤ (K1 + 2) * L := by
    have := hK1 n
    simp only [hWdef, hFdef]
    have : (K1 + 2) * L = K1 * L + 2 * L := by ring
    simp only [logSpace] at hL
    rw [hL] at *
    omega
  have hlogW : logSpace (2 * n + 2 + W) ≤ K2 * L := by
    have hWle : W ≤ F + 2 := by
      have := Nat.log_le_self 2 (F + 1); omega
    have hle : 2 * n + 2 + W ≤ (C + 2) * (n + 1) ^ (e + 1) + 2 := by
      have h1 : n + 1 ≤ (n + 1) ^ (e + 1) := by
        calc n + 1 = (n + 1) ^ 1 := by ring
          _ ≤ (n + 1) ^ (e + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      have h2 : (n + 1) ^ e ≤ (n + 1) ^ (e + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      have h3 : F ≤ C * (n + 1) ^ (e + 1) := Nat.mul_le_mul_left C h2
      have : (C + 2) * (n + 1) ^ (e + 1) = C * (n + 1) ^ (e + 1) + 2 * (n + 1) ^ (e + 1) := by
        ring
      omega
    have := hK2 n
    have hm := logSpace_mono hle
    simp only [logSpace] at hm this ⊢
    simp only [hL, logSpace]
    omega
  have hBL : 2 * B + 1 ≤ (2 * ((c0 + c1) * K2 + 1) + 1) * L := by
    have h1 : (c0 + c1) * logSpace (2 * n + 2 + W) ≤ (c0 + c1) * (K2 * L) :=
      Nat.mul_le_mul_left _ hlogW
    have e1 : (2 * ((c0 + c1) * K2 + 1) + 1) * L = 2 * ((c0 + c1) * (K2 * L)) + 3 * L := by ring
    rw [e1]
    simp only [hBdef]
    omega
  calc W + 2 + kD * (2 * B + 1) ≤ (K1 + 2) * L + kD * ((2 * ((c0 + c1) * K2 + 1) + 1) * L) :=
        Nat.add_le_add hWL (Nat.mul_le_mul_left _ hBL)
    _ = (K1 + 2 + kD * (2 * ((c0 + c1) * K2 + 1) + 1)) * L := by ring

/-- **Implicitly logspace computable functions are polynomial-time computable**
[AB09, p. 112: "logspace computations run in polynomial time"].

**Proof sketch.** `ImplicitlyLogspaceComputable.computesInSpace` gives a machine computing
`f` in logarithmic space; by configuration counting
(`Complexity.polyTimeComputable_of_computesInSpace`) it runs in polynomial time. -/
theorem ImplicitlyLogspaceComputable.polyTimeComputable {f : List Bool → List Bool}
    (hf : ImplicitlyLogspaceComputable f) : PolyTimeComputable f := by
  obtain ⟨M, c, hM⟩ := hf.computesInSpace
  exact polyTimeComputable_of_computesInSpace hM

end Complexity

```


## ===== TCSlib/Complexity/SpaceComplexity/Machines/ARMKit.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.ARMProof
import TCSlib.Complexity.SpaceComplexity.ImplicitPoly

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A toolkit for abstract register machines

Conveniences for writing logspace algorithms as abstract register machines
(`Complexity.LogProg.ARM`) on inputs `⟨1ⁿ, w⟩`: the virtual inputs of calls in `unaryFst`
mode with one or two register arguments are `⟨1ⁿ, bits r⟩` and `⟨1ⁿ, ⟨bits r, bits s⟩⟩`,
and `Complexity.LogProg.arm_decides_poly` restates `Complexity.LogProg.arm_decides` with
register values bounded by a polynomial in the input length.

## Main results

* `Complexity.LogProg.vword_unary₁`, `Complexity.LogProg.vword_unary₂` — virtual inputs
  of `unaryFst` calls.
* `Complexity.LogProg.arm_decides_poly` — abstract register machines with polynomially
  bounded register values decide languages in `L`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.)
-/

namespace Complexity.LogProg

open Turing

variable {m d : ℕ} {Λ : Type}

/-- The leading run of `1`s of `⟨1ⁿ, w⟩` is `1²ⁿ`. -/
lemma takeWhile_pairEncode_replicate (n : ℕ) (w : List Bool) :
    (pairEncode (List.replicate n true) w).takeWhile (· = true) =
      List.replicate (2 * n) true := by
  simp only [pairEncode_eq_dbl, dbl_replicate, List.append_assoc]
  rw [List.takeWhile_append_of_pos (by simp)]
  simp

/-- The virtual input of a `unaryFst` call with one argument on `⟨1ⁿ, w⟩` is `⟨1ⁿ, V r⟩`. -/
lemma vword_unary₁ (n : ℕ) (w : List Bool) (j : Fin d) (r : Fin m) (l₁ l₀ : Λ)
    (V : Fin m → List Bool) :
    vword (callSegs ⟨j, .unaryFst, [r], l₁, l₀⟩ (pairEncode (List.replicate n true) w) V) =
      pairEncode (List.replicate n true) (V r) := by
  simp only [callSegs, Mode.seg0, takeWhile_pairEncode_replicate, List.map_cons,
    List.map_nil, argSegs, vword, render, Bool.false_eq_true, ↓reduceIte]
  simp [pairEncode_eq_dbl, dbl_replicate]

/-- The virtual input of a `unaryFst` call with two arguments on `⟨1ⁿ, w⟩` is
`⟨1ⁿ, ⟨V r, V s⟩⟩`. -/
lemma vword_unary₂ (n : ℕ) (w : List Bool) (j : Fin d) (r s : Fin m) (l₁ l₀ : Λ)
    (V : Fin m → List Bool) :
    vword (callSegs ⟨j, .unaryFst, [r, s], l₁, l₀⟩ (pairEncode (List.replicate n true) w) V) =
      pairEncode (List.replicate n true) (pairEncode (V r) (V s)) := by
  simp only [callSegs, Mode.seg0, takeWhile_pairEncode_replicate, List.map_cons,
    List.map_nil, argSegs, vword, render, Bool.false_eq_true, ↓reduceIte]
  simp [pairEncode_eq_dbl, dbl_replicate]

/-- The indicator of a set at a point, as a decision. -/
lemma indicator_eq_decide {α : Type} (S : Set α) (a : α) :
    MultiTapeTM.indicator S a = @decide (a ∈ S) (Classical.dec _) := by
  unfold MultiTapeTM.indicator; split <;> simp_all

/-- **Abstract register machines with polynomially bounded registers decide languages in
`L`**: the form of `arm_decides` with register values at most `C₀ (|x| + 1)^{c₀}`.

**Proof sketch.** A value `v ≤ C₀ (|x|+1)^{c₀}` has `|bits (v + 1)| ≤ ⌊log₂ (v + 1)⌋ + 1`,
which `log_poly_bound` bounds by `K · logSpace |x|`. -/
theorem arm_decides_poly {L : Language Bool} [Fintype Λ] [DecidableEq Λ] (A : ARM m d Λ)
    (l₀ : Λ) (As : Fin d → Language Bool) (hAs : ∀ j, As j ∈ LOGSPACE) (C₀ c₀ : ℕ)
    (hcorr : ∀ x, AHalt A (fun j V => MultiTapeTM.indicator (As j : Set (List Bool)) V) x
      (fun a => PreS A x a ∧ ∀ r, a.2.1 r ≤ C₀ * (x.length + 1) ^ c₀)
      (some l₀, fun _ => 0, none) (MultiTapeTM.indicator (L : Set (List Bool)) x)) :
    L ∈ LOGSPACE := by
  obtain ⟨K, hK⟩ := log_poly_bound C₀ c₀ 1
  refine arm_decides A l₀ As hAs K fun x => (hcorr x).mono fun a ⟨h1, h2⟩ => ⟨h1, fun r => ?_⟩
  have e1 := length_bits_le_log (a.2.1 r + 1)
  have e2 : Nat.log 2 (a.2.1 r + 1) ≤ Nat.log 2 (C₀ * (x.length + 1) ^ c₀ + 1) :=
    Nat.log_mono_right (by have := h2 r; omega)
  have e3 := hK x.length
  simp only [logSpace]
  omega

end Complexity.LogProg

```


## ===== TCSlib/Complexity/SpaceComplexity/Machines/DblLang.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.ARMKit

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Reading the unary length in logarithmic space

The abstract register machines of `TCSlib.Complexity.SpaceComplexity.Machines.ARM` see their
input `⟨1ⁿ, w⟩` only through comparisons with `w` and through calls to logspace deciders on
`⟨1ⁿ, …⟩`; none of their instructions measures `n`. This file supplies the missing base
decider, written directly as a register-tape program: it counts the leading run `1²ⁿ` of
`⟨1ⁿ, w⟩ = 1²ⁿ 0 1 w` into a binary register and compares the register with `w`
[AB09, §4.1: a logspace machine keeps a counter of `O(log n)` bits].

The decider is generic logspace material; its first client is [AB09, Thm 6.15]
(`TCSlib.Complexity.CircuitComplexity.LogspaceTableau`).

## Main definitions

* `Complexity.LogProg.dblLang` — the inputs `⟨1ⁿ, bits (2n)⟩`.
* `Complexity.LogProg.Dbl.prog` — the register-tape program deciding it.

## Main results

* `Complexity.LogProg.dblLang_mem` — `dblLang ∈ L`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.)
-/

namespace Complexity.LogProg

open Turing

/-- The inputs `⟨1ⁿ, bits (2n)⟩`: the index on the input is twice the unary length. -/
def dblLang : Language Bool :=
  {y | ∃ n, y = pairEncode (List.replicate n true) (Nat.bits (2 * n))}

namespace Dbl

/-- The states of the counting program. -/
inductive St where
  | vU0 | vU1 | vS | vW0 | vWF | vWT | rw1 | rw2 | cnt | iC | iB | sw1 | sw2
  | jK | jK2 | jC | jRB (b : Bool) | jI1 (b : Bool) | jI2 (b : Bool) | yes | no
  deriving DecidableEq, Fintype

/-- The transitions: the format check (`vU0` … `rw2`), the count of the leading `1`s
(`cnt`, with the increment fragment `iC`, `iB`), the rewind (`sw1`, `sw2`), and the
comparison of the counter with the index (`jK` … `jI2`). -/
def tr : St → Option Bool → (Fin 1 → Option Bool) → Action 1 Bool St
  | .vU0, a, _ => valUAct 0 .vU0 .vU1 .vS false a
  | .vU1, a, _ => valUAct 0 .vU0 .vU1 .vS true a
  | .vS, a, _ => valSAct 0 .vW0 a
  | .vW0, a, _ => valWAct 0 .vWF .vWT .rw1 none a
  | .vWF, a, _ => valWAct 0 .vWF .vWT .rw1 (some false) a
  | .vWT, a, _ => valWAct 0 .vWF .vWT .rw1 (some true) a
  | .rw1, _, _ => xAct 0 (-1) 0 .rw2
  | .rw2, a, _ => rw2Act 0 .rw2 .cnt a
  | .cnt, a, _ => if a = some true then xAct 0 1 0 .iC else xAct 0 0 0 .sw1
  | .iC, _, w => incCAct 0 .iC .iB (w 0)
  | .iB, _, w => incBAct 0 .iB .cnt (w 0)
  | .sw1, _, _ => xAct 0 (-1) 0 .sw2
  | .sw2, a, _ => rw2Act 0 .sw2 .jK a
  | .jK, a, _ => skipAct 0 .jK .jK2 a
  | .jK2, _, _ => xAct 0 1 0 .jC
  | .jC, a, w => cmpAct 0 .jC St.jRB a (w 0)
  | .jRB b, _, w => backAct 0 (.jRB b) (.jI1 b) (w 0)
  | .jI1 b, _, _ => xAct 0 (-1) 0 (.jI2 b)
  | .jI2 b, a, _ => rewAct 0 (.jI2 b) (if b then .yes else .no) a
  | .yes, _, _ => retAct true
  | .no, _, _ => retAct false

/-- **The counting program** (one register, no calls). -/
def prog : RProg 1 0 St where
  tm := ⟨.vU0, tr⟩
  call := fun _ => none

/-- The (empty) oracle. -/
def o : Fin 0 → List Bool → Bool := fun j => j.elim0

variable {y : List Bool}

/-- The configuration in state `s`, input head `ip`, register holding `bits v` with its head at
`q`, nothing written. -/
def K (s : St) (ip : Fin (y.length + 2)) (v : ℕ) (q : ℤ) : Cfg 1 Bool St y :=
  ⟨some s, ip, fun _ => FinTM.bufferTape (Nat.bits v), fun _ => q, []⟩

/-- The input-scanning view of a counting configuration is a counting configuration. -/
lemma xCfg_K (s s' : St) (ip ip' : Fin (y.length + 2)) (v : ℕ) (q q' : ℤ) :
    xCfg (K s' ip' v q') s ip 0 q = K s ip v q := by
  refine Cfg.ext rfl rfl rfl ?_ rfl
  funext r; rw [Fin.fin_one_eq_zero r]; simp [xCfg, K]

/-- The register view of a counting configuration is a counting configuration. -/
lemma regCfg_K (s s' : St) (ip : Fin (y.length + 2)) (v v' : ℕ) (q q' : ℤ) :
    regCfg (K s' ip v q') s 0 (FinTM.bufferTape (Nat.bits v')) q = K s ip v' q := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext r; rw [Fin.fin_one_eq_zero r]; simp [regCfg, K]
  · funext r; rw [Fin.fin_one_eq_zero r]; simp [regCfg, K]

/-- A run from `c` to `c'` with the register head in `[-1, W]`. -/
def Rch (W : ℕ) (c c' : Cfg 1 Bool St y) : Prop :=
  ∃ T, rrun prog o c T = c' ∧ ∀ t < T, -1 ≤ (rrun prog o c t).workTapePos 0 ∧
    (rrun prog o c t).workTapePos 0 ≤ W

/-- Runs compose. -/
lemma Rch.trans {W : ℕ} {a b c : Cfg 1 Bool St y} (h₁ : Rch W a b) (h₂ : Rch W b c) :
    Rch W a c := by
  obtain ⟨T₁, e1, m1⟩ := h₁
  obtain ⟨T₂, e2, m2⟩ := h₂
  refine ⟨T₁ + T₂, by rw [rrun_add, e1, e2], fun t ht => ?_⟩
  rcases Nat.lt_or_ge t T₁ with h | h
  · exact m1 t h
  · obtain ⟨t', rfl⟩ : ∃ t', t = T₁ + t' := ⟨t - T₁, by omega⟩
    rw [rrun_add, e1]; exact m2 t' (by omega)

/-- One input-scanning step. -/
lemma step_x (s s' : St) (ip : Fin (y.length + 2)) (v : ℕ) (q : ℤ) (mvI : SignType)
    (h : ∀ w, tr s (inSym y ip.val) w = xAct 0 mvI 0 s') :
    rrun prog o (K s ip v q) 1 = K s' (moveInputPos ip mvI) v q := by
  rw [← xCfg_K s s ip ip v q q, rrun_one_x prog o _ s ip 0 q rfl]
  change (tr s (inSym y ip.val) _).apply _ = _
  rw [h, apply_xAct]
  simp only [SignType.coe_zero, add_zero]
  exact xCfg_K _ _ _ _ _ _ _

/-- The symbols of `⟨1ⁿ, w⟩`: `1` before position `2n`, `0` at `2n`. -/
lemma sym_lt {n : ℕ} {w : List Bool} (hy : y = pairEncode (List.replicate n true) w) {k : ℕ}
    (hk : k < 2 * n) : y[k]? = some true := by
  subst hy
  rw [pairEncode_eq_dbl, dbl_replicate, List.append_assoc,
    List.getElem?_append_left (by simpa using hk)]
  simp [hk]

/-- The separator `0` of `⟨1ⁿ, w⟩` sits at position `2n`. -/
lemma sym_eq {n : ℕ} {w : List Bool} (hy : y = pairEncode (List.replicate n true) w) :
    y[2 * n]? = some false := by
  subst hy
  rw [pairEncode_eq_dbl, dbl_replicate, List.append_assoc,
    List.getElem?_append_right (by simp)]
  simp

/-- The length of `⟨1ⁿ, w⟩` is `2n + 2 + |w|`. -/
lemma length_eq {n : ℕ} {w : List Bool} (hy : y = pairEncode (List.replicate n true) w) :
    y.length = 2 * n + 2 + w.length := by
  subst hy; simp [pairEncode_eq_dbl, dbl_replicate]; omega

/-- **The counting loop**: from `cnt` at input position `1` with counter `0`, the program
reaches `cnt` at position `1 + j` with counter `j`, for every `j ≤ 2n`.

**Proof sketch.** Induction on `j`: one `cnt` step reads a `1` and moves right, then the
increment fragment (`inc_run`) adds one to the counter; the register head stays within
`|bits (2n)|` since `j + 1 ≤ 2n` (`length_bits_mono`). -/
lemma count {n : ℕ} {w : List Bool} (hy : y = pairEncode (List.replicate n true) w) :
    ∀ j (hj : j ≤ 2 * n), Rch (Nat.bits (2 * n)).length
      (K (y := y) .cnt ⟨1, by have := length_eq hy; omega⟩ 0 0)
      (K (y := y) .cnt ⟨1 + j, by have := length_eq hy; omega⟩ j 0) := by
  have hl := length_eq hy
  intro j
  induction j with
  | zero => intro _; exact ⟨0, rfl, fun t ht => by omega⟩
  | succ j ih =>
    intro hj
    refine (ih (by omega)).trans ?_
    have h1 : rrun prog o (K .cnt ⟨1 + j, by omega⟩ j 0) 1 =
        K (y := y) .iC ⟨2 + j, by omega⟩ j 0 := by
      rw [step_x .cnt .iC _ j 0 1 (fun w => by
        simp only [tr, show 1 + j = j + 1 by omega, inSym_succ, sym_lt hy (by omega : j < 2 * n),
          ↓reduceIte])]
      congr 1; exact Fin.ext (by rw [moveInputPos_pos_val _ (by simp; omega)]; simp; omega)
    obtain ⟨T, h2, hm2⟩ := inc_run prog o 0 .iC .iB .cnt (fun _ _ => rfl) (fun _ _ => rfl) rfl rfl
      (K (y := y) .iC ⟨2 + j, by omega⟩ j 0) j
    rw [regCfg_K, regCfg_K] at h2
    refine ⟨1 + T, ?_, fun t ht => ?_⟩
    · rw [rrun_add, h1, h2]; congr 1; exact Fin.ext (by simp; omega)
    · rcases Nat.lt_or_ge t 1 with h | h
      · obtain rfl : t = 0 := by omega
        simp [rrun_zero, K]
      · obtain ⟨t', rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
        rw [rrun_add, h1]
        obtain ⟨s, f, q, hq, -, hq1, hq2⟩ := hm2 t' (by omega)
        rw [regCfg_K] at hq
        rw [hq]
        have := length_bits_mono (show j + 1 ≤ 2 * n by omega)
        simp only [regCfg, Function.update_self]
        omega

/-- The initial configuration. -/
lemma init_eq : (Cfg.init (k := 1) St.vU0 y) = K .vU0 ⟨1, by omega⟩ 0 0 := by
  refine Cfg.ext rfl rfl ?_ rfl rfl
  funext r z; simp [K, Nat.zero_bits]

/-- **The run on a well-formed input** `⟨1ⁿ, w⟩`: the program answers whether `w = bits (2n)`,
the register head staying in `[-1, |bits (2n)|]`.

**Proof sketch.** The format check (`valPlain_run`) returns to position `1`; the counting
loop (`count`) leaves `bits (2n)` in the register at the separator; the rewind
(`rewind_x`) and the comparison (`jeqPlain_run`) decide `w = bits (2n)`; one step answers. -/
lemma run_valid {n : ℕ} {w : List Bool} (hy : y = pairEncode (List.replicate n true) w)
    (hw : Canon w) :
    Rch (Nat.bits (2 * n)).length (K .vU0 ⟨1, by omega⟩ 0 0)
      (K (y := y) (if w = Nat.bits (2 * n) then .yes else .no) ⟨1, by omega⟩ (2 * n) 0) := by
  have hl := length_eq hy
  set W := (Nat.bits (2 * n)).length
  -- the format check
  have h1 : Rch W (K .vU0 ⟨1, by omega⟩ 0 0) (K (y := y) .cnt ⟨1, by omega⟩ 0 0) := by
    obtain ⟨T, e, hm⟩ := (valPlain_run (P := prog) (oracle := o) (r := 0) (vU0 := .vU0)
      (vU1 := .vU1) (vS := .vS) (vW0 := .vW0) (vWF := .vWF) (vWT := .vWT) (rw₁ := .rw1)
      (rw₂ := .rw2) (next := .cnt) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun a _ => by cases a <;> rfl) rfl rfl rfl rfl rfl rfl rfl rfl
      (K (y := y) .vU0 ⟨1, by omega⟩ 0 0) 0).1 ⟨n, w, hy, hw⟩
    rw [xCfg_K, xCfg_K] at e
    refine ⟨T, e, fun t ht => ?_⟩
    obtain ⟨s, ip, hs, -⟩ := hm t ht
    rw [xCfg_K, xCfg_K] at hs
    rw [hs]; simp [K]
  -- the count
  have h2 := count hy (2 * n) le_rfl
  -- the separator
  have h3 : Rch W (K (y := y) .cnt ⟨1 + 2 * n, by omega⟩ (2 * n) 0)
      (K .sw1 ⟨1 + 2 * n, by omega⟩ (2 * n) 0) := by
    refine ⟨1, ?_, fun t ht => ?_⟩
    · rw [step_x .cnt .sw1 _ _ 0 0 (fun _ => by
        simp only [tr, show 1 + 2 * n = 2 * n + 1 by omega, inSym_succ, sym_eq hy]; rfl)]
      rw [moveInputPos_zero]
    · obtain rfl : t = 0 := by omega
      simp [rrun_zero, K]
  -- the rewind
  have h4 : Rch W (K (y := y) .sw1 ⟨1 + 2 * n, by omega⟩ (2 * n) 0)
      (K .jK ⟨1, by omega⟩ (2 * n) 0) := by
    obtain ⟨T, e, hm⟩ := rewind_x prog o (K (y := y) .sw1 ⟨1 + 2 * n, by omega⟩ (2 * n) 0) 0 0
      .sw1 .sw2 .jK (fun _ _ => rfl) (fun a _ => by cases a <;> rfl) rfl rfl
      ⟨1 + 2 * n, by omega⟩
    rw [xCfg_K, xCfg_K] at e
    refine ⟨T, e, fun t ht => ?_⟩
    obtain ⟨s, ip, hs, -⟩ := hm t ht
    rw [xCfg_K, xCfg_K] at hs
    rw [hs]; simp [K]
  -- the comparison
  have h5 : Rch W (K (y := y) .jK ⟨1, by omega⟩ (2 * n) 0)
      (K (if w = Nat.bits (2 * n) then .yes else .no) ⟨1, by omega⟩ (2 * n) 0) := by
    obtain ⟨T, e, hm⟩ := jeqPlain_run (P := prog) (oracle := o) (r := 0) (jK := .jK)
      (jK2 := .jK2) (jC := .jC) (jRB := St.jRB) (jI1 := St.jI1) (jI2 := St.jI2) (yes := .yes)
      (no := .no) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)
      (fun _ _ _ => rfl) (fun _ _ _ => rfl) rfl rfl rfl (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) (K (y := y) .jK ⟨1, by omega⟩ (2 * n) 0) n w hy (2 * n) rfl
    rw [xCfg_K, xCfg_K] at e
    refine ⟨T, e, fun t ht => ?_⟩
    obtain ⟨s, ip, q, hs, -, hq1, hq2⟩ := hm t ht
    rw [xCfg_K, xCfg_K] at hs
    rw [hs]; simp only [K]; exact ⟨hq1, hq2⟩
  exact (((h1.trans h2).trans h3).trans h4).trans h5

/-- The answering step. -/
lemma ret_step (b : Bool) (ip : Fin (y.length + 2)) (v : ℕ) :
    (rrun prog o (K (if b then .yes else .no) ip v 0) 1).state = none ∧
      (rrun prog o (K (if b then .yes else .no) ip v 0) 1).output = [b] ∧
      (rrun prog o (K (if b then .yes else .no) ip v 0) 1).workTapePos 0 = 0 := by
  rw [rrun_one, rstep_noncall prog o _ _ rfl rfl]
  cases b <;> simp [MultiTapeTM.step, K, prog, tr, retAct, Action.apply]

/-- The trivial decider bank (no deciders are called). -/
def nilTM : MultiTapeTM 0 Bool Unit := ⟨(), fun _ _ _ => ⟨0, fun _ => (none, 0), none, none⟩⟩

end Dbl

open Dbl in
/-- **`dblLang` is in `L`**: the counting program decides it with one binary counter.

**Proof sketch.** On a well-formed input `⟨1ⁿ, w⟩` the run is `Dbl.run_valid` followed by the
answering step; on any other input the format check rejects (`valPlain_run`) with the
register untouched. The register head stays in `[-1, |bits |y||]`, so `compile_space` bounds
the space by `|bits |y|| + 2 ≤ 3 logSpace |y|` (there are no deciders). -/
theorem dblLang_mem : dblLang ∈ LOGSPACE := by
  refine ⟨3, compileFinTM prog .vU0 nilTM (fun _ => ()), fun y => ?_⟩
  set W := (Nat.bits y.length).length with hW
  have key : ∃ N, (rrun prog o (Cfg.init .vU0 y) N).state = none ∧
      (rrun prog o (Cfg.init .vU0 y) N).output =
        [MultiTapeTM.indicator (dblLang : Set (List Bool)) y] ∧
      ∀ t ≤ N, -1 ≤ (rrun prog o (Cfg.init .vU0 y) t).workTapePos 0 ∧
        (rrun prog o (Cfg.init .vU0 y) t).workTapePos 0 ≤ W := by
    rw [init_eq]
    by_cases hv : ValidPlain y
    · obtain ⟨n, w, hy, hw⟩ := hv
      have hl := length_eq hy
      obtain ⟨T, e, hm⟩ := run_valid hy hw
      obtain ⟨r1, r2, r3⟩ := ret_step (y := y) (decide (w = Nat.bits (2 * n))) ⟨1, by omega⟩
        (2 * n)
      have hW' : (Nat.bits (2 * n)).length ≤ W := length_bits_mono (by omega)
      have hind : MultiTapeTM.indicator (dblLang : Set (List Bool)) y =
          decide (w = Nat.bits (2 * n)) := by
        rw [indicator_eq_decide]
        refine decide_eq_decide.mpr ⟨fun ⟨n', h⟩ => ?_, fun h => ⟨n, by rw [hy, h]⟩⟩
        have := pairEncode_injective (a₁ := (List.replicate n true, w))
          (a₂ := (List.replicate n' true, Nat.bits (2 * n'))) (hy.symm.trans h)
        simp only [Prod.mk.injEq] at this
        obtain ⟨h1, h2⟩ := this
        have : n = n' := by simpa using congrArg List.length h1
        subst this; exact h2
      simp only [decide_eq_true_eq] at r1 r2 r3
      refine ⟨T + 1, ?_, ?_, fun t ht => ?_⟩
      · rw [rrun_add, e]; convert r1 using 4
      · rw [rrun_add, e, hind]; convert r2 using 4
      · rcases Nat.lt_or_ge t T with h | h
        · have := hm t h; omega
        · rcases Nat.lt_or_ge t (T + 1) with h' | h'
          · obtain rfl : t = T := by omega
            rw [e]; simp [K]
          · obtain rfl : t = T + 1 := by omega
            rw [rrun_add, e]
            have : (rrun prog o (K (y := y) (if w = Nat.bits (2 * n) then .yes else .no)
                ⟨1, by omega⟩ (2 * n) 0) 1).workTapePos 0 = 0 := by
              convert r3 using 4
            rw [this]; omega
    · obtain ⟨T, e1, e2, e3, hm⟩ := (valPlain_run (P := prog) (oracle := o) (r := 0)
        (vU0 := .vU0) (vU1 := .vU1) (vS := .vS) (vW0 := .vW0) (vWF := .vWF) (vWT := .vWT)
        (rw₁ := .rw1) (rw₂ := .rw2) (next := .cnt) (fun _ _ => rfl) (fun _ _ => rfl)
        (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
        (fun a _ => by cases a <;> rfl) rfl rfl rfl rfl rfl rfl rfl rfl
        (K (y := y) .vU0 ⟨1, by omega⟩ 0 0) 0).2 hv
      rw [xCfg_K] at e1 e2 e3 hm
      have hn : MultiTapeTM.indicator (dblLang : Set (List Bool)) y = false := by
        rw [indicator_eq_decide]
        simp only [decide_eq_false_iff_not]
        rintro ⟨n, rfl⟩
        exact hv ⟨n, _, rfl, canon_bits _⟩
      refine ⟨T, e1, by rw [e2, hn]; rfl, fun t ht => ?_⟩
      rcases Nat.lt_or_ge t T with h | h
      · obtain ⟨s, ip, hs, -⟩ := hm t h
        rw [xCfg_K] at hs
        rw [hs]; simp [K]
      · obtain rfl : t = T := by omega
        rw [e3]; simp [K]
  obtain ⟨N, h1, h2, hbox⟩ := key
  obtain ⟨T, hT, hsp⟩ := compile_space prog .vU0 nilTM (fun _ => ()) o (fun _ => -1)
    (fun _ => (W : ℤ)) 0 N _ h1 h2
    (fun t ht r => by rw [Fin.fin_one_eq_zero r]; exact hbox t ht)
    (fun t _ l cs _ hcs => by simp [prog] at hcs)
  refine ⟨T, hT, hsp.trans ?_⟩
  simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, zero_mul,
    add_zero]
  have e1 := length_bits_le_log y.length
  have : ((W : ℤ) - -1 + 1).toNat = W + 2 := by omega
  rw [this]
  simp only [logSpace]
  omega

end Complexity.LogProg

```


## ===== TCSlib/Complexity/SpaceComplexity/UnaryLogspace.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Tactic.FinCases
import TCSlib.Complexity.SpaceComplexity.Machines.DblLang

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Functions of the unary length computable in logarithmic space

A uniformity function only matters on the inputs `1ⁿ` [AB09, Def 6.14]. For a sequence of
words `g : ℕ → List Bool` (the value on `1ⁿ`) this file defines the bit and length
languages `{⟨1ⁿ, bits i⟩ | g(n)ᵢ = 1}`, `{⟨1ⁿ, bits i⟩ | i < |g(n)|}` and calls `g`
*unary-logspace* when both are in `L`; with a polynomial length bound this makes the
extension of `g` by `[]` off unary inputs implicitly logspace computable [AB09, Def 4.16].
The first example is `g(n) = 1ⁿ`, decided by an abstract register machine that counts
`k = 0, 1, …` and asks the base decider `dblLang` whether `2k = 2n`.

These pieces (`ltLang`, `UnaryLogspace`, `unaryExt`, and the counter-program simulation of
`TCSlib.Complexity.SpaceComplexity.CounterProgSim`) are generic logspace material; their
first client is [AB09, Thm 6.15] (`TCSlib.Complexity.CircuitComplexity.LogspaceTableau`).

## Main definitions

* `Complexity.uBit`, `Complexity.uLen` — the bit and length languages of `g`.
* `Complexity.UnaryLogspace g` — both are in `L`.
* `Complexity.unaryExt g` — `g |x|` on unary `x`, `[]` elsewhere.

## Main results

* `Complexity.UnaryLogspace.implicitlyLogspaceComputable` — with a polynomial length bound,
  `unaryExt g` is implicitly logspace computable.
* `Complexity.unaryLogspace_replicate` — `n ↦ 1ⁿ` is unary-logspace.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1; §4.3, Definition 4.16; §6.2.1, Definition 6.14.)
-/

namespace Complexity

open Turing LogProg

/-! ## Unary index languages -/

/-- The bit language of `g`: `⟨1ⁿ, bits i⟩` with `g(n)ᵢ = 1`. -/
def uBit (g : ℕ → List Bool) : Language Bool :=
  {y | ∃ n i, y = pairEncode (List.replicate n true) (Nat.bits i) ∧ (g n).getD i false = true}

/-- The length language of `g`: `⟨1ⁿ, bits i⟩` with `i < |g(n)|`. -/
def uLen (g : ℕ → List Bool) : Language Bool :=
  {y | ∃ n i, y = pairEncode (List.replicate n true) (Nat.bits i) ∧ i < (g n).length}

/-- `g` is *unary-logspace*: its bit and length languages are in `L`. -/
def UnaryLogspace (g : ℕ → List Bool) : Prop :=
  uBit g ∈ LOGSPACE ∧ uLen g ∈ LOGSPACE

/-- Membership of `⟨1ⁿ, bits i⟩` in a language of the form `{⟨1ⁿ, bits i⟩ | p n i}`. -/
lemma mem_unaryIdx (p : ℕ → ℕ → Prop) (n i : ℕ) :
    pairEncode (List.replicate n true) (Nat.bits i) ∈
        {y : List Bool | ∃ n i, y = pairEncode (List.replicate n true) (Nat.bits i) ∧ p n i} ↔
      p n i := by
  constructor
  · rintro ⟨n', i', h, hp⟩
    obtain ⟨rfl, hb⟩ := pairEncode_replicate_inj h
    rwa [bits_injective hb]
  · exact fun h => ⟨n, i, rfl, h⟩

/-- Membership in the bit language. -/
lemma mem_uBit (g : ℕ → List Bool) (n i : ℕ) :
    pairEncode (List.replicate n true) (Nat.bits i) ∈ uBit g ↔ (g n).getD i false = true :=
  mem_unaryIdx (fun n i => (g n).getD i false = true) n i

/-- Membership in the length language. -/
lemma mem_uLen (g : ℕ → List Bool) (n i : ℕ) :
    pairEncode (List.replicate n true) (Nat.bits i) ∈ uLen g ↔ i < (g n).length :=
  mem_unaryIdx (fun n i => i < (g n).length) n i

/-- Members of a unary index language are well-formed plain inputs. -/
lemma validPlain_of_mem_unaryIdx {p : ℕ → ℕ → Prop} {y : List Bool}
    (h : y ∈ {y : List Bool | ∃ n i, y = pairEncode (List.replicate n true) (Nat.bits i) ∧
      p n i}) : ValidPlain y := by
  obtain ⟨n, i, rfl, -⟩ := h
  exact ⟨n, _, rfl, canon_bits i⟩

/-! ## From unary-logspace to implicitly logspace computable -/

open Classical in
/-- The extension of `g` to all inputs: `g |x|` on `x = 1^{|x|}`, `[]` elsewhere. -/
noncomputable def unaryExt (g : ℕ → List Bool) (x : List Bool) : List Bool :=
  if x = List.replicate x.length true then g x.length else []

/-- On `1ⁿ` the extension is `g n`. -/
@[simp] lemma unaryExt_replicate (g : ℕ → List Bool) (n : ℕ) :
    unaryExt g (List.replicate n true) = g n := by
  simp [unaryExt]

/-- The index languages of the extension are those of `g`. -/
lemma indexLang_unaryExt (p : List Bool → ℕ → Prop)
    (hp : ∀ x i, p x i ↔ (x = List.replicate x.length true ∧ p x i))
    (q : ℕ → ℕ → Prop) (hq : ∀ n i, p (List.replicate n true) i ↔ q n i) :
    indexLang p =
      {y : List Bool | ∃ n i, y = pairEncode (List.replicate n true) (Nat.bits i) ∧ q n i} := by
  ext y
  constructor
  · rintro ⟨x, i, rfl, h⟩
    obtain ⟨hx, h⟩ := (hp x i).mp h
    refine ⟨x.length, i, by rw [← hx], ?_⟩
    rw [← hq, ← hx]; exact h
  · rintro ⟨n, i, rfl, h⟩
    exact ⟨_, i, rfl, (hq n i).mpr h⟩

/-- **Unary-logspace sequences of polynomial length give implicitly logspace computable
functions** [AB09, Def 4.16]: `unaryExt g`.

**Proof sketch.** Off unary inputs the extension is empty, so its bit and length languages
are exactly `uBit g` and `uLen g` (`indexLang_unaryExt`). -/
theorem UnaryLogspace.implicitlyLogspaceComputable {g : ℕ → List Bool} (h : UnaryLogspace g)
    (hlen : ∃ C c : ℕ, ∀ n, (g n).length ≤ C * (n + 1) ^ c) :
    ImplicitlyLogspaceComputable (unaryExt g) := by
  obtain ⟨C, c, hC⟩ := hlen
  refine ⟨⟨C, c, fun x => ?_⟩, ?_, ?_⟩
  · unfold unaryExt; split_ifs
    · exact hC _
    · simp
  · rw [indexLang_unaryExt _ (fun x i => by
        unfold unaryExt; split_ifs with hx
        · exact ⟨fun h => ⟨hx, h⟩, And.right⟩
        · simp [hx])
      (fun n i => (g n).getD i false = true) (fun n i => by simp)]
    exact h.1
  · rw [indexLang_unaryExt _ (fun x i => by
        unfold unaryExt; split_ifs with hx
        · exact ⟨fun h => ⟨hx, h⟩, And.right⟩
        · simp [hx])
      (fun n i => i < (g n).length) (fun n i => by simp)]
    exact h.2

/-! ## The identity `n ↦ 1ⁿ` -/

namespace LogProg

/-- A `unaryFst` call with one argument `r` on `⟨1ⁿ, w⟩` asks about `⟨1ⁿ, bits (v r)⟩`. -/
lemma astep_call₁ {m d : ℕ} {Λ : Type} (A : ARM m d Λ) (o : Fin d → List Bool → Bool)
    {l l₁ l₀ : Λ} {j : Fin d} {r : Fin m} (hl : A l = .call j .unaryFst [r] l₁ l₀) (n : ℕ)
    (w : List Bool) (v : Fin m → ℕ) :
    astep A o (pairEncode (List.replicate n true) w) (some l, v, none) =
      (some (if o j (pairEncode (List.replicate n true) (Nat.bits (v r))) then l₁ else l₀),
        v, none) := by
  simp only [astep, hl]
  rw [vword_unary₁]

end LogProg

/-- The inputs `⟨1ⁿ, bits i⟩` with `i < n`. -/
def ltLang : Language Bool :=
  {y | ∃ n i, y = pairEncode (List.replicate n true) (Nat.bits i) ∧ i < n}

namespace LtM

/-- The labels of the comparison machine. -/
inductive Lb where
  | start | test | cmp | i1 | i2 | i3 | yes | no
  deriving DecidableEq, Fintype

/-- **The comparison machine**: registers `k` (`0`) and `g = 2k` (`1`); at `test` ask
`dblLang` whether `g = 2n` (then answer `0`), at `cmp` whether `k = i` (then answer `1`),
else increment `k` once and `g` twice. -/
def A : ARM 2 1 Lb
  | .start => .valP 0 .test
  | .test => .call 0 .unaryFst [1] .no .cmp
  | .cmp => .jeqIn 0 .yes .i1
  | .i1 => .inc 0 .i2
  | .i2 => .inc 1 .i3
  | .i3 => .inc 1 .test
  | .yes => .ret true
  | .no => .ret false

/-- Two register values. -/
def vv (a b : ℕ) : Fin 2 → ℕ := fun j => if j = 0 then a else b

/-- Reading register `k`. -/
@[simp] lemma vv_0 (a b : ℕ) : vv a b 0 = a := rfl
/-- Reading register `g`. -/
@[simp] lemma vv_1 (a b : ℕ) : vv a b 1 = b := rfl

/-- Writing register `k`. -/
lemma upd_0 (a b c : ℕ) : Function.update (vv a b) 0 c = vv c b := by
  funext j; fin_cases j <;> simp [vv]

/-- Writing register `g`. -/
lemma upd_1 (a b c : ℕ) : Function.update (vv a b) 1 c = vv a c := by
  funext j; fin_cases j <;> simp [vv]

/-- The oracle: membership in `dblLang`. -/
noncomputable def orc : Fin 1 → List Bool → Bool :=
  fun _ V => MultiTapeTM.indicator (dblLang : Set (List Bool)) V

/-- The base decider answers whether `v = 2n`. -/
lemma orc_eq (n v : ℕ) : orc 0 (pairEncode (List.replicate n true) (Nat.bits v)) =
    decide (v = 2 * n) := by
  rw [orc, indicator_eq_decide]
  refine decide_eq_decide.mpr ⟨fun ⟨n', h⟩ => ?_, fun h => ⟨n, by rw [h]⟩⟩
  obtain ⟨rfl, hb⟩ := pairEncode_replicate_inj h
  exact bits_injective hb

/-- The invariant: syntactic preconditions and registers at most `2 (|y| + 1)`. -/
def G (y : List Bool) (a : AConf 2 Lb) : Prop :=
  PreS A y a ∧ ∀ r, a.2.1 r ≤ 2 * (y.length + 1) ^ 1

/-- **The loop**: from `test` with `k ≤ n`, `k ≤ i`, `g = 2k`, the machine answers `i < n`.

**Proof sketch.** Induction on `n - k`: if `k = n` the base decider says `2k = 2n` and the
machine answers `0` (correct, as `i ≥ k = n`); otherwise if `k = i` it answers `1` (`i < n`);
otherwise it moves to `k + 1`. -/
lemma loop (n i : ℕ) : ∀ d k, k + d = n → k ≤ i →
    AHalt A orc (pairEncode (List.replicate n true) (Nat.bits i)) (G (pairEncode
      (List.replicate n true) (Nat.bits i))) (some .test, vv k (2 * k), none) (decide (i < n)) := by
  set y := pairEncode (List.replicate n true) (Nat.bits i) with hy
  have hl : y.length = 2 * n + 2 + (Nat.bits i).length := by
    simp [hy, pairEncode_eq_dbl, dbl_replicate]; omega
  have hval : ValidPlain y := ⟨n, _, rfl, canon_bits i⟩
  have hG : ∀ (l : Lb) (a b : ℕ), a ≤ n + 1 → b ≤ 2 * n + 2 → G y (some l, vv a b, none) := by
    intro l a b ha hb
    refine ⟨?_, fun r => ?_⟩
    · cases l <;> simp [PreS, A, hval]
    · fin_cases r <;> simp <;> omega
  intro d
  induction d with
  | zero =>
    intro k hk hki
    obtain rfl : k = n := by omega
    refine AHalt.step (hG _ _ _ (by omega) (by omega)) ?_
    rw [astep_call₁ A orc (show A .test = _ from rfl), orc_eq]
    have hf : decide (i < k) = false := by simp; omega
    simp only [vv_1, decide_true, ↓reduceIte, hf]
    exact AHalt.ret rfl (hG _ _ _ (by omega) (by omega))
  | succ d ih =>
    intro k hk hki
    refine AHalt.step (hG _ _ _ (by omega) (by omega)) ?_
    rw [astep_call₁ A orc (show A .test = _ from rfl), orc_eq]
    simp only [vv_1, show 2 * k ≠ 2 * n by omega, decide_false, Bool.false_eq_true, ↓reduceIte]
    refine AHalt.step (hG _ _ _ (by omega) (by omega)) ?_
    by_cases hki' : k = i
    · subst hki'
      have : astep A orc y (some .cmp, vv k (2 * k), none) = (some .yes, vv k (2 * k), none) := by
        simp [astep, A, hy, plainWord_pairEncode]
      rw [this]
      have hlt : decide (k < n) = true := by simp; omega
      rw [hlt]
      exact AHalt.ret rfl (hG _ _ _ (by omega) (by omega))
    · have : astep A orc y (some .cmp, vv k (2 * k), none) = (some .i1, vv k (2 * k), none) := by
        simp [astep, A, hy, plainWord_pairEncode, bits_injective.eq_iff, hki']
      rw [this]
      refine AHalt.step (hG _ _ _ (by omega) (by omega)) ?_
      simp only [astep, A, vv_0, upd_0]
      refine AHalt.step (hG _ _ _ (by omega) (by omega)) ?_
      simp only [astep, A, vv_1, upd_1]
      refine AHalt.step (hG _ _ _ (by omega) (by omega)) ?_
      simp only [astep, A, vv_1, upd_1]
      have := ih (k + 1) (by omega) (by omega)
      rwa [show 2 * k + 1 + 1 = 2 * (k + 1) by ring]

end LtM

open LtM in
/-- **`ltLang` is in `L`**: the comparison machine decides it with the base decider
`dblLang`.

**Proof sketch.** `arm_decides_poly`: on a malformed input the format check rejects; on
`⟨1ⁿ, bits i⟩` the loop (`LtM.loop`) answers `i < n` with registers at most `2n + 2`. -/
theorem ltLang_mem : ltLang ∈ LOGSPACE := by
  refine arm_decides_poly A .start (fun _ => dblLang) (fun _ => dblLang_mem) 2 1 fun y => ?_
  by_cases hv : ValidPlain y
  · obtain ⟨n, w, rfl, hw⟩ := hv
    rw [canon_eq_bits w hw]
    set i := bitsVal w
    have hind : MultiTapeTM.indicator (ltLang : Set (List Bool))
        (pairEncode (List.replicate n true) (Nat.bits i)) = decide (i < n) := by
      rw [indicator_eq_decide]; exact decide_eq_decide.mpr (mem_unaryIdx _ n i)
    rw [hind]
    have hval : ValidPlain (pairEncode (List.replicate n true) (Nat.bits i)) :=
      ⟨n, _, rfl, canon_bits i⟩
    change AHalt A orc _ (G _) _ _
    rw [show (fun _ => 0 : Fin 2 → ℕ) = vv 0 (2 * 0) from by funext j; fin_cases j <;> rfl]
    refine AHalt.step ⟨by simp [PreS, A], fun r => by fin_cases r <;> simp⟩ ?_
    have : astep A orc (pairEncode (List.replicate n true) (Nat.bits i))
        (some .start, vv 0 (2 * 0), none) = (some .test, vv 0 (2 * 0), none) := by
      simp [astep, A, hval]
    rw [this]
    exact loop n i n 0 (by omega) (Nat.zero_le _)
  · have hn : MultiTapeTM.indicator (ltLang : Set (List Bool)) y = false := by
      rw [indicator_eq_decide]
      simp only [decide_eq_false_iff_not]
      exact fun h => hv (validPlain_of_mem_unaryIdx h)
    rw [hn]
    refine ⟨1, ?_, ?_, fun t ht => ?_⟩
    · simp [arun, astep, A, hv]
    · simp [arun, astep, A, hv]
    · obtain rfl : t = 0 := by omega
      exact ⟨by simp [arun, PreS, A], fun r => by simp [arun]⟩

/-- **`n ↦ 1ⁿ` is unary-logspace**: both its languages are `ltLang`. -/
theorem unaryLogspace_replicate : UnaryLogspace fun n => List.replicate n true := by
  have e1 : uBit (fun n => List.replicate n true) = ltLang := by
    ext y; simp only [uBit, ltLang]
    refine exists_congr fun n => exists_congr fun i => and_congr_right fun _ => ?_
    by_cases h : i < n <;> simp [List.getD_eq_getElem?_getD, h]
  have e2 : uLen (fun n => List.replicate n true) = ltLang := by
    ext y; simp [uLen, ltLang]
  exact ⟨e1 ▸ ltLang_mem, e2 ▸ ltLang_mem⟩

end Complexity

```


## ===== TCSlib/Complexity/SpaceComplexity/CounterProgSim.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.TuringMachine.CounterProgRun
import TCSlib.Complexity.SpaceComplexity.UnaryLogspace

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Simulating counter programs in logarithmic space

A counter program (`Complexity.CounterProg`, the model of the emitters of [AB09, Remark 6.7])
that runs for polynomially many steps keeps every register polynomially bounded, so its
registers fit in `O(log n)` bits. This file builds the abstract register machine
`Complexity.CPSim.A P l₀ lm` that, on `⟨1ⁿ, bits p⟩`, runs `P` with its registers, its input
position and the *number* of printed bits held in binary, reading the input of `P` through
two deciders (the length and bit languages of the input) and stopping at the `p`-th printed
bit [AB09, §4.3: composing implicitly logspace computable functions, by recomputing bits on
demand].

This file defines the machine and proves the simulation of one counter step
(`Complexity.CPSim.sim_step`); the whole run and the resulting closure property are in
`TCSlib.Complexity.SpaceComplexity.CounterProgSimRun`.

## Main definitions

* `Complexity.CPSim.A` — the simulating machine; `lm` selects the length language.
* `Complexity.CPSim.ev` — the register file of a counter state.

## Main results

* `Complexity.CPSim.sim_step` — one counter step is simulated, or the machine answers.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.3, Lemma 4.17; §6.1.1, Remark 6.7.)
-/

namespace Complexity

namespace CPSim

open Turing LogProg

variable {R : ℕ} {Λ : Type}

/-! ## The register file -/

/-- The register of counter register `r`. -/
def rg (r : Fin R) : Fin (R + 3) := Fin.castAdd 3 r
/-- The register of the input position. -/
def rP (R : ℕ) : Fin (R + 3) := ⟨R, by omega⟩
/-- The register of the number of printed bits. -/
def rO (R : ℕ) : Fin (R + 3) := ⟨R + 1, by omega⟩
/-- The scratch register of the print loop. -/
def rT (R : ℕ) : Fin (R + 3) := ⟨R + 2, by omega⟩

/-- The register file: counter registers `ρ`, input position `p`, output count `oc`, scratch
`tm`. -/
def ev (ρ : Fin R → ℕ) (p oc tm : ℕ) : Fin (R + 3) → ℕ := fun i =>
  if h : i.val < R then ρ ⟨i.val, h⟩ else if i.val = R then p else if i.val = R + 1 then oc
  else tm

/-- Reading a counter register. -/
@[simp] lemma ev_rg (ρ : Fin R → ℕ) (p oc tm : ℕ) (r : Fin R) : ev ρ p oc tm (rg r) = ρ r := by
  simp [ev, rg]
/-- Reading the input position. -/
@[simp] lemma ev_rP (ρ : Fin R → ℕ) (p oc tm : ℕ) : ev ρ p oc tm (rP R) = p := by simp [ev, rP]
/-- Reading the output count. -/
@[simp] lemma ev_rO (ρ : Fin R → ℕ) (p oc tm : ℕ) : ev ρ p oc tm (rO R) = oc := by
  simp [ev, rO]
/-- Reading the scratch register. -/
@[simp] lemma ev_rT (ρ : Fin R → ℕ) (p oc tm : ℕ) : ev ρ p oc tm (rT R) = tm := by
  simp [ev, rT]

/-- Writing a counter register. -/
lemma upd_rg (ρ : Fin R → ℕ) (p oc tm : ℕ) (r : Fin R) (v : ℕ) :
    Function.update (ev ρ p oc tm) (rg r) v = ev (Function.update ρ r v) p oc tm := by
  funext i
  obtain ⟨i, hi⟩ := i
  obtain ⟨r, hr⟩ := r
  simp only [Function.update_apply, ev, rg, Fin.ext_iff, Fin.coe_castAdd]
  split_ifs <;> simp_all

/-- Writing the input position. -/
lemma upd_rP (ρ : Fin R → ℕ) (p oc tm v : ℕ) :
    Function.update (ev ρ p oc tm) (rP R) v = ev ρ v oc tm := by
  funext i; obtain ⟨i, hi⟩ := i
  simp only [Function.update_apply, ev, rP, Fin.ext_iff]
  split_ifs <;> omega

/-- Writing the output count. -/
lemma upd_rO (ρ : Fin R → ℕ) (p oc tm v : ℕ) :
    Function.update (ev ρ p oc tm) (rO R) v = ev ρ p v tm := by
  funext i; obtain ⟨i, hi⟩ := i
  simp only [Function.update_apply, ev, rO, Fin.ext_iff]
  split_ifs <;> omega

/-- Writing the scratch register. -/
lemma upd_rT (ρ : Fin R → ℕ) (p oc tm v : ℕ) :
    Function.update (ev ρ p oc tm) (rT R) v = ev ρ p oc v := by
  funext i; obtain ⟨i, hi⟩ := i
  simp only [Function.update_apply, ev, rT, Fin.ext_iff]
  split_ifs <;> omega

/-- The scratch register is not a counter register. -/
lemma rT_ne_rg (r : Fin R) : rT R ≠ rg r := by
  intro h; have := congrArg Fin.val h; simp [rT, rg] at this; omega

/-! ## The machine -/

/-- The labels: simulating label `l`, and the auxiliary labels of the output count, the print
loop and the input read. -/
inductive Lb (Λ : Type) where
  | start
  | sim (l : Λ)
  | bump (l : Λ)
  | prL (l : Λ)
  | prC (l : Λ)
  | prB (l : Λ)
  | prT (l : Λ)
  | rdB (l : Λ)
  | rdT (l : Λ)
  | rdF (l : Λ)
  | ans (b : Bool)
  deriving DecidableEq

/-- Finitely many labels (via an explicit equivalence with `(Unit ⊕ Fin 9 × Λ) ⊕ Bool`). -/
instance [Fintype Λ] : Fintype (Lb Λ) := by
  classical
  let e : Lb Λ ≃ (Unit ⊕ (Fin 9 × Λ)) ⊕ Bool :=
    { toFun := fun q => match q with
        | .start => .inl (.inl ())
        | .sim l => .inl (.inr (0, l))
        | .bump l => .inl (.inr (1, l))
        | .prL l => .inl (.inr (2, l))
        | .prC l => .inl (.inr (3, l))
        | .prB l => .inl (.inr (4, l))
        | .prT l => .inl (.inr (5, l))
        | .rdB l => .inl (.inr (6, l))
        | .rdT l => .inl (.inr (7, l))
        | .rdF l => .inl (.inr (8, l))
        | .ans b => .inr b
      invFun := fun z => match z with
        | .inl (.inl ()) => .start
        | .inl (.inr (i, l)) =>
          match i with
          | 0 => .sim l | 1 => .bump l | 2 => .prL l | 3 => .prC l | 4 => .prB l
          | 5 => .prT l | 6 => .rdB l | 7 => .rdT l | 8 => .rdF l
        | .inr b => .ans b
      left_inv := fun q => by cases q <;> rfl
      right_inv := fun z => by
        rcases z with (⟨⟩ | ⟨i, l⟩) | b
        · rfl
        · fin_cases i <;> rfl
        · rfl }
  exact Fintype.ofEquiv _ e.symm

variable (P : Λ → CounterProg.Instr R Λ) (l₀ : Λ) (lm : Bool)

/-- **The simulating machine.** At `sim l` it executes `P l`: register instructions act on the
corresponding registers; printing a bit compares the output count with the index `p` on the
input (answer if equal, else count); printing a register loops over the scratch register;
reading asks the length decider (`0`) and the bit decider (`1`) about the input position;
`halt` answers `0` (the index is beyond the output). In length mode (`lm`) every printed bit
answers `1`. -/
def A : ARM (R + 3) 2 (Lb Λ) := fun q =>
  match q with
  | .start => .valP (rP R) (.sim l₀)
  | .sim l =>
    match P l with
    | .halt => .ret false
    | .goto l' => .jz (rP R) (.sim l') (.sim l')
    | .out b l' => .jeqIn (rO R) (.ans (lm || b)) (.bump l')
    | .inc r l' => .inc (rg r) (.sim l')
    | .dec r l' => .dec (rg r) (.sim l')
    | .jz r l0 l1 => .jz (rg r) (.sim l0) (.sim l1)
    | .pr _ _ => .clr (rT R) (.prL l)
    | .rd le _ _ => .call 0 .unaryFst [rP R] (.rdB l) (.sim le)
  | .bump l' => .inc (rO R) (.sim l')
  | .prL l =>
    match P l with
    | .pr r l' => .jeq (rT R) (rg r) (.sim l') (.prC l)
    | _ => .ret false
  | .prC l => .jeqIn (rO R) (.ans true) (.prB l)
  | .prB l => .inc (rO R) (.prT l)
  | .prT l => .inc (rT R) (.prL l)
  | .rdB l => .call 1 .unaryFst [rP R] (.rdT l) (.rdF l)
  | .rdT l =>
    match P l with
    | .rd _ _ lt => .inc (rP R) (.sim lt)
    | _ => .ret false
  | .rdF l =>
    match P l with
    | .rd _ lf _ => .inc (rP R) (.sim lf)
    | _ => .ret false
  | .ans b => .ret b

/-- On a well-formed input every configuration meets the syntactic preconditions. -/
lemma preS_A {y : List Bool} (hv : ValidPlain y) (a : AConf (R + 3) (Lb Λ)) :
    PreS (A P l₀ lm) y a := by
  obtain ⟨_ | q, v, res⟩ := a
  · trivial
  · cases q with
    | sim l => cases h : P l <;> simp [PreS, A, h, hv]
    | prL l => cases h : P l <;> simp [PreS, A, h, rT_ne_rg]
    | rdT l => cases h : P l <;> simp [PreS, A, h]
    | rdF l => cases h : P l <;> simp [PreS, A, h]
    | _ => simp [PreS, A, hv]

/-! ## One step -/

/-- The answer for index `p` on output `O`: the bit `O_p`, or in length mode `p < |O|`. -/
def ans (lm : Bool) (O : List Bool) (p : ℕ) : Bool :=
  if lm then decide (p < O.length) else O.getD p false

/-- A running abstract configuration. -/
abbrev cf (q : Lb Λ) (v : Fin (R + 3) → ℕ) : AConf (R + 3) (Lb Λ) := (some q, v, none)

section Step

variable {n p : ℕ} {u : List Bool} {o : Fin 2 → List Bool → Bool}
  (ho0 : ∀ h, o 0 (pairEncode (List.replicate n true) (Nat.bits h)) = decide (h < u.length))
  (ho1 : ∀ h, o 1 (pairEncode (List.replicate n true) (Nat.bits h)) = u.getD h false)
  (B : ℕ)

/-- The invariant of the simulation: preconditions, and registers at most `B`. -/
def G (y : List Bool) (a : AConf (R + 3) (Lb Λ)) : Prop :=
  PreS (A P l₀ lm) y a ∧ ∀ r, a.2.1 r ≤ B

variable {P l₀ lm B}

/-- Configurations with all values within `B` satisfy the invariant. -/
lemma G_ev (q : Lb Λ) (ρ : Fin R → ℕ) (ps oc tm : ℕ) (hρ : ∀ r, ρ r ≤ B) (hps : ps ≤ B)
    (hoc : oc ≤ B) (htm : tm ≤ B) :
    G P l₀ lm B (pairEncode (List.replicate n true) (Nat.bits p)) (cf q (ev ρ ps oc tm)) := by
  refine ⟨preS_A P l₀ lm ⟨n, _, rfl, canon_bits p⟩ _, fun i => ?_⟩
  obtain ⟨i, hi⟩ := i
  simp only [ev]
  split_ifs
  · exact hρ _
  all_goals assumption

/-- The output-count comparison: `bits oc = bits p` iff `oc = p`. -/
lemma jeqIn_eq (oc : ℕ) :
    (Nat.bits oc = plainWord (pairEncode (List.replicate n true) (Nat.bits p))) ↔ oc = p := by
  rw [plainWord_pairEncode, bits_injective.eq_iff]

/-- **The print loop**, when the whole value fits below the index: from `prL` with scratch
`j` and count `o₀ + j` the machine reaches the next label with count `o₀ + V`.

**Proof sketch.** Induction on the remaining count `d`: each round goes through `prL` (scratch
`≠` value), `prC` (count `≠ p`), `prB` (count `+1`) and `prT` (scratch `+1`); at `d = 0` the
test at `prL` exits to `sim l'`. -/
lemma pr_reach {l l' : Λ} {r : Fin R} (hP : P l = .pr r l') (ρ : Fin R → ℕ) (ps o₀ : ℕ)
    (hρ : ∀ r, ρ r ≤ B) (hps : ps ≤ B) (hle : o₀ + ρ r ≤ p) (hB : o₀ + ρ r ≤ B) :
    ∀ d j, j + d = ρ r →
      AReach (A P l₀ lm) o (pairEncode (List.replicate n true) (Nat.bits p))
        (G P l₀ lm B (pairEncode (List.replicate n true) (Nat.bits p)))
        (cf (.prL l) (ev ρ ps (o₀ + j) j)) (cf (.sim l') (ev ρ ps (o₀ + ρ r) (ρ r))) := by
  intro d
  induction d with
  | zero =>
    intro j hj
    simp only [Nat.add_zero] at hj; subst hj
    refine AReach.step (G_ev _ _ _ _ _ hρ hps (by omega) (by omega)) ?_
    have : astep (A P l₀ lm) o (pairEncode (List.replicate n true) (Nat.bits p))
        (cf (.prL l) (ev ρ ps (o₀ + ρ r) (ρ r))) = cf (.sim l') (ev ρ ps (o₀ + ρ r) (ρ r)) := by
      simp [astep, A, hP]
    rw [this]; exact AReach.refl _
  | succ d ih =>
    intro j hj
    have hG := fun q (oc tm : ℕ) (h1 : oc ≤ B) (h2 : tm ≤ B) => G_ev (n := n) (p := p) (P := P)
      (l₀ := l₀) (lm := lm) q ρ ps oc tm hρ hps h1 h2
    refine AReach.step (hG _ _ _ (by omega) (by omega)) ?_
    have e1 : astep (A P l₀ lm) o (pairEncode (List.replicate n true) (Nat.bits p))
        (cf (.prL l) (ev ρ ps (o₀ + j) j)) = cf (.prC l) (ev ρ ps (o₀ + j) j) := by
      simp [astep, A, hP, show j ≠ ρ r by omega]
    rw [e1]
    refine AReach.step (hG _ _ _ (by omega) (by omega)) ?_
    have e2 : astep (A P l₀ lm) o (pairEncode (List.replicate n true) (Nat.bits p))
        (cf (.prC l) (ev ρ ps (o₀ + j) j)) = cf (.prB l) (ev ρ ps (o₀ + j) j) := by
      simp only [astep, A, ev_rO, jeqIn_eq, show o₀ + j ≠ p by omega, ↓reduceIte]
    rw [e2]
    refine AReach.step (hG _ _ _ (by omega) (by omega)) ?_
    simp only [astep, A, ev_rO, upd_rO]
    refine AReach.step (hG _ _ _ (by omega) (by omega)) ?_
    simp only [astep, A, ev_rT, upd_rT]
    have := ih (j + 1) (by omega)
    rwa [show o₀ + j + 1 = o₀ + (j + 1) by ring]

/-- **The print loop**, when the index falls inside the printed block: the machine answers
`1` when the count reaches the index.

**Proof sketch.** Induction on the distance `d` from the count to `p`: each round goes through
`prL`, `prC`, `prB`, `prT`; at `d = 0` the comparison at `prC` succeeds and the machine
answers `1`. -/
lemma pr_halt {l l' : Λ} {r : Fin R} (hP : P l = .pr r l') (ρ : Fin R → ℕ) (ps o₀ : ℕ)
    (hρ : ∀ r, ρ r ≤ B) (hps : ps ≤ B) (hlt : p < o₀ + ρ r) (hB : o₀ + ρ r ≤ B) :
    ∀ d j, o₀ + j + d = p →
      AHalt (A P l₀ lm) o (pairEncode (List.replicate n true) (Nat.bits p))
        (G P l₀ lm B (pairEncode (List.replicate n true) (Nat.bits p)))
        (cf (.prL l) (ev ρ ps (o₀ + j) j)) true := by
  have hG := fun q (oc tm : ℕ) (h1 : oc ≤ B) (h2 : tm ≤ B) => G_ev (n := n) (p := p) (P := P)
    (l₀ := l₀) (lm := lm) q ρ ps oc tm hρ hps h1 h2
  intro d
  induction d with
  | zero =>
    intro j hj
    refine AHalt.step (hG _ _ _ (by omega) (by omega)) ?_
    have e1 : astep (A P l₀ lm) o (pairEncode (List.replicate n true) (Nat.bits p))
        (cf (.prL l) (ev ρ ps (o₀ + j) j)) = cf (.prC l) (ev ρ ps (o₀ + j) j) := by
      simp [astep, A, hP, show j ≠ ρ r by omega]
    rw [e1]
    refine AHalt.step (hG _ _ _ (by omega) (by omega)) ?_
    have e2 : astep (A P l₀ lm) o (pairEncode (List.replicate n true) (Nat.bits p))
        (cf (.prC l) (ev ρ ps (o₀ + j) j)) = cf (.ans true) (ev ρ ps (o₀ + j) j) := by
      simp only [astep, A, ev_rO, jeqIn_eq, show o₀ + j = p by omega, ↓reduceIte]
    rw [e2]
    exact AHalt.ret rfl (hG _ _ _ (by omega) (by omega))
  | succ d ih =>
    intro j hj
    refine AHalt.step (hG _ _ _ (by omega) (by omega)) ?_
    have e1 : astep (A P l₀ lm) o (pairEncode (List.replicate n true) (Nat.bits p))
        (cf (.prL l) (ev ρ ps (o₀ + j) j)) = cf (.prC l) (ev ρ ps (o₀ + j) j) := by
      simp [astep, A, hP, show j ≠ ρ r by omega]
    rw [e1]
    refine AHalt.step (hG _ _ _ (by omega) (by omega)) ?_
    have e2 : astep (A P l₀ lm) o (pairEncode (List.replicate n true) (Nat.bits p))
        (cf (.prC l) (ev ρ ps (o₀ + j) j)) = cf (.prB l) (ev ρ ps (o₀ + j) j) := by
      simp only [astep, A, ev_rO, jeqIn_eq, show o₀ + j ≠ p by omega, ↓reduceIte]
    rw [e2]
    refine AHalt.step (hG _ _ _ (by omega) (by omega)) ?_
    simp only [astep, A, ev_rO, upd_rO]
    refine AHalt.step (hG _ _ _ (by omega) (by omega)) ?_
    simp only [astep, A, ev_rT, upd_rT]
    have := ih (j + 1) (by omega)
    rwa [show o₀ + j + 1 = o₀ + (j + 1) by ring]

include ho0 ho1 in
/-- **One counter step.** From the configuration simulating the counter state
`⟨l, ρ, ps, out⟩` (with `|out| ≤ p`) the machine either answers `0` because `P` halts, or
reaches the configuration simulating the next state, or — if the step prints the `p`-th bit —
answers `ans lm s' p` for the next state `s'`; all through configurations within `B`.

**Proof sketch.** By cases on the instruction: register instructions are one machine step;
printing a bit compares the count with `p` (`jeqIn`); printing a register is the print loop
(`pr_reach`, `pr_halt`); reading asks the length decider, then the bit decider, and advances
the position. -/
lemma sim_step (l : Λ) (ρ : Fin R → ℕ) (ps : ℕ) (out : List Bool) (tm : ℕ)
    (hp : out.length ≤ p) (hρ : ∀ r, ρ r ≤ B) (hps : ps ≤ B) (hout : out.length ≤ B)
    (htm : tm ≤ B) (s' : CounterProg.St R Λ)
    (hs : s' = CounterProg.step P u ⟨some l, ρ, ps, out⟩) (hρ' : ∀ r, s'.regs r ≤ B)
    (hps' : s'.pos ≤ B) (hout' : s'.out.length ≤ B) :
    (s'.lbl = none ∧ s'.out = out ∧
      AHalt (A P l₀ lm) o (pairEncode (List.replicate n true) (Nat.bits p))
        (G P l₀ lm B (pairEncode (List.replicate n true) (Nat.bits p)))
        (cf (.sim l) (ev ρ ps out.length tm)) false) ∨
    (∃ l', s'.lbl = some l' ∧
      ((s'.out.length ≤ p ∧ ∃ tm' ≤ B,
        AReach (A P l₀ lm) o (pairEncode (List.replicate n true) (Nat.bits p))
          (G P l₀ lm B (pairEncode (List.replicate n true) (Nat.bits p)))
          (cf (.sim l) (ev ρ ps out.length tm))
          (cf (.sim l') (ev s'.regs s'.pos s'.out.length tm')))
      ∨ (p < s'.out.length ∧
        AHalt (A P l₀ lm) o (pairEncode (List.replicate n true) (Nat.bits p))
          (G P l₀ lm B (pairEncode (List.replicate n true) (Nat.bits p)))
          (cf (.sim l) (ev ρ ps out.length tm)) (ans lm s'.out p)))) := by
  set y := pairEncode (List.replicate n true) (Nat.bits p) with hy
  have hG0 := G_ev (n := n) (p := p) (P := P) (l₀ := l₀) (lm := lm) (.sim l) ρ ps out.length tm
    hρ hps hout htm
  cases hP : P l with
  | halt =>
    left
    have : s' = ⟨none, ρ, ps, out⟩ := by rw [hs]; simp [CounterProg.step, hP]
    subst this
    exact ⟨rfl, rfl, AHalt.ret (by simp [A, hP]) hG0⟩
  | goto l' =>
    have : s' = ⟨some l', ρ, ps, out⟩ := by rw [hs]; simp [CounterProg.step, hP]
    subst this
    refine Or.inr ⟨l', rfl, Or.inl ⟨hp, tm, htm, AReach.step hG0 ?_⟩⟩
    have : astep (A P l₀ lm) o y (cf (.sim l) (ev ρ ps out.length tm)) =
        cf (.sim l') (ev ρ ps out.length tm) := by simp [astep, A, hP]
    rw [this]; exact AReach.refl _
  | out b l' =>
    have : s' = ⟨some l', ρ, ps, out ++ [b]⟩ := by rw [hs]; simp [CounterProg.step, hP]
    subst this
    simp only [List.length_append, List.length_singleton] at hout' ⊢
    refine Or.inr ⟨l', rfl, ?_⟩
    by_cases heq : out.length = p
    · refine Or.inr ⟨by omega, AHalt.step hG0 ?_⟩
      have : astep (A P l₀ lm) o y (cf (.sim l) (ev ρ ps out.length tm)) =
          cf (.ans (lm || b)) (ev ρ ps out.length tm) := by
        simp only [astep, A, hP, ev_rO, hy, jeqIn_eq, heq, ↓reduceIte]
      rw [this]
      have ha : ans lm (out ++ [b]) p = (lm || b) := by
        subst heq; cases lm <;> simp [ans, List.getD_eq_getElem?_getD]
      rw [ha]
      exact AHalt.ret rfl (G_ev _ _ _ _ _ hρ hps hout htm)
    · refine Or.inl ⟨by omega, tm, htm, AReach.step hG0 ?_⟩
      have : astep (A P l₀ lm) o y (cf (.sim l) (ev ρ ps out.length tm)) =
          cf (.bump l') (ev ρ ps out.length tm) := by
        simp only [astep, A, hP, ev_rO, hy, jeqIn_eq, heq, ↓reduceIte]
      rw [this]
      refine AReach.step (G_ev _ _ _ _ _ hρ hps hout htm) ?_
      simp only [astep, A, ev_rO, upd_rO]
      exact AReach.refl _
  | inc r l' =>
    have : s' = ⟨some l', Function.update ρ r (ρ r + 1), ps, out⟩ := by
      rw [hs]; simp [CounterProg.step, hP]
    subst this
    refine Or.inr ⟨l', rfl, Or.inl ⟨hp, tm, htm, AReach.step hG0 ?_⟩⟩
    simp only [astep, A, hP, ev_rg, upd_rg]
    exact AReach.refl _
  | dec r l' =>
    have : s' = ⟨some l', Function.update ρ r (ρ r - 1), ps, out⟩ := by
      rw [hs]; simp [CounterProg.step, hP]
    subst this
    refine Or.inr ⟨l', rfl, Or.inl ⟨hp, tm, htm, AReach.step hG0 ?_⟩⟩
    simp only [astep, A, hP, ev_rg, upd_rg]
    exact AReach.refl _
  | jz r l0 l1 =>
    have : s' = ⟨some (if ρ r = 0 then l0 else l1), ρ, ps, out⟩ := by
      rw [hs]; simp [CounterProg.step, hP]
    subst this
    refine Or.inr ⟨_, rfl, Or.inl ⟨hp, tm, htm, AReach.step hG0 ?_⟩⟩
    by_cases hr : ρ r = 0
    · simp only [astep, A, hP, ev_rg, hr, ↓reduceIte]; exact AReach.refl _
    · simp only [astep, A, hP, ev_rg, hr, ↓reduceIte]; exact AReach.refl _
  | pr r l' =>
    have : s' = ⟨some l', ρ, ps, out ++ List.replicate (ρ r) true⟩ := by
      rw [hs]; simp [CounterProg.step, hP]
    subst this
    simp only [List.length_append, List.length_replicate] at hout' ⊢
    refine Or.inr ⟨l', rfl, ?_⟩
    have e0 : astep (A P l₀ lm) o y (cf (.sim l) (ev ρ ps out.length tm)) =
        cf (.prL l) (ev ρ ps (out.length + 0) 0) := by
      simp only [astep, A, hP, upd_rT, Nat.add_zero]
    by_cases hle : out.length + ρ r ≤ p
    · refine Or.inl ⟨hle, ρ r, hρ r, AReach.step hG0 ?_⟩
      rw [e0]
      exact pr_reach hP ρ ps out.length hρ hps hle hout' (ρ r) 0 (by omega)
    · refine Or.inr ⟨by omega, AHalt.step hG0 ?_⟩
      rw [e0]
      have ha : ans lm (out ++ List.replicate (ρ r) true) p = true := by
        cases lm
        · simp only [ans, Bool.false_eq_true, ↓reduceIte, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega), List.getElem?_replicate]
          rw [if_pos (by omega)]; rfl
        · simp [ans]; omega
      rw [ha]
      exact pr_halt hP ρ ps out.length hρ hps (by omega) hout' (p - out.length) 0 (by omega)
  | rd le lf lt =>
    have hcall : A P l₀ lm (.sim l) = .call 0 .unaryFst [rP R] (.rdB l) (.sim le) := by
      simp [A, hP]
    cases hx : u[ps]? with
    | none =>
      have : s' = ⟨some le, ρ, ps, out⟩ := by rw [hs]; simp [CounterProg.step, hP, hx]
      subst this
      refine Or.inr ⟨le, rfl, Or.inl ⟨hp, tm, htm, AReach.step hG0 ?_⟩⟩
      rw [astep_call₁ _ _ hcall, ho0]
      have : ¬ ps < u.length := by
        intro h; rw [List.getElem?_eq_getElem h] at hx; exact absurd hx (by simp)
      simp only [ev_rP, this, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact AReach.refl _
    | some b =>
      have hlt : ps < u.length := (List.getElem?_eq_some_iff.mp hx).1
      have hb : u.getD ps false = b := by simp [List.getD_eq_getElem?_getD, hx]
      have : s' = ⟨some (if b then lt else lf), ρ, ps + 1, out⟩ := by
        rw [hs]; cases b <;> simp [CounterProg.step, hP, hx]
      subst this
      refine Or.inr ⟨_, rfl, Or.inl ⟨hp, tm, htm, AReach.step hG0 ?_⟩⟩
      rw [astep_call₁ _ _ hcall, ho0]
      simp only [ev_rP, hlt, decide_true, ↓reduceIte]
      refine AReach.step (G_ev _ _ _ _ _ hρ hps hout htm) ?_
      rw [astep_call₁ _ _ (show A P l₀ lm (.rdB l) = .call 1 .unaryFst [rP R] (.rdT l) (.rdF l)
        from rfl), ho1]
      simp only [ev_rP, hb]
      refine AReach.step (G_ev _ _ _ _ _ hρ hps hout htm) ?_
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte, astep, A, hP, ev_rP, upd_rP]
        exact AReach.refl _
      · simp only [↓reduceIte, astep, A, hP, ev_rP, upd_rP]
        exact AReach.refl _

end Step

end CPSim

end Complexity

```


## ===== TCSlib/Complexity/SpaceComplexity/CounterProgSimRun.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.CounterProgSim

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Counter programs on unary-logspace inputs are unary-logspace

The closure property behind the logspace half of [AB09, Remark 6.7]: if a counter program
(`Complexity.CounterProg`) halts within polynomially many steps on the words `u(n)`, and `u`
is unary-logspace (its bits and length are decidable in logarithmic space from `⟨1ⁿ, i⟩`),
then so is the sequence of its outputs. This is the composition of implicitly logspace
computable functions [AB09, Lemma 4.17] in the special form needed here: the second
function is a polynomial-time counter program, whose registers are therefore polynomially
bounded and fit in `O(log n)` bits.

## Main results

* `Complexity.CPSim.sim_run` — the simulating machine answers for the whole run.
* `Complexity.UnaryLogspace.counterProg` — the closure property.
* `Complexity.CounterProg.length_out_le` — the outputs have polynomial length.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.3, Lemma 4.17; §6.1.1, Remark 6.7.)
-/

namespace Complexity

namespace CPSim

open Turing LogProg

variable {R : ℕ} {Λ : Type} {P : Λ → CounterProg.Instr R Λ} {l₀ : Λ} {lm : Bool}

/-- The answer for an index inside a prefix is the prefix's answer. -/
lemma ans_append (O e : List Bool) {p : ℕ} (hp : p < O.length) :
    ans lm (O ++ e) p = ans lm O p := by
  cases lm
  · simp [ans, List.getD_eq_getElem?_getD, List.getElem?_append_left hp]
  · simp [ans]; omega

/-- Past the output the answer is `0`. -/
lemma ans_of_le (O : List Bool) {p : ℕ} (hp : O.length ≤ p) : ans lm O p = false := by
  cases lm
  · simp [ans, List.getD_eq_getElem?_getD, List.getElem?_eq_none hp]
  · simp [ans]; omega

/-- The counter state is within `B`. -/
def Bd (B : ℕ) (s : CounterProg.St R Λ) : Prop :=
  (∀ r, s.regs r ≤ B) ∧ s.pos ≤ B ∧ s.out.length ≤ B

section Run

variable {n p : ℕ} {u : List Bool} {o : Fin 2 → List Bool → Bool}
  (ho0 : ∀ h, o 0 (pairEncode (List.replicate n true) (Nat.bits h)) = decide (h < u.length))
  (ho1 : ∀ h, o 1 (pairEncode (List.replicate n true) (Nat.bits h)) = u.getD h false)
  {B : ℕ}

include ho0 ho1 in
/-- **The whole run.** From the configuration simulating a running counter state `s` with
`|out| ≤ p`, if `P` halts after `k` more steps, all states within `B`, the machine answers
`ans lm O p` for the final output `O`.

**Proof sketch.** Induction on `k`, one counter step at a time (`sim_step`): a halting step
answers `0` (the index is past the output); a step printing the `p`-th bit answers it, and
later steps only append (`CounterProg.run_out`, `ans_append`); otherwise continue. -/
lemma sim_run : ∀ (k : ℕ) (s : CounterProg.St R Λ) (tm : ℕ) (l : Λ), s.lbl = some l →
    s.out.length ≤ p → tm ≤ B → (CounterProg.run P u s k).lbl = none →
    (∀ j ≤ k, Bd B (CounterProg.run P u s j)) →
    AHalt (A P l₀ lm) o (pairEncode (List.replicate n true) (Nat.bits p))
      (G P l₀ lm B (pairEncode (List.replicate n true) (Nat.bits p)))
      (cf (.sim l) (ev s.regs s.pos s.out.length tm)) (ans lm (CounterProg.run P u s k).out p) := by
  intro k
  induction k with
  | zero =>
    intro s tm l hl _ _ hk _
    rw [CounterProg.run_zero, hl] at hk; exact absurd hk (by simp)
  | succ k ih =>
    intro s tm l hl hp htm hk hbd
    obtain ⟨lbl, ρ, ps, out⟩ := s
    simp only at hl; subst hl
    obtain ⟨hρ, hps, hout⟩ := hbd 0 (by omega)
    obtain ⟨hρ', hps', hout'⟩ := hbd 1 (by omega)
    rw [CounterProg.run_zero] at hρ hps hout
    rcases sim_step (P := P) (l₀ := l₀) (lm := lm) ho0 ho1 l ρ ps out tm hp hρ hps hout htm
      (CounterProg.step P u ⟨some l, ρ, ps, out⟩) rfl hρ' hps' hout' with
      ⟨hnone, hout1, hh⟩ | ⟨l', hl', (⟨hle, tm', htm', hr⟩ | ⟨hlt, hh⟩)⟩
    · rw [CounterProg.run_succ, CounterProg.run_of_halted _ _ _ hnone, hout1,
        ans_of_le _ hp]
      exact hh
    · rw [CounterProg.run_succ] at hk ⊢
      refine hr.halt (ih _ tm' l' hl' hle htm' hk fun j hj => ?_)
      have := hbd (j + 1) (by omega)
      rwa [CounterProg.run_succ] at this
    · rw [CounterProg.run_succ]
      obtain ⟨e, he⟩ := CounterProg.run_out P u (CounterProg.step P u ⟨some l, ρ, ps, out⟩) k
      rw [he, ans_append _ _ hlt]
      exact hh

end Run

end CPSim

namespace CounterProg

variable {R : ℕ} {Λ : Type}

/-- **Outputs of polynomially many steps have polynomial length**: `t ≤ C (n + 1)^c` steps
print at most `(C + 1)² (n + 1)^{2c}` bits. -/
theorem length_out_le (P : Λ → Instr R Λ) (l₀ : Λ) (x : List Bool) (C c n t : ℕ)
    (ht : t ≤ C * (n + 1) ^ c) :
    (run P x (init l₀) t).out.length ≤ (C + 1) ^ 2 * (n + 1) ^ (2 * c) := by
  have h := run_init_out_le P x l₀ t
  have h1 : 1 ≤ (n + 1) ^ c := Nat.one_le_pow _ _ (by omega)
  have e : (C + 1) ^ 2 * (n + 1) ^ (2 * c) = ((C + 1) * (n + 1) ^ c) ^ 2 := by ring
  rw [e]
  have : t + 1 ≤ (C + 1) * (n + 1) ^ c := by nlinarith
  nlinarith

end CounterProg

open Turing LogProg CPSim in
/-- **Counter programs preserve unary-logspace sequences** [AB09, Lemma 4.17, for a
polynomial-time counter program as the outer function]: if `u` is unary-logspace and the
counter program `P` halts on every `u(n)` within `C (n + 1)^c` steps with output `g(n)`, then
`g` is unary-logspace.

**Proof sketch.** For each of the two languages, `arm_decides_poly` with the simulating
machine `CPSim.A` (length or bit mode) and the deciders of `u`: on `⟨1ⁿ, bits p⟩` the
machine validates the input and runs `sim_run` from the initial state. Within `t ≤ N =
C (n + 1)^c` steps the registers are at most `N`, the input position at most `N`, the output
count at most `N (N + 1)` (`CounterProg.run_init_out_le`), so all registers are below
`(N + 1)² ≤ (C + 1)² (|y| + 1)^{2c}`. Malformed inputs are rejected at once. -/
theorem UnaryLogspace.counterProg {R : ℕ} {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    (P : Λ → CounterProg.Instr R Λ) (l₀ : Λ) {u g : ℕ → List Bool} (hu : UnaryLogspace u)
    (C c : ℕ) (hrun : ∀ n, ∃ t ≤ C * (n + 1) ^ c,
      (CounterProg.run P (u n) (CounterProg.init l₀) t).lbl = none ∧
      (CounterProg.run P (u n) (CounterProg.init l₀) t).out = g n) :
    UnaryLogspace g := by
  let As : Fin 2 → Language Bool := fun j => if j = 0 then uLen u else uBit u
  have hAs : ∀ j, As j ∈ LOGSPACE := by
    intro j; fin_cases j
    · exact hu.2
    · exact hu.1
  have key : ∀ lm : Bool, (if lm then uLen g else uBit g) ∈ LOGSPACE := by
    intro lm
    refine arm_decides_poly (A P l₀ lm) .start As hAs ((C + 1) ^ 2) (2 * c) fun y => ?_
    by_cases hv : ValidPlain y
    · obtain ⟨n, w, rfl, hw⟩ := hv
      rw [canon_eq_bits w hw]
      set p := bitsVal w
      obtain ⟨t, ht, hhalt, hout⟩ := hrun n
      set N := C * (n + 1) ^ c with hN
      set B := (N + 1) ^ 2 with hB
      have ho0 : ∀ h, (fun j V => MultiTapeTM.indicator (As j : Set (List Bool)) V) 0
          (pairEncode (List.replicate n true) (Nat.bits h)) = decide (h < (u n).length) := by
        intro h
        simp only [As, ↓reduceIte, indicator_eq_decide]
        exact decide_eq_decide.mpr (mem_uLen u n h)
      have ho1 : ∀ h, (fun j V => MultiTapeTM.indicator (As j : Set (List Bool)) V) 1
          (pairEncode (List.replicate n true) (Nat.bits h)) = (u n).getD h false := by
        intro h
        show MultiTapeTM.indicator (uBit u : Set (List Bool)) _ = _
        have := mem_uBit u n h
        unfold MultiTapeTM.indicator
        split_ifs with hm <;> cases hb : (u n).getD h false <;> simp_all
      have hbd : ∀ j ≤ t, Bd B (CounterProg.run P (u n) (CounterProg.init l₀) j) := by
        intro j hj
        have hjN : j ≤ N := hj.trans ht
        have hNB : N * (N + 1) ≤ B := by simp only [hB]; nlinarith
        have hNN : N ≤ N * (N + 1) := Nat.le_mul_of_pos_right _ (by omega)
        refine ⟨fun r => ?_, ?_, ?_⟩
        · have := CounterProg.run_regs_le P (u n) (CounterProg.init l₀) r j
          have h0 : (CounterProg.init l₀ : CounterProg.St R Λ).regs r = 0 := rfl
          omega
        · have := CounterProg.run_pos_le P (u n) (CounterProg.init l₀) j
          have h0 : (CounterProg.init l₀ : CounterProg.St R Λ).pos = 0 := rfl
          omega
        · have := CounterProg.run_init_out_le P (u n) l₀ j
          have : j * (j + 1) ≤ N * (N + 1) := Nat.mul_le_mul hjN (by omega)
          omega
      have hrunA := sim_run (P := P) (l₀ := l₀) (lm := lm) (B := B) (n := n) (p := p)
        (o := fun j V => MultiTapeTM.indicator (As j : Set (List Bool)) V) ho0 ho1 t
        (CounterProg.init l₀) 0 l₀ rfl (by simp [CounterProg.init]) (Nat.zero_le _) hhalt hbd
      rw [hout] at hrunA
      have hans : ans lm (g n) p = MultiTapeTM.indicator
          ((if lm then uLen g else uBit g : Language Bool) : Set (List Bool))
          (pairEncode (List.replicate n true) (Nat.bits p)) := by
        cases lm
        · show (g n).getD p false = MultiTapeTM.indicator (uBit g : Set (List Bool)) _
          have := mem_uBit g n p
          unfold MultiTapeTM.indicator
          split_ifs with hm <;> cases hb : (g n).getD p false <;> simp_all
        · show decide (p < (g n).length) = MultiTapeTM.indicator (uLen g : Set (List Bool)) _
          have := mem_uLen g n p
          unfold MultiTapeTM.indicator
          split_ifs with hm <;> simp_all
      rw [← hans]
      have hval : ValidPlain (pairEncode (List.replicate n true) (Nat.bits p)) :=
        ⟨n, _, rfl, canon_bits p⟩
      have hev : (fun _ => 0 : Fin (R + 3) → ℕ) =
          ev (CounterProg.init l₀ : CounterProg.St R Λ).regs (CounterProg.init l₀ :
            CounterProg.St R Λ).pos (CounterProg.init l₀ : CounterProg.St R Λ).out.length 0 := by
        funext i; simp only [ev, CounterProg.init]; split_ifs <;> rfl
      refine AHalt.step ⟨preS_A P l₀ lm hval _, fun r => by simp⟩ ?_
      have : astep (A P l₀ lm) (fun j V => MultiTapeTM.indicator (As j : Set (List Bool)) V)
          (pairEncode (List.replicate n true) (Nat.bits p)) (some .start, fun _ => 0, none) =
          cf (.sim l₀) (ev (CounterProg.init l₀ : CounterProg.St R Λ).regs
            (CounterProg.init l₀ : CounterProg.St R Λ).pos
            (CounterProg.init l₀ : CounterProg.St R Λ).out.length 0) := by
        rw [← hev]; simp [astep, A, hval]
      rw [this]
      refine hrunA.mono fun a ⟨h1, h2⟩ => ⟨h1, fun r => (h2 r).trans ?_⟩
      have hn : n + 1 ≤ (pairEncode (List.replicate n true) (Nat.bits p)).length + 1 := by
        simp [pairEncode_eq_dbl, dbl_replicate]; omega
      have h1 : 1 ≤ (n + 1) ^ c := Nat.one_le_pow _ _ (by omega)
      calc B = (C * (n + 1) ^ c + 1) ^ 2 := rfl
        _ ≤ ((C + 1) * (n + 1) ^ c) ^ 2 := Nat.pow_le_pow_left (by nlinarith) 2
        _ = (C + 1) ^ 2 * (n + 1) ^ (2 * c) := by ring
        _ ≤ (C + 1) ^ 2 * ((pairEncode (List.replicate n true) (Nat.bits p)).length + 1) ^
            (2 * c) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn _)
    · have hn : MultiTapeTM.indicator ((if lm then uLen g else uBit g : Language Bool) :
          Set (List Bool)) y = false := by
        rw [indicator_eq_decide]
        simp only [decide_eq_false_iff_not]
        intro h
        cases lm
        · exact hv (validPlain_of_mem_unaryIdx (p := fun n i => (g n).getD i false = true) h)
        · exact hv (validPlain_of_mem_unaryIdx (p := fun n i => i < (g n).length) h)
      rw [hn]
      refine ⟨1, ?_, ?_, fun t ht => ?_⟩
      · simp [arun, astep, A, hv]
      · simp [arun, astep, A, hv]
      · obtain rfl : t = 0 := by omega
        exact ⟨by simp [arun, PreS, A], fun r => by simp [arun]⟩
  exact ⟨by simpa using key false, by simpa using key true⟩

end Complexity

```


## ===== TCSlib/Complexity/SpaceComplexity.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Basic
import TCSlib.Complexity.SpaceComplexity.ConfigCount
import TCSlib.Complexity.SpaceComplexity.Machines.Layout
import TCSlib.Complexity.SpaceComplexity.Machines.Program
import TCSlib.Complexity.SpaceComplexity.Machines.Sim
import TCSlib.Complexity.SpaceComplexity.Machines.CallReturn
import TCSlib.Complexity.SpaceComplexity.Machines.Call
import TCSlib.Complexity.SpaceComplexity.Machines.Compile
import TCSlib.Complexity.SpaceComplexity.Machines.CleanSweep
import TCSlib.Complexity.SpaceComplexity.Machines.Clean
import TCSlib.Complexity.SpaceComplexity.Machines.Bank
import TCSlib.Complexity.SpaceComplexity.Machines.Bin
import TCSlib.Complexity.SpaceComplexity.Machines.Lib
import TCSlib.Complexity.SpaceComplexity.Machines.FragDec
import TCSlib.Complexity.SpaceComplexity.Machines.Frag
import TCSlib.Complexity.SpaceComplexity.Machines.ParsePlain
import TCSlib.Complexity.SpaceComplexity.Machines.Parse
import TCSlib.Complexity.SpaceComplexity.Machines.Parse2
import TCSlib.Complexity.SpaceComplexity.Machines.ParseCmp
import TCSlib.Complexity.SpaceComplexity.Machines.ARM
import TCSlib.Complexity.SpaceComplexity.Machines.ARMSim
import TCSlib.Complexity.SpaceComplexity.Machines.ARMRun
import TCSlib.Complexity.SpaceComplexity.Machines.ARMProof
import TCSlib.Complexity.SpaceComplexity.Machines.ARMKit
import TCSlib.Complexity.SpaceComplexity.Machines.DblLang
import TCSlib.Complexity.SpaceComplexity.UnaryLogspace
import TCSlib.Complexity.SpaceComplexity.CounterProgSim
import TCSlib.Complexity.SpaceComplexity.CounterProgSimRun
import TCSlib.Complexity.SpaceComplexity.ImplicitPoly

/-!
# Space complexity

Space-bounded computation and logarithmic space [AB09, §4.1, §4.3]: the classes `SPACE(s)`
and `L`, `L ⊆ P` by configuration counting, implicitly logspace computable functions and
their polynomial-time computability, with a toolkit of logspace machines (register-tape
programs calling logspace deciders on virtual inputs, and abstract register machines
compiled onto them).

Related model: `Complexity.CounterProg` (`TCSlib.Complexity.TuringMachine.CounterProg`) is a
goto program over unary counters for the polynomial-time emitters of [AB09, §6.2]. It overlaps
in spirit with the programs here, which store registers in binary (as logarithmic space
requires) and call deciders on virtual inputs; the two are kept separate, and a polynomially
running counter program is simulated by an abstract register machine in
`TCSlib.Complexity.SpaceComplexity.CounterProgSim`.

## Contents

- `SpaceComplexity.Basic`: Def 4.1 space-bounded computation, `SPACE(s)`, `L`; Def 4.16
  implicitly logspace computable functions
- `SpaceComplexity.ConfigCount`: configuration counting; `L ⊆ P`; logspace functions run in
  polynomial time
- `SpaceComplexity.Machines.Layout`: virtual inputs assembled from segments
- `SpaceComplexity.Machines.Program`: register-tape programs with call nodes and their
  compilation
- `SpaceComplexity.Machines.Sim`: the lockstep simulation of a call's decider
- `SpaceComplexity.Machines.CallReturn`: compiled configurations; the return phase of a call
- `SpaceComplexity.Machines.Call`: the run of a call node
- `SpaceComplexity.Machines.Compile`: correctness and space of compiled programs
- `SpaceComplexity.Machines.CleanSweep`: the cleaned machine; the cleanup sweeps of one tape
- `SpaceComplexity.Machines.Clean`: the clean normal form of deciders (the whole run)
- `SpaceComplexity.Machines.Bank`: a bank of clean deciders
- `SpaceComplexity.Machines.Bin`: binary words of numbers
- `SpaceComplexity.Machines.Lib`: register steps and the increment fragment
- `SpaceComplexity.Machines.FragDec`: decrement and clear fragments
- `SpaceComplexity.Machines.Frag`: halve and equality fragments
- `SpaceComplexity.Machines.ParsePlain`: input shapes; the format check on inputs `⟨1ⁿ, w⟩`
- `SpaceComplexity.Machines.Parse`: comparisons on inputs `⟨1ⁿ, w⟩`
- `SpaceComplexity.Machines.Parse2`: the format check on inputs `⟨1ⁿ, ⟨u, w⟩⟩`
- `SpaceComplexity.Machines.ParseCmp`: comparisons on inputs `⟨1ⁿ, ⟨u, w⟩⟩`
- `SpaceComplexity.Machines.ARM`: abstract register machines and their compilation
- `SpaceComplexity.Machines.ARMSim`: per-instruction simulation
- `SpaceComplexity.Machines.ARMRun`: the run and space theorems of compiled machines
- `SpaceComplexity.Machines.ARMProof`: proving abstract machines correct; `arm_decides`
- `SpaceComplexity.Machines.ARMKit`: calls on unary inputs; `arm_decides_poly`
- `SpaceComplexity.Machines.DblLang`: reading the unary length `⟨1ⁿ, bits (2n)⟩` in
  logarithmic space
- `SpaceComplexity.ImplicitPoly`: implicitly logspace computable functions are
  polynomial-time computable
- `SpaceComplexity.UnaryLogspace`: functions of the unary length computable in logarithmic
  space (`UnaryLogspace`, `unaryExt`)
- `SpaceComplexity.CounterProgSim`, `SpaceComplexity.CounterProgSimRun`: polynomially
  running counter programs on unary-logspace inputs are unary-logspace

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1, §4.3.)
-/

```


## ===== TCSlib/Complexity/TimeHierarchy/ClockMachine.lean =====

```
/-
Copyright (c) 2026 Hydroxyi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Data.Nat.Bits
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Ring
import TCSlib.Complexity.TuringMachine.Simulation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The clocked runner: machine and setup phases

[AB09, Theorem 3.1, proof]: the diagonalizing machine of the time hierarchy theorem
runs the universal machine "for `g(|x|)` steps" and then answers. This file builds the
**clocked runner** `clockTM K W` realizing that sentence for an arbitrary (possibly
partial) machine `W`, with the step budget supplied by a second machine `K` (in the
hierarchy theorem, the time-constructibility witness of `g`).

The runner has three tape blocks (`Turing.FinTM.tapeBlocks`): `K`'s work tapes, one
**counter tape**, and `W`'s work tapes. It proceeds in phases:

1. *Budget.* Simulate `K` on the input, redirecting every emission onto the counter
   tape (exactly as phase one of `Turing.FinTM.bufferedCompTM`). The counter then holds
   `K`'s output word `s`, read as a little-endian binary number `ctrVal s`.
2. *Rewind.* Return the counter head to cell `0`, then the input head to the first
   input cell (`Turing.FinTM.timed_rewind`).
3. *Loop* (`ClockState.dec` / `ClockState.ret`). Decrement the counter by a
   little-endian borrow sweep; the step that clears the low `true` bit is fused with
   **one transition of `W`** on its own tape block and the native input, after which
   the counter head returns to cell `0`. `W`'s emissions are not passed to the output;
   they are summarized in a three-valued register `OutReg` ("empty", "one symbol `b`",
   "two or more symbols"). If the borrow sweep runs off the counter (value zero), the
   runner emits `true` and halts (timeout); if `W` halts, the runner emits `false`
   exactly when `W`'s completed output is `[true]`, and halts.

This file contains the machine, its configurations, and the exact run lemmas of the
budget and rewind phases. The loop and the specification `clockTM_spec` are in
`TCSlib.Complexity.TimeHierarchy.ClockLoop`.

## Design

* The runner clocks **its own simulation steps of `W`**, not steps of a machine that
  `W` might itself simulate. This is what makes the hierarchy proof go through in this
  development: the universal machine's per-code constant `C_α` has no uniform bound
  over codes `α` (it contains the representation scheme's abstract canonizer time), so
  a clock on *simulated* steps would not bound the diagonal machine's running time.
* The counter is a binary down-counter, not a unary one, so that a budget `g(n)` costs
  only `O(log g(n))` cells; the amortized analysis (in `ClockLoop.lean`) shows that
  `v` decrements cost `O(v + |s|)` steps in total.

## Main definitions

* `Complexity.TimeHierarchy.OutReg` — the output-summary register.
* `Complexity.TimeHierarchy.ctrVal`, `ctrPop` — value and popcount of a counter word.
* `Complexity.TimeHierarchy.clockTM` — the clocked runner.

## Main results

* `Complexity.TimeHierarchy.clockTM_setup` — from the initial configuration, the
  runner reaches the loop entry with counter word `s = K(x)` and a fresh copy of `W`'s
  initial configuration within `t_K + |s| + |x| + 5` steps.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.1, Theorem 3.1 and its proof, p. 69.)
-/

namespace Complexity.TimeHierarchy

open Turing Turing.FinTM

/-! ### The output-summary register -/

/-- A three-valued summary of a binary word: empty, a single symbol `b`, or two or
more symbols. It is exactly enough to decide whether a completed output is `[true]`. -/
inductive OutReg where
  | empty : OutReg
  | one : Bool → OutReg
  | many : OutReg
  deriving DecidableEq, Fintype

/-- The summary of a word. -/
def OutReg.ofList : List Bool → OutReg
  | [] => .empty
  | [b] => .one b
  | _ :: _ :: _ => .many

/-- The summary after appending an optional emitted symbol. -/
def OutReg.push : OutReg → Option Bool → OutReg
  | r, none => r
  | .empty, some b => .one b
  | .one _, some _ => .many
  | .many, some _ => .many

/-- Appending an optional emission commutes with summarizing. -/
lemma OutReg.ofList_push (w : List Bool) (o : Option Bool) :
    OutReg.ofList (w ++ o.toList) = (OutReg.ofList w).push o := by
  rcases o with _ | b
  · cases h : OutReg.ofList w <;> simp [OutReg.push, h]
  · match w with
    | [] => rfl
    | [_] => rfl
    | _ :: _ :: _ => rfl

/-- The summary is `one true` exactly for the word `[true]`. -/
lemma OutReg.ofList_eq_one_true (w : List Bool) :
    OutReg.ofList w = .one true ↔ w = [true] := by
  match w with
  | [] => simp [OutReg.ofList]
  | [b] => simp [OutReg.ofList]
  | _ :: _ :: _ => simp [OutReg.ofList]

/-! ### Counter words -/

/-- The little-endian value of a counter word (low bit first; leading zeros at the
high end allowed). -/
def ctrVal : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * ctrVal bs

/-- The number of `true` bits of a counter word. -/
def ctrPop : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + ctrPop bs

/-- The popcount is at most the width. -/
lemma ctrPop_le_length (s : List Bool) : ctrPop s ≤ s.length := by
  induction s with
  | nil => simp [ctrPop]
  | cons b s ih => cases b <;> simp [ctrPop] <;> omega

/-- The value of `Nat.bits n` is `n`. -/
lemma ctrVal_bits (n : ℕ) : ctrVal n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [ctrVal]
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn]
    cases b <;> simp [ctrVal, ih, Nat.bit_val]; omega

/-- Low zeros multiply the value by a power of two. -/
lemma ctrVal_replicate_false (j : ℕ) (rest : List Bool) :
    ctrVal (List.replicate j false ++ rest) = 2 ^ j * ctrVal rest := by
  induction j with
  | zero => simp
  | succ j ih =>
    simp only [List.replicate_succ, List.cons_append, ctrVal, ih]
    simp [Nat.pow_succ]
    ring

/-- Low ones contribute `2^j - 1`. -/
lemma ctrVal_replicate_true (j : ℕ) (rest : List Bool) :
    ctrVal (List.replicate j true ++ rest) + 1 = 2 ^ j * (ctrVal rest + 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
    simp only [List.replicate_succ, List.cons_append, ctrVal, if_true]
    rw [Nat.pow_succ]
    have : 1 + 2 * ctrVal (List.replicate j true ++ rest) + 1 =
        2 * (ctrVal (List.replicate j true ++ rest) + 1) := by ring
    rw [this, ih]
    ring

/-- One borrow: the value of `0^j 1 rest` exceeds that of `1^j 0 rest` by one. -/
lemma ctrVal_borrow (j : ℕ) (rest : List Bool) :
    ctrVal (List.replicate j true ++ false :: rest) + 1 =
      ctrVal (List.replicate j false ++ true :: rest) := by
  rw [ctrVal_replicate_true, ctrVal_replicate_false]
  simp only [ctrVal, Bool.false_eq_true, if_false, if_true]
  ring

/-- Popcount of a word with a run of low bits. -/
lemma ctrPop_replicate (j : ℕ) (b : Bool) (rest : List Bool) :
    ctrPop (List.replicate j b ++ rest) = (if b then j else 0) + ctrPop rest := by
  induction j with
  | zero => cases b <;> simp
  | succ j ih =>
    simp only [List.replicate_succ, List.cons_append, ctrPop, ih]
    cases b <;> simp; omega

/-- A word of positive value has a lowest `true` bit. -/
lemma ctrVal_pos_decomp (s : List Bool) (h : ctrVal s ≠ 0) :
    ∃ j rest, s = List.replicate j false ++ true :: rest := by
  induction s with
  | nil => simp [ctrVal] at h
  | cons b s ih =>
    cases b with
    | true => exact ⟨0, s, by simp⟩
    | false =>
      have hs : ctrVal s ≠ 0 := by
        intro h0
        apply h
        simp [ctrVal, h0]
      obtain ⟨j, rest, rfl⟩ := ih hs
      exact ⟨j + 1, rest, by simp [List.replicate_succ]⟩

/-- A word of value zero is all `false`. -/
lemma ctrVal_zero_eq (s : List Bool) (h : ctrVal s = 0) :
    s = List.replicate s.length false := by
  induction s with
  | nil => rfl
  | cons b s ih =>
    cases b with
    | true => simp [ctrVal] at h
    | false =>
      have hs : ctrVal s = 0 := by simp [ctrVal] at h; omega
      simp [List.replicate_succ, ← ih hs]

/-! ### The machine -/

/-- Control states of the clocked runner: simulating the budget machine (`none` =
the budget machine has just halted), rewinding the counter, rewinding the input,
and the two loop phases carrying the simulated machine's live state and output
register. -/
inductive ClockState (KS WS : Type) where
  | kRun : Option KS → ClockState KS WS
  | cScan : ClockState KS WS
  | iStart : ClockState KS WS
  | iScan : ClockState KS WS
  | dec : WS → OutReg → ClockState KS WS
  | ret : WS → OutReg → ClockState KS WS
  deriving DecidableEq, Fintype

/-- The index of the counter tape in the three-block layout. -/
def ctrIdx (kK kW : ℕ) : Fin (kK + (1 + kW)) := Fin.natAdd kK (Fin.castAdd kW (0 : Fin 1))

/-- An action touching only the counter tape: write `w`, move `d`, go to `q`. -/
def ctrAction {kK kW : ℕ} {S : Type} (w : Option (Option Bool)) (d : SignType)
    (q : Option S) : Action (kK + (1 + kW)) Bool S :=
  ⟨0, tapeBlocks (fun _ => (none, 0)) (w, d) (fun _ => (none, 0)), none, q⟩

/-- The transition table of the clocked runner (see the module docstring). -/
def clockTr (K W : FinTM Bool) (q : ClockState K.State W.State) (inp : Option Bool)
    (work : Fin (K.k + (1 + W.k)) → Option Bool) :
    Action (K.k + (1 + W.k)) Bool (ClockState K.State W.State) :=
  match q with
  | .kRun (some q) =>
    let a := K.tm.tr q inp (fun i => work (Fin.castAdd (1 + W.k) i))
    ⟨a.inputTape, tapeBlocks a.workTapes
      (a.output.map some, if a.output = none then 0 else .pos)
      (fun _ => (none, 0)), none, some (.kRun a.state)⟩
  | .kRun none => ctrAction none .neg (some .cScan)
  | .cScan =>
    if work (ctrIdx K.k W.k) = none then ctrAction none .pos (some .iStart)
    else ctrAction none .neg (some .cScan)
  | .iStart => controlAction .neg (some .iScan)
  | .iScan =>
    match inp with
    | some _ => controlAction .neg (some .iScan)
    | none => controlAction .pos (some (.dec W.tm.q₀ .empty))
  | .dec q r =>
    match work (ctrIdx K.k W.k) with
    | none => ⟨0, fun _ => (none, 0), some true, none⟩
    | some false => ctrAction (some (some true)) .pos (some (.dec q r))
    | some true =>
      let a := W.tm.tr q inp (fun i => work (Fin.natAdd K.k (Fin.natAdd 1 i)))
      ⟨a.inputTape, tapeBlocks (fun _ => (none, 0)) (some (some false), .neg) a.workTapes,
        (if a.state = none then some (decide (r.push a.output ≠ .one true)) else none),
        a.state.map (fun q' => .ret q' (r.push a.output))⟩
  | .ret q r =>
    if work (ctrIdx K.k W.k) = none then ctrAction none .pos (some (.dec q r))
    else ctrAction none .neg (some (.ret q r))

/-- **The clocked runner** `clockTM K W` [AB09, Theorem 3.1, proof of the hierarchy
theorem, "run `M_x` for `g(|x|)` steps"]: compute the budget word `K(x)` onto a
counter tape, then alternate one step of `W` (on the native input, with emissions
summarized in a register) with one binary decrement of the counter; answer `true` on
counter underflow, and on `W`'s halting answer whether `W`'s output differs from
`[true]`. See the module docstring for the phases. -/
def clockTM (K W : FinTM Bool) : FinTM Bool where
  k := K.k + (1 + W.k)
  State := ClockState K.State W.State
  tm := { q₀ := .kRun (some K.tm.q₀), tr := clockTr K W }

/-! ### Configurations -/

variable (K W : FinTM Bool)

/-- One step from a live configuration applies the transition table. -/
lemma clockTM_step_some {x : List Bool}
    (c : Cfg (clockTM K W).k Bool (clockTM K W).State x) (q : ClockState K.State W.State)
    (h : c.state = some q) :
    (clockTM K W).tm.step c = (clockTr K W q c.inputSymbol c.workTapeSymbols).apply c := by
  unfold MultiTapeTM.step
  rw [h]
  rfl

/-- Budget phase: `K`'s configuration in the left block, its emitted word on the
counter tape with the counter head on the right blank, the right block blank. -/
def kCfg {x : List Bool} (c : Cfg K.k Bool K.State x) :
    Cfg (clockTM K W).k Bool (clockTM K W).State x where
  state := some (.kRun c.state)
  inputPos := c.inputPos
  workTapes := tapeBlocks c.workTapes (bufferTape c.output) (fun _ _ => none)
  workTapePos := tapeBlocks c.workTapePos c.output.length (fun _ => 0)
  output := []

/-- The initial configuration is the embedded initial budget configuration. -/
lemma kCfg_init (x : List Bool) :
    (clockTM K W).tm.initCfg x = kCfg K W (K.tm.initCfg x) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [kCfg, tapeBlocks]
    · intro j
      refine Fin.addCases ?_ ?_ j <;> intro j <;> simp [kCfg, tapeBlocks]
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [kCfg, tapeBlocks]
    · intro j
      refine Fin.addCases ?_ ?_ j <;> intro j <;> simp [kCfg, tapeBlocks]

/-- One live budget step: the left block and input head follow `K`; an emission is
appended to the counter word.

**Proof sketch.** As `Turing.FinTM.bufferedFirstCfg_step`: reads of the left block are
`K`'s reads, a non-emitting step leaves the counter fixed, and an emitting step writes
the right blank (`Turing.FinTM.bufferTape_append`) and advances the counter head. -/
lemma kCfg_step {x : List Bool} (c : Cfg K.k Bool K.State x) (hs : c.state ≠ none) :
    (clockTM K W).tm.step (kCfg K W c) = kCfg K W (K.tm.step c) := by
  cases hq : c.state with
  | none => exact False.elim (hs hq)
  | some q =>
    rw [clockTM_step_some K W _ (.kRun (some q)) (by simp [kCfg, hq])]
    have hr : (fun i => (kCfg K W c).workTapeSymbols (Fin.castAdd (1 + W.k) i)) =
        c.workTapeSymbols := by
      funext i
      simp [kCfg, Cfg.workTapeSymbols]
    have hi : (kCfg K W c).inputSymbol = c.inputSymbol := rfl
    simp only [clockTr]
    rw [hr, hi]
    have hstep : K.tm.step c = (K.tm.tr q c.inputSymbol c.workTapeSymbols).apply c := by
      unfold MultiTapeTM.step; rw [hq]
    rw [hstep]
    generalize K.tm.tr q c.inputSymbol c.workTapeSymbols = a
    refine Cfg.ext rfl rfl ?_ ?_ ?_
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [kCfg, Action.apply]
      · intro j
        refine Fin.addCases ?_ ?_ j
        · intro j
          cases ho : a.output <;> simp [kCfg, Action.apply, ho, bufferTape_append]
        · intro j; simp [kCfg, Action.apply]
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [kCfg, Action.apply]
      · intro j
        refine Fin.addCases ?_ ?_ j
        · intro j
          cases ho : a.output <;> simp [kCfg, Action.apply, ho]
        · intro j; simp [kCfg, Action.apply]
    · simp [kCfg, Action.apply]

/-- Budget-phase lockstep up to and including `K`'s first halting transition. -/
lemma kCfg_run {x : List Bool} (c : Cfg K.k Bool K.State x) (t : ℕ)
    (h : ∀ s, s < t → (K.tm.runFrom c s).state ≠ none) :
    (clockTM K W).tm.runFrom (kCfg K W c) t = kCfg K W (K.tm.runFrom c t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (fun s hs => h s (by omega)),
      kCfg_step K W _ (h t (by omega)), MultiTapeTM.runFrom_succ_eq_step']

/-- Loop-phase configurations: the state `st`, the simulated machine's configuration
`c` in the right block (its input head is the native one), an arbitrary counter tape
`τ` with head `z`, a frozen left block, and real output `out`. -/
def ctrCfg {x : List Bool} (st : Option (ClockState K.State W.State))
    (c : Cfg W.k Bool W.State x) (τ : ℤ → Option Bool) (z : ℤ)
    (kt : Fin K.k → ℤ → Option Bool) (kh : Fin K.k → ℤ) (out : List Bool) :
    Cfg (clockTM K W).k Bool (clockTM K W).State x where
  state := st
  inputPos := c.inputPos
  workTapes := tapeBlocks kt τ c.workTapes
  workTapePos := tapeBlocks kh z c.workTapePos
  output := out

/-- The counter read of a loop configuration. -/
lemma ctrCfg_ctr {x : List Bool} (st : Option (ClockState K.State W.State))
    (c : Cfg W.k Bool W.State x) (τ : ℤ → Option Bool) (z : ℤ)
    (kt : Fin K.k → ℤ → Option Bool) (kh : Fin K.k → ℤ) (out : List Bool) :
    (ctrCfg K W st c τ z kt kh out).workTapeSymbols (ctrIdx K.k W.k) = τ z := by
  simp [ctrCfg, Cfg.workTapeSymbols, ctrIdx]

/-- The right-block reads of a loop configuration are the simulated machine's reads. -/
lemma ctrCfg_right {x : List Bool} (st : Option (ClockState K.State W.State))
    (c : Cfg W.k Bool W.State x) (τ : ℤ → Option Bool) (z : ℤ)
    (kt : Fin K.k → ℤ → Option Bool) (kh : Fin K.k → ℤ) (out : List Bool) :
    (fun i => (ctrCfg K W st c τ z kt kh out).workTapeSymbols
      (Fin.natAdd K.k (Fin.natAdd 1 i))) = c.workTapeSymbols := by
  funext i
  simp [ctrCfg, Cfg.workTapeSymbols]

/-- Applying a counter-only action (optional write `w` to the counter cell, counter head
move `d`, next state `q`) to a loop configuration yields the loop configuration with
state `q`, counter tape updated at the head by `w`, counter head at `z + d`, and all
other blocks unchanged.

**Proof sketch.** Compare the two configurations componentwise: the state and output
agree by definition of the action, and the input head does not move. For the tape
contents and head positions, split the work tapes into the `K` block, the counter
tape, and the `W` block; on the `K` and `W` blocks the action writes nothing and stays
put, and on the counter tape case analysis on `w` gives the update and the move. -/
lemma ctrAction_apply {x : List Bool} (st : Option (ClockState K.State W.State))
    (c : Cfg W.k Bool W.State x) (τ : ℤ → Option Bool) (z : ℤ)
    (kt : Fin K.k → ℤ → Option Bool) (kh : Fin K.k → ℤ) (out : List Bool)
    (w : Option (Option Bool)) (d : SignType) (q : Option (ClockState K.State W.State)) :
    (ctrAction (kK := K.k) (kW := W.k) w d q).apply (ctrCfg K W st c τ z kt kh out) =
      ctrCfg K W q c (match w with | none => τ | some v => Function.update τ z v)
        (z + d) kt kh out := by
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ (by simp [ctrAction, ctrCfg])
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [ctrAction, ctrCfg, Action.apply]
    · intro j
      refine Fin.addCases ?_ ?_ j
      · intro j
        cases w <;> simp [ctrAction, ctrCfg, Action.apply]
      · intro j; simp [ctrAction, ctrCfg, Action.apply]
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [ctrAction, ctrCfg, Action.apply]
    · intro j
      refine Fin.addCases ?_ ?_ j <;> intro j <;> simp [ctrAction, ctrCfg, Action.apply]

/-! ### Rewinding the counter and the input -/

/-- Counter scan configuration: the counter head at cell `j - 1`, the right block
blank, the left block frozen. -/
def cScanCfg {x : List Bool} (s : List Bool) (p : Fin (x.length + 2))
    (kt : Fin K.k → ℤ → Option Bool) (kh : Fin K.k → ℤ) (j : ℕ) :
    Cfg (clockTM K W).k Bool (clockTM K W).State x :=
  ctrCfg K W (some .cScan) ⟨none, p, fun _ _ => none, fun _ => 0, []⟩ (bufferTape s)
    ((j : ℤ) - 1) kt kh []

/-- Scanning left from cell `j - 1` of a stored word reaches cell `0` and the input
rewind state in exactly `j + 1` steps.

**Proof sketch.** As `Turing.FinTM.bufferedScanCfg_run`: at `j = 0` the head reads the
left blank and moves right; at `j + 1` it reads a stored symbol and moves left. -/
lemma cScanCfg_run {x : List Bool} (s : List Bool) (p : Fin (x.length + 2))
    (kt : Fin K.k → ℤ → Option Bool) (kh : Fin K.k → ℤ) : ∀ j, j ≤ s.length →
    (clockTM K W).tm.runFrom (cScanCfg K W s p kt kh j) (j + 1) =
      ctrCfg K W (some .iStart) ⟨none, p, fun _ _ => none, fun _ => 0, []⟩ (bufferTape s)
        0 kt kh [] := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero,
      clockTM_step_some K W _ .cScan rfl]
    simp only [clockTr, cScanCfg, ctrCfg_ctr, Nat.cast_zero, zero_sub, bufferTape_left,
      if_true]
    rw [ctrAction_apply]
    simp
  | succ j ih =>
    intro hj
    have hread : bufferTape s (((j + 1 : ℕ) : ℤ) - 1) = some s[j] := by
      rw [show (((j + 1 : ℕ) : ℤ) - 1) = (j : ℤ) by omega,
        bufferTape_nat, List.getElem?_eq_getElem (by omega)]
    have hstep : (clockTM K W).tm.step (cScanCfg K W s p kt kh (j + 1)) =
        cScanCfg K W s p kt kh j := by
      rw [clockTM_step_some K W _ .cScan rfl]
      simp only [clockTr, cScanCfg, ctrCfg_ctr, hread, reduceCtorEq, if_false]
      rw [ctrAction_apply]
      congr 1
      push_cast
      simp [SignType.neg_eq_neg_one]
      ring
    rw [MultiTapeTM.runFrom_succ_eq_step, hstep]
    exact ih (by omega)

/-- From a halted budget configuration, the counter rewind takes exactly
`|s| + 2` steps, where `s` is the budget word. -/
lemma kCfg_rewind {x : List Bool} (c : Cfg K.k Bool K.State x) (hs : c.state = none) :
    (clockTM K W).tm.runFrom (kCfg K W c) (c.output.length + 2) =
      ctrCfg K W (some .iStart) ⟨none, c.inputPos, fun _ _ => none, fun _ => 0, []⟩
        (bufferTape c.output) 0 c.workTapes c.workTapePos [] := by
  have hstep : (clockTM K W).tm.step (kCfg K W c) =
      cScanCfg K W c.output c.inputPos c.workTapes c.workTapePos c.output.length := by
    rw [clockTM_step_some K W _ (.kRun none) (by simp [kCfg, hs])]
    simp only [clockTr]
    have he : kCfg K W c = ctrCfg K W (some (.kRun none))
        ⟨none, c.inputPos, fun _ _ => none, fun _ => 0, []⟩ (bufferTape c.output)
        c.output.length c.workTapes c.workTapePos [] := by
      refine Cfg.ext (by simp [kCfg, ctrCfg, hs]) rfl rfl rfl rfl
    rw [he, ctrAction_apply]
    simp only [cScanCfg]
    congr 1
  rw [show c.output.length + 2 = (c.output.length + 1) + 1 by omega,
    MultiTapeTM.runFrom_succ_eq_step, hstep]
  exact cScanCfg_run K W c.output c.inputPos c.workTapes c.workTapePos _ (le_refl _)

/-- **Setup.** If `K` halts on `x` with output `s` within `tK` steps, the runner
reaches the loop entry — state `dec q₀ empty`, counter word `s` with its head on cell
`0`, and `W`'s initial configuration in the right block — within
`tK + |s| + |x| + 5` steps.

**Proof sketch.** Run the budget phase to `K`'s first halting time (lockstep,
`kCfg_run`), identify the counter word with `s` by determinism, rewind the counter in
`|s| + 2` steps (`kCfg_rewind`), and rewind the input in at most `|x| + 3` steps
(`Turing.FinTM.timed_rewind`, whose end configuration is the loop entry since the
right block was never touched). -/
lemma clockTM_setup (x s : List Bool) (tK : ℕ) (hK : K.ComputesInTime x s tK) :
    ∃ (a : ℕ) (kt : Fin K.k → ℤ → Option Bool) (kh : Fin K.k → ℤ),
      a ≤ tK + s.length + x.length + 5 ∧
      (clockTM K W).tm.runFrom ((clockTM K W).tm.initCfg x) a =
        ctrCfg K W (some (.dec W.tm.q₀ .empty)) (W.tm.initCfg x) (bufferTape s) 0 kt kh [] := by
  classical
  have hh : ∃ t, (K.tm.runFrom (K.tm.initCfg x) t).state = none :=
    ⟨tK, ((computesInTime_iff K x s tK).mp hK).1⟩
  let t := Nat.find hh
  let c := K.tm.runFrom (K.tm.initCfg x) t
  have hs : c.state = none := Nat.find_spec hh
  have ht : t ≤ tK := Nat.find_min' hh ((computesInTime_iff K x s tK).mp hK).1
  have hc : K.ComputesInTime x c.output t := (computesInTime_iff _ _ _ _).mpr ⟨hs, rfl⟩
  have ho : c.output = s := hc.output_unique hK
  -- the input rewind
  let start := ctrCfg K W (some .iStart) ⟨none, c.inputPos, fun _ _ => none, fun _ => 0, []⟩
    (bufferTape c.output) 0 c.workTapes c.workTapePos []
  obtain ⟨r, hr, hrun⟩ := timed_rewind (clockTM K W).tm ClockState.iStart ClockState.iScan
    (some (.dec W.tm.q₀ .empty)) (fun _ _ => rfl) (fun inp _ => by cases inp <;> rfl)
    start rfl
  refine ⟨t + (c.output.length + 2) + r, c.workTapes, c.workTapePos, ?_, ?_⟩
  · have hp : start.inputPos.val ≤ x.length + 1 := by
      have := start.inputPos.isLt
      omega
    rw [ho] at *
    omega
  · rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add, kCfg_init,
      kCfg_run K W _ t (fun s hs => Nat.find_min hh hs), kCfg_rewind K W c hs, hrun, ← ho]
    rfl

end Complexity.TimeHierarchy

```


## ===== TCSlib/Complexity/TimeHierarchy/ClockLoop.lean =====

```
/-
Copyright (c) 2026 Hydroxyi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.TimeHierarchy.ClockMachine

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The clocked runner: the loop and its specification

The loop phase of `Complexity.TimeHierarchy.clockTM` (see
`TCSlib.Complexity.TimeHierarchy.ClockMachine` for the machine), and the runner's
specification: on input `x`, with budget word `s = K(x)`, the runner halts within
`t_K + 4|s| + |x| + 4·val(s) + 6` steps and outputs `[b]` with `b = true` exactly when
`W` does **not** halt on `x` with completed output `[true]` within `val(s)` steps.
[AB09, Theorem 3.1, proof: "`D` runs `M_x` for `g(|x|)` steps".]

## Design

* **Amortized decrement cost.** One loop iteration on the counter word
  `0^j 1 r` costs `2j + 2` steps (the borrow sweep over `j` zeros, the fused
  simulation step, and the return sweep) and produces `1^j 0 r`. With the potential
  `B(s) = 4·val(s) + 2·(|s| - pop(s)) + |s| + 1` this cost is exactly
  `B(s) - B(s')`, so the whole loop costs at most `B(s) ≤ 4·val(s) + 3|s| + 1`: a
  budget of `v` simulated steps costs `O(v + log v)` runner steps, matching the
  book's "`D` runs in time `O(g(n))`" up to the constant.

## Main results

* `Complexity.TimeHierarchy.clockTM_loop` — the loop invariant (strong induction on
  the counter value).
* `Complexity.TimeHierarchy.clockTM_spec` — the clocked runner's specification.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.1, Theorem 3.1 and its proof, p. 69.)
-/

namespace Complexity.TimeHierarchy

open Turing Turing.FinTM

/-- Overwriting the cell at index `|l|` of a stored word replaces that letter. -/
lemma bufferTape_update_mid (l m : List Bool) (a b : Bool) :
    Function.update (bufferTape (l ++ a :: m)) (l.length : ℤ) (some b) =
      bufferTape (l ++ b :: m) := by
  funext z
  by_cases hz : z = l.length
  · subst hz
    simp [bufferTape]
  · rw [Function.update_of_ne hz]
    simp only [bufferTape]
    split_ifs with h0
    · have hne : z.toNat ≠ l.length := by omega
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · rw [List.getElem?_append_left hlt, List.getElem?_append_left hlt]
      · rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
        obtain ⟨d, hd⟩ : ∃ d, z.toNat - l.length = d + 1 := ⟨z.toNat - l.length - 1, by omega⟩
        rw [hd]
        simp
    · rfl

variable (K W : FinTM Bool)

/-- The borrow sweep over `j` zero bits: each is overwritten with a one, the head
advancing; exactly `j` steps.

**Proof sketch.** Induction on `j`, generalizing the head position `i`. In the
successor case the head reads the `false` at cell `i`; one step of the decrement
state overwrites it with `true` and moves right, which turns the buffer
`1^i 0^(j+1) rest` into `1^(i+1) 0^j rest` with the head at `i + 1`. The induction
hypothesis at `i + 1` finishes the remaining `j` steps, and `i + 1 + j = i + (j + 1)`. -/
lemma borrow_run {x : List Bool} (c : Cfg W.k Bool W.State x) (q : W.State) (r : OutReg)
    (kt : Fin K.k → ℤ → Option Bool) (kh : Fin K.k → ℤ) (rest : List Bool) :
    ∀ j i, (clockTM K W).tm.runFrom
      (ctrCfg K W (some (.dec q r)) c
        (bufferTape (List.replicate i true ++ List.replicate j false ++ rest)) i kt kh []) j =
      ctrCfg K W (some (.dec q r)) c
        (bufferTape (List.replicate (i + j) true ++ rest)) (i + j) kt kh [] := by
  intro j
  induction j with
  | zero => intro i; simp
  | succ j ih =>
    intro i
    have hread : bufferTape (List.replicate i true ++ List.replicate (j + 1) false ++ rest)
        (i : ℤ) = some false := by
      rw [bufferTape_nat]
      simp [List.replicate_succ]
    have hstep : (clockTM K W).tm.step (ctrCfg K W (some (.dec q r)) c
        (bufferTape (List.replicate i true ++ List.replicate (j + 1) false ++ rest)) i kt kh []) =
        ctrCfg K W (some (.dec q r)) c
          (bufferTape (List.replicate (i + 1) true ++ List.replicate j false ++ rest))
          ((i + 1 : ℕ) : ℤ) kt kh [] := by
      rw [clockTM_step_some K W _ (.dec q r) rfl]
      simp only [clockTr, ctrCfg_ctr, hread]
      rw [ctrAction_apply]
      have hl : List.replicate i true ++ List.replicate (j + 1) false ++ rest =
          List.replicate i true ++ false :: (List.replicate j false ++ rest) := by
        simp [List.replicate_succ]
      have hl' : List.replicate (i + 1) true ++ List.replicate j false ++ rest =
          List.replicate i true ++ true :: (List.replicate j false ++ rest) := by
        simp [List.replicate_succ', List.append_assoc]
      have hu := bufferTape_update_mid (List.replicate i true)
        (List.replicate j false ++ rest) false true
      simp only [List.length_replicate] at hu
      simp only [hl, hl', hu]
      congr 1
    rw [MultiTapeTM.runFrom_succ_eq_step, hstep, ih (i + 1)]
    rw [show i + 1 + j = i + (j + 1) by omega]
    congr 1
    push_cast
    ring

/-- The return sweep: from cell `j - 1` over `j` stored cells to the left blank at
cell `-1` and back to cell `0`; exactly `j + 1` steps, ending in the decrement state.

**Proof sketch.** Induction on `j`. For `j = 0` the head sits at cell `-1`, which is
blank, so a single step of the return state turns around to cell `0` and enters the
decrement state. For `j + 1` the head at cell `j` reads a stored (non-blank) cell,
so one step moves left to cell `j - 1` staying in the return state; the induction
hypothesis (whose non-blank hypothesis is inherited) supplies the remaining
`j + 1` steps. -/
lemma ret_run {x : List Bool} (c : Cfg W.k Bool W.State x) (q : W.State) (r : OutReg)
    (kt : Fin K.k → ℤ → Option Bool) (kh : Fin K.k → ℤ) (τ : ℤ → Option Bool)
    (hneg : τ (-1) = none) : ∀ j, (∀ i : ℕ, i < j → τ i ≠ none) →
    (clockTM K W).tm.runFrom (ctrCfg K W (some (.ret q r)) c τ ((j : ℤ) - 1) kt kh []) (j + 1) =
      ctrCfg K W (some (.dec q r)) c τ 0 kt kh [] := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero,
      clockTM_step_some K W _ (.ret q r) rfl]
    simp only [clockTr, ctrCfg_ctr, Nat.cast_zero, zero_sub, hneg, if_true]
    rw [ctrAction_apply]
    simp
  | succ j ih =>
    intro hj
    have hread : τ (((j + 1 : ℕ) : ℤ) - 1) ≠ none := by
      rw [show (((j + 1 : ℕ) : ℤ) - 1) = (j : ℤ) by omega]
      exact hj j (by omega)
    have hstep : (clockTM K W).tm.step
        (ctrCfg K W (some (.ret q r)) c τ (((j + 1 : ℕ) : ℤ) - 1) kt kh []) =
        ctrCfg K W (some (.ret q r)) c τ ((j : ℤ) - 1) kt kh [] := by
      rw [clockTM_step_some K W _ (.ret q r) rfl]
      simp only [clockTr, ctrCfg_ctr, hread, if_false]
      rw [ctrAction_apply]
      congr 1
      push_cast
      simp [SignType.neg_eq_neg_one]
      ring
    rw [MultiTapeTM.runFrom_succ_eq_step, hstep]
    exact ih (fun i hi => hj i (by omega))

/-- The fused simulation step: on reading the low `true` bit, the runner writes `false`,
moves the counter head left, applies `W`'s transition `a` to the right block and the
input head, and either continues in the return state (with the register updated by
`a`'s emission) or — if `a` halts `W` — halts, emitting whether the final summary
differs from `one true`.

**Proof sketch.** Since `W` is in the live state `q`, its step is the application of
its transition action `a` to `c`. Unfolding one step of the clock machine in the
decrement state on a `true` bit, the transition is the fused action; after
generalizing `a`, the two configurations are compared componentwise: the state and
output agree by construction, and the tape contents and head positions agree on
each block of tapes (input, counter, `K`'s tapes, `W`'s tapes) by unfolding the
action application, splitting on whether `a` halts. -/
lemma wstep {x : List Bool} (c : Cfg W.k Bool W.State x) (q : W.State) (r : OutReg)
    (hq : c.state = some q) (kt : Fin K.k → ℤ → Option Bool) (kh : Fin K.k → ℤ)
    (τ : ℤ → Option Bool) (z : ℤ) (hτ : τ z = some true) :
    (clockTM K W).tm.step (ctrCfg K W (some (.dec q r)) c τ z kt kh []) =
      ctrCfg K W ((W.tm.tr q c.inputSymbol c.workTapeSymbols).state.map
          (fun q' => .ret q' (r.push (W.tm.tr q c.inputSymbol c.workTapeSymbols).output)))
        (W.tm.step c) (Function.update τ z (some false)) (z - 1) kt kh
        (if (W.tm.tr q c.inputSymbol c.workTapeSymbols).state = none then
          [decide (r.push (W.tm.tr q c.inputSymbol c.workTapeSymbols).output ≠ .one true)]
        else []) := by
  have hW : W.tm.step c = (W.tm.tr q c.inputSymbol c.workTapeSymbols).apply c := by
    unfold MultiTapeTM.step; rw [hq]
  rw [clockTM_step_some K W _ (.dec q r) rfl, hW]
  simp only [clockTr, ctrCfg_ctr, hτ, ctrCfg_right]
  have hi : (ctrCfg K W (some (.dec q r)) c τ z kt kh []).inputSymbol = c.inputSymbol := rfl
  rw [hi]
  generalize W.tm.tr q c.inputSymbol c.workTapeSymbols = a
  refine Cfg.ext rfl rfl ?_ ?_ ?_
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [ctrCfg, Action.apply]
    · intro j
      refine Fin.addCases ?_ ?_ j <;> intro j <;> simp [ctrCfg, Action.apply]
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [ctrCfg, Action.apply]
    · intro j
      refine Fin.addCases ?_ ?_ j <;> intro j <;>
        simp [ctrCfg, Action.apply, SignType.neg_eq_neg_one, sub_eq_add_neg]
  · cases h : a.state <;> simp [ctrCfg, Action.apply, h]

/-- Underflow: reading a blank in the decrement state emits `true` and halts. -/
lemma underflow_step {x : List Bool} (c : Cfg W.k Bool W.State x) (q : W.State) (r : OutReg)
    (kt : Fin K.k → ℤ → Option Bool) (kh : Fin K.k → ℤ)
    (τ : ℤ → Option Bool) (z : ℤ) (hτ : τ z = none) :
    ((clockTM K W).tm.step (ctrCfg K W (some (.dec q r)) c τ z kt kh [])).state = none ∧
      ((clockTM K W).tm.step (ctrCfg K W (some (.dec q r)) c τ z kt kh [])).output = [true] := by
  rw [clockTM_step_some K W _ (.dec q r) rfl]
  simp only [clockTr, ctrCfg_ctr, hτ]
  simp [ctrCfg, Action.apply]

/-- The amortization potential of a counter word. -/
def ctrBound (s : List Bool) : ℕ := 4 * ctrVal s + 2 * (s.length - ctrPop s) + s.length + 1

/-- The answer of the loop started from `W`-configuration `c` with budget `v`:
`true` unless `W`, run `v` steps from `c`, has halted with output `[true]`. -/
def loopAnswer {x : List Bool} (c : Cfg W.k Bool W.State x) (v : ℕ) : Bool :=
  !(decide ((W.tm.runFrom c v).state = none ∧ (W.tm.runFrom c v).output = [true]))

/-- **The loop invariant.** From the loop entry with live simulated configuration `c`
(register = summary of `c`'s output) and counter word `s` (head on cell `0`), the runner
halts within `ctrBound s` steps with output `[loopAnswer c (val s)]`.

**Proof sketch.** Strong induction on `val s`. At value zero, `s` is all zeros: the
borrow sweep runs off the word in `|s|` steps and the runner emits `true` (the
simulated machine is live, so the answer is `true`). At positive value write
`s = 0^j 1 r`: sweep `j` zeros (`borrow_run`), then fuse one simulation step
(`wstep`). If that step halts `W`, the runner emits the correct answer at once (the
run from `c` for `val s` steps is absorbed at the halting configuration). Otherwise
return to cell `0` in `j + 1` steps (`ret_run`) with counter `1^j 0 r` of value
`val s - 1` and apply the induction hypothesis; the costs `2j + 2` are absorbed by
the potential drop `ctrBound s - ctrBound s' = 2j + 2`. -/
theorem clockTM_loop {x : List Bool} (kt : Fin K.k → ℤ → Option Bool) (kh : Fin K.k → ℤ)
    (s : List Bool) (c : Cfg W.k Bool W.State x) (q : W.State) (hq : c.state = some q) :
    ∃ t ≤ ctrBound s,
      ((clockTM K W).tm.runFrom
        (ctrCfg K W (some (.dec q (OutReg.ofList c.output))) c (bufferTape s) 0 kt kh []) t).state
          = none ∧
      ((clockTM K W).tm.runFrom
        (ctrCfg K W (some (.dec q (OutReg.ofList c.output))) c (bufferTape s) 0 kt kh []) t).output
          = [loopAnswer W c (ctrVal s)] := by
  obtain ⟨n, hn⟩ : ∃ n, ctrVal s = n := ⟨_, rfl⟩
  induction n generalizing s c q with
  | zero =>
    have hs := ctrVal_zero_eq s hn
    have hb := borrow_run K W c q (OutReg.ofList c.output) kt kh [] s.length 0
    simp only [List.replicate_zero, List.nil_append, List.append_nil, zero_add, Nat.cast_zero] at hb
    rw [← hs] at hb
    have hτ : bufferTape (List.replicate s.length true) (s.length : ℤ) = none := by
      rw [bufferTape_nat]; simp
    obtain ⟨h1, h2⟩ := underflow_step K W c q (OutReg.ofList c.output) kt kh _ _ hτ
    refine ⟨s.length + 1, by unfold ctrBound; omega, ?_, ?_⟩
    · rw [MultiTapeTM.runFrom_succ_eq_step', hb]; exact h1
    · rw [MultiTapeTM.runFrom_succ_eq_step', hb, h2, hn]
      simp [loopAnswer, hq]
  | succ n ih =>
    obtain ⟨j, rest, rfl⟩ := ctrVal_pos_decomp s (by omega)
    have hb := borrow_run K W c q (OutReg.ofList c.output) kt kh (true :: rest) j 0
    simp only [List.replicate_zero, List.nil_append, zero_add, Nat.cast_zero] at hb
    have hτ : bufferTape (List.replicate j true ++ true :: rest) (j : ℤ) = some true := by
      rw [bufferTape_nat]; simp
    have hw := wstep K W c q (OutReg.ofList c.output) hq kt kh _ _ hτ
    have hu := bufferTape_update_mid (List.replicate j true) rest true false
    simp only [List.length_replicate] at hu
    rw [hu] at hw
    have hreg : (OutReg.ofList c.output).push (W.tm.tr q c.inputSymbol c.workTapeSymbols).output =
        OutReg.ofList (W.tm.step c).output := by
      have hW : W.tm.step c = (W.tm.tr q c.inputSymbol c.workTapeSymbols).apply c := by
        unfold MultiTapeTM.step; rw [hq]
      rw [hW, ← OutReg.ofList_push]
      rfl
    have hstate : (W.tm.step c).state = (W.tm.tr q c.inputSymbol c.workTapeSymbols).state := by
      unfold MultiTapeTM.step; rw [hq]; rfl
    have hans : loopAnswer W c (n + 1) = loopAnswer W (W.tm.step c) n := by
      simp only [loopAnswer, MultiTapeTM.runFrom_succ_eq_step]
    have hlen : ctrPop rest ≤ rest.length := ctrPop_le_length rest
    have hpop1 := ctrPop_replicate j false (true :: rest)
    have hpop2 := ctrPop_replicate j true (false :: rest)
    simp only [ctrPop, if_true, Bool.false_eq_true, if_false] at hpop1 hpop2
    have hval := ctrVal_borrow j rest
    cases ha : (W.tm.tr q c.inputSymbol c.workTapeSymbols).state with
    | none =>
      -- the simulated machine halts on this step
      rw [ha] at hw
      simp only [Option.map_none, if_true] at hw
      refine ⟨j + 1, ?_, ?_, ?_⟩
      · unfold ctrBound; simp only [List.length_append, List.length_replicate,
          List.length_cons]; omega
      · rw [MultiTapeTM.runFrom_succ_eq_step', hb, hw]; rfl
      · rw [MultiTapeTM.runFrom_succ_eq_step', hb, hw]
        change [decide (_ ≠ _)] = _
        rw [hn, hans, hreg]
        have hh : (W.tm.step c).state = none := by rw [hstate, ha]
        simp only [loopAnswer, MultiTapeTM.runFrom_of_halt _ hh, hh, true_and]
        simp [OutReg.ofList_eq_one_true]
    | some q' =>
      rw [ha] at hw
      simp only [Option.map_some, reduceCtorEq, if_false] at hw
      rw [hreg] at hw
      have hr := ret_run K W (W.tm.step c) q' (OutReg.ofList (W.tm.step c).output) kt kh
        (bufferTape (List.replicate j true ++ false :: rest)) (bufferTape_left _) j
        (fun i hi => by
          rw [bufferTape_nat]
          rw [List.getElem?_append_left (by simpa using hi)]
          simp [hi])
      have hlive : (W.tm.step c).state = some q' := by rw [hstate, ha]
      obtain ⟨t', ht', h1, h2⟩ := ih (List.replicate j true ++ false :: rest) (W.tm.step c) q'
        hlive (by omega)
      have hrun : (clockTM K W).tm.runFrom
          (ctrCfg K W (some (.dec q (OutReg.ofList c.output))) c
            (bufferTape (List.replicate j false ++ true :: rest)) 0 kt kh [])
          (j + 1 + (j + 1)) =
          ctrCfg K W (some (.dec q' (OutReg.ofList (W.tm.step c).output))) (W.tm.step c)
            (bufferTape (List.replicate j true ++ false :: rest)) 0 kt kh [] := by
        have h1step : (clockTM K W).tm.runFrom
            (ctrCfg K W (some (.dec q (OutReg.ofList c.output))) c
              (bufferTape (List.replicate j false ++ true :: rest)) 0 kt kh []) (j + 1) =
            ctrCfg K W (some (.ret q' (OutReg.ofList (W.tm.step c).output))) (W.tm.step c)
              (bufferTape (List.replicate j true ++ false :: rest)) ((j : ℤ) - 1) kt kh [] := by
          rw [MultiTapeTM.runFrom_succ_eq_step', hb, hw]
        rw [MultiTapeTM.runFrom_add, h1step]
        exact hr
      refine ⟨j + 1 + (j + 1) + t', ?_, ?_, ?_⟩
      · unfold ctrBound at ht' ⊢
        simp only [List.length_append, List.length_replicate, List.length_cons] at ht' ⊢
        omega
      · rw [MultiTapeTM.runFrom_add, hrun]; exact h1
      · rw [MultiTapeTM.runFrom_add, hrun, h2, hn, hans]
        congr 2
        omega

open Classical in
/-- **Specification of the clocked runner** [AB09, Theorem 3.1, proof]. If the budget
machine `K` halts on `x` with output `s` within `tK` steps, then `clockTM K W` halts on
`x` within `tK + 4|s| + |x| + 4·val(s) + 6` steps with output `[b]`, where `b = true`
iff `W` does **not** compute `[true]` on `x` within `val(s)` steps.

**Proof sketch.** `clockTM_setup` reaches the loop entry with counter `s` and `W`'s
initial configuration within `tK + |s| + |x| + 5` steps; `clockTM_loop` finishes within
`ctrBound s ≤ 4·val(s) + 3|s| + 1` further steps with the answer
`loopAnswer (W.init x) (val s)`, which is the stated Boolean by
`Turing.FinTM.computesInTime_iff`. -/
theorem clockTM_spec (x s : List Bool) (tK : ℕ) (hK : K.ComputesInTime x s tK) :
    (clockTM K W).ComputesInTime x [!(decide (W.ComputesInTime x [true] (ctrVal s)))]
      (tK + 4 * s.length + x.length + 4 * ctrVal s + 6) := by
  obtain ⟨a, kt, kh, ha, hsetup⟩ := clockTM_setup K W x s tK hK
  obtain ⟨t, ht, h1, h2⟩ := clockTM_loop K W kt kh s (W.tm.initCfg x) W.tm.q₀ rfl
  have hreg : OutReg.ofList (W.tm.initCfg x).output = .empty := rfl
  rw [hreg] at h1 h2
  have hc : (clockTM K W).ComputesInTime x [!(decide (W.ComputesInTime x [true] (ctrVal s)))]
      (a + t) := by
    rw [computesInTime_iff, MultiTapeTM.runFrom_add, hsetup]
    refine ⟨h1, ?_⟩
    rw [h2]
    by_cases h : W.ComputesInTime x [true] (ctrVal s)
    · have h' := (computesInTime_iff W x [true] (ctrVal s)).mp h
      simp only [loopAnswer, h, h'.1, h'.2, and_self, decide_true]
    · have h' : ¬((W.tm.runFrom (W.tm.initCfg x) (ctrVal s)).state = none ∧
          (W.tm.runFrom (W.tm.initCfg x) (ctrVal s)).output = [true]) :=
        fun hh => h ((computesInTime_iff W x [true] (ctrVal s)).mpr hh)
      simp only [loopAnswer, h, h', decide_false]
  apply hc.mono
  have hb : ctrBound s ≤ 4 * ctrVal s + 3 * s.length + 1 := by
    unfold ctrBound; omega
  omega

end Complexity.TimeHierarchy

```


## ===== TCSlib/Complexity/TimeHierarchy/CodePrefix.lean =====

```
/-
Copyright (c) 2026 Hydroxyi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Tactic.DeriveFintype
import TCSlib.Complexity.TuringMachine.Encoding
import TCSlib.Complexity.TuringMachine.Simulation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Code-prefix duplication

Glue for the diagonal machine of the time hierarchy theorem
[AB09, Theorem 3.1, proof].

* **Code-prefix duplication.** The universal machine of this development
  (`Turing.universal`) reads its input as `pairEncode α x` — code first. The diagonal
  machine must run the machine coded in its input *on that same input*. On an input
  of the shape `x = pairEncode α w` this is `pairEncode α x`, which is the aligned
  doubled-bit prefix of `x` (up to and including the separator) followed by all of
  `x`. The machine `preTM` computes `x ↦ scanPre x ++ x` in linear time, where
  `scanPre` is that prefix (`scanPre_pairEncode`).
* **Timed partial composition** is `Turing.FinTM.bufferedCompTM_computesInTime`
  (`TCSlib.Complexity.TuringMachine.Composition`).

## Design

* Fixing the code `α` and padding the *input* (rather than taking ever longer codes of
  the same machine, as [AB09] does via "every machine has infinitely many codes") is
  forced here: the universal machine's constant depends on the code string itself,
  with no uniform bound in its length (see `Turing.universal`), so the diagonal
  argument must simulate one fixed code on longer and longer inputs.

## Main definitions

* `Complexity.TimeHierarchy.scanPre` — the aligned doubled-bit prefix of a word.
* `Complexity.TimeHierarchy.preTM` — the prefix-duplication machine.

## Main results

* `Complexity.TimeHierarchy.preTM_computes` — `preTM` computes `x ↦ scanPre x ++ x`
  within `3|x| + 5` steps.
* `Complexity.TimeHierarchy.scanPre_pairEncode_append` — on `pairEncode α w` the
  computed word is `pairEncode α (pairEncode α w)`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4, §3.1.)
-/

namespace Complexity.TimeHierarchy

open Turing Turing.FinTM

/-- The aligned doubled-bit prefix of a word: read aligned pairs, keep them while
they are `00` or `11`, and stop after (and including) the first other pair; a final
unpaired bit is kept. On `pairEncode α w` this is the doubled `α` and the separator. -/
def scanPre : List Bool → List Bool
  | [] => []
  | [b] => [b]
  | b :: b' :: r => b :: b' :: (if b = b' then scanPre r else [])

/-- On a code-first pair, the scanned prefix is the doubled code and the separator. -/
lemma scanPre_pairEncode (α w : List Bool) :
    scanPre (pairEncode α w) = (α.flatMap fun b => [b, b]) ++ [false, true] := by
  induction α with
  | nil => simp [pairEncode, scanPre]
  | cons b α ih =>
    simp only [pairEncode, List.flatMap_cons, List.cons_append, List.nil_append,
      List.append_assoc] at ih ⊢
    simp only [scanPre, if_true]
    rw [ih]

/-- **Prefix duplication on code-first pairs:** `scanPre x ++ x = pairEncode α x` for
`x = pairEncode α w`. -/
lemma scanPre_pairEncode_append (α w : List Bool) :
    scanPre (pairEncode α w) ++ pairEncode α w = pairEncode α (pairEncode α w) := by
  rw [scanPre_pairEncode]
  simp [pairEncode]

/-- Control states of the prefix-duplication machine. -/
inductive PreState where
  | scan0 : PreState
  | scan1 : Bool → PreState
  | rwStart : PreState
  | rwScan : PreState
  | copy : PreState
  deriving DecidableEq, Fintype

/-- Transition table of the prefix-duplication machine (no work tapes): scan and emit
aligned pairs while they are doubled bits, rewind the input head, then copy the
whole input to the output. -/
def preTr (q : PreState) (inp : Option Bool) (_work : Fin 0 → Option Bool) :
    Action 0 Bool PreState :=
  match q, inp with
  | .scan0, some b => ⟨.pos, fun _ => (none, 0), some b, some (.scan1 b)⟩
  | .scan0, none => controlAction 0 (some .rwStart)
  | .scan1 b, some b' =>
    ⟨.pos, fun _ => (none, 0), some b', some (if b = b' then .scan0 else .rwStart)⟩
  | .scan1 _, none => controlAction 0 (some .rwStart)
  | .rwStart, _ => controlAction .neg (some .rwScan)
  | .rwScan, some _ => controlAction .neg (some .rwScan)
  | .rwScan, none => controlAction .pos (some .copy)
  | .copy, some b => ⟨.pos, fun _ => (none, 0), some b, some .copy⟩
  | .copy, none => ⟨0, fun _ => (none, 0), none, none⟩

/-- **The prefix-duplication machine**: on input `x` it outputs `scanPre x ++ x`. -/
def preTM : FinTM Bool where
  k := 0
  State := PreState
  tm := { q₀ := .scan0, tr := preTr }

/-- One live step applies the table. -/
private lemma preTM_step {x : List Bool} (c : Cfg 0 Bool PreState x) (q : PreState)
    (h : c.state = some q) :
    preTM.tm.step c = (preTr q c.inputSymbol c.workTapeSymbols).apply c := by
  unfold MultiTapeTM.step
  rw [h]
  rfl

/-- The scanning phase: from input position `i + 1` with `drop i x = rest`, the
machine reaches the rewind state within `|rest| + 1` steps, having appended
`scanPre rest`.

**Proof sketch.** Strong recursion on `rest`, two symbols at a time. If `rest` is
empty, the head reads a blank and one step enters the rewind state, emitting nothing
new. If `rest = [b]`, two steps read `b`, then a blank, and enter the rewind state
having emitted what `scanPre [b]` prescribes. If `rest = b :: b' :: r`, two steps read
the pair and emit `b, b'`; when `b = b'` the machine is back in the scanning state two
cells further on, and the recursive call on `r` gives the rest of the run (with step
count `2 + t ≤ |rest| + 1`); when `b ≠ b'` the pair is the terminator of the prefix and
the machine is already in the rewind state after two steps. -/
private theorem pre_scan (x : List Bool) : ∀ (rest : List Bool) (i : ℕ)
    (c : Cfg 0 Bool PreState x), x.drop i = rest → i ≤ x.length →
    c.state = some .scan0 → c.inputPos.val = i + 1 →
    ∃ t ≤ rest.length + 1, (preTM.tm.runFrom c t).state = some .rwStart ∧
      (preTM.tm.runFrom c t).output = c.output ++ scanPre rest
  | [], i, c, hd, hi, hs, hp => by
    have hin : c.inputSymbol = none := by
      rw [inputSymbol_at c i hi hp, ← List.head?_drop, hd]; rfl
    refine ⟨1, le_refl _, ?_, ?_⟩
    · change (preTM.tm.step c).state = _
      rw [preTM_step c _ hs, hin]; rfl
    · change (preTM.tm.step c).output = _
      rw [preTM_step c _ hs, hin]; simp [preTr, controlAction, scanPre]
  | [b], i, c, hd, hi, hs, hp => by
    have hlt : i < x.length := by
      have := congrArg List.length hd; simp at this; omega
    have hin : c.inputSymbol = some b := by
      rw [inputSymbol_at c i hi hp, ← List.head?_drop, hd]; rfl
    let c1 := preTM.tm.step c
    have hc1 : c1 = (preTr .scan0 (some b) c.workTapeSymbols).apply c := by
      simp only [c1]; rw [preTM_step c _ hs, hin]
    have hp1 : c1.inputPos.val = (i + 1) + 1 := by
      rw [hc1]; simp only [preTr, Action.apply]
      rw [moveInputPos_pos_of_ne_right _ (by omega)]; simp [hp]
    have hin1 : c1.inputSymbol = none := by
      rw [inputSymbol_at c1 (i + 1) (by omega) hp1, ← List.head?_drop]
      have : x.drop (i + 1) = [] := by rw [← List.drop_drop, hd]; rfl
      rw [this]; rfl
    have hs1 : c1.state = some (.scan1 b) := by rw [hc1]; rfl
    refine ⟨2, le_refl _, ?_, ?_⟩
    · change (preTM.tm.step c1).state = _
      rw [preTM_step c1 _ hs1, hin1]; rfl
    · change (preTM.tm.step c1).output = _
      rw [preTM_step c1 _ hs1, hin1, hc1]
      simp [preTr, controlAction, scanPre]
  | b :: b' :: r, i, c, hd, hi, hs, hp => by
    have hlt : i + 1 < x.length := by
      have := congrArg List.length hd; simp at this; omega
    have hin : c.inputSymbol = some b := by
      rw [inputSymbol_at c i hi hp, ← List.head?_drop, hd]; rfl
    let c1 := preTM.tm.step c
    have hc1 : c1 = (preTr .scan0 (some b) c.workTapeSymbols).apply c := by
      simp only [c1]; rw [preTM_step c _ hs, hin]
    have hp1 : c1.inputPos.val = (i + 1) + 1 := by
      rw [hc1]; simp only [preTr, Action.apply]
      rw [moveInputPos_pos_of_ne_right _ (by omega)]; simp [hp]
    have hd1 : x.drop (i + 1) = b' :: r := by rw [← List.drop_drop, hd]; rfl
    have hin1 : c1.inputSymbol = some b' := by
      rw [inputSymbol_at c1 (i + 1) (by omega) hp1, ← List.head?_drop, hd1]; rfl
    have hs1 : c1.state = some (.scan1 b) := by rw [hc1]; rfl
    let c2 := preTM.tm.step c1
    have hc2 : c2 = (preTr (.scan1 b) (some b') c1.workTapeSymbols).apply c1 := by
      simp only [c2]; rw [preTM_step c1 _ hs1, hin1]
    have hp2 : c2.inputPos.val = (i + 2) + 1 := by
      rw [hc2]; simp only [preTr, Action.apply]
      rw [moveInputPos_pos_of_ne_right _ (by omega)]; simp [hp1]
    have hout2 : c2.output = c.output ++ [b, b'] := by
      rw [hc2, hc1]; simp [preTr]
    have hrun2 : preTM.tm.runFrom c 2 = c2 := rfl
    by_cases hbb : b = b'
    · have hs2 : c2.state = some .scan0 := by rw [hc2]; simp [preTr, hbb]
      have hd2 : x.drop (i + 2) = r := by rw [← List.drop_drop, hd]; rfl
      obtain ⟨t, ht, h1, h2⟩ := pre_scan x r (i + 2) c2 hd2 (by omega) hs2 hp2
      refine ⟨2 + t, by simp; omega, ?_, ?_⟩
      · rw [MultiTapeTM.runFrom_add, hrun2]; exact h1
      · rw [MultiTapeTM.runFrom_add, hrun2, h2, hout2]
        simp [scanPre, hbb]
    · have hs2 : c2.state = some .rwStart := by rw [hc2]; simp [preTr, hbb]
      refine ⟨2, by simp, ?_, ?_⟩
      · rw [hrun2]; exact hs2
      · rw [hrun2, hout2]; simp [scanPre, hbb]

/-- The copying phase: from input position `i + 1` with `drop i x = rest`, the machine
halts after exactly `|rest| + 1` steps, having appended `rest`.

**Proof sketch.** Recursion on `rest`. On an empty remainder the head reads a blank
and the machine halts in one step without output. On `b :: r` one step copies `b` to
the output and advances the input head, staying in the copy state; the recursive call
on `r` from position `i + 2` accounts for the remaining `|r| + 1` steps. -/
private theorem pre_copy (x : List Bool) : ∀ (rest : List Bool) (i : ℕ)
    (c : Cfg 0 Bool PreState x), x.drop i = rest → i ≤ x.length →
    c.state = some .copy → c.inputPos.val = i + 1 →
    (preTM.tm.runFrom c (rest.length + 1)).state = none ∧
      (preTM.tm.runFrom c (rest.length + 1)).output = c.output ++ rest
  | [], i, c, hd, hi, hs, hp => by
    have hin : c.inputSymbol = none := by
      rw [inputSymbol_at c i hi hp, ← List.head?_drop, hd]; rfl
    change (preTM.tm.step c).state = none ∧ (preTM.tm.step c).output = _
    rw [preTM_step c _ hs, hin]
    simp [preTr]
  | b :: r, i, c, hd, hi, hs, hp => by
    have hlt : i < x.length := by
      have := congrArg List.length hd; simp at this; omega
    have hin : c.inputSymbol = some b := by
      rw [inputSymbol_at c i hi hp, ← List.head?_drop, hd]; rfl
    let c1 := preTM.tm.step c
    have hc1 : c1 = (preTr .copy (some b) c.workTapeSymbols).apply c := by
      simp only [c1]; rw [preTM_step c _ hs, hin]
    have hp1 : c1.inputPos.val = (i + 1) + 1 := by
      rw [hc1]; simp only [preTr, Action.apply]
      rw [moveInputPos_pos_of_ne_right _ (by omega)]; simp [hp]
    have hd1 : x.drop (i + 1) = r := by rw [← List.drop_drop, hd]; rfl
    have hs1 : c1.state = some .copy := by rw [hc1]; rfl
    obtain ⟨h1, h2⟩ := pre_copy x r (i + 1) c1 hd1 (by omega) hs1 hp1
    have hrun : preTM.tm.runFrom c ((b :: r).length + 1) =
        preTM.tm.runFrom c1 (r.length + 1) := by
      rw [List.length_cons, MultiTapeTM.runFrom_succ_eq_step]
    rw [hrun]
    refine ⟨h1, ?_⟩
    rw [h2, hc1]
    simp [preTr]

/-- **Prefix duplication** [glue for AB09, Theorem 3.1]: `preTM` computes
`x ↦ scanPre x ++ x` within `3|x| + 5` steps.

**Proof sketch.** Scan (`pre_scan`, at most `|x| + 1` steps, emitting `scanPre x`),
rewind the input head (`Turing.FinTM.timed_rewind`, at most `|x| + 3` steps), and copy
(`pre_copy`, exactly `|x| + 1` steps, emitting `x`). -/
theorem preTM_computes (x : List Bool) :
    preTM.ComputesInTime x (scanPre x ++ x) (3 * x.length + 5) := by
  obtain ⟨t₁, ht₁, h1, h2⟩ := pre_scan x x 0 (preTM.tm.initCfg x) (by simp) (by omega) rfl rfl
  let c₁ := preTM.tm.runFrom (preTM.tm.initCfg x) t₁
  obtain ⟨r, hr, hrun⟩ := timed_rewind preTM.tm PreState.rwStart PreState.rwScan
    (some .copy) (fun inp _ => by cases inp <;> rfl) (fun inp _ => by cases inp <;> rfl) c₁ h1
  let c₂ : Cfg 0 Bool PreState x := {c₁ with state := some .copy, inputPos := 1}
  have hc := pre_copy x x 0 c₂ (by simp) (by omega) rfl rfl
  have hrun' : preTM.tm.runFrom (preTM.tm.initCfg x) (t₁ + r + (x.length + 1)) =
      preTM.tm.runFrom c₂ (x.length + 1) := by
    rw [MultiTapeTM.runFrom_add _ (t₁ + r), MultiTapeTM.runFrom_add _ t₁ r]
    change preTM.tm.runFrom (preTM.tm.runFrom c₁ r) _ = _
    rw [hrun]
  have hcomp : preTM.ComputesInTime x (scanPre x ++ x) (t₁ + r + (x.length + 1)) := by
    rw [computesInTime_iff, hrun']
    refine ⟨hc.1, ?_⟩
    rw [hc.2]
    change c₁.output ++ x = _
    rw [h2]
    rfl
  apply hcomp.mono
  have := c₁.inputPos.isLt
  omega

end Complexity.TimeHierarchy

```


## ===== TCSlib/Complexity/TimeHierarchy/Diagonal.lean =====

```
/-
Copyright (c) 2026 Hydroxyi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import TCSlib.Complexity.ClassP.DTIME
import TCSlib.Complexity.ClassP.TimeConstructible
import TCSlib.Complexity.TimeHierarchy.ClockLoop
import TCSlib.Complexity.TimeHierarchy.CodePrefix
import TCSlib.Complexity.TuringMachine.Composition
import TCSlib.Complexity.TuringMachine.MathlibBridge
import TCSlib.Complexity.TuringMachine.Universal

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The Time Hierarchy Theorem

[AB09, Theorem 3.1]: if `f, g` are time-constructible functions with
`f(n) log f(n) = o(g(n))`, then `DTIME(f) ⊊ DTIME(g)`. This file proves the theorem
in the form supported by this development's universal machine:

  if `g` is time constructible and `(f(n) + n + 1)² = o(g(n))`, then
  `DTIME(f) ⊊ DTIME(g + 1)`.

## The diagonal language

Fix the effective representation scheme `code` and the universal machine `univTM`
(`Turing.universal`). The simulator `diagSim` composes the prefix-duplication machine
`preTM` with `univTM`; on an input `x = pairEncode α w` it runs the machine coded by
`α` on `x` itself. The diagonal language is

  `diagLang g = {x | diagSim does not halt on x with output [true] within g(|x|) steps}`,

decided within `O(g(n))` by the clocked runner `clockTM K diagSim`, where `K` is the
time-constructibility witness of `g` (`diagLang_mem_DTIME`). If a machine `M`
decided `diagLang g` within `c·T(n)`, take a code `α` of its one-work-tape normal form
and the inputs `x = pairEncode α 1^m`: the simulation of `M` on `x` finishes within
`A·(T(n) + n + 1)²` steps for a constant `A` depending only on `M`, which is at most
`g(n)` for suitable `n` — and then `diagSim`'s verdict on `x` contradicts `M`'s
(`diagLang_not_mem_DTIME`).

## Divergences from [AB09, Theorem 3.1]

* **Overhead `f²` instead of `f log f`.** The book's universal machine has
  `O(T log T)` overhead ([AB09, Theorem 1.9 / §1.7]); this development's universal
  machine is linear on coded machines but coded machines are one-work-tape binary
  machines, and an arbitrary binary machine is normal-formed with quadratic slowdown
  (`Turing.FinTM.one_work_tape_binary`, [AB09, Claims 1.5–1.6]). The hypothesis is
  therefore `(f(n) + n + 1)² = o(g(n))`, written out as
  `∀ A, ∃ N, ∀ n ≥ N, A · (f n + n + 1)² ≤ g n`. The `+ n + 1` absorbs the linear
  cost of reading the input and the `+ 1` normalization of `DTIME` bounds. The
  sharper `f log f` form is out of reach until the `O(T log T)` simulation (phase-5
  stretch goal of the Chapter 1 plan) exists.
  Because of the `+ n + 1` term the hypothesis forces `g(n) = ω(n²)`, so finer
  separations below the quadratic threshold — e.g. the book's illustration
  `DTIME(n) ⊊ DTIME(n^1.5)` — are **not** derivable from this theorem; the best
  linear-time separation it yields is roughly `DTIME(n) ⊊ DTIME(n^(2+ε))`.
* **No time-constructibility hypothesis on `f`** — none is needed (the book assumes
  it only for symmetry).
* **`DTIME(g + 1)` instead of `DTIME(g)`.** `TimeConstructible g` permits `g 0 = 0`,
  and `DTIME` of a bound vanishing anywhere is empty
  (`Complexity.DTIME_eq_empty_of_exists_zero`); the `+ 1` repairs this degenerate
  case only (for `n ≥ 1`, `g n ≥ n ≥ 1`).
* **Padding the input, not the code.** The book uses that every machine has
  infinitely many codes. Here the universal machine's constant depends on the code
  string (`Turing.universal` — the canonizer time of the representation scheme is an
  opaque bound), so the diagonal argument fixes one code `α` and pads the *input*
  `pairEncode α 1^m`; the code is recovered from the input by `preTM`.
* **The clock counts the diagonal machine's own simulation steps**, via the clocked
  runner `Complexity.TimeHierarchy.clockTM`.
* The separation is proved in the stronger *infinitely-often* form:
  `diagLang_not_mem_DTIME` needs `A · (T n + n + 1)² ≤ g n` only for infinitely many
  `n`, for each `A`.

## Main definitions

* `Complexity.TimeHierarchy.code`, `univTM`, `diagSim` — the fixed scheme, universal
  machine, and simulator.
* `Complexity.TimeHierarchy.diagLang` — the diagonal language.

## Main results

* `Complexity.TimeHierarchy.diagLang_mem_DTIME` — `diagLang g ∈ DTIME (g + 1)`.
* `Complexity.TimeHierarchy.diagLang_not_mem_DTIME` — `diagLang g ∉ DTIME T` whenever
  `A · (T n + n + 1)² ≤ g n` infinitely often for every `A`.
* `Complexity.time_hierarchy` — [AB09, Theorem 3.1], in the form above.
* `Complexity.time_hierarchy_of_pos` — the same with `DTIME g` when `g` never vanishes.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.1, Theorem 3.1, pp. 69–70; §1.4.)
-/

namespace Complexity.TimeHierarchy

open Turing Turing.FinTM

/-- The fixed effective representation scheme of the hierarchy construction (any
scheme works; `Turing.exists_effectiveMachineCode` provides one). -/
noncomputable def code : EffectiveMachineCode := Classical.choice exists_effectiveMachineCode

/-- The universal machine for `code`, from `Turing.universal`. -/
noncomputable def univTM : FinTM Bool := Classical.choose (universal code)

/-- The universal machine's specification (`Turing.universal`). -/
lemma univTM_spec : ∀ α : List Bool, ∃ C : ℕ, ∀ x : List Bool,
    (∀ (output : List Bool) (t : ℕ),
      (code.decode α).toFinTM.ComputesInTime x output t →
      univTM.ComputesInTime (pairEncode α x) output (C * (t + 1))) ∧
    (∀ output : List Bool,
      (∃ t, univTM.ComputesInTime (pairEncode α x) output t) →
      ∃ t, (code.decode α).toFinTM.ComputesInTime x output t) :=
  Classical.choose_spec (universal code)

/-- The diagonal simulator: duplicate the code prefix (`preTM`), then run the
universal machine. On `x = pairEncode α w` it runs the machine coded by `α` on `x`. -/
noncomputable def diagSim : FinTM Bool := bufferedCompTM preTM univTM

/-- **The diagonal language** of the hierarchy theorem [AB09, Theorem 3.1, proof]:
the strings `x` on which the diagonal simulator does **not** halt with output `[true]`
within `g(|x|)` steps. -/
def diagLang (g : ℕ → ℕ) : Language Bool :=
  {x | ¬diagSim.ComputesInTime x [true] (g x.length)}

/-- **The diagonal language is decidable in time `O(g)`** [AB09, Theorem 3.1, proof:
"`D` runs in time `O(g(n))`"]: for time-constructible `g`,
`diagLang g ∈ DTIME (g + 1)`.

**Proof sketch.** Run the clocked runner `clockTM K diagSim`, with `K` the
time-constructibility witness of `g`: its budget word is `bits (g n)` of value `g n`,
so by `clockTM_spec` it outputs `[x ∈ diagLang g]` within
`c_K (g n + 1) + 4|bits (g n)| + n + 4 g n + 6 ≤ (c_K + 15)(g n + 1)` steps, using
`|bits m| ≤ m` and `n ≤ g n`. -/
theorem diagLang_mem_DTIME {g : ℕ → ℕ} (hg : TimeConstructible g) :
    diagLang g ∈ DTIME (fun n => g n + 1) := by
  classical
  obtain ⟨hgn, cK, _, K, hK⟩ := hg
  refine ⟨cK + 15, clockTM K diagSim, fun x => ?_⟩
  have h := clockTM_spec K diagSim x (g x.length).bits _ (hK x)
  rw [ctrVal_bits] at h
  have hout : [!(decide (diagSim.ComputesInTime x [true] (g x.length)))] =
      [MultiTapeTM.indicator (diagLang g : Set (List Bool)) x] := by
    by_cases hx : diagSim.ComputesInTime x [true] (g x.length)
    · have : x ∉ (diagLang g : Set (List Bool)) := fun h' => h' hx
      simp [MultiTapeTM.indicator, hx, this]
    · have : x ∈ (diagLang g : Set (List Bool)) := hx
      simp [MultiTapeTM.indicator, hx, this]
  rw [hout] at h
  apply h.mono
  have h1 := length_bits_le_self (g x.length)
  have h2 := hgn x.length
  nlinarith

/-- The polynomial bookkeeping of the diagonal argument: with `X = T + n + 1`, the
simulation cost `5n + 7 + C · (c₁ (c₀ T + 1)² + 1)` is at most
`(8 + C (c₁ (c₀ + 1)² + 1)) · X²`. -/
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

/-- **The diagonal language is not in `DTIME T`** [AB09, Theorem 3.1, proof: "`D`
differs from every machine running in time `f`"], provided `g` dominates
`A · (T n + n + 1)²` for infinitely many `n`, for every constant `A`.

**Proof sketch.** Suppose `M` decides `diagLang g` within `c₀ T(n)`. Normal-form `M`
to a one-work-tape binary machine (time `c₁ (c₀ T + 1)²`,
`Turing.FinTM.one_work_tape_binary`), relabel it to a coded machine `N`
(`Turing.exists_codeTM`), and let `α = ⌞N⌟`; let `C` be the universal machine's
constant for `α`. With `A = 8 + C (c₁ (c₀ + 1)² + 1)` pick `n ≥ 2|α| + 2` with
`A (T n + n + 1)² ≤ g n` and put `x = pairEncode α 1^(n - 2|α| - 2)`, so `|x| = n`.
Then `preTM` maps `x` to `pairEncode α x` (`scanPre_pairEncode_append`), on which
`univTM` simulates `N` on `x`, producing `M`'s verdict `[χ(x)]`; altogether `diagSim`
halts on `x` with `[χ(x)]` within `5n + 7 + C(c₁(c₀T + 1)² + 1) ≤ g n` steps
(`bufferedCompTM_computesInTime`, `diag_cost_le`). If `χ(x) = true` then
`x ∈ diagLang g`, i.e. `diagSim` does *not* output `[true]` within `g n` — a
contradiction; if `χ(x) = false` then `x ∉ diagLang g`, so `diagSim` outputs `[true]`
within `g n`, contradicting determinism of its output `[false]`. -/
theorem diagLang_not_mem_DTIME {g T : ℕ → ℕ}
    (hT : ∀ A N : ℕ, ∃ n ≥ N, A * (T n + n + 1) ^ 2 ≤ g n) :
    diagLang g ∉ DTIME T := by
  classical
  rintro ⟨c₀, M, hM⟩
  let χ := MultiTapeTM.indicator (diagLang g : Set (List Bool))
  obtain ⟨M₁, c₁, hk, h₁⟩ :=
    one_work_tape_binary M (fun x => [χ x]) (fun n => c₀ * T n) hM
  obtain ⟨N, hN⟩ := exists_codeTM M₁ hk
  let α := code.encode N
  have hdec : code.decode α = N := code.toMachineCode.decode_encode N
  obtain ⟨C, hC⟩ := univTM_spec α
  obtain ⟨n, hn, hgn⟩ := hT (8 + C * (c₁ * (c₀ + 1) ^ 2 + 1)) (2 * α.length + 2)
  let w := List.replicate (n - (2 * α.length + 2)) true
  let x := pairEncode α w
  have hx : x.length = n := by
    simp only [x, w, length_pairEncode, List.length_replicate]; omega
  -- the simulated decider
  have hNx : (code.decode α).toFinTM.ComputesInTime x [χ x]
      (c₁ * (c₀ * T n + 1) ^ 2) := by
    rw [hdec, hN]
    have := h₁ x
    rw [hx] at this
    exact this
  have hU := (hC x).1 [χ x] _ hNx
  have hP := preTM_computes x
  rw [show scanPre x ++ x = pairEncode α x from scanPre_pairEncode_append α w] at hP
  have hD := bufferedCompTM_computesInTime preTM univTM hP hU
  have hlen : (pairEncode α x).length ≤ 2 * n := by
    rw [length_pairEncode, hx]; omega
  have hD' : diagSim.ComputesInTime x [χ x] (g x.length) := by
    apply hD.mono
    rw [hx]
    have := diag_cost_le n (T n) c₀ c₁ C
    calc 3 * n + 5 + (pairEncode α x).length + 2 + C * (c₁ * (c₀ * T n + 1) ^ 2 + 1)
        ≤ 5 * n + 7 + C * (c₁ * (c₀ * T n + 1) ^ 2 + 1) := by omega
      _ ≤ _ := this
      _ ≤ g n := hgn
  by_cases hmem : x ∈ (diagLang g : Set (List Bool))
  · have hχ : χ x = true := by simp [χ, MultiTapeTM.indicator, hmem]
    rw [hχ] at hD'
    exact hmem hD'
  · have hχ : χ x = false := by simp [χ, MultiTapeTM.indicator, hmem]
    rw [hχ] at hD'
    have htrue : diagSim.ComputesInTime x [true] (g x.length) := by
      by_contra hc
      exact hmem hc
    have := htrue.output_unique hD'
    simp at this

end Complexity.TimeHierarchy

namespace Complexity

open TimeHierarchy

/-- **The Time Hierarchy Theorem** [AB09, Theorem 3.1], in the form supported by this
development: if `g` is time constructible and `(f(n) + n + 1)² = o(g(n))` — i.e. for
every constant `A`, eventually `A · (f n + n + 1)² ≤ g n` — then
`DTIME(f) ⊊ DTIME(g + 1)`.

Deviations from the book (see the module docstring): the overhead is quadratic
(`(f + n + 1)²` in place of `f log f`), owing to the one-work-tape normal form of
coded machines; `f` need not be time constructible; and the larger class is
`DTIME (g + 1)`, which differs from `DTIME g` only in the degenerate case `g 0 = 0`.

**Proof sketch.** *Inclusion:* the hypothesis with `A = 1` gives `f n ≤ g n` for
`n ≥ N`; the finitely many smaller lengths are absorbed into the constant, so
`f n ≤ c (g n + 1)` for all `n`, and `DTIME` absorbs `c`. *Strictness:* the diagonal
language `diagLang g` lies in `DTIME (g + 1)` (`diagLang_mem_DTIME`) but not in
`DTIME f` (`diagLang_not_mem_DTIME`, whose infinitely-often hypothesis follows from the
eventual one). -/
theorem time_hierarchy {f g : ℕ → ℕ} (hg : TimeConstructible g)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * (f n + n + 1) ^ 2 ≤ g n) :
    DTIME f ⊂ DTIME (fun n => g n + 1) := by
  refine ⟨?_, fun hsub => diagLang_not_mem_DTIME (g := g) (T := f) ?_
    (hsub (diagLang_mem_DTIME hg))⟩
  · -- inclusion
    obtain ⟨N, hN⟩ := hfg 1
    let F := ∑ i ∈ Finset.range N, f i
    have hle : ∀ n, f n ≤ (F + 1) * (g n + 1) := by
      intro n
      by_cases hn : n < N
      · have : f n ≤ F := Finset.single_le_sum (f := f) (fun _ _ => Nat.zero_le _)
          (Finset.mem_range.mpr hn)
        nlinarith
      · have h := hN n (by omega)
        have : f n ≤ g n := by nlinarith
        nlinarith
    rintro L ⟨c, M, hM⟩
    exact ⟨c * (F + 1), M, fun x => (hM x).mono (by
      simp only [Nat.mul_assoc]; exact Nat.mul_le_mul_left c (hle x.length))⟩
  · intro A N₀
    obtain ⟨N, hN⟩ := hfg A
    exact ⟨max N N₀, le_max_right _ _, hN _ (le_max_left _ _)⟩

/-- **The Time Hierarchy Theorem for a positive bound** [AB09, Theorem 3.1]: as
`Complexity.time_hierarchy`, with the larger class exactly `DTIME g` when `g` never
vanishes (then `DTIME (g + 1) = DTIME g`, the constant `2` being absorbed).

**Proof sketch.** `c (g n + 1) ≤ 2c · g n` when `g n ≥ 1`, so `DTIME (g + 1) ⊆ DTIME g`;
the reverse inclusion is `Complexity.DTIME.mono`; conclude from
`Complexity.time_hierarchy`. -/
theorem time_hierarchy_of_pos {f g : ℕ → ℕ} (hg : TimeConstructible g) (hpos : ∀ n, 0 < g n)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * (f n + n + 1) ^ 2 ≤ g n) :
    DTIME f ⊂ DTIME g := by
  have heq : DTIME (fun n => g n + 1) = DTIME g := by
    apply Set.Subset.antisymm
    · rintro L ⟨c, M, hM⟩
      refine ⟨2 * c, M, fun x => (hM x).mono ?_⟩
      have := hpos x.length
      dsimp only
      nlinarith
    · exact DTIME.mono (fun n => Nat.le_succ _)
  rw [← heq]
  exact time_hierarchy hg hfg

end Complexity

```


## ===== TCSlib/Complexity/TimeHierarchy/Separation.lean =====

```
/-
Copyright (c) 2026 Hydroxyi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.ClassNP.EXP
import TCSlib.Complexity.TimeHierarchy.Diagonal

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# P ⊊ EXP

[AB09, §3.1, after Theorem 3.1]: the time hierarchy theorem separates polynomial from
exponential time. We instantiate `Complexity.time_hierarchy` (more precisely, its two
halves `diagLang_mem_DTIME` and `diagLang_not_mem_DTIME`) with the budget `g(n) = 2ⁿ`:
the single diagonal language `diagLang (2^·)` lies in `DTIME(2ⁿ + 1) ⊆ EXP` and in no
`DTIME(nᵏ + 1)`, hence not in `P`.

## Main results

* `Complexity.timeConstructible_two_pow` — `n ↦ 2ⁿ` is time constructible
  [AB09, §1.3, example `2ⁿ`].
* `Complexity.eventually_poly_le_two_pow` — polynomials are eventually dominated by
  `2ⁿ`, with an arbitrary constant factor.
* `Complexity.dtime_poly_ssubset_dtime_two_pow` — `DTIME(nᵏ + 1) ⊊ DTIME(2ⁿ)` for
  every `k` (the hierarchy theorem at the polynomial/exponential gap).
* `Complexity.P_ssubset_EXP` — `P ⊊ EXP` [AB09, §3.1; cf. Claim 2.4 for `P ⊆ EXP`].
* `Complexity.P_ne_EXP` — `P ≠ EXP`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.3; §2.6, Claim 2.4; §3.1, Theorem 3.1.)
-/

namespace Complexity

open Turing Turing.FinTM TimeHierarchy

/-- The machine `x ↦ 0^|x| 1`, the binary representation of `2^|x|` (low bit first):
emit `false` for every input symbol, then `true`, and halt. -/
private def twoPowTM : FinTM Bool where
  k := 0
  State := Unit
  tm :=
    { q₀ := ()
      tr := fun _ inp _ =>
        match inp with
        | some _ => ⟨.pos, fun _ => (none, 0), some false, some ()⟩
        | none => ⟨0, fun _ => (none, 0), some true, none⟩ }

/-- The run invariant of `twoPowTM`: after `i ≤ |x|` steps it is live at input
position `i + 1` with `0^i` emitted. -/
private lemma twoPowTM_run (x : List Bool) : ∀ i, i ≤ x.length →
    (twoPowTM.tm.runFrom (twoPowTM.tm.initCfg x) i).state = some () ∧
    ((twoPowTM.tm.runFrom (twoPowTM.tm.initCfg x) i).inputPos : ℕ) = i + 1 ∧
    (twoPowTM.tm.runFrom (twoPowTM.tm.initCfg x) i).output = List.replicate i false := by
  intro i
  induction i with
  | zero => intro _; exact ⟨rfl, rfl, rfl⟩
  | succ i ih =>
    intro hi
    obtain ⟨hs, hp, ho⟩ := ih (by omega)
    rw [MultiTapeTM.runFrom_succ_eq_step']
    generalize twoPowTM.tm.runFrom (twoPowTM.tm.initCfg x) i = c at hs hp ho
    have hin : c.inputSymbol = some (x[i]'(by omega)) := inputSymbolInner i (by omega) (by omega)
    unfold MultiTapeTM.step
    rw [hs]
    simp only [twoPowTM, hin, Action.apply]
    refine ⟨trivial, ?_, ?_⟩
    · rw [moveInputPos_pos_of_ne_right _ (by omega)]; simp [hp]
    · simp [ho, List.replicate_succ']

/-- The binary representation of `2ⁿ`, low bit first. -/
private lemma bits_two_pow (n : ℕ) : (2 ^ n).bits = List.replicate n false ++ [true] := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : 2 ^ (n + 1) = Nat.bit false (2 ^ n) := by
      simp [Nat.bit_val, Nat.pow_succ]; ring
    rw [h, Nat.bits_append_bit _ _ (fun h0 => absurd h0 (by positivity)), ih]
    simp [List.replicate_succ]

/-- **`2ⁿ` is time constructible** [AB09, §1.3: "`n`, `n log n`, `n²`, `2ⁿ` are time
constructible"]: `n ≤ 2ⁿ`, and `twoPowTM` writes `bits (2^|x|) = 0^|x| 1` in
`|x| + 1 ≤ 2^|x| + 1` steps. -/
theorem timeConstructible_two_pow : TimeConstructible (fun n => 2 ^ n) := by
  refine ⟨fun n => Nat.lt_two_pow_self.le, 1, Nat.one_pos, twoPowTM, fun x => ?_⟩
  obtain ⟨hs, hp, ho⟩ := twoPowTM_run x x.length (le_refl _)
  have hhalt : twoPowTM.ComputesInTime x (2 ^ x.length).bits (x.length + 1) := by
    rw [computesInTime_iff, MultiTapeTM.runFrom_succ_eq_step']
    generalize twoPowTM.tm.runFrom (twoPowTM.tm.initCfg x) x.length = c at hs hp ho
    have hin : c.inputSymbol = none := by
      have hpos : c.inputPos = ⟨x.length + 1, by omega⟩ := Fin.ext hp
      simp [Cfg.inputSymbol, hpos]
    unfold MultiTapeTM.step
    rw [hs]
    simp only [twoPowTM, hin, Action.apply]
    exact ⟨trivial, by simp [ho, bits_two_pow]⟩
  exact hhalt.mono (by have := @Nat.lt_two_pow_self x.length; simp only; omega)

/-- **Polynomials are eventually below `2ⁿ`**: for all constants `A` and `K` there is
`N` with `A · (n + 1)^K ≤ 2ⁿ` for all `n ≥ N`.

**Proof sketch.** Let `d = K + 1` and `m = ⌊n / d⌋`, so `n + 1 ≤ d (m + 1)` and
`d m ≤ n`. Then `A (n+1)^K ≤ A d^K (m+1)^K ≤ m · (2^m)^K < (2^m)^(K+1) ≤ 2ⁿ` as soon as
`m ≥ A d^K`, i.e. for `n ≥ d · A d^K`. -/
theorem eventually_poly_le_two_pow (A K : ℕ) :
    ∃ N, ∀ n ≥ N, A * (n + 1) ^ K ≤ 2 ^ n := by
  refine ⟨(K + 1) * (A * (K + 1) ^ K), fun n hn => ?_⟩
  set d := K + 1 with hd
  have hd0 : 0 < d := by omega
  set m := n / d with hm
  have hmA : A * d ^ K ≤ m := by
    rw [hm, Nat.le_div_iff_mul_le hd0]; rw [Nat.mul_comm]; exact hn
  have hn1 : n + 1 ≤ d * (m + 1) := Nat.lt_mul_div_succ n hd0
  have hdm : d * m ≤ n := Nat.mul_div_le n d
  have hm2 : m + 1 ≤ 2 ^ m := Nat.lt_two_pow_self
  calc A * (n + 1) ^ K ≤ A * (d * (m + 1)) ^ K :=
        Nat.mul_le_mul_left A (Nat.pow_le_pow_left hn1 K)
    _ = (A * d ^ K) * (m + 1) ^ K := by rw [mul_pow]; ring
    _ ≤ 2 ^ m * (2 ^ m) ^ K :=
        Nat.mul_le_mul (hmA.trans (Nat.le_of_lt (Nat.lt_two_pow_self)))
          (Nat.pow_le_pow_left hm2 K)
    _ = 2 ^ (d * m) := by rw [← pow_mul, ← pow_add, hd]; ring_nf
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hdm

/-- The hierarchy hypothesis for polynomial `f = nᵏ + 1` against `g = 2ⁿ`: for every
`A`, eventually `A · (nᵏ + 1 + n + 1)² ≤ 2ⁿ`. -/
theorem eventually_poly_sq_le_two_pow (k A : ℕ) :
    ∃ N, ∀ n ≥ N, A * (n ^ k + 1 + n + 1) ^ 2 ≤ 2 ^ n := by
  obtain ⟨N, hN⟩ := eventually_poly_le_two_pow (9 * A) (2 * k + 2)
  refine ⟨N, fun n hn => le_trans ?_ (hN n hn)⟩
  have h1 : n ^ k ≤ (n + 1) ^ (k + 1) :=
    (Nat.pow_le_pow_left (Nat.le_succ n) k).trans
      (Nat.pow_le_pow_right (Nat.succ_pos n) (Nat.le_succ k))
  have h2 : n + 1 ≤ (n + 1) ^ (k + 1) := by
    calc n + 1 = (n + 1) ^ 1 := (pow_one _).symm
      _ ≤ (n + 1) ^ (k + 1) := Nat.pow_le_pow_right (Nat.succ_pos n) (by omega)
  have h3 : n ^ k + 1 + n + 1 ≤ 3 * (n + 1) ^ (k + 1) := by omega
  have h4 : (n ^ k + 1 + n + 1) ^ 2 ≤ 9 * (n + 1) ^ (2 * k + 2) := by
    calc (n ^ k + 1 + n + 1) ^ 2 ≤ (3 * (n + 1) ^ (k + 1)) ^ 2 := Nat.pow_le_pow_left h3 2
      _ = 9 * (n + 1) ^ (2 * k + 2) := by ring
  calc A * (n ^ k + 1 + n + 1) ^ 2 ≤ A * (9 * (n + 1) ^ (2 * k + 2)) :=
        Nat.mul_le_mul_left A h4
    _ = 9 * A * (n + 1) ^ (2 * k + 2) := by ring

/-- **The polynomial/exponential gap of the hierarchy theorem** [AB09, Theorem 3.1
instantiated]: `DTIME(nᵏ + 1) ⊊ DTIME(2ⁿ)` for every `k` (the `+ 1` normalization
is that of `Complexity.P`). -/
theorem dtime_poly_ssubset_dtime_two_pow (k : ℕ) :
    DTIME (fun n => n ^ k + 1) ⊂ DTIME (fun n => 2 ^ n) :=
  time_hierarchy_of_pos timeConstructible_two_pow (fun n => by positivity)
    (eventually_poly_sq_le_two_pow k)

/-- **`P ⊊ EXP`** [AB09, §3.1, consequence of the Time Hierarchy Theorem 3.1; the
inclusion is Claim 2.4]. The witness is the diagonal language `diagLang (2^·)`.

**Proof sketch.** Inclusion is `Complexity.P_subset_EXP`. The diagonal language with
budget `2ⁿ` lies in `DTIME(2ⁿ + 1) ⊆ DTIME(2^(n¹))` up to the constant `2`, hence in
`EXP`; and for every `k` it is not in `DTIME(nᵏ + 1)` (`diagLang_not_mem_DTIME`, whose
hypothesis `A (nᵏ + 1 + n + 1)² ≤ 2ⁿ` holds eventually by
`eventually_poly_sq_le_two_pow`), hence not in `P = ⋃ₖ DTIME(nᵏ + 1)`. -/
theorem P_ssubset_EXP : P ⊂ EXP := by
  refine ⟨P_subset_EXP, fun h => ?_⟩
  have hmem : diagLang (fun n => 2 ^ n) ∈ EXP := by
    obtain ⟨c, M, hM⟩ := diagLang_mem_DTIME timeConstructible_two_pow
    refine Set.mem_iUnion.mpr ⟨1, 2 * c, M, fun x => (hM x).mono ?_⟩
    have : 1 ≤ 2 ^ x.length := Nat.one_le_two_pow
    simp only [pow_one]
    nlinarith
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (h hmem)
  refine diagLang_not_mem_DTIME (T := fun n => n ^ k + 1) (fun A N₀ => ?_) hk
  obtain ⟨N, hN⟩ := eventually_poly_sq_le_two_pow k A
  exact ⟨max N N₀, le_max_right _ _, hN _ (le_max_left _ _)⟩

/-- **`P ≠ EXP`** [AB09, §3.1]. -/
theorem P_ne_EXP : P ≠ EXP := P_ssubset_EXP.ne

end Complexity

```


## ===== TCSlib/Complexity/TimeHierarchy.lean =====

```
/-
Copyright (c) 2026 Hydroxyi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.TimeHierarchy.ClockMachine
import TCSlib.Complexity.TimeHierarchy.ClockLoop
import TCSlib.Complexity.TimeHierarchy.CodePrefix
import TCSlib.Complexity.TimeHierarchy.Diagonal
import TCSlib.Complexity.TimeHierarchy.Separation

/-!
# The Time Hierarchy Theorem

[AB09, §3.1, Theorem 3.1]: more time decides more languages. The headline results are
`Complexity.time_hierarchy` (if `g` is time constructible and `(f(n) + n + 1)² = o(g(n))`
then `DTIME(f) ⊊ DTIME(g + 1)` — quadratic overhead in place of the book's
`f log f`, see `TimeHierarchy.Diagonal` for all divergences) and its consequence
`Complexity.P_ssubset_EXP` (`P ⊊ EXP`).

## Contents

- `TimeHierarchy.ClockMachine`: the clocked runner `clockTM K W` (budget word from `K` on a
  binary counter tape; `W` run step by step against it) and its setup phases
- `TimeHierarchy.ClockLoop`: the counter loop with amortized cost analysis and the runner's
  specification `clockTM_spec`
- `TimeHierarchy.CodePrefix`: the code-prefix duplication machine `preTM`
  (`pairEncode α w ↦ pairEncode α (pairEncode α w)`) and timed partial composition
- `TimeHierarchy.Diagonal`: the diagonal language, its upper and lower bounds, and
  `Complexity.time_hierarchy` [AB09, Theorem 3.1]
- `TimeHierarchy.Separation`: `2ⁿ` is time constructible, `DTIME(nᵏ + 1) ⊊ DTIME(2ⁿ)`,
  and `P ⊊ EXP`

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.1.)
-/

```
