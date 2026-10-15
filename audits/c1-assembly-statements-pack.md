# External audit pack — C1-A: the guess-then-run assembly lemma (statement gate)

Campaign: the Arora-Barak chapters 3-4 plan, cluster C1 (`Diagonalization/NTimeHierarchy.lean`,
[AB09, Theorem 3.2] at linear overhead, decision CH34-Q8). C1's host contracts passed their
statement gate on 2026-10-14 (PASS, 0/0/11; `audits/c1-hosts-statements-findings.md`) and landed
in PR #87. That gate ruled (open question 2, "ruling 2") that the public **guess-then-run assembly
lemma** be stated and gated in `Build/NDHost.lean` during C1-A, before the brief of the universal
NDTM. **This gate audits that lemma: one host definition (a composition of the present phase
host) and a family of eight theorems, to be appended to `TCSlib/Complexity/TuringMachine/Build/
NDHost.lean`.** Every theorem is proved and machine-checked; six of them use the writer's gated
contract `Turing.ndWriterTM_run_block`, which stays sorried, and are proved modulo it. No new
`sorry` is introduced. Nothing is landed.

| File (bundle path) | Content |
|---|---|
| `audits/evidence/c1/assembly/C1Assembly.lean.txt` (896 lines, MEASURED) | **the unit**: one part, appended to `Build/NDHost.lean` at landing; 20 declarations (18 public, 2 private), 0 sorries |
| `audits/evidence/c1/assembly/C1-assembly-design.md` | the design note: what UN and D need, the shape, alternatives, every cited declaration with `file:line` |
| `audits/evidence/c1/assembly/AssemblyConsumerProbe.lean.txt` | **the consumer probe**: the unit plus two derivations, UN's statement and D's `NTIME` membership shape |

Supporting evidence: `audits/evidence/c1/assembly/probes/C1AssemblySanity.lean.txt` (the unit
plus 16 sanity `example`s), `…/probes/C1AssemblyAxioms.lean.txt` (axiom prints),
`…/cut/NDHost.check.lean.txt` (the cut check file), `…/landed/NDHost.lean.txt` (the landing
form of `Build/NDHost.lean`), `…/scripts/` (the probe and landing builders, the freeze check, the
name screen, the cited-name screen, the sorry-isolation builder, the lint and width scripts, the
three probe tails, and `runall.sh`, which regenerates every log and **fails closed**: it records
each check as PASS or FAIL and exits 1 on any failure, answering the C1 host-contracts gate's
note N2). Logs: `audits/logs/c1-assembly-statements-base.log` (the tip's sources and the snapshot),
`…-elaboration.log`, `…-cutcheck.log`, `…-freeze.log`, `…-axioms.log`, `…-names.log`,
`…-summary.log` (34 checks, 0 failed).

**Bundle:** this pack first, then the standards (`audits/TEMPLATE.md`, `policy.md`,
`workflow.md`), the design note, the unit, the probes, the scripts and logs (with `base.log`), the C1
host-contracts pack, findings and resolutions, the C1 design note, the six C1 modules
(`Build/NDHost.lean`, `Nondeterministic.lean`, `ChoiceReplay.lean`, `NDCodeSimulator.lean`,
`ClassNP/ExhaustiveReplay.lean`, `NTimeHierarchy.lean`), and every library file whose
declarations the statements cite or use (`BUNDLE-FILES.txt` lists them in order).

**Provenance (maintainer).** A maintainer sub-agent wrote the files at campaign commit
`2c3c975a` (checkout `wt-c1asm`, snapshot `oleans-lc1`), then, after the tip moved, re-ran every
check reported here at the campaign tip **`e831b5b0d887dac3bbf1aa2c19af28983b15b982`**: its
sources extracted by `git archive` (`base.log` §1: 717 of 717 files; Lean content identical to
`13a16a69`, after MIG-0b's landing #90 and #91; the Mathlib manifest unchanged), elaborated against
`oleans-lm0b`, MIG-0b's replay output, the snapshot the B6 landing run used at `13a16a69`
(Lean `v4.25.0`). The tip's `Build/NDHost`, `Build/Catalog`, `Build/Embed`, `Build/Seam` and
`StateRenaming` elaborate against it with 0 errors (`base.log` §2). The unit needed no change.
The proofs were developed in a scratch draft and the unit was assembled from it with the
docstrings by a script (evidence of process only, not bundled).

## What the gate covers

1. **The guess-then-run host** `Turing.guessRunTM`: `Turing.NDTM.phaseHostND` over six fixed
   phases (setup, bounded writer, one step right, rewind, run, verdict leaf), with its phase
   index, state types, phase machines, redirect table, and the two configurations it is stated
   with (`Turing.guessRunCfg`, the run's entry; `Turing.streamStartCfg`, the interpreter core's
   start).
2. **The assembly theorems**: the handoff through the guess and the rewind, liveness before it,
   the whole branch to the verdict, the halting-setup case, all-branch halting, and exact-budget
   acceptance in both directions.
3. **The interpreter core's interface**: the core's clean-bank, head and output precondition at
   the handoff, and the composite with the core run silently (emission capture, live verdicts).
4. **Sufficiency for the consumers**: the two derivations of the consumer probe.
5. **Home, the one new import, names, documentation.**

Out of scope: the fills of `Turing.ndWriterTM_run_block`, `Turing.exists_ndInterpreterCore` and
the other C1 contracts (gated in the C1 host-contracts pack); UN's and D's own fills (the setup
machines and D's suffix; probe hypotheses); the six frozen statements of `NTimeHierarchy.lean`;
the B6 step clock (gated with the B6 hosts) and the H1 hosted-clock harvest (C1 resolutions).

## Decisions in force (verify that the files reflect them)

**User decisions of 2026-10-13, binding** (C1 design note, `audits/evidence/c1/C1-design.md` §6):
1. **Guess first** for `UN` and `D`; no nondeterministic loop host (SC-3 closed).
2. **`BF := E(UN)`**, `E = Turing.FinNDTM.exists_exhaustiveDecider`.
3. **ND codes interpreted through their replay machine**, the step block unchanged at `k = 3`.
4. **One step clock, shared with B6.**
5. **UN reads its input through a bounded window copy and input locality.**

**Ruling 2 of the C1 host-contracts gate** (findings, "Rulings on the five open questions", 2),
verbatim: "State and gate the public guess-then-run assembly lemma in `Build/NDHost.lean` during
C1-A, before UN's brief. It should identify the writer's word, transfer the deterministic phases,
account for dispatch/rewind/setup, and establish both directions of exact-budget acceptance and
all-branch halting. In particular, it must establish R's clean-bank/head/output precondition and
handle live verdicts and emission capture. This is composition of the present host, not a new
host requiring a different construction architecture."

**Earlier rulings of the same gate in force.** Note N3 (the assembly lemma is a future public
interface; "Keep the harvest and assembly gates before the respective consumer briefs"); the
`phaseHostND_run` row ("It is a one-phase result; concatenating phases is the disclosed future
assembly lemma"); brief point 8 ("Do not mistake them for the still-to-be-stated whole
guess-then-run equivalence"); finding M1 (the writer's timing is branch-independent only in the
trivial-controller instance, which is the one the assembly uses); the rulings keeping the
prefix clause of `R` and requiring the H1 harvest before `R`'s brief.

The design note's §1.3 maps ruling 2 to the statements item by item.

## Sequencing (the open PRs)

**This gate depends on no open PR.** No statement, proof or probe uses the statements of PR #92
(the B6 hosts, open), including `Turing.exists_stepClockTMVia`, which the C1 *consumers* cite (D's
suffix and `E`'s fill), not the assembly; the unit neither imports nor cites it. #92 patches two
modules in the landed NDHost's closure, `StateRenaming` and `Encoding` (additions); the name screen
covers #92's landing tree, with no clash (`names.log`). The two land in either order; if #92 merges
first, this part's landing PR re-runs the cut check at the merged tip. PR #93 (comments and
imports in 33 ARM files, open) touches no module of the unit's or the probes' closure (`names.log`).
UN's brief waits on this gate and on the H1 hosted-clock harvest (C1 resolutions).

## Home and landing

The part is appended to `TCSlib/Complexity/TuringMachine/Build/NDHost.lean`, after
`Turing.ndWriterTM_run_block`, verbatim. The file gains one import,
`TCSlib.Complexity.TuringMachine.Build.Catalog`, for the rewind rows `Turing.skipTM`,
`Turing.skipBackTM`, `Turing.SeekPhase` and their framed contracts (and the `Fintype` deriving
handler). `Build.Catalog` does not have `Build.NDHost` in its import closure; the only module
importing `Build.NDHost` is the `TCSlib.Complexity.TuringMachine` facade, which already imports
`Build.Catalog` (`names.log`). The module docstring's title, design list, `## Main definitions`,
`## Main results` and `## References` gain the new names (comment edits; `freeze.log` shows the
raw diff). No existing declaration changes (`freeze.log`). Landing obligations outside the
statements: the design §14 registry's C1 paragraph names `guessRunTM` as the assembly of the
phase host (not a new host row); the plan's C1 row and the backlog record this gate.

Why `Build/NDHost.lean`: ruling 2 names it; the assembly is a lemma about its host; its
consumers (UN, D) import it anyway.

## What the files state (verify)

All in namespace `Turing`; lines are the unit's (`C1Assembly.lean.txt`).
- `NDWriterState.instFintype` (85, instance): `NDWriterState Q` is finite when `Q` is, through
  `Option Q`.
- `GuessRunPhase` (100, inductive, deriving `DecidableEq`, `Fintype`): `pre | guess | skip | back
  | run | out`. `GuessRunPhase.State SP SQ` (118): `SP`, `NDWriterState Unit`, `SeekPhase`,
  `SeekPhase`, `SQ`, `Bool`. Instances `instFintypeState` (127), `instDecidableEqState` (137).
- `guessRunPhases P j Q` (154): `P.toNDTM`; the bounded writer with the trivial controller
  `ndWriterTM k j () (fun _ _ => ()) (fun _ => false) true`; `(skipTM k j).toNDTM`;
  `(skipBackTM k j).toNDTM`; `Q.toNDTM`; the leaf `⟨false, fun _ b _ _ => ⟨0, fun _ => (none, 0),
  some b, none⟩⟩` (state `b` emits `b` and halts).
- `guessRunRed pexit qentry acc rej` (170): `pexit ↦ ⟨guess, run ()⟩`; writer `done ↦ ⟨skip,
  run⟩`; skip `done ↦ ⟨back, run⟩`; back `done ↦ ⟨run, qentry⟩`; run `acc ↦ ⟨out, true⟩`, else
  `rej ↦ ⟨out, false⟩`; nothing else.
- `guessRunTM P pexit j Q qentry acc rej` (199): `NDTM.phaseHostND (guessRunPhases P j Q)
  ⟨.pre, P.q₀⟩ (guessRunRed pexit qentry acc rej)`.
- `guessRunCfg c j s q` (207): `⟨some q, c.inputPos, update c.workTapes j (p ↦ if pos ≤ p < pos
  + |s| then bufferTape s (p - pos) else c.workTapes j p), c.workTapePos, c.output⟩`, with
  `pos = c.workTapePos j`.
- `streamStartCfg z j q s` (219): `⟨some q, 1, i ↦ if i = j then bufferTape s else blank, 0, []⟩`
  (the core's `start`, `NDCodeSimulator.lean:134-136`, verbatim).
- **Setup hypotheses** (shared by the next six theorems): `hP : P.runFrom (P.initCfg z) TP = cP`,
  `hPexit : cP.state = some pexit`, `hPfirst : ∀ u < TP, (P.runFrom (P.initCfg z) u).state ≠ some
  pexit`, `hblock : ∀ p < m, cP.workTapes j (cP.workTapePos j + p) ≠ none`, `hend :
  cP.workTapes j (cP.workTapePos j + m) = none`, `hleft : cP.workTapes j (cP.workTapePos j - 1) =
  none`.
- `guessRunTM_runWith_handoff` (257): for every `w` with `|w| = TP + 2m + 9`, the host's branch
  from its initial configuration on `z` is `(guessRunCfg cP j ((w.drop (TP + 1)).take m)
  qentry).mapState (Sigma.mk .run)`.
- `guessRunTM_runWith_live` (435): for `|w| < TP + 2m + 9`, the branch's state is not `none`.
- `guessRunTM_runWith` (470): for a stream `s` with `|s| = m`, a time `TQ` at which the run from
  `guessRunCfg cP j s qentry` is at `acc` or `rej`, at neither before, and every `w` with
  `(w.drop (TP + 1)).take m = s` and `|w| ≥ TP + 2m + TQ + 11`: the branch is
  `⟨none, d.inputPos, d.workTapes, d.workTapePos, d.output ++ [decide (d.state = some acc)]⟩`
  with `d` the run's configuration at `TQ`.
- `guessRunTM_runWith_setup_halt` (563): if `P` halts at `TP`, never at `pexit` before, every
  `w` with `|w| ≥ TP` gives `(P.runFrom (P.initCfg z) TP).mapState (Sigma.mk .pre)`.
- `guessRunTM_haltsWithin` (609): with `hQ : ∀ s, |s| = m → ∃ TQ ≤ T, (verdict at TQ) ∧ (none
  before)`, `HaltsWithin z (TP + 2m + T + 11)`.
- `guessRunTM_accepts_iff` (642): with `hQ`, for every `B ≥ TP + 2m + T + 11`: `(∃ w, |w| = B ∧
  halted ∧ output = [true]) ↔ ∃ s, |s| = m ∧ ∃ TQ, (run at acc at TQ) ∧ (no verdict before) ∧
  (run's output at TQ = [])`.
- `guessRunCfg_clean` (715): for `ι : Fin K ↪ Fin k`, `cap ∉ range ι`, `blk` blank outside
  `[0, m)`, `|s| = m`: `guessRunCfg ⟨some q, 1, update blank (ι jR) blk, 0, []⟩ (ι jR) s entry =
  embedSilentCfg ι cap blank 0 [] [] (streamStartCfg z jR entry s)`.
- `guessRunTM_silent_spec` (808): with `hblk : ∀ p, blk p ≠ none ↔ 0 ≤ p < m`, `P` reaching
  the clean configuration `⟨some pexit, 1, update blank (ι jR) blk, 0, []⟩` first at `TP`, and
  `hR : ∀ s, |s| = m → ∃ TR ≤ T, R from streamStartCfg z jR entry s at acc or rej at TR, neither
  before`: for `N := guessRunTM P pexit (ι jR) (embedSilentTM ι cap R) entry acc rej`,
  `N.HaltsWithin z (TP + 2m + T + 11)` and, for every `B ≥ TP + 2m + T + 11`,
  `(∃ w, |w| = B ∧ halted ∧ output = [true]) ↔ ∃ s, |s| = m ∧ ∃ TR, (R at acc at TR) ∧ (no verdict
  before)`.

**The consumer probe** (`AssemblyConsumerProbe.lean.txt`, after the unit):
- `probe_universal_of_setup c hsetup`: from a setup hypothesis (for every `K` and stream tape
  `jR`, some `k`, `ι`, `cap ∉ range ι` and a finite setup machine that on `⟨⟨bits t, α⟩, x⟩`
  reaches its exit first within `C_P·(t + 1)`, clean, with a nonblank block of exactly `t` cells
  on tape `ι jR` from cell `0`), **the frozen statement of `Turing.exists_timed_universal_NDTM`**,
  with `UN := guessRunTM P pexit (ι jR) (embedSilentTM ι cap R) entry acc rej` for the core of
  `Turing.exists_ndInterpreterCore` and `C := C_P + C_R + 13`.
- `probe_ntime_of_guessRun`: if on every input `z` the setup meets the setup hypotheses with
  stream length `m z`, the run reaches a first verdict within `T z` on every stream, and
  `TP z + 2·m z + T z + 11 ≤ A·(g |z| + 1)`, then `{z | ∃ s, |s| = m z ∧ (first verdict acc, empty
  output)} ∈ NTIME (g + 1)`: the shape of "`D ∈ NTIME (g + 1)` by construction".

## Changes from the design (verify against the C1 design note §3.1 and this gate's design note)

The C1 design note §3.1 proposed "a deterministic prefix up to a block of length `m`, the
bounded choice writer, then a deterministic suffix `Q`", with all-branch halting if `Q` halts
from every written configuration and acceptance iff some `s` of length `m` makes `Q` accept,
ESTIMATE 200–400 lines.
1. **Live verdicts and a verdict leaf.** The suffix ends in live verdict states, redirected to a
   one-transition leaf that emits the verdict bit and halts, because the core `R` ends in live
   verdicts (ruling 2). A suffix that halts on its own still halts the host.
2. **The rewind is in the assembly** (two catalog seeks; the new import), so the run starts with
   every head where the setup left it, and a clean setup gives the core's exact start.
3. **Emission is explicit.** The generic acceptance carries the run's output (`= []`) in its
   right side; the core's composite captures the core's emissions with `Turing.embedSilentTM`.
4. **Exact times**: handoff `TP + 2m + 9`, halting `TP + 2m + TQ + 11`, uniform bound
   `TP + 2m + T + 11`.
5. **New cases**: liveness before the handoff, and a setup that halts before its exit (for
   inputs rejected without guessing, such as D's non-unary inputs).
6. **Size**: the part is 849 lines as it lands (MEASURED), against the ESTIMATE 200–400; the
   proofs are 425 nonblank tactic lines (MEASURED), of which 157 are the handoff's.
7. **Everything is proved**, against "proposed, not drafted".

## Brief for the auditor

Restate every definition in your own words before reading its docstring (failure mode 1); argue
each statement adequate for its consumers. **No sorried theorem is submitted**: the unit's
theorems are machine-checked, and the only sorried declaration they rest on is the writer's
contract `Turing.ndWriterTM_run_block`, gated and judged true in the C1 host-contracts gate
(findings, truth assessment 1). Argue in 2–5 sentences that the assembly uses that contract in
its gated form (the isolation probe substitutes an axiom with its statement verbatim; `axioms.log`
§2), or show a mismatch. Attempt at least the adversarial instantiations of point 11
(`audits/TEMPLATE.md` failure modes 1–5). Points to rule on:

1. **The host.** `guessRunPhases`, `guessRunRed`, `guessRunTM`, the leaf, the state types and
   instances. Is it a composition of the present host (ruling 2), with no new architecture? Is
   the hand-built leaf acceptable under policy §1 (construction reuse; the docstring names what
   is missing)? Does `acc` tested before `rej` matter?
2. **The writer's word.** Is `(w.drop (TP + 1)).take m` the stream on every branch (the setup's
   `TP` bits and its dispatch bit come first; the writer's last bit is ignored)? Is every stream
   of length `m` realized at every budget at least the handoff?
3. **The transfer of the deterministic phases.** On every branch, are the setup, the two seeks and
   the run their deterministic runs, so that only the writer's bits matter?
4. **Dispatch, rewind, setup.** The time `TP + 2m + 9` (four dispatches, `m + 1`, `1`, `m + 3`),
   and the halting time `TP + 2m + TQ + 11`. Are `hblock`, `hend`, `hleft` necessary (sanity
   example: a nonblank cell before the block changes the verdict) and sufficient? Are the heads
   really where the setup left them?
5. **All-branch halting and exact-budget acceptance.** Both directions of
   `guessRunTM_accepts_iff`; the budget `B ≥ TP + 2m + T + 11`; the output condition; the
   necessity of the verdict hypothesis `hQ` (sanity example: a run that halts with `[true]`
   without a verdict). Is the per-stream budget form needed by any consumer (the design note
   §2.3 says no)?
6. **The core's precondition.** Is `streamStartCfg` the core's `start` verbatim? Does
   `guessRunCfg_clean` establish the clean-bank, head and output precondition, including the
   capture tape and the frame? Is the clean-setup hypothesis of `guessRunTM_silent_spec`
   (`hblk` exact, every head `0`, input head `1`, empty output) the right one for UN?
7. **Live verdicts and emission capture.** In `guessRunTM_silent_spec`, is it right that `R`'s
   output is never examined, and that the host's output is exactly the verdict bit? (Sanity
   example: a noisy core, run directly and run silently.)
8. **The halting setup.** Is `guessRunTM_runWith_setup_halt` true and the right tool for D's
   rejections without guessing (alternative: an empty block and a rejecting run)?
9. **Sufficiency (the consumer probe).** Does probe 1 derive exactly the frozen statement of
   `Turing.exists_timed_universal_NDTM` (compare with `NTimeHierarchy.lean:159-164`), and is its
   setup hypothesis a fair statement of UN's remaining setup obligation (satisfiable, uniform in
   the code, `O(t + 1)`)? Does probe 2's conclusion have the shape `ntime_hierarchy`'s sketch uses
   for `D` (`NTimeHierarchy.lean:284-312`)?
10. **Home, the import, names, layering.** Appended to `Build/NDHost.lean`; the
    `Build.Catalog` import; the statements at the `NDTM` level, not `FinNDTM.AcceptsWithin`
    (layering: `TuringMachine/` does not import `ClassNP`); the names (`names.log`).
11. **Adversarial instantiations** (at least these): **(a)** a zero-length stream, a setup at its
    exit at time `0`, an immediately accepting run (`m = TP = TQ = 0`: halted with `[true]` at
    length `11`, live at `10`); **(b)** an immediately rejecting run (`[false]`); **(c)**
    `acc = rej` (the leaf emits `true`); **(d)** a stream longer than the budget (`m = 2`: every
    word shorter than `15` is live, so no budget below `15` accepts); **(e)** the zero-length
    choice word (the initial configuration); **(f)** a word longer than the halting time
    (absorption); **(g)** the stream read off the wrong bits (negative control `neg1`);
    **(h)** a noisy core without and with capture; **(i)** a run that halts with `[true]`
    without a verdict (the verdict hypothesis is load-bearing); **(j)** a nonblank cell just
    before the block (`hleft` is load-bearing); **(k)** a setup that halts at once; **(l)** `k`,
    `K` with `ι` onto (`cap ∉ range ι` unsatisfiable; the theorem is then vacuous, the consumer's
    choice `k = K + 1` is not); **(m)** a setup visiting `pexit` before `TP` (`hPfirst` fails: the
    host dispatches at the earlier visit).
12. **Documentation and policy** (`policy.md`): statement prose on every public declaration, the
    `[AB09, §2.1.2, proof of Theorem 2.6]` and `[AB09, Exercise 2.6]` tags, a literal
    `**Proof sketch.**` on every nontrivial theorem, the hand-built-leaf disclosure, 100-column
    lines, and the file-size WARN (1,064 lines; the user's standing decision: file size is not a
    driver). Duplication (failure mode 5): the two private helpers (a `Cfg.mapState` composition
    and a list split; no public equivalent found) and the proof of `guessRunCfg_clean`, which
    reads the private `embedSlot`'s body by `change`, as `SpaceComplexity/Inclusions.lean:726`
    does (open question 3).
13. Report anything else that the files, this pack or the design note misstate.

**Open questions (maintainer recommendations in italics).**
1. *The rewind inside the assembly*, at the price of `Build/NDHost.lean` importing
   `Build.Catalog`, or a rewind supplied by the caller inside the run? *Inside: ruling 2 asks the
   assembly to account for the rewind and to establish the core's precondition, which needs the
   stream head at `0`; the import changes nothing downstream.*
2. *UN's setup obligation* (probe 1's `hsetup`): a gated public row, or a fill obligation of UN's
   brief? *A fill obligation, stated in UN's brief verbatim as `hsetup`: it composes existing
   rows (the header's first component, `Turing.expandTM`, clears, the input rewind) and is not a
   host.*
3. *The capture tape's field of `embedSilentCfg`*: `guessRunCfg_clean` reads it through the
   private `embedSlot` body. *Request a shared lemma `embedSilentCfg_cap` (capture word and head,
   for `cap ∉ range ι`) in `Build/Embed`, beside the selected-field exports, at the next
   shared-file window (MIG-0b's landing, #90, added none); replace the `change` then.*
4. *The verdict leaf*: inline in `guessRunPhases`, or a catalog emit-and-halt row? *Inline: one
   transition, one consumer; register a row only if a second consumer appears.*

## Repository-side attestations (verify or challenge)

Source facts (checkable in the bundle) are separated from execution claims (the logs). Every
figure is MEASURED by the cited log unless marked ESTIMATE or INFERRED.
- **Base and snapshot** (`base.log`): the tip's tree extracted in full (717 files); 0 Lean files
  changed between `13a16a69` and the tip; the manifest unchanged; five tip sources elaborate
  against `oleans-lm0b` with 0 errors (MEASURED). That the snapshot equals the tip's Lean content
  up to docstrings is the B6 landing run's record (`<S>/land-b6r/LANDING-NOTES.md`), not
  re-derived here.
- **Elaboration** (`elaboration.log` §1): the unit, exit 0, **0 errors, 0 warnings** (MEASURED).
- **Cut check** (`cutcheck.log`): the tip's `Build/NDHost.lean` byte for byte, plus the
  `Build.Catalog` import, plus the part (1,046 lines), elaborated in `NDHost`'s import closure
  (`Build.Seam`, `Nondeterministic`) plus `Build.Catalog`, not importing `Build.NDHost`: exit 0,
  0 errors, 1 warning, the existing `declaration uses 'sorry'` of `ndWriterTM_run_block`
  (MEASURED). The landing form (1,064 lines): the same (MEASURED).
- **Freeze** (`freeze.log`): the landing form's code is the tip's code plus one import line
  plus the part's code; the tip's text after its module docstring (137 lines) occurs
  verbatim; the six existing declarations come first, in order (MEASURED).
- **Axioms** (`axioms.log`): every new public declaration and the two derived instances printed;
  `sorryAx` appears exactly on the six theorems that pass the writer and on
  `ndWriterTM_run_block`; `guessRunTM_runWith_setup_halt` and `guessRunCfg_clean` use at most
  `propext`, `Classical.choice`, `Quot.sound` (MEASURED). **Isolation** (§2): with the writer's
  contract and the core's contract replaced by axioms with their statements verbatim, no
  `sorryAx` remains: the unit's theorems rest on the writer's contract only, probe 1 on both
  contracts, probe 2 on the writer's (MEASURED). The isolation files use `axiom` declarations
  (evidence only, never landing material).
- **Sanity probes** (`elaboration.log` §2): 16 `example`s, 0 errors; four negative controls
  (the stream read early, the captured output claimed noisy, an early halt, liveness at the
  handoff time) each fail (MEASURED).
- **Consumer probe** (§3): 0 errors; both derivations' axioms as above (MEASURED).
- **Names** (`names.log`): the unit's 20 declarations plus 8 generated names (two derived
  instances, six constructors) against 16,926 names of 716 `TCSlib` files at the tip and 298
  pending units, drafts and open-PR files (every `*.lean.txt` under `audits/evidence/`, the
  scratchpad units of the MIG-1, ARM and B6 gates, and the landing trees of PRs #92 and #93):
  0 clashes; a positive control with two planted clashes catches both;
  short-name overlaps are constructor names and one instance name in other namespaces (MEASURED).
  Downstream of `Build.NDHost`: the facade only, which has `Build.Catalog` (MEASURED from the
  import graph).
- **Cited names** (`elaboration.log` §7): the population is every plain-identifier backticked
  token in the unit's comments, found lexically, with no further filter: 78 tokens, 41 do not
  resolve (MEASURED); all 41 are bound variables, module names, the constructor `done` or the
  core's local `start` (maintainer classification).
- **Widths, lint, forbidden constructs** (§4–§6): no line over 100 characters; the campaign
  lint over the landing form, 0 FAIL, 1 WARN (the file is 1,064 lines, over 1,000); no `#eval`,
  `run_cmd`, `IO`, `unsafe`, `implemented_by`, `extern`, `native_decide` or syntax commands
  (MEASURED).
- **Sizes**: the unit 896 lines, the part 849, `Build/NDHost.lean` 195 → 1,064 (MEASURED).
- **UN's setup obligation is buildable from existing rows in `O(t + 1)`** (INFERRED; not
  elaborated).
- **Nothing in the repository was changed** (`elaboration.log` §8: `git status` of `wt-c1asm` with
  optional locks off, clean; git ran read-only: rev-parse, ls-tree, diff, archive to stdout); no
  lake or elan command was run; `lean` ran only through `tools/leanelab.sh`, which
  writes no olean; Python only as `python3 -I` (process claims, not independently checkable).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into
`audits/c1-assembly-statements-findings.md`. The gate closes when a round reports zero blockers
and zero majors; the part then lands appended to `Build/NDHost.lean`, with the import and the
docstring edits of the landing form.
