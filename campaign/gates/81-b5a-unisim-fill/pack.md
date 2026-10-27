# External audit pack — B5a, the uniform simulator (PR #170, a fill gate)

Campaign: the Arora-Barak chapters 3-4 plan, B5a's H1 ([AB09, §1.4.1, Theorem 1.9, time-bounded
form; Example 3.6(3)'s uniformity]): `Turing.MachineFormat.exists_uniformSimulator` in
`TCSlib/Complexity/TuringMachine/CodeSimulator.lean`, one finite binary machine and one degree,
uniform in the code, answering bounded acceptance within `d · (|α| + |x| + t + 1)^d`.

- **The brief:** `campaign/fills/b5a/drafts/b5a-fill-unisim.DRAFT.md`, rewritten on 2026-10-27
  against the interpreter startup `Turing.exists_interpreterStartup` (PR #169, gate 79), which it
  cites at `p = F.k`. Its pre-ship: `campaign/fills/b5a/drafts/b5a-fill-unisim/preship-9d0af8cb/`
  and the junction's `preship-junction/`. It was never issued.
- **The proof:** assembled by the review of that brief
  (`campaign/fills/b5a/reviews/unisim-rewrite/REVIEW.md`; the assembly
  `probe/B5aReviewAssembly.lean.txt`). Its verdict: "issue after edits", and its decision D1 noted
  that the target was already proved.
- **The user's ruling (2026-10-27): D1 = (A),** land the review's proof by a maintainer PR with a
  fill gate and the downstream replay.

**The landing:** PR #170 on `lean/b5a-unisim-landing`, head
`101434fd2114a82436a44e5ac3f374c978290399` (the campaign merged in; no Lean change from it). The
three commits on the campaign tip, whose Lean is the tree after #169 (`evidence/patches/`):
- `1a508123`: the review's assembly as the owned file, without its trailing axiom prints;
- `3decc87b`: `CodeSimulator`'s module status and the target's docstring, rewritten (docstring
  only);
- `4ce6587c`: the status text of `Codes2Tape`, `EXPCOM` and `Relativization`, which said these
  results were proved modulo the simulator (docstrings only).

## What changed (verify)

| Class | Declarations |
|---|---|
| **Target proved** | `Turing.MachineFormat.exists_uniformSimulator`, with no `sorryAx` |
| **Privates** | 185 → 196 in `CodeSimulator`: 11 new `us_` declarations (`us_install`, `us_locality`, `us_verdict`, `us_table_le`, `us_window_verdict`, `us_ledger`, `us_bank`, `us_junction`, `us_tail`, `us_start`, `us_run`), at the home before `end StepBlockClients`; none removed or changed |
| **Frozen** | every public statement (12 → 12); the target's statement; two imports added (`Nondeterministic`, `Build/InterpreterStartup`) |
| **Text** | the target's docstring (its sketch rewritten to the startup route, an `**Implementation.**` paragraph, the dated fill appendices removed); `CodeSimulator`'s status paragraph; the status lines of `Codes2Tape`, `EXPCOM` and `Relativization` (`evidence/codeonly-docstring-files.txt`: code identical) |

## Brief for the auditor

1. **Faithfulness.** Does the proof establish the frozen statement, with `S` and `d` chosen
   before `α`, `x`, `t` (the wave-1 statement gate's note 34: per-code constants would not
   suffice for `EXPCOM`)? Check the edge cases: `t = 0` (the answer `[false]`), `|x| < t`,
   `α = []`, `x = []`, and a code decoding to the format's fallback.
2. **The route.**
   - The installer `us_install`: the polynomial canonizer through `FinTM.exists_installCallTM`.
   - The startup cited at `p = F.k`: its arguments, the reserved tapes started blank, and its
     first-arrival cut.
   - The tape map `us_bank`, and the junction `us_junction`: the threshold, relabelled, as the
     embedded `vhostCfg (counterLoopCfg (some (.dec .run)) d (bufferTape t.bits) 0)` start, with
     the `Rep` on the window.
   - `us_tail`: the seam into `embedEmitTM g (h1HostedVerdictTM F.k)`.
   - `us_start` and `us_run`: the restart at `Sum.inl entry`.
   - `us_window_verdict` with `us_locality`: the window `x.take t` to `x`.
   - `us_verdict` and `us_ledger`: the degree, from the startup's bound, the installer's
     polynomial, `us_table_le` and the hosted verdict's `t · 50 (|table| + 1) + 4t + 2|bits t| + 3`.

   Is the ledger's `d` uniform? Does any step use the startup's internal scratch?
3. **Rule 10** (with the scope of 2026-10-23). The review's seal covers 28 other-file
   definitions and erases the three `@[simp]` ones among them; all 28 controls fail sealed and
   close unsealed (`probe/B5aReviewAssemblySealed.lean.txt`, `probe/B5aReviewSealControl.lean.txt`,
   `out/`). Does any step close only because another file's definition reduces? Is any
   other-file definition passed to `rw`, `simp` or `unfold`? `h1HostedVerdict_effect` predates
   rule 10 and is cited, not imitated.
4. **Duplication.**
   - **The text screen:** the brief's 57-file population, base at the tree after #169
     (`preship-9d0af8cb/screen-base.txt`), head at `1a508123`
     (`landing-1a508123/screen-head.txt`, `pairdiff-head-vs-base.txt`). There are 24 new pairs
     and none gone, none at 90%.
     - **Disclosed:** `xr_E_initCfg` (`ExhaustiveReplay`) and `un_setup` (`NTimeHierarchy`)
       reproduce `us_start` at 89%. With `UniversalK`'s private `uk_init_mapState`, that makes
       four private variants of the restart identity, a promotion candidate.
     - The others are idiom pairs: `Cfg.ext` with field equations, `sl_rewrap`, and the
       canonizer's legs.

     Is each correctly classified? Should the identity be published before this lands?
   - **Semantic:** do the `us_` lemmas re-derive published API (`initCfg_with_q₀`,
     `embedEmitCfg_eq`, the seam's run lemmas, `Cfg.mapState_mapState`)?
5. **The maintainer's text.** Is the `**Implementation.**` paragraph an exact reading of the proof,
   and the sketch accurate? Are the downstream status lines true? In particular, are targets 3–8
   (`Turing.exists_uniformMachineCode2`, `Turing.exists_uniformMachineCode`,
   `Complexity.EXP_subset_POracle_EXPCOM`, `Complexity.POracle_EXPCOM_eq_EXP`,
   `Complexity.NPOracle_EXPCOM_eq_EXP`, `Complexity.POracle_EXPCOM_eq_NPOracle_EXPCOM`) and
   `Complexity.baker_gill_solovay` now admission-free? (The review's admission walk found the
   target their only admission; the replay's axiom prints settle it.) The text must be
   public-facing: no campaign labels, paths or dates in new text.
6. **Records.** Any correctness gap in the review's minors F2–F8, which concern the brief that was
   not issued, as they bear on this landing.

## Repository-side attestations (verify or challenge)

- **Elaboration:**
  - the review's assembly, against `oleans-laplusm` (the tree after #169), with 0 diagnostics;
    re-run by the maintainer with the same result;
  - the PR head's `CodeSimulator` with the 12 axiom prints appended, with 0 diagnostics
    (`evidence/elab-CodeSimulator-head-ax.out`).
- **Axioms:** the target and all 11 privates on `[propext, Classical.choice, Quot.sound]` (two of
  them on fewer).
- **Freeze** (`evidence/freeze-CodeSimulator.txt`, `declfreeze.py` v4, base against head): 12 → 12
  public; the one authorized body change; 11 privates added.
- **Lint** (`evidence/lint-head-*.txt`): `TuringMachine` 0 FAIL, 68 WARN over 84 files, the same
  as the base but for `CodeSimulator`'s size line (8,666 → 9,126); `Diagonalization` 0 FAIL, 2 WARN
  over 5 files. No new line over 100 characters.
- **Replay:** `CodeSimulator`'s downstream closure, 10 modules (`evidence/merged-tree/`), chained
  from `oleans-laplusm`, with the axiom prints of targets 3–8 and Baker–Gill–Solovay against its
  snapshot. **Pending** (the gate is dispatched before it).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `campaign/standards/TEMPLATE.md`. Findings go verbatim into
`campaign/gates/81-b5a-unisim-fill/findings.md`. The gate closes when it has zero blockers and zero
majors.

**Deliver your findings as a downloadable Markdown file named `b5a-unisim-fill-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
