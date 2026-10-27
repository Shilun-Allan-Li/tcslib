# External audit pack — the controller-stopped writer and one guess-then-run host (PR #174, an API gate)

**Why this PR.** The linear normal form `Turing.FinNDTM.exists_codeNDTM_accepts_linear`
(`ClassNP/NDNormalForm`) is one of the two contracts the nondeterministic time hierarchy rests on.
Its route (`campaign/items/c1/nf/NF-route-design.md`) guesses a display of one record per step of
the simulated machine, a word of unknown length, and then verifies it deterministically.
`Turing.guessRunTM` composed only the bounded choice writer, whose block length the setup fixes
before the guess. The controller-stopped flavor of `Turing.ndWriterTM` had a definition and no
contract (its statement was drafted on 2026-10-17, `campaign/items/c1/nf-writer/`, and never
landed). **The user ruled (2026-10-27), NF's D1 (A) and D2 (A):** the maintainer proves the
contract, and adds a controller-stopped guess-then-run host in `Build/NDHost`, in this PR.

**Two rounds before the gate.** The first version added the host beside `guessRunTM`. Its screen
(`evidence/round0-additive/`) found the new host reproducing `guessRunTM`'s definitions (84–100%)
and proofs (87%): 18 of the file's 45 declarations in one family. **The user ruled (2026-10-27) to
generalize:** one host over the writer, proved once, with `guessRunTM` its instance and every public
statement unchanged. The writer's two contracts were then also derived from one lemma.

**The PR:** #174 on `lean/nf-ndhost-api`, head `1045624da9ab88719214b3b9e5b347a8f436994b`, on the
campaign tip whose Lean is the tree after #172 (`d07187db`; the campaign's records merged in by
`448f713e`, no Lean change). `evidence/patches/` has the nine commits from `d07187db`; the last
three are the design as it stands:
- `172bed84`: one host over the writer; `guessRunTM` and its families its instances; the handoff
  and the rest of a branch proved once;
- `6ad2bfd4`: proof sketches for the three private general lemmas;
- `1045624d`: the writer's prefix induction and first stop proved once; both contracts their
  instances.

## What changed (verify)

| Class | Declarations |
|---|---|
| **The general host** (new public) | `Turing.GuessRunPhase.CtlState` and its `Fintype` and `DecidableEq` instances; `Turing.guessCtlRunPhases P j q₀ δ stop bounded V`; `Turing.guessCtlRunRed`; `Turing.guessCtlRunTM P pexit j q₀ δ stop bounded V qentry acc rej` |
| **Now its instances** (statements unchanged, bodies changed) | `Turing.GuessRunPhase.State`, `instFintypeState`, `instDecidableEqState`, `Turing.guessRunPhases`, `Turing.guessRunRed`, `Turing.guessRunTM` (the bounded writer, the trivial controller) |
| **Re-proved as corollaries** (statements unchanged) | `guessRunTM_runWith_handoff`, `guessRunTM_runWith` (of the private general lemmas); `ndWriterTM_run_block` (of the private first-stop lemma) |
| **New public** | `Turing.ndWriterTM_run_controller`; the controller-stopped instance's `guessCtlRunTM_runWith_handoff`, `_runWith`, `_stop_of_halted`, `_accepts_of`, `_stream_of_accepts` |
| **Private** | added: `gr_writer_end`, `gr_handoff`, `gr_runWith_of_handoff` (the host's handoff and the rest of a branch, for any writer whose run on the stream is given), `wr_prefix_gen`, `wr_run_first_stop` (the writer's prefix induction and first stop, for any controller and flavor), `wr_prefix_controller`; changed: `wr_cfg` (a writer-state parameter), `wr_cfg_nil`, `wr_cfg_scan`, `wr_cfg_stepWith` (any `δ`, `stop`, `bounded`), `wr_prefix` (an instance) |
| **Unchanged** | `guessRunTM_runWith_live`, `_handoff_state`, `_setup_halt`, `_haltsWithin`, `_accepts_iff`, `guessRunCfg_clean`, `guessRunTM_silent_spec`, `guessRunCfg`, `streamStartCfg`, and the phase host |
| **Frozen** | every public signature: 25 → 37 public, none removed (`evidence/freeze-NDHost.txt`, `freeze-note.txt`) |
| **Text** | the module header and the two section docstrings for the one-host design; `guessRunTM_silent_spec`'s stale "proved modulo the writer" corrected (its axioms are the standard three) |

## Brief for the auditor

1. **The writer.** Is `ndWriterTM_run_controller` the right public form? It is stated along one
   word `w` with its first stop `m` (`m < |w|`, no stop before `m`, a stop at `m`), because the
   controller's trajectory depends on the bits; its second clause covers the prefixes of `w` up to
   `m`, not every word. The written cells are those of `w.take m`; the writer ignores what they
   held. Both contracts are instances of the private `wr_run_first_stop` (a stop by the controller
   or, bounded, by a blank cell). Is `ndWriterTM_run_block`'s statement unchanged and its new proof
   sound (its "no shorter word" clause, over every word, comes from `wr_prefix`)?
2. **The host and its instances.** Is `guessCtlRunTM` the right general shape, and is
   `guessRunTM` exactly its bounded, trivial-controller instance? `GuessRunPhase.State SP SQ` is
   now `GuessRunPhase.CtlState SP SQ Unit`, and its instances delegate to the general ones. Do any
   consumers depend on the old definitional shapes? `NTimeHierarchy` cites `guessRunTM`,
   `guessRunTM_silent_spec`, `ndWriterTM_run_block`, `GuessRunPhase.State`, `phaseHostND` and
   `streamStartCfg` with its field lemmas, by statement; the replay re-elaborates it.
3. **The controller-stopped instance's lemmas** (`bounded := false`, over a tape blank from the
   setup's head on, `hblank`, and just before it, `hleft`):
   - `_runWith_handoff`: the time `TP + 2m + 9`, the stream `(w.drop (TP + 1)).take m`;
   - `_runWith`: the whole branch, halted by `TP + 2m + TQ + 11`, the output the run's followed by
     the verdict bit;
   - `_stop_of_halted`: a halted branch has a first stop `m` with `TP + 1 + m < |w|`, using only
     the setup's run to its exit. Is the liveness argument right in both cases (still in the
     setup; still in the writer)?
   - `_accepts_of`, `_stream_of_accepts`: forward at every budget beyond the branch's time, and
     backward under `hV` (every stream that first stops the controller at its end reaches a
     verdict); the backward direction pads the accepting word and uses absorption. Is any
     hypothesis stronger than a consumer can meet, or vacuous? Check the edge `m = 0` (an
     immediate stop: an empty stream).
   - There is no all-branch halting lemma, on purpose: a stream that never stops the controller
     never ends the guess, and NF claims no halting.
4. **Rule 10** (the scope of 2026-10-23). The changed code is sealed in five regions, each its own
   section (the writer's helpers and contracts; the three private general lemmas; the bounded
   handoff; the bounded whole branch; the controller-stopped instance's section), over 17 other-file
   TCSlib definitions, with the four `@[simp]` ones erased (`evidence/NDHostSealed.*`, generator
   `evidence/scripts/mkseal_nf2.py`): 0 diagnostics. Unchanged declarations stay outside every seal.
   - The controls (`evidence/NDHostSealControl.*`): 16 `rfl` controls and 4 `simp` controls close
     unsealed (20 `PASS` messages) and fail sealed; the recursive `NDTM.runWith` has a usage
     control instead (`runWith [b] c = stepWith b c`), which closes unsealed and fails sealed: 21
     sealed failures, each at its own line.
   - The `simp`, `rw` and `unfold` arguments of the sealed regions name no other-file definition
     (those named are this file's: `ndWriterTM`, `guessCtlRunPhases`, `guessCtlRunRed`,
     `NDTM.phaseHostND`, `guessRunCfg`, `wr_cfg`). The renamings are read through their `simps`
     field lemmas (`StateRenaming`), the start through `NDTM.initCfg_eq`,
     `MultiTapeTM.initCfg_eq` and `Cfg.init`'s fields, the step through `NDTM.stepWith_of_some`.
   - The unchanged bounded lemmas (2026-10-17) still unfold `Cfg.mapState` and `NDTM.stepWith`;
     they predate the rule and are not in this PR's scope.
5. **Duplication.**
   - **The API-copy search** (`evidence/api-copy-search.txt`): no branch, local landing or
     delivery has the new statements.
   - **The text screen** over a 14-file population (`evidence/screen/`; base the tip's tree at
     `940671e0`, head `1045624d`): 1,027 → 1,040 declarations, 732 → 738 pairs; 10 new, 4 gone
     (`pairdiff.txt`). The maintainer's dispositions:
     - **Moved, not new (4 new, 4 gone):** the instance boilerplate of the state family's
       `Fintype` and `DecidableEq` instances, paired with each other and with `ExhaustiveReplay`'s
       `xr_PhSt_fintype` and `xr_PhSt_decEq` at the base, now attaches to the general family's
       instances (`instFintypeCtlState`, `instDecidableEqCtlState`), which the bounded instances
       delegate to.
     - **Citation idiom (1):** `gr_handoff` against `InputRewind`'s `Cfg.mapState_mapState`
       (56%, 224 characters): the handoff cites it at every phase boundary.
     - **Invocation idiom (5):** the two instances of each general lemma call it the same way:
       `guessCtlRunTM_runWith` and `guessRunTM_runWith` (79% and 60%, 432 characters: the stream
       equation and the call of `gr_runWith_of_handoff`), `guessRunTM_runWith_handoff` and
       `guessCtlRunTM_runWith_handoff` (69% and 51%, 301 characters: the writer's start and the
       call of `gr_handoff`), and `ndWriterTM_run_block`'s no-shorter-word clause against
       `wr_prefix` (75%, 116 characters: the bounded instance of `wr_prefix_gen`).

     The first round's family (`round0-additive/pairdiff.txt`: 27 new pairs, the second host's
     definitions at 84–100% and its proofs at 87%) is gone. Are these dispositions right?
   - **Semantic:** does any new lemma re-derive a published one? Is the general host the right
     resolution of the first round's family?
6. **Records.** Are the new docstrings, the module header and the section docstrings accurate and
   public-facing?

## Repository-side attestations (verify or challenge)

- **Elaboration** against `oleans-lhh` (the snapshot of the tree after #172):
  - the head module with sixteen axiom prints appended (`evidence/NDHostAx.*`): 0 diagnostics;
    every theorem of the host family (the two contracts, the bounded host's nine lemmas, the
    controller-stopped instance's five) on `[propext, Classical.choice, Quot.sound]`;
  - the sealed copy: 0 diagnostics.
- **Freeze** (`declfreeze.py` v4, `evidence/freeze-NDHost.txt` and `freeze-note.txt`): 25 → 37
  public, 7 → 13 private. Its "STATEMENT CHANGED" lines for the five definitions written by pattern
  matching are an artifact (it counts their match arms); their signatures, and `guessRunTM`'s, are
  identical when compared up to the body.
- **Lint:** `TuringMachine` 0 FAIL, 68 WARN over 85 files, as at the base; only `NDHost`'s lines
  change: its size (1,256 → 1,954 lines) and check 8's list, where the general state family,
  phases and redirects join their instances, which carried the same warning
  (`evidence/lint-*-TuringMachine.txt`). The policy linter `scripts/style_lint.py`: the base's
  one finding, the size line (`style-lint-*-NDHost.txt`). No line over 100 characters.
- **Replay:** `NDHost`'s downstream closure, 4 modules (`evidence/merged-tree/down-lnfapi3.txt`:
  `NDHost`, `NTimeHierarchy` and the `Diagonalization` and `TuringMachine` facades), chained from
  `oleans-lhh`, pinning the head's blob `958b6ee4`: **passed** (the user, 2026-10-27), 4 of 4
  modules at `1045624d`, 0 failed, static-equal (0 mismatches; `replay-lnfapi3.log`,
  `replay-lnfapi3-static.txt`). The first round's replay passed at `248aecec`
  (`evidence/round0-additive/`).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `campaign/standards/TEMPLATE.md`. Findings go verbatim into
`campaign/gates/85-nf-ndhost-api/findings.md`. The gate closes when it has zero blockers and zero
majors.

**Deliver your findings as a downloadable Markdown file named `nf-ndhost-api-findings.md`** (the
findings table and the verdict line, no other wrapping), and also paste its content in your reply.
