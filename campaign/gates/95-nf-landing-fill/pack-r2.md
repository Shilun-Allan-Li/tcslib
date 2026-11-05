# External audit pack, round 2: NF's landing, the linear normal form (PR #191, a fill gate)

**Round 1** (`pack.md`; findings `findings.md`; resolutions `resolutions.md`) was **does not close,
0 blockers, 1 major, 4 minors, 4 notes**, with no soundness defect in
`exists_codeNDTM_accepts_linear`. The major was three inline re-derivations of `BufferWords`
identities. **Ruled (user, 2026-11-05): repair in #191, round 2.**

**The PR now:** #191 on `lean/c1-nf-landing`, head `ac934f99cc5d5009b8027fc0516ab2fd5be0042d`:
- `10c015177fde0f9f2b020c010cf44f0f3b3dd37f`, the repair (`evidence/round2/patches/`), which changes
  only `TCSlib/Complexity/ClassNP/NDNormalForm.lean`;
- then a merge of the campaign, which changes no `.lean` file (the campaign's commits since the
  round-1 head are records and tools only).

## What changed since round 1 (verify)

| Finding | Change |
|---|---|
| 1, `nf_bClear`'s `hw` | `rw [h, FinTM.bufferTape_drop R i h0, add_comm]` in place of the `bufferTape_nat`/`List.getElem?_drop`/`congr 1; omega` steps |
| 1, `nf_aReturn`'s `hw` | `FinTM.bufferTape_eq_none_of_not_mem s (z := (s.length : ℤ)) (by omega)`, then `FinTM.bufferTape_nil` |
| 1, `nf_region`'s cell `\|R\|` | `rw [hpL, FinTM.bufferTape_eq_none_of_not_mem]`, its side condition by `List.length_ofFn` and `omega` |
| 2, the seal and the axioms | regenerated on the repaired blob, with candidates at its seven imports (`evidence/round2/seal/`, `evidence/round2/axioms/`); the plain elaboration log is shipped (`evidence/round2/elab/`) |
| 3, `nf_pack`'s `hinit` | `(Cfg.mapState_eq_of_fields _ e _ …).symm`, the five field goals by the `Cfg.init_*` equations, as `nf_tag` |
| 4, the headline's docstring | the proof sketch follows the implemented route; "Fill obligations, named: …" is gone; docstring only |
| 5, the evidence | the screen with `TuringMachine/BufferWords` in the population (`evidence/round2/screen/`); the sweep with the buffer, `runFrom_add` and time-split patterns, a disposition per hit (`evidence/round2/sweep.md`) |
| 9, the ledger | `campaign/duplication-ledger.md`: RN-1's accounting, the major's record, RC-4 (both first-halt sites; `canonStageBuffer_none` for 12.2c), one numbering for F2 and F8 |

No other line of the owned file changes since round 1's head (`evidence/round2/freeze/`:
`declfreeze.py` gives 1 → 1 public and 103 → 103 private declarations, no addition or removal, no
statement change; bodies changed: `nf_pack`, `nf_aReturn`, `nf_bClear`, `nf_region`, and the
headline's docstring).

## Brief for the auditor

1. **Findings 1 and 3:** are the re-proofs correct and statement-preserving? Do they read other
   files' definitions only through published lemmas (rule 10)?
2. **Further re-derivations.** Round 1's major was inline sub-steps. Does any other inline step
   re-derive a lemma in the closure? The round-2 sweep lists every hit with a disposition; the
   nine time splits of finding 5 (thirteen lines, four nested) are dispositioned as idioms over
   windows that are not `Segment`-typed. Challenge any.
3. **Finding 4:** does the headline's sketch now describe the code?
4. **Findings 2, 5 and 9:** are the evidence and the record corrections right?

## Repository-side attestations (verify or challenge)

- **Elaboration:** the repaired file elaborates against the snapshot `oleans-cloud0` (the campaign
  at `dfed8b1f`'s Lean tree) with **no output** (`evidence/round2/elab/NDNormalForm.elab.out`,
  empty; `lean` exit 0).
- **Rule 10** (`evidence/round2/seal/`): the review's generator re-run on the repaired blob, with
  the candidates taken at its seven imports: **277 definitions**, the Lean audit's list identical to
  the textual one (19 new from `Build/Contract/Basic`, among them `Turing.Segment` and
  `Turing.HeadBox`, and `Turing.FinTM.stateEquivFin`). Both sealed copies, round 1's placement
  (`NFSeal`) and the whole file (`NFSealWhole`, which also covers `nf_pack`), elaborate with **0
  diagnostics**. Generic controls: 277 unsealed (`rfl` 267, equation 276), 5 sealed; source controls
  (round 1's 41 plus `Segment` and `HeadBox`): 43 close unsealed, 43 fail sealed. All 277 are
  discriminated (`summary.txt`: 272 by the generic controls, the 5 derived instances by source
  controls).
- **Axioms** (`evidence/round2/axioms/`): `NFAx` on the repaired blob:
  `exists_codeNDTM_accepts_linear` on `[propext, Classical.choice, Quot.sound]`; `nf_Ph`'s derived
  instances on subsets. `NTHAx` on the merged tree (`oleans-lnf2`): all seven theorems (the normal
  form, the diagonalizer, the timed universal NDTM, the decider, and `ntime_hierarchy`,
  `ntime_hierarchy_of_pos`, `NTIME_linear_ssubset_square`) on
  `[propext, Classical.choice, Quot.sound]`.
- **Screen** (`evidence/round2/screen/`): the bundled wrapper over the 22-file population plus
  `TuringMachine/BufferWords` at the repaired head: 1,444 declarations, 13 pairs, 5,191 characters;
  `pairdiff.py` against the round-1 run: 0 new, 0 gone. The one changed pair (`nf_bClear` against
  `nf_aReturn`, 57% → 56%) lost the hand-written buffer indexing the repair removed.
- **Replay:** `replay-lnf2` (`evidence/round2/merged-tree/`) covers `NDNormalForm`, `ClassNP`,
  `NTimeHierarchy` and `Diagonalization`, chained from `oleans-cloud0`: **4 modules, 0 failed, 0
  `sorry`**; the static check 0 mismatches.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/95-nf-landing-fill/findings-r2.md`. The gate closes when it has zero blockers and
zero majors.

**Deliver your findings as a downloadable Markdown file named `nf-landing-fill-r2-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
