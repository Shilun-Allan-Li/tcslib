# External audit pack — MIG-0b: the contract structure's second increment (statements and proofs)

Campaign: the foundation migration (design `machine-library-design.md` §16, §16a; backlog MIG-0).
MIG-0a, the framed-contract structure `Turing.Contract` (`Build/Contract.lean`), closed at round 2;
its landing PR (#83) has passed its replay. Round 1's major showed that a first-exit `Contract` does not directly replace
three kinds of existing specification: `CfgRecord`'s `RecordRun` segments, the return-or-escape
rounds, and `CounterLoop`'s joint head relation. So **MIG-0b** was redefined to supply them
before any dependent migration (MIG-12 to MIG-17). Round 2 recorded acceptance obligations for
MIG-0b (design §16a, *MIG-0a gate, round 2*; `audits/mig0a-r2-findings.md`, notes 3–4).

**This gate audits MIG-0b's statements and proofs together.** A maintainer sub-agent wrote the
draft, and the maintainer re-elaborated it. It is nearly all proved: one `sorry` remains, the
existence of the alphabet-reduction lockstep, which needs a private simulator exported (open
question 10). It has not landed. Landing is a Lean PR carrying out the layering split, with its
own replay.

**Bundle:** `audits/mig0b-bundle.md`. It holds:
- this pack and the standards;
- the MIG-0a records: both rounds' findings, the resolutions, and the gated round-2 file
  `audits/evidence/mig0/Contract-proposed-r2.lean.txt` (the landing PR changes only its status
  paragraph);
- the draft `audits/evidence/mig0b/Contract-mig0b-draft.lean.txt`, whose first 1,099 lines are
  the gated MIG-0a file byte for byte (checked), followed by the MIG-0b section;
- the adapters file `Contract-mig0b-adapters.lean.txt` (the same text plus `SymbolLift` and
  `CounterLoop`, and the symbol-lift and counter-loop adapters), and the layering probe;
- the notes `NOTES.md`: the declarations and the rows they serve, the fit tests, the R1 lemma's
  consumers, the layering plan, the tactics, 14 open questions, sizes, and record errors;
- the elaboration and axiom logs, the design document and the backlog;
- every Build or core file whose rows the layers must fit, or whose lemmas move.

## What the draft states (verify)

1. **The segment layer.** `Segment`: an exact length, which may be zero; an explicit endpoint
   configuration; an inclusive envelope; and a relation on the head vector. It has concatenation
   (`trans`, `cons`), `mono`, `take`/`drop`, `live` and `time_eq`. `SafeSegment` adds avoidance
   through the endpoint. The bridges are `Contract.segment` and `Contract.ofSegment`.
2. **The round layer.** `Round` and `RoundContract`: a positive time, an interior that is live and
   off both the anchor and the escapes, and either endpoint. With them come `roundOrbit`,
   `Round.iterate`, the `returning` and `escaping` cases, `ReturnContract.toRound` and
   `RoundContract.release`. **The counter loop over rounds** is proved as contract-to-contract
   theorems (`RoundContract.counterLoopDone`, `counterLoopEscape`) from the public
   `counterLoopTMVia_run_done` and `_run_escape`. The `_witness` and `_traj` theorems keep the
   shared round-and-offset witness for all body heads.
3. **The joint-trajectory layer.** `Contract.Traj`, preserved by `trans`, `seq`, `inPhase`,
   `embed` and `branch`, all proved; also `Frames.trans` and `Frames.seq`.
4. **The layering split, planned** (`NOTES.md` §6). The core imports only `Simulation`,
   `StateRenaming` and `Linarith`, so `Loop` and `CounterLoop` can import it; the probe confirms
   this. Two lemmas move down first: `spaceUsedByTape_le_card_Icc` (from `Catalog` to
   `Deterministic`) and `runFrom_mapState_of_agreeOn` (from `Build/Embed`, where it actually
   lives, to `StateRenaming`).
5. **The R1 reconstruction lemma** `embedEmitCfg_eq`, with `_mapState_eq` and `_ofWords_eq`. This
   is the wave-1 gate's acknowledged major F1: the user scheduled its resolution in MIG-0b.
   `oracleBankCfg_eq`, `canonEmbedEq` and `emCall_exit_fixed`'s local `hframe` are each proved
   from it in one term. The notes find the family larger: `counter_layout`, `canonEmbedWords`,
   `cert_embed_words` and `embedEmitCfg_select`. The silent flavour (`cert_silent_words`) needs a
   capture-field export.
6. **The pointwise release export** `seamReleaseTM_runFrom_pos`.
7. **Transports:** `Contract.mapState`, `Contract.liftSymbols`, `Lockstep` and `Contract.lockstep`
   (with a variable cost per step), all proved. The contract-to-contract alphabet-reduction
   theorem is proved from its lockstep's existence, which is the one `sorry`.
8. **Sanity lemmas:** `time_eq_zero_iff`, and positivity of `trans`, `seq`, `inPhase`, `branch`,
   `embed` and both releases.
9. **Tactics:** described, not implemented (`NOTES.md` §7).

## Brief for the auditor

1. **Round 2's obligations** (`audits/mig0a-r2-findings.md`, notes 3–4, and design §16a). Check
   each against the draft:
   - zero-length segments, the inclusive envelope and the configuration seam;
   - `counterSpan` as a segment with its zero-time case;
   - `splitSafe` as an endpoint-inclusive `SafeSegment`; the notes add that `SafeRun` avoids only
     strictly before the endpoint;
   - the joint trajectory for general segments, with the counter loop's shared witness, exact
     endpoints, bounds and liveness;
   - the live round interior.
2. **Fit with the rows.** Using the attached files, check that `RecordRun`/`recordRun_trans`,
   `rt_find_round_entry`, `counterSpan`/`counter_rounds`/`counterLoopTMVia_run_*`, `splitSafe`,
   `SafeRun` and `DGSpan` are each expressible, as the notes claim.
3. **Each statement's strength.** For each new layer, composition and transport: are the
   hypotheses necessary, and is the conclusion the strongest natural one? Rule on open questions
   1–6 and 12–13 (time-independent relations, `SafeSegment` as a conjunction, liveness in the
   cut, a constant round index, a general positive-cut contract, the lockstep index, the
   data-dependent envelopes, the frames and trajectories not yet drafted).
4. **The R1 reconstruction lemma.** Does it serve the whole family, including the members the
   notes add? Is the silent flavour's deferral right (question 9)?
5. **The layering split.** Check the planned modules, the two lemmas moving down, and the probe;
   rule on questions 7–8 and 14.
6. **The `sorry` and question 10.** Is deferring the alphabet-reduction lockstep's existence to
   RS-5 (exporting `arTM`, `arCfg` and `arCfg_cycle`) acceptable at this gate?
7. **Proofs.** The draft is kernel-checked per the logs. Check the fit-test proofs (the bridges
   and instances), and that the prefix is the gated MIG-0a file unchanged.
8. **Records.** Check the record errors the notes list (§10), and what the maintainer corrected
   (backlog MIG-15, MIG-17, RS-3; design §16a), against the code.
9. **Documentation and policy:** docstrings, literal proof sketches, attribution, 100 columns.
10. Report anything else the draft or its records misstate, in the standard table.

## Repository-side attestations (verify or challenge)

* **Elaboration** (`audits/logs/mig0b-elaboration.log`): the draft, the adapters file and the
  layering probe each give 0 errors and one `sorry` warning (the alphabet-reduction lockstep).
  The maintainer re-elaborated all three independently, with the same counts.
* **Prefix:** the draft's first 1,099 lines are the gated MIG-0a file byte for byte, checked by
  the drafter's script and by the maintainer.
* **Axioms** (`audits/logs/mig0b-axioms.log`): 120 public declarations; only the two
  alphabet-reduction ones depend on `sorryAx`.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into `audits/mig0b-findings.md`.
The gate closes when it has zero blockers and zero majors.
