# Gate 132 round 3 · `MultiTapeTM.runFrom_one` in Deterministic, cited at one-step sites (PR #296)

**Not yet clear to merge** · PR #296 is a draft. Seyoon dispatches and merges.
The current Lean commit is `befb73f97a63ce449fe1a9a1b7dfc3fdbda65969`, against campaign Lean `7b6bd1685a1436313dfbc13ce191f40c7dd065d3` (the campaign after #242).
Round 2 audited `ce427bde6ee5464a4146dce2b3add69b7a05677d` and returned HOLD with one minor,
G132-04 (`findings-r2.md`, verbatim). It found round 1's three minors resolved. This round checks
G132-04's resolution (`resolutions-r3.md`), the round 2 records it corrects, and the census that
closes the blind spot behind it. Dedup family RO-1; Seyoon ruled the home `Deterministic` on
2026-11-12.

## What changed since round 2

- `befb73f9`: `Bidirectional.foldCfg_run`'s one-step base cites `runFrom_one`, using the
  replacement round 2 proposed. This is one line in one declaration (`r3-evidence/R3-CHANGED-DECLS.txt`;
  `patch/round2-to-head.patch` in the carrier).

The PR now changes 70 files: Deterministic and 69 citing owners, Bidirectional newly
among them. The API is unchanged: one public addition, the same five deletions, and no other
statement, name, import or attribute change. `zr_cellContract` remains the one changed definition.

## Counts

- `SOURCE.json`: 269 changed or added declarations, which are 268 theorem or lemma
  bodies (including `runFrom_one`) and the private definition `zr_cellContract`.
- Seal targets: 280, the 268 bodies and the same 12 unchanged probes (`focus` in
  `scripts/seals.py` and `scripts/metadata.py`).

## Brief for the auditor

1. Check G132-04's repair in the current source, and the corrections in `resolutions-r3.md` to
   round 2's sweep dispositions and to the ledger.
2. Check the three round 3 checks behind it:
   - the re-reading of all 21 passing mutants, using the round 2 sweep logs in the round 2 carrier;
   - the census of explicit successor-and-zero rewrites (`r3-evidence/SUCC-ZERO-CENSUS.json`);
   - Bidirectional re-swept at the head (`r3-evidence/SWEEP-BIDIRECTIONAL-r3.json`, logs in the
     carrier).

   Report any one-step site that should, but does not, cite `runFrom_one`.
3. Check the whole-proof seals and the base comparison. Every ordinary foreign definition a
   changed proof reaches is made irreducible (227 definitions). 30 of 70
   owners pass in full at head, against 26 on the campaign sources with the same
   seals. `SEAL-COMPARISON-r3.json` finds:
   - **New failing roots at head:** none.
   - **Roots that newly pass:** 21, which are `arCfg_cycle` (AlphabetReduction), `arMoveCfg_run` (AlphabetReduction), `arWriteCfg_run` (AlphabetReduction), `retR_run` (CallReturn), `retR_scan` (CallReturn), `canonSuffix_run` (CodeSimulator), `canonTag_step` (CodeSimulator), `sim_step` (CounterProg), `enumCont_rewind` (EXP), `inputLength_round` (InputLength), `loop_scan_left` (Loop), `bridgeReach_step` (MathlibBridge), `emitterP2_body_round` (Primitives), `fl_leaf_run` (StepBlockForward), `sc_finish` (StepClock), `poly_loop` (TMSAT), `timedCut_Interpreter_initialize` (Universal), `timed_clock_pass` (Universal), `timed_flush` (Universal), `timed_output_forward` (Universal), `universalInterpreter_initialize` (UniversalInterpreter).
   - **Shared roots failing at head sites outside their base sites:** 8, each classified
     with its lines. These are round 2's cascades: the base fails at the `change`, `rfl` or `from`
     that RO-1 replaces, and the failure ends the block. At head the replacement passes, and the
     proof reaches an unchanged later tactic that already reads a foreign definition (or, in
     `Segment.one`, a zero-step run).
   - **Other:** the unrooted ObliviousSetup kernel error, as in rounds 1 and 2.
4. Check the 454 paired controls (run in 6 parts of at most 45 heads, because Lean stops
   after 100 errors): each sealed head closes natively and fails sealed.
5. Check the copy screen on the same 70 files: BASE `declarations screened: 4682; copy pairs (target reproduces >= half of source): 4015; reproduced text: 996,673 chars` (round 2's run; the base
   and the population are unchanged); HEAD `declarations screened: 4680; copy pairs (target reproduces >= half of source): 3225; reproduced text: 927,947 chars`. Check the dispositions of every new
   and removed pair (`PAIR-DISPOSITIONS-r3.json`). Report any exact reusable proof a changed
   declaration should cite instead.

## Evidence

- `r3-evidence/SOURCE.json`, `r3-evidence/TOKEN-DELTA.json`: the declaration inventory and the
  per-declaration token changes. Since round 2 the only added code tokens are `Nat.zero_add` and
  `runFrom_one` in `foldCfg_run`, replacing `runFrom_succ_eq_step`.
- `r3-evidence/REPLAY.json`: the merged-tree replay of the 403-module downstream closure of
  the changed files on the complete campaign snapshot after #242 (876 objects;
  prospective tree `5b7670ea809bf41e693e1fc870e1a47182454ab8`). 403 passed, 0 failed. The 65 inherited admissions
  are in downstream modules whose sources are byte-identical to earlier campaign replays (the
  four RecordTable admissions are the campaign's own and unchanged); the changed proofs have none.
- `r3-evidence/CHECKED-SUMMARY-r3.json`:
  - seals, the comparison and controls;
  - metadata (standard axioms only);
  - lint: no new style or campaign finding; under the unused-argument linter Bidirectional (the one file changed since round 2) elaborates and its `runFrom_one` citation is not flagged; round 2's run over the other 69 owners (`lint-r2.out` in the round 2 carrier) stands, their sources unchanged;
  - the argument sweep: 781 explicit-read candidates (386 distinct), each also present in the same declaration on the campaign base.
- `r3-evidence/DATA-CARRIER-r3.json` and its recovery map hold 1967 logical files:
  - every replay receipt and log;
  - seal and control sources and logs on both sides;
  - metadata, lint, the Bidirectional sweep jobs, confirmations and classifier, and the census script;
  - both screen outputs, and all 70 population files at both commits with the scorer;
  - the campaign versions of the owners;
  - the patches and the drivers.

  Decode each gzip+base64 blob and check its SHA-256 and byte count. Round 2's library-wide sweep
  logs are in the round 2 carrier (`r2-evidence/DATA-CARRIER-r2.json`, records commit
  `501f19ddf7f44f966f24c0bc7d82c1bd4a36de1d`). They stand for every file except Bidirectional.
- The checks ran on the cloud machine with the approved wrappers. The 20 PFR-dependent
  NewmanTheorem modules are not built there; none is in or imported by the closure.

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named `gate132-runfrom-one-r3-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in
your reply.
