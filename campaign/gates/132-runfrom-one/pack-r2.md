# Gate 132 round 2 · `MultiTapeTM.runFrom_one` in Deterministic, cited at one-step sites (PR #296)

**Not yet clear to merge** · PR #296 is a draft. Seyoon dispatches and merges.
The current Lean commit is `ce427bde6ee5464a4146dce2b3add69b7a05677d`, against campaign Lean `7b6bd1685a1436313dfbc13ce191f40c7dd065d3` (the campaign after #242).
Round 1 audited `677970b0e7bba401a707e409b5c275a664924f0b` and returned HOLD with three minors
(`findings.md`, verbatim). This round checks their resolutions (`resolutions-r2.md`) and the
library-wide sweep behind them. Dedup family RO-1; Seyoon ruled the home `Deterministic` on 2026-11-12.

## What changed since round 1

- `525bf933`: G132-01 and G132-02 repaired, plus every other one-step site the first sweep found.
- `43c5d693`: a **Proof sketch.** for the private `Reductions.acceptCfg_step`, whose proof the
  citation took past 20 lines. Statement and proof unchanged.
- `ce427bde`: eight one-step runs whose durations are written `0 + 1`, `Nat.zero + 1` or a
  constant function applied, found once the classifier evaluated closed durations.

`r2-evidence/R2-CHANGED-DECLS.txt` lists the 53 declarations in 29 files that round 2 changes, and
`patch/round1-to-head.patch` in the carrier is the exact difference from the audited source.
The PR now changes 69 files: Deterministic and 68 citing owners, nine of them new
(Reductions, CodePrefix, CertShell, `Contract/Basic`, CounterLoop, WindowRun,
AlphabetReduction, InputLength, SingleTape). The API is unchanged since round 1. There is one
public addition, the same five deletions, and no other statement, name, import or attribute
change. `zr_cellContract` remains the one changed definition.

## Counts (G132-03)

- `SOURCE.json`: 268 changed or added declarations, which are 267 theorem or lemma
  bodies (including `runFrom_one`) and the private definition `zr_cellContract`.
- Seal targets: 279, the 267 bodies and 12 unchanged probes. The probes are the
  fixed Simulation and Primitives set that the reused gate 121 seal tooling always selects
  (`focus` in `scripts/seals.py` and `scripts/metadata.py`). `zr_cellContract` is not a seal
  target; its two edited proof fields only cite `runFrom_one`.
- `SOURCE.json` lists `acceptCfg_step` under `header_changed` only because its header includes
  the docstring. Its statement is byte-identical to the campaign's.

## Brief for the auditor

1. Check each row of `resolutions-r2.md` against the current sources: the eighteen round 1
   sites, and the further repairs of `525bf933` and `ce427bde`.
2. Check the sweep (`r2-evidence/SWEEP-FINAL.json`, scripts and logs in the carrier):
   - its method: mutation with irreducible confirmation, and irreducibility with the
     closed-duration classifier;
   - its dispositions;
   - the disclosed sites left alone, the limitations and the disclosed parsing gap (tagged
     error headers, which affect two mutation rows and no irreducibility row).

   Report any one-step site that should, but does not, cite `runFrom_one`.
3. Check the whole-proof seals and the base comparison. Every ordinary foreign definition a
   changed proof reaches is made irreducible (227 definitions). 29 of 69
   owners pass in full at head, against 25 on the campaign sources with the same seals.
   `SEAL-COMPARISON-r2.json` finds:
   - **New failing roots at head:** none.
   - **Roots that newly pass:** 21, which are `arCfg_cycle` (AlphabetReduction), `arMoveCfg_run` (AlphabetReduction), `arWriteCfg_run` (AlphabetReduction), `retR_run` (CallReturn), `retR_scan` (CallReturn), `canonSuffix_run` (CodeSimulator), `canonTag_step` (CodeSimulator), `sim_step` (CounterProg), `enumCont_rewind` (EXP), `inputLength_round` (InputLength), `loop_scan_left` (Loop), `bridgeReach_step` (MathlibBridge), `emitterP2_body_round` (Primitives), `fl_leaf_run` (StepBlockForward), `sc_finish` (StepClock), `poly_loop` (TMSAT), `timedCut_Interpreter_initialize` (Universal), `timed_clock_pass` (Universal), `timed_flush` (Universal), `timed_output_forward` (Universal), `universalInterpreter_initialize` (UniversalInterpreter).
   - **Shared roots failing at head sites outside their base sites:** 8, each classified
     with its lines. In each, the base fails at the `change`, `rfl` or `from` that RO-1 replaces,
     and the failure ends the block. At head the replacement passes, and the proof reaches an
     unchanged later tactic that already reads a foreign definition (or, in `Segment.one`, a
     zero-step run).
   - **Other:** the unrooted ObliviousSetup kernel error, as in round 1.
4. Check the 454 paired controls (run in 6 parts of at most 45 heads, because Lean stops
   after 100 errors): each sealed head closes natively and fails sealed.
5. Check the copy screen on the 70 files (the 69 owners and Bidirectional): BASE
   `declarations screened: 4682; copy pairs (target reproduces >= half of source): 4015; reproduced text: 996,673 chars`; HEAD `declarations screened: 4680; copy pairs (target reproduces >= half of source): 3237; reproduced text: 929,463 chars`. Check the dispositions of every new and removed pair
   (`PAIR-DISPOSITIONS-r2.json`). Report any exact reusable proof a changed declaration should cite
   instead.

## Evidence

- `r2-evidence/SOURCE.json`, `r2-evidence/TOKEN-DELTA.json`:
  - the declaration inventory;
  - the per-declaration token changes. Added code tokens are `runFrom_one`, tactic glue,
    `Nat.zero_add`, `List.length_nil`, three `runFrom_succ_eq_step'` and one `runFrom_zero`.
    No foreign definition token is added.
- `r2-evidence/REPLAY.json`: the merged-tree replay of the 403-module downstream closure of
  the changed files on the complete campaign snapshot after #242 (876 objects;
  prospective tree `ba91788951e681ee0e3529c4b6742fb51772518c`). 403 passed, 0 failed. The 65 inherited admissions
  are in downstream modules whose sources are byte-identical to earlier campaign replays (the
  four RecordTable admissions are the campaign's own and unchanged); the changed proofs have none.
- `r2-evidence/CHECKED-SUMMARY-r2.json`:
  - seals, the comparison and controls;
  - metadata (standard axioms only);
  - lint: no new style or campaign finding; under the unused-argument linter the 69 owners elaborate, and no `runFrom_one` citation is flagged;
  - the argument sweep: 781 explicit-read candidates (386 distinct), each also present in the same declaration on the campaign base.
- `r2-evidence/DATA-CARRIER-r2.json` and its recovery map hold 2659 logical files:
  - every replay receipt and log;
  - seal and control sources and logs on both sides;
  - metadata, lint, the sweep jobs, confirmations and classifier;
  - both screen outputs, and all 70 population files at both commits with the scorer;
  - the campaign versions of the owners;
  - the patches and the drivers.

  Decode each gzip+base64 blob and check its SHA-256 and byte count.
- The checks ran on the cloud machine with the approved wrappers. The 20 PFR-dependent
  NewmanTheorem modules are not built there; none is in or imported by the closure.

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named `gate132-runfrom-one-r2-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in
your reply.
