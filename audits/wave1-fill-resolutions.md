# Wave-1 fill gate: resolutions (round 1, CLOSED)

**Gate:** the wave-1 fill gate (`audits/wave1-fill-pack.md`, bundle SHA-256
`1c7218cde8a4106d2c78aed6880fccb2308db1709158c6266b966746de0e7c33`, 93 sections), covering
R8.5c `Turing.exists_inputLengthTM`, W2-V `Turing.FinTM.exists_certificateShell`, W2-C
`Turing.FinOracleNDTM.exists_choiceTM` and W2-S `Turing.FinOracleTM.exists_plain_simulation`.
**Findings:** `audits/wave1-fill-findings.md`, preserved verbatim: **0 blockers, 1 major (a
duplication-debt major), 4 minors, 19 notes.**

**The gate closes at round 1.** The template's closing rule for a duplication-debt major is that
the human maintainer explicitly accepts the debt and names its scheduled resolution
(`audits/TEMPLATE.md`, failure mode 5). The user did so (below), and the minors are swept.

The auditor confirmed:
- the cumulative freeze, byte for byte;
- the four routes, including W2-S's refinement to one phase host with a single R2 seam, which is
  sound, documented and no weaker than the bound route;
- W2-C's exhaustion exception;
- the empty admission walks of the targets and of `POracle_eq_P_of_mem_P`;
- the rulings asked for: the split word is accepted as pre-disclosed (N10), and OracleSim's
  action and configuration pairs against `Simulation.lean` are forced specializations (N11).

## Major F1: acknowledged, with its resolution scheduled

**The debt.** `OracleSim.oracleBankCfg_eq` repeats the R1 configuration-reconstruction argument
inside the local `hframe` of `Loop.emCall_exit_fixed` (Loop → OracleSim 203/363, 56%). The
argument: from the selected-bank projections and the unchanged ambient frame, conclude equality
of an embedded configuration. The auditor charges OracleSim's whole 363-character body, 0.757% of
its extracted text.

**The family**, as now known:
- `OracleSim.oracleBankCfg_eq`;
- the local `hframe` in `Loop.emCall_exit_fixed`;
- `CodeSimulator.canonEmbedEq`, integrated at fills-7 (backlog F7-1(b));
- the private analogues in `Primitives` and `CertShell` that the canonizer continuation's report
  names.

**Acknowledged by the user (2026-10-12), with the resolution scheduled in MIG-0b:** one public R1
reconstruction lemma in `Build/Embed`, written during MIG-0b's layering split, the step that
already moves the contract exports into `Build/Embed`. `OracleSim`, `Loop` and `CodeSimulator`
then cite it. It permits state relabelling, or comes with a thin relabelling corollary, as the
auditor proposed. Recorded in backlog F6-1(i). The MIG-0b list in design §16a gets this item in
the next records PR, once PR #78, which edits that list, has landed.

## Minors

- **F2, the exhaustion execution.** The delivery's probe `OracleSimSanity.lean`, its log and its
  summary are now attached (`audits/evidence/wave1-fill-gate/delivery-oraclesim-cont-2/`), each
  matching the delivery manifest's hash. **The maintainer also elaborated the probe**, read-only
  against the fills-6/CH34-D4 snapshot (`audits/logs/wave1-fill-gate-sanity-maintainer.log`):
  `exhausted_at_query` holds, for both oracle answers, on `[propext, Classical.choice,
  Quot.sound]`. The probe uses `open private` to reach the witness, which is acceptable in a
  probe and absent from the library.
- **F3, the earlier union screens.** `audits/logs/wave1-fill-gate-earlier-pairs.txt` excerpts
  every pair touching the three owned files from the three fills-6 combined screens, each bound
  to its full log by SHA-256. The maintainer checked the claim the pack made: all 28 pairs of the
  gate's union screen that touch the three files appear in an earlier fills-6 combined screen,
  so none is new.
- **F4, the stale design extract.** Design §12.10 now marks the three rows proved, gives W2-C's
  exhaustion exception, and records W2-S's delivered refinement: one phase host, a single R2
  seam, and the preparation, restoration and query costs. The attached extract
  `audits/evidence/wave1-fill-gate/design-12.8b-12.10.md` is labelled historical in the pack's
  erratum.
- **F5, the axiom count.** The pack's erratum reads "26 axiom prints: 25 within the standard
  three, one (`FinTM.prefixWords`) with none".

## Notes

N1–N19 record no findings. Two of them are carried forward:
- **N15, `oracleEmbed_updateTape`:** promote it in the shared-file window **before** a second
  consumer is briefed (F6-1(f)), and coordinate it with F1's lemma, which lands with MIG-0b.
- **N10, SH-1:** it retires the polynomial `contSplitWord` consumer only, and keeps the
  exponential route's `e3SplitWord`.
