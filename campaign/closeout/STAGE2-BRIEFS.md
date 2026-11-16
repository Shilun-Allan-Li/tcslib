# Stage 2 briefs: delegated fills (draft, 2026-11-16)

Stage 2 of `STAGES.md` is medium structural work, delegated to outside workers as three fills.
Each fill owns files disjoint from the other two, so they can run in parallel. The maintainer
integrates all three into one stage 2 PR and one gate.

**Base.** Each fill starts from the campaign tip after stage 1 (#349) merges, because stage 1
touches ExhaustiveReplay, CodeSimulator and Nondeterminism. The maintainer will pin the exact base
commit and refresh line numbers when the fills are dispatched.

**Approvals needed before dispatch.** These are new public lemmas, imports or moves, so Seyoon
rules on them first, as one checklist:

- **A2:** a public `NDTM` first-halt row in `TuringMachine/Nondeterministic` (RC-4). Its
  rebuild covers about 160 modules.
- **B1:** a general `Action` tape-half lemma ("an action changes a work cell only under that
  tape's old head"), harvested from Oracle's private `apply_workTapes_eq_of_ne` (WS-1).
- **B2:** a general-configuration additive space lemma for `seamCompTM` in `Build/Seam`
  (F6-1(b)).
- **C2:** an import of the Build stack (`Build/Embed`) into chapter 1's
  `TuringMachine/UniversalStartup` (MIG-7).

## Common rules for every fill

- Read `policy.md`, `workflow.md` and `campaign/maintainer/WORKFLOW.md` (rule 10).
- Rule 10: a changed proof may read another file's definition only through its published
  equations. That means no `simp [Def]` or `unfold Def` on another file's definitions, no
  generated `eq_1`/`eq_def`, and no `rfl`/`change`/`show` that unfolds them. Same-file
  definitions and structure-update projections are fine.
- No statement changes to existing public declarations. New public declarations only as
  approved above, with docstrings, `[AB09, …]` attribution and proof sketches.
- Elaborate only with the approved wrappers (`devtools/seyoon/leanelab.sh` or the replay
  scripts). Never run `lake build`.
- **Deliver** a patch or branch against the pinned base, plus a short report. The report gives
  the lines saved per item, any item that turned out not to be mechanical (stop and report it,
  as SH-1 and RS-1 were), and anything you could not prove without unfolding.
- **The maintainer then:** integrates the fills, runs the merged-tree replay, seals, controls,
  sweeps and copy screen, and stages one gate.

## Fill A: rewinds and first halts (IR-1, RC-4)

Files: `ClassNP/ExhaustiveReplay`, `TuringMachine/UniversalK`, `TuringMachine/NDNormalForm`,
`TuringMachine/Nondeterministic` (new row only).

- **IR-1.** Re-point the last input-rewind copies to the public `Build/InputRewind` row
  (`Turing.inputRewindTM`, `inputRewindTM_run`) and `Turing.Cfg.mapState_mapState`.
  - In ExhaustiveReplay this is `xr_inRewindTM` and its run lemma (82% / 73% against the
    public machine).
  - In UniversalK this is U2-S's `ss_inputRewind`.
  - The phase hosts' arms change, so recheck the seam-time arithmetic of the public
    `exists_selfStartupTMK`; its statement must stay byte-identical.
  - Ledger: `duplication-ledger.md`, "IR-1, the input rewind family". Measured: 6 members,
    144 lines, 9 uses, 0 rule-10 exposure.
- **RC-4's first-halt row (approval A2).** Publish an `NDTM` first-halt lemma: the first prefix
  length of a choice word at which `runWith` halts, with `Nat.find`'s minimality, and the output
  after it by `NDTM.runWith_append`/`runWith_of_halt`. This is the nondeterministic form of
  `MultiTapeTM.exists_first_halt`. Cite it at NDNormalForm's `nf_forward` and ExhaustiveReplay's
  `xr_replay_host`. Ledger: "RC-4, row candidates from NF cont1".

## Fill B: windows and seam space (WS-1, F6-1(b))

Files: `TuringMachine/Oracle` (harvest only), the `Action` home that B1 settles on,
`Build/CfgRecord`, `SpaceComplexity/ExpBFS/Radius`, `SpaceComplexity/Codec/Step` and the other
WS-1 members, plus `Build/Seam` and `ClassP/Constructible` (F6-1(b)).

- **WS-1 (approval B1).** Every proof that one step keeps a configuration within a window, and
  every proof of window monotonicity, should cite `Turing.Cfg.InWindow.apply_iff`,
  `Cfg.InWindow.mono` and the new tape-half lemma.
  - The member list is in the ledger: "WS-1, one step keeps a configuration in a window, scoped
    by kind".
  - Hydroxyi's files (ExpBFS, Codec) get an FYI line.
  - Measured: 11 members, 311 lines, 14 uses, about 19 rule-10 repairs.
- **F6-1(b) (approval B2).** Publish a general-configuration additive space lemma for
  `seamCompTM`, usable at a genuine halt, and derive the existing canonical corollaries from it.
  Then replace Constructible's private `b3a_seam_space`; also try defining `b3a_cfg` through
  `Cfg.ofWords`. Backlog: §F6-1(b). Measured exposure: 1 member and 6 uses.

## Fill C: renamings and the universal capture (RN-1, MIG-7)

Files: `TuringMachine/CodeSimulator`, `TuringMachine/UniversalStartup`, `Build/Embed` (citations
only).

- **RN-1, narrowed to CodeSimulator.** Convert the remaining inline "renamed configuration, field
  by field" blocks to `Turing.Cfg.mapState_eq_of_fields`: `canonStageOuterSpec`,
  `canonStageInnerSpec` and any left in the legs after CC7-1 (#345). Ledger: "RN-1, renamed
  configurations converted field by field". `us_start` stays as it is; RS-1 is carried.
- **MIG-7 (approval C2).** Move `universalCaptureTM` onto `Build/Embed`'s `embedSilentTM`.
  Backlog MIG-7, about −130 lines. Measured: 8 members, 126 lines, 6 uses, 5/5 rule-10 exposure.
