# External audit pack: NF's landing, the linear normal form (PR #191, a fill gate)

## What this gate covers

The target is `Turing.FinNDTM.exists_codeNDTM_accepts_linear` in
`TCSlib/Complexity/ClassNP/NDNormalForm.lean`, the linear-overhead coded normal form of a
nondeterministic machine. It is the input the nondeterministic time hierarchy (`NTimeHierarchy`)
needs besides the diagonalizer `exists_diagonalizer`, which is gate 93's (#188). Two fills
produced it, and this gate covers the whole file:
- **NF, checkpoints 1–2** (brief `campaign/fills/c1/briefs/c1-fill-nf.md`, Codex). The report is
  `campaign/fills/c1/reports/nf-1-REPORT.md`. The review, `campaign/fills/c1/reviews/nf-fill/`, gave
  **land with edits, 0/0/3/6**, with edits E1–E3 (docstrings).
- **NF cont1, checkpoints 3–8** (brief `campaign/fills/c1/briefs/c1-fill-nf-cont1.md`, Claude),
  delivered complete. The report is `campaign/fills/c1/reports/nf-cont1-REPORT.md`, and the evidence
  is in `campaign/fills/c1/evidence/c1-nf-cont1/`. The review,
  `campaign/fills/c1/reviews/nf-cont1-fill/`, gave **land with edits, 0/2/2/10**, with edits E1–E6.

**Ruled by the user, 2026-11-04:**
- the partial travels with its continuation, and nothing landed until the target was proved;
- the `un_setup` idiom pair is excluded from the debt count (NF-X1);
- **F2 of the cont1 review, homes first:** four kinds of fact that NF re-stated now have public
  homes, in #190 (`TuringMachine/CfgFacts`, gate 94), and NF cites them;
- E6, the Implementation paragraph, lands;
- the missing checkpoint zips are accepted as absent.

## The PR

#191 on `lean/c1-nf-landing`, head `e210f418` at staging (`evidence/patches/`, 12 commits on the
file):
- the partial's two worker commits and its E1–E3 commit (`7791e6fc`, `252dea65`, `969d221d`, from
  `lean/c1-nf-partial`);
- cont1's seven commits, cherry-picked in order with authorship kept, the checkpoint labels and
  the `Claude-Session:` trailers dropped from their bodies. At the seventh, the file equals the
  delivered head's (blob `d767cc72`);
- `1785dc0f`, cont1's landing edits E1–E6. The file equals the review's tested landed file (blob
  `5723152d`; `evidence/landing-edits.diff`);
- `f79b48be`, the re-points to `CfgFacts` (`evidence/repoints.diff`):
  - `nf_inputSymbol_congr` is removed, and its two uses cite `Cfg.inputSymbol_congr`;
  - `nf_retag`, `nf_tagged_ne_park` and `nf_stream_length` keep their statements, with bodies
    citing `Cfg.mapState_const_eq_mapState_sigma`, `Cfg.mapState_sigma_state_ne` and
    `length_flatMap_uniform`;
  - the file imports `TuringMachine/CfgFacts`.

**Stacked on #190**, whose branch is merged in. After #190 merges, #191 is retargeted to the
campaign branch, merged with the campaign, and replayed.

## Brief for the auditor

1. **Correctness.** Is `exists_codeNDTM_accepts_linear` proved as stated? In particular:
   - the verifier's characterization (`nf_V_char`) and `hV` on every first-stopped stream
     (`nf_hV`);
   - the forward and backward transfers;
   - the constant `C = 4k² + 47k + 45` (`nf_C`, the ledger `nf_ledger`).
2. **Route conformance** with both briefs' binding pins, and the cont1 review's MP1–MP11 table.
3. **The landing.**
   - The cherry-picks are the delivered commits (patch-ids against the delivery's patches in the
     evidence).
   - `1785dc0f` is exactly the review's E1–E6.
   - `f79b48be`'s re-points are statement-preserving, and read `CfgFacts` only through its
     statements.
4. **Rule 10** (`evidence/seal/`): the review's seal generator re-run on the landing file
   (`mkseal.py`, its anchor now found rather than fixed, since the landing adds one import line).
   It seals 257 definitions, and the sealed copy elaborates with 0 errors. The generic controls
   discriminate 252 of 257. The review's 41 source controls all close unsealed and all fail
   sealed, and they cover the five that close by structure eta (four derived `Fintype` instances
   and `instInhabitedCfg`).
5. **Duplication.**
   - The cont1 review's dispositions: F1 (removed by E1); F2 (homes first, #190); the in-file
     pairs; the promotion requests.
   - The partial review's F6, NF-X1.
   - The screen at the landing head (`evidence/screen/`): the v3 screen restricted to pairs with an
     `NDNormalForm` declaration, over the brief's 21-file population plus `CfgFacts`.

   Is anything else re-derived, including inline sub-steps (gate 93's lesson)?
6. **Public-facing text:** E2–E6, and the target's docstring now that the proof exists.

## Repository-side attestations (verify or challenge)

- **Elaboration:** the landing file elaborates against a clone of the campaign's snapshot with
  #190 compiled in, with no output.
- **Axioms** (`evidence/axioms/`): `exists_codeNDTM_accepts_linear` on
  `[propext, Classical.choice, Quot.sound]`.
- **Replay:** after #190 merges. It covers `NDNormalForm`, the `ClassNP` facade, `NTimeHierarchy`
  and `Diagonalization`, chained from #190's snapshot. With #188 merged too, `NTimeHierarchy`'s
  three theorems should be free of `sorryAx`. That is checked at the replay.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/95-nf-landing-fill/findings.md`. The gate closes when it has zero blockers and zero
majors.

**Deliver your findings as a downloadable Markdown file named `nf-landing-fill-findings.md`** (the
findings table and the verdict line, no other wrapping), and also paste its content in your reply.
