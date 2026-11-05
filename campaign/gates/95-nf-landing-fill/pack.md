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

#191 on `lean/c1-nf-landing`, head `e8994dc115fd61a940509516b658a9975edbb71a`, based on the campaign branch since #190
merged. Against the campaign it changes one file, `ClassNP/NDNormalForm.lean` (3,289 lines, blob
`9474847a`; `evidence/final-vs-campaign.diff`). Its 14 commits on the file are in `evidence/patches/`:
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
  - the file imports `TuringMachine/CfgFacts`;
- `5732d5bd`: `nf_tag` (RN-1) converts the tagged stream start through
  `Cfg.mapState_eq_of_fields`;
- `4354cbeb`: two inline steps found by the maintainer's sweep for inline re-derivations
  (`campaign/maintainer/WORKFLOW.md` §3) now cite published lemmas. **Its commit message says
  `nf_setup`; the site is `nf_entry`.**
  - `nf_backward_host`'s equal first verdict times cite `Segment.time_eq`, the pattern gate 93
    rated a major in E-D's `dz_first`;
  - `nf_entry`'s blank cell past the stream cites `FinTM.bufferTape_eq_none_of_not_mem`;
  - the file imports `BufferWords` and `Build/Contract/Basic`, low published modules.

**#190 merged on 2026-11-05.** #191 was then retargeted to the campaign branch and merged with
it (`e8994dc1`, a merge commit; the file is unchanged by it).

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
   - The screen at the final head (`evidence/screen/`): the v3 screen restricted to pairs with an
     `NDNormalForm` declaration, over the brief's 21-file population plus `CfgFacts`, on a frozen
     checkout of the final head. **13 pairs** (1,438 declarations, 5,230 characters), against 14 at
     the first landing head `e210f418` (`superseded-e210f418/`, `pairdiff-e210f418-final.txt`):
     - gone: `nf_tag` against `CfgFacts`' `Cfg.mapState_eq_of_fields` (83%; `nf_tag` now cites
       it) and `nf_entry` against `CodeSimulator`'s `canonStageBuffer_none` (80%; the blank cell
       now cites `FinTM.bufferTape_eq_none_of_not_mem`);
     - new: `nf_entry` against `nf_tag` (54%, in the file). **Disposition: idiom**, the five
       `streamStartCfg_*` field equations rewritten around two different statements;
     - the one cross-file pair left is `un_setup` against `nf_setup` (57%), NF-X1, excluded by the
       user's ruling. The other eleven are in-file pairs, with the cont1 review's dispositions.

   **The sweep** (`evidence/sweep.txt`) looked for `bufferTape_eq` unfoldings,
   `Nat.exists_eq_add_of_le`, `runFrom_add`/`runFrom_of_halt`, `lt_trichotomy`, `Nat.find` and
   `Cfg.ext` blocks. Its results:
   - two inline re-derivations, now fixed (above);
   - `Nat.find` in `nf_forward`: the first halt of a nondeterministic branch (`runWith` over word
     prefixes), with no published lemma, as NF's report notes;
   - twelve `Cfg.ext` blocks, which are configuration-equation idioms or RN-1 members, under the
     user's by-kind acknowledgment.

   Is anything else re-derived, including inline sub-steps?
6. **Public-facing text:** E2–E6, and the target's docstring now that the proof exists.

## Repository-side attestations (verify or challenge)

- **Elaboration:** the landing file elaborates against a clone of the campaign's snapshot with
  #190 compiled in, with no output. The replay below compiles it on the merged tree.
- **Axioms** (`evidence/axioms/`): `exists_codeNDTM_accepts_linear` on
  `[propext, Classical.choice, Quot.sound]`.
- **Replay:** `replay-lnf` (`evidence/merged-tree/`), the downstream closure of the one changed
  file on the merged tree: `NDNormalForm`, the `ClassNP` facade, `NTimeHierarchy` and
  `Diagonalization`, 4 modules chained from `oleans-lcf3` (the campaign after #190). With #188
  merged too, `NTimeHierarchy`'s three theorems should be free of `sorryAx`; their axiom prints
  are in `evidence/axioms/`.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/95-nf-landing-fill/findings.md`. The gate closes when it has zero blockers and zero
majors.

**Deliver your findings as a downloadable Markdown file named `nf-landing-fill-findings.md`** (the
findings table and the verdict line, no other wrapping), and also paste its content in your reply.
