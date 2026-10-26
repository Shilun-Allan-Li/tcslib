# External audit pack — U2, the `k`-tape universal machines (the U2 landing, a fill gate)

Campaign: the Arora-Barak chapters 3-4 plan, U2 ([AB09, §1.4.1, Theorem 1.9; Exercise 4.1]).
- **The brief:** U2 (`campaign/fills/u2s/briefs/u2s-fill-universal.md`, megafill C's only item,
  issued at `ed8f2e87146be90eb76216e9bc34f7838ec79574`). It targets `Turing.exists_selfUniversalK`
  (U2-U) and `Turing.universalK` (U2-E) in `TCSlib/Complexity/TuringMachine/UniversalK.lean`.
- **The delivery:** complete, on 2026-10-26 (`fill-u2s-universal.zip`, SHA-256
  `1834327679968d9276a9de60b17cfea13d70d1d1296893fd25f6dfb4484600f7`). The worker's report is
  `campaign/fills/u2s/reports/universal-REPORT.md`.
- **The review:** the maintainer's, `campaign/fills/u2s/reviews/universal/REVIEW.md`, with its
  evidence (`out/`, `probe/`, `scripts/`). Its verdict: "both targets are proved with no
  admission (2/2); land it through a maintainer PR plus a fill gate".

**The user's rulings (2026-10-26)** on the review's decisions:
- **F1 (major):** three inline arguments re-proved published lemmas. **Apply the review's edits
  D1–D3:**
  - `uk_loop_forward` now cites `MultiTapeTM.exists_first_halt`;
  - `exists_selfUniversalK` cites `MultiTapeTM.visitedByTapeHead_mono`;
  - `exists_selfUniversalK`'s `hfreeze` is replaced by `FinTM.ComputesInTime.spaceUsed_le_of_halt`.
- **F2:** the ruler is tape `k + 2`, immediately after the simulation bank, where the brief said
  last. **Accepted.**
- **F3/F4:** **all of the review's wording edits S1–S6:**
  - the proved status in `UniversalK`'s header and main results, `SelfUniversal`'s status and the
    facade's entries;
  - an `**Implementation.**` paragraph in `universalK`'s docstring;
  - the stale "deferred until this statement is filled" sentence, reworded.
- **F5 (E-CHK):** three grouped checkpoint zips instead of one per checkpoint. **Accepted**, with
  no re-delivery.
- **Order:** this PR merges after #164 and #167.

**The landing:** PR #168 on `lean/u2-universal-landing` at
`fd995ec1ff08e90f46aa9d98c03f1d137402ad37`. It is 6 commits on the campaign branch at
`a680ba528aa54dcecfd915bcbfc205758b32984f`, whose Lean is the tree after #165
(`campaign/fills/u2s/evidence/u2s-universal-landing/patches/`):
- 5 commits, the delivery's series, cherry-picked unchanged (the worker's authorship and subjects
  kept). They reproduce the delivered file byte for byte.
- `fd995ec1`, the review's landing edits D1–D3 and S1–S6, exactly
  `campaign/fills/u2s/reviews/universal/out/45-landing-edits.diff`. It touches `UniversalK`,
  `SelfUniversal` and the `TuringMachine` facade.

## What changed (verify)

| Class | Declarations |
|---|---|
| **Targets proved** | `Turing.exists_selfUniversalK` (`C = T + 1 + D + B + N·(2D + 1) + N`), `Turing.universalK` (`C = T + 2ℓ + 5 + C_R·(ℓ + 1)·D`, no `|x|` term), with no `sorryAx`; with them `Turing.exists_selfUniversal` (`SelfUniversal`) is admission-free |
| **Privates** | 39 → 67: 28 new `uk_` declarations, none removed or changed |
| **Frozen** | every public statement; every docstring except `universalK`'s (the review's S4 and S5: an Implementation paragraph and one reworded sentence); 12 → 12 public declarations; one import added (`Build/Rewind`, the brief's region (a)) |
| **Text** | `UniversalK`'s status paragraph and main results, `SelfUniversal`'s status paragraph, the facade's two entries |

## Brief for the auditor

1. **Faithfulness.** Do the proofs establish the frozen statements? Check:
   - U2-U's time `C · (t + 1)`, its space `C · (s + 1)` and its converse;
   - U2-E's time with no `|x|` term, and its converse;
   - both constants against the proofs, and that each is chosen after `α` but before the input.

   The edge cases: `k = 0`, `α = []`, an empty suffix (`w = []`, `x = []`), a canonizer with no
   work tapes, arbitrary canonizer time, and a coded machine that never halts (the converses).
2. **The route.** Check the binding rows: the seam into the forwarding loop
   `StepBlock.exists_forwardLoopTM` (`seamCompTM` with the explicit `q₀` override); R1, not R1′;
   the ruler host `exists_rulerHostTM` consumed exactly as stated, with no ruler-device exit
   treated as stationary and `inj` only a state map (gate 60's C60-1); the ruler tag `false`;
   `pairEncode_drop` cited, not copied; the ruler's rewind by `rewindTM_run_ofCfg`; the header
   scan as the only leaf.

   **The accepted layout (F2):** the ruler on tape `k + 2`, which the startup leaves blank. Does
   anything in the proof depend on the ruler being last?
3. **Rule 10** (with the scope of 2026-10-23). The review's seal covers 27 other-file definitions
   and erases two from `simp`, with two instance controls. The body has 0 errors, and all 31
   controls fail sealed and close unsealed, at the delivered head and with the landing edits
   (`out/21-*`, `out/46-land-seal.out`). No other-file definition is passed to `rw`, `simp` or
   `unfold` (229 arguments, `out/20-*`). The worker's `uk_loop_init` closes unsealed by `rfl`, and
   the proof instead cites a transport lemma: does any step still close only because another
   file's definition reduces?

   **Rule 11:** no R3 row, and no other file's private.
4. **Duplication.**
   - **Text:** the v3 screen on the brief's 20-file population, under the lock. Its base is the
     brief's screen base, measured at the issue commit; the tip's population files are identical
     to it. Its head is the landing head `fd995ec1` (7 minutes, 3.4 GB):
     - 1,057 → 1,085 declarations, 788 → 793 pairs;
     - 5 new and none gone, all inside `UniversalK`, none at 90% or more (the highest 61%), no
       cross-file pair (`screen-head-fd995ec1.txt`, `pairdiff-head-vs-base.txt`).

     The head's screen is byte-identical to the review's screen of the delivered head
     (`pairdiff-head-vs-review-head.txt`), so the landing edits change no pair. Are the in-file
     pairs justified (REPORT's table of five)?
   - **Semantic:** the review's search (`out/26-semantic-greps.txt`, `out/27-dup-exact*`,
     `out/29-semantic-table.txt`) found F1, fixed by D1–D3. Is any other new private a
     re-derivation of published API? The candidates:
     - `uk_init_mapState`, against `initCfg_with_q₀` and the `Cfg.mapState_*` equations;
     - `uk_loop_live` and `uk_loop_converse`, against `Lockstep.cut` and `Contract.live`;
     - `uk_loop_space`, against the seam and embedding visited-set lemmas;
     - the scan rows, against the catalog's one-step lemmas;
     - `uk_ruler_fields` and `uk_embed_suffix`, against `rulerHostCfg_*`.
5. **The maintainer's text** (S1–S6, from the review). Is the `**Implementation.**` paragraph an
   exact reading of the proof: the order of the phases, the tape layout, `T + 2ℓ + 4` steps before
   the host, and the constant? Are the status texts accurate? All of it must be public-facing: no
   campaign labels, paths or dates in new Lean text. The frozen statement docstrings keep their
   old wording outside S4.
6. **Records.** Look for any correctness gap in:
   - the review's F5 (E-CHK) and F6 (the worker's seal omitted two reached definitions and had no
     `simp`-erasure control; the review's seal covers both);
   - F8 (the last commit rephrased one scan proof to clear a 56% cross-file text pair);
   - F9 (the brief's stale lint base and one wrongly listed out-of-scope sorry);
   - the worker's post-sweep tail rebuild (`UniversalK` and the six later modules, after the
     last proof edit).

## Repository-side attestations (verify or challenge)

- **Elaboration:**
  - the review: the delivered file with no diagnostic against `oleans-lkit2` (the base's tree);
    this landing's three files, byte-identical to its `wt-tip`, with no diagnostic against
    `oleans-lg4c4m` (the tree after #165); `SelfUniversal`, inlined after the edited module, with
    none either (`out/04-*`, `out/46-*`, `out/49-*`);
  - the maintainer: the landing head's `UniversalK` against `oleans-lg4c4m`, with no diagnostic,
    and both targets' axiom prints (`elab-UniversalK-fd995ec1.out`).
- **Axioms:** all 81 prints (every declaration of the module, the 28 new privates included, and
  `exists_selfUniversal`) on `[propext, Classical.choice, Quot.sound]`; unchanged by the landing
  edits
  (`out/05b-axioms-table.txt`, `out/46-land-axioms-compare.txt`).
- **Probes** (the review): the brief's import probe (93 checks) and the worker's (593, covering
  all 563 direct citations), with 0 errors.
- **Sweep** (the worker; checked by the review): 97 modules, 26 → 24 sorry warnings, exactly the
  base set less the two targets.
- **Freeze** (`freeze-UniversalK.txt`, `freeze-SelfUniversal.txt`, `declfreeze.py` v4): 12 → 12
  public, the two authorized body changes, 28 privates added; `SelfUniversal` header text only.
- **Lint:** `TuringMachine` 0 FAIL, 67 WARN over 84 files at both ends; the only changes are the
  size lines (`UniversalK` 1,762 → 2,873 lines). No line over 100 characters.
- **Replay:** `UniversalK`'s downstream closure (3 modules: `UniversalK`, `SelfUniversal`, the
  `TuringMachine` facade). It is chained from the snapshot that #164's and #167's replays leave,
  after the campaign is merged in. **Pending** (the gate is dispatched before it).

**Not in the bundle, for size:**
- the review's eleven probe files that are copies of the module with a block inserted
  (`probe/UKSeal_{sealed,unsealed,extended}`, `LandSeal`, `UKAudit`, `TipAudit`, `LandAudit`,
  `UKKinds`, `UKDup`, `UKDedup`, `UKDedupSeal`, each about 150 KB). Each is rebuilt from the
  module and the blocks in `scripts/` by that folder's generators (`mkseal.py` with
  `seal_block.lean.txt`, `mkaudit.py` with `audit_tail.lean.txt`, `mkdup.py`,
  `dedup_edits.py`), and their outputs are in `out/`;
- `out/aux/first-commit-UniversalK.lean.txt` and `out/aux/added-lines.txt`, both derived from
  the patch series.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `campaign/standards/TEMPLATE.md`. Findings go verbatim into
`campaign/gates/80-u2-universal-fill/findings.md`. The gate closes when it has zero blockers and
zero majors.

**Deliver your findings as a downloadable Markdown file named `u2-universal-fill-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
