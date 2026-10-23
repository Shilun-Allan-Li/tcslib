# The seam-layout fill: integration erratum to `seamlayout-1-REPORT.md`

## Erratum (at integration; gate 59, minors 1 and 3)

**Scope.** Seven statements of the worker's report (`seamlayout-1-REPORT.md`, beside this file,
blob `ba3cb78b…`), as corrected at integration. The report itself stays as delivered. Sources: the
maintainer's review
(`campaign/fills/c1/reviews/seamlayout-1/REVIEW.md`, F1, F2 and F4) and gate 59, the fill gate
of PR #145 (`campaign/gates/59-c1-seamlayout-fill/`, minors 1 and 3). None changes the delivered
Lean or its verdict. `Turing.exists_seamLayoutTM` is proved on `[propext, Classical.choice,
Quot.sound]`, and the landed file elaborates with no diagnostic.

1. **§5, the seal.** "The seal test with `attribute [local irreducible] Turing.phaseHostTM` would
   fail on it" is wrong. `simp only [phaseHostTM, hs]` closes the table goal even with
   `phaseHostTM` sealed. Only `simp only [hs]` fails ("no progress"; review
   `probe/SLPhase8Route.lean.txt`, `out/21b-phase8-route.out`). A definition named explicitly is
   unfolded whatever its reducibility, so a seal cannot detect that unfolding. Rule 10 bans the
   unfolding itself. The review's inspection of every `rw`/`simp`/`dsimp`/`unfold` argument
   (`out/20-rwargs.txt`) found no other-file definition in the delivered proof. The phase-8
   self-redirect stands; its host's table equals the brief's host's table
   (`out/21c-same-machine.out`).
2. **CP2 and §6, `FinTM.bufferTape_of_neg`.** The proof does not cite it. `sl_reverse_read` uses
   `bufferTape_nat`, `List.getElem?_reverse`, `bufferTape_left` and
   `bufferTape_eq_none_of_not_mem`. `bufferTape_of_neg` occurs only in the frozen target
   docstring (review `out/25-citations-vs-probe.txt`; `out/15-ax-head.out.tcslib-consts.txt`).
3. **Paths.** In the archive, read `evidence/logs/…` as `logs/…` and `evidence/probe/…` as
   `probes/…`. There are 19 references, in §§1–3, 6, 10 and 11.
4. **§10, item 1.** The archive has no `final-module-check.log`, and the standalone check left no
   log either. Its module checks are `logs/module-check-cp1.log` and `logs/module-check-cp2.log`
   (checkpoints 1 and 2). The final state was checked as item 6 below says.
5. **§2, the manifest check.** `logs/manifest-check.log` ends `MANIFEST CHECK: FAIL`. The 11
   packages present show `url OK rev OK`. `doc-gen4`, `UnicodeBasic`, `BibtexQuery` and `MD4Lean`
   show `url MISMATCH rev MISMATCH` with empty values. These four are the documentation
   toolchain, which the narrowed fetch does not clone, so they are absent, not at another pin. The
   reading "absent, not mismatched" is right, but the check's literal result is FAIL, by
   construction under addendum v2.3's narrowed fetch.
6. **§§10–11, the final sweep.** The 94-module sweep checked `Build/SeamLayout` at
   03:32:31–03:32:39 UTC. That is after commit 5 (`56510600`, 03:25:52) and before commit 6
   (`09773a66`, 03:39:39, `sl_apply_eq`'s proof restated fieldwise). After commit 6, only the
   facade was re-checked. The delivered head was elaborated with no diagnostic by the review
   (`out/13-elab-head-lbw2.out`), and the landed file by the maintainer
   (`campaign/gates/59-c1-seamlayout-fill/evidence/land/elab-SeamLayout-lg4c2.out`, exit 0). The
   sweep's other results stand: 94/94, and 35 → 34 sorry warnings, by name.
7. **§7 and §12, "No new public declaration" and "1 public".** These count source declarations.
   In the elaborated environment the module also adds public constants:
   - the target's 19 `_proof_` auxiliaries;
   - six instances that `deriving DecidableEq, Fintype` generates for the three private
     inductives (`Turing.instDecidableEqSl_Key`, `…Sl_PairPhase`, `…Sl_SplitPhase`,
     `Turing.instFintypeSl_Key`, `…Sl_PairPhase`, `…Sl_SplitPhase`), with 18 auxiliaries.

   (Review `out/15-ax-head.out`, MODULE PUBLICS.) The instances' types are private, so no other
   file can use them, and no other file declares these names (`out/41-name-clash.txt`). Landed
   code does the same.
