# Round 5 evidence corrections and scope

Maintainer review, 2026-11-06 PST, of the verbatim round-5 findings. Audited head: `9ac1c4260adb8fbfe8c6f50df7786dbdd015656e`.
The frozen pack is at records `c39f0e118f1c0f89325cbc828401a5c024bb36d1`; these are post-audit corrections. No Lean head moved.

## File sets and replay

- **PR delta:** 26 Lean files against `7018d13e243df4d8b54b99444c34c934199755f5`: 25 implementation files plus the root
  `TCSlib.lean` facade. The facade adds one import of `TCSlib.Cryptography.Games.Bridges`.
- **`pr-files.txt`:** the 25 implementation files; it omits the root facade.
- **Seal set:** 26 modules: those 25 implementation files plus unchanged
  `TCSlib/Cryptography/Foundations/Probability.lean`. It does not contain the root facade.
- **Replay:** the historical final logs contain 108 plus 23 successful rows, including Checks;
  the root facade was not replayed. The independent auditor reports rebuilding the 122-module
  head import closure and sealing the 26 targets. These are distinct file/module sets.

[file-sets.json](file-sets.json) records the exact lists and revision pairs.

## Candidate counts

The historical table used pre-notation counts in seven rows. Reading the actual candidate files
after filtering gives **260 active file/name pairs**, plus **one** already globally irreducible
pair (`ggmFrom` in `PRFLemmas.lean`). The notation filter dropped seven `PolyExpr.eval` rows and
zero `glNeed` rows. `PolyExpr.eval` stays semireducible under Q1; it was not made reducible.

[post-filter-candidates.md](post-filter-candidates.md) gives the corrected per-file counts.
The corrected main seal table uses these counts. The original headers inside the candidate files
describe their pre-filter generation; they are retained as historical inputs.

## Comparisons

`evidence-r5/stmtdiff-vs-merge.txt` compares **`849b86b82bd19731aa70b4039252761d68d2fff2` → `4d99b0cb7241b1f431476e1b7cf2f5a551d57d62`**.
It is an intermediate repair comparison, not a direct comparison with round 4's audited head.

The direct comparison is **`a588adfed01eefe6971abd0846e3938ad02e8624` → `9ac1c4260adb8fbfe8c6f50df7786dbdd015656e`**, over the 26 PR-delta files:

- `decls2.py`'s public source headers: **26 added, 2 changed, 0 removed**.
- The historical docstring/source comparator, which also includes private declarations:
  **27 added, 2 statement changes, 9 docstring changes, 0 removed**.

The two changed public statements are `NUPPT.runAt_preComp` and `prfScheme_multiEncDist`;
the auditor checked their tape-preserving equivalences and accepted the old-form propositions.
Intervening API additions and documentation edits are included in this direct comparison.
Neither source comparator certifies ambient binders or universes: the separate elaborated-signature
classifier does that, and the auditor reports reproducing it.

See [the public headers](round4-to-head-headers.tsv) and
[the docstring/source comparison](round4-to-head-docs-and-source-statements.txt).

## Admissions and axiom scope

There are **four** explicit deferred `sorry` proofs in the audited implementation set, all in
`Games/Efficiency.lean`:

1. `exists_handlerMachine`;
2. `exists_interactiveHandlerMachine`;
3. `exists_toCompOn_of_toComp`;
4. `exists_toOracleAdversary_of_bitCodec`.

The worker report's former sentence that the 26 files and Checks have no `sorry` was incorrect.
The 198-theorem axiom print covers its specified eight files. The auditor's broader 433-public-theorem
print across the full seal set found `sorryAx` only in the four deferred targets. These scopes must
not be conflated.

## Tool limits and repair

- The collector traverses stored constants, including private/generated constants and the
  documented transparent-body/lemma-statement paths. An anonymous command need not leave such
  a constant. Its collection coverage is therefore not universal command coverage.
- The source scanner resolves supported textual tactic forms against TCSlib names. It does not
  check explicit core/Mathlib definition unfolds. Its `show`/`change` column is conditional on
  seal coverage, not an independent check of every such command.
- The comment/blank-line continuation false negative is repaired in `tools/scan.py`.
  [scanner-regressions.log](scanner-regressions.log) reproduces the old failure and passes 12
  focused cases, checking hit line numbers. These are Python text-scanner tests, not new Lean
  executions of the fixtures. [scan-head-hardened.log](scan-head-hardened.log) remains 0/0/0
  on the same head, candidate and seal inputs.
- The anonymous-command collector gap remains open. The auditor reports all 26 targets passing
  a conservative import-closure seal (6,322 file/name pairs), which supplies coverage for this
  gate. A future whole-file seal needs conservative candidates or command-aware collection, plus
  an anonymous-command control; a stored-constant list alone is insufficient.

The four inherited `Function.comp` occurrences are listed in
[inherited-core-unfolds.tsv](inherited-core-unfolds.tsv) and queued for clean-up. The two formula
docstrings are also queued, with a prepared comment-only patch. Neither proposed Lean patch has
been applied; the core-equation patch still needs Lean verification in its landing PR.

Reproduce this record reconciliation with `python3 -I .../evidence-r5-review/review.py` and
the scanner checks with `python3 -I .../evidence-r5-review/check-scanner.py`, from the campaign
root. Frozen historical tool behavior is available at the pack's records commit.
