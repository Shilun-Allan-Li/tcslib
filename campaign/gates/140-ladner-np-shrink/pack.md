# Gate 140 · Ladner fills 5 and 6: targets 2 and 5 (PR #322)

**Not yet clear to merge** · PR #322 is a draft. Seyoon dispatches and merges.
The Lean commit is `266e6e8cc5322429024e2e11ee53c7afa13c0a6f`, against campaign Lean
`34643146ee1fe6bf6d7ffdf2e543e8342a3e16a0` (the campaign after #321). This is the first audit.

## Scope

Two targets of Ladner's theorem [AB09, Theorem 3.3 and its proof]. Seyoon dispatched the two
Codex fills in parallel on the same base, and ruled one combined gate (2026-11-15). The briefs
(bundled, with their pre-ships) gave the two new sections disjoint anchors in
`Diagonalization/Ladner.lean`, the only file the PR changes. There are three commits:

1. `cded2d38`: fill 5, Codex's delivery verbatim (brief `campaign/fills/ladner-np/`). It
   proves target 2, `SAT_H_mem_NP : SAT_H ∈ NP`, with four private declarations, placed
   before the targets' section: `ladner_verifier` (parse the final separator, check the unary
   suffix, check SAT of the prefix with the linear verifier), `ladner_verifier_P`,
   `ladner_verifier_equiv` and `ladner_padded_NP`. The target follows from
   `ladnerH_polyTime` and `SAT_exists_linear_verifier`. Its proof sketch is rewritten, as the
   brief allows, because the old sketch guessed the prefix.
2. `791f376e`: fill 6, Codex's delivery verbatim (brief `campaign/fills/ladner-shrink/`). It
   proves target 5, `SAT_mem_P_of_padSAT_NPHard`, the shrinking argument, with fifteen private
   declarations placed after the finite-table leaves. It uses none of targets 1–4.
3. `266e6e8c`: a merge commit with both as parents. Its tree is git's clean three-way merge of
   the two deliveries over the base (`git merge-file` reproduces it), with no hand edits.

No maintainer repair follows. The deliveries (final zips and checkpoints, with Codex's reports
and logs) are in the carrier under `delivery/`; the reports are data, re-checked here.

## Brief for the auditor

1. **Target 2.** Check that `SAT_H_mem_NP` is proved as stated and that `ladner_padded_NP` has
   the pre-ship's meaning. Check the route's risks: the SAT reader's concatenation
   `prefix ++ u` versus the NP reader's `pairEncode y u`; the last false separator, all-true
   rejection, the empty prefix, exponent zero and `0 ^ 0`; the power compared only through
   `powCap`; `hp` applied to the prefix; and the certificate bound.
2. **Target 5.** Check that `SAT_mem_P_of_padSAT_NPHard` is proved as stated, and that the
   pre-ship's binding helpers keep their meanings (`ladner_reduction_shrinks`,
   `ladner_shrinkStep_FP`, `ladner_shrink_progress`, `ladner_shrink_final_readout`). Check the
   route's risks:
   - padding validity is decided before shrinking;
   - the two exceptional sets (input length `< K`, prefix length `< B`) each have a finite
     table;
   - a terminal `[false]` differs from the live flag `[]`;
   - every power stays capped;
   - each round makes exactly one shrinking call;
   - the size bound holds on every reached state;
   - the square bound holds for every syntactically valid output;
   - no monotonicity of `h` is assumed.
3. **Scope, freeze and merge.** Only `Ladner.lean` changes. In each delivery, check that
   removing its new section and restoring its target's body reproduces the base. Check that
   the merge commit's tree is the clean merge. No import, attribute, public declaration,
   `sorry`, `admit` or axiom is added; only target 6 (`SAT_H_intermediate`) remains admitted.
4. **Rule 10.** Check that each proof reads other files' TCSlib definitions only through
   published equations (the reports' reader tables list them; target 5 reads `NPHard` and
   reductions only through `NPHard_iff` and `polyTimeReducible_iff`). Two checks:
   - **Seals** (`seals/`): all 16 new or changed proofs (the 14 new theorems and the two
     targets) pass with every other-file definition they reach irreducible: 24 definitions,
     all by a local attribute. Neither section reaches `BinArith.decWords`.
   - **Controls** (`controls-part0/`): the 48 paired controls, two for each sealed definition,
     each close natively and fail sealed.

   Also check the `rw`/`simp`/`unfold` arguments; each report's `rewrite-arguments.log`
   lists them.
5. **Standards.** Docstrings cite [AB09, Theorem 3.3 and its proof] or library declarations;
   every proof over 20 lines has a proof sketch; no campaign labels appear in Lean text.
6. **Duplication.** Check the copy screens and their dispositions
   (`evidence/PAIR-DISPOSITIONS.json`).
   - **Narrow** (`Ladner.lean` alone): BASE 105 declarations and 73 pairs; HEAD 123 and 78,
     with 5 new and none gone.
   - **Wide** (`Ladner.lean` with PClosure, Reductions, NP, PolyTimePairing, PolyTime and
     Iterate; population in `screen-wide/POPULATION.txt`): BASE 192 and 86; HEAD 210 and 91,
     with the same 5 new and none gone.

   The five new pairs are classified:
   - three `fp-idiom`: polynomial-time closure chains;
   - one `step-skeleton`: `ladner_shrinkStep_FP` versus `ladner_memoStep_FP`;
   - one `helper-citation`: `ladner_shrink_progress` calls `ladner_shrink_terminal_result` four
     times. Their remaining shared text is a one-line measure reading, left inline.

   Check semantically that neither fill re-proves a fact already in the import closure or the
   file's earlier leaves (each report's `helper-search.log`); for example, check that
   `ladner_prefix_square_bound` is new arithmetic and `ladner_verifier_P` reuses the parser and
   syntax leaves.

## Evidence

- `evidence/REPLAY.json`: the merged-tree replay of the downstream closure (Ladner and the
  `Diagonalization` facade) on the campaign snapshot after #321 (876 objects; prospective tree
  `a25f1e984f1b21fb5e882cf370d3b03f065afc82`). 2 passed, 0 failed; the 1 admission is target 6
  (`SAT_H_intermediate`). Only `Ladner.olean` changes.
- Metadata: all 16 new or changed proofs use standard axioms only. `probes/LadnerAx.log`
  prints every private theorem of the merged file and every target: all print at most
  `propext`, `Classical.choice`, `Quot.sound`, except `SAT_H_intermediate` and `ladner`, which
  depend on the remaining admission. `probes/` also holds both pre-ship probes and the
  combined one. Lint: no new finding.
- `evidence/DATA-CARRIER.json` and its recovery map hold 121 logical files, including both
  deliveries, both screens with their population sources at BASE and HEAD, and the patch of
  each commit. Decode each gzip+base64 blob and check its SHA-256 and byte count.

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named `gate140-ladner-np-shrink-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
