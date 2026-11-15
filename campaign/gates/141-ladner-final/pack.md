# Gate 141 · Ladner fill 7: `SAT_H_intermediate`, completing Ladner's theorem (PR #325)

**Not yet clear to merge** · PR #325 is a draft. Seyoon dispatches and merges.
The Lean commit is `b2d562d926a822cc59545fbc89513ca573effbd2`, against campaign Lean
`d811bdaaf5e923b2a57f0453135af5c7ee37713a` (the campaign after #322). This is the first audit.

## Scope

Target 6 of Ladner's theorem [AB09, Theorem 3.3 and its proof] is
`Complexity.SAT_H_intermediate (h : P ≠ NP) : SAT_H ∈ NP ∧ SAT_H ∉ P ∧ ¬ NPComplete SAT_H`, the
last admission of `Diagonalization/Ladner.lean`. The packaging theorem
`Complexity.ladner : P ≠ NP → ∃ L ∈ NP, L ∉ P ∧ ¬NPComplete L` follows from it unchanged.
Codex's fill 7, under the brief `campaign/fills/ladner-final/briefs/ladner-final.md` (bundled;
pre-shipped, `preship/`), proves it in one commit, `b2d562d9`, Codex's delivery verbatim. It
adds eight private declarations immediately before the targets' section:
- `ladner_padWord`, the literal padding map `x ↦ x ++ false :: 1^(|x|^h|x|)`;
- `ladner_bounded_pad_length`;
- `ladner_power_cases_FP`, fixed unary powers for the finitely many exponent values, selected
  by canonical equality tests;
- `ladner_bounded_pad_FP`;
- `ladner_padWord_membership`;
- the pre-shipped `ladner_bounded_pad_reduction`, `ladner_outside_P` and `ladner_not_complete`,
  kept byte-for-byte apart from added docstrings.

It also replaces `SAT_H_intermediate`'s `sorry` by the pre-shipped assembly from targets 1–5. No
maintainer repair follows. The delivery (final zip and two checkpoints, with Codex's report and
logs) is in the carrier under `delivery/`; its report is data, re-checked here.

## Brief for the auditor

1. **The mathematics.** Check that `SAT_H_intermediate` is proved as stated, and that
   `ladner_bounded_pad_FP` and `ladner_padWord_membership` have the pre-ship's meaning. Check
   the route's risks:
   - boundedness is of the exponent's **value**: the FP construction must not rely on a
     bit-length bound alone;
   - the empty prefix pads with `0 ^ 0 = 1`;
   - membership recovers the prefix at the **final** false separator (through the existing
     parser leaves);
   - "outside P" uses target 3 and the SAT collapse; "not NP-complete" reads completeness only
     through `NPComplete_iff`, then uses targets 4 and 5.
2. **Completeness.** Check that `Ladner.lean` has no `sorry` or `admit` left, and that
   `Complexity.ladner` and all six targets print only `propext`, `Classical.choice` and
   `Quot.sound` (`probes/LadnerFinal.log`).
3. **Scope and freeze.** Only `Ladner.lean` changes. Removing the new section and restoring the
   target's body reproduces the base. No import, attribute, public declaration or axiom is
   added.
4. **Rule 10.** Check that each proof reads other files' TCSlib definitions only through
   published equations; reductions go through `polyTimeReducible_iff`. Two checks:
   - **Seals** (`seals/`): all 8 new or changed proofs (the 7 new theorems and the target) pass
     with every other-file definition they reach irreducible: 24 definitions, all by a local
     attribute. `BinArith.decWords` is not reached.
   - **Controls** (`controls-part0/`): the 48 paired controls, two for each sealed definition,
     each close natively and fail sealed.

   Also check the `rw`/`simp`/`unfold` arguments; the report's `rewrite-arguments.log` lists
   them.
5. **Standards.** Docstrings cite [AB09, Theorem 3.3 and its proof] or library declarations;
   every proof over 20 lines has a proof sketch; no campaign labels appear in Lean text.
6. **Duplication.** Check the copy screens and their dispositions
   (`evidence/PAIR-DISPOSITIONS.json`).
   - **Narrow** (`Ladner.lean` alone): BASE 123 declarations and 78 pairs; HEAD 131 and 82,
     with 4 new and none gone.
   - **Wide** (`Ladner.lean` with Reductions, PClosure, PolyTimePairing, Loops and AddSub;
     population in `screen-wide/POPULATION.txt`): BASE 210 and 118; HEAD 218 and 122, with the
     same 4 new and none gone.

   All four are short idioms; the largest reproduces 141 characters. For example,
   `ladner_shrink_progress` and `ladner_padWord_membership` share one `simp` call over the
   existing `ladner_pad_membership`, applied to different parses. Check semantically that no new
   helper re-proves an existing fact (the report's search log): in particular that
   `ladner_padWord_membership` cites `ladner_parse_pad` and `ladner_pad_membership`, and that
   `ladner_power_cases_FP` builds on `polyTimeComputable_unary` and
   `BinArith.polyTimeComputable_mulU`.

## Evidence

- `evidence/REPLAY.json`: the merged-tree replay of the downstream closure (Ladner and the
  `Diagonalization` facade) on the campaign snapshot after #322 (876 objects; prospective tree
  `c0d07c95c23f8f555f338a5e966485308a43db1b`). 2 passed, 0 failed, **0 admissions**. Only
  `Ladner.olean` changes.
- Metadata: all 8 new or changed proofs use standard axioms only. `probes/LadnerFinal.log`
  prints `Complexity.ladner` and all six targets: each depends on exactly `propext`,
  `Classical.choice` and `Quot.sound`. `probes/` also holds the pre-ship probe. Lint: no new
  finding.
- `evidence/DATA-CARRIER.json` and its recovery map hold 109 logical files, including the
  delivery zips, both screens with their population sources at BASE and HEAD, and the patch.
  Decode each gzip+base64 blob and check its SHA-256 and byte count.

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named `gate141-ladner-final-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
