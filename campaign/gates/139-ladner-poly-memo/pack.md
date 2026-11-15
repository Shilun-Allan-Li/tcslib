# Gate 139 · Ladner fill 4: `ladnerH_polyTime` (PR #321)

**Not yet clear to merge** · PR #321 is a draft. Seyoon dispatches and merges.
The Lean commit is `80c18b7ec5bb9e30d838be8dc6fec9c79a0384f3`, against campaign Lean
`1320a5c8ce93f4644c2c92ed32e2768ed07ea9bb` (the campaign after #320). This is the first audit.

## Scope

Target 1 of Ladner's theorem [AB09, Theorem 3.3 and its proof] is
`Complexity.ladnerH_polyTime : PolyTimeComputable (fun x => Nat.bits (ladnerH x.length))`.
Part A (through the private `ladner_candidate_FP`) merged as #320. Codex's fill 4, under the
brief `campaign/fills/ladner-poly-memo/briefs/ladner-poly-memo.md` (bundled; pre-shipped,
`preship/`), proves it. The PR changes only `Diagonalization/Ladner.lean`, in two commits:

1. `9e3df79e`: the reorder Seyoon ruled on 2026-11-15. The five admitted declarations
   (`ladnerH_polyTime`, `SAT_H_mem_NP`, `SAT_mem_P_of_padSAT_NPHard`, `SAT_H_intermediate`,
   `ladner`) move, byte-identical and in order, to the end of the file under the new header
   `/-! ### The theorem and its remaining targets -/`, so that each target follows the leaves
   its proof needs. It is the pre-shipped `preship/Ladner-move.patch.txt` applied verbatim
   (result SHA-256 `4c9a04c3…`).
2. `80c18b7e`: Codex's delivery, verbatim. It adds 21 private declarations, the route's part B,
   between part A and the moved targets:
   - the selection scan (`ladner_selectCtx`/`Init`/`Step`/`Out`), with
     `ladner_candidate_selectCtx`, `ladner_stage_spec`, an exact orbit equation
     `ladner_select_orbit` in place of the route's invariant/measure helpers,
     `ladner_select_size`, `ladner_select_readout` and `ladner_stage_FP`;
   - `ladner_stage_correct`: a stage over a table of correct earlier values is `ladnerH` at
     the table's length;
   - the memo table (`ladner_memoInit`/`Step`), with `ladner_memo_orbit`, `ladner_memo_size`
     (`4(|z|+1)^2`) and `ladner_memo_readout`.

   It then replaces `ladnerH_polyTime`'s `sorry` by the pre-shipped assembly: the public
   iterator on the memo step, `getW`, and the merged `ladner_candidate_FP` with the public
   `SAT_exists_linear_verifier`.

No maintainer repair follows the delivery. The delivery (final zip and checkpoint, with Codex's
`REPORT.md` and logs) is in the carrier under `delivery/`; its report is data, re-checked here.

## Brief for the auditor

1. **The mathematics.** Check that `ladnerH_polyTime` is proved as stated, and that the
   pre-ship's binding helpers keep their meanings: `ladner_stage_FP`, `ladner_stage_correct`
   and `ladner_memo_readout`. Check the route's risks:
   - entries are counted by `countW`, not serialized length;
   - the size bounds hold on every state of both loops, including after the selection
     finishes;
   - a never-successful selection returns the exact cap;
   - `stage_correct` applies `padSAT_congr` only to prefixes below the table's length (empty
     table included);
   - no monotonicity of `ladnerH` is assumed (`ladnerH_le` is per index).
2. **Scope and freeze.** Only `Ladner.lean` changes. Check that the first commit is exactly the
   pre-shipped move, so the five moved declarations are byte-identical. Check that the second
   commit only inserts the private section and replaces `ladnerH_polyTime`'s body. No import,
   attribute, public declaration, `sorry`, `admit` or axiom is added; the other three targets
   remain admitted.
3. **Rule 10.** Check that each proof reads other files' TCSlib definitions only through
   published equations (the delivery's reader table lists them). Two checks:
   - **Seals** (`seals/`): all 16 new or changed proofs (the 15 new theorems and
     `ladnerH_polyTime`) pass with every other-file definition they reach irreducible: 25
     definitions, 24 by a local attribute. The 25th, `BinArith.decWords`, is defined by
     well-founded recursion, so Lean already makes it irreducible
     (`checks/reducibility.log`); the harness lists it under `inherently_irreducible`, as in
     gate 138.
   - **Controls** (`controls-part0/`): the 48 paired controls (two for each of the 24
     attribute-sealed definitions) each close natively and fail sealed.

   Also check the `rw`/`simp`/`unfold` arguments; the delivery's `rewrite-arguments.log`
   lists them.
4. **Standards.** Docstrings cite [AB09, Theorem 3.3 and its proof] or library declarations;
   every proof over 20 lines has a proof sketch; no campaign labels appear in Lean text.
5. **Duplication.** Check the copy screens and their dispositions
   (`evidence/PAIR-DISPOSITIONS.json`).
   - **Narrow** (`Ladner.lean` alone): BASE 86 declarations and 53 pairs; HEAD 105 and 73,
     with 20 new and none gone.
   - **Wide** (`Ladner.lean` with Basic, AddSub, Words, Loops, Iterate and PolyTimePairing;
     population in `screen-wide/POPULATION.txt`): BASE 202 and 117; HEAD 221 and 148, with 31
     new and none gone. Codex's own final screen on the same population reported the same
     totals.

   Every new pair is classified:
   - `fp-idiom`: polynomial-time closure chains;
   - `step-skeleton`: the iterator-step skeleton shared by `ladner_selectStep_FP` and fill 3's
     two scan steps;
   - `orbit-idiom`: the `Function.iterate` orbit induction opening;
   - `helper-citation`: one pair, where `ladner_selectStep_FP` calls
     `ladner_index_lt_loglog_FP` (checked against its source text).

   The largest reproduces 439 characters. Check semantically that no new helper re-proves a
   fact already in the import closure or the file's earlier leaves (the delivery's
   `helper-search.log`). For example, `ladner_stage_spec` reads the table-based
   `ladner_stage` by `Nat.find_spec`/`Nat.find_min`, as `ladnerH_le` and fill 1's helpers read
   `ladnerH`.
6. **Delivery conduct (data).** Codex used the shared slot protocol with the process-count gate
   (148 launches, no waits) and disclosed it; its two exchange commits touch only the inbox
   folder.

## Evidence

- `evidence/REPLAY.json`: the merged-tree replay of the downstream closure (Ladner and the
  `Diagonalization` facade) on the campaign snapshot after #320 (876 objects; prospective tree
  `ce2850d8de68d281eee7edee55012f08ff47f763`). 2 passed, 0 failed; the 3 admissions are the
  remaining targets (`SAT_H_mem_NP`, `SAT_mem_P_of_padSAT_NPHard`, `SAT_H_intermediate`). Only
  `Ladner.olean` changes.
- Metadata: all 16 new or changed proofs use standard axioms only. `probes/LadnerAx.log`
  prints every private theorem of the file and the targets: `ladnerH_polyTime` and both fill 1
  targets print exactly `propext`, `Classical.choice`, `Quot.sound`. Only the still-admitted
  `SAT_H_mem_NP` shows `sorryAx`. Lint: no new finding.
- `evidence/DATA-CARRIER.json` and its recovery map hold 113 logical files, including the
  delivery zips, both screens with their population sources at BASE and HEAD, the move patch
  and the patches of both commits. Decode each gzip+base64 blob and check its SHA-256 and byte
  count.

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named `gate139-ladner-poly-memo-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
