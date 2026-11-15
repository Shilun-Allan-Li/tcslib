# Gate 138 · Ladner fill 3: the polynomial-time candidate test (PR #320)

**Not yet clear to merge** · PR #320 is a draft. Seyoon dispatches and merges.
The Lean commit is `fc72e67b25e79231fbb04a324d9978d9e9f00349`, against campaign Lean
`fe8a8520f65a9feaa4c960c11874b68ebf8798db` (the campaign after #310). This is the first audit.

## Scope

Target 1 of Ladner's theorem [AB09, Theorem 3.3 and its proof] is
`Complexity.ladnerH_polyTime`. Codex's fill 3, under the brief
`campaign/fills/ladner-poly-candidate/briefs/ladner-poly-candidate.md` (bundled; pre-shipped at the
base, `preship/`), builds part A, up to the polynomial-time candidate test. It proves no Ladner
target. The PR changes only `Diagonalization/Ladner.lean`, in three commits:

1. `ec0e501d`: Codex's delivery, verbatim. It adds 57 private declarations (1,054 lines), from
   the route's `values` and `shortWords` through the binding handoff
   `ladner_candidate_FP (linear : …) : PolyTimeComputable (fun S => [ladner_candidate S])`.
   The delivery (final zip and two checkpoints, with Codex's `REPORT.md` and logs) is in the
   carrier under `delivery/`; its report is data, re-checked here.
2. `3a42f28f`: the maintainer's dedup repair, ruled by Seyoon on 2026-11-15 before gating. The
   copy screen of the delivery found three in-file copies, each now a private helper:
   - `ladner_padSyntax_FP`, the padding-syntax FP proof for an input-dependent exponent. Fill 2's
     `ladner_syntax_FP` and fill 3's `ladner_tableSyntax_FP` are its instances; the delivered
     `ladner_tableSyntax_FP` reproduced 87% of `ladner_syntax_FP`.
   - `ladner_bits_prepend`, the bits-prepend induction, formerly inline in fill 1's
     `ladner_padded_index` and re-proved in fill 3's `ladner_shortWords_complete`. Both now cite
     it.
   - `ladner_index_lt_loglog_FP`, the test "a canonical index lies below the double logarithm
     of a length", shared by `ladner_validQuery_FP` and `ladner_ctxGuard_FP`.
3. `fc72e67b`: the two-line binary-length FP step, repeated in eleven proofs of fills 2 and 3,
   becomes the private `ladner_lengthBits_FP`.

No statement changes. The only existing proof bodies that change are those of fill 1's
`ladner_padded_index` and fill 2's `ladner_syntax_FP` and `ladner_parse_FP`.
`patch/campaign-to-head.patch` and `patch/delivery-to-head.patch` in the carrier show the
whole change and the maintainer's part.

## Brief for the auditor

1. **The mathematics.** Check that each part A definition has the route's meaning, and that
   `ladner_candidate_FP` proves the binding handoff from the stated `linear` hypothesis alone.
   Check the route's risks:
   - the simulator's cost is charged in the numeric deadline, not its bit length;
   - nested SAT and simulator work is charged inside the scan step's FP proof;
   - the size bounds hold on every reached state (`ladner_count_size`, `ladner_test_size`),
     including malformed and post-termination states;
   - malformed inputs cause no long loop or huge allocation (`powCap` throughout);
   - no monotonicity of `ladnerH` is assumed.
2. **Scope and freeze.** Only `Ladner.lean` changes. Every new declaration is private. No
   import, attribute, `sorry`, `admit` or axiom is added. The four admitted targets and every
   other existing declaration are byte-identical, except the three re-pointed proof bodies
   above, whose statements are unchanged.
3. **Rule 10.** Check each proof reads other files' TCSlib definitions only through published
   equations. The delivery's boundary table lists the readings. Two checks:
   - **Seals** (`seals/`): all 45 changed or new proofs pass with every other-file definition
     they reach irreducible: 38 definitions, 37 by a local attribute. The 38th,
     `BinArith.decWords`, is defined by well-founded recursion, so Lean already makes it
     irreducible (`checks/reducibility.log`); the harness lists it under
     `inherently_irreducible` instead of re-sealing it. The delivery's own seal disclosed the
     same fact.
   - **Controls** (`controls-part0/`): the 74 paired controls, two per attribute-sealed
     definition, each close natively and fail sealed. `decWords` has no native `rfl` control,
     for the same reason.

   The seal and control scripts gained only this list (`checks/irreducible.json`; the
   scripts are under `drivers/`). Also check the `rw`/`simp`/`unfold` arguments: the
   delivery claims none names a foreign definition.
4. **Standards.** Docstrings cite [AB09, Theorem 3.3 and its proof] or library declarations;
   every proof over 20 lines has a proof sketch; no campaign labels appear in Lean text.
5. **Duplication.** Check the copy screens and their dispositions
   (`evidence/PAIR-DISPOSITIONS.json`).
   - **Narrow** (`Ladner.lean` alone): BASE 32 declarations and 1 pair; the delivered head 82
     and 58; this head 86 and 53, with 52 new and none gone. Reproduced text fell from 14,266
     to 9,488 characters.
   - **Wide** (`Ladner.lean` with eleven API files; population in
     `screen-wide/POPULATION.txt`): BASE 591 and 248; the
     delivered head 641 and 319; this head 645 and 312, with 64 new and none gone.

   The four repairs are listed under `repaired`. The delivered and intermediate screens are in
   the carrier (`screen-delivered/`, `screen-wide-delivered/`). Every remaining new pair is
   classified:
   - `fp-idiom`: polynomial-time closure chains shared by proofs of different predicates;
   - `spec-mirror`: the route's specification definitions (`ladner_stage` and
     `ladner_candidate` mirror `ladnerH`'s selection);
   - `step-skeleton`: the iterator-step skeleton, as among Mul's step proofs at base;
   - `orbit-idiom`: the `Function.iterate` orbit induction opening;
   - `helper-citation`: text shared with a new helper is its call.

   Check whether any classification hides a copied argument. The screen is textual: also
   check semantically that no new helper re-proves a public fact in the import closure (`evidence/logs/proof-search.log`
   in the delivery zip; the maintainer found none beyond the repaired bits-prepend
   induction). Report any proof a new helper should cite instead.
6. **Delivery conduct (data).** The report discloses three things. Codex coordinated with other
   jobs on the Mac through a shared slot protocol, reserving one slot for about five minutes
   between modules; it logs no overrun of the three-process cap. It deviated from pull-first
   ordering in one metadata-only exchange push. And it has a retained local worktree. None
   touches source; check that the exchange commits touch only the inbox folder.

## Evidence

- `evidence/REPLAY.json`: the merged-tree replay of the downstream closure (Ladner and the
  `Diagonalization` facade) on the campaign snapshot after #310 (876 objects; prospective tree
  `f46a0aed394a55192e1f6555c90a135f1d537cf5`). 2 passed, 0 failed; the 4 admissions are the
  remaining Ladner targets. Only `Ladner.olean` changes.
- Metadata: all 45 changed or new proofs use standard axioms only. `probes/LadnerAx.log`
  prints 47 of them: the 42 new theorems; the re-pointed `ladner_padded_index`,
  `ladner_syntax_FP` and `ladner_parse_FP`; and both fill 1 targets. Each uses at most
  `propext`, `Classical.choice` and `Quot.sound`. Lint: no new finding.
- `evidence/DATA-CARRIER.json` and its recovery map hold 129 logical files, including the
  delivery zips, both screens with their population sources at BASE and HEAD, and the
  delivered and pre-repair screens. Decode each gzip+base64 blob and check its SHA-256 and
  byte count.

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named `gate138-ladner-poly-candidate-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
