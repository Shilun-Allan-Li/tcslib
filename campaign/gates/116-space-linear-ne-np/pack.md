# Gate 116: closing the linear-space/NP separation with E-PAD

Audit [PR #229](https://github.com/Shilun-Allan-Li/tcslib/pull/229),
`lean/space-linear-ne-np`. The user selected **Codex**. Published Lean head:
`d143c091a8ef25cfd42cb0ed650dc3faa9b5a7c4`. The source base is `96daf38bc82ea21dab18da257fc517ca0bd59ff6`; the final bundle header pins the later records snapshot.
The two-module current-campaign merged-tree replay passed on **oleans-mlin1**, zero failures
and zero static mismatches. The target is admission-free; F6's unchanged admission remains.
All eleven screen-population blobs match the published PR exactly. The user dispatches this
audit and merges only after it closes; this pack does not authorize a merge.

## Scope

The change is confined to `TCSlib/Complexity/SpaceComplexity/Hierarchy.lean`: add the explicitly
approved import of `SpaceComplexity.Padding`, and replace the existing `SPACE_linear_ne_NP`
admission with its already-planned consumer derivation. E-PAD merged as #228 after gate 115
closed. The user had authorized this small consumer PR separately from the fill.

The target statement remains exactly:

```lean
theorem SPACE_linear_ne_NP : SPACE (fun n => n + 1) ≠ NP
```

No new public/source declaration, private declaration, definition, host, rename or statement
change is introduced. All 47 source declarations survive with the same headers, visibility and
order: **4 public / 43 private**. Every declaration's full text except the target proof body is
unchanged. Source lines are 2505 → 2518. The new body is 13 lines; its existing proof sketch
continues to describe the argument.

The unchanged same-home helper `sph_linear_ne_NP_of_padding` already proves the separation from
the space hierarchy and one precise padded-language hypothesis. The new body supplies that
hypothesis by `mem_SPACE_padLang` at `S n = n² + 1`, `T m = m + 1`, `C = 1`, `d = 2`. The
language equality is proved using `Set.ext` and the published `mem_padLang_iff`; no foreign
definition is unfolded. The inequality at the padded length uses `Nat.pow_le_pow_left` and
arithmetic. The target now uses only the standard three axioms.

## Sources and declared normalization

The source is [AB09, Exercise 3.2]. `review/source-reference.md` supplies a short excerpt and
the official Princeton reproduction, with its indexed-text retrieval limit. The exercise
asserts a class inequality and cautions against claiming a containment direction.

The frozen formal statement uses the positive normalization `n + 1`. Its existing docstring
explains the library's visited-cell convention and the literal `SPACE(n)` zero-work-tape
phenomenon. This is an inherited declared deviation, not a newly strengthened claim. The gate
asks the auditor to verify that the new dependency chain proves exactly this frozen statement.

## Brief for the auditor

Follow `campaign/standards/TEMPLATE.md`, `policy.md`, `workflow.md` and the duplication ledger.
Do not review kernel-checked tactic scripts for logical correctness. Definitions, statement
fidelity, hypotheses, semantic reuse, rule 10 and cumulative debt are the audited surface.

1. Restate the defining meanings of `SPACE`, `NP`, `padLang` and `pairEncode` before comparing
   them to their docstrings. They are unchanged context; check that the instantiated padding
   theorem supplies the exact language and resource bound required by the frozen helper.
2. Check the mathematical route: assuming equality of linear space and NP, a language in
   quadratic space has a padded member language in linear space, hence in NP. Polynomial-time
   padding and preimage closure put the original language in NP and thus linear space,
   contradicting `space_hierarchy`. Verify that malformed padded words cannot leak into the
   image language and that the preimage argument uses the existing pairing injectivity.
3. Attempt at least **three adversarial instantiations**. Include the empty original word
   (pad length 1, paired length 3), a one-bit word (pad length 4, paired length 8), and the empty
   language witnessed by a zero-work-tape constant rejector/source space multiplier zero.
   Separately challenge the difference between class inequality and either direction of
   noninclusion, and the positive normalization. The published padding theorem, not a new
   unproved decider, pays the validation cost.
4. Verify the source/public freeze and distinguish source declarations from compiler constants:
   the source public count remains four, while the non-private compiled census is **4 → 5**.
   The sole addition is the internal theorem `Complexity.SPACE_linear_ne_NP._proof_1_1`.
   The complete module census, including private constants, is **137 → 138**, with 133 private
   constants on each side and no removed, renamed or moved constant.
5. Challenge the rule-10 evidence. The target-plus-auxiliary inventory reaches exactly four
   direct foreign TCSlib definitions: `SPACE`, `NP`, `padLang`, `pairEncode`. All four are
   effectively sealed around the new target section, with eight positive/eight negative
   controls and no exclusions. The claim concerns the new section, not every legacy proof in
   Hierarchy. The existing helper is same-home and its body is held byte-for-byte fixed.
6. Inspect the semantic reuse and new inline steps, not only whole statements. The only new
   explicit rewrite argument is a proved local language equality; the padding membership
   reading is the published iff. No machine, host, code traversal, buffer-indexing argument or
   private cross-file API is added. Challenge any new text-screen candidate against the public
   API and cumulative ledger; do not infer a new debt acknowledgment from a passing screen.
7. Verify the import and downstream consequences on the final published PR/replay. A new import
   may change downstream simp sets. The supplied two-module current merged-tree
   replay checks that import consequence, with zero failures/static mismatches. F6's unchanged `space_universal` admission remains separate
   and is not a dependency of the newly proved separation.

## Evidence and limits

Primary independent review and receipts are under `review/`. The complete source populations
are in `review/screen/population-{base,head}.txt`; both contain the same eleven full files:
Hierarchy, Padding, SpaceComplexity.Basic, ClassNP.NP, TuringMachine.Encoding, ClassNP.PClosure,
SpaceComplexity.Constructible, Configuration, Deterministic, Nondeterministic and Finite. The
additional model files provide the seal/default-simp context. Every file is supplied in full.

`review/README.md` distinguishes the performed source, lint, axiom/census, seal and screen
checks from the parent's completed replay/publication checks in `evidence/merged-tree/`. `review/source-freeze.json`, complete header files,
the source diff and SHA-256 pins cover the actual fixed source. An `input := x` inside a binder
is not treated as a proof delimiter; a parser control is retained.

The primary `review/Inventory.lean.txt` inventories the target and all compiler auxiliaries
whose full names extend it. The target uses `[propext, Classical.choice, Quot.sound]`; its one
auxiliary uses `[propext, Quot.sound]`. Both compiled census populations are unfiltered with
respect to generated/internal constants, with full kind/module-owner information.

The strong source seal removes all four default-simp definition unfoldings present in this
import closure: `Turing.Action.apply`, `Turing.Cfg.init`, `Turing.MultiTapeTM.initCfg` and
`Turing.NDTM.initCfg`. It elaborates with zero errors and only the unchanged F6 admission
warning. All four pointwise and four parameter-abstracted equations close unsealed; each fails
sealed, with exact diagnostic-line multiplicities and the expected exit status. No unsafe
reducibility option is used. The earlier seal with defaults present is retained separately.

The parent's inherited-comment `evidence/Metadata.lean.txt` is **preliminary**, not the primary
inventory attestation: its old prose overdescribes the later target filter. The accurately
documented `review/Inventory.lean.txt` and its raw output are the primary evidence.

Campaign per-file lint remains **0 FAIL / 1 inherited size WARN**. The policy lint retains the
same two findings (missing Main definitions heading and size); no new policy finding is added.
The standing no-size-driver ruling applies. No blueprint file or public name binding changes;
this packet does not claim a fresh strict global blueprint validation.

The copy-text screen's raw outputs and pair delta are provided in `review/screen/`, with a
semantic classification. A text screen enumerates candidates; it is not a proof of semantic
uniqueness. The existing duplication ledger remains the accounting baseline. Every execution
receipt names its actual inputs and statuses. The completed replay, precheck, full order and
static comparison are in `evidence/merged-tree/`. The source match receipt independently checks
all eleven published population blobs; earlier pending fields describe their original run time.

## Findings

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Include a verdict line with blocker/major/minor/note counts and the definition restatements and
adversarial analysis even if the findings table is empty. Gate closure requires zero blockers
and zero majors, with minor dispositions recorded. Seyoon merges after gate closure and the
current-campaign replay; this internal review does not close the external gate.

**Deliver your findings as a downloadable file named `space-linear-ne-np-findings.md`** (the
findings table and the verdict line, no other wrapping), and also paste its content in your reply.
