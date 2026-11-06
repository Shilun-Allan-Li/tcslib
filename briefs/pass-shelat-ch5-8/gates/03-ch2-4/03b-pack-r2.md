# Gate 03b ([PS10] ch. 2–4, one-wayness and collections), round 2: external closing audit pack

**What is audited:** the repairs of round 1, on `cryptography/pass-shelat-ch2-4` at
`e79397eaf68b156b9db091f464741f6eb75b9c28` (the branch after #201 merged; its Lean files are #201's head `0c348ff9`).
- **Round 1** audited `a3c5fa8b72e50939822f22364647dc844a3914a0` and found **0 blockers, 1 major (#1), 3 minors and 10 notes**; after the review, 1 major and 4 minors (#12 (c) raised) (`gate03b-findings.md`, in the bundle,
  verbatim).
- **The repair:** PR #198 (G3-1: the field `Collection.encD_decD`, every instance proved, derived lemmas; G3-7 (c): `glPad`'s `henc` cost; 03b's minors), merged; later changes to this pack's files come from #201 (03a's docstring repairs to `OneWay.lean`). The full delta is `evidence-r2/03b/repair.diff.txt`; each round 1
  row's resolution is in `resolutions-03b-r1.md` (both in the bundle). The maintainer's review of
  round 1 is `review/gate03b-review.md` (in the bundle).
- **The deliverable:** **`gate03b-r2-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10], 3rd ed., January 2010 (PDF; book page = PDF page −
12).

## Brief for the auditor

Round 2 does two things.
1. **It verifies the round 1 resolutions.** For each row of `resolutions-03b-r1.md` (the
   findings and the review's missed items `M1`, …) say whether the resolution is adequate:
   - **fixed**: the defect is gone, and the fix introduces no new one;
   - **recorded** or **scheduled**: accepted as declared, or deferred to a named PR or gate, and
     the record is accurate;
   - **not resolved**: say why.
2. **It audits the changed surface afresh** (section A of `evidence-r2/03b/repair.diff.txt`):
   - restate every new public declaration listed below in your own words, and say whether its
     statement is what its docstring claims;
   - check every changed statement and docstring;
   - look for regressions: anything round 1 accepted that the repair broke.

Pack 03a's brief and severity guide apply (03a's pack is in the bundle). Attempt at least
**three adversarial instantiations** against the changed surface. Do not give a blanket
approval.

## What changed

- **Statements:** `Collection` gains the field `encD_decD`, so every instance (the candidates, `glPad`, OT's collections) now proves it; no theorem statement of this pack changes otherwise.
- **New public declarations:**
- `Collection.encD_decD` (a new **field** of `Collection`: decoding is canonical) and the derived
  `Collection.decD_eq_some_iff`, `apply_of_decD`, `eval_of_decD`, `sample_eq_encD`,
  `HardCore.evaluator`, `TrapdoorCollection.inv_eq_encD`, `TrapdoorCollection.eval_inv`;
- `ofFn_of_decodeFin_eq_some` (`CollectionsHelpers.lean`, new file: the split of
  `Collections.lean`);
- `natToList_length_listToNat`, `natToList_val_natCast` (`Arithmetic.lean`: numerals are
  canonical);
- the non-vacuity witnesses `not_weakOneWay_id`, `not_worstCaseOneWay_id`,
  `FunFamily.invProbAt_ofString_id_eq_one` (`OneWay.lean`), `FunFamily.not_toCollection_oneWay_id`
  (`Collections.lean`).
- The instances' proofs are in packs 03f1, 03f2 (candidates) and 03i (`HardCoreCollection.lean`); they are context here (section B of the diff).

## Scope

| Item | Where |
|---|---|
| Round 1 findings, review, resolutions, repair diff | `findings/gate03b-findings.md`, `review/gate03b-review.md`, `resolutions-03b-r1.md`, `evidence-r2/03b/repair.diff.txt` |
| Under audit (the changed surface), at the pin | `TCSlib/Cryptography/Asymptotic/{OneWay, Collections, CollectionsHelpers, Permutations}.lean`, `Candidates/Arithmetic.lean` |
| Context | `03b-pack.md` (round 1), `03a-pack.md` (common brief), `policy.md`, `briefs/pass-shelat/DESIGN.md`, the duplication ledger (scheduled rows) |
| Out of scope | tactic proofs; the scheduled clean-up (G3-5, DL-9 onward) beyond checking that its record is accurate |

## Attestations (maintainer execution claims; evidence under `evidence/b2/` in the bundle)

### Attestation results at `e79397eaf68b156b9db091f464741f6eb75b9c28` (evidence under `evidence/b2/`)

1. **Elaboration** (`replay.log`): the closure of this pack's files, 66 modules, each
   checked alone into a fresh olean tree by `scripts/lean_check_tree.sh`: all pass, 0 errors;
   17 `sorry` warnings in the closure.
2. **Axioms** (`axioms.log`): 111 prints of every public theorem and lemma in this pack's files:
   111 use only the standard axioms, and 0 depend on `sorryAx`; any other axiom is listed
   in the log.
3. **Admissions** (`admissions.txt`): 0 declarations in this pack's files contain `sorry`.
4. **Lint** (`lint.log`): `scripts/style_lint.py` on this pack's files: 0 findings in 5 files.

The replay is the 416-module replay at `af91d53a` overlaid with the re-check of the 98 modules
downstream of #201's changes (`evidence-repairs/03ac/replay.log`); each line of `replay.log` is the
newest check of its module, and the Lean files at the pin equal #201's head.

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Plus one line per round 1 row: `<row>: fixed / recorded / scheduled / not resolved — <reason>`.

Severity guide: **blocker** (a downstream phase would build on a wrong statement); **major**
(fixable but materially misleading, or debt that needs explicit acknowledgment); **minor** (an edge
case, naming or attribution); **note** (no change required). The gate closes at **0 blockers and 0
majors**.
