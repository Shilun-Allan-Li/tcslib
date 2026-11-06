# Gate 03c ([PS10] ch. 2–4, hard-core bits and PRGs), round 2: external closing audit pack

**What is audited:** the repairs of round 1, on `cryptography/pass-shelat-ch2-4` at
`e79397eaf68b156b9db091f464741f6eb75b9c28` (the branch after #201 merged; its Lean files are #201's head `0c348ff9`).
- **Round 1** audited `a3c5fa8b72e50939822f22364647dc844a3914a0` and found **0 blockers, 1 major (#1), 5 minors and 5 notes**; after the review, 2 majors (#3 raised) (`gate03c-findings.md`, in the bundle,
  verbatim).
- **The repair:** the 03c repair commit (G3-2: the expansion cost declared; G3-7 (b): Thm 75.4 without `0 < ℓ(n)`; minors and notes 4–11; the collection section split off into `HardCoreCollection.lean`), merged in #201; G3-7 (c) (`glPad`'s `henc` cost) is #198's. The full delta is `evidence-r2/03c/repair.diff.txt`; each round 1
  row's resolution is in `resolutions-03c-r1.md` (both in the bundle). The maintainer's review of
  round 1 is `review/gate03c-review.md` (in the bundle).
- **The deliverable:** **`gate03c-r2-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10], 3rd ed., January 2010 (PDF; book page = PDF page −
12).

## Brief for the auditor

Round 2 does two things.
1. **It verifies the round 1 resolutions.** For each row of `resolutions-03c-r1.md` (the
   findings and the review's missed items `M1`, …) say whether the resolution is adequate:
   - **fixed**: the defect is gone, and the fix introduces no new one;
   - **recorded** or **scheduled**: accepted as declared, or deferred to a named PR or gate, and
     the record is accurate;
   - **not resolved**: say why.
2. **It audits the changed surface afresh** (section A of `evidence-r2/03c/repair.diff.txt`):
   - restate every new public declaration listed below in your own words, and say whether its
     statement is what its docstring claims;
   - check every changed statement and docstring;
   - look for regressions: anything round 1 accepted that the repair broke.

Pack 03a's brief and severity guide apply (03a's pack is in the bundle). Attempt at least
**three adversarial instantiations** against the changed surface. Do not give a blanket
approval.

## What changed

- **Statements:** **Thm 75.4** (`Ensemble.NextBitUnpredictable.pseudorandom`) no longer takes `hℓ : ∀ n, 0 < ℓ.eval n` (strengthened to the source's statement). `PRG` declares a second Deviation (expansion at every `n`, `n = 0` included).
- **New public declarations:**
- `prgAdv_eq_zero_of_length_eq_zero` (`NextBit.lean`: no advantage on `{0,1}^0`);
- the reading lemmas `PRG.easy_iff` (`Pseudorandom.lean`), `hardCore_iff`, `PRG.oneBit_stretch`,
  `PRG.oneBit_G`, `owpPredictorSnoc_eq`, `oneBitStep_eq`, `expandRed_eq` (`HardCore.lean`),
  `Collection.glBit_eq` (`HardCoreCollection.lean`);
- `HardCoreCollection.lean`: 17 declarations moved unchanged from `HardCore.lean` (names and
  statements as before; `HardCore.lean` imports it).


## Scope

| Item | Where |
|---|---|
| Round 1 findings, review, resolutions, repair diff | `findings/gate03c-findings.md`, `review/gate03c-review.md`, `resolutions-03c-r1.md`, `evidence-r2/03c/repair.diff.txt` |
| Under audit (the changed surface), at the pin | `TCSlib/Cryptography/Asymptotic/{Pseudorandom, NextBit, HardCore, HardCoreClaims, HardCoreCollection}.lean` |
| Context | `03c-pack.md` (round 1), `03a-pack.md` (common brief), `policy.md`, `briefs/pass-shelat/DESIGN.md`, the duplication ledger (scheduled rows) |
| Out of scope | tactic proofs; the scheduled clean-up (G3-5, DL-9 onward) beyond checking that its record is accurate |

## Attestations (maintainer execution claims; evidence under `evidence/c2/` in the bundle)

### Attestation results at `e79397eaf68b156b9db091f464741f6eb75b9c28` (evidence under `evidence/c2/`)

1. **Elaboration** (`replay.log`): the closure of this pack's files, 95 modules, each
   checked alone into a fresh olean tree by `scripts/lean_check_tree.sh`: all pass, 0 errors;
   18 `sorry` warnings in the closure.
2. **Axioms** (`axioms.log`): 76 prints of every public theorem and lemma in this pack's files:
   76 use only the standard axioms, and 0 depend on `sorryAx`; any other axiom is listed
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
