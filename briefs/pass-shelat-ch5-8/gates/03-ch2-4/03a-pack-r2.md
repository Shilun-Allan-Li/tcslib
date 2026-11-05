# Gate 03a ([PS10] ch. 2–4, probabilistic machines, closure, ensembles: the interface), round 2: external closing audit pack

**What is audited:** the repairs of round 1, on `cryptography/pass-shelat-ch2-4` at
`e28773ef3bda6f7b4b112ec1657427bfef01e374` (the branch after #201 and #203 merged; its Lean files are #203's head `f29be161`).
- **Round 1** audited `a3c5fa8b72e50939822f22364647dc844a3914a0` and found **0 blockers, 0 majors, 13 minors and 13 notes**; after the review, 2 majors (#4 and #8 raised: duplication rooted in private helpers) (`gate03a-findings.md`, in the bundle,
  verbatim).
- **The repair:** the 03a repair commit (G3-7 (a): `negligible_zero` moved; precise imports; minors and notes), merged in #201; gate 03 clean-up part 1, #203 (item H: `NUPPT.exists_compParam`, the fix for #3 that #201 missed; item D: `polyTimeComputable_stateFind` public; item G: `Repetition.lean`'s construction prose). The full delta is `evidence-r2/03a/repair.diff.txt`; each round 1
  row's resolution is in `resolutions-03a-r1.md` (both in the bundle). The maintainer's review of
  round 1 is `review/gate03a-review.md` (in the bundle).
- **The deliverable:** **`gate03a-r2-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10], 3rd ed., January 2010 (PDF; book page = PDF page −
12).

## Errata to the round 1 pack (review of round 1)

- **Context** (#22): `Asymptotic/EnsemblesLemmas.lean` is context for this pack; pack 03i audits it.
- **Q1** (#23): the stale question is answered by the inventory banners ("superseded by DESIGN
  D3–D6", `inventory-ch2.md`, `inventory-ch3.md`).

## Brief for the auditor

Round 2 does two things.
1. **It verifies the round 1 resolutions.** For each row of `resolutions-03a-r1.md` (the
   findings, grouped as the review grouped them, and the review's missed items `M1`, …) say
   whether the resolution is adequate:
   - **fixed**: the defect is gone, and the fix introduces no new one;
   - **recorded** or **scheduled**: accepted as declared, or deferred to a named PR (clean-up part 2,
     after #195), and the record is accurate;
   - **not resolved**: say why.
2. **It audits the changed surface afresh** (section A of `evidence-r2/03a/repair.diff.txt`):
   - restate every new public declaration listed below in your own words, and say whether its
     statement is what its docstring claims;
   - check every changed statement, rename and docstring;
   - look for regressions: anything round 1 accepted that the repair broke.

Pack 03a's brief and severity guide apply (03a's pack is in the bundle). Attempt at least
**three adversarial instantiations** against the changed surface. Do not give a blanket
approval.

## What changed

- **Statements:** No public statement of this pack changes (statement-text comparison against round 1). `negligible_zero` moved from `Ensembles.lean` to `Negligible.lean` (both in this pack), name and statement unchanged. `Repetition.lean`'s proofs were re-pointed to `Build/`'s new reading lemmas (#203); its 03l-related prose is re-audited in gate 03l round 2 as well.
- **New public declarations:**
- `NUPPT.exists_compParam` (`Closure.lean`): closure under polynomial-time pre- and
  post-processing that see `1^n`; `exists_comp` is re-derived as its special case;
- `polyTimeComputable_stateFind` (`Repetition.lean`): made public (statement unchanged).

## Scope

| Item | Where |
|---|---|
| Round 1 findings, review, resolutions, repair diff | `findings/gate03a-findings.md`, `review/gate03a-review.md`, `resolutions-03a-r1.md`, `evidence-r2/03a/repair.diff.txt` |
| Under audit (the changed surface), at the pin | `TCSlib/Complexity/Randomized/{PolyExpr, PPT, Primitives, Closure, Repetition, NonUniform}.lean`, `TCSlib/Cryptography/Asymptotic/{Adversary, Sampling, Ensembles, SamplingFinDist}.lean`, `TCSlib/Cryptography/Foundations/Negligible.lean` |
| Context | `03a-pack.md` (round 1), `03a-pack.md` (common brief), `policy.md`, `briefs/pass-shelat/DESIGN.md`, the duplication ledger (scheduled rows) |
| Out of scope | tactic proofs; clean-up part 2 (after #195) beyond checking that its record is accurate |

## Attestations (maintainer execution claims; evidence under `evidence/a2/` in the bundle)

### Attestation results at `e28773ef3bda6f7b4b112ec1657427bfef01e374` (evidence under `evidence/a2/`)

1. **Elaboration** (`replay.log`): the closure of this pack's files, 64 modules, each
   checked alone into a fresh olean tree by `scripts/lean_check_tree.sh`: all pass, 0 errors;
   18 `sorry` warnings in the closure.
2. **Axioms** (`axioms.log`): 164 prints of every public theorem and lemma in this pack's files:
   163 use only the standard axioms, and 1 depend on `sorryAx`; any other axiom is listed
   in the log.
3. **Admissions** (`admissions.txt`): 1 declarations in this pack's files contain `sorry`.
4. **Lint** (`lint.log`): `scripts/style_lint.py` on this pack's files: 0 findings in 11 files.

The one `sorryAx` print and the one admission are the same declaration,
`NUPPT.decides_of_decidesWithAdviceInTime` (`NonUniform.lean:160`): the optional admission recorded
in DESIGN D11 (round 1, note 20).

The replay is the 416-module replay at `af91d53a`, overlaid by the re-check at #201's head
(`evidence-repairs/03ac/replay.log`) and by #203's builds and re-check
(`evidence-repairs/03l-cleanup1/`); each line of `replay.log` is the newest check of its module,
and the Lean files at the pin equal #203's head.

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Plus one line per round 1 row (or row group): `<row>: fixed / recorded / scheduled / not resolved —
<reason>`.

Severity guide: **blocker** (a downstream phase would build on a wrong statement); **major**
(fixable but materially misleading, or debt that needs explicit acknowledgment); **minor** (an edge
case, naming or attribution); **note** (no change required). The gate closes at **0 blockers and 0
majors**.
