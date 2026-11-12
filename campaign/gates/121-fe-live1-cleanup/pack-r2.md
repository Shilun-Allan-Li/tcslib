# Gate 121 round 2 · fixed-stop first-entry reuse after the repairs (PR #241)

**Not yet clear to merge** · PR #241 is a draft. Seyoon dispatches and merges.
The current Lean commit is `0f6f07eba0c2d91dbb082287f6479cb0962dc377`, against campaign Lean `4fff1ea826606070b86d0057052c20f3504b19e6`
(the campaign after #251). Round 1 audited `d64dff4fbef865d815c6a561ce8037ea1bae07a2`
and held it on one major and one minor (`findings.md`, verbatim).

## What changed since round 1

The round 1 scope is unchanged: nine first-entry consumers in `EXP`,
`ExhaustiveReplay`, `Hardness` and `InputCall` cite the published
`MultiTapeTM.exists_first_entry_of_fixed`. Since round 1 the branch adds only
proof-only repairs for finding 1 and merges of the campaign:

- `5abe015a`: `clA5Compare_compute` reads its configurations through
  existing published equations.
- `46edaeef`: nine stationary helpers (the idle proofs and EXP's
  `enumCont_absorb`) read the step through `MultiTapeTM.step_of_some`.
- `9936345a`: the approved `CfgFacts` import in Hardness (Seyoon,
  2026-11-08) and the `Cfg.mapState_eq_of_fields` reads it enables.
- `e2ccda50`: `exists_inputLengthTM` reads its machine through the owner
  equations #251 published (gate 129).
- `0f6f07eb`: `clFresh_idle` and `clPrepared_idle` read the right-hand seam
  state through `seamCompTM_tr_inr` (gate 131, approved 2026-11-08).

No statement, definition, public declaration or import changes beyond the
approved `CfgFacts` import. `patch/round1-to-head.patch` in the carrier is the
exact difference from the audited round 1 source.

## Brief for the auditor

1. Check each row of `resolutions-r2.md` against the current sources,
   in particular that none of the seven declarations named in finding 1
   still reads `MultiTapeTM.step`, `seamCompTM`, `Action.mapState`,
   `Cfg.mapState` or `Cfg.inputSymbol` by unfolding or simplification.
2. Check the whole-proof seals: every changed proof (24) elaborates in its
   owner file with each ordinary foreign definition it reaches made
   irreducible (25 definitions), and each control closes natively and
   fails sealed.
3. Check the copy screen and the dispositions of all 43 new pairs
   (`PAIR-DISPOSITIONS.json`): 3 first-entry adaptations of round 1's kind
   N1–N3, 38 zero-action configuration identities of round 1's kind N4–N8,
   and 2 fixed-run inductions present at the campaign. Report any exact
   reusable proof the repairs should have cited instead.
4. Check that the 78 remaining raw `MultiTapeTM.step` tokens in Hardness and
   EXP lie only in declarations this PR does not change, as the resolutions'
   bounded-scope paragraph states.
5. Check minor 2: the four original integrity files are sections of this
   bundle and match the records.

## Evidence

- `r2-evidence/SOURCE.json`: the 24 changed or added declarations per owner,
  against the campaign.
- `r2-evidence/REPLAY.json`: the merged-tree replay of the 164-module
  downstream closure of the five changed files, on the complete campaign
  snapshot after #251 (876 objects; prospective tree `f6fcc197e7a1b664a2d5849294881ac0296967f7`).
  164 passed, 0 failed. The 55 inherited admissions are in eight downstream
  modules whose sources are byte-identical to the campaign's; the five owners
  have none.
- `r2-evidence/CHECKED-SUMMARY-r2.json`: 24 whole-proof seals over five
  owners, 25 sealed definitions and 50 paired controls, all passing;
  standard axioms only; no new lint finding (one existing missing-sketch
  warning for `enumCont_first_anchor` is gone). The argument sweep's single
  candidate is a false positive (a local `have init`).
- The copy screen on round 1's 33-file population: BASE `declarations screened: 2429; copy pairs (target reproduces >= half of source): 2043; reproduced text: 454,870 chars`;
  HEAD `declarations screened: 2429; copy pairs (target reproduces >= half of source): 2037; reproduced text: 453,099 chars`. `screen/pairdiff.txt` lists 43 new and 49 gone pairs.
- `r2-evidence/DATA-CARRIER-r2.json` and its recovery map hold 582 logical
  files: every replay receipt and log, the seal and control sources and logs,
  the metadata, lint and screen outputs, the campaign versions of the owners,
  both patches and the drivers. Decode each gzip+base64 blob and check its
  SHA-256 and byte count.
- This round's checks ran on the cloud machine with the campaign's approved
  wrappers. The 20 PFR-dependent NewmanTheorem modules are not built there;
  none is in or imported by the closure.

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named
`gate121-fe-live1-cleanup-r2-findings.md`** (the findings table and the verdict
line, no other wrapping), and also paste its content in your reply.
