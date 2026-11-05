# Gate 03e ([PS10] ch. 2–4, interaction, proof systems, ZK definitions, commitments, NP layer), round 2: external closing audit pack

**What is audited:** the repairs of round 1, on `cryptography/pass-shelat-ch2-4` at
`e79397eaf68b156b9db091f464741f6eb75b9c28` (the branch after #201 merged; its Lean files are #201's head `0c348ff9`).
- **Round 1** audited `a3c5fa8b72e50939822f22364647dc844a3914a0` and found **0 blockers, 2 majors (#1, #2), 4 minors and 11 notes**; no severity change in the review (`gate03e-findings.md`, in the bundle,
  verbatim).
- **The repair:** the 03e repair commit (G3-3: bounded honest messages; G3-4: the perfect forms' cost and `PerfectZKAbort.statZK`; minors and notes), merged in #199; the DESIGN records it missed (§5 items 8 and 11, §7 item 51) were committed after #201 merged. The full delta is `evidence-r2/03e/repair.diff.txt`; each round 1
  row's resolution is in `resolutions-03e-r1.md` (both in the bundle). The maintainer's review of
  round 1 is `review/gate03e-review.md` (in the bundle).
- **The deliverable:** **`gate03e-r2-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10], 3rd ed., January 2010 (PDF; book page = PDF page −
12).

## Errata to the round 1 pack (review of round 1)

- **Scope line** (M7): pack 03g is 3-colouring and 03k graph isomorphism (round 1's line 39 had
  them swapped).
- **Inventory** (#16): Thm-124.1 and Claim-124.d are owned by pack 03g (its inventory list); this
  pack audits `NP.lean`'s forms of them as well ("also 03g").
- **Q-1** stands as ruled (no cap on `V*`; finding 7).

## Brief for the auditor

Round 2 does two things.
1. **It verifies the round 1 resolutions.** For each row of `resolutions-03e-r1.md` (the
   findings and the review's missed items `M1`, …) say whether the resolution is adequate:
   - **fixed**: the defect is gone, and the fix introduces no new one;
   - **recorded** or **scheduled**: accepted as declared, or deferred to a named PR or gate, and
     the record is accurate;
   - **not resolved**: say why.
2. **It audits the changed surface afresh** (section A of `evidence-r2/03e/repair.diff.txt`):
   - restate every new public declaration listed below in your own words, and say whether its
     statement is what its docstring claims;
   - check every changed statement and docstring;
   - look for regressions: anything round 1 accepted that the repair broke.

Pack 03a's brief and severity guide apply (03a's pack is in the bundle). Attempt at least
**three adversarial instantiations** against the changed surface. Do not give a blanket
approval.

## What changed

- **Statements:** `InteractiveProof(Err)`'s completeness carries a message bound `B` (`ProverBounded`), and `EfficientProverProof(Err)` has the new field `boundedP`. `zk_proof_of_mem_NP` and `_of_owp` become corollaries of the witness-relation forms; the `_owp_` Levin-reduction forms tie the commitment and the protocol together (`∃ Com ℓ, Commitment Com ℓ ∧ …`).
- **New public declarations:**
- `Protocol.ProverBounded` (def), `ProverBounded.mono`, `ProverBounded.pullback`,
  `ProverBounded.exists_complete`, `npProtocol_proverBounded`;
- `InteractiveProof.exists_accept`, `InteractiveProofErr.exists_accept` (the old completeness, for
  consumers);
- `PerfectZKAbort.statZK` (error `2^{-|x|}`), `PerfectZKAbort.zk`, `perfectZK_zeroRounds`, and the
  retry construction `AbortRetry.attempt`, `retry`, `attempt_poly`, `retry_poly`,
  `statClose_retry`, `exists_retrySimulator`, `firstHit_map_getD_eq`, `uprob_not_ne_nil_le`;
- `exists_commitment_of_owp` (`Commitment.lean`);
- `zk_proof_of_witnessRelation`, `zk_proof_of_witnessRelation_of_owp`,
  `exists_commitment_zk_proof_of_owp_levinReduction` (`NP.lean`).
- Consumers re-proved by the repair (graph isomorphism, 3-colouring) are in packs 03k and 03g; they are context here (section B of the diff).

## Scope

| Item | Where |
|---|---|
| Round 1 findings, review, resolutions, repair diff | `findings/gate03e-findings.md`, `review/gate03e-review.md`, `resolutions-03e-r1.md`, `evidence-r2/03e/repair.diff.txt` |
| Under audit (the changed surface), at the pin | `TCSlib/Cryptography/ZeroKnowledge/{Interaction, InteractiveProofs, Defs, Commitment, NP}.lean` |
| Context | `03e-pack.md` (round 1), `03a-pack.md` (common brief), `policy.md`, `briefs/pass-shelat/DESIGN.md`, the duplication ledger (scheduled rows) |
| Out of scope | tactic proofs; the scheduled clean-up (G3-5, DL-9 onward) beyond checking that its record is accurate |

## Attestations (maintainer execution claims; evidence under `evidence/e2/` in the bundle)

### Attestation results at `e79397eaf68b156b9db091f464741f6eb75b9c28` (evidence under `evidence/e2/`)

1. **Elaboration** (`replay.log`): the closure of this pack's files, 126 modules, each
   checked alone into a fresh olean tree by `scripts/lean_check_tree.sh`: all pass, 0 errors;
   21 `sorry` warnings in the closure.
2. **Axioms** (`axioms.log`): 116 prints of every public theorem and lemma in this pack's files:
   109 use only the standard axioms, and 7 depend on `sorryAx`; any other axiom is listed
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
