# Gate 03f1 ([PS10] ch. 2–4, discrete log, its hard-core bit, ElGamal), round 2: delta audit pack

**What is audited:** the repair of round 1, on `cryptography/pass-shelat-ch2-4` at `1ea782b11617e15a51c3e2f6bd15dd0e3befbd95` (the merge of
[Shilun-Allan-Li/tcslib#206](https://github.com/Shilun-Allan-Li/tcslib/pull/206), the gate 03 repair batch, and the records commits of 2026-11-06).
- **The round 1 findings** are `findings/gate03f1-findings.md` (in the bundle, verbatim), the maintainer's review `review/gate03f1-review.md`, and the resolutions `resolutions-03f1-r1.md`.
- **The repair:** #206's diff (`evidence-repairs/03-batch/repair.diff.txt`; it covers five gates, and only this pack's files are under audit) and the records changes named in the resolutions.
- **The deliverable:** **`gate03f1-r2-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header. **The source is attached separately:** [PS10] (PDF; book page = PDF page − 12).

## Brief for the auditor

1. **Verify each resolution** of `resolutions-03f1-r1.md`: fixed, recorded, scheduled, or not resolved (and why).
2. **Audit the changed surface afresh:**
   - **the rewritten sketch of `fullDLCollection_hardCore`** (the major): recompute its coin budget, the statistical term `(1 + 16n^{2c+2})·2⁻ⁿ`, `T ≤ 16n^c` and the success bound, and say whether a worker following it can prove the statement as stated (`hbig` kept, ruling R-03f1-1 (A));
   - the new lemmas `sampleBelowL_eq_rejectBlocksL` and `rejectBlocksL_eq` (each an equation and nothing more);
   - the docstring changes (#3, M1, M3).
3. **Check that nothing else changed** in this pack's files: the statement diff (`statements.txt`) lists every added and changed declaration of the batch.

Pack 03a's severity guide applies. Attempt at least one adversarial instantiation against the changed surface. Do not give a blanket approval.

## Scope

| Item | Where |
|---|---|
| Findings, resolutions, the diff | as above |
| Under audit, at the pin | `Candidates/{DiscreteLog, DiscreteLogHardcore, ElGamal, Concrete}.lean`; records: `briefs/pass-shelat/inventory-ch2.md` (Claim-62.2) |
| Context | `03f1-pack.md` and earlier round packs, `03a-pack.md`, `policy.md` |

## Attestations (maintainer execution claims; `evidence-repairs/03-batch/`)

- **Elaboration** (`replay.log`): the 128 modules downstream of #206's 21 changed files, then `audits/pass-shelat/Checks`, each checked alone after a base sync (`base-sync.log`): **129 of 129 pass, 0 errors**; every module's `sorry` count equals the base. A maintainer re-check of 8 key modules also passes (`maintainer-recheck.log`).
- **Axioms** (`axioms.log`): 549 prints over the 21 files, compared with the base: no axiom set changed; the 10 new lemmas are standard.
- **Seal** (`seal.log`): the consumers of `ProverBounded` pass sealed (their base versions fail); the new proofs pass with the definitions they could unfold sealed.
- **Lint** (`lint.log`): `scripts/style_lint.py` and `scripts/campaign_style_lint.py --check8b`, compared with the base: no new finding.
- **Statements** (`statements.txt`): 10 added, 2 changed (the two ruled ones in `NP.lean`), 0 removed.

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Plus one line per resolution row: `<row>: fixed / recorded / scheduled / not resolved — <reason>`. The gate closes at **0 blockers and 0 majors**.
