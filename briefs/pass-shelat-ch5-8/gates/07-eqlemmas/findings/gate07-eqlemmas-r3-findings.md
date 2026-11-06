# Gate 07, round 3: equation-lemma PR #210 — external audit

**Verdict: PASS — 0 blockers, 0 majors, 0 minors.** R2-01, R2-02 and R2-03 are fixed; F02 is fixed. This closes the round-three scope specified by `pack-r3.md`. Round two's other conclusions and recorded deferred work stand.

## Pins and verification boundary

- Exchange checkout: `70718ea85420f324294d3448a55145f5c32af3da`, branch `exchange/pass-shelat-ch5-8`.
- Audited Lean head: `eb99dd7bb2d8a270b2ce17a3cf3e1487a65ad0ee`, branch `cryptography/pass-shelat-ch2-4-eqlemmas`.
- Its parent, round-two head: `3436321ba28042549bead976dc654aab3d661f10`; PR base: `05fe903fc736ac8036c161ad159dc8bdddcd6ee2`; round-one head: `fff0430c7c9db136e60ed14b069e972c2ea56fc8`.
- Records: `00e2aa4676f9cc74ca1ffac8a7f8f7b90447bafd` on `cryptography/pass-shelat-ch2-4`, under `briefs/pass-shelat-ch5-8/gates/07-eqlemmas/`.
- Bundle SHA-256 verified: `5eaec3f74e39c522482c4550645a5d78a35beba9f09c54e51e0a103a74c0d5b5`. All 26 sections match their pinned record files, allowing only terminal-newline differences introduced by bundling; their order matches `BUNDLE-FILES.txt`. I also retrieved the additional round-three evidence, including `decls-vs-r1.tsv`.

I checked the pinned Lean sources, actual repair diff, probe sources and logs, declaration tables, executable `sorry` counts and replay coverage. **No Lean compilation was performed in this audit:** this host has no Lean/lake toolchain. Compiler outcomes below are reviews of the archived logs, as permitted by the brief. Table regeneration, source comparisons, token counting, reverse-import analysis and Python lint checks were executed independently here; they are not a fresh elaboration certificate.

Evidence paths below are relative to the records directory; Lean paths are relative to the repository at the audited head.

## Findings

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| — | — | Round-three scope | No new findings. | Checks and dispositions below. | None. |

R2-01: **fixed** — the external consumer now exercises the padded permutation collection under the promised seal, with matching open/sealed controls and correct source-to-log attribution.

R2-02: **fixed** — all six docstrings state the correct formula; no declaration statement, definition body or proof changed.

R2-03: **fixed** — the corrected baseline and counts are explicit, and the regenerated declaration tables include both branches of `GGMRed.queryOf_eq`.

F02: **fixed** — `glPad_domEquiv`, the general `Equiv` lemmas and `glPad_perm` provide the usable foreign domain/permutation interface. The definition-specific identity statement `glPad_domEquiv_apply` is not needed by that consumer.

## R2-01: consumer and controls

The imported interface is at `TCSlib/Cryptography/Asymptotic/HardCoreCollection.lean:394–412`. The probes import this module from a separate file; they do not copy its definitions or prove the positive equations by unfolding them.

I compared the seal with `R201Collect.log`: it contains exactly 42 distinct constants, namely every logged plain definition and auxiliary matcher except the authorized `PolyExpr.eval`/matcher exclusions, plus `PermCollection.glPad_domEquiv`. Both `PermCollection.glPad` and `Collection.glPad` are included. The collector traverses the types and values of reached definitions and the types of reached theorems. I reviewed that algorithm and its recorded output; I did not rerun the Lean collector.

| Positive examples | What they establish under the seal |
|---|---|
| P1–P2 | The published equivalence exposes the product domain, and its inverse reconstructs the original padded-domain element. |
| P3 | The padded permutation is the original permutation times the identity, conjugated through the domain equivalence, by the published `glPad_perm`. |
| P4–P5 | Forward application, both for an abstract padded-domain element and for an element constructed through the inverse equivalence, follows by cancellation of the equivalence and its inverse. |
| P6 | Inverse application follows from the inverse of the same conjugated equivalence, preserving the padding component. |
| P7 | The padded collection's function is its encoding after its permutation, by the `PermCollection.f_perm` field. |

The explicit rewrites in P4–P6 have the correct composition directions. P1–P7 contain no `sorry`, `admit` or auxiliary axiom. Their sealed and open logs both report `rc=0` without diagnostics.

The sealed and open source files differ **only** by the seal line, for both the positive and control pairs. The five sealed-control errors occur at `17:46`, `20:89`, `25:68`, `31:2` and `35:67`, respectively: C1 projects `z.1`; C2 supplies a raw pair as a padded-domain element; C3 applies a product permutation directly to that abstract element; C4 tries to prove P3 by `rfl`; C5 states the identity equation across the hidden domain identification. There is exactly one error per control, at log lines 1, 5, 11, 19 and 27, matching `R2-01-MAPPING.md`. The open control reports `rc=0` without diagnostics.

The maintainer's interpretation of C5 is correct. In `glPad_domEquiv_apply`, the two sides are accepted as having one type because the defining file can identify the padded domain with the product. That statement is not a representation-independent consumer interface. P1–P6 instead keep the types distinct and transport through the published equivalence; they prove the required domain and permutation facts without that identity lemma. Thus C5's failure is expected and does not leave the requested consumer missing.

## R2-02: formula docstrings

I checked each new docstring against the adjacent definition and equation:

| Declaration | Check |
|---|---|
| `Experiments.lean:88`, `invProb_def` | Success means the adversary's output has the same image as the sampled input, with uniform input and coins. |
| `Experiments.lean:93`, `predProb_def` | The predicted bit equals `B x`, with the same input/coin distribution. |
| `Experiments.lean:98`, `acceptProb_def` | The test accepts the sampled output; the prose's bit `1` is the statement's `true`. |
| `Experiments.lean:102`, `distAdv_def` | Absolute difference of the two acceptance probabilities. |
| `Adversary.lean:183`, `invProbOpt_def` | There exists a returned `some x'` with the correct image; failure remains excluded. |
| `HardCoreLemmas.lean:983`, `glPadInvFun_eq` | On the stated nested input layout, the projections recover the parameter, trapdoor, image, padding and coins; the inverter receives the parameter, trapdoor/image pair, empty advice and those coins, and its result is paired with the unchanged padding. |

The last check uses `NUPPT.layout` and its projection equations in `Complexity/Randomized/Closure.lean:91–138`. The docstring describes structured inputs and does not assert different behavior for malformed strings.

## R2-03: corrected evidence

I independently counted executable `sorry` tokens after removing nested block comments, line comments and strings in all 70 changed Lean files. The archived table's per-file counts match exactly:

| Scope | PR base | Audited head |
|---|---:|---:|
| `Candidates/Factoring.lean` | 8 | 10 |
| `Candidates/RSA.lean` | 9 | 10 |
| All 70 changed files | 63 | 66 |

The three additions in the source diff are precisely S1 `polyTimeComputable_samplePrimeL`, S2 `statClose_samplePrimeL_pair`, and S3 `statClose_sampleUnitL`. At the corrected later comparison baseline `16a7d02d69cae1a700c131e3cc3dd918a7b3d6e1`, Factoring and RSA already have 10 each. The correction is carried by `resolutions-r2.md` and `pack-r3.md`; the historical `pack-r2.md` retains its superseded sentence. I have not treated that old sentence as a valid PR-base attestation.

Running the reviewed `decls2.py` against the pinned sources reproduces all three round-three tables byte for byte: 367 additions / 58 changes / 2 removals against the PR base; 184 / 55 / 2 against round one; an empty table against round two. Comparing the old and corrected extractor tables at the same head changes exactly one row, `GGMRed.queryOf_eq`: it now includes both `some ([false], x) => decodeFin ℓ₁ x` and `_ => none`, matching `GGMReduction.lean:97–100`. The extractor's match-arm exception fixes this reported truncation; this audit does not certify it as a general Lean parser.

## Repair and replay

The actual repair is one commit with exactly three changed files, 11 inserted lines and 6 deleted lines. Its diff matches `evidence-r3/repair-r3.diff.txt` exactly. Removing comments leaves identical code tokens in every changed file, independently confirming that the repair changes only the six docstrings.

The archived replay names the audited head and contains 105 distinct library modules plus `audits/pass-shelat/Checks`, all with `rc=0` and `errors=0`. Computing the reverse-import closure of the three repaired files independently reproduces those 105 library modules exactly. The warning counts in the corrected `sorry` table agree with the replay summary wherever that table reports a replay count.

A fresh run of `scripts/style_lint.py` reports **0 findings in 3 files**. Comparing the check-8b scanner's results on the three files before and after the repair gives no change, consistent with the archived empty `check8b-diff.log`. No further repair is required for this gate round.
