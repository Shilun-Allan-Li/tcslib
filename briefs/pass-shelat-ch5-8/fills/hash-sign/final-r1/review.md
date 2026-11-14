# hash-sign · maintainer delivery review (r1)

**Verdict: ACCEPT WITH LANDING EDITS.** The landing edits LE-width and LE-facade are done. LE-doc (109 formulas and
one sketch, docstrings only) is in progress.

## Delivery and landing branch

**Delivery**
- **Source:** Codex worker, exchange `90e4b3c833e5e7fed134941e016724531ad64f1f` (`inbox/fills/hash-sign/`): 4 patches on
  the issue base `eff2dcd0`.
- **Target:** `Authentication.hashAndSign_oneTimeSecure`, [PS10, Theorem 144.1]: hash-and-sign of a one-time scheme
  with a CRH family is one-time secure. The brief is `../issued-r1/brief.md`, SHA-256 `d4ddbdb3…`.
- **Files:**
  - the owned file `Authentication/Signatures/HashAndSign.lean`;
  - 8 new helpers in `HashAndSign/`: `CodecReaders`, `CollisionGame`, `CollisionHandler`, `FixedGame`,
    `ForwardGame`, `ForwardHandler`, `OneQuery` and `OneQuerySampling`;
  - the facade `Authentication.lean`.
- **Approved exception** (Seyoon, 2026-11-14): exactly eight helper imports in `Authentication.lean`. Against the
  base, the facade diff is exactly those 8 lines.

**Landing branch:** `land/pass-shelat-hash-sign`.
- **Base:** the worker commits are rebased onto records tip `dee0de32ee33d7188afe97bdc3089fac68412057`, which is after
  #303 and #305. Neither rebase had a conflict, and the Lean content did not change.
- **Worker commits:** `e6bcdd62`, `f92c2f72`, `dcf726fe` and `b7e4249b`. Their author (Codex) is kept.
- **Landing edits:**
  - **LE-width** `189f1c21`: re-wraps the one 101-character statement line of `expect_hashAndSign_sign`. Whitespace
    only.
  - **LE-facade** `6056f3ed7774d308846f7293e2c6ed992ce9d4f8` (tree `683ac79ce6e8f7c8a00321293a81c344a1fa05b1`):
    swaps `OneQuerySampling` and `OneQuery`, so the helpers follow `Signatures.HashAndSign` in alphabetical order, as
    in `Randomness.lean` and `PrivateKey.lean`. Order only.
- **The worker's commit hashes:** they cannot be reproduced, because no committer metadata was delivered. The REPORT's
  tree `20aa8ef6` does reproduce.

**Evidence:** `review-evidence.zip`.
- SHA-256 `e20cf9f08838b9b0a6464f8398fb9fa44a942e3ea43f37a8df4b8e86cc6b0cbf`.
- It has 420 entries under `hash-sign-r1/`: the 419 manifest paths plus `SHA256SUMS`. The manifest is
  `evidence-SHA256SUMS`.
- Extracts are in `landing/`.

## Checks

**Integrity**
- `PAYLOAD-SHA256SUMS` verifies 1226/1226 and `evidence/SHA256SUMS` 1210/1210, with exact path sets.
- The issue package verifies 7/7 and `SOURCE-SHA256SUMS` 150/150.
- `git am` at the base gives tree `20aa8ef6`. The 10 files are byte-identical to `src/`, and `src/` holds nothing else.

**Build** on `$SP/dl-oleans` (verified first as the base snapshot)
- 15 modules, all with rc 0 and 0 errors: the 8 helpers, `HashAndSign`, `Authentication`, the #303 base-delta modules
  and root `TCSlib`.
- After the edits, `HashAndSign`, `Authentication` and `TCSlib` were rebuilt, also with rc 0.
- Whole-tree check at the head: 1209 modules plus PFR.
- No `audits/*/Checks` module imports the unit.
- The tree was restored to the base snapshot (`landing/tree-check-post.txt`).

**Statements**
- decls2 against `eff2dcd0`: 110 ADDED, 0 CHANGED, 0 REMOVED.
- All 32 pre-existing declaration headers are byte-identical, the target's included. Only the target's body and
  sketch changed.

**Axioms**
- The target prints `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.
- `lamport_oneTimeSecure` is still admitted at this base, and the target does not depend on it.
- Of the 176 stored constants, only the pre-existing `exists_oneTimeSecure_of_crh_owf` carries `sorryAx`, through
  Lamport, as at the base.
- There are no new `@[simp]` lemmas and no new instances.

**Rule 10**
- Seals A and B, in both the strict and the coe variant, pass for all 10 files at the head, and for the owned file and
  the facade at the base. The two variants agree.
- Paired controls: 20 probes and 57 sealed negatives, ALL_OK.
- The explicit-unfold scan finds 0 foreign definitions.

**Admissions:** 22 → 21. Only the target was removed.

**Lint**
- New lint (#305): 92/102 at the records tip and at the head, with identical lines.
- Old lint: 216/102 at the base and at the head, with identical lines.
- Every file is under 1000 lines and every line is at most 100 characters, except one pre-existing facade line.

**Content.** The proof follows [PS10, Theorem 144.1].
1. **Common transcript.** The forge game equals a common transcript.
2. **Two cases.** A success is either a collision or a forward success.
   - The collision case is handled by adversary B, built with T1, using freshness and `hdom`.
   - The forward case is handled by adversary C, built with T2, as an exact equality.
3. **Conclusion.** A union bound, then `Negligible.add`.
4. **Edge cases:**
   - with no query, the run takes the forward branch;
   - `m′ = m` is excluded by freshness;
   - the `hlen` casts go through `Fin.cast`;
   - timeouts are handled by `forgerCodec_eq_bitCodec`.

## Findings

| # | Severity | Finding | Disposition |
|---|---|---|---|
| M1 | minor | 109 new public declarations have no formula in their docstrings. `polyTimeComputable_collisionRun` (16 lines) has no proof sketch. | **LE-doc**, docstrings only (ext-nosrc, cca2-ett and dl-crh precedent). In progress. |
| M2 | minor | 7 new declarations are not used anywhere: `sampledHashSign` with its `_eq` and `_apply` readers, `expect_sampledHashSign_eq_transcript`, `collisionAdv_seedIn`, `forward_fresh` and `hashWord_eq_hash`. | **Accepted** as published API: a definition with its readers, plus three statement-level facts. Removing them would be a code change and gains nothing. Disclosed to the gate. |
| M3a | minor | `HashSignForward.roundWord`/`handler` repeats the `Games/Forwarding` pattern (`fwdRun`/`fwdHandler`), but hashes each query and uses different inner and outer widths, which `fwdHandler` cannot express. Disclosed by the worker. | Ledger **DL-42**: generalize `fwdHandler` with a query map. |
| M3b | minor | `splitBits_pad_concat` is a corollary of `Games.padFin_append_split`. `expect_simulate_sample_once` is close to `Games.expect_simulate_eager` but does not restate it. | Ledger **DL-42**: promote, as the worker requests. |
| M3c | minor | Overlap with the parallel `lamport` delivery: its `lamport_codec_ext` ≈ `MachineCodec.ext_of_fields`, `lamport_forgerCodec` is an instance of `forgerCodec_eq_bitCodec`, and its `exists_pure_of_cost_zero` ≈ `eq_pure_of_cost_zero`. | Ledger **DL-42**: fold after both land. The lamport review records the same overlap from its side. |
| O1 | obs | `MachineCodec.ext_of_fields` destructures a foreign structure with `cases`. This reads no foreign definition. | Accepted. Promote to `Games/Machines` with no attribute. |

## LE-doc · `4f0280c8` (built)

- **Head:** `4f0280c85fae8730ca0dfad980b41749452980fa`, tree `4485fafd1abee34129c24c8aa76f4325230eb442`.
- **Change:** 109 formula docstrings and 1 proof sketch (`polyTimeComputable_collisionRun`). Docstrings only:
  - every hunk lies inside a doc comment, and with doc comments blanked the files are byte-identical;
  - all headers are byte-identical, and decls2 against the previous head is empty;
  - every new public declaration now passes the docaudit, except the target, whose first line is prose.
- **Rebase:** No rebase was needed: origin had only records commits after `dee0de32`.
- **Build** on `$SP/dl-oleans`: 15 modules (the 8 helpers, `HashAndSign`, `Authentication`, base-delta, root `TCSlib`) rc 0; full head check 1209 modules OK. The tree was restored to the base snapshot afterwards.
- **Lint (#305):** 92 FAIL / 102 WARN, with the same lines at the head as at the records tip.
- **Evidence:** `ledoc-evidence.zip`, SHA-256 `ab6c3d6492425d73d0b1caf35fa1d2ec0960696796daaa9e5cf9af2aa16dd7c9`, 110 entries. Its manifest is `ledoc-evidence-SHA256SUMS`, and extracts
  are in `landing-ledoc/`.
- **PR:** draft [PR #308](https://github.com/Shilun-Allan-Li/tcslib/pull/308).
