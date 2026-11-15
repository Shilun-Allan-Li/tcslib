# Gate 30 · Promotion of `prfAdv_eq_expect` to the PRF layer (DL-44 F-01)

Round 1. The auditor is Codex, under the standing ruling of 2026-11-11 (Codex for audits and reviews). A small
promotion/refactor PR: one new public lemma and one proof-only re-derivation.

- **PR:** draft [PR #314](https://github.com/Shilun-Allan-Li/tcslib/pull/314) at
  `5757bc0604527602d790a1a57e9703374ce02c7b` (branch `promote/pass-shelat-prfadv-expect`, tree
  `6e784db3a2644929e03e47727c075eaf1e5908d1`).
- **Target and base:** the PR targets `cryptography/pass-shelat-ch2-4` on base
  `8aefdab4cdb372d0787a9be83bc65f1567ceb8b4` (the merge base; the tip after the #311 merge).
  - From the base to the records tip `f52a24be7442013d00bef3608ce5336429dd4719` there are 10 commits. Their only
    non-record paths are #312's `Complexity/Randomized.lean` and `Complexity/Randomized/SeedMajority.lean` and
    `machine-library-design.md`. Re-checked for this pack from git objects: no path is shared with the PR; neither
    module is in the head closure of a changed file (164 files); the only tip modules downstream of both are root
    `TCSlib` and `audits/pass-shelat/Checks` (import aggregators). `git merge-tree --write-tree` of the tip with the
    head gives tree `288b72c6aae4d80812b1ec21365a7fb72d696e10` with no conflict.
  - `pr.diff.txt` is `git diff origin/cryptography/pass-shelat-ch2-4...5757bc06`, which equals `8aefdab4..5757bc06`
    byte for byte.
- **Commits:** 1, by the maintainer (author and committer Claude): `5757bc06` "Promote prfAdv_eq_expect to the PRF
  layer (DL-44 F-01, Seyoon 2026-11-15)". It was first cut as `384229b08d2f6d6500e92d3f40222551abd5ecbb` on
  `99a38e3a` and rebased once onto `8aefdab4` after #311 merged; `git range-diff` gives `=` (identical patch;
  `evidence/checks/rebase-range-diff.txt`).
- **Scope:** a **promotion audit**. Seyoon's ruling on prf-mac finding F-01 (2026-11-15, "promote it now"): publish the
  generic PRF-advantage identity beside `prfAdv`, and re-derive the encrypt-then-tag copy from it with a proof-only
  change that keeps its API. prf-mac then re-points its local `hadv` by a proof-only landing edit on its own landing
  branch; that edit is **not** part of this PR.

## What changed

Paths are under `TCSlib/Cryptography/`. 2 Lean files, both modified (40 insertions, 8 deletions).

| File | Lines | Change |
|---|---:|---|
| `Pseudorandom/Functions/Defs.lean` | 106 → 142 | one import; one `## Main results` bullet; `section Expect` (`open Games ProbComp`) after `prfAdv_nonneg` with the new theorem |
| `Encryption/PrivateKey/EncryptThenTag/Reduction.lean` | 395 → 391 | `ETTGame.prfAdv_eq_expect`: body replaced by the new lemma; one docstring sentence inserted |

The new theorem (namespace `TCSlib.Cryptography`, the namespace of `prfAdv`; `I O : Type` from the file's
`variable`; formula docstring, proof sketch, no attribute):

```lean
theorem prfAdv_eq_expect {K ρ : Type} [Fintype K] [Nonempty K] [Fintype I] [DecidableEq I]
    [Fintype O] [Nonempty O] [Fintype ρ] [Nonempty ρ] (F : K → I → O)
    (A : OracleAdversary ρ I O) :
    prfAdv F A =
      |expect (sample K)
          (fun k => expect (sample ρ) fun c => if (A c).eval (F k) = true then (1 : ℝ) else 0) -
        expect (sample (I → O))
          (fun R => expect (sample ρ) fun c => if (A c).eval R = true then (1 : ℝ) else 0)|
```

Its proof is the ETT proof verbatim (`rw [prfAdv_def, distAdv_def, Bridge.acceptProb_eq ×2, accept_eq ×2,
Bridge.acceptGame_eq ×2, prob_bind ×2]`, then `prob_bind`, `prob_pure`, `oracleDist_apply`, `randomFunction_apply`).
It generalizes `ETTGame.prfAdv_eq_expect` from `K = I = O = {0,1}^m` to any finite nonempty key, input, output and
coin types (in `Type`). `ETTGame.prfAdv_eq_expect` is now `:= TCSlib.Cryptography.prfAdv_eq_expect Fm A'`.

**Statements:** decls2 against `8aefdab4` gives 1 ADDED (the new theorem), 0 CHANGED, 0 REMOVED
(`evidence/statements/decls2-vs-8aefdab4.tsv`, `.err` empty). All 20 pre-existing declaration headers of the two files
are byte-identical (`evidence/statements/header-bytes-vs-8aefdab4.txt`; the one MISSING row is the new theorem).
`touched`: 1 ADDED, 1 CHANGED (`ETTGame.prfAdv_eq_expect`, body and docstring), 20 UNCHANGED. Re-checked for this pack
from git objects with `maintainer/tools/decls2.py`'s parser: 1 ADDED, 20 unchanged.

## Rulings and records in force

1. **F-01 (Seyoon, 2026-11-15): promote it now.** The prf-mac delivery's local `hadv` in `Bound.exists_forgeGame_le`
   re-proved the public `ETTGame.prfAdv_eq_expect` (from #306) line for line (`records/…/fills/prf-mac/final-r1/review.md`,
   F-01, major). The ruling: a small PR publishes `prfAdv_eq_expect` in the PRF layer beside `prfAdv`
   (`Pseudorandom/Functions/Defs.lean` is not prf-long-owned), re-derives the ETT copy proof-only, and then prf-mac
   re-points. Decision-log rows of 2026-11-15 (the prf-mac review row with the ruling, and the promotion row).
2. **DL-44 (duplication ledger, open).** F-01 is paid by this PR (and prf-mac's re-point). F-02, F-03 and **the private
   `prfAdv_prfReduction` in `Encryption/PrivateKey/OracleFromPRF.lean`** (the same identity specialised to the
   CPA reduction, DL-40) stay in the deferred cleanup. **Not a finding:** that private copy remaining. What you can
   raise: another copy of the identity, public or private, that this PR should re-point or that the ledger misses.
3. **The PRF layer is read-only for `prf-long`.** The running `prf-long` job (final delivered 2026-11-15, under review)
   lists `Pseudorandom/Functions/Defs.lean` as read-only and owns `Asymptotic/Defs.lean`, the facade
   `Pseudorandom/Functions.lean` and `FromPRF*` (`records/…/fills/prf-long/issued-r1/brief.md`). This PR touches none
   of the owned files; no new module was created, so the facade is not edited.
4. **Rule 10.** `PolyExpr.eval` is notation (Q1, 2026-11-07; seal A canonical, B also reported); a `CoeFun`/`Coe`
   instance whose body is a structure projection is notation (Seyoon, 2026-11-14; coe seals canonical, strict run and
   attributed). For this PR strict and coe agree in every row.
5. **Lint, #305 baseline.** `campaign_style_lint.py TCSlib/Cryptography --check8b` gives **92 FAIL / 101 WARN** at
   the parent and at the head, with identical FAIL and WARN lines; the full diff is the two INFO lines (line counts,
   and Defs' public count 7 → 8) (`evidence/lint/`).

## Questions for the audit

**1. Placement**
- Is `Pseudorandom/Functions/Defs.lean`, beside `prfAdv`/`prfAdv_def`/`prfAdv_nonneg`, the right home, and is the name
  `TCSlib.Cryptography.prfAdv_eq_expect` (no `PRF` namespace exists in this layer) appropriate? Is `section Expect`
  with `open Games ProbComp` scoped so that it changes nothing for the rest of the file?
- Is the statement as general as it should be (finite nonempty `K`, `I → O` and `ρ`; `K ρ : Type` where the file's
  `variable` has `Type*`, because the game layer's `sample` is in `Type`), and are the `Nonempty` hypotheses needed?
- Are the formula docstring, its source tag `[Gar26, Definition 3.9]` (the tag `prfAdv` itself carries) and the
  proof sketch accurate, and is the new Main-results bullet right?

**2. The new import (acyclic and justified)**
- `Defs.lean` now imports `TCSlib.Cryptography.Games.Bridges.Experiments` (for `Bridge.acceptProb_eq`,
  `Bridge.acceptGame_eq`, `accept_eq`, `expect`, `sample`, `prob_bind`, `prob_pure`). `evidence/checks/imports.txt`:
  the closure of `Experiments` (7 modules) does not contain `Defs`, so there is no cycle; the import adds
  `Games.Probability`, `Games.Advantage` and `Games.Bridges.Experiments` to the closures of `Defs` (6 → 9) and the
  facade `Pseudorandom.Functions`; 42 of the 95 modules downstream of `Defs` gain them; 0 to `EncryptThenTag/Reduction`
  (163) and to root `TCSlib`. `Defs` already depended on the game layer through `OracleAdversary` → `Games.OracleComp`.
  Is the import acyclic, justified, and free of layering or name-resolution effects on the 42 modules that gain it?
- Every rebuilt module with a same-source reference built a byte-identical olean (127 of 129; the two #311 modules
  have no reference; `landing/build-refcmp.txt`). Does that settle that no downstream elaboration changed?

**3. The ETT re-derivation (proof only, API unchanged)**
- Is `ETTGame.prfAdv_eq_expect`'s header byte-identical (`evidence/statements/docstring-header-ETT.txt`) and is the
  only other change one inserted docstring sentence (`evidence/statements/docstring-delta-ETT.txt`)? Do its uses in
  `EncryptThenTag.lean` (`ccaScheme_cca2`, lines 730 and 732) and in `exists_tagStep` build unchanged
  (`landing/root-checks.jsonl`)?
- The ETT docstring's first paragraph still reads "(PRFGame overlap: `prfAdv_prfReduction`, re-derived here in general
  form from the published readers)", now followed by "This is the published `TCSlib.Cryptography.prfAdv_eq_expect` at
  `K = I = O = {0,1}^m`.", and its sketch still lists the rewrite chain. The maintainer's open point: is the first
  paragraph now stale (a minor), or still accurate as a record of the PRFGame overlap?

**4. Other copies of the identity**
- Known and deferred: the private `prfAdv_prfReduction` (`OracleFromPRF.lean:286`, same rewrite chain specialised; DL-44,
  DL-40). Known and to be re-pointed after this merges: prf-mac's local `hadv` (on the unmerged landing branch
  `land/pass-shelat-prf-mac` at `bd45faec`, not on the tip).
- Checked by the maintainer for this pack, at the head (`git grep` for `prfAdv_def` and `Bridge.acceptProb_eq`): the
  other uses are `FromPRF/Hybrid.lean:162` and `GGM.lean:254` (hybrid chains rewriting `prfAdv_def, distAdv_def` into
  hybrid probabilities, not this identity), `Asymptotic/Defs.lean:435` (`prfAdv_toOracleAdversary`, a `rfl` reading),
  and `PublicKey/BitwiseCPA.lean:392`, `OracleSecurity/PaddedCPA.lean:264` (one acceptance probability as an
  expectation over a product sample, no `prfAdv`). Are there copies this list misses, and should any be re-pointed
  here rather than in the cleanup?

**5. Rule 10**
- Seals A and B, strict and coe, pass for both changed files (requests: `Defs` strict 72/72, coe 71/71; `Reduction`
  strict 2271/2272, coe 2270/2271; `evidence/rule10/seals-*.tsv`). The paired controls (rows `prfAdv` with reader
  `prfAdv_def`, `ProbComp.expect` with `expect_pure`, `uprob`, and `PolyExpr.eval` in B) are ALL_OK in both harnesses
  (8 probes and 11 sealed negatives each; `evidence/rule10/ctlcheck-*.log`); `prfAdv` is `Defs`' own definition, so it
  is not in `Defs`' request set. Does the new proof read only published readers (`prfAdv_def` is the defining file's
  reader of `prfAdv`)? No explicit-unfold scan was run for this PR; the new proof's `rw`/`simp only` lists name only
  the theorems quoted above.

## Known dispositions (not findings)

- **The interaction with #313** (Gate 29, `learning`). `Defs.lean` is in the learning unit's closure (through
  `FromPRF/HybridLemmas` and the PRF layer), so this PR adds the three game-layer modules to it. `git merge-tree
  --write-tree 8befc589 5757bc06` gives tree `647c2e96fbb887ce32cd094d08536f7d1a57a8e8` with no conflict. The combined
  tree has not been built; whichever PR merges second is rebuilt on the merged tip.
- **The interaction with prf-long and prf-mac.** prf-long's owned modules are downstream of `Defs`; its landing rebuilds
  on whatever tip it lands on. `MAC/FromPRF` (prf-mac's owned module, still admitted on the tip) is among the 42 modules
  that gain the import; prf-mac's landing is rebuilt with its re-point.
- **The base advance after the cut** (`evidence/checks/base-advance-8aefdab4-to-711a9f4a.txt`): #312 is in neither
  changed file's closure, `Defs` is not in #312's closure, and the only shared downstream modules are root `TCSlib`
  and `audits/pass-shelat/Checks`, so the branch was not rebased a second time.
- **The build ran on a tree at the `eff2dcd0` base**, so its 129-module queue is the 96 modules downstream of the two
  files united with the 63 of the #303–#309 and #311 base delta and its downstream. The 10 sorries are all
  pre-existing (MAC/FromPRF 1, SpecialEncryptionSecurity 3, #311's SpecialEncryptionMulti 1, GarblingSecurity 1, Yao
  3, Randomness/Learning 1).
- **The PR description differs from the records draft.** `records/…/promote-prfadv-2026-11-15/pr-body.md` (also in the
  evidence ZIP; its `PROVENANCE.txt` calls it "draft PR description (not opened; nothing pushed)") is the long draft.
  The opened PR's description (`pr-description.md`, fetched 2026-11-15) is a shorter rewrite; its displayed signature
  omits the binders and instance arguments and writes `if (A c).eval (F k) then 1 else 0`. The Lean file is
  authoritative. What you can raise: a claim in either description that is false.

## Also check

**Axioms:** `TCSlib.Cryptography.prfAdv_eq_expect`, `ETTGame.prfAdv_eq_expect`, `ETTGame.exists_tagStep` and
`Composability.ccaScheme_cca2` each print `[propext, Classical.choice, Quot.sound]`; the log also has the `#check` of
the elaborated statement (`landing/axioms-head.txt`).

**Sizes and widths:** `Defs.lean` 142 lines (max width 97), `Reduction.lean` 391 (max 99) (`source-head.json`,
`evidence/checks/widths.txt`).

**Build:** 129/129 rc 0, 0 errors in both diagnostic forms, through root `TCSlib`, `audits/garg-ch1-3/Checks` and
`audits/pass-shelat/Checks` (`landing/root-checks.jsonl`, whose last line is the runner's `done` record); the olean
tree was restored to the base snapshot (`evidence/restore/tree-check-post.txt`).

## Evidence

- **`verification.zip`** (38 entries): byte-identical originals; `SHA256SUMS` lists every other entry and
  `PROVENANCE.txt` gives each entry's source.
  - `promote-prfadv-evidence.zip` (`maintainer/promote-prfadv-2026-11-15/`, SHA-256 `3c9a9f32…`) and
    `evidence-SHA256SUMS`, its manifest: 732 entries, 66 directory entries and 666 files, exactly the 665 manifest
    paths plus `SHA256SUMS` (byte-identical to the manifest); every hash verifies. It covers the patch and diff, the
    rebase, imports, statements, the build with the olean comparison, axioms, seals and controls, lint, the restore,
    and the pre-rebase run (`pre-rebase-384229b0/`);
  - `records/`: `PROVENANCE.txt` and `pr-body.md` beside the ZIP (each equal to the ZIP entry), the decision log, the
    duplication ledger, the prf-mac review and the issued prf-long brief, at records
    `f52a24be7442013d00bef3608ce5336429dd4719`;
  - `evidence/`: byte copies of the ZIP entries this pack cites.
- **`landing/`:** byte copies of evidence-ZIP entries: `root-checks.jsonl` (= `build/results.jsonl`),
  `build-refcmp.txt` (= `build/refcmp.txt`), `axioms-head.txt` (= `axioms/AxiomsHead.log`).
- **`pr-description.md`:** the PR #314 description as fetched from the GitHub REST API on 2026-11-15 (`.body`, raw).
- **`pr.diff.txt`:** `git diff` from the base to the head (2 paths, 40 insertions, 8 deletions).
- **`source-head.json`:** the head hashes, line counts and over-width counts of the 2 changed files.
- **`sources.zip`:** the source closure at the head of both changed modules, 164 files.

## Findings delivery

Return `gate30-prfadv-promote-findings.md` as a Markdown file in this chat. If you have several evidence files, return
a ZIP. The user dispatches and merges.

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

**Severities**
- **blocker:** a false or unusable statement, a changed API of `ETTGame.prfAdv_eq_expect`, a cycle, or a scope
  violation (a prf-long-owned file touched).
- **major:** a changed frozen statement, a forbidden read not covered by the rulings, an undisclosed copy left behind
  that this PR claims to remove, or necessary evidence that cannot be verified.
- **minor:** documentation or API defects, including an inaccurate formula docstring or proof sketch.
- **note:** anything else.

Report the audited head and the counts by severity. The gate closes at zero blockers and zero majors.
