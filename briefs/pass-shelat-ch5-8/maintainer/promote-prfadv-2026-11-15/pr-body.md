## Promote `prfAdv_eq_expect` to the PRF layer (DL-44 F-01)

Seyoon's ruling of 2026-11-15 on prf-mac finding F-01 (duplication ledger DL-44): publish the generic PRF-advantage
identity beside `prfAdv`, and re-derive the encrypt-then-tag copy from it with a proof-only change. prf-mac then
re-points its local `hadv` in `MAC/FromPRF/Bound.lean` (on its landing branch `land/pass-shelat-prf-mac`, not on
ch2-4) by a proof-only landing edit, which is not part of this PR.

**Branch:** `promote/pass-shelat-prfadv-expect` at `5757bc06`, 1 commit on `cryptography/pass-shelat-ch2-4` at `8aefdab4`
(the tip after the #311 merge).

### Changes

**`TCSlib/Cryptography/Pseudorandom/Functions/Defs.lean`**
- New theorem `TCSlib.Cryptography.prfAdv_eq_expect`, placed after `prfAdv_nonneg` in a `section Expect` that opens
  `Games ProbComp`. It has a formula docstring and a proof sketch, and no attribute:
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
  It generalises `ETTGame.prfAdv_eq_expect` from `K = I = O = {0,1}^m` to any finite nonempty key, input, output and
  coin types. The proof is the ETT proof unchanged.
- New import `TCSlib.Cryptography.Games.Bridges.Experiments`. The proof needs `Bridge.acceptProb_eq`,
  `Bridge.acceptGame_eq`, `accept_eq`, `expect`, `sample`, `prob_bind` and `prob_pure`.
  - There is no cycle: the closure of `Games.Bridges.Experiments` (7 modules) does not contain `Defs`.
  - The import adds `Games.Probability`, `Games.Advantage` and `Games.Bridges.Experiments` to the closures of `Defs`
    and the `Pseudorandom/Functions` facade. 42 of the 95 modules downstream of `Defs` gain them. It adds nothing to
    root `TCSlib`.
  - No new module was needed, so the facade `Pseudorandom/Functions.lean` is **not** edited and nothing conflicts with
    prf-long.
- One new `## Main results` bullet.

**`TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Reduction.lean`**
- `ETTGame.prfAdv_eq_expect` is now `:= TCSlib.Cryptography.prfAdv_eq_expect Fm A'` (proof only).
- Its name and statement are unchanged. Its docstring is unchanged except for one inserted sentence: "This is the
  published `TCSlib.Cryptography.prfAdv_eq_expect` at `K = I = O = {0,1}^m`."
- Its two uses in `EncryptThenTag.lean` (`ccaScheme_cca2`) and the one in `exists_tagStep` build unchanged.

No other file changes. No prf-long-owned file is touched (`Asymptotic/Defs.lean`, the facade, `FromPRF*`).

### Checks
- **Statements.** decls2 against `8aefdab4` shows 1 ADDED (the new theorem), 0 CHANGED and 0 REMOVED. All 20
  pre-existing declaration headers of the two files are byte-identical.
- **Build.** I built with `scripts/lean_check_tree.sh`, one module at a time, with no `lake`, on a tree at the
  `eff2dcd0` base.
  - The queue was 129 modules: the 2 changed files and their downstream (96 modules with them), plus the
    #303–#309 and #311 base delta and its downstream (63), up to root `TCSlib`, `audits/garg-ch1-3/Checks` and
    `audits/pass-shelat/Checks`.
  - All 129 returned rc 0 with 0 errors.
  - The only sorries are the 10 pre-existing ones: MAC/FromPRF 1, SpecialEncryptionSecurity 3, the #311 statement
    `SpecialEncryptionMulti` 1, GarblingSecurity 1, Yao 3 and Randomness/Learning 1. Every warning was already there
    before, or is #311's own `sorry` warning.
  - Each of the 127 modules with a same-source reference build produced a byte-identical olean. The two #311 modules
    have no reference. So the new import changes no downstream olean.
- **Axioms.** `prfAdv_eq_expect`, `ETTGame.prfAdv_eq_expect`, `ETTGame.exists_tagStep` and
  `Composability.ccaScheme_cca2` each depend on `[propext, Classical.choice, Quot.sound]`.
- **Rule 10.** Seals A and B, strict and coe, pass for both changed files. The paired controls (`prfAdv`,
  `ProbComp.expect`, `uprob`, and `PolyExpr.eval` in B) come out ALL_OK in both harnesses.
- **Lint.** `campaign_style_lint.py TCSlib/Cryptography --check8b` gives 92 FAIL and 101 WARN at both the parent and
  the head, with identical FAIL and WARN lines. Max line width is 97 and 99.

Evidence: `dl-review/promote-prfadv/` (PROVENANCE.txt, SHA256SUMS), zipped as `dl-review/promote-prfadv-evidence.zip`.

### Base
The branch was cut from `99a38e3a` and rebased once, with an identical patch, onto `8aefdab4` after #311 merged;
#311's `SpecialEncryptionMulti` is downstream of `Defs` and is in the build above. The tip has since gained #312
(`711a9f4a`: `Complexity/Randomized/SeedMajority.lean` and the `Randomized` facade). #312 is outside both changed
files' closures and their downstream, except root `TCSlib` and `audits/pass-shelat/Checks`, which aggregate imports.
It causes no name clash and merges cleanly, so the branch was not rebased a second time.

### Follow-up
- prf-mac: re-point `hadv` in `Bound.exists_forgeGame_le` to `TCSlib.Cryptography.prfAdv_eq_expect` (proof-only
  landing edit, DL-44).
- Deferred (DL-40/DL-44): the private `prfAdv_prfReduction` in `OracleFromPRF.lean` is the same identity specialised.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

https://claude.ai/code/session_01PqpVTiuDcjSqhyfbqnsVxA
