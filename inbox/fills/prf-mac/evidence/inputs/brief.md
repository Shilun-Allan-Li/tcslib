# Claude fill · the PRF MAC is secure (`prfMAC_secure`, Theorem 135.4)

**Issue base** `107f1e8c218733eac12d6b9bee6fece441271317` on `cryptography/pass-shelat-ch2-4` (the records tip after #303, #305, #306,
#308 and #309; records-only commits since `58a061c9`). **Unit** `prf-mac`. **Worker** Claude (standing ruling, 2026-11-11). **Lean** 4.25.0 and the
Mathlib revision in that commit's `lake-manifest.json`.

Prove the admitted theorem `prfMAC_secure` of [PS10, Theorem 135.4] in
`TCSlib/Cryptography/Authentication/MAC/FromPRF.lean`. The statement passed the prong A statement phase and Gate 06 (chapters 5–8 statements),
and is frozen. Its docstring holds the maintainer's proof sketch.

## Feasibility (maintainer's assessment)

Feasible as stated. The machine and PRF interfaces it needs are published (T2, T3, T4, `PRF`, lazy sampling). It depends on no admitted target: the closure's admissions are the machine-library stubs and `dlHash_crh`, none of which is on the route.

**Estimated size:** 1,500–2,500 lines in 3–6 helper modules. For calibration, hash-sign landed 2,247 lines and cca2-ett 5,364.

## Checkout and delivery

- Fetch `cryptography/pass-shelat-ch2-4`. Start a local branch `fill/prf-mac` at the exact issue base, and
  record the base in `REPORT.md`. Keep the proof branch local.
- Read `policy.md`, the attached environment addendum and `README.md`.
- Deliver every checkpoint and the final payload under `inbox/fills/prf-mac/` on `exchange/pass-shelat-ch5-8`:
  - `REPORT.md`;
  - `patches/`: the whole `git format-patch` series from the issue base;
  - `patches/COMMITS.tsv`: one row per commit, giving its hash, the author's name, email and date, and the
    committer's name, email and date, so that `git am` at the base reproduces every hash. Before you push,
    check the reproduction in a scratch clone and say so in `REPORT.md`. The last batch's worker hashes
    could not be reproduced, because no committer metadata was delivered;
  - `src/`: the changed and new files;
  - `evidence/`, with an `evidence/SHA256SUMS` manifest (see *Evidence completeness*);
  - a top-level `SHA256SUMS` listing every delivered file under `inbox/fills/prf-mac/` except itself. The
    delivered paths must equal the manifest's paths exactly, with nothing missing and nothing extra.
    Check this before each push.
- Commit as `fill prf-mac: checkpoint N` and `fill prf-mac: final`.
- Pull with rebase before pushing, push only your delivery path, and never force-push. Campaign changes land
  by a maintainer PR for Seyoon's approval.

## Base and parallel work

- **#307 (dl-crh) is not merged.** It changes `Candidates/DiscreteLog.lean`, the `Hashing.lean` facade and `Hashing/FromDiscreteLog*`. This unit edits none of them, but its closure contains `Candidates/DiscreteLog`, `Hashing/FromDiscreteLog` (through the `Authentication` facade), at their pre-#307 state, with `dlHash_crh` still admitted. If #307 merges during the fill, stay on the issue base; the maintainer rebases at landing.
- The other fills of this batch (`learning`, `derand`, `seq-zk`, `canonizer`, `sc-ot`, `sc-compose`) start from the same base.
  Each edits only its own owned file and helper directory.

## Target (frozen; quoted from the issue base)

```lean
theorem prfMAC_secure {F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool)}
    (hF : PRF F) (E : List Bool → List Bool) (hE : PolyTimeComputable E)
    (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) =
      List.ofFn (F n s x)) :
    (prfMAC F E hE hFE).Secure := by
  sorry
```

It lives in namespace `TCSlib.Cryptography.Authentication`. The theorem's arguments are `{F}` (a family `∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool)`),
`hF : PRF F`, the evaluator `E`, `hE : PolyTimeComputable E` and `hFE` (`E ⟨s, x⟩ = F n s x`).

**The scheme `prfMAC`** (Protocol 134.3, all in the owned file): `msgLen = tagLen = var`. `Gen`'s coins are the key
(`runAt_coinKey`); `Tag` has no coins (`.const 0`) and returns `E ⟨k, m⟩` (`prfTagFun_eq`); `Ver` returns
`[E ⟨k, m⟩ = σ]` (`prfVerFun_eq`). Read the scheme only through those lemmas and the `simps` fields of `prfMAC`
(`msgLen`, `tagLen`, `gen`, `tag`, `ver`).

**The security notion** (`Authentication/MAC/Defs.lean`): `MAC.Secure` (`secure_iff`) bounds `accept (forgeGame A
(q n) n)` by a negligible `ε n` for every forger `A` and budget `q`. `forgeGame_eq` samples the key and the forger's
coins, runs the forger against the logged tagging oracle (`tagImpl_eq`) through `forgerCodec` (`forgerCodec_*`),
and wins when `Accepts` (`accepts_iff`) holds and the output message was never queried.

## Published interfaces

| Interface | Provider |
|---|---|
| `prfTagFun_eq`, `prfVerFun_eq`, `polyTimeComputable_prfTagFun`, `polyTimeComputable_prfVerFun`, the `simps` fields of `prfMAC` | owned file |
| `MAC`, `accepts_iff`, `tagImpl_eq`, `forgerCodec_decodeMove`, `forgerCodec_encodeEntry`, `forgerCodec_timeout`, `forgeGame_eq`, `secure_iff` | `Authentication/MAC/Defs.lean` |
| `PRF` (`easy`, `pseudorandom`), `PRF.negligible_prfAdv`, `prfAdv_toOracleAdversary`; `prfAdv_def`; `acceptProb_random_eq_lazy`; `lazyDist_apply`; `oracleDist_apply` | `Pseudorandom/Functions/Asymptotic/Defs.lean`, `Pseudorandom/Functions/Defs.lean`, `…/LazySampling.lean`, `…/OracleAdversary.lean` |
| T2 `exists_interactiveHandlerMachine` and the `InteractiveHandler` readers; the input-free companion `exists_toCompOn_of_toComp`; T4 `exists_toOracleAdversary_of_bitCodec` | `Games/Efficiency.lean` |
| `fwdHandler`, `fwdHandler_impl` | `Games/Forwarding.lean` |
| `prob_mem_le`, `prob_bad_le`, `expect_sample_mem_le`, `prob_eq_until_bad` | `Games/Hopping.lean` |
| PRFGame: `fImpl`, `lazyImpl`, `expect_lazyImpl`, `abs_expect_fImpl_sub_le` (import, do not copy) | `Encryption/PrivateKey/OracleFromPRF/*.lean` |
| `runAt_coinKey`, `NUPPT.runAt_eq`, `NUPPT.runAtL_ofPolyTimeUniform`, `NUPPT.inArg_eq`, `padFin_ofFn`, `atParam_eq` | `Encryption/PrivateKey/FromPRG.lean`, `Asymptotic/*`, `Games/BitCodec.lean` |
| `Negligible.add`, `mono`, `negligible_two_pow_neg` | `Foundations/Negligible.lean` |
| `simulate` and `OracleComp` laws, `buildComp_*`, `CostBoundedBy`, `bitCodec_*`, `ProbComp.expect_*`, `advantage_eq`, `accept_eq` | `Games/*` |

## Proof route and checkpoints

1. **Checkpoint 1 · the distinguisher (sketch steps 2, 3 and 6).** Apply `exists_toCompOn_of_toComp` to the forger. Build the forwarding reduction with T2: forward each tagging query `m` to the outer oracle, keep the queried messages in the state, and in the finalization make one query at the output message and return `[answer = σ ∧ m fresh]` (`finCall = 1`, `outLen = 1`, budget `q + 1`). Make it an oracle adversary at `ℓ₁ = ℓ₂ = var` with T4. Prove that against `f_k` its acceptance probability is the forgery probability: the tag oracle is deterministic (`.const 0` coins) and equals `f_k` through `hFE`, and the key is `Gen`'s coins (`runAt_coinKey`). Send this checkpoint.
2. **Checkpoint 2 · the random function (sketch step 4).** Against a uniform random function, the reduction accepts with probability at most `2^{-n}`: a fresh point's value is uniform and independent of the forger's view. Use lazy sampling (`acceptProb_random_eq_lazy`, `lazyDist_apply`) with `prob_mem_le`, or a direct count. Send this checkpoint.
3. **Final · the bound (sketch step 5).** `accept (forgeGame A (q n) n) ≤ prfAdv (F n) (D^{q n + 1}) + 2^{-n}`, negligible by `PRF.negligible_prfAdv`, `Negligible.add` and `negligible_two_pow_neg`. Take `ε` to be that bound, which holds at every `n`, `n = 0` included.

Check the edge cases: `n = 0` (the empty message: an unqueried forger wins with probability 1, and `2^{-0} = 1` covers it); budget 0; repeated queries; a forger whose output message was queried (not fresh); malformed outputs and the codecs' timeout outputs (`forgerCodec_timeout` is `zeroBits`); the tag machine's empty coins; the extra final query in the budget (`q + 1`).

If the sketch is wrong, or a target is false as stated, stop and escalate with the exact obligation: a
checkpoint with the counterexample or the missing fact. Do not weaken any statement.

## Scope and proof discipline

- **Owned file.** You own `TCSlib/Cryptography/Authentication/MAC/FromPRF.lean` (147 lines at the issue base):
  - replace the target's proof body and edit its sketch to describe the delivered proof;
  - update the module title (drop "(statement phase)" where present) and the `## Main results` status.
- **Helper modules.**
  - They are permitted under `TCSlib/Cryptography/Authentication/MAC/FromPRF/`. The owned file imports them precisely and gets a
    `## Contents` list.
  - **Facades.** After the facade-lint fix (#305), a new helper under `X/` is covered as long as `X.lean`
    imports it, so no parent facade needs an edit.
  - A helper may import `Encryption/PrivateKey/OracleFromPRF` and its helpers (the PRFGame API). They are not downstream of the owned file, so this creates no cycle (checked at the issue base); the order below includes their upstream closure.
- **Size and width.** Every line has at most 100 characters (Python `len`), and every file at most 1000 lines.
  Check both with a short `python3 -I` script before each push and include its output in `evidence/`.
- **Frozen files.** Do not edit any other file.
  - `Games/Efficiency.lean` is at 982 lines. Do not add to it.
  - **Scope requests.** If the route needs a change to a frozen file (a reader beside a foreign definition, an
    import, a promotion), stop that line of work. Ask Seyoon in your session, giving the exact file, the diff
    and the reason, and go ahead only on his approval. Record the request and his answer verbatim under
    `evidence/scope-request/` and in `REPORT.md` § *Scope requests*. The Codex fills obtained their facade
    imports, and dl-crh its two `DiscreteLog` readers, this way. Seyoon prefers a route with no frozen-file edit
    where one exists.
  - A lemma that belongs in an existing file goes in your helper module, with a promotion request.
- **Parallel fills.** The seven fills `prf-mac`, `learning`, `derand`, `seq-zk`, `canonizer`, `sc-ot` and
  `sc-compose` are issued from the same base. Edit only your owned file and helper directory.
- **Duplication (binding).**
  - **Search first.** Before writing any lemma, search `TCSlib/` and Mathlib for its statement shape and key
    names. Reuse published lemmas by importing them.
  - **Private lemmas.** Never copy a private lemma silently. If you need one, re-derive it from published
    readers, keep its statement general, and disclose it.
  - **Disclose every overlap.** `REPORT.md` has a section **`## Overlap and reuse`**. For every new declaration
    that restates, specializes or re-proves existing material (public or private, TCSlib or Mathlib), give its
    nearest relative (`path:line`), the relation, and why it is not reused. List the searches you ran.
  - **Why.** Undisclosed duplication is a freeze violation, not debt. The majors that held Gates 23 and 24
    were undisclosed duplicates: G23-01, a private copy of `length_le_length_encodeLog`; G24-01,
    `inputWord_take`, which re-proves the public `take_ofFn_castLE`.
  - **Nearest relatives here:** the random-function tag-forgery bound of cca2-ett (`Encryption/PrivateKey/EncryptThenTag/Forgery.lean`: `expect_prob_bad_le`, `abs_ettAcc_rej_sub_le`), the lazy random function of `OracleFromPRF/Collision.lean` and `EncryptThenTag/Lazy.lean`, hash-sign's forwarding game (`Signatures/HashAndSign/ForwardGame.lean`, `forward_fresh`) and Lamport's freshness readers (`Signatures/Lamport/Planted.lean`, `fresh_firstLog_iff`).
- **Statements.** Preserve the target statement, every other declaration, the statement prose and the global
  simp attributes.
- **Docstrings and sketches.** The last batch's landing edits were mostly LE-doc (cca2-ett: 94 formulas and
  15 sketches; dl-crh: 59 formulas; lamport: 188 formulas and 7 sketches) and LE-width. Do these yourself:
  - every new public declaration has a docstring that states its formula: the equation or inequality, with its
    arguments in the Lean order, and a `[PS10, …]` tag where it comes from the source;
  - every proof of 15 lines or more carries a `**Proof sketch.**` paragraph, and long proofs get step comments
    (policy §3);
  - a new public `def` lands with its `_eq`, `_iff` or `simps` readers (lint check 8), and a new public
    `abbrev` with an `_eq` or `_iff` lemma;
  - add no `@[simp]`.
- **Rule 10.**
  - Use only published readers for other files' definitions, including generated matchers and projections.
  - Your helper modules count as foreign to each other and to the owned file. The owned file's definitions
    are foreign to your helpers.
  - **Notation, never sealed:**
    - `PolyExpr.eval` (Q1);
    - reducible abbreviations (2026-10-26; for example `QueryImpl`, `OracleSpec.add`, `glNeed`);
    - **projection coercions:** a `CoeFun`/`Coe` instance whose body is a structure projection, such as
      `FinDist`'s `⟨FinDist.prob⟩` (Seyoon's ruling, 2026-11-14).

    The coe-variant seals are canonical. Run the strict variant as well, and attribute each difference.

## Checks and report

- **Bootstrap.**
  - Bootstrap from `order.txt` (208 modules) and the narrow `roots.txt` (83), following the addendum.
  - Check one module per `scripts/lean_check_tree.sh` call, with one Lean process per olean tree.
  - Never run `lake build` or an unfiltered cache get. Run Python as `python3 -I`.
  - Insert helper modules before their consumers.
- **Sweep.**
  - Recheck the owned module, then sweep the supplied order with 0 errors.
  - Compare the `sorry` warnings with `base-sorries.txt` (20 declarations in 10 modules). The only change
    must be the removal of `prfMAC_secure`.
- **Axioms.**
  - Print the axioms of `prfMAC_secure`. Expect only `propext`, `Classical.choice` and `Quot.sound`.
  - Print them for every stored constant of the changed and new files.
- **Rule 10 evidence.**
  - Run whole-file seals A and B of every changed or new file over its full TCSlib import closure, at base and
    final.
  - Run both the **strict** and the **coe** variant (projection coercions sealed, or treated as notation).
    Report every failing declaration in each.
  - Add paired controls that pass unsealed and fail sealed, each sealed negative failing exactly once.
  - Run the explicit-unfold scan.
  - Report the seals with `PolyExpr.eval` both excluded as notation and sealed.
  - **Error counts (G26-N1).** Your runner must count both diagnostic forms, `error:` and `error(…)`, for
    example with `^\S+\.lean:\d+:\d+: error[:(]`. Keep every raw log.
- **Lint.**
  - Run `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography --check8b` at base and at final.
  - The baseline at the issue base is **92 FAIL / 101 WARN** (after #305).
  - Diff the line sets, not only the counts. There must be no new FAIL line, and no new WARN line except one you
    disclose and justify.
- **Report.** `REPORT.md` gives:
  - the base and the status of each target;
  - the changed files and the sketch edits;
  - the new declarations;
  - **Overlap and reuse**;
  - **Scope requests** (none, or each with Seyoon's answer);
  - the promotion and reader requests;
  - the evidence, with its manifest.

### Evidence completeness

Gate 20 held a delivery for omitted raw evidence (G20-01).
- Every file that `evidence/SHA256SUMS` names must be delivered. That includes:
  - seal and control sources, manifests and request records;
  - every raw log and `results.jsonl`;
  - the probe sources and the tools used.
- If the evidence is too large for one commit, deliver it in several commits, or as numbered ZIP parts, each part
  with an entry list. Do not leave anything out for size.
- Check before delivery that the delivered paths are exactly the manifest's.

The maintainer checks `TCSlib` and `audits/pass-shelat/Checks` on the full-library tree at landing.

**Ready to dispatch**
