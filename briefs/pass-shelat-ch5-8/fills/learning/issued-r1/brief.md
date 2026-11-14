# Claude fill · no efficient learner predicts the PRF concept class (`predictAdv_prfConcept_negligible`, Theorem 179.1 (b))

**Issue base** `107f1e8c218733eac12d6b9bee6fece441271317` on `cryptography/pass-shelat-ch2-4` (the records tip after #303, #305, #306,
#308 and #309; records-only commits since `58a061c9`). **Unit** `learning`. **Worker** Claude (standing ruling, 2026-11-11). **Lean** 4.25.0 and the
Mathlib revision in that commit's `lake-manifest.json`.

Prove the admitted theorem `predictAdv_prfConcept_negligible` of [PS10, §8.1, Theorem 179.1] in
`TCSlib/Cryptography/Randomness/Learning.lean`. The statement passed the prong D statement phase (ruling D-5: the learning game is the PAC layer of `TCSlib/LearningTheory`) and Gate 06,
and is frozen. Its docstring holds the maintainer's proof sketch.

## Feasibility (maintainer's assessment)

Feasible as stated. The PRF, machine and probability interfaces exist, and the PAC game reads through published lemmas. The main work is the law bridge between the oracle run and `trialDist`. No dependency on an admitted target: `bpp_subset_dtime_subexp` is in the closure only through the `Randomness` facade.

**Estimated size:** 1,200–2,500 lines in 3–6 helper modules.

## Checkout and delivery

- Fetch `cryptography/pass-shelat-ch2-4`. Start a local branch `fill/learning` at the exact issue base, and
  record the base in `REPORT.md`. Keep the proof branch local.
- Read `policy.md`, the attached environment addendum and `README.md`.
- Deliver every checkpoint and the final payload under `inbox/fills/learning/` on `exchange/pass-shelat-ch5-8`:
  - `REPORT.md`;
  - `patches/`: the whole `git format-patch` series from the issue base;
  - `patches/COMMITS.tsv`: one row per commit, giving its hash, the author's name, email and date, and the
    committer's name, email and date, so that `git am` at the base reproduces every hash. Before you push,
    check the reproduction in a scratch clone and say so in `REPORT.md`. The last batch's worker hashes
    could not be reproduced, because no committer metadata was delivered;
  - `src/`: the changed and new files;
  - `evidence/`, with an `evidence/SHA256SUMS` manifest (see *Evidence completeness*);
  - a top-level `SHA256SUMS` listing every delivered file under `inbox/fills/learning/` except itself. The
    delivered paths must equal the manifest's paths exactly, with nothing missing and nothing extra.
    Check this before each push.
- Commit as `fill learning: checkpoint N` and `fill learning: final`.
- Pull with rebase before pushing, push only your delivery path, and never force-push. Campaign changes land
  by a maintainer PR for Seyoon's approval.

## Base and parallel work

- **#307 (dl-crh) is not merged.** It changes `Candidates/DiscreteLog.lean`, the `Hashing.lean` facade and `Hashing/FromDiscreteLog*`. This unit edits none of them, and its closure contains none of them.
- The other fills of this batch (`prf-mac`, `derand`, `seq-zk`, `canonizer`, `sc-ot`, `sc-compose`) start from the same base.
  Each edits only its own owned file and helper directory.

## Target (frozen; quoted from the issue base)

```lean
theorem predictAdv_prfConcept_negligible (hF : PRF F) (A : NUPPT) (m : PolyExpr) :
    Negligible fun n => predictAdv (prfConcept F n) (m.eval n) (learnerOf A n (m.eval n)) := by
  sorry
```

It lives in namespace `TCSlib.Cryptography.Randomness`. The section variable is `F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool)` (explicit). The
theorem takes `hF : PRF F`, a machine `A : NUPPT` and a polynomial `m : PolyExpr`.

**The game** (`TCSlib/LearningTheory/PAC/Prediction.lean`): `predictAdv C m L = |predictSuccess C m L − ½|`
(`predictAdv_eq`). `predictSuccess` (`predictSuccess_eq`, `trialDist_eq`) is the probability, over a uniform key, `m`
independent uniform examples, uniform coins and a fresh uniform point `x`, that the hypothesis agrees with `C_k(x)`.
The examples are labelled by `label` (`label_apply`). The fresh point may coincide with an example.

**The owned definitions:** `prfConcept F n k x` is the first bit of `F n k x`, `false` at `n = 0`
(`prfConcept_eq`); `encodeSample_eq`; `learnerOf A n m S r x` is `[A(1^n, ⟨S, x⟩; r) = [true]]` (`learnerOf_eq`).

**Dependencies.** The proof needs neither `prfMAC_secure` (the MAC modules are not in this closure) nor any
other admitted target. Part (c), `not_weakLearnsUnder_prfConcept`, in the same file is proved from this target
and is unchanged; its axioms become standard with yours.

## Published interfaces

| Interface | Provider |
|---|---|
| `prfConcept_eq`, `encodeSample_eq`, `learnerOf_eq`, `prfConcept_decidable` (the evaluator pattern) | owned file |
| `trialDist_eq`, `predictSuccess_eq`, `predictAdv_eq`, `label_apply`, `predictSuccess_coin` | `LearningTheory/PAC/Prediction.lean`, `PAC/Defs.lean` |
| `FinDist` laws (`uniform`, `prod`, `iid`, `probTrue`) and their readers; `uprob_comp_eq_probTrue_map` | `InformationTheory/FinDist.lean`, `Asymptotic/SamplingFinDist.lean` |
| `PRF`, `PRF.negligible_prfAdv`, `prfAdv_toOracleAdversary`, `prfAdv_def`, `oracleDist_apply`, `acceptProb_random_eq_lazy`, `lazyDist_apply` | `Pseudorandom/Functions/Asymptotic/Defs.lean`, `…/Defs.lean`, `…/OracleAdversary.lean`, `…/LazySampling.lean` |
| T1 `exists_handlerMachine` (non-adaptive queries) and the `PolyHandler` readers; T2; T4 `exists_toOracleAdversary_of_bitCodec` | `Games/Efficiency.lean` |
| `prob_mem_le`, `expect_sample_mem_le` | `Games/Hopping.lean` |
| `NUPPT.exists_comp`, `ofPolyTimeUniform` and the run/coin readers; `coinBlock`, `FunFamily.blocks`, `ofFn_blocks` | `Complexity/Randomized/Closure.lean`, `Asymptotic/Adversary.lean`, `Foundations/BitLists.lean` |
| `Negligible.add`, `mono`, `mul_pow` (the polynomial factor `m(n)`), `negligible_two_pow_neg` | `Foundations/Negligible.lean` |
| `simulate` and `OracleComp` laws, `buildComp_*`, `CostBoundedBy`, `bitCodec_*`, `ProbComp.expect_*`, `advantage_eq`, `accept_eq` | `Games/*` |

## Proof route and checkpoints

1. **Checkpoint 1 · the distinguisher and the real game (sketch step 1).** Build `D`: its coins are `A`'s coins and `m(n) + 1` blocks of `n` bits (`coinBlock`). It queries its oracle at the `m(n) + 1` points (T1, non-adaptive), labels the first `m(n)` with the first bits of the answers, runs `A` on `⟨encodeSample S, x_last⟩`, and outputs whether `A`'s prediction equals the first bit of the last answer. Make it an oracle adversary with T4 at `ℓ₁ = ℓ₂ = var`. Prove that with the oracle `f_k` its acceptance probability is `predictSuccess (prfConcept F n) (m n) (learnerOf A n (m n))`: the oracle run with uniform coins has the law `trialDist × uniform`, through `uprob_comp_eq_probTrue_map` and the `FinDist` product and `iid` readers. Send this checkpoint.
2. **Checkpoint 2 · the random function (sketch step 2).** With a uniform random function, the acceptance probability is within `m(n)/2^n` of `½` for `n ≥ 1`: unless the last point was sampled (probability at most `m(n)/2^n`), its label is the first bit of a fresh uniform value, independent of the sample. Send this checkpoint.
3. **Final · the bound (sketch step 3).** `predictAdv ≤ prfAdv (F n) (D^{m(n)+1}) + m(n)/2^n` for `n ≥ 1`. It is negligible by `PRF.negligible_prfAdv`, `Negligible.mul_pow` and `Negligible.add`. Handle `n = 0` by `Negligible.mono` (eventual bounds).

Check the edge cases: `n = 0` (one point, `prfConcept` constant `false`); `m(n) = 0` (no examples); a fresh point equal to an example; `A` printing anything other than `[true]`; the codecs' timeout outputs; the coin split between `A.Coins n` and the `(m(n) + 1) · n` sample bits.

If the sketch is wrong, or a target is false as stated, stop and escalate with the exact obligation: a
checkpoint with the counterexample or the missing fact. Do not weaken any statement.

## Scope and proof discipline

- **Owned file.** You own `TCSlib/Cryptography/Randomness/Learning.lean` (149 lines at the issue base):
  - replace the target's proof body and edit its sketch to describe the delivered proof;
  - update the module title (drop "(statement phase)" where present) and the `## Main results` status.
- **Helper modules.**
  - They are permitted under `TCSlib/Cryptography/Randomness/Learning/`. The owned file imports them precisely and gets a
    `## Contents` list.
  - **Facades.** After the facade-lint fix (#305), a new helper under `X/` is covered as long as `X.lean`
    imports it, so no parent facade needs an edit.
  - A helper may import `Games/Efficiency`, `Games/Hopping`, `Encryption/PrivateKey/OracleFromPRF` (and its helpers) and `Asymptotic/SamplingFinDist`. None is downstream of the owned file, so there is no cycle (checked at the issue base); the order includes their upstream closure.
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
  - **Nearest relatives here:** ext-nosrc's sampler law (`Randomness/Extraction/Sampler.lean`), the GGM reduction (`Pseudorandom/Functions/Asymptotic/GGM/Reduction.lean`), the T1 reductions of hash-sign and Lamport (`Signatures/HashAndSign/*`, `Signatures/Lamport/*`) and the PRFGame collision bound (`OracleFromPRF/Collision.lean`).
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
  - Bootstrap from `order.txt` (246 modules) and the narrow `roots.txt` (82), following the addendum.
  - Check one module per `scripts/lean_check_tree.sh` call, with one Lean process per olean tree.
  - Never run `lake build` or an unfiltered cache get. Run Python as `python3 -I`.
  - Insert helper modules before their consumers.
- **Sweep.**
  - Recheck the owned module, then sweep the supplied order with 0 errors.
  - Compare the `sorry` warnings with `base-sorries.txt` (20 declarations in 10 modules). The only change
    must be the removal of `predictAdv_prfConcept_negligible`.
- **Axioms.**
  - Print the axioms of `predictAdv_prfConcept_negligible`. Expect only `propext`, `Classical.choice` and `Quot.sound`.
  - Print them for every stored constant of the changed and new files, and of `not_weakLearnsUnder_prfConcept`.
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
