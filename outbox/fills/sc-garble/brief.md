# Claude fill · special encryption and garbling probability (`sc-garble`, U1)

**Issue base** `fbd37f447596d4207c8d08b7ef7602f57fe95198`: the head of draft PR #315 (`prf-long`, branch
`land/pass-shelat-prf-long`), **not** the records tip. **Unit** `sc-garble` (U1 of the secure-computation plan).
**Worker** Claude (standing ruling, 2026-11-11). **Lean** 4.25.0 and the Mathlib revision in that commit's
`lake-manifest.json`.

**Why this base (the `prf-long` dependency).** The B1 proof and `spDecStr_wrongKey` use the PRF machinery at
`ℓ(n)`-bit outputs that `prf-long` delivered (D1–D4, ruling B3). That machinery is not merged: it is draft PR #315,
under its own gate (Gate 31). Under the campaign's **proved-modulo rule** (`policy.md` §1: a consumer cites a
dependency while its own landing is still running), you build on the #315 head `fbd37f44`. Your results are proved
modulo the merge of #315, and `sc-garble` lands only after #315 merges, rebased by the maintainer. The #315 head
contains everything on the records branch up to `dd98360d` (#303, #305–#309, #311 and #312) plus the six prf-long
commits; the records commits since then touch no Lean.

Prove seven admitted, frozen statements:

| Target | File | Source |
|---|---|---|
| `spDecStr_wrongKey` | `TCSlib/Cryptography/SecureComputation/SpecialEncryptionSecurity.lean` | [PS10, §6.2.2], "the extra property" (Claim 157.a (ii), strings) |
| `specialScheme_wrongKey` | the same | Claim 157.a (ii), the scheme |
| `specialScheme_multiMessageSecure` | the same | Claim 157.a (i); [PS10, Definition 93.1, Theorem 99.2] |
| `nestedSpecial_wrongKeyBot` | `TCSlib/Cryptography/SecureComputation/GarblingSecurity.lean` | Claim 157.a (ii) for the nesting, [PS10, §6.2.2–6.2.3] |
| `uprob_not_good_le` | `TCSlib/Cryptography/SecureComputation/Garbling.lean` | Claim 159.a, probabilistic part, [PS10, §6.2.3] |
| `yaoSeed_good_whp` (**only this body** of the file) | `TCSlib/Cryptography/SecureComputation/Yao.lean` | Claim 159.a applied to Protocol 162.6's seed |
| `sliceMultiMessageSecure_of_prfOut` (the B1 statement) | `TCSlib/Cryptography/SecureComputation/SpecialEncryptionMulti.lean` | [PS10, §6.2.2, "it is easy to modify construction 99.1"; Definition 93.1, Theorem 99.2]; [LP09] |

All seven are confirmed at the issue base: each is a `theorem` whose body is `sorry` (`base-sorries.txt`). The
first six passed the prong statement phase and Gate 06; the B1 statement passed Gate 27 (CLEAR, 0/0/1/0) and was
merged in #311 (ruling B1, 2026-11-14). All are frozen. Their docstrings hold the maintainer's proof sketches.

Also publish, as the plan's requirement **B2**, a stronger garbling bound (see *Scope* and checkpoint 2).

## Feasibility and size (maintainer's assessment)

**Feasible.** The secure-computation plan (`briefs/pass-shelat-ch5-8/maintainer/securecomp-plan-2026-11-14/plan.md`,
§2.3–2.8 and §3) found none of these statements false as frozen and no missing hypothesis. Codex gave a full
mathematical proof of B1 as written at Gate 27, with one convention (the maximum advantage is `0` when no slice
vector fits). The prf-long review (`fills/prf-long/final-r1/review.md`, § *Content*) checked the B1 consumer map
below against the merged B1 file.

**Estimated size: 2,500–4,700 lines in all.** The plan's estimate was 3,000–5,000, with the multi-message lemma
dominating (1,000–1,800 lines, the `ℓ`-output PRF hybrid included). D1–D4 now supply that hybrid, the query-chain
and one-query machines and the total; what remains of B1 is the slice post-processor, its poly-time parser, the
advice and the maximization.
- checkpoint 1, 700–1,350: `spDecStr_wrongKey` 300–600 (the one-query machine and the budget-1 PRF bound are D3 and
  D1; left are the distinguisher, the length guard, the random-function probability `2^{-n}` and the coin
  bookkeeping), `specialScheme_wrongKey` 100–250, `nestedSpecial_wrongKeyBot` 300–500;
- checkpoint 2, 1,000–1,800: the B2 bound with `uprob_not_good_le` as its corollary 500–900, `yaoSeed_good_whp`
  500–900 (the push-forward through disjoint coin blocks; the output-key collision);
- the final, 800–1,550: the B1 step 0 (masks, the post-map `P`, its poly-time parser and the pointwise identity with
  the slice sampler, the advice and the maximization) 750–1,450, and `specialScheme_multiMessageSecure` 50–100.

## Checkout and delivery

- Fetch `land/pass-shelat-prf-long` (and `cryptography/pass-shelat-ch2-4`). Start a local branch
  `fill/sc-garble` at the exact issue base `fbd37f447596d4207c8d08b7ef7602f57fe95198`, and record the base in
  `REPORT.md`. Keep the proof branch local.
- Read `policy.md`, the attached environment addendum and `README.md`.
- Deliver every checkpoint and the final payload under `inbox/fills/sc-garble/` on `exchange/pass-shelat-ch5-8`:
  - `REPORT.md`;
  - `patches/`: the whole `git format-patch` series from the issue base;
  - `patches/COMMITS.tsv`: one row per commit, giving its hash, the author's name, email and date, the committer's
    name, email and date, and its **signing** (`none`, or the signature format), so that `git am` at the base
    reproduces every hash. **Commit with `git -c commit.gpgsign=false`** (prf-mac F-05, prf-long F-03: the last
    workers' hashes reproduced only with the environment's deterministic SSH signature, which was not recorded). If
    a commit is signed anyway, say so in its row and in `REPORT.md`. Before you push, check the reproduction in a
    scratch clone and say so in `REPORT.md`;
  - `src/`: the changed and new files;
  - `evidence/`, with an `evidence/SHA256SUMS` manifest (see *Evidence completeness*);
  - a top-level `SHA256SUMS` listing every delivered file under `inbox/fills/sc-garble/` except itself. The
    delivered paths must **equal** the manifest's paths exactly, with nothing missing and nothing extra, and
    without a leading `./`. Check this before each push.
- Commit as `fill sc-garble: checkpoint N` and `fill sc-garble: final`.
- Pull with rebase before pushing, push only your delivery path, and never force-push. Campaign changes land by a
  maintainer PR for Seyoon's approval.

## Base and parallel work

- **In the base:** #303, #305–#309, #311 (the B1 statement) and #312 (the derand host), and prf-long's six commits
  (four worker commits, LE-doc, LE-ws). The lint baseline below is re-run at the issue base.
- **#315 (prf-long) is under Gate 31.** Do not edit its files: `Pseudorandom/Functions/Asymptotic/Defs.lean`,
  `Encryption/PrivateKey/FromPRF*` and `Encryption/PrivateKey.lean` are **frozen for this unit**, and D1–D4 are used
  as published. If Gate 31 leads to a resolution edit of #315, stay on `fbd37f44`; the maintainer rebases at
  landing. If a D1–D4 statement turns out not to fit, stop and escalate (*Escalation*); do not restate it.
- **In flight, inside this order, not edited by this unit:**
  - `sc-ot` (final in, under review) changes `SecureComputation/ObliviousTransfer.lean` and adds helpers;
  - `sc-compose` (dispatched) changes `SecureComputation/ComposeSecurity.lean`;
  - `derand` (staged) has pre-approved additions to `Complexity/ClassP/DTIME.lean` and
    `Complexity/Randomized/Build/IterateFind.lean`.

  They are in the closure only as upstream modules, or (`ObliviousTransfer`, `ComposeSecurity`) as modules that
  `YaoReal` imports. Stay on the issue base if any of them merges during the fill.
- **Merged after the issue base:** #314 (the `prfAdv_eq_expect` promotion, Gate 30 CLEAR), at `59c2c1fb` on the
  records branch. It adds `TCSlib.Cryptography.prfAdv_eq_expect` to `Pseudorandom/Functions/Defs.lean` (upstream of
  your order) and re-derives `ETTGame.prfAdv_eq_expect`. It is **not** in your base; do not merge it in. The
  maintainer rebuilds the combined tree at landing (#315 itself needs that integration rebuild before it merges).
- **Later:** `sc-yao` (U3) proves `yaoHybrid_polyTime` and `yaoHybrid_simulators` in `Yao.lean` after this unit
  lands; it shares `Yao.lean` with you (*Scope*). #313 (`learning`) is outside this order.

## Targets (frozen; quoted from the issue base)

```lean
theorem spDecStr_wrongKey (ℓ : PolyExpr)
    (G' : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin ((PolyExpr.add .var ℓ).eval n) → Bool))
    (E' : List Bool → List Bool)
    (hGE' : ∀ n (s x : Fin n → Bool), E' (pairEncode (List.ofFn s) (List.ofFn x)) =
      List.ofFn (G' n s x))
    (hG' : PRFOut (.add .var ℓ) G') :
    ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n (m : Fin (ℓ.eval n) → Bool),
      1 - ε n < uprob (fun t : (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool) =>
        spDecStr E' n (ℓ.eval n) (List.ofFn t.2.1)
          (spEncStr E' (List.ofFn t.1) (List.ofFn m) (List.ofFn t.2.2)) = none) := by
  sorry
```

```lean
theorem specialScheme_wrongKey (hG : PRFOut (.add .var .var) G) :
    ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n (m : Fin n → Bool),
      1 - ε n < uprob (fun t : (specialScheme G E hE hGE).gen.Coins n ×
          (specialScheme G E hE hGE).gen.Coins n × (specialScheme G E hE hGE).enc.Coins n ×
          (specialScheme G E hE hGE).dec.Coins n =>
        decodeFin n ((specialScheme G E hE hGE).dec.runAt n
          (pairEncode ((specialScheme G E hE hGE).gen.runAt n [] t.2.1)
            ((specialScheme G E hE hGE).enc.runAt n
              (pairEncode ((specialScheme G E hE hGE).gen.runAt n [] t.1) (List.ofFn m)) t.2.2.1))
          t.2.2.2) = none) := by
  sorry
```

```lean
theorem specialScheme_multiMessageSecure (hG : PRFOut (.add .var .var) G) :
    (specialScheme G E hE hGE).MultiMessageSecure := by
  sorry
```

```lean
include hGE₁ hGE₂ in
theorem nestedSpecial_wrongKeyBot (hG₁ : PRFOut (.add .var .var) G₁)
    (hG₂ : PRFOut (.add .var innerLen) G₂) :
    ∃ δ : ℕ → ℝ, Negligible δ ∧ ∀ n, (nestedSpecial E₁ E₂ n).WrongKeyBot (δ n) := by
  sorry
```

```lean
theorem uprob_not_good_le [Fintype K] [Fintype ρ] (hdec : M.DecCorrect) {δ : ℝ}
    (hδ : M.WrongKeyBot δ) (hC : Cc.IsFaninTwo) :
    uprob (fun s : GarbleSeed Cc K ρ => ¬ Good M Cc s) ≤ 12 * Cc.gates.length * δ := by
  sorry
```

```lean
include hGE₁ hGE₂ in
theorem yaoSeed_good_whp (hG₁ : PRFOut (.add .var .var) G₁)
    (hG₂ : PRFOut (.add .var innerLen) G₂) :
    ∃ δ : ℕ → ℝ, Negligible δ ∧ ∀ n, uprob (fun r : Fin ((yaoCoins Y).eval n) → Bool =>
      ¬ (Good (nestedSpecial E₁ E₂ n) (Y.circ n) (yaoSeed Y n (List.ofFn r)) ∧
        ∀ j, keyAt (Y.circ n) (yaoSeed Y n (List.ofFn r)) (Y.outs n j) false ≠
          keyAt (Y.circ n) (yaoSeed Y n (List.ofFn r)) (Y.outs n j) true)) ≤ δ n := by
  sorry
```

```lean
theorem sliceMultiMessageSecure_of_prfOut {ℓ : PolyExpr}
    {G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (ℓ.eval n) → Bool)} (hG : PRFOut ℓ G) :
    SliceMultiMessageSecure G := by
  sorry
```

- **`SpecialEncryptionSecurity.lean`** (namespace `TCSlib.Cryptography.SecureComputation`, under
  `open Complexity Turing TCSlib.Cryptography`): `specialScheme_multiMessageSecure` and `specialScheme_wrongKey` use
  the section variables `G` (length-doubling, `Fin (n + n)` outputs), `E`, `hE : PolyTimeComputable E` and `hGE`.
  `spDecStr_wrongKey` takes its own `ℓ`, `G'`, `E'`, `hGE'` and `hG'`; note that `E'` has **no**
  `PolyTimeComputable` hypothesis (use the evaluator of `hG'.easy`, which agrees with `E'` on canonical inputs).
- **`Garbling.lean`** (namespace `TCSlib.Cryptography.SecureComputation`, `open BoolCircuit TCSlib.Cryptography`):
  section variables `{K C ρ : Type} [Inhabited K] {n : ℕ} (M : MultiEnc K C ρ) (Cc : DAGCircuit n)`. `GarbleSeed` is
  an `abbrev` (notation): keys, row coins and row permutations.
- **`GarblingSecurity.lean`**: section variables `G₁`, `G₂` (`Fin ((PolyExpr.add .var innerLen).eval n)` outputs),
  `E₁`, `E₂`, `hGE₁`, `hGE₂`, with `include hGE₁ hGE₂ in`. The proved `garbling_good_whp` already consumes
  `nestedSpecial_wrongKeyBot` and `uprob_not_good_le`.
- **`Yao.lean`** (`section Security`): `yaoSeed_good_whp` with the same `G₁`, `G₂`, `hGE₁`, `hGE₂` and the file
  variables `Y`, `E₁`, `E₂`. `Y.fanin`, `Y.size_le`, `Y.outs_lt` and `Y.outs_sink` are its circuit facts.
- **`SpecialEncryptionMulti.lean`**: the definitions `sliceEnc`, `sliceMultiEncDist`, `SliceMultiMessageSecure`
  with their readers, the target, and the proved corollary `specialScheme_multiMessageSecure_of_joint` and bridges.

## Published interfaces

| Interface | Provider |
|---|---|
| **D1** `prfAdv_toOracleAdversary_out`, `OracleEnsemble.Indist.negligible_prfAdv` | `Pseudorandom/Functions/Asymptotic/Defs.lean` (#315) |
| **D2** `prfEncRealOut` (`prfEncRealOut_apply`), `otpEncOut` (`otpEncOut_apply`), `multiMsgAdvOut` (`eval_multiMsgAdvOut`, `multiMsgAdvOut_boundedBy`), `acceptProb_oracleDist_multiMsgAdvOut`, `prfAdv_multiMsgAdvOut`, `distAdv_prfEncRealOut_random_otp_le`, `acceptProb_otpEncOut`, `distAdv_prfEncRealOut_le` | `Encryption/PrivateKey/FromPRF/Hybrid.lean` (#315) |
| **D3** `MultiMsg.exists_queryChainOut_nuppt`, `MultiMsg.exists_oneQuery_nuppt` | `Encryption/PrivateKey/FromPRF/ReductionMachine.lean` (#315) |
| **D4** `encodeTupleOut` (`encodeTupleOut_eq`, `encodeTupleOut_eq_flatten`), `MultiMsg.encodeList_eq_flatMap`, `MultiMsg.exists_negligible_distAdv_prfEncRealOut` | `Encryption/PrivateKey/FromPRF/MultiMsgOut.lean` (#315) |
| `MultiMsg.prfAdv_congr_equiv`, `MultiMsg.abs_uexp_sub_le_uprob`, `MultiMsg.negligible_choose_div_two_pow`, `uprob_not_injective_le`, `pushesUniform_comp_injective`, `MultiMsg.blockMapFun`, `MultiMsg.take_drop_ofFn_blocks` | `FromPRF/HybridLemmas.lean`, `FromPRF/Hybrid.lean`, `FromPRF/ReductionMachine.lean` |
| `OracleEnsemble.keyed_O`, `random_O`, `acceptProb_random_eq`, `acceptProb_random_eq_lazy`, `NUPPT.toOracleAdversary` readers | `Pseudorandom/Functions/Asymptotic/Defs.lean` |
| `PRFOut` (fields `easy`, `pseudorandom`), `prfOut_var_iff`, `specialScheme_gen/_enc/_dec` (`simps`) | `SecureComputation/SpecialEncryptionSecurity.lean` |
| `spEncStr_eq`, `spDecStr_eq`, `spDecStr_spEncStr`, `length_spEncStr`, `runAt_spEnc`, `runAt_spDec`, `polyTimeComputable_spEncFun` | `SecureComputation/SpecialEncryption.lean` |
| `sliceEnc_eq`, `sliceEnc_eq_spEncStr`, `sliceEnc_append_left/_right`, `sliceMultiEncDist_apply`, `sliceMultiMessageSecure_iff`, `specialScheme_multiMessageSecure_of_joint` | `SecureComputation/SpecialEncryptionMulti.lean` |
| `MultiEnc.decCorrect_iff`, `wrongKeyBot_iff`, `good_iff`, `keyAt_eq`, `argKeys_eq`, `garbledRow_eq`, `garbledTable_eq`, `tableAt_eq`, `tableAt_gate`, `gateOut_eq`, `GarbleSeed_eq` | `SecureComputation/Garbling.lean` |
| `nestedSpecial_enc`, `nestedSpecial_dec` (`simps`), `nestedSpecial_decCorrect`, `innerLen_eq` | `SecureComputation/GarblingSpecial.lean` |
| `yaoSeed_fst`, `yaoSeed_snd_fst`, `yaoSeed_snd_snd`, `keyAt_yaoSeed`, `readBits_apply`, `xorShift_apply`, `assignIdx_eq`, `yaoCoins_eval` | `SecureComputation/Yao.lean` |
| `runAt_coinKey`, `decodeFin_ofFn`, `PrivateKeyScheme.multiMessageSecure_iff`, `multiEncDist_apply`, `encodeList_nil/_cons`, `NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn`, `NUPPT.coinsCongr_ofFn` | `Encryption/PrivateKey/{FromPRG,EnsembleSecurity}.lean`, `Asymptotic/Adversary.lean`, `Complexity/Randomized/PPT.lean` |
| `NUPPT.exists_comp`, `NUPPT.exists_withAdvice`, `NUPPT.exists_split`, `NUPPT.distinguisherL` readers | `Complexity/Randomized/Closure.lean` and the `NUPPT` layer |
| `polyTimeComputable_blockMap`, `NMSim.chunkMap` (`polyTimeComputable_chunkMap`) | `Complexity/Randomized/Repetition.lean`, `Encryption/PublicKey/NonMalleability/Simulation/Generic.lean` |
| `uprob_mono`, `uprob_exists_le`, `uprob_prod`, `uprob_comp_equiv`, `uprob_fst`, `uprob_le_one`, `uprob_nonneg`, `uprob_true`, `uprob_false`, `uprob_const`, `acceptProb_def`, `distAdv_def`, `acceptProb_comp_equiv`, `uprob_comp_eq_sum_map`, `distAdv_comp`, `OneWay.uprob_eq_one_div_card`, `OneWay.uexp_const`, `HardcoreBit.pushesUniform_restrict`, `Negligible.add`, `negligible_two_pow_neg`, `EnsembleLemmas.negligible_polyExpr_mul` | `Foundations/{Probability,Experiments,Negligible}.lean`, `Asymptotic/EnsemblesLemmas.lean`, `Pseudorandom/Indistinguishability.lean`, `OneWayFunctions/Basic.lean`, `HardcoreBit/Basic.lean` |

## Scope

**Owned files** (you prove their targets and may add to them):

| File | Lines at base | What changes |
|---|---|---|
| `SecureComputation/SpecialEncryptionSecurity.lean` | 157 | the proofs of `spDecStr_wrongKey`, `specialScheme_wrongKey` and `specialScheme_multiMessageSecure` and their sketch paragraphs; new public declarations (for example the coin-relabelling readers of `specialScheme`, see *The import direction*); the module title (drop "(statement phase)") and `## Main results`; imports of its helpers and of the D1–D4 modules |
| `SecureComputation/SpecialEncryptionMulti.lean` | 325 | the proof of `sliceMultiMessageSecure_of_prfOut` and its sketch; the title and `## Main results`; imports of its helpers |
| `SecureComputation/Garbling.lean` | 427 | the B2 lemma (new, beside the target); the proof of `uprob_not_good_le` from it and its sketch; the title and `## Main results`; imports of its helpers |
| `SecureComputation/GarblingSecurity.lean` | 87 | the proof of `nestedSpecial_wrongKeyBot` and its sketch; the title and `## Main results`; imports of its helpers |
| `SecureComputation/Yao.lean` (**shared** with `sc-yao`) | 942 | **only** the body of `yaoSeed_good_whp`, its `**Proof sketch.**` paragraph, and the `## Main results` bullet that lists it (split `yaoSeed_good_whp` out as proved). No import line, no new declaration, nothing else |

**New helper modules** are permitted in four directories, each imported by its file (after the facade-lint fix
#305 a helper under `X/` is covered as long as `X.lean` imports it, so `SecureComputation.lean` needs no edit):
- `SecureComputation/SpecialEncryptionSecurity/`, imported by `SpecialEncryptionSecurity.lean`: the PRF-facing parts
  of the wrong-key proof and the pad identities shared by the two multi-message proofs. They may import the D1–D4
  modules (`FromPRF/MultiMsgOut`, `FromPRF/ReductionMachine`, `FromPRF/Hybrid`, `Functions/Asymptotic/Defs`). State
  them on `PRFOut`'s clause (2) hypothesis
  `(OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := ℓ) F).Indist (OracleEnsemble.random .var ℓ)`, as prf-long does, since
  `PRFOut` is defined in `SpecialEncryptionSecurity.lean` itself.
- `SecureComputation/SpecialEncryptionMulti/`, imported by `SpecialEncryptionMulti.lean`: the slice post-processor,
  its parser and the advice (B1 step 0). These cannot see `sliceEnc`; state them on `spEncStr` and the D4 objects,
  and assemble in `SpecialEncryptionMulti.lean`.
- `SecureComputation/Garbling/`, imported by `Garbling.lean`: **definition-free** probability helpers (the marginal
  of the keys at a `Nodup` argument list, the union-bound bookkeeping, the push-forward of a uniform string through
  disjoint blocks). `Garbling.lean` imports only `DAGCircuit`, two Mathlib modules and `Foundations.Probability`;
  keep these helpers as light. They are upstream of `Yao.lean`, so `yaoSeed_good_whp` can use them without a new
  import in `Yao.lean`.
- `SecureComputation/GarblingSecurity/`, imported by `GarblingSecurity.lean`: the relabelling for the nesting.

Check the import graph for cycles: a helper of a file never imports that file or anything downstream of it.

**The import direction (binding): `specialScheme_multiMessageSecure`.**
- The frozen target sits in `SpecialEncryptionSecurity.lean`, but the proved corollary
  `specialScheme_multiMessageSecure_of_joint` sits in `SpecialEncryptionMulti.lean`, which **imports**
  `SpecialEncryptionSecurity.lean`. So the target **cannot** be proved through that corollary in its own file; the B1
  docstring's "is `specialScheme_multiMessageSecure_of_joint G E hE hGE (sliceMultiMessageSecure_of_prfOut hG)`" holds
  only as a statement about the two results. Do not move either declaration (the frozen-statement rule).
- Prove it **directly from D4** in its own file: `ℓ = .add .var .var`, masks `w_i = 0^n ‖ m_i`, all slices `(0, n)`,
  so no post-map is needed (the window is all of `G_k(r_i)`). The scheme's sampler is then
  `encodeTupleOut ∘ prfEncRealOut (G n) w` up to the relabelling of `Gen`'s and `Enc`'s coins as an `n`-bit key and
  `n`-bit nonces (keeping their strings): `runAt_coinKey`, `runAt_spEnc`, `hGE`, and `spEncStr E k m r =
  ⟨r, (0^n ‖ m) ⊕ E(⟨k, r⟩)⟩` (`spEncStr_eq`), closed with `acceptProb_comp_equiv`.
- That relabelling repeats the **frozen private** helpers of `SpecialEncryptionMulti.lean`
  (`specialScheme_gen_runAt`, `specialScheme_enc_runAt`, `specialKeyEq`, `ofFn_specialKeyEq`, `specialNonceEq`,
  `ofFn_specialNonceEq`), which you may not make public or delete. Publish it **once**, as public readers in
  `SpecialEncryptionSecurity.lean` beside `specialScheme`, and disclose the overlap with the private copies as a
  **ledger** row in *Overlap and reuse* (the maintainer opens the ledger row; the private copies are removed in the
  cleanup). **Names:** the new public names must differ from those six private names and from
  `zipWith_xor_append_of_le`: a public declaration upstream with the same name makes the frozen private one fail to
  declare (the prf-long clash, DL-46). The name-clash scan (*Checks*) covers this.
- Put the pad identity that both multi-message proofs need (a special ciphertext from offset `o` equals the D4 entry
  `⟨r_i, w_i ⊕ G_k(r_i)⟩` cut by `P`) in a `SpecialEncryptionSecurity/` helper, so it is proved once.

**The frozen-statement rule (binding; checked).**
- **Headers.** Every declaration present at the issue base in the five owned files stays in the same file and the same
  order, with its header byte-identical. The header is the attributes and modifiers, the keyword, the name, the
  binders and the type, up to the `:=`, `by`, `where` or first `|` that begins the proof. `open … in`,
  `include … in` and `omit … in` prefixes count as part of the header.
- **Definitions are statements.** A `def`, `abbrev`, `structure`, `inductive`, `class` or `instance` stays
  byte-identical, body included. Delete nothing, private lemmas included.
- **What may change.** Only the proofs of the seven targets; their `**Proof sketch.**` paragraphs, rewritten to
  describe the delivered proof (the statement prose before the sketch stays); module docstrings (title, `## Main
  results`, `## Contents`; for `Yao.lean` only the one bullet); and, within the scope above, added imports and
  declarations. `set_option`s and attributes do not change.
- **`Yao.lean` is stricter:** apart from the `yaoSeed_good_whp` body, its sketch and its `## Main results` bullet,
  the file is byte-identical to the base.
- **Check.** Write a `python3 -I` script that extracts every declaration of the five files at the base and at the
  final and compares headers (and whole definitions) byte for byte, and checks that the base declarations appear in
  the same order; for `Yao.lean` also report the full diff and show it touches only the allowed lines. Deliver it and
  its output under `evidence/headers/`, with zero differences. Add a control: a copy with one header altered by one
  character must report exactly one difference. The prf-long review's checker counted 126 declarations; do not let
  private or unnamed declarations, `include … in` lines or match-arm headers escape the count.

**Everything else is frozen**, in particular `SpecialEncryption.lean`, `GarblingSpecial.lean`, the rest of
`Yao.lean`, `YaoReal.lean`, every prf-long file (*Base and parallel work*), `Pseudorandom/*`, `Encryption/*`,
`Games/*` (`Games/Efficiency.lean` is at 982 lines; do not add to it) and the circuit library.
- **Scope requests.** If the route needs any other change to a frozen file (a reader beside a foreign definition,
  an import or declaration in `Yao.lean`, a promotion, a change to a D1–D4 statement), stop that line of work. Ask
  Seyoon in your session, giving the exact file, the diff and the reason, and go ahead only on his approval. Record
  the request and his answer verbatim under `evidence/scope-request/` and in `REPORT.md` § *Scope requests*. Seyoon
  prefers a route with no frozen-file edit where one exists.
- A lemma that belongs in an existing file goes in your helper module, with a promotion request.

## Proof route and checkpoints

1. **Checkpoint 1 · the wrong-key property.**
   - **`spDecStr_wrongKey`** (plan §2.3; its sketch).
     - *The event.* For every `n` and `m`, with `k, k', r` uniform: the length guard of `spDecStr` always passes on an
       honest ciphertext (`|k'| = |r| = n`, and `|c₂| = n + ℓ(n)` because `E'` outputs `n + ℓ(n)` bits by `hGE'`;
       `length_spEncStr`), so the decryption is `none` exactly when `G'_k(r)_{<n} ≠ G'_{k'}(r)_{<n}`. The event does
       not depend on `m`.
     - *The distinguisher.* `D` reads `⟨⟦r⟧, ⟦u⟧⟩`, draws `k'` from its coins, and accepts iff `u_{<n}` equals the
       first `n` bits of `E(⟨k', r⟩)`, where `E` is the polynomial-time evaluator of `hG'.easy` (it agrees with `E'`
       on canonical inputs through `hGE'`). `MultiMsg.exists_oneQuery_nuppt D (.add .var ℓ)` turns it into a
       one-query oracle machine `B` with coins `(r, c)` and the evaluation identity for every oracle.
     - *Against a random function* the acceptance probability is exactly `2^{-n}`: the answer `g(r)` is uniform and
       independent of `k'` and `r` (`OracleEnsemble.acceptProb_random_eq`/`_lazy`; `OneWay.uprob_eq_one_div_card`
       for the point probability). *Against `G'_k`* it is the success probability of the wrong key.
     - *The bound.* `hG'.pseudorandom.negligible_prfAdv B (.const 1)` (D1, budget `1`; `PolyExpr.eval_const`) makes
       the PRF advantage negligible. Take `ε n = prfAdv … + 2 · 2^{-n}`: the extra `2^{-n} > 0` gives the strict `<`.
   - **`specialScheme_wrongKey`** (plan §2.4): `spDecStr_wrongKey` at `ℓ = .var` with `G' = G` and `E' = E`, through
     `runAt_coinKey`, `runAt_spEnc`, `runAt_spDec` and `decodeFin_ofFn` (`1^{n+1}` decodes to no `n`-bit message; a
     `some` output has `n` bits); the `dec.Coins` factor has one element (`uprob_comp_equiv`, `uprob_fst`).
   - **`nestedSpecial_wrongKeyBot`** (plan §2.7; its sketch): the three cases (one position; two positions, first
     differs: `spDecStr_wrongKey` at `ℓ = innerLen` with `G₂`; first agrees, second differs: the outer layer opens by
     `spDecStr_spEncStr` and `length_spEncStr`, then `spDecStr_wrongKey` at `ℓ = .var` with `G₁`), the relabelling
     `(Fin len → Bool → K) × ρ ≃` (the used keys) × (the rest), and `δ = ε₁ + ε₂` (`Negligible.add`).
   - Send this checkpoint.
2. **Checkpoint 2 · the garbling bound (B2) and Yao's seed.**
   - **B2 (required, brief level).** `uprob_not_good_le` as frozen is about a uniform `GarbleSeed`, whose third
     component is a uniform `Equiv.Perm`, but `yaoSeed` uses XOR shifts, so it cannot be applied to Yao's seed (plan
     §2.8). Publish in `Garbling.lean`, beside the target, one stronger bound. The recommended form is the bound for
     **every fixed row-permutation family**; draft signature, binding unless the name clashes:

     ```lean
     theorem uprob_not_good_le_of_perm [Fintype K] [Fintype ρ] (hdec : M.DecCorrect) {δ : ℝ}
         (hδ : M.WrongKeyBot δ) (hC : Cc.IsFaninTwo)
         (π : (i : Fin Cc.gates.length) → Equiv.Perm (Fin (Cc.gates[i]).args.length → Bool)) :
         uprob (fun t : (Fin Cc.size → Bool → K) ×
             ((i : Fin Cc.gates.length) → (Fin (Cc.gates[i]).args.length → Bool) → ρ) =>
           ¬ Good M Cc (t.1, t.2, π)) ≤ 12 * Cc.gates.length * δ
     ```

     The allowed alternative is the bound for **every seed law whose keys and row coins are uniform and independent
     of the permutations**; if you choose it, give its signature in `REPORT.md` and say why. Either way it is one
     public declaration with a formula docstring, and:
     - **`uprob_not_good_le`** follows by averaging over the uniform permutations (reassociate the seed,
       `uprob_comp_equiv`, `uprob_prod`): a corollary, not a second proof;
     - the B2 proof is the target's sketch: correctness of the row of `a`; the arguments are distinct vertices below
       the gate's own (`IsFaninTwo`: `args.Nodup`, at most two arguments; `args_lt`), so the argument keys, the
       plaintext key and the row coin are independent; `WrongKeyBot` averaged over the plaintext and the coin; at
       most `4 · 3 = 12` events per gate; the union bound (`uprob_exists_le`). Constant gates add no event; the row
       order plays no role.
   - **`yaoSeed_good_whp`** (plan §2.8; its sketch) as a corollary of B2 and `nestedSpecial_wrongKeyBot` by
     push-forward: the keys, the row coins and the shifts of `yaoSeed` read disjoint blocks of Alice's coins
     (`yaoSeed_fst`, `yaoSeed_snd_fst`, `yaoSeed_snd_snd`, `readBits_apply`; the blocks fit in
     `yaoCoins = 10 S n + 2 S`, `assignIdx` injective below `4` for at most two positions, `|gates| ≤ size ≤ S`), so
     for each fixed shift block the keys and row coins are uniform; apply B2 with the XOR-shift family; add the output
     collision `outLen(n) · 2^{-n}` (two independent uniform keys per output vertex). `δ = 12 · S · δ₀ + outLen ·
     2^{-n}` is negligible (`EnsembleLemmas.negligible_polyExpr_mul`, `negligible_two_pow_neg`, `Negligible.add`).
     Keep the generic push-forward lemma in a `Garbling/` helper, so that `Yao.lean` changes only in this body.
   - Send this checkpoint.
3. **Final · the B1 statement and Claim 157.a (i).**
   - **`sliceMultiMessageSecure_of_prfOut`**, by the **B1 consumer map** (the prf-long review § *Content* and the
     prf-long worker's REPORT § *B1 consumer map*, both checked against the merged file):
     - **Step 0 · reduction to tuples (this unit's part).** Fix `D` and `q`. For a fitting slice vector
       (`o_i + n + ℓ_i ≤ ℓ(n)`) and messages `m`, the masks are
       `w_i = 0^{o_i + n} ‖ m_i ‖ 0^{ℓ(n) − o_i − n − ℓ_i} : Fin (ℓ.eval n) → Bool`, and the post-map
       `P_{o,ℓ} : (r, u) ↦ (r, (u.drop o_i).take (n + ℓ_i))` acts on each block inside `encodeList`. Prove pointwise,
       on the same seed space `(Fin n → Bool) × (Fin (q + 1) → Fin n → Bool)` (no coin relabelling), that
       `P_{o,ℓ} (encodeTupleOut (prfEncRealOut (G n) w t)) = sliceMultiEncDist G n q o len m t`, reading
       `prfEncRealOut` only through `prfEncRealOut_apply`, `encodeTupleOut` through `encodeTupleOut_eq` or
       `encodeTupleOut_eq_flatten`, and the slice sampler through `sliceMultiEncDist_apply`, `sliceEnc_eq` and
       `spEncStr_eq`: within one ciphertext the revealed prefix `G_k(r)_{[o, o+n)}` and the masked message are
       disjoint windows of `w ⊕ G_k(r)`.
     - **The reduction `D' = D ∘ P`, with the slices as advice.** The advice at `n` encodes the maximizing slice
       vector (`q(n) + 1` pairs of numbers at most `ℓ(n)`: polynomial length); `P` is polynomial-time given the
       advice (a block parser: `polyTimeComputable_blockMap`, `NMSim.polyTimeComputable_chunkMap`, or the
       `encodeList` readers); `D'` comes from `NUPPT.exists_comp` and `NUPPT.exists_withAdvice`, with
       `D'.distinguisherL n z = D.distinguisherL n (P z)` read through the `NUPPT` readers.
     - **The maximization, with the empty-set convention.** Let `A(n)` be `D`'s largest advantage over the finitely
       many fitting slice vectors and message pairs, and `0` when no slice vector fits (for example when `ℓ(n) < n`;
       the advice is then arbitrary). D4's `ε` precedes the masks, so
       `MultiMsg.exists_negligible_distAdv_prfEncRealOut hG.pseudorandom D' q` bounds the maximizing pair's
       advantage, and every fitting `o, ℓ, m, m'` is at most `A(n) ≤ ε(n)` (`distAdv_comp` moves `P` into `D'`).
       `hG.pseudorandom` is literally D4's hypothesis (the prf-long worker's B1 probe and the review's consumer probe
       check this at the base).
     - **Steps 1–3** (the PRF step, the random function and collision, the total) are inside D4; do not repeat them.
   - **`specialScheme_multiMessageSecure`** directly from D4, as in *The import direction*.
   - **Gate 27's hand-off obligations for `sc-garble`** (`gates/27-b1-multimsg/resolutions-r1.md`; obligations, not
     findings). Your delivery must show each: (1) the maximizing advice, with the empty-set convention; (2) the slice
     post-processor; (3) the random-function slice law (here: inside D2/D4, the full `ℓ(n)`-bit pads are uniform, so
     every window is; say where your proof relies on it); (4) the triangle bound (inside D4); (5) the frozen theorem:
     `specialScheme_multiMessageSecure` proved (directly, by the import direction), with
     `specialScheme_multiMessageSecure_of_joint` staying proved beside B1; (6) B2. Map each to declarations in
     `REPORT.md` § *Gate 27 hand-off*.

Check the edge cases: `n = 0` (keys and nonces empty; the strict `<` of `spDecStr_wrongKey` at `2^{-0} = 1`);
`ℓ(n) = 0` and `ℓ(n) < n` (no slice fits; `A(n) = 0`); `q(n) = 0`; messages of length `0`; slices that fit exactly
(the outer slice `(2n, 4n + 2)` of Yao fits exactly); `len = 1` and `len = 2` in `WrongKeyBot` and constant gates;
gates with fewer than two arguments; the XOR shift at `len = 0`; `|gates| = 0`; output vertices that coincide
(`outs` need not be injective).

**Escalation.** If a sketch is wrong, a target is false as stated, or a D1–D4 statement does not fit, stop and
escalate with the exact obligation: a checkpoint with the counterexample or the missing fact. Do not weaken any
statement.

## Proof discipline

- **Size and width.** Every line has at most 100 characters (Python `len`), and every file at most 1000 lines. Keep
  `Yao.lean` (942 lines) at most 1000: `sc-yao` adds two large bodies to the same file after you; if the body
  cannot fit, make a scope request. Check both with a short `python3 -I` script before each push and include its
  output in `evidence/`.
- **Parallel fills.** See *Base and parallel work*. Edit only the files of *Scope*.
- **Duplication (binding).**
  - **Search first.** Before writing any lemma, search `TCSlib/` and Mathlib for its statement shape and key names.
    Reuse published lemmas by importing them.
  - **Probability, expectation and list identities first.** The undisclosed re-proofs that the last reviews and gates
    found were all of this kind:
    - prf-mac (F-01, a major): `hadv` re-proved `ETTGame.prfAdv_eq_expect` (`EncryptThenTag/Reduction.lean:347`;
      promoted as `TCSlib.Cryptography.prfAdv_eq_expect` in `Pseudorandom/Functions/Defs.lean` by #314, merged
      after your base);
    - learning: `uprob_eq_point` restated `OneWay.uprob_eq_one_div_card` (`OneWayFunctions/Basic.lean:144`), and an
      inline argument re-proved `MultiMsg.abs_uexp_sub_le_uprob` (`FromPRF/HybridLemmas.lean:61`);
    - Gate 29: `hj` re-proved `OneWay.uexp_const` (`OneWayFunctions/Basic.lean:69`; G29-01), and `firstBit_of_pos`
      re-proved `LamportFill.headD_drop_ofFn` (`Authentication/Signatures/Lamport/MachineSpec.lean:195`, outside
      your order; being promoted to a shared list layer, ruling G29-02).

    Before writing any advantage, expectation, uniform-projection, point-probability, push-forward or list-window
    lemma, search for `uprob_*` (`uprob_comp_equiv`, `uprob_prod`, `uprob_fst`, `uprob_exists_le`, `uprob_const`,
    `uprob_comp_eq_sum_map`, `uprob_eq_one_div_card`), `uexp_*` (`uexp_const`, `abs_uexp_sub_le_uprob`),
    `prfAdv_*` (`prfAdv_eq_expect`, `prfAdv_congr_equiv`), `acceptProb_*`, `distAdv_comp`, `pushesUniform_*`,
    `uprob_not_injective_le`, and for lists `ofFn_drop_take` (`Asymptotic/CollectionsHelpers.lean:210`),
    `take_ofFn_castLE` (`Asymptotic/ReductionSupport.lean:288`), `take_drop_ofFn_blocks`, `headD_drop_ofFn`,
    `zipWith_xor_*` (`HardcoreBit.zipWith_xor_ofFn_add`, the `MultiMsg.zipWith_xor_*` family), `encodeList_eq_flatMap`
    and Mathlib's `List.take_append_of_le_length`, `List.drop_append_of_le_length`, `List.ofFn_*`. Use
    `MultiMsg.encodeList_eq_flatMap` (public, D4); do not add a fourth copy (DL-46).
  - **Private lemmas.** Never copy a private lemma silently. If you need one, re-derive it from published readers,
    keep its statement general, and disclose it. The relabelling of *The import direction* is the one expected case.
  - **Disclose every overlap.** `REPORT.md` has a section **`## Overlap and reuse`**. For every new declaration that
    restates, specializes or re-proves existing material (public or private, TCSlib or Mathlib), give its nearest
    relative (`path:line`), the relation, and why it is not reused. Disclose inline re-proofs inside a proof (`have`
    blocks) the same way. List the searches you ran.
  - **Why.** Undisclosed duplication is a freeze violation, not debt. The majors that held Gates 23, 24 and 29 were
    undisclosed duplicates (G23-01, a private copy of `length_le_length_encodeLog`; G24-01, `inputWord_take`, which
    re-proves the public `take_ofFn_castLE`; G29-01 and G29-02 above), and so was prf-mac F-01.
  - **Nearest relatives here:**
    - the frozen private relabelling helpers of `SpecialEncryptionMulti.lean` (*The import direction*) and
      `prfScheme_coinsEquiv` (`Encryption/PrivateKey/FromPRF.lean`) for scheme coin relabellings;
    - D1–D4 themselves: do not rebuild a machine, a hybrid or a collision bound; `exists_oneQuery_nuppt` is the
      one-query machine, `exists_queryChainOut_nuppt` the chain;
    - `MultiMsg.blockMapFun`, `polyTimeComputable_blockMap`, `NMSim.chunkMap` for the block parser;
    - `Equiv.piEquivPiSubtypeProd`, `Equiv.sumArrowEquivProdArrow` and the `uprob` product lemmas for the marginals;
      `HardcoreBit.pushesUniform_restrict` for restrictions of uniform functions;
    - `sliceEnc_append_left/_right` for the two layers of `nestedSpecial`.
- **Docstrings and sketches.** The last batches' landing edits were mostly LE-doc (cca2-ett: 94 formulas and 15
  sketches; dl-crh: 59 formulas; lamport: 188 formulas and 7 sketches; learning: 17 formulas; prf-long: 3) and
  LE-width. Do these yourself:
  - every new public declaration has a docstring that states its formula: the equation or inequality, with its
    arguments in the Lean order, and a source tag where it comes from the source (`[PS10, §6.2.2, Algorithm 157.2]`,
    `[PS10, §6.2.3, Claim 159.a]`, `[PS10, Theorem 99.2, with slices]`);
  - every proof of 15 lines or more carries a `**Proof sketch.**` paragraph, and long proofs get step comments
    (policy §3); each target's sketch is rewritten to describe the delivered proof;
  - a new public `def` lands with its `_eq`, `_iff` or `simps` readers (lint check 8), and a new public `abbrev` with
    an `_eq` or `_iff` lemma;
  - add no `@[simp]`.
- **Rule 10.**
  - Use only published readers for other files' definitions, including generated matchers and projections: for
    example `spEncStr` through `spEncStr_eq`, `spDecStr` through `spDecStr_eq`, `sliceEnc` through `sliceEnc_eq`,
    `Good` through `good_iff`, `WrongKeyBot` through `wrongKeyBot_iff`, `nestedSpecial` through its `simps` readers,
    `yaoSeed` through `yaoSeed_fst`/`_snd_fst`/`_snd_snd`, `readBits` through `readBits_apply`, `xorShift` through
    `xorShift_apply`, `prfEncRealOut` through `prfEncRealOut_apply`, `encodeTupleOut` through its two readers.
  - Each owned file and each helper module counts as foreign to the others; inside one owned file its own
    definitions may be read directly.
  - **Notation, never sealed:**
    - `PolyExpr.eval` (Q1);
    - reducible abbreviations (2026-10-26; for example `GarbleSeed`, `QueryImpl`, `OracleSpec.add`, `glNeed`);
    - **projection coercions:** a `CoeFun`/`Coe` instance whose body is a structure projection, such as
      `FinDist`'s `⟨FinDist.prob⟩` (Seyoon's ruling, 2026-11-14).

    The coe-variant seals are canonical. Run the strict variant as well, and attribute each difference.

## Checks and report

- **Bootstrap.**
  - Bootstrap from `order.txt` (166 modules) and the narrow `roots.txt` (71), following the addendum.
  - The order is the upstream closure of the modules downstream of the five owned files (root `TCSlib` excluded),
    and of the modules your helpers may import: the `FromPRF` facade (D2–D4 and `HybridLemmas`),
    `NonMalleability/Simulation/Generic` (`NMSim.chunkMap`) and `Games/Efficiency`. It contains `YaoReal` and the
    `SecureComputation` facade.
  - Check one module per `scripts/lean_check_tree.sh` call, with one Lean process per olean tree.
  - Never run `lake build` or an unfiltered cache get. Run Python as `python3 -I`.
  - Insert helper modules before their consumers.
- **Sweep.**
  - Recheck the five owned files and every helper, then sweep the supplied order with 0 errors.
  - Compare the `sorry` warnings with `base-sorries.txt` (32 declarations in 15 modules). The only
    change must be the removal of the seven targets (25 in 11 modules: `Yao.lean` keeps
    `yaoHybrid_polyTime` and `yaoHybrid_simulators`).
  - **Name-clash scan.** No new public or private name may already be declared anywhere in `TCSlib/` at the issue
    base, with namespaces resolved; private names count (the frozen private helpers of `SpecialEncryptionMulti.lean`
    in particular). Deliver the script and its output under `evidence/clash/`.
- **Axioms.**
  - Print the axioms of the seven targets, of the B2 lemma and of every stored constant of the changed and new files.
    Expect only `propext`, `Classical.choice` and `Quot.sound`.
  - Print, at base and final, the axioms of `garbling_good_whp` (it must become standard-only),
    `specialScheme_multiMessageSecure_of_joint`, `yaoHybrid_hbcSecure` and `yaoProtocol_hbcSecure`. The last two keep
    `sorryAx` through admissions outside this unit; say which.
- **Headers.** The check of *The frozen-statement rule*, with its control.
- **Rule 10 evidence.**
  - Run whole-file seals A and B of every changed or new file over its full TCSlib import closure, at base and final.
  - Run both the **strict** and the **coe** variant (projection coercions sealed, or treated as notation). Report
    every failing declaration in each.
  - Add paired controls that pass unsealed and fail sealed, each sealed negative failing exactly once.
  - Run the explicit-unfold scan.
  - Report the seals with `PolyExpr.eval` both excluded as notation and sealed, and attribute every seal-B failure by
    reading its raw log; do not summarize new B failures as "where the base fails" (Gate 31).
  - **Error counts (G26-N1), both forms.** Your runner must count both diagnostic forms, `error:` and `error(…)`,
    for example with `^\S+\.lean:\d+:\d+: error[:(]`, in every seal, control, sweep and probe log. Keep every raw log.
- **Lint.**
  - Run `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography --check8b` at base and at final.
  - The baseline at the issue base is **92 FAIL / 101 WARN**, re-run by the maintainer at `fbd37f44`.
  - Diff the line sets, not only the counts. There must be no new FAIL line, and no new WARN line except one you
    disclose and justify.
- **Report.** `REPORT.md` gives:
  - the base, and the status of each target;
  - the changed and new files, with lines at base and final, and the sketch edits;
  - the new declarations with their final signatures, the B2 lemma in full;
  - **Gate 27 hand-off** (each obligation mapped to declarations);
  - **Overlap and reuse**;
  - **Scope requests** (none, or each with Seyoon's answer);
  - the promotion and reader requests;
  - the evidence, with its manifest.

### Evidence completeness

Gate 20 held a delivery for omitted raw evidence (G20-01).
- Every file that `evidence/SHA256SUMS` names must be delivered. That includes:
  - seal and control sources, manifests and request records;
  - the header-check script, its output and its control, and the name-clash scan;
  - every raw log and `results.jsonl`;
  - the probe sources and the tools used.
- If the evidence is too large for one commit, deliver it in several commits, or as numbered ZIP parts, each part
  with an entry list. Do not leave anything out for size.
- Check before delivery that the delivered paths are exactly the manifest's (top level and `evidence/`), with no
  leading `./`.

The maintainer checks `TCSlib` and `audits/pass-shelat/Checks` on the full-library tree at landing, after #315
merges, on the then records tip (which includes #314).

**Ready to dispatch**
