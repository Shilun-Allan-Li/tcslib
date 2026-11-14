# Secure-computation admissions: analysis and proposed unit split

Read-only analysis. Branch `cryptography/pass-shelat-ch2-4` at
`58a061c98ef07e50a57f2a1a2d24485d24aac803` (fetched 2026-11-14; local = origin). No Lean was run,
nothing was staged, committed or pushed. Line counts and estimates come from reading the source.
The sizes are estimates, not measurements.

Source: `Pass–Shelat.pdf` at the root of the records branch (book page = PDF page − 12). Pages
156–164 were read (Alg 157.2, §6.2.3, Prot 160.4, Prop 161.5, Prot 162.6, Thm 163.7). The
"Claim 157.a" and "Claim 159.a" labels are the inventory's names for unnumbered claims in the
text of §6.2.2–6.2.3.

## 0. Census and corrections to the brief

**Admissions: 13 `sorry`s in 6 files.** The brief lists 13 declarations, and all 13 are confirmed.

| File | Lines | Admitted |
|---|---|---|
| `ObliviousTransfer.lean` | 671 | `otProtocol_simulators` (:639), `otProtocol_polyTime` (:656) |
| `SpecialEncryptionSecurity.lean` | 157 | `specialScheme_multiMessageSecure` (:115), `spDecStr_wrongKey` (:137), `specialScheme_wrongKey` (:155) |
| `Garbling.lean` | 427 | `uprob_not_good_le` (:425) |
| `GarblingSecurity.lean` | 87 | `nestedSpecial_wrongKeyBot` (:69) |
| `Yao.lean` | 942 | `yaoSeed_good_whp` (:820), `yaoHybrid_polyTime` (:843), `yaoHybrid_simulators` (:918) |
| `ComposeSecurity.lean` | 382 | `composeP_efficient` (:296), `composeV_efficient` (:305), `hbcSecure_compose` (:378) |

**`YaoReal.lean` has no admission.** Its only "sorry" match is module-docstring prose at line 43
("resting on their `sorry`s"). `yaoProtocol_hbcSecure` is a closed term built from
`hbcSecure_compose`, `yaoHybrid_hbcSecure` and `otProtocol_hbcSecure`.

**G3-8 is not pending.** It was ruled (A) by the user on 2026-11-05 (decision log row 268; QUEUE.md
:127, "ruled (A)"). It was applied in prong B commit `587843c76f95f10056c9ddc9174da9dc8fba8b54`
(row 272). `EnhancedHardCore` is already a hypothesis of the frozen `otProtocol_simulators`,
`otProtocol_hbcSecure` and `yaoProtocol_hbcSecure`. Gate 06B closed PASS (row 467), and the
internal review `maintainer/gate06-integration-2026-11-06/review-B.md` confirms the hypothesis is
still necessary. So G3-8 does not block OT. One residual point concerns the Implications layer
only: no collection in the library is proved to have an `EnhancedHardCore` predicate. Its only
consumers are `ObliviousTransfer.lean` and `YaoReal.lean`. That limits how the real Yao theorem
can be used, not whether it can be proved.

**Leaf admissions.** No other declaration's code uses `specialScheme_multiMessageSecure`,
`specialScheme_wrongKey` or `yaoSeed_good_whp`. The proved `garbling_good_whp` is also unused.
`yaoSeed_good_whp` appears only in the sketch of `yaoHybrid_simulators`.

## 1. Dependency graph

**Import graph** (within `SecureComputation/`):

```
Defs ─┬─ ObliviousTransfer (+ Asymptotic/Collections) ─────────────┐
      └─ Hybrid ─┬─ Compose ─ ComposePhases ─ ComposeSecurity ─────┤
                 └──────────────────────────┐                      ├─ YaoReal
SpecialEncryption ─┬─ SpecialEncryptionSecurity (+FromPRG, GGM) ─┐ │
Garbling ──────────┴─ GarblingSpecial ─────── GarblingSecurity ──┴─ Yao
```

No module outside `SecureComputation/` imports these files, apart from the facade
`SecureComputation.lean`.

**Proof-route graph.** `→` means "is used by the proof of".

- `otProtocol_polyTime`, `otProtocol_simulators` → `otProtocol_hbcSecure` → `yaoProtocol_hbcSecure`
- `composeP_efficient`, `composeV_efficient` → `polyTime_compose` → (sketch) `hbcSecure_compose` → `yaoProtocol_hbcSecure`
- `spDecStr_wrongKey` → `nestedSpecial_wrongKeyBot` → `garbling_good_whp` (proved, unused)
- `spDecStr_wrongKey` → `specialScheme_wrongKey` (leaf; sketch: reduces to `ℓ = n`)
- `uprob_not_good_le` → `garbling_good_whp`
- `nestedSpecial_wrongKeyBot` + (a generalized) `uprob_not_good_le` → `yaoSeed_good_whp` (sketch)
- `yaoSeed_good_whp` → `yaoHybrid_simulators` (sketch: steps 1 and 3, `Bad`) → `yaoHybrid_hbcSecure`
- `yaoHybrid_polyTime` → `yaoHybrid_hbcSecure`
- `specialScheme_multiMessageSecure` → **nothing as frozen**. The simulators' step 3 needs a
  joint, length-generic variant that is not yet stated (§3, B1).

**Does `hbcSecure_compose` need Yao or OT?** No. It is generic in `G`, `F`, `H` and `ρ`, and it
imports only `ComposePhases`. Yao and OT meet only in `YaoReal`. The OT file is independent of
every other admission, on both the import graph and the proof route.

## 2. Per-declaration analysis

Size: S < 300 lines, M 300–1000, L > 1000 (proof plus the helpers it needs).

### 2.1 `otProtocol_polyTime` (`ObliviousTransfer.lean`:656)

1. **Statement.** `otFunctionality.PolyTime (otProtocol T H)` given `hH : PolyTimeComputable H`:
   both strategies are `Strategy.Efficient`, and the messages of honest runs are bounded by a
   polynomial. Ref.: [PS10, Def 155.1] efficiency clause (ruling of 2026-11-05), for Prot 160.4.
2. **Dependencies.** None among the admissions. Used by `otProtocol_hbcSecure`.
3. **Well-posed.** Yes. `Strategy.Efficient` quantifies over all `x z r hist`. The next-message
   functions branch only on `hist.length`, and they use `T.gen`/`T.sample`/`T.inv` (uniform
   NUPPTs, so `runAtL` on arbitrary tapes is poly-time), `T.eval` (`eval_poly` is a field of
   `Collection`), `H` and `List.replicate (inv.coins.eval n)`. The message bound covers the index
   (at most the length of Gen's output), two sampler/eval outputs, two one-bit masks and empty
   fillers.
4. **Infrastructure.** Mostly present.
   - Present: `NUPPT.ofPolyTimeUniform`, `polyTimeComputable_output`, `polyTimeComputable_layout`,
     `polyTimeComputable_ite`, `pairXor`, `polyTimeComputable_coinSeg` (same file).
   - History readers over `encodeMsgs` exist in the GI efficiency work (`ZeroKnowledge/GraphIsomorphism/EfficiencyRep.lean`:
     `pairSndD_encodeMsgs`, `iterate_pairSndD_encodeMsgs`) and in `BinaryArith/Words` (`countW`).
   - Precedent: `giProver_efficient` and the other GI efficiency proofs, about 600 lines each.
   - Missing: a ready-made "length of the encoded history" reader in the OT file. The output-length
     bounds come from `PolyTimeComputable.output_length_le`.
5. **Size:** M (500–900).

### 2.2 `otProtocol_simulators` (`ObliviousTransfer.lean`:639)

1. **Statement.** For `hT : T.OneWay` and `hEHC : EnhancedHardCore T h` (with `henc`, `hH`):
   `∀ D, ∃ ε negligible, ∀ n a b`, `D`'s advantage is at most `ε n` for Alice's
   real/ideal pair (`otSimA`) and for Bob's (`otSimB`). Ref.: [PS10, Prop 161.5]. `S_B` is the
   source's exercise; the enhanced predicate follows [Gol04, App. C.1, §7.3.2].
2. **Dependencies.** None among the admissions. Uses the proved `otProtocol_outV`/`outP`.
3. **Well-posed.** Yes, as frozen. Checked:
   - **Alice.** Her tape coincides with `coinSeg 0 gen.coins`, and `simIdx` reads the same coins.
     Real `y_b = encD(perm x)` for `x` close to uniform; `SampleClose` holds *per generated index*,
     and `perm` is a bijection. `y_{1−b}` is canonical (`SamplerCanonical`). So both coordinates
     are δ-close to `encD(U)`, and the advantage is at most 2δ.
   - **Bob.** `otSimZb` uses exactly Bob's first coin block, and `H⟨i,w⟩ = [h x]` by
     `apply_of_decD`. The only difference is `z_{1−b}`. The predictor gets `⟨i, s'⟩` (the sampler
     coins of `y_{1−b}`), which is what `EnhancedHardCore` allows. Its advice is the worst of the 8
     triples `(b, a₀, a₁)`.
4. **Infrastructure.**
   - Present: `distAdv_le_of_statClose`, `StatClose` (`Asymptotic/Sampling`);
     `exists_pkPredictor` (`PublicKey/Trapdoor.lean`:337, but stated for `f : α ≃ α` inputs, so it
     needs an adapted copy for `⟨i, coins⟩` challenges); `NUPPT.exists_comp`, `exists_withAdvice`,
     `exists_split`; `uprob_prod`, `uprob_comp_equiv`; `Collection.sample_spec`, `inv_spec`,
     `f_perm`, `apply_of_decD`.
   - Missing: the view equations of the real execution (5 moves) for `viewP`/`viewV`, which follow
     the pattern of `otProtocol_outV`; the coin-space equivalences between real and simulated tapes.
5. **Size:** L (1500–2500).

### 2.3 `spDecStr_wrongKey` (`SpecialEncryptionSecurity.lean`:137)

1. **Statement.** Take any polynomial `ℓ`, a PRF `G'` with `n + ℓ(n)`-bit outputs and an evaluator
   `E'` on canonical inputs. Then `∃ ε` negligible such that for all `n` and every `ℓ(n)`-bit `m`,
   `1 − ε n < Pr_{k,k',r}[spDecStr E' n ℓ k' (spEncStr E' k m r) = none]`. Ref.: [PS10, §6.2.2],
   "the extra property" (Claim 157.a (ii)).
2. **Dependencies.** None. Used by `nestedSpecial_wrongKeyBot`, and by `specialScheme_wrongKey`
   per its sketch.
3. **Well-posed.** Yes.
   - The length guard always passes: `|p| = n + ℓ` by `hGE'`, so `|c₂| = n + ℓ`. Hence `none`
     holds exactly when `f_k(r)_{<n} ≠ f_{k'}(r)_{<n}`.
   - The one-query distinguisher has `Pr = 2^{-n}` against a random function.
   - `E'` has no `PolyTimeComputable` hypothesis, but the distinguisher can use the evaluator from
     `hG'.easy`, which agrees with `E'` on canonical inputs.
   - The strict `<` is met by adding `2^{-n}` to `ε`.
4. **Infrastructure.**
   - `PRFOut.pseudorandom` is an `OracleEnsemble.Indist` at a general `ℓ₂`, so it applies directly
     to `D.toOracleAdversary n n ℓ₂ q`.
   - **Missing:** a one-query next-query machine for an `ℓ₂`-output oracle, and an `ℓ₂` analogue of
     `PRF.negligible_prfAdv`. `PRFOut` has no consumer outside `SecureComputation`. The existing
     `MultiMsg.exists_queryChain_nuppt` is specific to `n`-bit outputs.
5. **Size:** M (400–700).

### 2.4 `specialScheme_wrongKey` (`SpecialEncryptionSecurity.lean`:155)

1. **Statement.** The same property for the `PrivateKeyScheme` (n-bit messages): `decodeFin n` of
   `Dec_{k'}(Enc_k(m))` is `none` except with negligible probability. Ref.: Claim 157.a (ii).
2. **Dependencies.** `spDecStr_wrongKey` at `ℓ = .var` (`G' = G`; the `Fin` types agree).
3. **Well-posed.** Yes. `runAt_spDec` returns `1^{n+1}` on `⊥`, which `decodeFin n` rejects. A
   `some` output has `n` bits. The coin space has an extra `dec.Coins` factor of size 1, removed
   by `uprob_comp_equiv`/`uprob_fst`.
4. **Infrastructure.** Present: `runAt_coinKey`, `runAt_spEnc`, `runAt_spDec`, `decodeFin_ofFn`.
5. **Size:** S (100–250).

### 2.5 `specialScheme_multiMessageSecure` (`SpecialEncryptionSecurity.lean`:115)

1. **Statement.** `(specialScheme G E hE hGE).MultiMessageSecure` for a length-doubling `PRFOut`
   `G`. Ref.: Claim 157.a (i), "easy to modify Construction 99.1"; [PS10, Def 93.1, Thm 99.2].
2. **Dependencies.** None. **No consumer as frozen.**
3. **Well-posed.** Yes. It is Thm 99.2 with a `2n`-bit pad and the message padded by `0^n`.
4. **Infrastructure.** This is the main gap.
   - The proof of `prfScheme_multiMessageSecure` (`Encryption/PrivateKey/FromPRF*.lean`, about
     1500 lines) is typed throughout for `F : … → (Fin n → Bool) → (Fin n → Bool)`
     (`prfEncReal`, `multiMsgAdv`, `distAdv_prfEncReal_le`, `exists_queryChain_nuppt`,
     `PRF.negligible_prfAdv`).
   - Generalizing to `ℓ₂`-bit outputs means editing those frozen files or copying them, which is
     duplication debt for the ledger.
   - The collision lemmas (`MultiMsg.negligible_choose_div_two_pow`) are reusable.
5. **Size:** L (1000–1800). If the joint lemma of B1 is proved generically, this declaration is a
   short corollary (S) of it.

### 2.6 `uprob_not_good_le` (`Garbling.lean`:425)

1. **Statement.** Assume `M.DecCorrect`, `M.WrongKeyBot δ` and `Cc.IsFaninTwo`. Then
   `Pr_{s ← GarbleSeed}[¬Good] ≤ 12 · |gates| · δ`. Ref.: Claim 159.a, probabilistic part
   ([PS10, §6.2.3], "all but one row will evaluate to ⊥"), weakened to first-success correctness.
2. **Dependencies.** None. Used by `garbling_good_whp`. Its argument is reused by `yaoSeed_good_whp`.
3. **Well-posed.** Yes.
   - `IsFaninTwo` gives `args.Nodup` and `|args| ≤ 2`. `args_lt` puts the gate's own vertex
     `n + i` outside its arguments, so the plaintext key is independent of the argument keys.
     `WrongKeyBot` is `∀ o`, so averaging over the plaintext is enough.
   - There are at most 4 × 3 = 12 ordered pairs `(a, a'')` with `a ≠ a''`. Constant gates add no
     event.
   - Failure is contained in the event "some other row decrypts", whatever the row order.
4. **Infrastructure.** Present: `uprob_exists_le` (union bound), `uprob_mono`, `uprob_prod`,
   `uprob_comp_equiv`, `uprob_fst`. Missing: the marginal of `Fin size → Bool → K` restricted to
   a `Nodup` argument list, through an equivalence such as `Equiv.piEquivPiSubtypeProd`, plus the
   bookkeeping for the `findSome?` failure event.
5. **Size:** M (400–700). This is the "contained garbling bound" of the decision-log rows
   480/481, with a 3-module local closure.

### 2.7 `nestedSpecial_wrongKeyBot` (`GarblingSecurity.lean`:69)

1. **Statement.** Given `hG₁` (length-doubling) and `hG₂` (`n + innerLen`):
   `∃ δ` negligible with `∀ n, (nestedSpecial E₁ E₂ n).WrongKeyBot (δ n)`. Ref.: Claim 157.a (ii)
   for the double encryption of [PS10, §6.2.3].
2. **Dependencies.** `spDecStr_wrongKey`, at `ℓ = .var` (with `G₁`) and at `ℓ = innerLen` (with `G₂`).
   Used by `garbling_good_whp`, and by `yaoSeed_good_whp` per its sketch.
3. **Well-posed.** Yes. The cases are `len = 1`, then `len = 2` where the first key differs (the
   outer layer fails), then `len = 2` where the first key agrees and the second differs.
   - In the last case the outer layer opens correctly: `spDecStr_spEncStr` applies, since the
     inner ciphertext has `innerLen` bits by `length_spEncStr`.
   - The inner message is random but independent of the outer keys, so Fubini over the remaining
     coordinates finishes the case.
   - `δ = ε₁ + ε₂`, negligible by `Negligible.add`.
4. **Infrastructure.** Present: `nestedSpecial_enc/dec` simps readers, `spDecStr_spEncStr`,
   `length_spEncStr`, `uprob_prod`. Missing: the relabelling `(Fin len → Bool → K) × ρ` ≃ (the
   two used keys × the rest).
5. **Size:** M (300–500).

### 2.8 `yaoSeed_good_whp` (`Yao.lean`:820)

1. **Statement.** On Alice's uniform `yaoCoins(n)` coins, the event "`yaoSeed` is not `Good`, or
   some output vertex has two equal keys" has probability at most `δ n`, for a negligible `δ`.
   Ref.: Claim 159.a, applied to Prot 162.6's seed.
2. **Dependencies.** `nestedSpecial_wrongKeyBot`, and the argument of `uprob_not_good_le`.
   - **`uprob_not_good_le` cannot be applied as frozen.** It is about a uniform `GarbleSeed`,
     whose third component is a uniform `Equiv.Perm`, but `yaoSeed` uses XOR shifts. Its sketch
     says "the argument applies".
   - The garbling proof should therefore publish a stronger form: the bound for every fixed
     row-permutation family, or for every seed distribution whose keys and row coins are uniform.
     `uprob_not_good_le` then follows by averaging, and `yaoSeed_good_whp` by push-forward.
3. **Well-posed.** Yes.
   - The blocks are disjoint and fit in `yaoCoins = 10Sn + 2S`. Keys sit at `(b·S + v)·n` with
     `v < size ≤ S`, rows at `2Sn + (4i + idx a)·2n` with `idx a < 4` (`assignIdx` is injective
     for `len ≤ 2`), and shifts at `10Sn + 2i`.
   - `|gates| ≤ size ≤ S`.
   - At `n = 0` the keys are trivial, but `δ(0)` is unconstrained.
   - `δ = 12·S·δ₀ + outLen·2^{-n}`, negligible.
4. **Infrastructure.** Present: `yaoSeed_fst/snd_fst/snd_snd`, `keyAt_yaoSeed`, `readBits_apply`,
   `uprob_exists_le`. Missing: the push-forward of the uniform measure through disjoint
   `readBits` blocks, and the generalized garbling bound described in item 2.
5. **Size:** M (500–900).

### 2.9 `yaoHybrid_polyTime` (`Yao.lean`:843)

1. **Statement.** `(yaoHybrid Y E₁ E₂).PolyTime (yaoFunctionality Y)` from `hE₁` and `hE₂`.
   This is the efficiency clause of `HybridProtocol.PolyTime`: efficient `main` strategies,
   poly-time call inputs and a message bound for **any** answers. Ref.: [PS10, Def 155.1] and the
   ruling of 2026-11-05.
2. **Dependencies.** None among the admissions.
3. **Well-posed.** Yes.
   - A row has at most `7n + 4` bits whatever `E` returns (`take`/`zipWith` cap the pads), so the
     bound does not depend on the answers.
   - Alice's `garbledTable` uses the noncomputable `Finset.univ.toList`. For `len ≤ 2` this is a
     fixed finite table, so `PolyTimeComputable` still holds: prove it for an arbitrary constant
     enumeration. The proof needs care here.
4. **Infrastructure.** Largely missing.
   - Missing: a poly-time decoder of `encodeCircuit`/`DAGCircuit.encode`. `Uniform.lean` has only
     the encoder and injectivity, and the CVAL machine (`CircuitEval*`, about 2260 lines) is a
     hand-built TM for Boolean gates that cannot be reused.
   - Missing: a poly-time `runWith` with a data-dependent gate function (`evalGate` with
     decryption), and the garbling function from coins as `PolyTimeComputable`.
   - Present building blocks: `polyTimeComputable_stateFind`/`iterate`/`blockMap`,
     `BinArith` `mapW`/`zipWithW`/`countW`, `polyTimeComputable_spEncFun`/`spDecFun`, and the GI
     `EfficiencyRep` history loops.
   - The same infrastructure is needed for `S_B` in `yaoHybrid_simulators`.
5. **Size:** L (1500–2500).

### 2.10 `yaoHybrid_simulators` (`Yao.lean`:918)

1. **Statement.** Assume `hE₁`, `hE₂`, `hG₁`, `hG₂` and the joint `hG₁₂`. Then `∃ SA SB`,
   `∀ D ∃ ε` negligible, both advantages are at most `ε n` uniformly in `x, y`. Ref.:
   [PS10, Thm 163.7] in the OT-hybrid model; the one-active-key simulator of [LP09].
2. **Dependencies.**
   - `yaoSeed_good_whp` (the `Bad` event) and the proved `yaoHybrid_correct`.
   - Step 3's hybrid needs multi-message security, under one inactive key `ι_u`, of the
     ciphertexts of **both** layers: the `G₂`-scheme with `(4n+2)`-bit messages where `u` is a
     first argument, and the `G₁`-scheme with `n`-bit messages where it is a second or only
     argument.
   - The frozen `specialScheme_multiMessageSecure` (`G` only, `n`-bit messages) does not give
     this. The docstring says so: "not yet stated in the library".
3. **Well-posed: yes, modulo B1.**
   - Alice's side is statistical: δ by `yaoSeed_good_whp`.
   - Bob's side:
     - the point-and-permute relabelling is a bijection of Alice's coins;
     - outputs are sinks (`outs_sink`), so the decoding pairs never reveal an encryption key;
     - Alice's keys and Bob's answers are active, so `ι_u` is only an encryption key.
   - The reductions are non-uniform: their advice is the worst `(x, y)`, the hybrid index, and
     the other randomness. The fixed-vector `MultiMessageSecure` bound is uniform in the messages.
   - No false statement found.
4. **Infrastructure.** Missing:
   - (a) the joint-key, length-generic multi-message lemma (B1);
   - (b) the poly-time garbling of 2.9 (for `S_B` and the reductions);
   - (c) the view equations of the two-move main phase, plus the hybrid-model sampler equations
     (`yaoMain_outV`/`outP` exist);
   - (d) a gate-indexed hybrid with an advice-selected index. `abs_sub_le_sum_hybrids` and
     `exists_hybrid_gap` exist.
5. **Size:** L, likely the largest (3000–5000, plus about 1000–1500 for (a)).

### 2.11 `composeP_efficient` / `composeV_efficient` (`ComposeSecurity.lean`:296/305)

1. **Statement.** Assume `hH : H.PolyTime F` and `hρ : G.PolyTime ρ`. Then `(H.composeP ρ).Efficient`,
   and symmetrically `(H.composeV ρ).Efficient`. Ref.: [Gol04, §7.3.1], efficiency of the
   protocol of Thm 7.3.3.
2. **Dependencies.** None. Used by `polyTime_compose` (proved), which the sketch of
   `hbcSecure_compose` uses for its efficiency clause.
3. **Well-posed.** Yes.
   - `composeP.next` (`Compose.lean`:344) branches on `|hist|` against `L·R`. It calls `runNextA`
     (one ρ-activation on a slot history cut from `hist`, with the run tape cut from `r`) or
     `main.P.next` on `⟨z, answersFromA⟩`.
   - `answersFromA` runs ρ's output function `L(n)` times. Each activation's input is at most the
     total input, so the time is `L(n)·poly`.
   - The call inputs are poly-time by the `callA`/`callB` clauses of `HybridProtocol.PolyTime`.
4. **Infrastructure.**
   - Present: `polyTimeComputable_blockMap` (fixed block size `b(|fst z|)`), `stateFind`/`iterate`,
     `exists_comp`/`exists_seq`, `Strategy.Efficient` readers, and `slotMsgs`/`runTape` readers
     in `Compose.lean`.
   - Missing: a "map a poly-time function over the `L(n)` run slots of a history" lemma (the slots
     are interleaved, not fixed-size blocks), and the extraction of a `PolyTimeComputable` function
     from `Strategy.Efficient` (`Computes.polyTimeComputable` exists for uniform NUPPTs).
5. **Size:** L for the pair (1000–1800). They are symmetric, so share the helpers.

### 2.12 `hbcSecure_compose` (`ComposeSecurity.lean`:378)

1. **Statement.** Assume `hM : ∀ n, 0 < H.main.rounds.eval n`, `H.HBCSecure F` and
   `HBCSecure ρ G`. Then `HBCSecure (H.compose ρ) F`. Ref.: [Gol04, Thm 7.3.3] (the numbering is
   "to be verified at audit"), with calls first. It is used unstated by [PS10, Thm 163.7].
2. **Dependencies.**
   - `composeP_efficient`/`composeV_efficient` through `polyTime_compose`, as statements only.
   - Not Yao, not OT.
3. **Well-posed: yes.**
   - **Output clause (step 2).** One non-uniform distinguisher with the worst inputs as advice
     tests the second component against `f_B(x*, y*)`. This gives
     `Pr[ρ-output ≠ ideal] ≤ ε₁`, uniformly, and is sound because `ε` precedes the inputs.
   - **Run hybrid (step 3).** The advice is the worst `i`, inputs, main tapes and ideal answers.
   - **`Φ` in step 4.** It recomputes the call inputs from `(x, r_main)`, which is poly-time by
     `H.PolyTime`, and runs `S_A^ρ`.
   - **Layout.** Real ρ-views have exact tape lengths, so `Φ`'s "cut to length" acts as the
     identity on them, and the end-hybrid matches exactly.
   - The worker's own `hM` counterexample is recorded in the docstring.
   - No false statement found.
4. **Infrastructure.**
   - Present: the phase lemmas in `ComposePhases.lean` (599 lines: `compose_exec_main`,
     `compose_viewP`, `compose_outV`, …), `compose_msg_bound`, `exists_runExec_eq_transcript`,
     `exists_hybrid_gap`, `abs_sub_le_sum_hybrids`, `uprob_exists_le`, and the NUPPT combinators.
   - Missing:
     - a NUPPT that runs a simulator `L(n)` times on blocks and assembles a view;
     - the statistical-switch argument "agree off a bad event";
     - the coin-space equivalence for the hybrid of run `i`;
     - `padFin` readback, which exists (`padFin_ofFn`).
5. **Size:** L (2000–3500).

## 3. Blockers and rulings

- **B1 (needed before the Yao simulators are dispatched): the joint multi-message lemma is not
  stated.** `yaoHybrid_simulators` cannot be proved from the frozen
  `specialScheme_multiMessageSecure`.
  - It needs a lemma of roughly this form: for a `PRFOut` family `G` and a list of encryption
    "slices" (pad offset and message length), many ciphertexts under one key, each from a slice
    of `G_k(r)`, are indistinguishable for any two message vectors. It is instantiated with
    `G₁ ‖ G₂` under `hG₁₂`.
  - Who states it is a design decision. Options, recommended first:
    - (A) the maintainer states it, sorried, in a small statement PR on the gate path, so that it
      is frozen. It is owned by U1 and consumed by U3. `specialScheme_multiMessageSecure` becomes
      a corollary.
    - (B) U3 states and proves it inside its own delivery, and U1 keeps the frozen
      `specialScheme_multiMessageSecure` only.
    - (C) U1 designs it as published API under a brief-level specification.
- **B2 (brief-level, no ruling): the garbling bound is too weak to reuse.** `uprob_not_good_le` as
  frozen is not reusable for `yaoSeed`'s XOR-shift seed. The U1 brief should require a published
  stronger lemma (every fixed permutation, or any seed law with uniform keys and coins), with
  `uprob_not_good_le` and `yaoSeed_good_whp` as corollaries. This is an addition, not a statement
  change.
- **B3 (likely ruling): duplication.** The `ℓ₂`-output PRF machinery duplicates `FromPRF/*` and
  `PRF.negligible_prfAdv` (n-bit only). Either accept it as recorded debt (a DL row, the precedent
  of DL-36/37/40) or generalize the frozen `FromPRF` files, which puts them outside the unit and
  needs a ruling. Recommended: accept as debt. Open a DL row at brief time. Consolidate later.
- **B4 (record only): G3-8 is closed.** See §0. The residual point, that no `EnhancedHardCore`
  instance exists, matters only to the Implications layer.
- **B5 (record only): Yao.lean size.** `Yao.lean` is at 942 lines. U1 edits one proof body and U3
  two large ones. Under the standing size rule a fill-owned file may pass 1000 lines and is never
  split, but helper modules (`Yao/…`) are better than growing the file.
- **No statement found false as frozen.** No missing hypothesis was found beyond B1, which is a
  missing *lemma* rather than a missing assumption: `hG₁₂` already supplies the hypothesis.

## 4. Proposed split (3 units, in dependency order)

Totals are rough: about 15–22k lines across the 13 admissions.

### U1 `sc-garble`: special encryption and garbling probability (wave 1)

- **Declarations (6).** `spDecStr_wrongKey`, `specialScheme_wrongKey`,
  `specialScheme_multiMessageSecure`, `nestedSpecial_wrongKeyBot`, `uprob_not_good_le`,
  `yaoSeed_good_whp`. Also the joint lemma of B1 under (A) or (C), and the stronger garbling
  lemma of B2.
- **Owns.** `SpecialEncryptionSecurity.lean`, `Garbling.lean`, `GarblingSecurity.lean`, and the
  body of `yaoSeed_good_whp` in `Yao.lean`. It may add new helper modules, for example
  `SecureComputation/SpecialEncryptionMulti.lean` and `SecureComputation/PRFOut.lean`.
- **Frozen.** Every statement; `SpecialEncryption.lean`, `GarblingSpecial.lean`, the rest of
  `Yao.lean`, `FromPRF*`, `Pseudorandom/*`.
- **Size.** About 3–5k (the multi-message lemma dominates).
- **Internal order.** `spDecStr_wrongKey` → `specialScheme_wrongKey`, `nestedSpecial_wrongKeyBot`;
  `uprob_not_good_le` (generalized) → `yaoSeed_good_whp`. The multi-message lemma is independent
  and can be checkpointed last.

### U2 `sc-ot-compose`: oblivious transfer and the composition theorem (wave 1, parallel to U1)

- **Declarations (5).** `otProtocol_polyTime`, `otProtocol_simulators`, `composeP_efficient`,
  `composeV_efficient`, `hbcSecure_compose`.
- **Owns.** `ObliviousTransfer.lean` and `ComposeSecurity.lean`, plus new helpers (for example
  `ObliviousTransfer/…`, `ComposeSecurity/…`).
- **Frozen.** `Defs.lean`, `Hybrid.lean`, `Compose.lean`, `ComposePhases.lean`, `YaoReal.lean`,
  `Asymptotic/Collections`, `PublicKey/Trapdoor`.
- **Size.** About 4–7k.
- **Structure.** Two independent halves on disjoint files, OT (about 2–3.4k) and composition
  (about 3–5k). Checkpoint per half. If a smaller job is wanted, U2 splits cleanly into U2a (OT)
  and U2b (compose) with no dependency between them, which gives four units.
- **Shared infrastructure.** The two efficiency targets share history readers with
  `otProtocol_polyTime`. This is one reason to keep them together.

### U3 `sc-yao`: Yao in the OT-hybrid model (wave 2)

- **Declarations (2).** `yaoHybrid_polyTime`, `yaoHybrid_simulators`.
- **Owns.** `Yao.lean` (these two bodies) and new `Yao/…` helper modules: a circuit decoder,
  poly-time garbling and garbled evaluation, the simulator `S_B`, and the hybrid.
- **Frozen.** Everything else, including U1's published lemmas.
- **Size.** About 5–8k. This is the long pole.
- **Wait condition.**
  - Under B1(A), U3 can start once the statement PR merges, using U1's sorried statements.
    However, it shares `Yao.lean` with U1's `yaoSeed_good_whp`, so the two land in sequence: U1,
    then U3 rebased.
  - Under B1(B), U3 can start now in parallel and lands after U1.
  - The simplest safe order is to dispatch U3 after U1 merges.

**Parallelism summary.**
- U1 ∥ U2 now.
- U3 after the B1 statement, or after U1's merge. U3 may run in parallel with U2.
- `YaoReal.lean` needs no unit: `yaoProtocol_hbcSecure` becomes free of admissions when U1, U2
  and U3 have all landed.

## 5. Recommendation

- **Dispatch U2 now.** No blocker. G3-8 is closed.
- **Dispatch U1 now if B1 is decided as (B).** Otherwise, first take the B1 ruling, recommended
  (A): a maintainer statement PR for the joint multi-message lemma, plus the brief-level B2
  requirement. Take the B3 debt ruling at the same time.
- **Hold U3** until B1 is settled and U1 has landed (or at least until the B1 statement is
  frozen).
