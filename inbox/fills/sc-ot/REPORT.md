# Fill sc-ot — final (`otProtocol_polyTime` and `otProtocol_simulators`)

**Unit** `sc-ot` · **Worker** Claude · **Issue base** `107f1e8c218733eac12d6b9bee6fece441271317`
(`cryptography/pass-shelat-ch2-4`) · **Proof branch** `fill/sc-ot` (local), three commits:
`fc7d0366067738271851488a8d1d7d7240cb70f1` (checkpoint 1), `a643e566b57d450d4abdad7b8484215385179233`
(checkpoint 2), `e2c6f1a8f9e16d830e07f9cd3b1158553edb5500` (final) · **Lean** 4.25.0, Mathlib at the base's manifest.

## Target status

| Target | Status |
|---|---|
| `otProtocol_polyTime` | **proved** (`propext`, `Classical.choice`, `Quot.sound`) |
| `otProtocol_simulators` | **proved** (`propext`, `Classical.choice`, `Quot.sound`) |

Both statements are unchanged. Their consumer `otProtocol_hbcSecure` (unchanged) now depends on
the standard axioms only (`logs/final-axioms.log`). The sorry census of the final sweep is
`base-sorries.txt` minus exactly these two declarations (29 declarations in 13 modules).

## 1. Environment (addendum v1)

- **Preflight** (`evidence/logs/preflight.log`): 4 CPUs; cgroup v1 limit unlimited, so the
  headroom is `MemAvailable` = 16503980032 B = 15.37 GiB (floor 4 GiB); the clone's filesystem
  (ext4, `/dev/vda`) had 16496836608 B = 15.36 GiB free (floor 12 GiB): `PREFLIGHT PASS`. To get
  there the git worktree of this host's delivered `canonizer` fill (`/workspace/canon`, branch
  kept) was removed. No dependency tree was copied or moved.
- **Clone:** a new worktree `/workspace/scot` of the local repository, branch `fill/sc-ot` at the
  issue base; its sources match `SOURCE-SHA256SUMS` (159 files, `source-sha256.log`).
- **Cache:** the store (`~/.cache/mathlib`, `cache-store.log`) held 2403 archives (120576651 B)
  from this host's earlier fills of this campaign (not downloaded by this session). The narrowed
  `lake exe cache get` for the 74 roots (`mathlib-roots.txt`, the same list as `roots.txt`)
  reported "No files to download", decompressed 2082 files and exited 0 (`cache-get.log`). No
  zero-size olean among 2091 (`zero-size-oleans.log`); the probe importing
  `Mathlib.Algebra.BigOperators.Field` elaborates (`cache-probe.log`, `probes/CacheProbe.lean`).
- **Packages** (`packages-check.log`): `RESULT: all present packages match the manifest`
  (`doc-gen4`, `UnicodeBasic`, `BibtexQuery`, `MD4Lean` ABSENT; no module of the order imports
  them).
- **Bootstrap** (`bootstrap.log`): the 159 modules of `order.txt`, one `scripts/lean_check_tree.sh`
  call each (through `tools/check.sh`), in order: 159/159 status 0, no error; maximum RSS
  2726572 KiB. Sorry census = `base-sorries.txt` (31 declarations in 14 modules;
  `census-bootstrap.txt`, `census-bootstrap-vs-base.diff`: identical). The whole order was built
  before any check of the owned file.
- **Host restarts.** The VM restarted several times during the session (uptime resets). Every
  long run is resumable and was resumed from its last completed module or run; no log was moved
  or edited. An interrupted run leaves a module header without its end line in the raw log, and is
  rerun in full.
  In particular: one seal run of checkpoint 1 (rerun), a scratch check between the checkpoints,
  and the final sweep once (at module 90, `Asymptotic/OneWayYao`, which has a header without an
  end line in `final-sweep.log` and was then rerun; 166 headers, 165 `status=0`).

## 2. The proof

The helper modules cannot import the owned file (it imports them). So they state every result
for **every protocol and every pair of machines of the shapes** of Protocol 160.4 and of `S_A`,
`S_B`, given by predicates that restate the owned definitions' bodies, and the owned file proves
that `otProtocol`, `otSimA` and `otSimB` have these shapes from its published readers:

```lean
theorem otProtocol_polyTime : otFunctionality.PolyTime (otProtocol T H) :=
  OT.polyTime_of_isOT T hH (otProtocol_isOT T H)

theorem otProtocol_simulators (hT : T.OneWay) (hEHC : EnhancedHardCore T h) : … :=
  OT.simulators_of_isOT T H hH henc (otProtocol_isOT T H) (otProtocol_outV T H henc)
    (otProtocol_outP T H) (otSimA_isSimA T) (otSimB_isSimB T hH) hT
    ((enhancedHardCore_iff T h).1 hEHC)
```

### 2.1 Shape (`ObliviousTransfer/Shape.lean`)

`OT.IsOT T H π`: `π.P.next = OT.senderNext T H`, `π.V.next = OT.receiverNext T H` (the bodies
of `otSender`, `otReceiver` with `otMask` = `OT.mask`, `otKnown`, `otRaw` expanded), coins
`coins_Gen` and `coins_Sample + coins_Sample`, five messages, Alice first. `otProtocol_isOT`
(owned) proves it from `otSender_next`, `otReceiver_next`, `otMask_eq`, `otKnown_eq`, `otRaw_eq`,
`otSender_coins`, `otReceiver_coins`, `otProtocol_rounds`, `otProtocol_verifierFirst`. The module
gives the messages on histories of length 0, 1, 2, the five moves of a prover-first execution
(`OT.exec_five`) and the transcript `([y, []], [i, z, []])` (`OT.transcriptWith_isOT`: the
five-message layout with its two empty fillers).

### 2.2 Checkpoint 1: `otProtocol_polyTime` (`ObliviousTransfer/Efficiency.lean`)

- Alice's raw function `OT.senderRaw` reads the case off the encoded history `w` by the emptiness
  tests `w = []`, `snd w = []` (`polyTimeComputable_isNil`, `polyTimeComputable_ite`): `Gen`'s
  index (`OT.genRaw`), the two masks (`OT.maskRaw`: the inverter on the all-`true` tape
  `polyTimeComputable_unaryPoly`, `H`, XOR), or `[]`. Bob's `OT.receiverRaw` adds a third test and
  uses the sampler on the two coin blocks (`polyTimeComputable_pairTakePoly`/`DropPoly`) and
  `eval_poly`. `OT.senderRaw_advInput`, `OT.receiverRaw_advInput`: on the raw input of an
  activation they compute the next messages for every history (cases `[]`, `[m]`, two, three or
  more messages). So `NUPPT.ofPolyTimeUniform` of them, with the parties' coin polynomials,
  witnesses `Strategy.Efficient` for both.
- Messages (`OT.exists_messages_le`): `|i| ≤ Q₁(n)` (`Gen`'s `runLenPoly`), samples `≤ Q₂(n)`
  (the sampler's `runLenPoly` at `Q₁`), the evaluation `≤ Q₃(n)` (`eval_poly`'s bound at
  `2Q₁ + 2 + Q₂`), masks one bit each: `B = Q₁ + (3(Q₂ + Q₃) + 2) + 5`.

### 2.3 Checkpoint 2: Alice's side (`ObliviousTransfer/Simulators.lean`, `ObliviousTransfer/ViewA.lean`)

- `OT.IsSimA`, `OT.IsSimB` restate `otSimAFun`, `otSimBFun` (with `coinSeg`, `simIdx`,
  `simSample`, `otSimZ`, `otSimZb`) as `OT.simAView`, `OT.simBView`; the owned file proves
  `otSimA_isSimA`, `otSimB_isSimB` from `otSimA_coins`, `runAt_otSimA`, `otSimB_coins`,
  `runAt_otSimB` and the simulator-function readers. The coin spaces: `OT.splitLen` (a tape of
  length `a + b` as two blocks), `OT.realCoins` (the real
  `ExecCoins ≃ Coins_Gen × (Coins_Sample × Coins_Sample)`), `OT.simACoins`, `OT.simBCoins`, with
  `_ofFn` readers; the simulated views on assembled tapes (`OT.simAView_layout`,
  `OT.simBView_layout`); the OT inputs as bits (`OT.inA2`, `OT.inB1`, `OT.ofFn_f_fst`,
  `OT.ofFn_f_snd`, from the published `otFunctionality_*` readers).
- `OT.realA_realCoins`, `OT.idealA_simACoins`: on `(r, s₁, s₂)` Alice's real and ideal samplers are
  `W r y` with `y = ⟨eval ⟨i, w₁⟩, w₂⟩` (`⟨w₂, eval ⟨i, w₁⟩⟩` if `b`) and `y = ⟨w₁, w₂⟩`,
  `w_j = Sample(i; s_j)`, `i = index n r`.
- `OT.statClose_eval_sample`: at every generated index `eval ⟨i, Sample⟩` is `2δ(n)`-close to
  `Sample` under `SampleClose δ` (`δ` to the uniform element mapped by `encD ∘ perm`, `0` from
  `perm`, `δ` back by canonical decoding). `OT.statClose_prod_of_forall` lifts closeness for every
  value of a shared coordinate to the joint samplers.
- `OT.distAdv_realA_idealA_le`: Alice's side is at most `2δ(n)` for every distinguisher, `n` and
  inputs (`acceptProb_comp_equiv` along the coin equivalences, `StatClose.prod` with the identical
  raw sample, the blocks swapped when `b = 1`, `distAdv_le_of_statClose`).

### 2.4 Final: Bob's side (`ObliviousTransfer/Predictor.lean`, `ObliviousTransfer/ViewB.lean`)

- **The views.** `OT.bobView u b a₀ a₁ i s w β` is Bob's view (paired with Alice's `[]`) with
  tape `s`, index `i`, selected mask `H ⟨i, w⟩ ⊕ [a_b]` and unselected mask `[β ⊕ a_{1−b}]`.
  On `(r, s₁, s₂)` the real sampler is `bobView … (s₁ ++ s₂) (Sample(i; s₁)) (B s₂)` with the
  enhanced bit `B s₂ = OT.hcBit T h n r s₂ = h_i(perm_i⁻¹(dec_i(Sample(i; s₂))))`
  (`OT.realB_realCoins`: the selected mask by `OT.mask_eval`, the unselected one by
  `OT.mask_raw`, both through the inverter on the all-`true` tape `OT.inv_runAtL_ones`,
  `inv_eq_encD`, and `henc` extended to decodable strings by `apply_of_decD`); on
  `(r, s₁, s₂, c)` the ideal one is the same with `β = c ⊕ a_{1−b}` (`OT.idealB_simBCoins`).
- **Acceptance.** With `accB … r g = Pr[D(bobView … (g s₂)) = 1]`, the real acceptance is
  `E_r accB r B` (`OT.acceptProb_realB`) and the ideal one `E_r (accB r B + accB r ¬B)/2`
  (`OT.acceptProb_idealB`, `OT.uprob_xor_shear`).
- **The predictor.** `OT.viewDist D b a₀ a₁` (`NUPPT.ofPolyTime` of `OT.viewDistRaw`, `D`'s
  advice, coins `coins_Sample + coins_D`) reads `⟨i, ⟨s', [β]⟩⟩` and its coins `s₁ ++ ρ`, builds
  `bobView (1^n) b a₀ a₁ i (s₁ ++ s') (Sample(i; s₁)) β` and runs `D` on it with `ρ`
  (`OT.distinguisherL_viewDist`). The published `tdpPredictor (viewDist …) flip` of Algorithm
  104.3 is the predictor: by `uprob_tdpPredictor` and the signed-predictor identity for uniform
  coin challenges (`OT.uprob_signedPredictor_false`/`_true`), it predicts `B` from `⟨i, s'⟩` with
  probability `1/2 ± (accB r B − accB r ¬B)/2` (`OT.uprob_predictor_false`/`_true`).
- **The bound.** For the inputs' bits `t = (b, a₀, a₁)`, `hEHC` at the two predictors gives
  `|ε_{t,0}(n)| + |ε_{t,1}(n)|` (`OT.distAdv_realB_idealB_le`, `uexp_half_add`/`_sub`). Over the
  eight triples and two signs, `ε_B(n) = Σ_t Σ_fl |ε_{t,fl}(n)|` is negligible
  (`OT.negligible_finset_sum`) and bounds every input (`OT.exists_negligible_bob`).
- **Together** (`OT.simulators_of_isOT`): `ε(n) = 2|δ(n)| + ε_B(n)`, with `δ` from
  `T.OneWay`'s `sampleClose`.

**Edge cases** (the brief's list): `b = 0, 1` (the two branches of `realA_realCoins`,
`realB_realCoins`, `idealB_simBCoins` and the block swap in `distAdv_realA_idealA_le`); all eight
`(b, a₀, a₁)` (sixteen machines); the five-message layout and its two empty fillers
(`exec_five`, `transcriptWith_isOT`); non-canonical strings (`apply_of_decD` in `mask_eval`,
canonical decoding in `statClose_eval_sample` and `mask_raw`); the inverter's fixed all-`true`
tape (`inv_runAtL_ones`, and `OT.maskRaw` in the machine); small `n` (`SampleClose δ` holds at
every `n`, so Alice's bound needs no threshold; only the final `ε` is asymptotic); the
distinguisher's advice (`viewDist` and `tdpPredictor` keep `D`'s advice and advice polynomial).

**Route differences from the maintainer's sketch** (statements unchanged): the predictor machine
is the published `tdpPredictor` around `OT.viewDist` (an `ofPolyTime` machine) rather than a new
`NUPPT.exists_comp` composite; and instead of the worst of the eight triples as advice, each
triple is hard-wired in its own machine and the sixteen bounds are summed (equivalent, and it
keeps `D`'s advice untouched).

### 2.5 The owned file

`ObliviousTransfer.lean` (671 → 747 lines): the six helper imports (each directly), the title
without "(statement phase)", `## Main results` (the new `otProtocol_isOT`, `otSimA_isSimA`,
`otSimB_isSimB`; both targets proved), a `## Contents` list of the helpers, the two proofs, and the
two targets' `**Proof sketch.**` paragraphs rewritten to describe the delivered proofs (the
statement prose is unchanged). No other declaration changed.

### 2.6 New declarations (namespace `TCSlib.Cryptography.SecureComputation`)

- Owned file: `otProtocol_isOT`, `otSimA_isSimA`, `otSimB_isSimB`.
- `OT.` in `Shape.lean` (206 lines): `mask`, `mask_eq`, `senderNext`, `senderNext_eq`,
  `receiverNext`, `receiverNext_eq`, `IsOT`, `isOT_iff`, `senderNext_nil`, `senderNext_single`,
  `senderNext_pair`, `receiverNext_single`, `receiverNext_pair`, `exec_five`,
  `transcriptWith_isOT`.
- `OT.` in `Efficiency.lean` (526 lines): `headD_eq_pairFstD`, `pairSndD_nil'`, `getD_one_eq`,
  `runAtL_eq_layout`, `advInput_layout`, `genRaw`, `genRaw_eq`, `polyTimeComputable_genRaw`,
  `maskRaw`, `maskRaw_eq`, `polyTimeComputable_maskRaw`, `senderRaw`, `senderRaw_eq`,
  `polyTimeComputable_senderRaw`, `genRaw_layout`, `maskRaw_layout`, `getD_zero_eq`,
  `getD_one_eq'`, `senderRaw_advInput`, `knownRaw`, `knownRaw_eq`, `rawRaw`, `rawRaw_eq`,
  `outRaw`, `outRaw_eq`, `pairRaw`, `pairRaw_eq`, `receiverRaw`, `receiverRaw_eq`,
  `polyTimeComputable_receiverRaw`, `knownRaw_layout`, `rawRaw_layout`, `receiverRaw_advInput`,
  `length_runAtL_le`, `length_zipWith_singleton_le`, `length_mask_le`, `exists_messages_le`,
  `polyTime_of_isOT`.
- `OT.` in `Simulators.lean` (431 lines): `splitLen`, `splitLen_symm_ofFn`, `simSeg`,
  `simSeg_eq`, `simIndex`, `simIndex_eq`, `simSampled`, `simSampled_eq`, `simAView`,
  `simAView_eq`, `simZbit`, `simZbit_eq`, `simZpair`, `simZpair_eq`, `simBView`, `simBView_eq`,
  `IsSimA`, `isSimA_iff`, `IsSimB`, `isSimB_iff`, `simSeg_layout`, `length_ofFn_coins`,
  `simIndex_layout`, `simSampled_layout`, `simAView_layout`, `simBView_layout`, `realCoins`,
  `realCoins_symm_fst_ofFn`, `realCoins_symm_snd_ofFn`, `simACoins`, `simACoins_symm_ofFn`,
  `simBCoins`, `simBCoins_symm_ofFn`, `inA_eval`, `inB_eval`, `inA2`, `inA2_apply`, `ofFn_inA2`,
  `inB1`, `inB1_apply`, `ofFn_inB1`, `ofFn_eq_inB1`, `ofFn_f_fst`, `ofFn_f_snd`.
- `OT.` in `ViewA.lean` (186 lines): `statClose_prod_of_forall`, `statClose_eval_sample`,
  `realA_realCoins`, `idealA_simACoins`, `distAdv_realA_idealA_le`.
- `OT.` in `Predictor.lean` (206 lines): `bobView`, `bobView_eq`, `polyTimeComputable_bobView`,
  `viewRaw`, `viewRaw_eq`, `viewDistRaw`, `viewDistRaw_eq`, `polyTimeComputable_viewDistRaw`,
  `viewDist`, `viewDist_coins`, `viewDistCoins`, `viewDistCoins_symm_ofFn`, `runAtL_viewDist`,
  `distinguisherL_viewDist`.
- `OT.` in `ViewB.lean` (534 lines): `uprob_signedPredictor_false`, `uprob_signedPredictor_true`,
  `uprob_xor_shear`, `negligible_finset_sum`, `hcBit`, `hcBit_eq`, `inv_runAtL_ones`, `mask_eval`,
  `mask_raw`, `ofFn_inA2_eq`, `realB_realCoins`, `idealB_simBCoins`, `accB`, `accB_eq`,
  `acceptProb_realB`, `acceptProb_idealB`, `acceptProb_viewDist`, `uprob_predictor_false`,
  `uprob_predictor_true`, `distAdv_realB_idealB_le`, `exists_negligible_bob`, `simulators_of_isOT`.

Every public `def` has an `_eq`/`_iff` reader (or, for the coin equivalences, `_ofFn` readers
named after them, which lint check 8 accepts); every docstring states its formula; every proof
of 15 lines or more has a `**Proof sketch.**`; no `@[simp]` was added.

## 3. Overlap and reuse

Searches: `logs/checkpoint1-searches.log`, `logs/final-searches.log` (TCSlib at the base,
Mathlib/Batteries, Lean core). **Reused** (published, imported): `uprob_tdpPredictor`,
`tdpPredictor`, `uexp_half_add`, `uexp_half_sub` (`Encryption/PublicKey/TrapdoorPredictor.lean`);
`distAdv_le_of_statClose`, `StatClose.prod`, `.map`, `.trans`, `.refl`, `.comp_equiv_left`,
`abs_uexp_sub_le` (`Asymptotic/Sampling.lean`); `uprob_prod`, `uprob_comp_equiv`, `uprob_not`,
`uprob_bool_prod`; `acceptProb_comp_equiv`; `splitCoins`, `ofFn_splitCoins_symm`,
`NUPPT.runLenPoly`, `length_runAt_le_runLenPoly`; `inv_eq_encD`, `apply_of_decD`,
`evalSampled_iff`, `decD_eq_some_iff`, `f_perm`, `sampleClose_iff`; `Negligible.add`,
`.const_mul`, `.mono`, `negligible_zero`; `polyTimeComputable_isNil`, `_ite`, `_headD`, `_tail`,
`_pairXor`, `_pairTakePoly`, `_pairDropPoly`, `_unaryPoly`, `BinArith.polyTimeComputable_xor`,
`NUPPT.ofPolyTime`, `ofPolyTimeUniform` and their readers.

| New declaration | Nearest relative | Relation | Why not reused |
|---|---|---|---|
| `OT.uprob_signedPredictor_false`, `_true` | `predProb_pkPredictor_false`, `_true`, `exists_pkPredictor` (`Encryption/PublicKey/Trapdoor.lean:317,326,337`); `predProb_owpPredictor_false`, `_true` (`Pseudorandom/GeneratorFromPermutation.lean:131,172`) | **the expected adapted copy**: the same signed-predictor identity, for a uniform challenge `x` itself (the `⟨i, coins⟩` challenges, `f = id`), stated with the explicit predictor `(if D(x, c; ρ) then c else ¬c) ⊕ flip`; proved like `predProb_owpPredictor_false` | `pkPredictor` has no published reader and the bridge `predProb_pkPredictor_eq` is private; `owpPair`, `owpGen`, `owpGenNot` have no readers either. Under the rule-10 seals the identity cannot be read off them. **Promotion request** below |
| `OT.uprob_xor_shear` | `uprob_bool_prod` (`GeneratorFromPermutation.lean:59`) and the bijection inside `predProb_owpPredictor_false` | a re-centred form | no published lemma for a masked uniform bit |
| `OT.negligible_finset_sum` | `Negligible.add` (`Foundations/Negligible.lean:86`) | its finite-sum form, by induction | no finite-sum lemma exists (searched `Negligible.*∑`, `negligible_sum`) |
| `OT.hcBit` | the bit of `EnhancedHardCore`'s experiment (`ObliviousTransfer.lean:231`); private `tdpSampled` (`Trapdoor.lean:351`) | the bit, named | the helper cannot import the owned file; `tdpSampled` is private |
| `OT.inv_runAtL_ones` | `TrapdoorCollection.inv_eq_encD` (`Asymptotic/Collections.lean:415`); the same step inside `otProtocol_outV` | `inv_eq_encD` on the all-`true` list tape | the masks run the inverter on a list |
| `OT.mask_eval`, `OT.mask_raw` | steps of `otProtocol_outV`; private `tdpBitScheme_pkEncDist` (`Trapdoor.lean:357`) | the masks on Bob's real pair | needed as rewrite lemmas; the latter is private |
| `OT.bobView`, `OT.viewRaw`, `OT.viewDistRaw`, `OT.viewDist`, `OT.viewDistCoins` and lemmas | `tdpPredFun`, `tdpPredictor`, `predCoins` (`TrapdoorPredictor.lean`) | the same construction pattern for a different distinguisher; `tdpPredictor` itself is reused around it | a new machine |
| `OT.accB`, `OT.acceptProb_realB`, `OT.acceptProb_idealB`, `OT.acceptProb_viewDist`, `OT.uprob_predictor_false`, `_true`, `OT.distAdv_realB_idealB_le` | the steps `hclose`, `key`, `hf`, `ht` inside `TrapdoorCollection.tdpBitScheme_singleBitSecure` (`Trapdoor.lean:412`) | the analogous steps for Bob's view | different samplers |
| `OT.mask`, `OT.senderNext`, `OT.receiverNext`, `OT.simSeg`, `OT.simIndex`, `OT.simSampled`, `OT.simAView`, `OT.simZbit`, `OT.simZpair`, `OT.simBView` | `otMask`, `otSender`, `otReceiver`, `coinSeg`, `simIdx`, `simSample`, `otSimAFun`, `otSimZb`, `otSimZ`, `otSimBFun` (the owned file) | restatements of the bodies | the helpers cannot import the owned file; `otProtocol_isOT`, `otSimA_isSimA`, `otSimB_isSimB` prove the equalities from the published readers |
| `OT.exec_five`, `OT.transcriptWith_isOT` | `exec_succ`/`exec_zero` (`ZeroKnowledge/Interaction.lean:262,266`); the unfolding inside `otProtocol_outV` | the five-move unfolding, stated once | no five-move lemma exists |
| `OT.headD_eq_pairFstD` | `Strategy.pairFstD_encodeMsgs` (`Interaction.lean:143`) | its symmetric form | used as a left-to-right rewrite |
| `OT.pairSndD_nil'`, `OT.getD_one_eq` | private `pairSndD_nil` (`Asymptotic/BlockEncryptor.lean:156`); `GI.pairSndD_encodeMsgs`, `GI.encodeMsgs_eq_nil_iff` (`GraphIsomorphism/EfficiencyRep.lean:93,110`) | re-derived from the public `length_pairSndD_le` (`ClassNP/PolyTimeBlockLoop.lean:187`) | the first is private; `EfficiencyRep` comes after the owned module in `order.txt` |
| `OT.runAtL_eq_layout`, `OT.advInput_layout` | `NUPPT.runAtL_eq_output_layout` (`Randomized/Closure.lean:159`); `advInput_eq`, `layout_eq` | uniform specialization; composite | match `runAtL_ofPolyTimeUniform` |
| `OT.getD_zero_eq`, `OT.getD_one_eq'` | `List.getD_cons_zero`, `List.getD_cons_succ` (core `Init/Data/List/Lemmas.lean:330`) | the `headD` forms for every list | the core lemmas cover cons only |
| `OT.length_runAtL_le` | `NUPPT.length_runAt_le_runLenPoly` (`Asymptotic/CollectionsHelpers.lean:132`) | its list form, proved from it | the strategies' tapes are lists |
| `OT.length_zipWith_singleton_le`, `OT.length_mask_le` | `List.length_zipWith` | two-line consequences | — |
| raw functions `OT.genRaw` … `OT.receiverRaw` and lemmas | `GI.giProver_efficient`, the GI/3-col machines (`GraphIsomorphism/EfficiencyRep*.lean`, `ThreeColoring/Machines.lean`) | the same pattern (raw layout function, `ofPolyTimeUniform`) | specific to Protocol 160.4 |
| `OT.splitLen`, `OT.splitLen_symm_ofFn` | `splitCoins`, `ofFn_splitCoins_symm` (`CollectionsHelpers.lean:145,172`); `Fin.appendEquiv` | `splitCoins` after a length cast, proved from `ofFn_splitCoins_symm` | the coin lengths are `coinLen`/`PolyExpr.eval` terms, not syntactic sums |
| `OT.realCoins`, `OT.simACoins`, `OT.simBCoins`, `OT.length_ofFn_coins` | `Collection.owfCoinsEquiv`, `NUPPT.coinsEquivPoly` | coin equivalences of the same kind | specific layouts |
| `OT.inA2`, `OT.inB1`, `OT.ofFn_f_fst`, `OT.ofFn_f_snd`, `OT.ofFn_inA2_eq` | `otFunctionality_inA`, `_inB`, `_outA`, `_f_snd_apply` (`SecureComputation/Defs.lean:202–232`) | consequences of the published readers | inputs as `Fin 2`/`Fin 1` functions for `otProtocol_outV` |
| `OT.statClose_prod_of_forall` | `StatClose.prod`, `StatClose.abs_uprob_sub_le_prod` (`Sampling.lean:237,262`) | the dependent form | `StatClose.prod` needs independent coordinates |
| `OT.statClose_eval_sample` | `hclose` inside `tdpBitScheme_singleBitSecure` | a related use of `SampleClose` | different samplers |

No private lemma was copied. **Promotion requests** (general lemmas in this fill's helpers, for
landing; none is needed for the proofs to stand):
- `OT.uprob_signedPredictor_false`/`_true` beside `exists_pkPredictor` in
  `Encryption/PublicKey/Trapdoor.lean` (with a reader `pkPredictor_apply`, which would also let
  `predProb_pkPredictor_false` serve sealed consumers);
- `OT.negligible_finset_sum` in `Foundations/Negligible.lean`;
- `OT.statClose_prod_of_forall` beside `StatClose.prod` in `Asymptotic/Sampling.lean`;
- `OT.exec_five` beside `exec_succ` in `ZeroKnowledge/Interaction.lean`;
- `OT.length_runAtL_le` beside `NUPPT.length_runAt_le_runLenPoly` in
  `Asymptotic/CollectionsHelpers.lean`.

**Reader request** (optional, not used): `pkPredictor_apply`, `owpPair_apply`, `owpGen_apply`,
`owpGenNot_apply` would make the published predictor identities usable under the seals.

## 4. Scope requests

None. No frozen file was edited (`git diff --stat` from the base touches only the owned file and
the six new helpers under `SecureComputation/ObliviousTransfer/`). Seyoon was not asked anything.

## 5. Checks (final)

- **Owned module recheck** (`logs/final-owned-recheck.log`): status 0, no warning.
- **Final sweep** (`logs/final-sweep.log`, order `logs/final-order.txt`: `order.txt` with the six
  helpers inserted before `ObliviousTransfer`, 165 modules): every module status 0, 0 errors;
  maximum RSS 2645308 KiB.
- **Census** (`logs/final-census.txt`, `logs/final-census-vs-base.diff`): 29 declarations in 13
  modules; the only difference from `base-sorries.txt` is the row
  `SecureComputation/ObliviousTransfer: 2: otProtocol_simulators, otProtocol_polyTime`, absent
  at the final.
- **Axioms** (`logs/final-axioms.log`, `probes/AxiomsFinal.lean`): `otProtocol_polyTime`,
  `otProtocol_simulators` and `otProtocol_hbcSecure`: `[propext, Classical.choice, Quot.sound]`.
  Every stored constant of the owned module and the six helpers, enumerated from the environment
  (234 constants: 70 owned, 15 `Shape`, 49 `Efficiency`, 55 `Simulators`, 7 `ViewA`, 15
  `Predictor`, 23 `ViewB`, auxiliary constants included): **0 with a non-standard axiom**.
- **Seals** (`seals/`): whole-file seals of the seven changed or new files at the final, and of
  the owned file at the base (a verbatim copy, `base/ObliviousTransferBase.lean`, recorded under
  the original path), each over its full TCSlib import closure, in the four variants A-strict,
  A-coe, B-strict, B-coe (A: `PolyExpr.eval` excluded as notation; B: sealed; coe: projection
  coercions excluded, the only one in this closure being `FinDist.instCoeFunForallReal`):
  **every run status 0, 0 errors** (28 final runs, 4 base runs; `final-*.jsonl`, `base-*.jsonl`,
  raw `.out`, sealed copies in `seals/sources/`; errors counted with `error[:(]`). Comparison
  (`seals/seals-compare.log`): no new failing declaration against the base, and no difference
  between strict and coe, nor between A and B: nothing to attribute.
- **Paired controls** (`controls/`, `logs/controls-plain.log`, `seals/controls-*.jsonl`):
  `CtlUnfold` (`NUPPT.layout u y α r = ⟨⟨⟨u, y⟩, α⟩, r⟩ := rfl`, a foreign library definition)
  and `CtlUnfoldHelper` (`OT.mask … = … := rfl`, a helper definition, foreign to every other
  module): unsealed 0, **1 error in each of the four sealed variants**; `CtlEval`
  (`(PolyExpr.const 5).eval 3 = 5 := rfl`): unsealed 0, A 0, **B 1**; `CtlReader` (the same facts
  through `layout_eq`, `OT.mask_eq`, `eval_const`): 0 everywhere; `CtlCoe` (an explicit application
  of `FinDist.instCoeFunForallReal` by `rfl`): 0 everywhere, a documented probe, not a negative
  control (Lean reduces a projection of an instance even when the strict seal makes the instance
  irreducible). Each sealed negative fails exactly once; the positive passes.
- **Explicit-unfold scan** (`scan/`, `logs/scan-*.log`): every identifier given to
  `rw`/`simp`/`unfold`/… in the seven files, resolved: **0 foreign TCSlib definitions** at the
  final (392 rows) and at the base (47 rows); `scan/scan-compare.log`: "NEW foreign explicit
  unfolds: 0". The own-definition rows are the owned file's 14 at the base (unchanged:
  `otProtocol`, `otSender`, `otReceiver`, … inside the pre-existing correctness proofs) and three
  helper-internal ones (`viewDist`, `simACoins`, `simBCoins`, each in its own file).
- **Width and size** (`logs/final-width.log`): no line over 100 characters; the owned file has
  747 lines, the helpers 206, 526, 431, 186, 206 and 534.
- **Lint** (`logs/base-lint.log`, `logs/final-lint.log`, `logs/final-lint-vs-base.diff`):
  92 FAIL / 101 WARN at the base and at the final; the FAIL/WARN line sets are identical (no new
  line). The facade check is satisfied: the owned file imports each helper directly.
- **Patches** (`patches/`, `patches/COMMITS.tsv`): the three commits from the base. Reproduction
  (`logs/final-repro.log`): `git am` at the base in a scratch clone (`/tmp/scot-repro`, deleted
  afterwards), with the committer identity and date of `COMMITS.tsv`: every hash reproduced.
- **Checkpoints** (kept): `logs/checkpoint1-*`, `logs/checkpoint2-*`, `seal-cp1/`, `seal-cp2/`,
  `probes/AxiomsCP1.lean`, `probes/AxiomsCP2.lean`.

## 6. Evidence (`evidence/`, manifest `evidence/SHA256SUMS`)

- `logs/`: environment (`preflight.log`, `source-sha256.log`, `order.txt`, `mathlib-roots.txt`,
  `cache-store.log`, `cache-get.log`, `packages-check.log`, `zero-size-oleans.log`,
  `cache-probe.log`), bootstrap (`bootstrap.log`, `census-bootstrap.txt`,
  `census-bootstrap-vs-base.diff`), checkpoints 1 and 2 (`checkpoint{1,2}-checks.log`,
  `census-checkpoint{1,2}-checks.txt`, `checkpoint{1,2}-axioms.log`, `checkpoint{1,2}-width.log`,
  `checkpoint{1,2}-lint.log`, `checkpoint{1,2}-lint-diff.log`, `checkpoint{1,2}-repro.log`,
  `checkpoint1-searches.log`), final (`final-order.txt`, `final-owned-recheck.log`,
  `final-sweep.log`, `final-census.txt`, `final-census-vs-base.diff`, `final-axioms.log`,
  `final-width.log`, `final-lint.log`, `final-lint-vs-base.diff`, `final-repro.log`,
  `final-searches.log`, `final-pipeline.log`, `controls-plain.log`, `scan-final.ids.log`,
  `scan-final.raw.log`, `scan-base.ids.log`, `scan-base.raw.log`), `base-lint.log`.
- `seals/`: `final-*.jsonl`/`.out`, `base-*.jsonl`/`.out`, `controls-*.jsonl`/`.out` (four
  variants each), `seals-compare.log`, `sources/` (every sealed copy: `f*` final, `b*` base,
  `c*` controls).
- `seal-cp1/`, `seal-cp2/`: the checkpoint seals.
- `scan/`: `scan-final.tsv`, `scan-base.tsv`, `scan-compare.log`, `sources/` (the scan modules).
- `controls/`: `CtlUnfold.lean`, `CtlUnfoldHelper.lean`, `CtlEval.lean`, `CtlReader.lean`,
  `CtlCoe.lean`. `base/`: `ObliviousTransferBase.lean` (the base copy of the owned file).
- `probes/`: `CacheProbe.lean`, `AxiomsCP1.lean`, `AxiomsCP2.lean`, `AxiomsFinal.lean`.
- `tools/`: every script used (`check.sh`, `dev.sh`, `devall.sh`, `sweep_chunk.sh`, `census.py`,
  `cmpcensus.sh`, `pkgcheck.py`, `seal_gen.py`, `seal_run.py`, `seal_all.sh`, `seal_cp1.sh`,
  `seal_cp1b.sh`, `cp2_checks.sh`, `rwids.py`, `rwids_run.sh`, `cmp_scans.py`, `width_check.py`,
  `run_final.sh`, `final_pipeline.sh`, `payload.sh`, `repro_check.sh`, `manifest.sh`,
  `finalize.sh`).
- `patches/` (three patches and `COMMITS.tsv`), `src/` (the seven changed or new files at the
  final commit).

The top-level `SHA256SUMS` lists every delivered file under `inbox/fills/sc-ot/` except itself;
the delivered paths equal the manifest's (checked before the push).
