# Fill · Yao's protocol in the OT-hybrid model (`sc-yao`, U3)

**Issue base** `6ce4658db08a1dc2a03a149987197660db078011`,
the head of `cryptography/pass-shelat-ch2-4`. It contains #311, #312 and #314–#317; #313 is not merged and lies
outside this order. **Unit** `sc-yao`, U3 of the secure-computation plan, the last core unit. **Worker** as
Seyoon dispatches (ruling SY-6: Codex on his Mac, or Claude); the brief calls it "the worker". **Lean** 4.25.0 and
the Mathlib revision in that commit's `lake-manifest.json`.

**Rulings.** Six questions were put to Seyoon at staging (SY-1 to SY-6, *Open rulings* below). This brief is
written for the recommended answers, and every place that depends on one names it. Seyoon's answers are added to
this package as `ruling-SY.md` before dispatch. Where a ruling differs from the brief, the ruling wins.

Prove two admitted, frozen statements of `TCSlib/Cryptography/SecureComputation/Yao.lean`:

| Target | Line at base | Source |
|---|---|---|
| `yaoHybrid_polyTime` | 841 | [PS10, Definition 155.1] (the efficiency clause, ruling of 2026-11-05), for Protocol 162.6 in the OT-hybrid model |
| `yaoHybrid_simulators` | 907 | [PS10, Theorem 163.7] in the OT-hybrid model; the one-active-key simulator of [LP09] |

Both are confirmed at the issue base: each is a `theorem` whose body is `sorry` (`base-sorries.txt`). They passed
the prong statement phase and Gate 06 and are frozen. Their docstrings hold the maintainer's proof sketches. Together
with the proved `yaoHybrid_hbcSecure` they give Theorem 163.7 in the OT-hybrid model.

## Proved modulo sc-garble (the parallel units)

- **`sc-garble` (U1)** is delivered (exchange `a73072f1`) and under review. It is **not merged**. It proves, among
  others, `yaoSeed_good_whp` (in this same file) and `sliceMultiMessageSecure_of_prfOut` (the B1 statement,
  `SpecialEncryptionMulti.lean`), plus the garbling bounds. **In your base both stay `sorry`.**
  - You cite them as frozen statements, exactly as stated. `yaoHybrid_simulators` is therefore proved **modulo
    sc-garble**: its axioms keep `sorryAx` through those two statements until sc-garble lands. This is expected.
  - `sc-yao` lands **after** sc-garble, rebased by the maintainer. Both units edit the same `## Main results` bullet
    of `Yao.lean`; the maintainer resolves that conflict at the rebase.
  - **Use none of sc-garble's new declarations.** Its B2 lemma (`uprob_not_good_le_of_perm`), its helpers
    (`Garbling/*`, `GarblingSecurity/*`, `SpecialEncryptionSecurity/*`, `SpecialEncryptionMulti/*`) and its
    approved reader `DAGCircuit.isFaninTwo_iff` are not in your base. The single exception is SY-3: a byte-identical
    copy of that reader.
- **`sc-ot`** is draft PR #318 (head `f62a25b3`, Gate 34 on hold for LE-gate34). It proves `otProtocol_*` in
  `ObliviousTransfer.lean`. **`sc-compose`** is delivered (exchange `bdfdcb76`) and under review; it proves the
  `ComposeSecurity.lean` admissions. Those two files are in your order only because `YaoReal.lean` imports them. You
  neither edit them nor need them: `yaoProtocol_hbcSecure` composes the three units in `YaoReal.lean`.
- **`derand`** is delivered (exchange `186ffb99`) and under review. It has pre-approved additions to
  `Complexity/ClassP/DTIME.lean` and `Complexity/Randomized/Build/IterateFind.lean`, which are in your order as
  upstream modules. They are unchanged here.
- #319 (canonizer) and #313 (learning) are outside your order.
- If any of these merges during the fill, **stay on the issue base**. The maintainer rebases at landing.

## Feasibility and size (maintainer's assessment)

**Feasible, and the longest unit of the plan.**
- The secure-computation plan (`briefs/pass-shelat-ch5-8/maintainer/securecomp-plan-2026-11-14/plan.md`, §2.9–2.10
  and §3) found neither statement false and no missing hypothesis once B1 was stated.
- Gate 27 (CLEAR) confirmed that B1 supplies step 3. Both slice shapes fit, `(0, n)` and `(2n, 4n + 2)` in
  `L(n) = 7n + 2`. The non-adaptive interface suffices.
- Re-read at staging, the sketches hold:
  - the point-and-permute relabelling is a bijection of Alice's coins: key blocks swap, row-coin blocks permute
    by `a ↦ a ⊕ v_args`, and shift bits XOR;
  - the message bound does not depend on the answers;
  - `S_A`, `S_B` and the reductions are uniform, or non-uniform with polynomial advice.

The risks are engineering, not mathematics:
1. **Visibility** (SY-1). A helper that `Yao.lean` imports cannot see `Yao.lean`'s definitions. So the helpers are
   stated generically, and the bodies in `Yao.lean` connect them to Yao's definitions, within a line budget (SY-2).
2. **Missing poly-time infrastructure.** No poly-time decoder of circuit descriptions exists, and no poly-time
   `runWith` with a data-dependent gate function. The CVAL machine (`CircuitEval*`) decides a language and cannot be
   reused.
3. **The B1 embedding.** It needs exact sampler identities, all-occurrence enumeration and fixed auxiliary
   randomness.

**Estimated size: 5,000–8,600 lines** in roughly 15–25 helper modules. The plan estimated 5–8k; the generic form of
SY-1 adds hypotheses but no proofs. For calibration, sc-garble added about 1.8k lines and cca2-ett 5.4k.

The checkpoints each deliver whole declarations (*Proof route and checkpoints*):

| Checkpoint | Content | Lines |
|---|---|---|
| 1 | poly-time infrastructure (decoder, garbling from coins, garbled evaluation, length bounds) | 1,600–2,800 |
| 2 | `yaoHybrid_polyTime` proved | 400–700 |
| 3 | views, `S_A` and Alice's side, Bob's output switch, `S_B` and its efficiency | 1,000–1,700 |
| 4 | the exact sampler identities `H₀ = H₁` and `H₂,end = S_B` | 600–1,000 |
| final | the B1 embedding and the gate hybrid; `yaoHybrid_simulators` proved | 1,400–2,400 |

A partial final is allowed (*Partial delivery*).

## Checkout and delivery

- Fetch `cryptography/pass-shelat-ch2-4`. Start a local branch `fill/sc-yao` at the exact issue base
  `6ce4658db08a1dc2a03a149987197660db078011`, and record the base in `REPORT.md`. Keep the proof branch local.
- Read `policy.md`, the attached environment addendum (and, on Seyoon's Mac, the host addendum), `README.md` and
  `ruling-SY.md`.
- Deliver every checkpoint and the final payload under `inbox/fills/sc-yao/` on `exchange/pass-shelat-ch5-8`:
  - `REPORT.md`;
  - `patches/`: the whole `git format-patch` series from the issue base;
  - `patches/COMMITS.tsv`: one row per commit. Give its hash, the author's name, email and date, the committer's
    name, email and date, and its **signing**: `none`, or the signature format. With these, `git am` at the base
    reproduces every hash. **Commit with `git -c commit.gpgsign=false`.** If a commit is signed anyway, say so in
    its row and in `REPORT.md`. Before you push, check the reproduction in a scratch clone and say so in
    `REPORT.md`;
  - `src/`: the changed and new files;
  - `evidence/`, with an `evidence/SHA256SUMS` manifest (see *Evidence completeness*);
  - a top-level `SHA256SUMS` listing every delivered file under `inbox/fills/sc-yao/` except itself. The delivered
    paths must **equal** the manifest's paths exactly: nothing missing, nothing extra, and no leading `./`. Check
    this before each push.
- Commit as `fill sc-yao: checkpoint N` and `fill sc-yao: final`.
- Pull with rebase before pushing. Push only your delivery path, and never force-push. Campaign changes land by a
  maintainer PR for Seyoon's approval.

## Targets (frozen; quoted from the issue base)

```lean
theorem yaoHybrid_polyTime (hE₁ : PolyTimeComputable E₁) (hE₂ : PolyTimeComputable E₂) :
    (yaoHybrid Y E₁ E₂).PolyTime (yaoFunctionality Y) := by
  sorry
```

```lean
include hGE₁ hGE₂ in
theorem yaoHybrid_simulators (hE₁ : PolyTimeComputable E₁) (hE₂ : PolyTimeComputable E₂)
    (hG₁ : PRFOut (.add .var .var) G₁) (hG₂ : PRFOut (.add .var innerLen) G₂)
    (hG₁₂ : PRFOut (.add (.add .var .var) (.add .var innerLen))
      (fun n s x => Fin.append (G₁ n s x) (G₂ n s x))) :
    ∃ SA SB : NUPPT, ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n (x : Fin ((yaoFunctionality Y).inA.eval n) → Bool)
        (y : Fin ((yaoFunctionality Y).inB.eval n) → Bool),
        distAdv ((yaoHybrid Y E₁ E₂).realA (yaoFunctionality Y) n x y)
            ((yaoFunctionality Y).idealA SA n x y) (D.distinguisherL n) ≤ ε n ∧
          distAdv ((yaoHybrid Y E₁ E₂).realB (yaoFunctionality Y) n x y)
            ((yaoFunctionality Y).idealB SB n x y) (D.distinguisherL n) ≤ ε n := by
  sorry
```

**Context.**
- Namespace `TCSlib.Cryptography.SecureComputation`, under `open Complexity Turing TCSlib.Cryptography BoolCircuit`.
- File variables `(Y : YaoCircuit) (E₁ E₂ : List Bool → List Bool)`.
- `section Security` variables `G₁` (`Fin (n + n)` outputs) and `G₂` (`Fin ((PolyExpr.add .var innerLen).eval n)`
  outputs), and `hGE₁`, `hGE₂` (the evaluators on canonical inputs). The simulators carry `include hGE₁ hGE₂ in`.
- `yaoHybrid_hbcSecure` (proved) consumes both targets. It is the only consumer, and `YaoReal.lean`'s
  `yaoProtocol_hbcSecure` consumes it.
- Unfolded, `HybridProtocol.PolyTime` (`polyTime_iff`) asks for:
  - `main.P.Efficient` and `main.V.Efficient`;
  - polynomial-time call inputs, from `⟨1^n, ⟨x, ⟨r, 1^j⟩⟩⟩`;
  - a polynomial message bound for **any** answers of the right lengths.
- `HBCSecure`'s simulator clause is exactly the conclusion of `yaoHybrid_simulators`, with `SA` and `SB` chosen
  before `D`, and `ε` after `D` but before `n`, `x` and `y`.

## Published interfaces

| Interface | Provider |
|---|---|
| **Frozen statements, cited (proved modulo sc-garble):** `yaoSeed_good_whp`; `sliceMultiMessageSecure_of_prfOut` with `sliceMultiMessageSecure_iff`, `sliceMultiEncDist_apply`, `sliceEnc_eq`, `sliceEnc_eq_spEncStr`, `sliceEnc_append_left`, `sliceEnc_append_right` | `Yao.lean`; `SpecialEncryptionMulti.lean` |
| `encodeCircuit_eq`, `encodeCircuit_injective`, the `YaoCircuit` fields (`circ`, `outs`, `outs_lt`, `outs_sink`, `fanin`, `size_le`, `uniform`), `YaoCircuit.output_apply`, `yaoFunctionality_inA/_inB/_outA/_outB/_f` (`simps`), `readBits_apply`, `assignIdx_eq`, `xorShift_apply`, `xorShift_symm_apply`, `yaoCoins_eq`, `yaoCoins_eval`, `yaoSeed_fst`, `yaoSeed_snd_fst`, `yaoSeed_snd_snd`, `keyAt_yaoSeed`, `decodeMsgs_eq`, `decodeMsgs_encodeMsgs`, `decodeMsgs_nil`, `yaoTables_eq`, `yaoKeysA_eq`, `yaoPairs_eq`, `yaoMsg_eq`, `yaoBobTables_eq`, `yaoBobInit_eq`, `yaoBobValues_eq`, `decodeOut_eq/_fst/_snd`, `yaoBobOut_eq`, `yaoAlice_next_nil/_cons`, `yaoAlice_coins`, `yaoBob_next`, `yaoBob_coins`, `yaoMain_P/_V/_rounds/_verifierFirst` (`simps`), `yaoMain_outV`, `yaoMain_outP`, `yaoCall_eq`, `yaoCall_finProdFinEquiv`, `yaoHybrid_main/_calls` (`simps`), `yaoHybrid_callA`, `yaoHybrid_callB`, `yaoBobTables_yaoMsg`, `yaoBobInit_yaoMsg`, `yaoBobValues_yaoMsg`, `yaoBobOut_yaoMsg`, `yaoHybrid_answersB_getD`, `yaoHybrid_correct` | `SecureComputation/Yao.lean` (usable **only in the two bodies**; see SY-1) |
| `HybridProtocol.answersA_eq`, `answersB_eq`, `privA_eq`, `privB_eq`, the four approved `pairFstD/pairSndD_privA/privB` rules, `coins_eq`, `realA_eq`, `realB_eq`, `polyTime_iff`, `hbcSecure_iff` | `SecureComputation/Hybrid.lean` |
| `Functionality.idealA_eq`, `idealB_eq`, `otFunctionality_inA/_inB/_outA/_outB/_f/_f_snd/_f_snd_apply` | `SecureComputation/Defs.lean` |
| `Strategy.efficient_iff`, `ofNUPPT_next`, `ofNUPPT_efficient`, `encodeMsgs_nil/_cons`, `pairFstD_encodeMsgs`, `View.encode_mk`, `Protocol.viewP_eq`, `viewV_eq`, `outV_eq`, `outP_eq`, `outV_eq_out`, `outP_eq_out`, `transcript_eq`, `transcriptWith_eq`, `exec_succ`, `exec_zero` | `ZeroKnowledge/Interaction.lean` |
| `keyAt_eq`, `argKeys_eq`, `garbledRow_eq`, `garbledTable_eq`, `tableAt_eq`, `tableAt_gate`, `evalGate_eq`, `inputKeys_eq`, `garbledValues_eq`, `garbledValues_getD`, `good_iff`, `gateOut_eq`, `gateOut_eq_eval`, `runWith_sim`, `GarbleSeed_eq`, `MultiEnc.decCorrect_iff` | `SecureComputation/Garbling.lean` |
| `nestedSpecial_enc`, `nestedSpecial_dec` (`simps`), `nestedSpecial_decCorrect`, `innerLen_eq` | `SecureComputation/GarblingSpecial.lean` |
| `spEncStr_eq`, `spDecStr_eq`, `spDecStr_spEncStr`, `length_spEncStr`, `runAt_spEnc`, `runAt_spDec`, `polyTimeComputable_spEncFun`, `polyTimeComputable_spDecFun` | `SecureComputation/SpecialEncryption.lean` |
| `PRFOut` (`easy`, `pseudorandom`) | `SecureComputation/SpecialEncryptionSecurity.lean` |
| `runWith` and its equations, `DAGCircuit.size_eq`, `length_values`, `values` readers; `DAGCircuit.encode_injective`, `size_le_length_encode`, `length_encode_le_of_isFaninTwo`; `encodeNat_def`, `decodeNat_encodeNat`; nearest relatives `DAGCircuit.decode`, `DAGCircuit.decode_encode`, `decodeList_encodeList` (`DAGCircuitSatLang.lean`) and `encodeList_eq_flatMap` (`UniformTableauEmitter.lean:256`, not in the order) | `Complexity/CircuitComplexity/{DAGCircuit,Uniform,UnaryCode,DAGCircuitSatLang}.lean` |
| `PolyTimeComputable.comp`, `.comp'`, `.pairEncode`, `.pairMapSnd`, `polyTimeComputable_ite`, `polyTimeComputable_iterate_pairFstD`, `polyTimeComputable_unaryPoly`, `polyTimeComputable_stateFind`, `polyTimeComputable_iterate`, `polyTimeComputable_iterateFind`, `polyTimeComputable_iterateEmit`, `polyTimeComputable_blockMap`, `BinArith.polyTimeComputable_mapW/_zipWithW/_countW`, `BinArith.decWords_encWords`, `NMSim.polyTimeComputable_chunkMap`, `NUPPT.polyTimeComputable_layout`, `NUPPT.exists_comp`, `exists_compParam`, `exists_withAdvice`, `exists_split` | `Complexity/ClassNP/{PolyTime,PolyTimePairing}.lean`, `Complexity/Randomized/{Primitives,Closure,Repetition}.lean`, `Complexity/ClassP/BinaryArith/*`, `Encryption/PublicKey/NonMalleability/Simulation/Generic.lean` |
| `uprob_mono`, `uprob_exists_le`, `uprob_prod`, `uprob_comp_equiv`, `uprob_fst`, `uprob_le_one`, `uprob_nonneg`, `acceptProb_def`, `acceptProb_comp_equiv`, `distAdv_def`, `distAdv_comp`, `distAdv_le_of_statClose`, `abs_sub_le_sum_hybrids`, `exists_hybrid_gap`, `Negligible.add`, `negligible_two_pow_neg`, `EnsembleLemmas.negligible_polyExpr_mul`, `OneWay.uprob_eq_one_div_card`, `OneWay.uexp_const`, `MultiMsg.abs_uexp_sub_le_uprob`, `HardcoreBit.pushesUniform_restrict`, `pushesUniform_comp_injective` | `Foundations/{Probability,Experiments,Negligible}.lean`, `Asymptotic/{Sampling,EnsemblesLemmas}.lean`, `Pseudorandom/Indistinguishability.lean`, `OneWayFunctions/Basic.lean`, `HardcoreBit/Basic.lean`, `FromPRF/HybridLemmas.lean` |
| `TCSlib.Cryptography.headD_drop_ofFn`, `flatten_ofFn_one`, `padFin_ofFn`, `PrivateKeyScheme.encodeList_nil/_cons`, `GI.pairSndD_encodeMsgs`, `GI.iterate_pairSndD_encodeMsgs` | `Foundations/BitLists.lean`, `Asymptotic/Adversary.lean`, `Encryption/PrivateKey/EnsembleSecurity.lean`, `ZeroKnowledge/GraphIsomorphism/EfficiencyRep.lean` |

## Scope

### The owned file: `Yao.lean` (shared with `sc-garble`; the stricter rule)

`SecureComputation/Yao.lean` has 942 lines at the base. You own **only**:

1. the bodies of the two targets (line 843 and line 918, each `  sorry`);
2. their `**Proof sketch.**` paragraphs, lines 826–840 and 860–906. Rewrite each to describe the
   delivered proof; it may point to the helpers' sketches. The statement prose before each sketch stays
   byte-identical, including the simulators' *Deviation: the joint PRF hypothesis* paragraph. The old sketch's
   "(not yet stated in the library)" is obsolete since #311, so drop it in the rewrite;
3. the `## Main results` bullet at lines 96–98. Split the two targets out as proved and leave
   `yaoSeed_good_whp` "(stated; `sorry` under a sketch)";
4. **(SY-1)** exactly one new line,
   `import TCSlib.Cryptography.SecureComputation.Yao.<Hub>`, inserted directly after line 9
   (`import TCSlib.Cryptography.Foundations.BitLists`).

Everything else in `Yao.lean` stays **byte-identical** to the base. That covers every other declaration, header,
body and docstring (in particular `yaoSeed_good_whp`'s sorried body and sketch), every import line, the
`set_option`s, the title (its "(statement phase)" is left for the maintainer's landing edit), the
`## Main definitions` list, every `variable`, `section`, `include`, `open` and comment. Add **no** declaration to
`Yao.lean`: no lemma, no `private` helper, no `abbrev`, `instance`, `local notation` or attribute.

**Line budget (SY-2).** `Yao.lean` has at most **972** lines at your final, a net change of at most
**+30**. sc-garble's delivery and its landing branch put the file at 970 lines (+28), so
the landed file stays at most 1000. To make room, the two sketch paragraphs (62 lines at base) may be
shortened. Do not compress proofs below readability, and keep every line at most 100 characters. If the bodies
cannot fit, stop that line of work and make a scope request (*Scope requests*), proposing SY-2 (B).

### Helper modules (SY-1): one hub, generic statements

**Placement.**
- Helpers go under `SecureComputation/Yao/<Hub>/` (and deeper, each deeper directory with its own facade beside
  it). The hub `SecureComputation/Yao/<Hub>.lean` imports every helper and carries a module docstring with a
  `## Contents` list. `Yao.lean` imports only the hub.
- Put **no other file directly under `Yao/`**. Once `Yao/` exists, the style lint treats `Yao.lean` as a facade.
  It then requires `Yao.lean` to import every child directly or through an intermediate facade beside its
  directory (`scripts/campaign_style_lint.py`, `check_facade`), so a second file under `Yao/` would need a second
  import line.
- `SecureComputation.lean` needs no edit (#305: a helper under `X/` is covered when `X.lean` imports it).
- Choose `<Hub>` and the helper names. Run the name-clash scan on them.

**Imports.** A helper may import any module of `order.txt` except `Yao.lean`, the modules downstream of it and the
in-flight files named below. Two are worth naming:
- `SpecialEncryptionMulti` (B1) is in the order, but `Yao.lean` does not import it today. Your hub brings it in;
- `Games/Efficiency`, `NonMalleability/Simulation/Generic` (`NMSim.chunkMap`), `GraphIsomorphism/EfficiencyRep`
  (history readers) and `CircuitComplexity/DAGCircuitSatLang` (the existing description decoder).

A helper never imports `Yao.lean`, `YaoReal.lean` or the facade, since that would be a cycle. Do not import
`ObliviousTransfer.lean` or `Compose*.lean`: they are in flight, and they belong downstream in `YaoReal.lean`.
Every import you add enters `Yao.lean`'s closure and `YaoReal.lean`'s, so prefer the lightest module that serves.
Any other import needs a scope request.

**Visibility (binding).** A helper that `Yao.lean` imports cannot name anything declared in `Yao.lean`:
`YaoCircuit`, `readBits`, `xorShift`, `assignIdx`, `yaoCoins`, `yaoSeed`, `yaoMsg`, `yaoAlice`, `yaoBob`,
`yaoHybrid`, `yaoFunctionality`, `yaoSeed_good_whp`, `yaoHybrid_correct`, and the rest. State each helper on the
library objects upstream: `DAGCircuit`, `garbledTable`, `evalGate`, `nestedSpecial`, `Strategy`, `Protocol`,
`HybridProtocol`, `Functionality`, `NUPPT` and `sliceMultiEncDist`. Yao's specifics enter as **parameters and
hypotheses**:
- the circuit family as its fields: `inA inB outLen sizeBound : PolyExpr`, `circ`, `outs`, with `outs_lt`,
  `outs_sink`, fan-in two, `size_le` and uniformity as hypotheses;
- the seed as a function `ℕ → List Bool → GarbleSeed …`, with the block equations of `yaoSeed_fst`,
  `yaoSeed_snd_fst`, `yaoSeed_snd_snd`, `readBits_apply` and `xorShift_apply` as hypotheses;
- the strategies and the hybrid protocol by their next-message, coin and call-input equations;
- the `Bad` bound of `yaoSeed_good_whp` and the conclusion of `yaoHybrid_correct` as hypotheses.

A `Prop`-valued structure that bundles these hypotheses is allowed, with `simps` readers. The bodies discharge the
hypotheses in `Yao.lean` with its published readers, or by `rfl`/`show` on `Yao.lean`'s own definitions. *Rule 10*
allows the owned file to read its own definitions. **Do not re-define** a `Yao.lean` definition in a helper, such
as a copy of `yaoSeed`, `yaoMsg` or `yaoHybrid`. A copied definition is duplication (*Duplication*). New objects
are of course defined in helpers, among them `S_A`, `S_B`, the fake garbling and the reductions.

**Frozen-file readers (SY-3, pre-approved; nothing else).** `IsFaninTwo` and the circuit encodings have no reader
at the base, so reading them would break Rule 10. You may add exactly these `rfl` readers, each directly after its
definition, with a formula docstring, no attribute, and names subject to the name-clash scan:
- in `Complexity/CircuitComplexity/DAGCircuit.lean`, **byte-identical to sc-garble's approved reader** (so that the
  hunk coincides at landing):

  ```lean
  /-- A circuit is fan-in two exactly when each gate has distinct arguments, each negation
  gate has one argument, and every gate has at most two arguments:
  `C.IsFaninTwo ↔ (∀ g ∈ C.gates, g.args.Nodup ∧ (g.kind = .not → g.args.length = 1)) ∧
    ∀ g ∈ C.gates, g.args.length ≤ 2`. [AB09, Definition 6.1] -/
  theorem isFaninTwo_iff :
      C.IsFaninTwo ↔
        (∀ g ∈ C.gates, g.args.Nodup ∧ (g.kind = .not → g.args.length = 1)) ∧
          ∀ g ∈ C.gates, g.args.length ≤ 2 := Iff.rfl
  ```

  The block is indented here only for the list. In the file it starts at column 0 and follows `def IsFaninTwo`'s
  body and its blank line, itself followed by one blank line: exactly lines 510–518 of sc-garble's delivered
  `src/TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean` (exchange `a73072f1`, identical in its landing
  branch);
- in `Complexity/CircuitComplexity/Uniform.lean`:
  - `encodeList f [] = [false]` and `encodeList f (a :: as) = true :: (f a ++ encodeList f as)`;
  - `GateKind.encode` at `.and`, `.or`, `.not` (`[false, false]`, `[false, true]`, `[true, false]`);
  - `g.encode = g.kind.encode ++ encodeList encodeNat g.args`;
  - `C.encode = encodeNat n ++ (encodeList DAGGate.encode C.gates ++ encodeNat C.output)`.

Each addition is a pure insertion, and removing it restores the base file byte for byte. Use them only where you
need them, and report which you added.

### The frozen-statement rule (binding; checked)

- **Headers.** Every declaration present at the issue base in `Yao.lean` (and in `DAGCircuit.lean` and
  `Uniform.lean`, if SY-3 is used) stays in the same file and order, with its header byte-identical. The header is
  the attributes and modifiers, the keyword, the name, the binders and the type, up to the `:=`, `by`, `where` or
  first `|` that begins the proof. `open … in`, `include … in` and `omit … in` prefixes are part of the header.
- **Definitions are statements.** A `def`, `abbrev`, `structure`, `inductive`, `class` or `instance` stays
  byte-identical, body included. Delete nothing, private declarations included.
- **What may change** is listed under *The owned file* and *Frozen-file readers*. Nothing else.
- **Check.** Write a `python3 -I` script. It extracts every declaration of the touched frozen files at the base and
  at the final, and compares headers (and whole definitions) byte for byte. It checks that the base declarations
  appear in the same order. For `Yao.lean` it also prints the full diff and shows that the diff touches only the
  four allowed regions and that the line budget holds. For the circuit files it shows that the diff is exactly the
  approved insertions. Deliver the script and its output under `evidence/headers/`, with zero unexpected
  differences.
  - Add two controls: a copy with one header altered by one character must report exactly one difference, and a
    copy with one extra line in a frozen region of `Yao.lean` must report exactly one region violation.
  - Do not let private or unnamed declarations, `include … in` lines or match-arm headers escape the count. Report
    the count (the lint counts 72 public and 4 private declarations in `Yao.lean`).

**Everything else is frozen.** That covers the rest of `SecureComputation/` (`Garbling*`, `SpecialEncryption*`,
`Hybrid`, `Defs`, `YaoReal`, and `ObliviousTransfer` and `Compose*` in flight), `Pseudorandom/*`, `Encryption/*`,
`Games/*`, `ZeroKnowledge/*` and the circuit and complexity libraries, apart from SY-3.

### Scope requests

If the route needs any other change to a frozen file, stop that line of work. That includes:
- another reader;
- a second import line or any declaration in `Yao.lean`;
- a body that does not fit the budget;
- a promotion;
- a new import outside the order.

Ask Seyoon in your session, giving the exact file, the diff and the reason, and go ahead only on his approval.
Record the request and his answer verbatim under `evidence/scope-request/` and in `REPORT.md` § *Scope requests*.
Seyoon prefers a route with no frozen-file edit where one exists. A lemma that belongs in an existing file goes in
your helper module, with a promotion request.

## Proof route and checkpoints

Write `S = sizeBound(n)`. The sketches in the targets' docstrings are the route. What follows fixes the
checkpoints and the obligations.

1. **Checkpoint 1 · poly-time infrastructure** (helpers only; whole declarations, all public):
   - **The description decoder** (a host, SY-4). It is a polynomial-time map from
     `pairEncode C.encode (Strategy.encodeMsgs …)` (the shape of `encodeCircuit_eq`) to a representation of the
     gate list and the output list from which the garbler and the evaluator compute. Give its correctness on every
     circuit description and its polynomial time on every string.
     - Reuse `DAGCircuit.decode`, `DAGCircuit.decode_encode` and `decodeList_encodeList` (`DAGCircuitSatLang.lean`)
       where they fit. Read the encodings through the SY-3 readers.
     - Uniformity then gives the circuit from `1^n` in polynomial time (`YaoCircuit.uniform`, passed as a
       hypothesis).
   - **Garbling from coins.** For a seed given by readBits-type block equations and a row order given by XOR
     shifts, the encoded tables `encodeMsgs (ofFn fun i => encodeMsgs (garbledTable (nestedSpecial E₁ E₂ n) C s i))`,
     Alice's input keys and the decoding pairs are polynomial-time from `⟨1^n, ⟨input, coins⟩⟩`. Use `hE₁`, `hE₂`
     and `polyTimeComputable_spEncFun`.
     - `garbledTable` enumerates the assignments with the noncomputable `Finset.univ.toList`. For at most two
       positions this is a fixed finite list, so prove polynomial time **for an arbitrary constant enumeration**
       and instantiate.
     - Fan-in two (SY-3's reader) bounds the arguments by `2`.
   - **The garbled evaluation host** (SY-4). `runWith` over the decoded gates with `evalGate` of `nestedSpecial`
     (`polyTimeComputable_spDecFun`) on tables decoded from an **arbitrary** message (`decodeMsgs`), then Bob's
     output decoding. Make it polynomial in the whole input, as `Strategy.Efficient` under D8 requires.
   - **Length bounds.** A row has at most `7n + 4` bits whatever `E₁`, `E₂` return (`take`/`zipWith` cap the
     pads). Alice's message has `O((S + inA(n) + outLen(n)) · n)` bits. Bob's has `outLen(n)`.
   - Send this checkpoint.
2. **Checkpoint 2 · `yaoHybrid_polyTime`.**
   - The four clauses of `polyTime_iff`, through a generic theorem in a helper:
     - the strategies are `Efficient` (`efficient_iff`, `ofNUPPT_next`, a uniform `NUPPT` with coin polynomial
       `yaoCoins` for Alice and `.const 0` for Bob, correct on **every** `x z r hist`);
     - the call inputs are polynomial-time: `(i, t) = finProdFinEquiv⁻¹ j`, and two coins at positions computed
       from `n`, `inA(n)` and `S`;
     - the message bound holds for any answers.
   - Then add the `Yao.lean` import line, the body and the sketch.
   - Send this checkpoint.
3. **Checkpoint 3 · views, the statistical parts and the simulators.**
   - The view and output equations of the two-move main phase of an OT-hybrid protocol, generic in the
     strategies: `viewP`, `viewV`, `outV`, `outP` and `View.encode` through their readers; `|1^n| = n` through
     `List.length_replicate`.
   - **`S_A`** (`yaoCoins(n)` coins; `⟨1^n, ⟨x, []⟩, r, [f]⟩`) and **Alice's side**: the real and ideal samplers
     agree off `Bad`, so the advantage is at most `δ(n)`, for all inputs. `δ` is `yaoSeed_good_whp`'s bound,
     passed in by the body.
   - **Bob's output switch**: off `Bad`, Alice's output is `f`, by `yaoHybrid_correct`, passed in.
   - **`S_B`**, the fake garbling with active keys `k_w^0`, the real enumeration and shifts, and the swapped
     decoding pairs, as a NUPPT. Prove its efficiency (uniformity map, `E₁`, `E₂`).
   - Send this checkpoint.
4. **Checkpoint 4 · the exact sampler identities.**
   - `H₀ = H₁` by the point-and-permute bijection of Alice's coins (keys `k_w^b ↦ k_w^{b ⊕ v_w}`, rows
     `a ↦ a ⊕ v_args`, shifts `λ_i ↦ λ_i ⊕ v_args`), closed with `uprob_comp_equiv`/`acceptProb_comp_equiv`.
   - `H₂,|gates|` equals `S_B`'s output up to renaming the active key as `k^0`.
   - Both identities are seed by seed, on stated coin equivalences.
   - Send this checkpoint.
5. **Final · the gate hybrid and `yaoHybrid_simulators`.**
   - **`H₂,ᵢ ≈ H₂,ᵢ₊₁`** by an embedding into B1 under `hG₁₂`, in at most two sub-steps per gate, one for each
     inactive argument key `ι_u`:
     - every row under `ι_u`, in **every** gate that reads `u`, is a challenge slot: `(0, n)` where `u` is a second
       or only argument (`sliceEnc_append_left`), and `(2n, 4n + 2)` where it is a first argument
       (`sliceEnc_append_right`);
     - pad to `q(n) + 1` slots, with `q` a polynomial bound such as `4 S(n)`; unused slots and rows whose plaintext
       does not change get equal messages;
     - an outer challenge plaintext is an inner ciphertext under another, sampled key, prepared before; an inner
       challenge ciphertext is wrapped afterwards under the known other key.
   - **The reduction.**
     - It is one NUPPT `D'`. Its advice at `n` is the worst `(x, y)`, the hybrid index and sub-step, the slices,
       and a fixing of all other randomness (the other keys, the other nonces, the shifts), chosen by averaging, so
       that the B1 messages `m, m'` are deterministic in the advice.
     - Its sampler identity: `D'` on `sliceMultiEncDist` is `D` on the two hybrids. It rebuilds the garbling and
       Bob's view in polynomial time.
   - **The total.** Use `exists_hybrid_gap`/`abs_sub_le_sum_hybrids` over the `2 S(n)` steps, with the index
     chosen by advice. Bob's bound is `δ(n) + 2 S(n) · ε_B1(n)`, negligible.
   - Then the body and the sketch.

**Gate 27's hand-off obligations for `sc-yao`** (`gates/27-b1-multimsg/resolutions-r1.md` item 4, and the findings
§ *Required handoff* item 4; obligations, not findings). Your delivery must show each, mapped to declarations in
`REPORT.md` § *Gate 27 hand-off*:
1. the gate and row sub-hybrids;
2. the enumeration of **all** occurrences of the selected key, with padding;
3. **the no-dependence argument**: in `H₂,ᵢ`, `ι_u` is only an encryption key. It is no plaintext (if `u` is a
   gate, that gate's table is already fake). It is in no decoding pair (`outs_sink`). It is not among Alice's keys
   or Bob's OT answers, which are active. `g.args.Nodup` prevents one row from using `u` twice;
4. the exact coin and view **sampler identities**;
5. **polynomial-time reconstruction** of the garbling and of the view by the reduction.

Gate 27 also recorded the following:
- the non-adaptive interface suffices, because no challenge plaintext needs an earlier challenge ciphertext;
- accidental equal values of independently sampled keys do not invalidate the simulation;
- the two nonce blocks of `nestedSpecial` are independent in `yaoSeed`;
- `distinguisherL n` runs at `1^n`.

Gate 31 checked the B1 consumer map. That map is sc-garble's, and `sc-yao` consumes only the frozen B1 statement:
do not rebuild D1–D4, a PRF hybrid or a collision bound.

**Edge cases.** Check:
- `n = 0`, and `inA`, `inB` or `outLen` equal to `0`;
- `|gates| = 0`, constant gates (no arguments: one row, no keys), gates with one argument (the shift reads one
  bit), and two arguments;
- output vertices that are input vertices, and output vertices that coincide;
- a wire read by several gates in different argument positions, which puts both slice shapes under one key;
- wires read by no gate, and coin blocks that are never read;
- arbitrary (malformed) histories, private inputs and tapes in `Efficient`;
- `x.length` versus `n` in the strategies;
- the noncomputable enumeration.

**Escalation.** If a sketch is wrong, a target is false as stated, or a frozen statement you cite does not fit,
stop and escalate with the exact obligation: a checkpoint with the counterexample or the missing fact. Do not
weaken any statement.

**Partial delivery.** If you cannot finish both targets, the final may prove `yaoHybrid_polyTime` alone. Deliver
every completed helper of the simulator route as whole declarations.
- A proved target uses only the standard axioms, apart from the cited sc-garble statements and base admissions
  (*Axioms*).
- An unproved target keeps its `sorry` and its base sketch.
- No helper contains `sorry`, and no new admission appears.
- `REPORT.md` says what remains, step by step.

## Proof discipline

- **Size and width.** Every line has at most 100 characters (Python `len`). Every file has at most 1000 lines,
  and `Yao.lean` keeps its budget (SY-2). Check both with a short `python3 -I` script before each push, and include
  its output in `evidence/`.
- **Duplication (binding).**
  - **Search first.** Before writing any lemma, search `TCSlib/` and Mathlib for its statement shape and key names.
    Reuse published lemmas by importing them.
  - **Probability, expectation and list identities first.** The undisclosed re-proofs that the last reviews and
    gates found were all of this kind:
    - prf-mac F-01: `prfAdv_eq_expect`;
    - learning: `OneWay.uprob_eq_one_div_card` and `MultiMsg.abs_uexp_sub_le_uprob`;
    - Gate 29 G29-01 and G29-02: `OneWay.uexp_const` and `headD_drop_ofFn`;
    - Gate 32 G32-01, the DL-47 family of `getD`/`headD` of `List.ofFn` copies: use
      `TCSlib.Cryptography.headD_drop_ofFn` (#316) and Mathlib's `List.getD_eq_getElem`/`List.getElem_ofFn`, and
      do not add a further copy. `Yao.lean`'s private `getD_ofFn'` is itself a DL-47 row; it cannot be reached
      from helpers anyway;
    - Gate 34 G34-01 and G34-02: `headD_drop` re-proofs and `length_ofFn_coins`.

    Before writing any advantage, expectation, statistical-switch, hybrid-sum, averaging (fixing randomness),
    push-forward, coin-relabelling or list-window lemma, search for:
    - `uprob_*`, `uexp_*`, `acceptProb_*`, `distAdv_*` (`distAdv_comp`, `distAdv_le_of_statClose`);
    - `abs_sub_le_sum_hybrids`, `exists_hybrid_gap`, `pushesUniform_*`;
    - the `NUPPT.coinsEquiv_*`/`coinsCongr_*` family;
    - for lists, `ofFn_drop_take`, `take_ofFn_castLE`, `flatten_ofFn_one`, `padFin_ofFn`, `encodeList_eq_flatMap`
      (the DL-46 family; do not add a further copy), `BinArith.decWords_*`, and `pairFstD_encodeMsgs` with its GI
      siblings.
  - **Private lemmas.** Never copy a private lemma silently. If you need one, re-derive it from published readers,
    keep its statement general, and disclose it.
  - **Disclose every overlap.** `REPORT.md` has a section **`## Overlap and reuse`**. For every new declaration
    that restates, specializes or re-proves existing material (public or private, TCSlib or Mathlib), give its
    nearest relative (`path:line`), the relation, and why it is not reused. Disclose inline re-proofs inside a
    proof (`have` blocks) the same way. List the searches you ran.
  - **Unmerged parallel work (SY-5).** The deliveries of sc-garble (`Garbling/CoinBlocks.lean`,
    `Garbling/Probability.lean`, the B2 lemma), #318 sc-ot (`ObliviousTransfer/{Efficiency,Shape,ViewA,ViewB,
    Simulators}.lean`) and sc-compose (`ComposeSecurity/{Efficiency,Lengths,Machines,Runs,Sim,Probability}.lean`)
    are not in your base. Where you need a lemma that exists only there, you may re-derive it in a general form.
    Disclose it in *Overlap and reuse* with its counterpart's path and name (exchange `a73072f1`, PR head
    `f62a25b3`, exchange `bdfdcb76`). The maintainer re-points it, proof only, after both have landed. Read those
    deliveries as working material only.
  - **Why.** Undisclosed duplication is a freeze violation, not debt. It held Gates 23, 24, 29 and 34.
  - **Nearest relatives here:**
    - `Yao.lean`'s own readers (usable only in the bodies);
    - the GI efficiency layer (`ZeroKnowledge/GraphIsomorphism/Efficiency*`) for strategies and history loops;
    - `DAGCircuit.decode` for the decoder;
    - `polyTimeComputable_stateFind`/`_iterate`/`_blockMap` for loops;
    - `MultiMsg.blockMapFun`, `NMSim.chunkMap` for block parsers;
    - `Equiv.piEquivPiSubtypeProd`, `Equiv.sumArrowEquivProdArrow` and the `uprob` product lemmas for coin
      bijections;
    - the CVAL machine (`CircuitEval*`, not reusable; say so where relevant).
- **Hosts first (SY-4).** The description decoder and the garbled-evaluation host are hosts in the sense of
  `policy.md` §1 (an evaluation scheme, an input device). Build each as a **public, generic contract**:
  correctness and polynomial time, stated on `DAGCircuit.encode` and `runWith` with a polynomial-time step, not on
  Yao. Put each in its own helper module. In `REPORT.md`, file a promotion request (to `Complexity/CircuitComplexity/`
  or the `Randomized` construction layer) and a registry-row request (`machine-library-design.md` §14). Never make
  one `private`.
- **Docstrings and sketches.** The last batches' landing edits were mostly LE-doc (formulas and sketches) and
  LE-width. Do these yourself:
  - every new public declaration has a docstring that states its formula: the equation or inequality, with its
    arguments in the Lean order. Add a source tag where it comes from the source (`[PS10, Protocol 162.6]`,
    `[PS10, Theorem 163.7]`, `[LP09]`, `[BMR90]`, `[Gol04, §7.3]`);
  - every proof of 15 lines or more carries a `**Proof sketch.**` paragraph, and long proofs get step comments
    (policy §3). Each target's sketch is rewritten to describe the delivered proof;
  - a new public `def` lands with its `_eq`, `_iff` or `simps` readers (lint check 8), and a new public `abbrev`
    with an `_eq` or `_iff` lemma;
  - add no `@[simp]`.
- **Rule 10.**
  - Use only published readers for other files' definitions, including generated matchers and projections: for
    example `garbledTable` through `garbledTable_eq`, `evalGate` through `evalGate_eq`, `Good` through `good_iff`,
    `nestedSpecial` through its `simps` readers, `spEncStr`/`spDecStr` through `_eq`, `sliceEnc` through
    `sliceEnc_eq`, `sliceMultiEncDist` through `_apply`, the samplers through `realA_eq`, `realB_eq`, `idealA_eq`
    and `idealB_eq`, `Strategy.Efficient` through `efficient_iff`, `View.encode` through `View.encode_mk`,
    `IsFaninTwo` and the circuit encodings through SY-3's readers.
  - Each helper module counts as foreign to the others. **Inside `Yao.lean`** its own definitions may be read
    directly (`rfl`, `show`), which is what the glue in the bodies does.
  - **Notation, never sealed:**
    - `PolyExpr.eval` (Q1);
    - reducible abbreviations (2026-10-26; for example `GarbleSeed`, `HybridProtocol.Coins`,
      `Protocol.ExecCoins`, `QueryImpl`);
    - **projection coercions:** a `CoeFun`/`Coe` instance whose body is a structure projection (Seyoon's ruling,
      2026-11-14).

    The coe-variant seals are canonical. Run the strict variant as well, and attribute each difference.

## Checks and report

- **Bootstrap.**
  - Bootstrap from `order.txt` (184 modules) and the narrow `roots.txt` (76), following the
    addendum.
  - The order is the upstream closure of the modules downstream of `Yao.lean` (`YaoReal`, the `SecureComputation`
    facade; root `TCSlib` excluded), and of the extras helpers may import (`Games/Efficiency`,
    `NonMalleability/Simulation/Generic`, `GraphIsomorphism/EfficiencyRep`, `CircuitComplexity/DAGCircuitSatLang`).
  - Check one module per `scripts/lean_check_tree.sh` call, with one Lean process per olean tree (on Seyoon's Mac,
    through `lean-slot.sh`).
  - Never run `lake build` or an unfiltered cache get. Run Python as `python3 -I`.
  - Insert helper modules before their consumers.
- **Sweep.**
  - Recheck `Yao.lean`, every helper and any SY-3 file, then sweep the supplied order with 0 errors.
  - Compare the `sorry` warnings with `base-sorries.txt` (32 declarations in 15 modules). The only
    change must be the removal of the two targets (30 in 15 modules: `Yao.lean` keeps
    `yaoSeed_good_whp`; a partial final, 31 in 15).
  - **Name-clash scan.** No new public or private name may already be declared, with namespaces resolved and
    private names counted:
    - anywhere in `TCSlib/` at the issue base. Mind `Yao.lean`'s private `encodeMsgs_inj`, `encodeNat_inj`,
      `getD_ofFn'` and `yaoBobOut_yaoMsg_of_eq`: your helpers are upstream of `Yao.lean`, so a public helper of the
      same full name would make the private one fail to declare (the DL-46 class);
    - in sc-garble's final `src/` (exchange `a73072f1`), #318's head `f62a25b3` and sc-compose's final `src/`
      (exchange `bdfdcb76`), which land before or beside you. The one expected coincidence is SY-3's
      `isFaninTwo_iff`, byte-identical to sc-garble's.

    Deliver the script and its output under `evidence/clash/`.
- **Axioms.**
  - Print the axioms of both targets and of every stored constant of the changed and new files.
  - Run a **dependency trace**, a probe that walks the constant closure and lists every sorried constant it reaches.
    - `yaoHybrid_polyTime` should reach none, or only base admissions of the complexity layer; name them if any.
    - `yaoHybrid_simulators` should reach exactly `yaoSeed_good_whp` and `sliceMultiMessageSecure_of_prfOut` (and
      their own closures), plus any base complexity admission, named.
    - No helper reaches any sorried constant other than these.
  - Print, at base and final, the axioms of `yaoHybrid_hbcSecure` and `yaoProtocol_hbcSecure`, and say which
    admissions they still reach and from which unit.
- **Headers.** The check of *The frozen-statement rule*, with its controls.
- **Rule 10 evidence.**
  - Run whole-file seals A and B of every changed or new file over its full TCSlib import closure, at base and
    final, with `-DmaxErrors=0` (C-F02).
  - Run both the **strict** and the **coe** variant (projection coercions sealed, or treated as notation). Report
    every failing declaration in each.
  - Add paired controls that pass unsealed and fail sealed, each sealed negative failing exactly once.
  - Run the explicit-unfold scan.
  - Report the seals with `PolyExpr.eval` both excluded as notation and sealed. Attribute every seal-B failure by
    reading its raw log; do not summarize new B failures as "where the base fails" (Gate 31).
  - **Error counts (G26-N1), both forms.** Your runner must count both diagnostic forms, `error:` and `error(…)`,
    for example with `^\S+\.lean:\d+:\d+: error[:(]`, in every seal, control, sweep and probe log. Keep every raw
    log.
- **Lint.**
  - Run `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography --check8b` at base and at final. Run it on
    `TCSlib/Complexity/CircuitComplexity` as well if SY-3 is used.
  - The baseline at the issue base is **92 FAIL / 101 WARN** over 350 files, re-run by the maintainer at
    `6ce4658d`.
  - Diff the line sets, not only the counts. There must be no new FAIL line, and no new WARN line except one you
    disclose and justify. `Yao.lean` becomes a facade for the lint once `Yao/` exists, so its INFO size line
    disappears. That is expected; say so.
- **Report.** `REPORT.md` gives:
  - the base, and the status of each target;
  - the changed and new files, with lines at base and final; `Yao.lean`'s line count against the budget; the
    sketch edits;
  - the new declarations with their final signatures, and the interface theorems the bodies instantiate in full;
  - **Interface (SY-1)**: each hypothesis of the generic theorems and the reader or `rfl` that discharges it;
  - **Gate 27 hand-off** (each obligation mapped to declarations);
  - **Overlap and reuse** (including SY-5 rows);
  - **Scope requests** (none, or each with Seyoon's answer), and the SY-3 readers used;
  - the host, promotion and reader requests (SY-4);
  - the evidence, with its manifest.

### Evidence completeness

Gate 20 held a delivery for omitted raw evidence (G20-01).
- Every file that `evidence/SHA256SUMS` names must be delivered. That includes:
  - seal and control sources, manifests and request records;
  - the header-check script, its output and its controls, and the name-clash scan;
  - the dependency trace;
  - every raw log and `results.jsonl`;
  - the probe sources and the tools used.
- If the evidence is too large for one commit, deliver it in several commits, or as numbered ZIP parts, each part
  with an entry list. Do not leave anything out for size.
- Check before delivery that the delivered paths are exactly the manifest's (top level and `evidence/`), with no
  leading `./`.

The maintainer checks `TCSlib` and `audits/pass-shelat/Checks` on the full-library tree at landing, after
sc-garble lands, on the then records tip.

## Open rulings (asked at staging; answers in `ruling-SY.md`)

Recommended option first. The brief is written for the recommendations.

- **SY-1 · import line and helper architecture.** `Yao.lean` imports nothing under `Yao/` today, so helpers are
  unreachable without an edit. (A) Pre-approve exactly one hub import line, with the generic, interface-style
  helpers above. (B) First a maintainer PR, statement-preserving and gated, that moves everything before
  `section Security` into an upstream `Yao/` module, so that helpers can name Yao's definitions; then one import
  line. This conflicts with the standing never-split rule and delays dispatch.
- **SY-2 · line budget.** (A) Net change of at most +30, so the landed file stays at most 1000 after sc-garble's
  +28; the sketches may be shortened. (B) At most 1000 at sc-yao's final on the issue base (+58); the landed file
  may reach about 1,028, recorded under the standing size rule. (C) Waive the cap under the standing rule, up to
  1,200.
- **SY-3 · frozen-file readers.** (A) Pre-approve the readers above: `isFaninTwo_iff`, byte-identical to sc-garble's,
  and the `Uniform.lean` encoding readers. (B) Only `isFaninTwo_iff`; the encoding readers by scope request. (C)
  None; all by scope request.
- **SY-4 · hosts first.** (A) Public generic contracts in sc-yao helpers, with promotion and registry requests at
  landing. (B) Statement-gate the two host contracts in a maintainer PR before dispatch, consumed proved-modulo.
  (C) Treat them as ordinary helper lemmas.
- **SY-5 · overlap with unmerged parallel deliveries.** (A) Pre-approve disclosed general re-derivations, re-pointed
  proof-only after landing. (B) Forbid them; stop and ask each time.
- **SY-6 · worker.** (A) Codex on Seyoon's Mac, single agent, under the host addendum. (B) Claude (the standing
  ruling's default).

**Ready to dispatch after rulings SY-1–SY-6**
