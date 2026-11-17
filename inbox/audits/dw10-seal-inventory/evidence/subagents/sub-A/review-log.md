# sub-A review log: DW-10 classification review (SecureComputation, ZeroKnowledge)

Reviewer: sub-A. Inputs: the frozen snapshot `snap-r1` (open-items.tsv, seal-errors.jsonl, readers-v4.json,
readers-structs.json) and the read-only base worktree `subA`. No Lean, lake, git or network was used. Nothing was
written outside this directory.

Output: `overrides-A.tsv` (290 rows, one for each open item whose `agent` is `sub-A`). Working files:
`work/decisions.tsv` holds the per-declaration rulings and `scripts/expand.py` turns them into the per-row table.
`scripts/dossier*.py` and `work*/` are the dossiers I read.

## Scope and method

- **Agent filter.** The brief said `agent == A`, but no row has that value. The 290 rows with `agent == sub-A` lie
  in SecureComputation and ZeroKnowledge. The coordinator confirmed that these are the intended rows.
- **Harness rows.** None of the 290 rows has a `<outside src:N>` declaration or the "failed to set
  `[local irreducible]`" message, so the HARNESS note was never needed.
- **Reader index.** The coordinator asked for `readers-v4.json`, and I used it throughout. Rows done before that
  message were checked again against v4. I also grepped the sources for readers that v4 still misses because they
  are not named `<def>_*` or `<field>_<def>`:
  - `GI.mem_Lniso_iff` and `GI.mem_Liso_iff`
  - `EnsembleLemmas.ofFn_padFin_eq_padL`
  - `decGraph_fst` and `decGraph_snd_apply`, which are indexed but were never picked by the tool
- **Seal items.** For each declaration I read every coe-A error in seal-errors.jsonl and the source around it, and
  identified the definition that is actually unfolded at the failing step. A failure counts as a statement failure
  only when the header itself fails to elaborate. An error reported on the last header line counts as a proof
  failure when it belongs to the proof term on that line:
  - the term after `:=`, such as `:= rfl`
  - `fun T => by`
  - `unsolved goals` reported at the `by` token
- **Unfold items.** I checked the tactic at the scan line and whether the published reader really replaces it at
  that step.
- **SEAL-B-ONLY rows.** I checked that the counts are B-only (`coe_A = strict_A = 0`) and that the coe-B error is
  a PolyExpr.eval read or a cascade from one. All 31 rows hold. No row needed STRICT-ONLY.

## Counts per file (rows reviewed)

| File | Rows |
|---|---|
| SecureComputation/GarblingSecurity | 2 |
| SecureComputation/GarblingSecurity/NestedBounds | 1 |
| SecureComputation/SpecialEncryptionMulti | 1 |
| SecureComputation/SpecialEncryptionSecurity | 5 |
| SecureComputation/SpecialEncryptionSecurity/WrongKey | 1 |
| SecureComputation/Yao | 9 |
| SecureComputation/Yao/HybridProof/GarbledRun | 1 |
| ZeroKnowledge/Commitment | 16 |
| ZeroKnowledge/CommitmentLemmas | 8 |
| ZeroKnowledge/Defs | 16 |
| ZeroKnowledge/EncodingPermutations | 7 |
| ZeroKnowledge/GraphIsomorphism | 33 |
| ZeroKnowledge/GraphIsomorphism/Concrete | 4 |
| ZeroKnowledge/GraphIsomorphism/Efficiency | 1 |
| ZeroKnowledge/GraphIsomorphism/EfficiencyRep | 6 |
| ZeroKnowledge/GraphIsomorphism/EfficiencyRepGI | 3 |
| ZeroKnowledge/GraphIsomorphism/Soundness | 7 |
| ZeroKnowledge/GraphIsomorphism/SoundnessRep | 13 |
| ZeroKnowledge/GraphIsomorphism/SoundnessRepGI | 9 |
| ZeroKnowledge/GraphIsomorphismZK | 6 |
| ZeroKnowledge/GraphIsomorphismZK/Closeness | 18 |
| ZeroKnowledge/GraphIsomorphismZK/Simulator | 8 |
| ZeroKnowledge/InteractiveProofs | 10 |
| ZeroKnowledge/NP | 9 |
| ZeroKnowledge/NPLemmas | 17 |
| ZeroKnowledge/ThreeColoring/Parties | 1 |
| ZeroKnowledge/ThreeColoring/Protocol | 16 |
| ZeroKnowledge/ThreeColoring/ProtocolProofs | 11 |
| ZeroKnowledge/ThreeColoring/Simulator | 17 |
| ZeroKnowledge/ThreeColoring/SimulatorMachine | 14 |
| ZeroKnowledge/ThreeColoring/SimulatorNumeric | 20 |

By channel: 250 seal rows (117 distinct declarations outside SEAL-B-ONLY, plus 31 SEAL-B-ONLY rows) and 40 unfold
rows. There were no eqn rows.

## Result

**Class changes.** 23 rows move from STATEMENT to STAGE2, all with statement_level changed from yes to no. No
other class changes.

**Final classes.**

| Class | Rows |
|---|---|
| STAGE2 | 259 |
| SEAL-B-ONLY | 31 |
| STAGE2-PROVIDER-READER | 0 |
| STATEMENT | 0 |
| STRICT-ONLY | 0 |

**Fix column.** The fix differs from the tool's in 199 rows. There are four reasons:

- The provider was corrected, because the tool's reader targets a definition that is not read at the failing step
  (about 105 rows).
- The provider was identified where the tool had none (13 rows).
- A partial fix was completed (about 33 rows).
- The reader name was made concrete for a tool "add X_eq (or _iff/_apply)" (15 rows).

The fix is unchanged in 91 rows.

No STAGE2-PROVIDER-READER is needed. Every read of a non-owner Complexity definition already has a published
reader:
- `pairSndD` via `pairSndD_of_pairDecode_eq_none` with `Turing.pairDecode_nil`
- `Turing.pairEncode_eq`
- `MultiTapeTM.indicator_def`

## Patterns

1. **Single-line `:= rfl` or term theorems were classified STATEMENT (23 rows).** The tool flags the row because
   the error's source_line equals the header's last line. In every case the failing term is the proof on that
   line, and the header elaborates. Examples:
   - `decGraph_snd ... := rfl`
   - `giProver_efficient : giProver.Efficient := GI.giProver_efficient`
   - `liftVerifier_coinLen`
   - `colProtocol_outV`
   - `gniProtocolRep_outV`
   - `statClose_giHonestView ... := fun T => by`
   - `acceptProb_distinguisher(L)_of_runAtL`, where the error is `unsolved goals` at the `by` on the last header
     line

   The tool is also inconsistent here. It classified the same `unsolved goals at by` shape as STAGE2 for
   `giVerifierRep_next_end_enc` and `attemptStr_ofFn`. If column information is available, the lead may want to
   use it to settle header-line errors mechanically.

2. **Shadow transfer (39 rows).** These rows are flagged SHADOW-TRANSFER in their notes. Three groups of files
   restate main-file definitions verbatim in an inner namespace:
   - `GraphIsomorphism/Proofs.lean` (GI.\*)
   - `ThreeColoring/ProtocolProofs.lean` (ColProofs.\*)
   - `GraphIsomorphismZK/Simulator.lean` (GIZK.\*) and `ThreeColoring/SimulatorNumeric.lean` (ColSimMachine.\*)

   The main file then takes results over by definitional equality, as in `X_efficient := GI.X_efficient` and
   `gni_interactiveProofErr := GI.gni_interactiveProofErr ..`. Under the seal the shadows are sealed, so every
   transfer fails, and the tool's "efficient_iff" or STATEMENT is wrong for them.

   The Stage 2 fix is a bridge `X = GI.X` in the main file, proven from the shadow's readers. Where the shadow's
   readers are complete the row says "use":
   - GI.giProverRep (`_coins`, `_next`)
   - GI.gniVerifierRep (`_coins`, `_next`)
   - GI.giProtocolRep (`_P`, `_V`, `_rounds`, `_verifierFirst`)

   Otherwise the row names the reader to add (mostly the shadows' `coins` fields, protocol `rounds` and
   `verifierFirst`, `permFailBound_def` and `instanceVertices_def`). For ColProofs the published `next` readers
   have the string-machine form (`proverStr` on `ilayout`), so body-form `next` readers are needed.

   **Seyoon:** whether Stage 2 should bridge each shadow (one structure equation per shadow) or take a different
   route for the shadow layer is a design question. I have not decided it.

3. **Field reads of `ofPolyTimeUniform`.** `rfl : (NUPPT.ofPolyTimeUniform hF c).coins = c` fails in:
   - `exists_retrySimulator`
   - `GIZK.exists_simulator`
   - `ColSimMachine.exists_simulator`
   - `npProtocol_efficientP` and `npProtocol_efficientV`

   The reader is the field equation `Complexity.NUPPT.coins_ofPolyTimeUniform`. The tool's `uniform_iff` or
   `advInput_eq` is wrong for these.

4. **Definitional unfolds introduced by `intro` or an anonymous constructor.** Statements of the form
   `intro T`, `intro c`, `intro V' hV'`, `⟨..⟩` or `obtain ⟨..⟩ := h` act on a Prop definition:
   - StatClose: use `statClose_iff`
   - Negligible: use `negligible_iff`
   - ZK: use `ZK_iff`
   - StatZK: use `StatZK_iff`
   - Strategy.Efficient: use `efficient_iff`
   - Strategy.ReadsPrefix: no reader yet; add `readsPrefix_iff`
   - NUPPT.Uniform: use `uniform_iff`

   The tool often named an unrelated provider here, for example `ofPolyTimeUniform` for `perfectZK_zeroRounds`,
   `Riso_eq` for `gi_statZK` and `HVZK_eq` for `gi_hvzk`.

5. **The tool picks the first provider even when it occurs identically on both sides.** Examples:
   - `pairFstD_eq` or `pairSndD_eq`, where the read is GI.encInstance, GI.gniProver or edgeMsg
   - `polyTimeComputable_iff` for ColSimMachine nV, mE, baseR, vIdx, kPos, chunk and opnStr, whose defining
     readers are missing in SimulatorNumeric.lean
   - `decGraph_eq`, where `decGraph_fst` or `decGraph_snd_apply` is the exact reader
   - `mergeAt_def`, where the read is colCommit with multiCom
   - `exec_succ` in the zero case of `exec_congr`, which needs `exec_zero`

6. **Unfold scan.** 34 of the 40 unfold rows are confirmed as the tool gave them. Four have a corrected reader:
   - C1-0306: `fisherYates_succ` does not give the foldr; add `fisherYates_def`.
   - C1-0320: the published `View.encode_mk` covers the constructed views.
   - C1-0327: the published `firstIdx_eq_of_forall`, vacuous at 0, is enough.
   - C1-0338: `ofFn_padFin_eq_padL`, not `padL_eq`.

   Two are false positives, described below.

## Readers to add (owner files), as named in the fix column

| File | Readers |
|---|---|
| Pseudorandom/GeneratorFromPermutation.lean | `owpPair_apply`, `owpGen_apply`, `owpGenNot_apply` |
| Asymptotic/EnsemblesLemmas.lean | `EnsembleLemmas.swapAux_apply` |
| Asymptotic/Permutations.lean | `fisherYates_def`, `permFromCoins_def` |
| ZeroKnowledge/Interaction.lean | `Strategy.readsPrefix_iff` |
| ZeroKnowledge/EncodingPermutations.lean | `EncodingMachines.trialIdx_def` |
| ZeroKnowledge/GraphIsomorphism.lean | `decGraphAt_apply`, `permCoinLen_eq`, `encInstance_eq`, `giProver_next`, `instanceVertices_def` |
| GraphIsomorphism/Proofs.lean | `GI.permFailBound_def`, `GI.instanceVertices_def`; the shadow `coins` readers `GI.{giProver,giVerifier,gniVerifier,giVerifierRep,gniProver}_coins`; `GI.giProtocol_{rounds,verifierFirst}`; `GI.gniProtocol_{rounds,verifierFirst}`; `GI.gniProtocolRep_{P,rounds,verifierFirst}` |
| GraphIsomorphismZK/Simulator.lean | `GIZK.simCoins_def` |
| ThreeColoring/Language.lean | `edgeMsg_def` |
| ThreeColoring/ProtocolProofs.lean | `ColProofs.finOneEquiv_apply`; `ColProofs.{colProver,colVerifier,colProverRep,colVerifierRep}_coins` with body-form `_next` |
| ThreeColoring/SimulatorLemmas.lean | `ColSimLemmas.attemptCoinsEquiv_symm_apply`, `ColSimLemmas.truncAttempts_def` |
| ThreeColoring/SimulatorNumeric.lean | `ColSimMachine.{simCoins,blockPoly,nV,mE,baseR,vIdx,kPos,edgePos,chunk,opnStr}_def` |

Optional, in a provider file outside the campaign: `Complexity.pairSndD_nil` in `ClassNP/PolyTimeBlockLoop.lean`,
next to `pairFstD_nil`. It is not required, because published readers already cover the four pairSndD rows.

## False positives (unfold scan)

Two rows are not debt. They are kept as STAGE2 with fix "none" because the brief has no class for this case. The
lead should drop them.

- `NEW|..SpecialEncryptionMulti.lean|..sliceMultiMessageSecure_of_prfOut|unfold|301 dsimp Complexity.P`: the `P`
  is a local `let P` at l.290.
- `NEW|..Yao/HybridProof/GarbledRun.lean|..garbledRunWith_poly|unfold|117 simpa Complexity.P`: the `P` is a local
  `let P := PolyExpr.normal Cn cn` at l.111.

The scan resolved the bare name `P` to `Complexity.P`.

## Unresolved cases (need a Lean check)

- **SEAL-0318 and SEAL-0319** (`CommitmentLemmas.acceptProb_distinguisher_of_runAtL` and
  `acceptProb_distinguisherL_of_runAtL`). The proof failure is certain, so these are STAGE2 with statement_level
  no. The read is not certain. After `simp only [distinguisherL_eq, runAt_eq, hofn, hrun]` the residual goal has
  two identical printed sides, so the difference is a hidden implicit argument. It is most likely the coin-length
  index through NUPPT.coinLen.
- **H:202 and SEAL-0374** (`GI.giRep_accept_le`). The `show` at l.425 most likely fails on the coin-length cast in
  `giRepCoins` (`giProtocolRep.V.coinLen`), for which `GI.giProtocolRep_V_coinLen` is the reader. The tool's
  `decGraphAt_apply` does not fit.
- **H:259 and SEAL-0425** (`statClose_colSimTruncH`). The message is truncated at 4000 characters in
  seal-errors.jsonl. Read from the proof, the failing identification is local `firstSome` against
  `ColSimLemmas.truncAttempts`, so the fix is to add `truncAttempts_def`. The tool's `statClose_iff` does not
  address this step.
- **Shadow transfer** (pattern 2, 39 rows). The fixes are concrete, but the approach is a design question for
  Seyoon.

## Surprising items

- Several SEAL-B-ONLY rows fail under seal B in the header, not the proof:
  - `nestedSpecial_wrongKeyBot`, `garbling_good_whp`, `PRFOut`, `prfOut_var_iff`
  - `specialScheme_multiMessageSecure`, `specialScheme_wrongKey`
  - `exists_negligible_prefix_collision`, `owpComStr_ofFn`, `outV_pullback_cheat`

  I kept them SEAL-B-ONLY with statement_level no as the tool gave, per the brief. The separate PolyExpr.eval
  ruling should know that its fix touches statements: `PRFOut (.add .var .var) G` with `G : .. → Fin (n + n) → ..`.
- `GI.length_pairSndD_le` re-proves the published `Complexity.length_pairSndD_le`.
- In several CommitmentLemmas and Commitment cases the tool's provider list contained the real provider, but its
  reader pick went to a different definition from the same list. One example is `exists_bitRed_bound`, which needs
  `acceptProb_def` and not `FunFamily.blocks_apply`.
