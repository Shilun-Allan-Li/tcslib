### Concrete simulator assembly and premise discharge (agent a)

The complete a12 prototype preserves the full frozen target signature, including
`G₁`, `G₂`, both evaluator equations, both efficiency hypotheses, and all three PRF
hypotheses. Its checked body is124 lines (maximum width93); the computational `hBob`
instantiation is25 lines. It introduces no new admission or global Yao semantic definition.

`S_A = AliceSimulator.simulator (yaoCoins Y)`. `FakeSimulatorFactory.exists_simulator`
constructs one uniform `S_B` with the same coin polynomial and the exact ideal-view word
contract; both machines are chosen before the distinguisher and inputs. The factory uses
`Y.uniform`, `Y.circ`, `Y.outs`, `Y.outs_lt`, both actual evaluator algorithms and their
proved efficiency. Its description equation uses `encodeCircuit_eq` and
`encodeMsgs_eq_encWords`; its input-range equation is reflexivity under polynomial notation.
Arity follows from `DAGCircuit.isFaninTwo_iff` applied to `Y.fanin`.

| Premise | Actual instantiation/readers |
| --- | --- |
| Key blocks | `yaoSeed_fst`, `keyAt_eq`, `dif_pos`, `readBits_apply`. |
| Both nonce halves | `congrArg Prod.fst/snd (yaoSeed_snd_fst ...)`, `readBits_apply`, `assignIdx_eq`. |
| Row shifts | `yaoSeed_snd_snd`, `xorShift_apply`, `readBits_apply`. |
| Input wire values | `values_getD_input`, `Fin.castAdd/natAdd`, `Fin.append_left/right`, and public `ofFn` list readers. |
| Actual Bob view | `BobStageZero.acceptProb_eq_stage0`, with `yaoAlice_next_nil`, `yaoHybrid_answersB_getD`, main/coin/call readers, and `yaoMsg_eq`/`yaoTables_eq`/`yaoKeysA_eq`/`yaoPairs_eq`. |
| Ideal endpoint | `SamplerEndpoints.acceptProb_end_eq_ideal` and the factory's exact ideal word contract. `yaoCoins_eval`, `NUPPT.coinsEquivPoly_symm_ofFn`, and `ofFn_arrowCongr_finCongr` preserve the tape word. |

The negligible bad-event bound is the frozen `yaoSeed_good_whp` instantiated with the
actual `hGE₁`, `hGE₂`, `hG₁`, `hG₂`. `yaoHybrid_correct` supplies both off-bad output
equalities. `AliceStatistical.distAdv_real_ideal_le` and
`BobStatistical.statClose_real_output_switch` discharge the two statistical steps.

The computational call is `GateHybridSecurity.endpoint_negligible` with input family
`(Fin (Y.inA.eval n) → Bool) × (Fin (Y.inB.eval n) → Bool)`, counts
`S=Y.sizeBound`, `A=Y.inA`, `B=Y.inB`, `O=R=Y.outLen`, seed `yaoSeed Y`, output
selector `Y.outs`, wire values `((Y.circ n).values (Fin.append x y)).getD · false`,
Bob word `ofFn y`, and outer Alice word `ofFn (Y.output n x y)`. `Y.size_le`,
`Y.fanin`, `GateHybrids.values_consistent`, `Y.outs_sink`, and `List.length_ofFn`
discharge its structural/word bounds. The joint generator is exactly
`Fin.append (G₁ n s x) (G₂ n s x)`, with
`L = .add (.add .var .var) (.add .var innerLen)`. `List.ofFn_fin_append` proves its
word equation; public `PolyExpr.eval_add/mul/const/var` and `innerLen_eq` establish
`7*n+2 ≤ L.eval n`. B1 is exactly `sliceMultiMessageSecure_of_prfOut hG₁₂`.
`simulators_of_output_switch` combines the resulting computational bound with the
statistical bound. No assumed fake-message or active-answer efficiency remains.

### Verification and ownership qualification

The generic helper passes its normal check and all four full-file A/B × strict/coe seals.
Both stored helper constants have empty sorry closures and only `propext`,
`Classical.choice`, `Quot.sound`. The complete prototype's final normal check has zero
errors/warnings, and both owner-context canonical A seals pass. A genuine initial A issue
(implicit expansion of foreign `distAdv` at the final bound) was repaired with an explicit
`distAdv_def` rewrite; all affected checks were rerun and both versions are retained.

Each diagnostic B variant has9 errors:2 already in the unchanged PRF signature,
3 further polynomial add-index mismatches, and4 dependent-constructor cascades.
These arise when B deliberately seals the explicitly exempt `PolyExpr.eval` notation;
they are individually attributed in `a12/B-ATTRIBUTION.json`, not reported as passes.
Both error forms were counted with `-DmaxErrors=0`.

The prototype seals exempt exactly `TCSlib.Cryptography.SecureComputation.Yao` to emulate
its future owner-local theorem body; all other imported TCSlib definitions are sealed.
This is an owner-context prototype audit, not a substitute for the lead's final full-source
`Yao.lean` normal/seal checks after installing the body.

The focused trace visits18544 dependencies, excludes the old `yaoHybrid_simulators`,
and finds exactly these two authorized frozen admitted declarations:

* `TCSlib.Cryptography.SecureComputation.yaoSeed_good_whp`;
* `TCSlib.Cryptography.SecureComputation.sliceMultiMessageSecure_of_prfOut`.

Thus the prototype is proved modulo sc-garble, with no new admission. Canonical source:
`a12/probes/CompleteSimulators.lean`, SHA256
`2438566d0ccd1ec9b4b40e1e12b4d4dc5fc4e98f1db5741e1603d4c079b7d300`.
Generic helper SHA256:
`197cdfbe60aa5ee5fffb13f45f62c4d3eacb51cbf9fa00f78a3220c337ca5170`.
