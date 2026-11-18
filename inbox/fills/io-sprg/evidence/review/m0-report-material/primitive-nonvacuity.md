## Rule 15: primitives and their efficiency fields

Source snapshot: `2af7d5111f63dcb24a498dbddcf76b1d26c591ef` (candidate HEAD observed
read-only after the instance-reader additions). Paths in the tables are relative to
`TCSlib/Cryptography/Obfuscation/StructuredSeed/`. These tables record source-level
contracts; this reviewer ran no Lean, Lake, cache fetch, build, seal, or axiom command.

| Primitive / algorithm layer | Exact uniform efficiency fields | Raw layer and actual sampler law | Construction from targets |
| --- | --- | --- | --- |
| `BoolPRG` (`BoolPRG.lean:48`) | `eval_eff` (`:92`) chooses one `PolyTimeComputable` string map before all `n`, indices, and Boolean seeds. `idSamp_eff` (`:97`) is the shared `CoinSampling.SamplesEfficiently` contract for its supplied `IdDraw`, `encIdDraw`, `encIdx`, and `idCore`. | The input primitive itself carries the algorithm data. `BoolPRG.idSamp` (`:122`) is exactly the pushforward of one uniform `IdDraw` through `idCore`, with proved reader `idSamp_eq` (`:126`). It is not a disconnected arbitrary sampler field. | This job assumes a `BoolPRG`; it constructs no new value of that type. Its evaluator and sampler witnesses are mandatory input data. |
| `LPNFamily` (`LPN.lean:397`) | `sample_eff` (`:399`) is shared `SamplesEfficiently` for the exact joint matrix/secret/noise draw, parameter word `sampleWord`, draw/output encodings, and `sampleCore`. | `LPNFamily.Raw` (`:77`) fixes samples, public modulus, exact noise denominator, polynomial bounds, canonical `toLWE` (`:134`), `adv` (`:163`), and `Assumption` (`:172`). Its complete draw is `Raw.Draw` (`:186`), its actual core is `sampleCore` (`:303`), and `sampleLaw` (`:314`) is the exact one-draw pushforward. | `Params.lpnFamily` (`Targets.lean:279`) extends `P.lpnFamily_raw pi` with the field furnished by `lpnSamplerEfficient_of_target` (`:269`), from T6. `lpnFamily_toRaw` (`:285`) is proved `rfl`. |
| `SPRG` (`Defs.lean:393`) | `eval_eff` (`:394`) is `toRaw.EvalEfficient`; `idSamp_eff` (`:395`) and `sdSamp_eff` (`:398`) are shared `SamplesEfficiently` contracts on the exact raw index and seed draws and their cores. | `SPRG.Raw` (`:97`) stores all honest algorithm data, explicit finite-coordinate equivalences, and encodings. `Raw.idSamp` (`:179`) and `Raw.sdSamp` (`:188`) are derived exact uniform-draw pushforwards. `Raw.EvalEfficient` (`:314`) chooses one map before all parameters, with the public modulus in its input. | `jlsSPRG` (`Targets.lean:301`) extends `jlsSPRG_raw P pi`; T1 supplies `eval_eff` via `evalEfficient_of_target` (`:238`), T3 and T5 supply both sampler fields via `idSampEfficient_of_targets` (`:245`) and `sdSampEfficient_of_targets` (`:257`). `jlsSPRG_toRaw` (`:308`) is proved `rfl`. |

`Raw` is expressly an algorithm bundle, not a primitive claiming efficiency. The only
new `SPRG`/`LPNFamily` structure expressions are these two target assemblies. The named
bridge theorems are M0 proof obligations; the tables do not assert that their `sorry`
bodies have been filled.

Literal target selection in the assemblies is consistent with
`Targets = T1 /\ T2 /\ T3 /\ T4 /\ T5 /\ T6` (`Targets.lean:216`):

| Field / consequence | Target witness selected |
| --- | --- |
| sPRG `eval_eff` | `hT.1` (T1) |
| sPRG `idSamp_eff`, `sdSamp_eff` | `hT.2.2.1` (T3) and `hT.2.2.2.2.1` (T5) |
| LPN `sample_eff` | `hT.2.2.2.2.2` (T6) |
| `HasComplexityEff P.d 2` | T2, through `hasComplexityEff_of_target` (`Targets.lean:293`) |
| reduction realisers | T4, through `realizable_of_targets` (`Targets.lean:232`) |

T3 and T5 are predicates on the *same complete draw* for each honest algorithm.
`SamplesEfficiently.intro` joins their halves; it does not combine independent draw
samplers. No product `UniformSampler` is constructed. Data-instance readers are published beside
the supplied Boolean Fintype instances (`BoolPRG.lean:109`, `:113`) and advice
instances (`Reductions/LPN.lean:231`; `Reductions/PRG.lean:181`, `:193`).

T6 (`Targets.lean:197`) uses the shared contract with
`P := fun _ => PrimeSchedule`. Therefore one sampler `U`, one coin polynomial, and one
core map are quantified before **all** `L` and schedules `pi`. This is not the weaker
`forall pi, exists U/f` shape. `lpnSamplerEfficient_of_target` (`:269`) restricts this
single witness to a fixed `pi` and `Unit`, retaining its sampler, polynomial, and map.
The parameter word carries the public prime and unary dimension; no machine computes
a prime schedule.

The shared contract's equivalence need not itself be computable. Explicit supplied
finite-coordinate equivalences and faithful encodings are additional disclosed
pre-M0 interface data, not facts implied by `SamplesEfficiently`.

## Non-vacuity

| Object | Source witness and finite-coordinate data | Zero/off-image behavior and scope |
| --- | --- | --- |
| `PrimeSchedule` (`Defs.lean:72`) | `PrimeSchedule.nonempty` (`:82`) is proved using existing `Nat.exists_prime_lt_and_le_two_mul`. | At `kappa=0`, `p=2` is admitted by the weak interval endpoints. This is an existence proof, not a prime algorithm. `Classical.choose` occurs only in this non-vacuity proof (`:86`), outside encodings, draw equivalences, preprocessing maps, and targets. |
| `P.LPNAdvice pi L` (`Reductions/LPN.lean:135`) | `instLPNAdviceNonempty` (`:235`) maps the component product through `lpnAdviceProductEquiv.symm`. `lpnAdviceEquiv` (`:197`) gives explicit `Fin (lpnAdviceCard pi L)` coordinates; `instLPNAdviceFintype` (`:226`) transports from them. | The hop component is `Fin (kappaOf L + 1)`, so the sentinel remains nonempty at zero and at independent dimensions off the schedule image. Boolean indices are nonempty by the input `BoolPRG`; bucket/noise widths are positive; function products with empty domains remain nonempty. The hop inequality is required only when its value is below `kappa`. `lpnPre` (`:321`) returns `[]` off image. |
| `P.PRGAdvice pi N` (`Reductions/PRG.lean:91`) | `instPRGAdviceInhabited` (`:185`) supplies all-zero buckets, matrix, and public vectors, using `P.B_pos`. `prgAdviceEquiv` (`:154`) is an explicit coordinate equivalence and `instPRGAdviceFintype` (`:176`) transports finiteness. | Valid for every `N`, including zero and off-image dimensions. No choice is used to obtain the explicit default. `prgPre` (`:246`) returns `[]` off image. |
| Input Boolean indices and index draws | `BoolPRG.idxNonempty` (`BoolPRG.lean:58`) and `idDrawNonempty` (`:68`) are mandatory supplied fields; their instances are at `:103`/`:106`. `idxEquiv` (`:54`) and `idDrawEquiv` (`:64`) are explicit data. | Honest Boolean index sampling never samples an empty type. These hypotheses describe the input primitive rather than an additional construction assumption. |
| Generic sPRG index/index draw/seed draw | `SPRG.Raw.idxNonempty`, `idDrawNonempty`, `sdDrawNonempty` (`Defs.lean:104`, `:109`, `:129`) are mandatory raw data; the public instances are at `:143`, `:145`, `:149`. | Every exact uniform law has a nonempty draw; every raw family includes explicit cardinal/equivalence data (`:105`/`:106`, `:110`/`:111`, `:130`/`:131`). |
| Construction's exact draws | `Params.IdDraw`, `Params.Draw` (`Encoding.lean:133`, `:145`) are concrete finite products; `idDrawEquiv`, `drawEquiv` (`:212`, `:230`) compose supplied Boolean and canonical modular/function/product equivalences. | Empty vector domains at zero do not make the function type empty. Positive bucket/noise widths and nonzero prime modulus provide nonempty codomains. |
| LPN exact joint draw | `LPNFamily.Raw.Draw` (`LPN.lean:186`) is the concrete matrix/secret/noise-seed product. `drawEquiv` (`:275`) gives explicit `Fin (drawCard ell)` coordinates; nonzero modulus and noise denominator instances are at `:99`/`:100`. | It remains nonempty when the secret dimension or sample count is zero. It is one product draw, not an illicit product fair-coin sampler construction. |
| Shared realiser predicate | Existing `Complexity.NUPPT.realizesOn_self` and `realizesOn_self_take` (`TCSlib/Cryptography/Asymptotic/Realization.lean:167`, `:179`) establish generic satisfiability, including the required coin-prefix shape. | These do **not** by themselves realize the actual LPN/PRG preprocessing. Actual reduction realisers are obtained conditionally from T4 by the existing `exists_realizesOn_of_preTarget` (`:220`) through the M0 `realizable_of_targets` obligation. |

`LPNRealizable` (`Reductions/LPN.lean:413`) and `PRGRealizable`
(`Reductions/PRG.lean:286`) quantify over every adversary and every typed advice family,
then ask for a realiser using the shared predicate and exact coin layout
`A.coins.subst .var`. `Params.Realizable` (`Security.lean:45`) is their conjunction;
it does not define a local variant of `RealizesOn`. The every-realiser security
inequalities choose advice before quantifying the realisers.

## Primitive and link helper plan

The named proof sketches and reuse notes support the following plan. It is pending
proof work, not a list of checks or completed proofs.

| Obligation | Existing API / intended argument | Current source-level status |
| --- | --- | --- |
| Exact scalar LPN noise law (`LPN.lean:65`, `lpnNoise_law`) | Existing finite uniform product/point-mass readers; partition the selector-zero and selector-nonzero cases. Reuse the canonical `LWE.Noise` interface. | M0 theorem hole. |
| Joint draw/output encoding injectivity (`LPN.lean:362`, `:387`) | Existing fixed-width residue/matrix injectivity and pair/list encoding facts, with modulus width bound and explicit coordinate encodings. | M0 theorem holes; the preceding bodies are still `by ... sorry`, not completed proofs. |
| Construction encoding injectivity and polynomial bounds (`Encoding.lean:406` onward) | Owner equations plus existing `Encoding.Modular` lengths/injectivity, `BoolCircuit.encodeList`, `pairEncode` facts, monotonicity of `PolyExpr.eval`, and explicit `Fin` maps. | M0 theorem holes. Do not replace them by classical enumerations. |
| Advice encoding injection and length bounds (`Reductions/LPN.lean:368`, `:376`, `:385`; `Reductions/PRG.lean:302`, `:309`, `:320`) | Canonical `LWE.encodeChallenge_injective`; pair/list/vector lengths; actual draw bounds; inverse-parameter bounds; shared syntactic polynomial monotonicity. | M0 theorem holes. LPN uses a disclosed coarse coefficient `4096`; PRG uses `100`. |
| Targets imply reduction realisers (`Targets.lean:232`) | Apply shared `NUPPT.exists_realizesOn_of_preTarget` with `kappaOf`/`kappaOfN`, `.var`, parameter bound, canonical assumption encoding, explicit advice encoding, length theorem, and T4 witness; use `RealizesOn.congr` only if necessary. | M0 theorem hole. No machine construction or efficiency proof is attempted. |
| T1/T3/T5/T6 assembly bridges (`Targets.lean:238`, `:245`, `:257`, `:269`) | Read target witnesses through the shared contract readers, restrict public parameters to supplied schedule, preserve the sampler/map witnesses, join same-draw halves using `SamplesEfficiently.intro`, and use owner encoding/core readers. | M0 theorem holes. The assembly definitions and `toRaw` readers are already explicit. |
| Efficient polynomial-complexity bridge (`Targets.lean:293`) | Use actual G4 polynomial witnesses, T2's denoting term lists, degree bound, and sampled-seed correctness. | M0 theorem hole; T2 itself remains an unproved Phase B proposition. |

Read-only reuse evidence inspected: `evidence/review/interfaces-notes.txt`,
`prg-notes.txt`, and `lpn-reduction-notes.txt`. They disclose name/shape searches and
reuse of canonical LWE, shared sampler contracts, approved finite equivalences,
`BoolCircuit.encodeList`, shared realiser readers, averaging, and coin-prefix APIs.
Their `exact?`/`apply?` probes are explicitly pending lead-only work; no such probe was
run by this reviewer. Corresponding search artifacts named by those notes are
`reuse-searches.json`, `prg-reuse-searches.json`, and the reduction owner notes.

At M0, named theorem holes used as stored fields can propagate `sorryAx` into raw and
primitive definition dependencies. The lead's actual axiom census/trace must report
that graph; this table makes no claim that only theorem constants depend on `sorryAx`.
