# Individual final Yao B diagnostics

Each row below occurs independently in **strict** and **coe**, at the same line/column with byte-identical normalized error text. Both canonical A variants pass. B deliberately seals the Q1-exempt `PolyExpr.eval`; these B failures are reported as failures, not passes.

| # | Original line | Sealed line | Declaration | Origin | Individual attribution |
|---|---:|---:|---|---|---|
| 1 | 283 | 325 | `yaoCoins_eval` | base | The unchanged yaoCoins_eval rfl requires the polynomial coin expression to evaluate to 10*S(n)*n+2*S(n). B seals PolyExpr.eval and blocks that owner-local arithmetic reduction. |
| 2 | 591 | 633 | `yaoHybrid` | base | The first yaoHybrid callA argument j has Fin ((Y.inB.mul var).eval n), whereas yaoCall expects Fin (Y.inB.eval n*n). Sealed polynomial evaluation blocks the definitional identification. |
| 3 | 592 | 634 | `yaoHybrid` | base | The second yaoHybrid callA use of yaoCall has the same explicit mul-evaluation index mismatch; it is a separate diagnostic in the unchanged definition. |
| 4 | 593 | 635 | `yaoHybrid` | base | The yaoHybrid callB use of yaoCall has the same explicit mul-evaluation index mismatch in the unchanged definition. |
| 5 | 599 | 641 | `yaoHybrid_callA` | base | The unchanged yaoHybrid_callA reader passes product-index j into the protocol call domain ((yaoHybrid...).calls.eval n), which no longer reduces under the B eval seal. |
| 6 | 607 | 649 | `yaoHybrid_callB` | base | The unchanged yaoHybrid_callB reader has the corresponding product-index/protocol-call-domain mismatch. |
| 7 | 718 | 760 | `yaoHybrid_answersB_getD` | base | The unchanged answersB getD proof calls callA with product-index j; the protocol call-count evaluation is opaque in B. |
| 8 | 719 | 761 | `yaoHybrid_answersB_getD` | base | The same unchanged answer-reader expression calls callB with product-index j; this is its separate call-domain mismatch. |
| 9 | 725 | 767 | `yaoHybrid_answersB_getD` | base | The later ofFn expression in the unchanged answer-reader proof again calls callA with product-index j, with the opaque polynomial call domain. |
| 10 | 726 | 768 | `yaoHybrid_answersB_getD` | base | The later ofFn expression separately calls callB with product-index j; the same eval multiplication reduction is blocked. |
| 11 | 817 | 859 | `yaoSeed_good_whp` | base | The frozen yaoSeed_good_whp signature supplies G1 with Fin(n+n) output, while PRFOut (.add var var) asks for Fin ((var.add var).eval n). This existing signature depends on exempt polynomial notation. |
| 12 | 917 | 959 | `yaoHybrid_polyTime` | efficiency | CallEquations.inputA_eq ranges over Fin (Y.inB.eval n*n), while the goal ranges over Fin ((yaoHybrid...).calls.eval n). Its ordinary/canonical-A application uses the authorized polynomial-evaluation notation; this exact failure already appears in the efficiency audit. |
| 13 | 929 | 971 | `yaoHybrid_polyTime` | efficiency | CallEquations.inputB_eq has the same product-domain versus opaque calls.eval mismatch. This exact failure is the second efficiency-only diagnostic. |
| 14 | 995 | 1037 | `yaoHybrid_simulators` | base | The frozen simulator G1 hypothesis has the same Fin(n+n) versus Fin ((var.add var).eval n) mismatch as the baseline; it is also prototype diagnostic1. |
| 15 | 997 | 1039 | `yaoHybrid_simulators` | base | The frozen simulator concatenation Fin.append has output length n+n+(var.add innerLen).eval n, whereas joint PRFOut expects the opaque outer add evaluation; this is baseline and prototype diagnostic2. |
| 16 | 1016 | 1058 | `yaoHybrid_simulators` | new simulator body | FakeSimulatorFactory is instantiated at inputs=.add Y.inA Y.inB. The actual circuit has DAGCircuit (Y.inA.eval n+Y.inB.eval n), while the sealed factory expects DAGCircuit ((Y.inA.add Y.inB).eval n). This is the first direct new body mismatch, corresponding to prototype diagnostic3. |
| 17 | 1020 | 1062 | `yaoHybrid_simulators` | new simulator body | The supplied Nat.le_refl proves A(n)+B(n)<=A(n)+B(n), while the factory expects A(n)+B(n)<=(Y.inA.add Y.inB).eval n. This is a second direct eval-add mismatch, prototype diagnostic4. |
| 18 | 1021 | 1063 | `yaoHybrid_simulators` | new simulator body | After diagnostic16 rejected the actual circuit family, the key obligation explicitly contains (sorry n).size and (sorry n q) rather than Y.circ/yaoSeed. The actual seed-key reader cannot close that poisoned dependent obligation. This is the matching prototype diagnostic5 cascade, not an independent unproved seed law. |
| 19 | 1022 | 1064 | `yaoHybrid_simulators` | new simulator body | The nonce0 simp step is a premise of the same factory whose circuit family was rejected in diagnostic16. The supplied actual nonce reader no longer matches that dependent family. The exact same source line/message is prototype diagnostic6; canonical A checks this premise successfully. |
| 20 | 1023 | 1065 | `yaoHybrid_simulators` | new simulator body | The nonce1 premise is the separate corresponding dependent-family simp failure after diagnostic16, matching prototype diagnostic7; canonical A checks the unchanged source successfully. |
| 21 | 1025 | 1067 | `yaoHybrid_simulators` | new simulator body | The factory permutation premise uses the actual seed/permutation readers, but the factory family is poisoned by diagnostic16. This separate simp-no-progress cascade matches prototype diagnostic8 and disappears in canonical A. |
| 22 | 1068 | 1110 | `yaoHybrid_simulators` | new simulator body | The GateHybridSecurity call supplies Fin.append G1 G2 at the exact joint polynomial L. B prevents reducing L.eval n to the explicit concatenation output length, so this body application fails just like prototype diagnostic9. |
| 23 | 1142 | 1184 | `yaoHybrid_hbcSecure` | base | The unchanged yaoHybrid_hbcSecure G1 hypothesis again requires n+n to identify with the opaque polynomial add evaluation. It is the penultimate baseline diagnostic. |
| 24 | 1144 | 1186 | `yaoHybrid_hbcSecure` | base | The unchanged yaoHybrid_hbcSecure joint-family header has the same explicit concatenation length versus opaque nested-add evaluation mismatch as the last baseline diagnostic. |

Per variant: **24 = 15 baseline + 2 efficiency + 7 new simulator body**. The seven new body errors are three direct polynomial-index mismatches and four dependent factory-premise cascades. Prototype B9 includes the simulator header's two baseline errors, so those two must not be added a second time.

The four cascade classifications are causal inferences from the rejected factory circuit family, the poisoned `(sorry n)` key goal, the shared dependent factory premises, exact prototype matches, and the one-flag A/B instrumentation difference. They are distinguished from the three direct new index mismatches.

Failing-declaration multiplicities: `yaoCoins_eval` 1, `yaoHybrid` 3, `yaoHybrid_callA` 1, `yaoHybrid_callB` 1, `yaoHybrid_answersB_getD` 4, `yaoSeed_good_whp` 1, `yaoHybrid_polyTime` 2, `yaoHybrid_simulators` 9, `yaoHybrid_hbcSecure` 2.

Every baseline/efficiency/prototype comparator was checked individually for identical normalized diagnostic text; prototype rows also have identical source lines. `ATTRIBUTION.json` contains all48 full final excerpts, full comparator excerpts and exact input hashes. No strict-only/coercion-only difference remains.

This review reads stored outputs only. It does not rerun Lean, replace the lead's broader Rule10/axiom checks, or alter the source/frozen signatures. The original source is1152 lines, SHA256 `aa54fc5eb5cd4fb3aca8671c1aaba7bfbeb6b0ccabcd2b30ad12db64aad3ee84`.
