**Chapter 2, phase 4, round 2 — independent adversarial re-audit**

Intended repository destination: `audits/ch2-phase4-reaudit-findings.md`.
Audited snapshot: the supplied bundle labelled `c3579472`, branch `complexity/arora-barak-ch1`.
Bundle SHA-256: `5840c037d88a39d01c21efbc8af2854f00ac18ebd91d2ebb1fc3c0c94d387a31`.

**Disposition: zero blockers, zero majors, zero minors, three notes. The statement-phase gate condition is met.** The round-1 major and both minors are resolved. The six-stage transcription is semantically faithful, and its emitter obligations are complete at the requested statement-phase granularity. The product encoding, exact serialization ledger, and pinning-cost absorption agree with Derivations B–C. No further statement or sketch repair is required by this review.

This is a source-level re-audit of the specified repairs. Round-1 mathematical certifications and the closed phases remain trusted context. Completeness of the obligation list does not constitute completion of the native machines, their simulation invariants, or their polynomial-time proofs. Historical byte comparisons and maintainer-local execution claims are assessed separately below. File locations are relative to `TCSlib/Complexity/` unless otherwise specified; line numbers refer to the extracted attached sources.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | note | `CookLevin/Hardness.lean:162` · `SAT_NPHard`, stage (5) | The repaired emitter list names all required semantic contracts at statement phase. | Stages (s1)–(s6) cover exact arithmetic and returning capture, the initialized virtual reference run, suppressed simulation emissions and internal halting, the complete source-time trajectory, strict last visits with sequential access, and exact serialization before physical halting. The output invariant explicitly spans the preparatory/serialization boundary. The boundary checks below expose no missing independent contract. | No repair. Inherit these contracts in the fill brief and discharge their native-machine and cost obligations. |
| 2 | note | `CookLevin/Hardness.lean:101,202` · product encoding and length ledger | Per-field bitwise pinning excludes junk blocks; the displayed ledger includes the growing unary indices of the pinning family. | Product fields cover the entire block; strong induction uses only earlier reconstructed blocks. Direct expansion of `serializeLit`, `serializeClause`, and `serialize` gives the stated identity. Pinning contributes `n(n-1)/2 + 5n`, excluding the one shared formula terminator; positivity of the normalized horizon justifies absorption. | No repair. Use the exact identity in the fill rather than charging constant serialized length per pinning clause. |
| 3 | note | Round-2 pack · attestations 1–3 | Source corroboration must remain distinct from historical and execution verification. | The attachment inventory, admission sites, two imports, dependency order, and relevant sketch text check out. The bundle supplies neither the `6484ce88` source tree nor the claimed sweep/lint logs; `lean`, `lake`, and `elan` are absent from this audit's executable path. Historical stripped identity, fresh elaboration, and the exact lint results were therefore not independently reproduced. | No mathematical repair. Retain these as maintainer attestations, without describing this report as a replay of those checks. |

**Resolution table, checked row by row.**

| Round-1 finding | Re-audit result | Source evidence |
|---|---|---|
| 1 major — output silence and halt redirection | **Resolved.** Every invariant in the earlier six-row contract table survives; the additions supply cost and implementation context without weakening it. | `Hardness.lean:162–206`; detailed contract check below. “Adopted verbatim” is substantively faithful, although the prose is reformatted and expanded rather than literally identical. |
| 2 minor — some-term versus every-term failure | **Resolved.** The evaluator now accepts exactly when every DNF term has an unsatisfied literal, with both empty cases explicit. | `Tautology.lean:101–109`; Boolean equivalence below. |
| 3 minor — missing normalization imports | **Resolved.** Both precise imports are present and introduce no cycle in the attached graph. | `Hardness.lean:7–8`; `Robustness.Oblivious`, `ClassNP.TMSAT`, and `Hardness` occur at positions 18, 44, and 46 in the order list. |
| 4 note — locality fill guidance | **Retained.** Strict earlier visits and the no-write/write-blank distinction remain intact. | `Snapshot.lean:133–134,149–152`; the new plan row at line 219 explicitly carries forward blank erasure and writes on the halting transition. No locality theorem is reopened. |
| 5 note — product encoding | **Resolved.** The encoding is explicitly a concatenation of fixed field codes, with bitwise field constraints and a totalized decoder. | `Hardness.lean:104–110,140–143`; product argument below. |
| 6 note — private DNF congruence bridge | **Retained.** The mentioned-variable argument remains an explicit fill obligation; this repair does not require a new public theorem. | `Tautology.lean:95–100`. |
| 7 note — survey-row nuance | **Resolved as an appended clarification.** The old survey is read as a protocol-readiness assessment and an engineering estimate that does not exclude partial reuse. | `AroraBarakChapter2Plan.md:219`. This audit makes no new claim about the unattached external development. |
| 8 note — evidence separation | **Retained, with the limits in finding 3.** Current-source facts corroborate parts of the attestations; historical and compiler claims are not inferred from them. | Pack labels the attestations as maintainer-local claims; independent source checks are listed below. |

The two appended decision rows accurately record the earlier disposition, repairs, and pending re-audit. The reserved human design question is not disposed of by these rows or this report.

**Emitter completeness and boundary checks.** The six items are proof obligations for one controller; (s2)–(s4) operate together during simulation. They do not require three separate executions of the source. The following are consequences to prove under the named contracts, not additional unmentioned sub-machine requirements.

| Stage | Contract preserved in the repair | Boundary check |
|---|---|---|
| (s1) Exact arithmetic | Retain `x`; compute exactly `Q(n)`, `m`, and `T`; capture complete binary answers on work tapes; return with empty physical output. | The inherited exact-value discipline handles `C₀=0` and `c₀=0` without majorizing certificate length. Capturing an answer includes a bit emitted on its subroutine's halting transition. Returning control excludes forwarding that halt to the physical machine. |
| (s2) Reference simulation | Simulate the run defining `inputPosAt` and `workPosAt`, on virtual input `List.replicate m false`, with head initially `1`, bounds `0..m+1`, and disjoint work tapes. | Those definitions use `initCfg`: source initial state, blank work tapes, and zero work-head positions. Native input `x` cannot be substituted when `n≠m`, or when its bits differ. Initialization and faithful work-tape evolution belong to this named simulation contract. |
| (s3) Output and halting | Discard reference output, represent source halting internally, and continue its frozen trajectory through `T`. | A transition that writes, moves, emits, and halts must first apply its tape/head effects, then enter the internal halted state. Only output forwarding and physical termination are suppressed. Early rejection and a halt at the last simulated transition are both covered. |
| (s4) Trajectory | Record source times `0..T` inclusive; counters equal the signed work positions and clamped input positions; administrative work consumes no simulated steps. | Record time `0` before the first source transition and time `T` after the last. Recording/counter scans cannot advance the logical source clock or corrupt its represented configuration. A first halted snapshot records the post-transition positions. |
| (s5) Last visits | For each target time and tape, inspect all strictly earlier records and keep the greatest matching time, or `none`; charge sequential access. | At `t=0` the candidate set is empty. Including `t` itself would violate “earlier” and the definition's `List.range t`; returning an arbitrary earlier match would violate “greatest.” Idle halted steps correctly yield the immediately preceding time. |
| (s6) Serialization | Use the fixed clause order and fixed finite templates; emit the unary packed indices, every marker, and the final terminator; halt after completion. | The physical output is initially empty and thereafter exactly a prefix of `serialize φ_x`. The templates are chosen once for fixed `M`; input-dependent changes are the already-named wiring, constants, and index arithmetic. Neither an arithmetic answer nor the reference verdict precedes the serialization. |

The output suppression is compatible with source simulation because the source transition reads only its state and input/work symbols; it does not read accumulated output. Internal storage of the source halt preserves the absorbing source branch while keeping the controller alive. Thus the repaired wrapper can preserve every source component needed by the schedule without exposing the source output physically. The simulation, recording, and serialization invariants require noninterference at their boundaries; no additional semantic assumption is being supplied here.

Re-fire the old counterexample: for the empty source/verifier languages and zero certificate length, the reference verifier emits `false`. Stage (s3) discards that bit and intercepts its halt; stages (s4)–(s5) finish their work; stage (s6) emits exactly the unsatisfiable tableau's serialization. Consequently neither `[false] ++ serialize φ_x` nor the prematurely halted `[false]` satisfies the repaired contract. The former false-positive mechanism is closed.

No uniform compiler for arbitrary machine descriptions is required: `M`, its finite transition table, its encoding, and all constant-arity CNF templates are fixed before the reduction input `x`. The choice of finite templates may be made once, then hardwired. Correct native implementations and explicit runtime bounds remain substantial fill work, but their contracts are now named.

**Product encoding.** The new passage specifies exactly the structure required by Derivation B. At time zero, family (ii) pins the whole encoded block. At positive time `t`, the state field depends on block `t-1`, each work-symbol field depends on a block at `s<t` or the blank constant, and the input-symbol field depends on a selected input bit or boundary blank. Strong induction therefore gives

\[
z_t=\operatorname{enc}\bigl(\operatorname{snapshotAt} M (x\mathbin{++}u) t\bigr)
\qquad(0\le t\le T).
\]

Each field's **bits**, rather than merely its decoded value, equal its prescribed field code. The literal slices jointly cover the block, so the displayed equality follows; no junk pattern survives. The total decoder is used on earlier blocks already established to be genuine encodings. Finiteness permits fixed field codes, and positive total width `B` is available, so the existing quotient/remainder packing argument applies. No extra well-formedness family is needed.

**Length and time ledger, re-derived.** Use the sketch's parameters

\[
n=|x|,\quad Q(n)=C_0(n+1)^{c_0},\quad m=n+Q(n),\quad
T=c\bigl(A(m+1)^d+1\bigr)^2,\quad N=m+(T+1)B.
\]

1. Normalization chooses `A,d≥1`. Although the oblivious theorem's existential statement does not explicitly assert `c>0`, its decider contract does: `c=0` would make the machine compute on the empty input in zero steps, contradicting `FinTM.not_computesInTime_zero`. Hence `c≥1`, and

   \[
   A(m+1)^d\ge m+1,\qquad
   T\ge(m+2)^2\ge(m+1)^2\ge(n+1)^2.
   \]

   In particular `T≥4`; the use of `O(log T)` for these counters has no zero-horizon exception.

2. Expand the actual serializer definitions (`CNFEncoding.lean:88–100`):

   \[
   \begin{aligned}
   |\operatorname{serializeLit}(v,b)|&=(v+1)+2=v+3,\\
   |\operatorname{serializeClause}(C)|&=1+\sum_{(v,b)\in C}(v+3),\\
   |\operatorname{serialize}(\varphi_x)|
   &=1+\sum_{C\in\varphi_x}\left(2+\sum_{(v,b)\in C}(v+3)\right)\\
   &=1+2\,\#\mathrm{clauses}
     +\sum_{(v,b)\text{ occurrence in }\varphi_x}(v+3).
   \end{aligned}
   \]

   Repeated literals count repeatedly, as required by the list serializer.

3. Each pinning unit clause at index `j<n` contributes `2+(j+3)=j+5`. Summing gives

   \[
   \sum_{j=0}^{n-1}(j+5)=\frac{n(n-1)}2+5n.
   \]

   This is the family's contribution to the whole formula; its shared final terminator is the leading `1` in the previous identity. For `n=0` the contribution is zero, with that terminator still present. Also

   \[
   \frac{n(n-1)}2+5n
   \le\frac92(n+1)^2\le\frac92T,
   \]

   so the claimed absorption is valid even before allowing the full tableau bound.

4. Every literal index satisfies `v<N`, hence `v+3≤N+2`. Fixed finite templates give both clause count and literal-occurrence count `O_M(n+T+1)`. Therefore

   \[
   \begin{aligned}
   |\operatorname{serialize}(\varphi_x)|
   &\le1+2\,\#\mathrm{clauses}+(N+2)\,\#\mathrm{literals}\\
   &=O_M\bigl((n+T+1)(N+1)\bigr)=O_M(T^2).
   \end{aligned}
   \]

   The last equality uses `n≤m≤T`, fixed `B`, and `N=m+(T+1)B`. Polynomiality in the original input length follows explicitly from

   \[
   \begin{aligned}
   m+1&\le(C_0+1)(n+1)^{\max(1,c_0)},\\
   T&\le c\bigl(A(C_0+1)^d+1\bigr)^2
              (n+1)^{2d\max(1,c_0)}.
   \end{aligned}
   \]

5. By source time `t≤T`, work positions lie in `[-t,t]` and the input position is at most `min(m+1,t+1)`. A trajectory thus occupies `O((k+1)(T+1)log(T+2))` bits. The all-earlier-record comparison scheme uses exactly

   \[
   k\sum_{t=0}^{T}t=\frac{kT(T+1)}2
   \]

   position comparisons. Sequential retrieval, rewinding, signed comparison, and counter arithmetic add polynomial scan overhead; the sketch now explicitly charges it. Unary emission costs its output length plus polynomial counter overhead. This establishes numerical feasibility of the named scheme, not a completed native-machine runtime proof. The latter is expressly part of stage (5)'s fill obligation; no random-access hypothesis is needed.

**Corrected DNF quantifier.** For any assignment `a`, unfolding `evalDNF` gives

\[
\operatorname{evalDNF}(a,\varphi)=\mathrm{false}
\iff
\forall C\in\varphi,\ \exists(v,b)\in C,\ a(v)\ne b.
\]

This is exactly the repaired phrase. An empty term makes the right side false; an empty formula makes it vacuously true. For the earlier counterexample `[[ (0,true) ], [ (0,false) ]]`, one term is satisfied on every assignment, so the corrected complement verifier rejects every proposed falsifying assignment. The named mentioned-variable congruence bridge and the buffered-verdict discipline remain present.

**Assessment of attestations 1–3.**

| Attestation | Independently corroborated from the attachment | Not independently reproduced |
|---|---|---|
| 1 — repair scope and freeze | The current repaired text and two precise imports are present. Comment-stripped inspection of the two changed Lean files finds the expected five hardness statements, three tautology-related definitions, and two tautology statements, with the expected bodies. The two appended plan rows describe these repairs accurately. | Exact changed-path enumeration, the stripped diff against `6484ce88`, byte identity of other files, and verbatim preservation of the earlier findings file require baseline bytes absent from this bundle. Current-source consistency is not a historical diff. |
| 2 — elaboration and admissions | The bundle has 70 attachments: 53 ordered Lean modules plus `TCSlib.lean` and 16 other files. All 53 order entries are distinct and attached. All 123 imports between ordered modules point backwards; the graph is acyclic and the root reaches all 53. Comment-stripped source has 59 `sorry` sites, distributed by phase as `19+14+12+14`; phase 4 remains `2/5/5/2` in DNF/Snapshot/Hardness/Tautology. | Successful repaired-module/facade elaboration, fresh-olean production, zero gate errors, and exactly 59 compiler admission warnings. Source token counts are not compiler output. |
| 3 — policy and lint | Both added imports are precise; relevant statement prose precedes the sketches; the two changed theorem sketches remain attached to their declarations. No bare `import Mathlib` occurs in the supplied Lean tree. | The lint program's zero-FAIL result and exact six-WARN baseline: its script and execution log are not included. No whole-tree lint run was performed here. |

No evidence found in the repaired sources contradicts the maintainer's execution attestations. Those limits do not reopen the already trusted mathematical results or add an unfulfilled semantic contract to the repaired emitter.

**Notation glossary.** `M` is the fixed oblivious verifier machine; `k` is its work-tape count. `x` is the reduction input; `n=|x|`; `u` is a certificate; `Q(n)=C₀(n+1)^c₀` is its exact length; `m=n+Q(n)`. `A,d≥1` are enlarged verifier-time constants; `c≥1` is the oblivious-simulation multiplier; `T=c(A(m+1)^d+1)^2` is the source-time horizon. `B` is the fixed snapshot-code width; `N=m+(T+1)B` is the exclusive variable-index bound; `enc` is the product encoder; `z_t` is the block at source time `t`; `s` denotes an earlier source time. `φ_x` is the emitted CNF; `φ` is an arbitrary formula; `C` is one clause/term; `(v,b)` is a literal, with variable index `v` and polarity `b`; `a` is a Boolean assignment; `j` indexes a pinning clause. `#clauses` and `#literals` count clauses and literal occurrences of `φ_x`; `O_M` allows constants depending on the fixed machine and its chosen encoding. `|·|` denotes word length, and `++` denotes concatenation.
