**Chapter-1 infrastructure audit — round 3**

**Gate: CLOSED — 0 blockers, 0 majors, 3 minors.** The new `exists_loopCfgTM` passes this statement-phase audit, and its conclusion supplies the unchanged `enumMachine_contracts` after the stated instantiation and the explicit translation below. Round 2's major is discharged. Its three minors are also discharged. The three new findings concern documentation.

Audited input: `ch1-infra-r3-bundle.md`, SHA-256 `9d411051a98ebe2ad8adb8dd4250817dc6e7892b921bd4bf053966ab16f46aee`. The manifest is correct: 26 attachments after the pack. For the stability comparison, I also obtained the saved round-2 bundle and verified its SHA-256 against the previous findings: `9517118a3bdb1ccfdaca6e82df05f168c2b29b327e8cacc4d7fdd6d4141618c6`.

References use repository file-local lines. `Build/` abbreviates `TCSlib/Complexity/TuringMachine/Build/`; `EXP.lean`, `NP.lean`, and `TMSAT.lean` have prefix `TCSlib/Complexity/ClassNP/`. Evidence and log filenames have prefixes `audits/evidence/ch1-infra/` and `audits/logs/`, respectively.

This is a mathematical/source audit with byte comparisons and independent log recounts. No Lean executable or complete build tree is available here. The finite controller and its simulation invariants remain to be implemented and kernel-checked; the realizability argument below is not a completed Lean construction proof. Previously passed proofs and statements were carried forward, without a new proof audit.

1. **[MINOR — R3-1] The new corollary descriptions do not match the frozen summation interface.**

   **References:** `Build/Loop.lean:36–39,118–130,149–151,195–202,223–225`; `machine-library-design.md:340–341`.

   Directly applying `loop_run` to the exported family requires taking `N = R |x| + 1`. Its `hout` hypothesis then demands
   \[
     (\mathrm{cfg}(R(|x|)+1)).\mathrm{output}=[]
   \]
   because it quantifies over **all** `j ≤ N`. The new export instead supplies
   \[
     (\mathrm{cfg}(R(|x|)+1)).\mathrm{output}=[\mathrm{false}].
   \]
   These are incompatible. Monotonicity of a time bound does not supply the missing output premise. Thus “`loop_run` + monotonicity” omits a necessary interface adaptation.

   The decision corollary itself is valid. Use an already-halted-terminal summation lemma, with the shape of the attached `EXP.lean:630–659`: induction over the remaining rounds gives at most `(R+1)·B` steps from `cfg 0`, where `B` is the uniform segment bound. Including startup costs at most `(R+2)·B`, exactly the decision form's allowance. Such a lemma does not need empty output at the terminal. It can be added at fill time without changing the frozen `loop_run` statement.

   The same docstring's plural “final-answer forms below are corollaries” also overstates the export: `exists_loopFindTM` has an arbitrary accepting payload, while this configuration contract and `loop_run` expose Boolean verdicts. They do not directly supply its payload or first-success output.

   **Repair:** describe the decision form as a corollary through an already-halted-terminal summation lemma or an explicitly proved adapter. Restrict the corollary claim to that form; describe the find form as the corresponding payload-host construction. The actual enumerator translation in item 5 does not use this mismatched invocation.

2. **[MINOR — R3-2] The configuration proof sketch must justify a worst-case segment bound, rather than read an amortized bound off one segment.**

   **Reference:** `Build/Loop.lean:153–160`, especially “one amortized counter operation” and “read off at segment granularity.”

   An aggregate countdown-cost bound does not by itself imply a bound on every individual segment. A decrement from a power of two can traverse the full counter, and the final zero-counter underflow can do so as well.

   The required stronger estimate is available from the existing hypotheses: the counter's initial width is at most `T |x|`, and it never grows. Consequently **each** debit, rewind, and underflow costs a constant multiple of `T |x| + 1`; item 4 gives the calculation. This proves the advertised uniform budget without amortization.

   **Repair:** put this width-based worst-case estimate into the new proof sketch, explicitly including the final underflow and false-bit emission. The theorem statement needs no change.

3. **[MINOR — R3-3] The coefficient-shift paragraph points to the wrong equality.**

   **Reference:** `machine-library-design.md:350–354`.

   The three equalities are listed in the order stripping, increment, split search. “The middle one is false without the shift” therefore refers to `incFixed = enumInc`, which has no coefficient parameter and is correct without a shift. The intended warning concerns the **last**, split-search equality.

   **Repair:** replace “the middle one” with “the split-search equality.” The displayed shifted equation and the P10/P8 parameter choices are already correct.

4. **[PASS — new configuration contract] The uniform segments, exhaustion terminal, and output clauses are realizable.**

   **References:** `Build/Loop.lean:161–203`; `TCSlib/Complexity/TuringMachine/Finite.lean:82–107`; `Build/Convention.lean:68–77`.

   Fix an input `x`. For this argument, write
   \[
     n=|x|,\qquad
     s_i=(\mathrm{stepF}\ x)^{[i]}(s_0(x)),\qquad
     L=|\mathrm{Nat.bits}(R(n))|.
   \]
   The hypotheses of the new export are byte-identical to the decision form's hypotheses. In particular,
   \[
     \mathrm{Inv}(x,s_0),\qquad
     \mathrm{Inv}(x,s_i)\Rightarrow\mathrm{Inv}(x,s_{i+1}),
   \]
   so induction supplies the body contract at every orbit point.

   The fuel machine and `output_length_le` give the crucial local estimate:
   \[
   \begin{aligned}
     L
       &=\left|\bigl(F.\mathrm{tm.runFrom}(F.\mathrm{tm.initCfg}\ x)(T(n))\bigr)
                    .\mathrm{output}\right|\\
       &\le T(n).
   \end{aligned}
   \]
   Use a fixed-width little-endian counter with these `L` cells, retaining high zero bits after decrements. A single borrow scan and return to the origin use at most a constant multiple of `L+1` steps. This also covers the all-zero underflow and `L=0`.

   The finite host isolates the fuel tapes, restores the input head, and starts the body on its own blank work tapes. Fuel capture, its counter rewind, and the input rewind cost `O(T(n)+1)`: the input head can have moved only `T(n)` positions. Body startup has the same bound. No scan of the entire input is necessary when `T` is sublinear.

   For `0 ≤ i ≤ R(n)`, define `cfg i` to be the host's body seam for `s_i`, with empty physical output and counter value `R(n)-i` in the same `L` cells. Preserve the completed fuel phase's unused tape contents across these configurations. Distinct finite-control phases separate startup, active body execution, counter handling, and final emission. After releasing a seam, execute a body action before recognizing another anchor entry.

   A rejecting body's endpoint is the live, empty-output seam. Absorbing halts and append-only output imply that this round neither halted nor emitted earlier. Positive duration and the no-interior-anchor clause identify the next seam return. The host then debits the counter. Acceptance instead reaches a captured halt and the host emits `[true]` once.

   The segment endpoints are therefore:

   | Case | Host action and endpoint |
   |---|---|
   | Acceptance at `i ≤ R(n)` | Run the body, detect its halt, emit `[true]`, halt. |
   | Rejection at `i < R(n)` | Run the body to `s_(i+1)`, debit the positive counter, rewind, enter `cfg (i+1)`. |
   | Rejection at `i = R(n)` | Run the last body round, underflow the zero counter, emit `[false]`, halt at `cfg (R(n)+1)`. |

   In the last row, underflow and emission belong to the **last rejecting segment**. There is no extra unbudgeted terminal round. If the last candidate accepts, the separately specified rejection terminal is unreachable and can be any halted configuration with output `[false]`. Likewise, configurations following an earlier acceptance need not be reachable from startup; their local contracts are established from their specified seams. Values of `cfg` beyond the terminal are unconstrained.

   More explicitly, take fixed controller constants `a₀,a₁,a₂,a₃` bounding startup, body simulation, counter work, and dispatch/emission. Every segment has a witness satisfying
   \[
   \begin{aligned}
     t_i
       &\le a_1T(n)+a_2(L+1)+a_3\\
       &\le (a_1+a_2+a_3)(T(n)+1).
   \end{aligned}
   \]
   Startup is at most `a₀(T(n)+1)`. Choosing
   \[
      K=\max\{1,a_0,a_1+a_2+a_3\}
   \]
   gives the export's single constant `c = K`, uniformly over all inputs and rounds. Producing the concrete controller and proving these simulation estimates in Lean are the remaining construction work.

   The empty-output clause is correctly restricted to `i ≤ R(n)`; it does not include the already-emitted terminal. For `R(n)=0`, startup reaches `cfg 0`, the initial candidate is tested once, and its rejection performs the first debit/underflow into `cfg 1`. No initial candidate is skipped.

   The delay-machine separation is closed: if candidate zero accepts, startup followed by its accepting segment forces halting within `2K(T(n)+1)`. In the enumerator instantiation this is polynomial. A machine deliberately waiting exponentially long before accepting cannot satisfy the new conclusion.

5. **[PASS — exact customer translation] The export lands on the attached `enumMachine_contracts`, including zero width.**

   **References:** `machine-library-design.md:300–310,336–348`; `EXP.lean:103–111,128–132,194–208,750–764`.

   Fix the customer's parameters and verifier. Retain the round-2-approved body/fuel instantiation and its pending concrete seam/restoration proofs. Put
   \[
      w=C(n+1)^c,\qquad R(n)=2^w-1.
   \]
   Since `2^w ≥ 1`, natural-number subtraction gives
   \[
      R(n)+1=2^w,\qquad
      i\le R(n)\ \Longleftrightarrow\ i<2^w.
   \]
   Thus both the terminal index and the range of round quantification match exactly.

   The required orbit bridge is **bounded to candidate indices**:
   \[
      \forall i<2^w,\qquad s_i=\mathrm{enumWord}(w,i).
   \]
   Its base case is `enumWord_zero`. For a successor still below `2^w`, use `incFixed = enumInc` and `enumInc_word`:
   \[
   \begin{aligned}
      s_{i+1}
        &=(\mathrm{incFixed}(s_i)).\mathrm{getD}(s_i)\\
        &=(\mathrm{some}(\mathrm{enumWord}(w,i+1)))
                           .\mathrm{getD}(s_i)\\
        &=\mathrm{enumWord}(w,i+1).
   \end{aligned}
   \]
   Consequently, for every customer round,
   \[
      \mathrm{acceptF}(x,s_i)
        =\mathrm{MultiTapeTM.indicator}\ V\,
                   (x\mathbin{++}\mathrm{enumWord}(w,i)).
   \]
   No orbit identity at `i=2^w` is required: the host terminal is produced by underflow. Indeed, at positive width the stalled orbit generally differs there from the wrapped `enumWord`. At width zero, there is exactly one candidate `[]`, `R(n)=0`, and terminal index `1`.

   For budget domination, choose fixed `A,D` for the common body/fuel polynomial envelope
   \[
      T(n)\le A(n+w+1)^D.
   \]
   All coefficients and degrees are chosen after the customer's fixed parameters and before the universally quantified input. Since `n+w+1 ≥ 1`,
   \[
   \begin{aligned}
      K(T(n)+1)
        &\le K\bigl(A(n+w+1)^D+1\bigr)\\
        &\le K(A+1)(n+w+1)^D.
   \end{aligned}
   \]
   Set `b = K(A+1)` and `e = D`. Use the **same** exported machine, configuration family, startup, and segment witnesses. Weaken their bounds by this inequality, rewrite the terminal and index range, and substitute the bounded orbit bridge. Reorder the conjuncts and discard the extra empty-output clause. This is precisely `EXP.lean:750–764`; no customer-statement edit or replacement decider theorem is needed.

6. **[VERIFIED — stability and corrected attestations] The supplied counts and narrow changes agree with independent comparisons.**

   The hash-matching round-2 baseline allows an exact comparison, rather than inference solely from the diff summary:

   | Check | Result |
   |---|---|
   | Existing Build declarations | All earlier statements and proofs are byte-unchanged. The only new declaration is `exists_loopCfgTM`. |
   | New export hypotheses | Byte-identical to those of `exists_loopTM`. |
   | `Loop.lean` delta | 88 inserted / 8 deleted lines: new export, module overview, and decision-corollary prose. |
   | `Primitives.lean` delta | 3 inserted / 2 deleted lines: P10 docstring only. |
   | Combined production-source delta | 91 insertions / 10 deletions, matching `tree-deltas.txt:9–12`. |
   | Shared model, composition, encoding, facade, Convention, Wrappers, NP, EXP, and order-list files | Byte-identical between the two bundles. In particular the full 882-line `EXP.lean` is unchanged. |
   | Design document | Only the 45-line §9c insertion. |
   | Attestation programs | Bridge traversal program unchanged; Build printer adds the new theorem and updates the contract count. The two-file source-scope claim concerns `TCSlib`; this disclosed audit-program edit also exists. |

   Independently recounted sweep logs:

   | Run | Module headers, in supplied order | Errors | Build admissions | Other admissions | Total |
   |---|---:|---:|---:|---:|---:|
   | C | 57/57, unique | 0 | 18 | 28 | 46 |
   | E | 57/57, unique | 0 | 23 | 28 | 51 |

   Both end in `SWEEP_PASS modules=57`. Run E's Build distribution is exactly **4 wrappers + 4 loops + 15 primitives**. The non-Build admission-warning lines are identical between C and E, and between the saved D log and E. These are declaration-level warning counts.

   The axiom log has **40 print lines, 26 containing `sorryAx`, and 8 root reports**. Its final 30 prints match the Build program's print list exactly: five headlines, two Convention lemmas, and 23 contracts. The 23 source stubs match the expected Build distribution. The Convention prints are exactly `[propext, Quot.sound]` and `[propext]`. The root reports match the unchanged traversal expectations, and the transcript reports PASS and exit 0.

   Lint has **0 FAIL and 7 WARN over 38 distinct files**: 6/28 in the machine invocation and 1/10 in ClassNP. Every warned file is covered by one of the pack's cited justifications: Universal, TMSAT, or the five named merge-refactor files. The quoted disposition is now complete. The original decision-log records are not attached; their provenance remains a maintainer attestation.

   `tree-deltas.txt:3–7` supplies the previously missing C→D production-tree change summary. Lines 14–22 report matching current/historical bridge blobs:

   | File | Reported identical Git blob |
   |---|---|
   | Universal | `f6bfefbfdfcdff65dcc64696c070282a0bb151c0` |
   | TMSAT | `8492aea5a04daf1e6f79debd2b110392c90b66fa` |

   I independently reproduced the TMSAT value from the saved round-2 source; the Universal prefix agrees with the historical patch. Accept the supplied current-blob comparison as evidence of preservation. The current bridge files and Git object database are absent from this round's bundle, so those current hashes were not independently recomputed here. No bridge proof was re-audited.

   The Universal baseline correction also agrees with the saved patch: the old final hunk ends at `2831+4−1 = 2834`, and `2834+67 = 2901`. The fresh-olean claim, toolchain, and mathlib pin remain execution attestations rather than facts reproduced in this environment.

7. **[DISPOSITION — D5 v3 and adopted notes] Accept the narrowed interface/continuation plan with the inherited 2B evidence limit.**

   **References:** `audits/ch1-infra-r3-pack.md:66–82`; `machine-library-design.md:350–370`.

   | Customer | Round-3 disposition |
   |---|---|
   | 2A `enumMachine_contracts` | **Approved at statement/interface level.** Items 4–5 close the former major; concrete body, orbit-bridge, and restoration proof terms remain fill work. |
   | P10 | **Approved, carried forward.** Introductory and construction references now consistently name `exists_loopFindTM`. |
   | 2C `pairedVerifier` | **Approved, carried forward.** Both orientations of the length comparison, with the recorded pairing assembly and conjunction, supply exact width. |
   | 2C `paddedVerifier` | **Approved.** P10 uses `(C+1,c)` and P8 retains `(C,c)`; missing split/marker and original-bound failures are guarded. |
   | D-WRAP | **Approved, carried forward:** guarded P13 and verifier composition. |
   | D-EMIT | **Approved, carried forward:** general pairing assembly, exact P5 unary outputs, retained input, and fixed outer encoding. |
   | D-MEM | **Approved as explicitly limited.** Assembly is supported; timed variable-prefix extraction, unary-shape checks, and complete-answer recognition remain named continuation obligations. |
   | 2B `choiceVerifier` | **Component-level assessment carried forward.** The detailed simulation-core/customer source is still not attached; this audit does not upgrade the old assessment to complete customer-contract verification. The bespoke NDTM reverse direction remains outside library coverage. |
   | Clearing | **Accepted discipline.** Every rejecting body still owes a concrete scratch-restoration proof. |
   | E3/E4 | **Deferred, as requested.** No full brief-level coverage verdict is issued here. |

   The shifted split-search equality is correctly recorded, subject to R3-3's prose fix. The canonical `H/s/t` construction preserves the round-2 derivation, including `g ∘ pairFst` when mapping the second component of the duplicated `s x`. It also explicitly records C1's restriction to the payload and routes cross-component work through a retained whole request. No new assembly claim bypasses that caveat.

   The two previously overbroad commentary claims concerning zero-tape startup and off-invariant noncomputability are acknowledged without replacement blanket claims. Their statement-level dispositions remain unchanged.

8. **Round-2 resolution ledger.**

   | Round-2 item | Resolution |
   |---|---|
   | 1 — major, missing host configurations | **Discharged:** new export and exact customer translation, items 4–5. |
   | 2 — lint totals and warning dispositions | **Discharged:** both invocations counted and all seven justifications cited. |
   | 3 — Convention axiom wording | **Discharged:** exact subsets correctly reported. |
   | 4 — P10 Boolean-loop reference | **Discharged:** corrected to the payload loop. |
   | 5 — coefficient shift | **Adopted correctly in formulas and pipeline parameters;** R3-3 corrects its new prose pointer. |
   | 6 — evidence limits | **Advanced as documented in item 6.** Current-blob comparisons and C→D scope now have supplied evidence; run C is independently recounted. Execution provenance and 2B's detailed customer verification remain limited. |
   | Item-7 commentary qualifications; item-10 pairing/C1 caveat | **Adopted.** |

   The statement/interface gate closes under the specified zero-blocker, zero-major rule. This disposition authorizes no claim that the admitted construction or customer fills have been completed.

**Notation glossary.** `n=|x|` is input length; `s_i` is the iterated state word defined in item 4; `L` is the initial fuel-bit length; `a₀,a₁,a₂,a₃` are fixed controller-cost constants; `K` is their common bound, replacing the export's witness name `c` to distinguish it from the customer's polynomial degree; `B=K(T(n)+1)` is the segment budget; `w=C(n+1)^c` is certificate width; `A,D` are a fixed polynomial-envelope coefficient and degree; `b=K(A+1), e=D` are the customer's time-bound witnesses. `++` is list concatenation; `[i]` on a function denotes its `i`-fold iterate. `H,s,t,f,g` in item 7 are the existing pairing-recipe functions from §9c. Other identifiers are those of the attached contracts.
