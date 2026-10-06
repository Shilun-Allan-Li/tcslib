FAIL — 0 blockers / 2 majors / 1 minor / 11 notes.

Input SHA-256: `dedf11496a462d5b73c12659ab0fe1021fd4b291ad3c389f8f95e918fecda21a`. The received `ch2-epoch34-bundle.md` is 1,942,554 bytes and contains exactly the advertised **45 attachments**, with 45 distinct `## ===== <path> =====` headers. The enumerated manifest matches. There is no attachment-count blocker. Finding 2 identifies a separate reference to an allegedly attached log outside that enumerated manifest.

This is a fill-gate review of the supplied evidence, dated 2026-10-06. I followed the pack's risk order, reviewed the carrier exception separately, and did not reopen the excluded statement gates, machine-construction/emitter implementations, or colleague chapter trees. No repository history was consulted and no supplied source or pack was modified. The two majors concern the evidence needed to certify the requested closure and merge-preservation claims. I found no concrete counterexample to a completed target in the inspected source proof paths; that is not a substitute for the missing certification.

Verification environment: Linux x86-64, glibc 2.39, Python 3.12.14. Lean/Lake/Elan were absent from `PATH`. A subsequent runtime inventory located `/tmp/lean-4.25.0-linux/bin/lean`; its unmodified invocation failed with `error: failed to locate application`. I compiled an auditor-local `readlink` compatibility shim that redirects only `/proc/<current-pid>/exe` to `/proc/self/exe`, using `cc -shared -fPIC ... -ldl` and per-command `LD_PRELOAD`. With that shim, Lean reported **4.25.0**, commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`, Release. The shim source SHA-256 is `b51f9ed00a8268b30962bcc0bccd052d8617e83881963c293547b0697d2b904a`. It changes no Lean source or proof-checking code.

I independently elaborated the isolated checker counterexample in finding 1 with that runtime. I did **not** elaborate the campaign. The bundle supplies nine campaign Lean modules, not the 65-module dependency closure or build manifest. An available local checkout was inspected for build availability: its order has 57 modules, it lacks the eight added module paths, and its SAT/EXP bytes differ from the attachment. Its manifest names the requested mathlib revision `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`, but I did not authenticate or reuse its dependency caches or campaign oleans. No cache download, cache substitution, or `lake build` was performed. Consequently this report does not independently certify elaboration of the owned proofs, generated-declaration counts/visibility, or their complete kernel dependency closures. Supplied execution logs remain maintainer evidence. Textual dependency checks below are source checks, not kernel walks.

1. **[major] The supplied closure programs do not establish their advertised universal axiom and target coverage.**

   **Files/declarations:** `audits/programs/ch2-e4B-ClosureAxioms.lean`: `BAudit.hasSorry`, `BAudit.visit`, `BAudit.allowed`, the `run_cmd` target array and whole-surface loop; `audits/programs/ch2-e4A5-ClosureAxioms.lean`: the corresponding `A5Audit` declarations and whole-module loop. Associated claims occur in `audits/evidence/ch2-epoch34/span-attestation.md`, §5, and the two attached axiom logs.

   **Argument:** The final program applies `collectAxioms` only to its explicit target array. That array contains 13 of this gate's 21 targets. Its log does not print roots for `Complexity.ntime_expPow_subset_NEXP`, `Complexity.NEXP_eq_iUnion_NTIME`, `Complexity.EXP_eq_NEXP_of_P_eq_NP`, `Complexity.P_ne_NP_of_EXP_ne_NEXP`, `Complexity.snapshotAt_zero`, `Complexity.snapshotAt_state_succ`, `Complexity.snapshotAt_inputSymbol`, or `Complexity.oblivious_schedule_eq`. The A5 log covers 12 of the 21 explicitly. Some omitted locality facts are consumed transitively; that does not make the assertion that all 21 print empty roots true.

   More substantially, the whole-module/whole-surface loops call `hasSorry`, which tests only whether a declaration's type or value directly mentions `sorryAx`. They do not apply the permitted-axiom test to every enumerated declaration. A concrete counterexample to this checker property is an unused declaration:

   ```lean
   private axiom auditProbe : False
   ```

   Its type contains no `sorryAx`, it has no proof value, it satisfies the private-surface predicate, and it changes none of the explicitly checked target closures. Thus the supplied whole-module predicates accept it while the claimed standard-triple property fails. I reproduced precisely that predicate failure in a separate imported probe module using pinned Lean 4.25.0. Both compiler invocations exited 0; the check printed:

   ```text
   PROBE _private.AuditProbe.0.auditProbe: supplied module predicates pass=true; axioms=[_private.AuditProbe.0.auditProbe]; permitted=false
   ```

   This probe was never inserted into a campaign file. It demonstrates a verification gap, not an allegation that this axiom exists in the attachment. The direct-zero-`sorryAx` pass is useful evidence, but it does not prove the claimed axiom bound for all 1,206 net new privates, especially retained helpers outside target closures. Additionally, `hasSorry` returns `false` on a missing checked declaration, and neither program verifies that all manifest modules were imported; the printed declaration totals and “65-module” conclusion are not coverage assertions.

   **Resolution:** In a new resolutions artifact, enumerate all 21 frozen targets explicitly; check each root and permitted axioms. Enumerate every checked declaration in the six owned modules, including generated and unconsumed declarations, reject missing checked entries, and enforce the same axiom bound on each. Verify their permitted kernel public surfaces at the final snapshot as well. If retaining the stronger whole-campaign axiom claim, enforce it over that whole surface too. Assert inclusion of every module in the supplied order and record source/olean identity for the run. Re-run against the complete final snapshot. No target statement needs alteration.

2. **[major] Merge #2's owned-file preservation and new dependency closure cannot be certified from the supplied evidence.**

   **Files/declarations:** `TCSlib/Complexity/ClassNP/SAT.lean`: `sat_pt_linear`, `sat_pt_const`, `sat_pt_cond`, `sat_pt_and`, `sat_comp_on_image`, `sat_pipeline_poly`, `satSafeValue_poly`, `satVerdict_true_poly`; `TCSlib/Complexity/ClassNP/EXP.lean`: `enumWord`, `exists_proj_decider`, `NP_subset_EXP`; `audits/evidence/ch2-epoch34/span-attestation.md`, §§3–5; `scripts/ab_ch1_module_order.txt`. Referenced but absent: `audits/logs/colleague-merge2-sweep.log`, the owned-file merge diff, and `TCSlib/Complexity/ClassNP/PolyTimePairing.lean`.

   **Argument:** The SAT aliases now discharge their contracts using `polyTimeComputable_of_linear`, `polyTimeComputable_const`, `polyTimeComputable_ite`, `polyTimeComputable_and`, and `FinTM.exists_comp_on_image`. The declarations in the attached file expose sensible unchanged local contracts, including the concrete composition budget `2*T₁(n)+T₂(n)+2`. That establishes what the callers require; it does not inspect the newly substituted implementations or establish preservation of every changed proof. The pack expressly puts these rewires in scope, and the new shared modules have not been placed within an excluded closed gate.

   The pack says the first failed merged sweep and its resume are in an attached merge log. That log is not one of the 45 attachments. The final successful sweep is present, but cannot identify which earlier definitions were changed, demonstrate the first-parent +217/−236 diff, or verify no other owned-file drift. None of the actual patches or before-images needed for that comparison is supplied. The attached post-merge closure checker also has finding 1's limitations. Successful elaboration would establish a final proof at its final dependencies; it would not by itself establish preservation of an earlier audited implementation.

   I did inspect the two public EXP endpoints. `enumWord` is explicitly the fixed-width low-bit enumeration. `exists_proj_decider` uses `enumMachine_contracts`, `enumLoop_run`, and `enumAny_certificates`, charges startup by doubling the loop coefficient, and handles width zero with `2^0=1` candidate. I found no endpoint defect there. The historical promotion/addition and complete private rewrite inventory remain attestations.

   **Resolution:** Supply an immutable supplement containing the two owned-file merge diffs or authenticated before/after blobs, the cited merge log, and the new shared definitions and proof dependencies actually substituted into owned proof closures. Supply a reproducible final source/build manifest for the 65 modules. Review those substitutions at their contracts and implementations, and re-run the corrected closure audit. This requires neither development history nor a re-audit of the excluded colleague chapter trees or closed library internals. Until then, the merge-2 ride-along and full dependency-closure certification remain open.

3. **[minor] The attached final lint log does not cover both owned Cook–Levin files.**

   **Files/declarations:** `audits/logs/e4B-closure-lint.log`; module-wide policy coverage for `TCSlib/Complexity/CookLevin/Hardness.lean` and `TCSlib/Complexity/CookLevin/Snapshot.lean`.

   **Argument:** The log ends with “0 FAIL, 5 WARN over 15 files” and lists ClassNP files only. Four warnings concern owned files; the fifth concerns `ClassNP/TMSAT.lean`. `Hardness.lean` and `Snapshot.lean` are absent. Therefore these five warnings are not the five owned-file size exceptions. The claimed current sizes are correct, including Hardness at 9,937 lines, but this log does not establish a final policy pass for that file or Snapshot. Earlier agent REPORT claims are separate evidence, not missing rows in this log.

   **Resolution:** Append a scoped final lint result for all six owned files and identify the five size exceptions explicitly. Preserve the exceptions while correcting coverage; no pre-gate split is required by this finding.

4. **[note] The endpoint census and displayed numstat arithmetic check out, with a ten-line residual deletion category.**

   **Files/declarations:** All source-level private declarations in the six owned files; `audits/evidence/ch2-epoch34/span-attestation.md`, §§1–3; the attached agent inventories.

   **Argument:** A fresh census excluding nested comments and strings gives:

   | File under `TCSlib/Complexity/` | Lines | Private declarations | Executable admission/axiom tokens found |
   |---|---:|---:|---:|
   | `ClassNP/Nondeterminism.lean` | 5,835 | 271 | 0 |
   | `ClassNP/EXP.lean` | 3,268 | 147 | 0 |
   | `ClassNP/SAT.lean` | 4,815 | 288 | 0 |
   | `CookLevin/Snapshot.lean` | 368 | 4 | 0 |
   | `ClassNP/Tautology.lean` | 1,749 | 95 | 0 |
   | `CookLevin/Hardness.lean` | 9,937 | 618 | 0 |
   | Total | **25,972** | **1,423** | **0** |

   The token check found no executable `sorry`, `admit`, `axiom`, `unsafe`, or `native_decide` in these sources. This is a source check, not an axiom-closure proof. The stated baseline sums to 5,768 lines, 217 privates, and 21 admissions, so the differences are 20,204 lines and 1,206 privates. Baseline counts themselves cannot be independently recounted without baseline blobs.

   Summing the 16 displayed fill rows gives +20,325/−98. Adding +35/−39 and +217/−236 gives net +20,204, exactly the endpoint line delta. However, `98−21−34−33=10`. The “remaining single-digit deletions” description is accurate only if intended per delivery, not as an aggregate. The total arithmetic is sound; the residual should be written as ten lines and itemized. The 59-commit census would leave 37 maintainer commits after the 16 fills, four emitter fills, and two merges. The attachment supplies no complete 59-commit inventory, so that historical census and no-touch assertion remain unverified.

   The five Hardness REPORT name inventories contain 77, 52, 150, 176, and 163 declarations, respectively: 618 total, all names present in the endpoint. Tautology has 67 inherited declarations plus 28 from 4B, confirming the corrected 67 rather than 68. The extracted Snapshot, Hardness, and Tautology SHA-256 values match their terminal REPORT hashes. That binds these endpoint bytes to the reports, not the reports' claimed verification procedures.

   **Resolution:** Retain the confirmed endpoint counts. Record the ten-line residual and distinguish recomputed endpoint facts from historical provenance attestations in the resolutions file; do not amend the immutable pack.

5. **[note] Cook–Levin soundness reconstructs raw blocks before decoding and derives acceptance from the exact decider output.**

   **File/declarations:** `TCSlib/Complexity/CookLevin/Hardness.lean`: `clA5Group_eval`, `clA5Tableau_eval`, `clA5Reconstruct`, `clBlock_ext`, `clA5Certificate`, `clA5Run_output`, `clA5NoFalse`, `clA5Decider_accept`, `clA5Sound`, `clA5Complete`, `clA5Equisat`, `clA5Reduction`.

   **Argument:** `clA5Tableau_eval` extracts initial, state, input, work, pin, and acceptance constraints at their correct time ranges. At zero, the whole raw block is fixed. At a successor, `clA5Reconstruct` uses already established raw equality for the preceding state block and each strictly earlier work predecessor; only then can `clBlockDecode_encode` identify the decoded source. The separate state/input/work slices exhaust the product code by `clBlock_ext`. A junk raw block cannot satisfy the argument merely because the total decoder maps it to a legitimate halted/blank snapshot.

   The first `m=n+C(n+1)^e` assignment bits give a concrete word. Pinning establishes its length-`n` prefix as the original input, and dropping that prefix gives exactly the required certificate length, including `C=0`. The converse constructs assignment blocks from the genuine trace and proves their addressed bits agree, rather than assuming an arbitrary satisfying encoding.

   `clA5Run_output` lists actual emissions for `t<T`, including a halting transition's emission. `clA5NoFalse` relates the acceptance predicates to absence of false in that output. Crucially, `clA5Decider_accept` also assumes the exact singleton decider output at the horizon. A machine emitting nothing would satisfy “no false emission” but would fail this singleton premise. Thus silence cannot yield soundness. The final reduction uses `decode_serialize` on the exact output word; there is no well-formedness restriction on original inputs and no prefixed rejecting bit.

   **Resolution:** Retain this proof route. Include these declarations in the strengthened kernel coverage of finding 1.

6. **[note] The final Cook–Levin serializer supplies actual bounded field access, positive rounds, and a common polynomial budget.**

   **File/declarations:** `TCSlib/Complexity/CookLevin/Hardness.lean`: `clA5Field_native`, `clA5Decode_native`, `clA5Template_native`, `clA5GroupAt_exact`, `clA5Emit_exact`, `clA5Next_pack`, `clA5Startup`, `clA5Round`, `clA5Fuel`, `clA5Output_of_nativeChunk`, `clA5OutputIdentity`, `clEmitter_of_body`, `clTableau_chunks`, `clTableau_quadratic`.

   **Argument:** Field access iterates actual native pair-tail projections under a unary clock, with a shrinking-word bound. Binary movement counts are converted to unary by candidate comparison only up to a separately computed unary bound. For a malicious binary word denoting an enormous number beyond that bound, the result is empty after the bounded iteration; the decoded integer never becomes the loop clock. Fixed-template serialization charges each unary variable address and each literal occurrence. Noncomputable choices select finite tables for a fixed source machine, not input-dependent computational oracles.

   The six family lengths sum to `n+1+T+(T+1)+k(T+1)+T=R+1`, where `R=n+(k+3)T+k+1`. In the degenerate case `n=k=T=0`, there are still two groups and `R=1`. Empty fragments retain their rounds; only round `R` appends the formula terminator. The cursor saturates at `R+1`, whose emission is empty. `clA5Round` nevertheless pays a dispatch and positive clean calls there. Its guards and whole-configuration endpoints supply the emitting-loop contract.

   The source constructs `P=start+round+fuel`, with

   `start(n)=2n+3+aS(n+1)^dS+aJ(aH(n+1)^dH+1)^dJ`,

   `round(n)=1+aE(W(n)+1)^dE+aI(W(n)+1)^dI`, and `fuel(n)=aF(n+1)^dF`.

   Here `W` bounds every packed cursor word through `R+1`; all coefficients come from actual machine contracts. Polynomial addition/composition justifies this single `P`, and the library total `cLoop(P+1)(R+2)` is normalized separately. The tableau horizon and quadratic output-size theorem are not substituted for an execution-time proof. `clA5OutputIdentity` has no satisfiability premise and consumes the completed producer through the install bridge.

   **Resolution:** Retain the common-budget and exact-output construction. No earlier refactoring is forced by this source review.

7. **[note] The producer's greatest-earlier search uses charged sequential operations and preserves predecessor zero.**

   **File/declarations:** `TCSlib/Complexity/CookLevin/Hardness.lean`: `clWipe_run`, `clFresh_run`, `clLoad_field`, `clMatch_prefix`, `clLastIndex_max`, `clVisitCode`, `clLastCode_prev`, `clRecordOutput_compute`, `clSearch_native`, `clRepeat_complete`, `clRepeat_budget`, `clVisitRows_native`, `clPackedRecords_native`, `clPackedRecords_machine`.

   **Argument:** Each reused destination is first wiped, so a shorter subsequent field cannot leave a nonblank suffix. `clFresh_run` pays `2|old|+3|new|+6`; a dispatched field load pays one more step. The reader's forward-only overwrite condition is discharged on each restart. Search scans precisely the strict prefix of rows before the queried time and updates the retained answer to the newest matching index. At time zero the prefix is empty; for a frozen head at positive time the immediately preceding time is eligible and maximal.

   `clVisitCode none=[]`, whereas `clVisitCode (some 0)=pairEncode [] []=[false,true]`. Absence and predecessor zero therefore cannot be confused by the final work-template selector. The source's finite-row and field identities are used with native readers; they do not manufacture constant-time random access.

   The implementation recomputes reference outputs in several query arguments. Those runs are covered by `clSearchArg_native`/native composition and the replay terms in `clRecordOutput_compute`; output length bounds intermediate argument length. The outer visit builder uses `N=T+1` positive clean calls, includes the zero and final rows, and pays preparation, each call, and final replay. `clRepeat_budget` yields coefficient `13+7k+a(K+1)^d+K` and degree `2d+3` for its stated tape count and storage bound. Final native composition returns the entire packed header/trajectory/visits word. I found no free replay or uncharged indexed access in this assembly.

   **Resolution:** Retain the producer contracts and their ledger terms. Preserve the reset precondition and presence marker in any later routine extraction.

8. **[note] Recorder and preparation invariants handle signed positions, clamps, terminal effects, and the inclusive final row.**

   **File/declarations:** `TCSlib/Complexity/CookLevin/Hardness.lean`: `clPrepHeader_native`, `clRefAction`, `clRef_apply`, `clRef_schedule`, `clCountTM`, `clCount_first`, `clCount_seam`, `clMoves_correct`, `clSigned_eq`, `clCounts_schedule`, `clCounts_halted`, `clCmpUpdate_spec`, `clRec_prefix`, `clRec_prefix_silent`, `clRec_complete`.

   **Argument:** The preparation header computes the exact certificate width, reference-input width, binary horizon, all-false reference word, and unary horizon. Zero coefficients and degrees are included by the arithmetic constructions. The virtual reference transition copies writes and movements before retaining a halted state internally; it suppresses physical verdict output. Terminal writes therefore survive. Input movement is clamped before selecting the displacement counter, and the public input coordinate is recovered with its required shift by one.

   Position equality is `positive₁+negative₂=positive₂+negative₁`. For example, movement counts `(1,0)` and `(2,1)` denote the same coordinate despite different encodings. The comparator implements cross-sum arithmetic, checks final carries as well as column bits, and rewinds its buffers. Counts freeze after source halt.

   `clRec_prefix` stores completed rows before the current source time; `clRec_complete` explicitly copies the last row. At `T=0` it stores row zero, not an empty trajectory. Prefix silence follows from output monotonicity and the proved empty output endpoint. The counter's modified silent absorbing return is supported by new carry/rewind and first-return proofs, with bound `2|w|+2`; it is not inherited by asserting equivalence to an unchanged length-counter machine. The recorder cost includes the final copy and is bounded by `(4l+7)(T+1)^2`, where `l=2(k+1)`.

   **Resolution:** Retain these invariants, especially effects-before-halt, clamp-before-count, and the inclusive row convention.

9. **[note] SAT membership and clause splitting preserve the required malformed-input and streaming behavior.**

   **File/declarations:** `TCSlib/Complexity/ClassNP/SAT.lean`: `satSyntaxStep`, `satSafe_spec`, `satSafeValue_poly`, `satVerdict_true_poly`, `satChain_sound`, `satChain_extend_step`, `satTransformFrom_complete`, `satStreamStart`, `satStreamTail_chain`, `satStreamRun_formula`, `satStreamCount`, `satReduction_poly`, `satReduction_correct`.

   **Argument:** The syntax state after the formula terminator rejects any trailing bit. Thus `[true,false,false,true]` is invalid even though its prefix terminates a formula. The membership construction follows the total decoder's satisfiable empty fallback on that input; it does not run a width check on a prematurely accepted prefix. Invalid certificate splits reject, including even total lengths and zero; the valid `(1,1)` split gives an assignment of exactly input length plus one. Evaluation is invoked on the safe encoded image, whose length and literal bounds are established before its specialized runtime contract is used.

   In splitting a long clause, the new positive literal closes the current link and its negative begins the next. Completeness sets the fresh bit to the truth of the remaining tail, and later extensions preserve all indices below the threaded fresh cursor. `satSplitClause []=[[]]` preserves an unsatisfiable empty clause. This semantic induction is also the recurrence used by the streaming chunk proof.

   Startup validates the whole word before physical clause output. With `R(n)=n`, the loop executes `n+1` rounds. The chunk-count bound places completion within those rounds; remaining rounds emit nothing. A malformed input starts directly in the terminating path and emits exactly `[false]`, including at `n=0`. The seam stores the bounded cursor/phase, while literal buffering occurs within a charged round. The common envelope covers startup, request preparation, append/capture, emit/install calls, and fuel. The discarded full raw serializer route is not used to certify the reduction; the proved raw maximum-pass prefix is still reused by `satMaxTM`.

   **Resolution:** Retain this source route. Close the substituted shared-helper evidence gap in finding 2 before certifying its full dependency closure.

10. **[note] The padding cluster charges evaluation before validation and implements exponential emission by binary countdown.**

    **Files/declarations:** `TCSlib/Complexity/ClassNP/Nondeterminism.lean`: `ntime_expPow_subset_NEXP`, `a2_countdown`, `a2_exp_scheduler`, `a2_compile`, `a2_exponent_bound`, `a3nVerifier`, `a3n_verifier_mem_P`, `a3n_prevalidation`, `a3n_pad_emit`, `a3n_unpad_EXP`, `e3c_track_run`, `e3c_track_clearable`; `TCSlib/Complexity/ClassNP/EXP.lean`: `a3_exp_bits_timed`, `a3_decider_clean`, `a3_run_call`, `a3_split_timed`, `a3_source_budget`, `a3NonemptyTM`, `EXP_subset_NEXP`.

    **Argument:** The split searches use the native binary evaluator with an input-length polynomial allowance for every candidate before a split succeeds. The width function in the EXP inclusion is `2^((n+1)^c)`; adding the prefix length makes the split function strictly increasing even at degree zero. Failed search returns an explicitly guarded rejecting payload. A successful encoded pair remains nonempty even when its recovered prefix is empty, so rejection of `[]` does not discard that valid case.

    `a3_decider_clean` destructures `0<C.k` from the audited install bridge before reading tape zero. `a3_run_call` executes the mandatory first action before testing the return state, which matters if entry and exit coincide. The exact singleton verdict is extracted only after the full clean seam. The source decider's exponential cost is charged at the recovered prefix and bounded by the actual padded input length.

    The Theorem-2.22 verifier checks both the all-true padding word and the separate witness's exact exponential length. Its binary evaluation cost is polynomial in the entire encoded request before either equality is known: for example, a request with an empty incorrect padding field still pays the evaluator's unconditional bit-length bound. `a3n_pad_emit` uses the actual countdown to construct the padded request before running its polynomial decider.

    The countdown emits one true per successful fixed-width debit and none on underflow, while charging the final failed debit. Zero coefficient gives the empty binary counter and zero emitted bits. The reverse nondeterministic construction combines exact witness coverage with all-branch halting; extending the clock uses that halting premise. Small input lengths zero and one are absorbed into a uniform coefficient when normalizing to the frozen exponential class.

    The retained A-cont track/clear helpers also satisfy their narrower contracts: contiguous visited markers cover data with blank holes; a terminal move is stamped before halt; a separate origin marker permits erasure and restoration of all three aligned heads. Their per-tape cleanup proof does not assert an assembled global body. Final routes use the completed library split construction rather than assuming that unfinished assembly.

    **Resolution:** Retain the completed routes and the clearly bounded retained helpers. Include the four omitted padding targets in the explicit final closure checks required by finding 1.

11. **[note] Snapshot locality retains the halting write and proves strict predecessor locality.**

    **File/declarations:** `TCSlib/Complexity/CookLevin/Snapshot.lean`: `workCell_succ`, `workCell_eq_of_no_visit`, `prevVisit_some_last`, `prevVisit_none_no_visit`, `snapshotAt_zero`, `snapshotAt_state_succ`, `snapshotAt_inputSymbol`, `snapshotAt_workSymbol`, `oblivious_schedule_eq`.

    **Argument:** The predecessor search filters `List.range t`, so every returned time satisfies `s<t`; maximality excludes visits in the remaining interval. The none case transports initial blankness to time `t`. The some case first applies the action at `s`, then transports the resulting cell through the interval without visits. Consequently a write on a transition that halts is retained. At that action, outer `none` preserves the cell and `some none` erases it; the proof follows the actual option write semantics. Obliviousness transports head coordinates between equal-length inputs, while the symbol arguments remain attached to the genuine input and trace.

    **Resolution:** Retain the five local proofs and their four helpers. Add the omitted roots to the final explicit audit inventory.

12. **[note] The TAUTOLOGY carrier retype and the adapted membership/completeness proofs are faithful at the supplied endpoint.**

    **Files/declarations:** `TCSlib/Complexity/Formulas/DNF.lean`: `Std.Sat.DNF`, `DNF.eval`, `DNF.decode`, `DNF.serialize`, `CNF.dual`, `DNF.dual`, `CNF.eval_dual`, `CNF.tautology_dual_iff`; `TCSlib/Complexity/ClassNP/Tautology.lean`: `TAUTOLOGY`, `taut_eval_congr`, `taut_certificate_equiv`, `taut_formula_run`, `TAUTOLOGY_mem_coNP`, `tautDual_output`, `tautDual_round`, `tautDual_poly`, `TAUTOLOGY_coNPComplete`.

    **Argument:** The wrapper holds the same literal-list shape and reads it as OR of ANDs. Decoding and serialization delegate to the supplied CNF encoding, but evaluation does not silently retain the CNF interpretation. Flipping every polarity gives pointwise Boolean negation, by the actual clause/formula inductions in `eval_dual`; applying the two duals restores the original object. Universal truth of the dual is therefore precisely unsatisfiability of the original CNF.

    The degenerate instances distinguish the conventions: empty DNF evaluates false, while a DNF containing an empty term evaluates true. Malformed bytes decode to empty DNF and are outside `TAUTOLOGY`. The complement verifier accepts that fallback, rejects when any term is true, and accepts only when every term fails. Its certificate restriction uses the finite variable bound; the outer coNP complement is applied separately. These are the correct polarities after the retype.

    For completeness, the native transducer first validates the whole string, then flips only literal-polarity bits. An invalid suffix cannot leave a partial valid-looking output: the invalid branch emits exactly `[false]`, the serialization of the dual fallback. The `R=0` emitter call still performs one positive round, with full endpoint restoration. Its explicit durations are `4n+5` on valid input and `2n+3` on invalid input, including three steps on empty input. Zero work tapes are legitimate here because the seam carries `[]` and no tape-zero install interface is used. The common budget gives a linear standalone transducer.

    The final proof combines complement SAT hardness, pointwise duality, serialization round-trip, and the definition of TAUTOLOGY on every string. I approve the mathematical carrier exception and the adapted endpoint proof at source level. Historical byte-preservation through merge #1 is not independently established by this endpoint review.

    **Resolution:** Retain the carrier and both proofs. Preserve the explicit DNF-fragment and malformed-fallback conventions in later refactoring.

13. **[note] The duplicate-dispatch selection policy is acceptable; its actual execution remains an attestation.**

    **Files/declarations:** `audits/evidence/ch2-epoch34/span-attestation.md`, §§1 and 6; `audits/ch2-epoch3-agent-reports/batchA-cont3.md`; the selected endpoint's `a3_decider_clean`, `a3_split_timed`, and `a3n_verifier_mem_P` in the owned EXP/Nondeterminism files.

    **Argument:** Integrity and protocol eligibility must be determined before ranking mathematical implementations. Given that eligibility, preferring direct consumption of audited contracts, then route fidelity, then economy is a defensible order. Whole-run selection preserves a single reviewable provenance chain. A hybrid assembled from selected fragments would require a new integration, freeze, and proof audit rather than inherit either run's status.

    The selected source visibly uses the positive-tape install interface and the completed split-search route, supporting the technical rationale for β. However, two archive hash strings do not demonstrate archive integrity, α's eligibility, or absence of hybridization. The actual archives, comparison record, and selected patch identity are not supplied. I therefore approve the stated governance rule, but do not independently confirm the asserted tie, the relative economy of α/β, or α's wholesale discard. No defect in those actions is inferred merely from missing evidence.

    **Resolution:** Retain whole-run selection and the stated criterion order. Preserve a checksum-verified two-run comparison and a binding from β's complete selected patch/tree to the integration. Report execution of the policy as verified only when that record is inspectable.

14. **[note] Both deferrals are acceptable; the 65-module verification surface is acceptable in principle but not yet certified.**

    **Files/declarations:** `TCSlib/Complexity/CookLevin/Hardness.lean`: `clFillTM`, `clFill_run`, `clNative_fill`, `clPrepHeader_native`, `clCertificateCall`, `clTrack_schedule`, `clA5Reduction`; `TCSlib/Complexity/ClassNP/Nondeterminism.lean`: retained `e3c*` components and final padding targets; all six owned modules; `scripts/ab_ch1_module_order.txt`; `audits/logs/e4B-closure-sweep.log`.

    **Argument and explicit dispositions:**

    | Requested disposition | Decision | Basis and remaining condition |
    |---|---|---|
    | E5-closure dedup scope | **Approve serial post-gate deferral.** | Retained unconsumed helper contracts are bounded and do not supply an assumed missing body to final proofs. Preserve a kernel-derived live/dead inventory before deletion. |
    | Five size exceptions and routine-layer retrofit after design gates | **Approve deferral.** | The five current sizes are independently confirmed. I found no source-level proof failure requiring immediate splitting. Correct the lint coverage in finding 3 and preserve contracts, exact output, cleanup, and cost accounting during extraction. |
    | 65-module order as the verification surface | **Approve the intended expanded scope; withhold certification of its dependency completeness and final execution provenance.** | There are 65 distinct entries; the supplied sweep contains exactly those entries in the same order, numbered 1–65, with zero `error:` lines and zero sorry warnings. All direct campaign imports of the nine supplied modules occur earlier in the list. The unsupplied modules' imports, the 57→65 dependency assertion, and fresh-build identity require finding 2's supplement and finding 1's coverage assertions. |

    The dedup inventory must not equate “banked” with “dead.” In particular, the source path `clFillTM`/`clFill_run` → `clNative_fill` → preparation → producer → `clA5OutputIdentity` → `clA5Reduction` is live. Its actual scan emits one fixed bit per native input bit and halts silently at the boundary, taking `|x|+1` steps, including empty input. It has no unfinished body contract. By contrast, `clCertificateCall` and `clTrack_schedule` have no source callers in the supplied files. The retained `e3c*` phase machinery is largely bypassed by the final split-search route, but utility lemmas such as `e3c_bits_injective` remain live. In SAT, the old maximum-pass prefix is reused even though the unfinished full raw transducer route was superseded. These distinctions rule out deletion by prefix or checkpoint label.

    The eight final-order paths absent from the available 57-module snapshot are `ClassNP/PolyTimePairing`, `TuringMachine/UnaryTape`, `TuringMachine/CounterProg`, `TuringMachine/CounterProgRun`, `ClassNP/Transducer`, `ClassNP/CounterProgPolyTime`, `ClassNP/PClosure`, and `ClassNP/ExpPoly`, all under `TCSlib/Complexity/`. This availability comparison does not authenticate the historical insertion set. Including new shared dependencies in verification is appropriate. A module list and success transcript alone cannot prove that these are all dependencies or that the same source/olean snapshot was checked.

    **Resolution:** Keep the two serial post-gate work items and the broader intended verification surface. Close findings 1–2 before closing this fill gate; do not use dedup or the routine retrofit to conceal an unreviewed dependency substitution.
