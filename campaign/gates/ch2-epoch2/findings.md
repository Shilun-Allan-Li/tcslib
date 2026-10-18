# Chapter 2, epoch-2 fill-gate findings

**Gate position: PASS — 0 blockers, 0 majors, 2 minors.** The eleven frozen theorem names are proved without admissions. The two minors concern the immutable audit material, not the proofs; record their corrections in the resolutions file. I approve the E5 deferral, the D7 extension, and unchanged D6, with the qualifications below. This audit recommends closure; it does not itself edit the maintainer’s gate records.

The input contains exactly the advertised 34 attachments. Its SHA-256 is `a85ad53cc29087b4e115f6621ea15625c46df144a74ba01ae4b49f19ea4ef588`. I audited the supplied proof bodies, helper contracts and their implementation, dependency closures, and consumption of the previously audited library and bridge. I did not reopen the frozen statements or the excluded library/model proofs.

For independent elaboration, all nine supplied source/model files were matched byte-for-byte to the available local checkout at `022cd0f3cf63689b866cc0e7407db62f7e14cc77`; that checkout supplied the remaining project dependencies and baseline history. I rebuilt the 57-module order into an initially empty, separate project-olean directory, using Lean 4.25.0 and mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`. All 57 modules and the supplied closure program passed. My runtime required a locally compiled, inspected shim translating the executable’s `/proc/<pid>/exe` lookup to `/proc/self/exe`; it did not modify Lean or its kernel. The supplied ordinary-host maintainer run remains a separate execution record. The accompanying evidence archive contains the independent logs, additional helper traversal, runner, shim source, and source hashes.

1. **minor — The C continuation brief specifies the wrong final verifier in the reverse construction.**

   **File and declarations:** `briefs/ch2-e2cont-batchC.md`, “Owned file and targets,” target 2, instruction to “finish through target 1’s paired decider”; `TCSlib/Complexity/ClassNP/NP.lean`, `pairedVerifier`, `paddedVerifier`, `paddedVerifier_mem_P`, `mem_NP_iff_exists_length_le`.

   Target 1’s `pairedVerifier C c V` requires both exact width `|u| = C(|x|+1)^c` and membership of `x ++ u` in its argument language. Target 2 must instead check the original upper bound `|u| ≤ C(|x|+1)^c` and consult the supplied language on `pairEncode x u`. These predicates are different in both their width test and their encoding.

   A concrete separation is `C = 1`, `c = 0`, `x = []`, `u = []`, and `V = {pairEncode [] []}`. The original bounded test accepts: `0 ≤ 1` and the pair belongs to `V`. The enlarged certificate region has length 2, so `[true, false]` strips to this empty witness and must be accepted by the padded construction. Target 1’s predicate rejects `pairEncode [] []`, since `0 ≠ 1`.

   The implementation is correct: after the shifted split, marker strip, and original-bound check, `paddedVerifier_mem_P` invokes the original `V` decider on the reconstructed pair. `audits/ch2-epoch2-agent-reports/batchC-cont.md`, “Reverse padded verifier,” explicitly explains this choice. **Resolution:** correct the brief instruction through the resolutions file to name the supplied original paired verifier, and record that the delivered proof already follows that interpretation. No proof or statement change is needed.

2. **note — B2’s read normalization establishes exact elapsed-time correspondence, including first halt.**

   **File and declarations:** `TCSlib/Complexity/ClassNP/Nondeterminism.lean`, `b2UnaryTM`, `b2UnaryCfg`, `b2_unary_read`, `b2_unary_apply`, `b2_unary_step`, `b2_unary_run`, `b2_unary_initial`, `b2_unary_mask`, `b2_unary_first`.

   I re-derived the seam from the machine definitions. At head positions 0 and `|x|+1`, both the original and same-length unary inputs read blank; at an interior position, mapping the original read to `true` gives precisely the unary read. This includes empty input, whose initial head is already at the right boundary. No work-tape symbol is normalized.

   `b2UnaryCfg` preserves the state, numeric input-head position, all work tapes and heads, and output. Since input clamping depends only on length, applying any action commutes with this configuration map. In a live state, the normalized machine and the original machine on the mapped configuration therefore choose the same action. In a halted state, both steps are absorbing. Induction gives the exact configuration equality in `b2_unary_run` for **every** elapsed time, not merely at a runtime bound. The genuine initial configurations correspond as well.

   The emission mask also agrees step by step, including an emission on the halting action. Consequently the least halt on the unary input transfers to every word of that length, and every strictly earlier state remains live. `b2_unary_first` uses the scheduler’s budget only to establish existence and an upper bound; absorption identifies its first-halt output with its completed output at the supplied bound. This is a valid replacement for the previously missing scheduler relocation. It does not infer value-independent timing from an extensional function-computation contract.

3. **note — The B2 host dispatches on actual halt, covers complete physical choice words, and proves a common all-branch bound.**

   **File and declarations:** `TCSlib/Complexity/ClassNP/Nondeterminism.lean`, `b2Host`, `b2_tables_coincide`, `b2_start`, `b2_guess_run`, `b2_guess_coverage`, `b2_assembly`, `b2_verify_timed`, `b2_host_contract`, `b2_host_bound`, `b2_compile`, `NP_subset_iUnion_NTIME`, `NP_eq_iUnion_NTIME`.

   The scheduler, assembled input, verifier work, and verifier output occupy disjoint banks. Startup copies the original input and restores its physical input head in exactly `2n+2` steps. During guessing, only physical positions selected by the scheduler’s emission mask append choices after that copy. The source-halting action is simulated before the scheduler-return state is entered, so its last emission is retained. The next transition dispatches on the stored scheduler state being `none`; the machine contains no test against the mathematical upper bound or the externally chosen first-halt function.

   `b2_tables_coincide` is a case split reducing to definitional equality for every symbol tuple outside live scheduler states. It establishes independence of the two transition tables there; it does **not** incorrectly require equal verifier runtimes for different certificates. In the verifier phase, a separate first halt is chosen for each assembled input, the complete output is summarized, and one verdict is emitted only after halt. A live prefix `[true]` or a completed multi-bit output cannot trigger acceptance.

   For `Q(n)=C(n+1)^c`, scheduler first halt `τ(n)`, verifier bound `A(n+Q(n)+1)^d`, and `m=n+Q(n)+1`, the actual accounting is

   $$H(n)=(2n+2)+\tau(n)+(n+Q(n)+2)+(A m^d+1)
   =3n+Q(n)+\tau(n)+A m^d+5.$$

   The assembly term includes the mandatory first move left from the buffer’s right blank; it also handles an empty buffer. Taking `r=c+d+1` gives `m≥1`, `r≥c+1`, `r≥d`, and `r≥1`. Thus

   $$\tau(n)\le B(n+1)^{c+1}\le Bm^r,\qquad
   Am^d\le Am^r,\qquad 3n+Q(n)+5\le5m\le5m^r,$$

   and hence `H(n) ≤ (B+A+5)m^r`, exactly as claimed. When `n=C=0`, this specializes to `m=1` and overhead 5; no positive-certificate assumption is concealed.

   `b2_host_contract` splits a complete physical branch word at the startup and actual scheduler offsets. It proves extraction on every branch and constructs a complete branch for every exact-width certificate, with irrelevant choices supplied in administrative phases. Each verifier branch is completed and then absorbed to the same deadline. `b2_compile` consequently supplies both all-branch halting and the acceptance equivalence at that deadline. The reverse inclusion and equality corollary are clean consequences.

4. **note — The banked guessing and final NTIME normalization preserve the frozen coefficient.**

   **File and declarations:** `TCSlib/Complexity/ClassNP/Nondeterminism.lean`, `contSelect`, `cont_select_surjective`, `contEmissionMask`, `contGuessTM`, `cont_guess_step`, `cont_guess_run`, `cont_guess_coverage`, `acceptsWithin_iff_of_halts`, `cont_guess_time_bound`, `cont_guess_normalize`.

   The guessing phase consumes a choice on every physical step but stores only those at actual source-emission positions. Surjectivity inserts arbitrary bits at unmarked positions and the desired witness bits at marked positions; it never identifies the witness with the first `Q(n)` choices. A zero-emission mask covers exactly the empty witness. The `captureAction` specialization preserves the scheduler bank, appends the replacement bit on an emitting action, and returns live to the host after scheduler halt.

   The arithmetic first bounds `n+C(n+1)^c+1` by `(C+1)(n+1)^max(1,c)`, raises to `r`, and applies `succ_pow_le`. The resulting coefficient is exactly

   $$K(C+1)^r\,2^{r\max(1,c)},$$

   with degree `r max(1,c)`. The derivation permits zero coefficient, zero degree, empty input, and even `r=0`. Enlargement of the decision budget uses `acceptsWithin_iff_of_halts`: accepting branches can be padded, and larger accepting branches can be truncated because **all** branches have already halted by the smaller bound. Acceptance monotonicity alone would not justify that reverse implication; the delivered proof supplies the necessary stronger premise.

5. **note — The forward NDTM compiler meets the boundary, output, and timed-composition obligations.**

   **File and declarations:** `TCSlib/Complexity/ClassNP/Nondeterminism.lean`, `choiceCore_step`, `choiceCore_run`, `choiceCore_timed`, `contPairTM`, `cont_pair_computes`, `cont_split_bridge`, `ntime_poly_subset_NP`.

   The aligned pair parser copies an undoubled source input and a separate choice suffix. The prepared simulation exposes only the copied source input through the virtual-boundary API, including repeated outward moves and empty input. Each copied choice drives exactly one simulated transition; after a source halt, the simulated configuration absorbs while remaining choices are consumed. Final acceptance requires halt and the complete captured output to be exactly `[true]`, including any emission on the halting action.

   The paired machine costs `3|x|+3|u|+6`, bounded by `3(|pairEncode x u|+1)`. Split output has length at most `2m+2`; timed startup and the downstream run therefore add at most `8m+13` beyond split time. This yields the advertised `(A+13)(m+1)^(c+2)` envelope. The proof uses timed buffered composition and actual output-length bounds, not bare computability.

   Here `cont_split_bridge` is genuinely `rfl` with coefficient `C`: this file’s equation is `n+C(n+1)^c=m`. The shift to `C+1` belongs to the different padding definition in `NP.lean`. The final choice `C=2a` correctly dominates `a(n^c+1)`. No coefficient-shift defect was found.

6. **note — The enumerator discharges the configuration-level contract, including restoration and the terminal index.**

   **File and declarations:** `TCSlib/Complexity/ClassNP/EXP.lean`, `enumCont_log_run`, `enumCont_clean_complete`, `enumCont_first_anchor`, `enumCont_common_bound`, `enumCont_from_body`, `enumMachine_contracts`, `enumLoop_run`, `enumDecider`, `NP_subset_EXP`.

   The continuation’s logged simulation records the overwritten symbols, head moves, and a separate clock mark for each live transition. Recording old blank symbols is sufficient because the clock, rather than nonblank history content, determines the undo length. Undo reverses the movements and restores the old cells; the cleanup proof restores complete source tapes and heads, clears history, retains the intended candidate, rewinds the input and capture buffers, and emits no physical output. It stops the simulated source at its actual first halt. The bound `3T+n+|y|+8` does not treat the source’s upper bound as an executable clock.

   The body separately proves fresh startup, rejection cleanup and increment, acceptance halt, and a positive first return to the anchor. The first-anchor argument uses an absorbing anchor in the comparison machine and exports the complete endpoint configuration. An accepting path cannot have visited that live absorbing anchor earlier. These facts satisfy the library’s configuration-level seam, not merely a final-answer specification.

   For width `w=C(n+1)^c`, the loop instance uses invariant `|s|=w`, initial word `replicate w false`, step `incFixed(s).getD(s)`, and fuel `R=2^w−1`. The bits-of-fuel induction gives `Nat.bits R = replicate w true`, including `w=0`. The rank-orbit bridge is used only for `i<2^w`; it does not assert a nonexistent final increment beyond overflow. The terminal index is `R+1=2^w`, so width zero still tests the single empty candidate.

   The common body bound and library overhead are fixed before the input is chosen. `enumCont_from_body` translates the returned configurations into the original `enumMachine_contracts` statement with terminal output `[false]`. `enumDecider` sums those segments using the checkpoint’s **already-halted-terminal** lemma `enumLoop_run`, not the incompatible empty-output-terminal lemma. The final exponential majorization handles `n=0` and `n=1` separately. This closes the shared dependency of `NP_subset_EXP` and the two HALT results without an admission or a weakened contract.

7. **note — TMSAT membership respects exact parsing, clock conversion, timeout, and complete-answer recognition.**

   **File and declarations:** `TCSlib/Complexity/ClassNP/TMSAT.lean`, `tmsatTakeTM`, `tmsat_take_computes`, `tmsatGood`, `tmsatRequest`, `tmsat_request_poly`, `tmsat_good_bounds`, `tmsat_comp_on_image`, `tmsatAnswer_accept`, `tmsat_simulation_budget`, `TMSAT_mem_NP`.

   The odd split is instantiated at `(1,1)` and reconstructs a certificate of length `|instance|+1`. Grammar checks validate the outer split and all three levels of the right-nested quadruple, then both unary fields. The variable-prefix machine counts the doubled first field and emits exactly the requested prefix of the payload; zero width and a payload shorter than the requested width are covered. Malformed fields cannot acquire meaning merely because the projection primitives are total.

   Clock conversion applies `lengthBits` through `pairMapSnd` to the intended payload while preserving the rest of the request. A malformed instance is mapped to a well-formed zero-deadline request. A genuine source starts live and cannot halt at time zero, so this fallback cannot yield `[true,true]`.

   The bridge supplies one simulator before code/input/deadline selection and both completion and timeout behavior. The budget uses the canonizer bound at the actual code length, followed by its polynomial envelope; no monotonicity of the canonizer’s raw time function is assumed. `tmsat_comp_on_image` requires totality only on the well-formed requests actually emitted, with the downstream runtime evaluated at the emitted length. Acceptance compares the entire simulator answer with `[true,true]`, ruling out timeout and all other source outputs. Padding the bounded witness is sound because the parsed requested width is at most the instance length. Bridge consumption is through its public statement only.

8. **note — Polynomial constructibility and TMSAT hardness preserve exact values throughout the reduction.**

   **File and declarations:** `TCSlib/Complexity/ClassNP/TMSAT.lean`, `polyUnaryTM`, `poly_loop`, `poly_unary_computes`, `timeConstructible_poly`, `tmsat_deadline_bound`, `tmsat_certificate_unary`, `tmsat_reduction_correct`, `TMSAT_NPHard`, `TMSAT_NPComplete`.

   The checkpoint unary machine enumerates a `(c+1)`-dimensional box of side `n+1`, emits exactly `C` symbols per point, and restores inner-loop heads before reuse. Its proved cost is `(C+5(c+1)+4)(n+1)^(c+1)`, including startup and final halt. Timed composition with the public binary length counter yields the exact polynomial’s binary representation within a constant multiple of that polynomial plus one. Empty input is handled by the deliberately added unary cell; the helper also permits coefficient zero.

   The hardness wrapper first rejects malformed pairs and otherwise decides the original verifier on the concatenation. Its total timed contract is established before one-work-tape binary normalization. Coding then needs only `decode_encode`; the proof does not smuggle effective-code hypotheses into the general `MachineCode` hardness theorem.

   With original certificate parameters `C₀,c₀`, wrapper parameters `B,e`, normalization coefficient `K`, and `r=max(1,c₀)`, the reduction emits exactly

   $$Q(n)=C_0(n+1)^{c_0},\quad
   D=(K+1)(B+1)^2(C_0+3)^{2e},\quad
   T'(n)=D(n+1)^{2er}.$$

   The bound on paired-input length is `(C₀+3)(n+1)^r`; raising and squaring gives precisely this deadline. Only the deadline is enlarged. The certificate output retains exact length `Q(n)` in the zero-coefficient, degree-zero, and positive-degree cases. The live deadline emitter uses `polyUnaryTM (2er−1) D`, justified by `e≥1` and `r≥1`, so its exponent is exactly `2er`.

   The §9c pairing construction retains the original input and assembles the exact unary fields in the frozen right-nested order. Quadruple injectivity and uniqueness of the completed normalized wrapper output prove both directions of the reduction. `TMSAT_NPComplete` then combines the independently proved membership and hardness halves with their respective hypotheses. No issue was found.

9. **note — Exercise 2.1 and the HALT pair use the required original predicates and timed plumbing.**

   **File and declarations:** `TCSlib/Complexity/ClassNP/NP.lean`, `verifier_poly_pair`, `verifier_poly_reverseBound`, `pairedVerifier_mem_P`, `paddedVerifier_mem_P`, `mem_NP_iff_exists_length_le`; `TCSlib/Complexity/ClassNP/Reductions.lean`, `acceptTM`, `acceptTM_halts_iff`, `fixedPair_polyTime`, `HALT_NPHard`, `HALT_not_mem_NP`.

   The forward Exercise 2.1 construction tests both orientations of exact width. Its reverse orientation constructs unary `Q+1` and tests `Q+1≤|u|+1`, equivalently `Q≤|u|`; together with the original P8 upper bound this forces equality. The §9c pairing recipe correctly threads the whole retained request when a cross-component function is needed.

   The reverse construction uses P10 at `(C+1,c)`, guards split and marker failure, then P8 at `(C,c)` measured against the retained original prefix. An oversized stripped witness is rejected even if it fitted the enlarged certificate region. The final call uses the original paired verifier, as required by finding 1. Coefficient zero, degree zero, an empty witness, and absence of a marker are covered.

   For HALT hardness, the polynomial fixed-prefix map is a concrete timed machine. After a total singleton-output decider is normalized to one work tape, `acceptTM` updates the stored output bit before redirecting a source-halting action: true becomes actual halt, false becomes a live loop. Its singleton-output premise prevents a last-bit test from being misused on arbitrary multi-bit outputs. The reduction uses only the frozen coding vocabulary. `HALT_not_mem_NP` obtains a total EXP decider from NP membership and contradicts the audited effective-code HALT noncomputability result. Neither route replaces a timed obligation by untimed computability.

10. **minor — E5’s description of “superseded” routes needs a live-dependency correction; the deferral itself is sound.**

    **File and declarations:** `audits/ch2-epoch2-pack.md`, “Dispositions requested,” E5; `TCSlib/Complexity/ClassNP/EXP.lean`, `enumLoop_run`; `TCSlib/Complexity/ClassNP/Reductions.lean`, `prefixTM`, `fixedPair_polyTime`; `TCSlib/Complexity/ClassNP/TMSAT.lean`, `polyUnaryTM`, `poly_unary_computes`.

    The pack groups these helpers among families superseded by the continuations’ library routes. The kernel dependency walk instead establishes the following live paths:

    | Final theorem | Still-consumed checkpoint route |
    |---|---|
    | `NP_subset_EXP` | `enumDecider` → `enumLoop_run` |
    | `HALT_NPHard` | `fixedPair_polyTime` → timed fixed-prefix construction → `prefixTM` |
    | `timeConstructible_poly` | `poly_unary_computes` → `polyUnaryTM` |
    | `TMSAT_NPHard` | Exact unary deadline emission → `poly_unary_computes` / `polyUnaryTM` |

    In contrast, the checkpoint `enumCarryTM` and `enumCaptureTM` are absent from the `NP_subset_EXP` closure, and `choiceCopyTM` is absent from the completed forward inclusion’s closure. “Partially dead” is accurate; classifying all listed routes as already replaced is not. The subsumption of a *promotion request* by a catalog entry also does not mean its existing client was rewritten.

    These live checkpoint contracts are finished, were included in this audit, and have clean kernel closures. They do not smuggle an unaudited machine-existence assumption. **Approve serial post-gate E5**, but record the actual live/dead inventory in resolutions. Deleting a dead family, replacing a live implementation with a catalog instance, and relocating a family are distinct changes. For a live replacement, review the timed and configuration contracts before deletion and rerun client closures; byte-identical relocation is not the applicable correctness argument for a changed implementation.

11. **note — Current closure and helper hygiene are independently verified; the six maintainer attestations have the following evidence status.**

    **Files and declarations:** `audits/evidence/ch2-epoch2/span-attestation.md`, sections 1–6; `audits/programs/ch2-e2-ClosureAxioms.lean`, `visit`, `roots`, and its `run_cmd`; the eleven target declarations and all private declarations in the five owned source files.

    The supplied closure traversal follows kernel types and values, including opaque values and inductive constructors, and fails on an unexpected admission root or axiom. I reran it against the fresh project oleans. All eleven targets plus `timed_universal_quantitative` have empty admission-root sets and at most `{propext, Classical.choice, Quot.sound}`. The five Chapter-1/library regressions pass, and `EXP_subset_NEXP` has exactly its own admission root.

    Target closure alone would miss unused private admissions. I therefore additionally enumerated all 386 named source helpers, required each to exist in the checked environment, and traversed all 1,167 kernel declarations under the five modules’ private prefixes, including generated declarations and all their dependencies. This wider traversal also has **no admission roots** and exactly the standard three axioms in its union. The source/helper counts are:

    | File | Source privates | Private/generated kernel declarations |
    |---|---:|---:|
    | `TCSlib/Complexity/ClassNP/EXP.lean` | 135 | 428 |
    | `TCSlib/Complexity/ClassNP/Nondeterminism.lean` | 110 | 294 |
    | `TCSlib/Complexity/ClassNP/NP.lean` | 38 | 78 |
    | `TCSlib/Complexity/ClassNP/Reductions.lean` | 16 | 56 |
    | `TCSlib/Complexity/ClassNP/TMSAT.lean` | 87 | 311 |
    | **Total** | **386** | **1,167** |

    | Attestation | Verification or qualification |
    |---|---|
    | **1. Whole-span freeze** | Independently verified for the supplied five-file endpoint against available baseline `f317f0c7`: exactly eleven removed target `sorry` lines, six docstring-tail splices, and the one token-identical NP statement-line respacing. Comment-aware extraction preserves every prior public name and header; only the sanctioned bridge is added. The reported imports match and elaborate in the supplied order. Checkpoint-to-final deletion inspection finds no rewrite of completed checkpoint helper bodies; the admitted `enumMachine_contracts` body is filled, and the separately audited bridge changes are distinguished. This establishes the supplied source freeze, not independent possession of final integration commit `2e176f60`. |
    | **2. Nine deliveries and integration provenance** | The available history corroborates the ten fill commits, with original B2 commit `022cd0f3` corresponding to the delivered source; the supplied B2 source hash is reproduced as `d2f7358daaf0c0dd43779728bf1e1b536970b82cdd58b2c7645a5b8ccfcc8317`. The two available earlier maintainer integration commits touch no owned proof source. The bundle contains reports, not all nine archive payloads and replay worktrees, and the final maintainer integration object is unavailable locally. Thus all-nine checksum/replay execution and all-three integration-commit claims remain maintainer attestations, not independently reproduced facts. No contradictory evidence was found. |
    | **3. Elaboration and admission ledger** | Independently reproduced the final 57/57 sweep, zero errors, and exactly 21 admission warnings: Nondeterminism 5, EXP 1, SAT 3, Tautology 2, CookLevin 10. This agrees with the supplied final log and the net removal of eleven admissions, giving 38/59 original admissions closed. Earlier 32→29→23 integration runs are consistent historical records; I did not rerun their past trees. |
    | **4. Axioms** | Independently reproduced the final program’s expectations and strengthened coverage to every in-scope source helper and associated private/generated kernel declaration as above. The reported interim `enumMachine_contracts` roots remain historical execution claims; the current contract and all final consumers are now clean. |
    | **5. Policy and attribution** | Independently reran the repository linter on the supplied ClassNP source: 0 FAIL, 3 WARN, at exactly 2,887 / 2,627 / 1,908 lines. Original sketch text and attributions are retained, with appended completion notes at the recorded seams. The linter prints 86 TMSAT privates because its declaration regex misses `private noncomputable def tmsatWrapperOutput`; the independent source/environment inventory confirms the attestation’s correct count of 87. This is a counting limitation of that lint output, not a missing helper. |
    | **6. Disclosed deviations** | The attached reports explicitly label the four initial deliveries partial, record C’s respacing, and disclose the cache/shim recoveries, including B2’s `TAR_OPTIONS=--no-same-owner`. B’s continuation is also explicitly partial pending B2. The present source does not conceal those frontiers as completed results. Past host operations and unchanged-pin execution are corroborated disclosures rather than independently replayed events; my final rebuild uses the stated pins. Finding 1 should be added as a resolutions clarification of C’s reported, correct final-verifier choice. |

    These qualifications delimit provenance evidence; they are not unexplained source gaps or proof failures. I found no new axiom, admission, unchecked evaluation escape, or dependency on an unfinished checkpoint contract in the audited proof/helper closure.

12. **note — Approve the D7 extension after this gate; preserve its existing private-visibility qualification.**

    **Files and declarations:** `audits/ch2-epoch2-pack.md`, “D7 extension”; `audits/ch1-libfill-resolutions.md`, disposition D7; the private families and public clients in `TCSlib/Complexity/ClassNP/EXP.lean`, `TCSlib/Complexity/ClassNP/Nondeterminism.lean`, and `TCSlib/Complexity/ClassNP/TMSAT.lean`.

    The size exceptions impede review but do not create a missing proof premise or a dependency cycle. The fresh ordered build and closure checks provide no reason to force a split before E3 fills consume these modules. Serial trailing refactoring is appropriate under the recorded ownership exceptions.

    Carry forward the **full** approved D7 discipline: byte-identical relocation and ordered-sequence comparison alone do not solve cross-file access to private names. Keep dependent private families together, or separately review any visibility/interface change. Re-run the module-order sweep, target closures, the all-private/generated traversal for these five files, and the kernel export inventory; preserve the existing whole-Build checks when those files are involved. Coordinate E5 replacements separately from moves so a changed proof route is not represented as mere relocation.

13. **note — D6 remains appropriately deferred.**

    **Files and declarations:** `audits/ch2-epoch2-pack.md`, D6; `audits/ch1-libfill-resolutions.md`, disposition D6; the queued library promotions `timed_input_bound` and `timed_rewind`.

    The completed epoch-2 proofs consume available proved contracts or establish their own local configuration facts. They require no future public promotion to elaborate or close their kernel dependencies. This does not assert that the existing library implementations never use those private lemmas internally. Keep promotion as a separate serial API change, retaining all hypotheses and tape/head/output preservation conclusions and checking clients before replacing private copies. No additional promotion is a prerequisite for this gate.

**Notation glossary.** Throughout, `n` is the original input length; `Q(n)` is the exact certificate length; `τ(n)` is the normalized scheduler’s actual first halt; `m=n+Q(n)+1`; `H(n)` is the complete reverse-host deadline. In findings 3–4, `C,c` are certificate parameters, `A,d` verifier runtime parameters, `B` the scheduler coefficient, and `r=c+d+1`; `K,r` in the standalone normalization inequality are its arbitrary envelope parameters. In finding 6, `w=Q(n)` and `R=2^w−1` is loop fuel. In finding 8, `C₀,c₀` are the original certificate parameters, `B,e` the wrapper parameters, `K` the one-tape normalization coefficient, `r=max(1,c₀)`, and `D,T'` are the displayed exact deadline coefficient and function. Their scopes are local to the indicated findings.
