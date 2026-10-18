**Chapter-1 machine-library fill: proof audit — 2026-10-04**

**Verdict: 0 blockers, 0 majors, 2 minors. Recommend closing the proof gate on the supplied snapshot.** The two actionable findings concern a proof sketch and the scope of an audit diagnostic. No proof repair is requested. Historical integration claims that cannot be independently established from this bundle are explicitly qualified in finding 10.

Scope: the 23 filled public contracts and all 282 explicit private declarations in the four supplied `Build/` files. The previously audited statements and attached model definitions were treated as ground truth. The pack plus all 32 promised attachments were present. Review included source inspection, independent phase and coefficient calculations, declaration/import inventories, a normalized harvest comparison, and recounting the attached logs. Lean, Lake, and Elan were unavailable in this audit workspace: **this is not a newly executed Lean elaboration or kernel traversal**. Execution evidence is the supplied maintainer logs, which identify integrated HEAD `c013f270402ec5babaf33f94d3c15c3ca2589239`. The delivery reports specify Lean 4.25.0 and mathlib `029db123ddaa`.

References below are repository-relative, with one-based line numbers in the supplied files. `Build/` abbreviates `TCSlib/Complexity/TuringMachine/Build/`; `TM/` abbreviates `TCSlib/Complexity/TuringMachine/`. The bundle SHA-256 is `f0ef58b8f3253811957ded769cecff5367702e488f29ebaf517b1bb7e4456fd6`.

1. **[minor] The decision-loop sketch still names the summation lemma that R3-1 ruled out.**

   **References:** `Build/Loop.lean:2495–2512,2552–2554`; `audits/ch1-infra-resolutions.md:25`.

   Lines 2495–2499 correctly explain the already-halted-terminal route, but lines 2509–2510 still say that `Turing.loop_run` sums the seam family. That lemma requires an empty-output terminal; this family has terminal output `[false]`. The actual proof correctly invokes `loop_halted_run` at line 2552. This is residual contradictory documentation, not a recurrence of the former proof obstruction. The resolution record's statement that the description sites were corrected should be read with this qualification.

   **Requested correction:** add a local erratum identifying `loop_halted_run`, or make an explicitly authorized documentation correction after the current docstring freeze. The neighboring reference to amortized borrow should also point readers to the actual worst-case-width argument at lines 2384–2390. No statement or proof change is needed.

2. **[minor] The attached closure program's success message overstates its traversal scope.**

   **References:** `audits/programs/ch1-libfill-ClosureAxioms.lean:7–11,23–38,53–100`; `audits/logs/ch1-libfill4-axioms.log:32`; `audits/ch1-lib-agent-reports/batchP4.md:62,80`.

   The program traverses the dependency closures of its 23 library targets and five regression targets. It does not enumerate every checked declaration originating in the four `Build/` modules. Its line-100 assertion that “the Build tree carries zero admissions” therefore states more than this program checks. Unused private lemmas are a real distinction here: for example, `loopBody_capture` (`Build/Loop.lean:696`) and `splitFind_none` (`Build/Primitives.lean:2965`) have no subsequent source references. A new unused admitted helper need not affect any listed target's closure.

   The separate 1,171-declaration P4 traversal is reported, but its program and inventory are not attached. The current sources contain no admission tokens, and the final sweep reports no Build admission warnings; this finding identifies an audit-instrument scope mismatch, not an admission in the delivered proofs. The program also retains obsolete checkpoint comments at lines 7–11 and after the line-100 command.

   **Requested correction:** make the success message describe the checked target closures and update the stale comments. Alternatively, add explicit whole-module enumeration before claiming whole-tree coverage. Preserve the independent whole-tree check for unused helpers and generated descendants.

3. **[note] The loop host discharges the construction ledger, including zero fuel, terminal choice, and coefficient 10.**

   **References:** `Build/Loop.lean:568–689,737–835,1230–1364,1445–1481,1561–1644,1858–1966,2060–2189,2213–2358,2444–2475,2548–2568,2578–2608,2665–2690`; ledger comparison: `audits/ch1-lib-agent-reports/batchL-continuation.md:77–145` and `batchL2.md:25–68`.

   The tape layout keeps the body, stop flag, counter, fuel residue, and capture tape distinct. Fuel copying erases the capture tape; the synchronized return scan tests the counter, which still contains the word, rather than the erased capture cells. The input rewind preserves the work configuration. The body wrapper's release bit permits one action from an active anchor; subsequent anchor recognition and genuine halt have different flag values. Consequently an accepting empty payload is distinguishable from exhaustion.

   Write `T = T(x.length)`, let `u ≤ T` be the first fuel halt, and let `L` be the binary fuel width. The fuel output bound gives `L ≤ T`; every debit preserves this width. Recomputing the transitions gives:

   | Component | Independently recomputed bound |
   |---|---|
   | Fuel rewind, copy, synchronized return | `1 + 3(L+1) = 3L+4` |
   | Native-input rewind after fuel | `p+2 ≤ u+3`, since `p ≤ u+1` |
   | Prepared startup | `u + 3L+4 + (u+3) ≤ 5T+7` |
   | Body startup, anchor stop, release | `≤ T+2` |
   | Entire startup | `≤ 6T+9 ≤ 9(T+1)` |
   | Counter borrow and rewind | `2j+2 ≤ 2L+2`, where `j ≤ L` |
   | Rejecting round, including final exhaustion emission | `≤ t+2L+5` |
   | Accepting round, including payload replay | `≤ 3t+3`, because payload length is at most the first-halt time, itself at most `t` |
   | Common segment envelope | `≤ 3t+2L+5 ≤ 5T+5 ≤ 10(T+1)` |

   Thus `max 1 (max 9 (3+2+5)) = 10` is valid without amortization or an extra logarithmic factor. Phase 11 is charged to the final rejecting segment, not to an additional unbudgeted round.

   Startup performs no debit, so `R=0` still tests candidate zero, including width-zero fuel. In `loopHost_contracts`, each candidate configuration is defined and proved locally even if an earlier acceptance makes it unreachable. If the last candidate rejects, the terminal is its actual underflow-and-emission endpoint. If it accepts, an arbitrary halted false/empty terminal is legitimate because no rejecting edge must reach it. The input-indexed invariant is established for every orbit point used by a local contract.

   The abstract `loop_run` induction is sound for its own frozen terminal convention. The decision proof uses `loop_halted_run`; the find proof uses `loop_find_run` and retains the first accepted payload, including `[]`. Startup plus at most `R+1` segments gives `10(T+1)(R+2)` with the same host constant.

4. **[note] Capture lockstep and halt redirection preserve the required endpoint information.**

   **References:** `Build/Wrappers.lean:93–146,166–196,208–314,326–363`; model interface: `TM/Configuration.lean:199–207`.

   `capture_apply` matches the model's write-before-head-movement semantics. An emission writes at the old capture head, extends the represented word from `pre ++ output` by that bit, and advances the head exactly once. This occurs even when the same source action halts. The other work tapes, native-input movement, and arbitrary host output `out₀` are preserved as specified.

   In `capture_run`, the strict-prefix liveness hypothesis is used exactly where another simulated transition is needed. It allows a halt on transition `t` but does not extend the simulation beyond that halt, when the host is already in its return state. The zero-step case and arbitrary capture prefix are retained; the result is not restricted to initialized or empty-prefix configurations.

   Redirection updates its optional last-output register before deciding whether a halting transition matches `haltOn`. Its all-time correspondence handles both absorbing successful halts and the stationary live state after mismatch. `redirectTM_live` derives a contradiction through output uniqueness if an alleged redirected halt disagrees with the completed source output. Empty source output therefore remains live, as required.

5. **[note] The split body's global trace argument and native-bit emitter close the P3 frontier.**

   **References:** `Build/Primitives.lean:3053–3221,3226–3323,3405–3415,3441–3603,3607–3651,3669–3735,3773–3908,3922–4198,4206–4257,4261–4284,4319–4364`; frontier comparison: `audits/ch1-lib-agent-reports/batchP3-continuation.md:39–90`.

   `splitSafe` excludes the anchor at every time through a phase endpoint, inclusively. `splitSafe_add` splits a time index at the exact seam and checks both resulting intervals. The body proof composes preparation, dispatch, counted evaluation, check, rewind, and the selected finishing path using actual configuration equalities. It does not infer a global first return merely from separate subroutines' first-return lemmas. The initial departure contributes one positive step; on rejection the final explicit anchor transition lies outside the safe prefix. Every strict interior time is covered even when an individual subphase has duration zero.

   Counted evaluation suppresses source output and advances the native input once per emission, including an emission on the source's halting action. The overflow flag records attempts to consume beyond the saturated right boundary. Testing blank input together with absence of overflow is therefore equivalent to `s.length + out.length = w.length`; testing the saturated position alone would have been insufficient. The source's virtual input is empty, so its input-head movements cannot change the symbol supplied to its transition table.

   Acceptance implies `s.length ≤ w.length`. In `splitEmitTM`, candidate cells are tested only for presence: both copies of each prefix bit come from native input. The separator is emitted explicitly, and suffix copying resumes at the exact native split. Its runtime is `2|s|+2 + (|w|-|s|+1) = |s|+|w|+3`. No unary assumption on the candidate's bit values is used.

   Rejection clears the complete scratch words, including the extra cell at index `s.length`, preserves the old candidate bits, appends a true exactly when the old length is at most the input length, and restores every work head and the input head. At length `|w|+1` it returns the same arbitrary-bit candidate silently in positive time. The global anchor argument covers this stall as well.

   Both remaining source obligations are supplied: the positive-exponent box generator and the zero-exponent constant prefix machine on empty virtual input. `splitSolve_of_body` is genuinely instantiated, rather than being used as an assumed existence theorem. The orbit/search lemmas then identify candidates `0…n`, least success, failure, and the required native split output.

6. **[note] Constants 5 and 40, and the split-body envelope, survive independent derivation; the arbitrary-time composition trap is avoided.**

   **References:** `Build/Wrappers.lean:456–502,613–644,659–685`; `Build/Primitives.lean:2063–2109,2425–2463,2526–2590,2592–2719,2746–2768,4076–4198,4292–4340`.

   For the conditional, let the decider's first halt be `t ≤ T₀(n)`. Its input position is at most `t+1`. The two captured-bit reading transitions and a rewind of at most `t+3` steps give prefix time `2T₀(n)+5`. With `B = max(T₁(n),T₂(n))`, the full time is bounded by `2T₀(n)+5+B ≤ 5(T₀(n)+B+1)`. The selected branch begins on the original input with fresh branch tapes. No monotonicity of any supplied time function is required or silently used.

   For the threaded map, the extractor's actual output is `y`, with `|y| ≤ n` even on malformed input. The low-level buffered-composition startup costs at most `5(n+1)+|y|+2 ≤ 6(n+1)+1`. The second machine is run within `Tg(|y|) ≤ Tg(n)`. Thus the captured source budget is `T = 6(n+1)+Tg(n)+1`, not a budget containing `Tg(5(n+1))`.

   The surrounding map controller costs at most `3T+4n+10 ≤ 4(T+n+3)`: source capture and rewinds, silent validation, native-prefix/separator replay, and captured-payload replay are all charged. Substitution gives

   `4(6(n+1)+Tg(n)+1+n+3) = 28n+4Tg(n)+40 ≤ 40(n+1+Tg(n))`.

   For the split body, put `l=|s|`, `n=|w|`, and let the source budget be `T`. Directly summing the dispatches and proved scans gives accepting time at most `T+3l+2n+12` and rejecting time at most `T+4l+2n+15`. Both fit `T+5l+3n+20`. Under `l ≤ n+1`,

   `l+1 ≤ n+2 ≤ 2(n+1)` and `(l+1)^e ≤ 2^e (n+1)^(e+1)`.

   The source bound is `(C+1+5e)(l+1)^e+1`. The remaining overhead satisfies `5l+3n+21 ≤ 8n+26 ≤ 40(n+1) ≤ 40(n+1)^(e+1)`. This proves the recorded coefficient `A=(C+1+5e)2^e+40`, including `n=0`, `e=0`, and `C=0`. Enlarging the common coefficient to cover the fuel machine and multiplying by `n+2 ≤ 2(n+1)` yields the stated final exponent `e+2` (`Build/Primitives.lean:2993–3003,4206–4257`).

   This audit does not make the stronger, false assertion that no coarse composition bound is ever used: `polyBits` and `pairLenCheck` legitimately absorb such bounds for fixed linear/polynomial time functions. The forbidden arbitrary-`Tg` substitution is absent.

7. **[note] The harvested generator, fixed-width increment, length counter, and prefix primitives retain the source semantics.**

   **References:** `Build/Primitives.lean:130–208,443–550,983–1405,2121–2205,2219–2230,4413–4416`; `TCSlib/Complexity/ClassNP/TMSAT.lean:116–541`; `TCSlib/Complexity/ClassNP/EXP.lean:103–106,249–257,289–302,397–409`; `TCSlib/Complexity/ClassNP/Reductions.lean:286–364`; `TCSlib/Complexity/ClassP/TimeConstructible.lean:68–71,431–455`.

   A mechanical comparison of all 20 generator declarations, from `PolyControl` through `poly_unary_computes`, found identical declaration text after consistent identifier renaming and removal of comments and whitespace. The recurrence is `F(0)=C+1` and `F(r+1)=q(F(r)+2)+q+2`, bounded by `(C+1+5r)q^r` for positive `q`. The positive public exponent case chooses generator parameter `d` when `e=d+1`; the output exponent is therefore exactly `e`, not `e+1`. The constant case and zero coefficient do not require a positive output length. Binary conversion composes with a linear length counter and absorbs coefficients without doubling the polynomial degree.

   `incFixed` has the same little-endian recursion as `enumInc`. The new machine intentionally differs from the in-place carry controller: it detects a first false before emitting anything. An all-true word, including the empty word, halts silently; a first false at index `j` leads to `j` false bits, one true, then the untouched suffix. Detection, rewind, and emission cost at most `3(n+1)` and preserve width.

   Unpacking `TimeConstructible id` provides exactly a machine computing `Nat.bits x.length` within `c(n+1)`, not merely a unary clock. The attached witness theorem explicitly supplies `c=5`, including the empty-input case. The prefix family likewise emits the fixed word then copies native input in `|prefix|+n+1`, including the final blank-reading halt. These are the interfaces used by `prepend` and `pairEncodeFixed`. No private declaration from a later harvest-source module is imported into the fill.

8. **[note] Parser and marker proofs discharge validation before physical output.**

   **References:** `Build/Primitives.lean:272–368,570–977,1418–1755,1757–2010,2015–2059,2234–2314,2322–2358,2670–2719,2782–2911`.

   The shared pair parser consumes aligned two-bit blocks: `00` and `11` extend the decoded prefix; `01` terminates it; `10`, missing separators, and incomplete blocks reject. `pairExtractTM` buffers the decoded prefix silently and begins replay only after that validated separator. An invalid suffix of a partially decoded prefix cannot leak output. The three extractor modes use the same proof and `5(n+1)` envelope, including the silent buffer traversal in suffix-only mode. `pairValid` emits only its terminal verdict. `pairDup` has exact ledger `2n + 1 + (n+1) + 1 + (n+1) = 4(n+1)`.

   `pairLenCheck` captures the polynomial bound, rewinds native input, parses the aligned prefix, and uses captured cells only for the suffix countdown. The parser never spends the countdown on prefix bits. The terminal test is the required inequality: an empty suffix succeeds even at zero remaining count, whereas a nonempty suffix at zero count rejects. Malformed inputs return `[false]` independently of any work already performed by the captured generator. The fixed polynomial coefficient absorbs the extractor's linear-time composition bound at `Build/Primitives.lean:2808–2829`.

   `stripLast` first tests for a true bit in the **parsed payload**. Thus a true in the encoded prefix or delimiter cannot authorize stripping an all-false payload. Only a valid pair with a payload marker takes the raw-strip branch. The raw machine buffers the entire encoding, erases the trailing false run and final true, then replays the retained prefix. `catalogMarker_cases` and pair reconstruction show that this retains the complete pairing prefix and exactly the required payload prefix. Invalid pairs and marker-free payloads select empty output. Its linear construction is legitimately weakened to the frozen quadratic envelope.

   The threaded map also validates before emitting its retained native prefix; arbitrary `g []` output computed on malformed input stays captured and cannot leak. This complements the timing check in finding 6.

9. **[note] Helper hygiene is satisfactory, with an explicit rather than disguised duplicate proof wrapper.**

   **References:** `Build/Primitives.lean:983–995,3686–3702,4206–4257,4319–4364,4392–4399`; `Build/Loop.lean:2213–2358`; `audits/ch1-lib-agent-reports/batchP4.md:78–84`; `audits/logs/ch1-libfill-lint.log:9–13`.

   The current source inventory is:

   | File | Public source declarations | Explicit private declarations | Lines |
   |---|---:|---:|---:|
   | `Build/Wrappers.lean` | 7 | 20 | 687 |
   | `Build/Primitives.lean` | 15 | 167 | 4,418 |
   | `Build/Loop.lean` | 5 | 95 | 2,693 |
   | `Build/Convention.lean` | 6 | 0 | 122 |

   Comment-stripped scans found no `sorry`, `admit`, `axiom`, `unsafe`, `implemented_by`, `native_decide`, or custom elaborator/macro bypass in these files. The new finite control types use explicit private instances; the reported discarded public `deriving` instance is absent from the supplied P4 source. Source inventory alone is not a kernel-export freeze check.

   `splitSolve_closed` literally repeats the final public proposition. It is therefore an exception to a literal “no restatement” reading of the pack, but it is not a hidden assumption or an unfilled frontier: its two exponent cases construct the sources and discharge the concrete body's hypotheses. The public theorem is an explicit alias at line 4399. The report and local docstring disclose the purpose—keeping generated proof auxiliaries private. Similarly, `loopHost_contracts` proves the concrete host's stronger configuration contract; it does not replace construction by an existential assumption. Generic simulation helpers are used with explicit table agreement, endpoint, and liveness hypotheses. Beyond the already disclosed D6 candidates, no further helper needs promotion to make the current public proofs usable.

10. **[note] Maintainer attestations 1–6: current-source and final-log claims are corroborated; historical whole-span claims remain partly unverified.**

    **References:** `audits/ch1-libfill-pack.md:24–63,144–165`.

    | Attestation | Audit disposition and evidence |
    |---|---|
    | **1. Whole-span freeze** | **Not independently verified in its historical form.** The current public counts are exactly 7/15/5/6, and all 23 target proofs are present without source admissions. However, the bundle contains neither the `e346139c` baseline nor the complete patches/diff, so “deletes exactly 23 placeholders and nothing else,” zero additions over the entire span, unchanged public order/content/docstrings, and append-only module prose cannot be established by comparing final files alone. P4 reports 78 preserved public kernel declarations, but its stated baseline is `494d4835`, already after earlier fills (`batchP4.md:8,63–64,82`). That last-step comparison does not independently establish the entire `e346139c`→pack claim. No contrary diff is available either. |
    | **2. Per-delivery verification** | **Partly corroborated, historical replay unverified.** All current imports among modules represented in the supplied 57-module order go strictly forward; the Build dependency order is consistent and introduces no visible cycle. The reports disclose the harvest and added import routes. The eight archives, their manifests and patches, isolated replay trees, decision log, and P3/P4 integrated-source hash attestations are not attached. Their checksums and byte-identical replay cannot be reproduced from the reports or final source alone. |
    | **3. Elaboration** | **Final log corroborated; earlier progression and execution freshness remain attested.** Recounting `ch1-libfill4-sweep.log` finds exactly 57 headers, in exactly `scripts/ab_ch1_module_order.txt:1–57` order, zero `error:` diagnostics, and exactly 28 admission warnings, all outside Build. The admissions occur at log lines 1013–1051; lines 1052–1059 finish the sweep successfully. The log identifies HEAD and timestamps at lines 1–3. The earlier 33→30→29 counts and fresh-olean procedure cannot be independently replayed from the attached final log. |
    | **4. Axioms** | **The attached target-closure check is corroborated.** The program inspects checked declarations' types and opaque values, follows constructor dependencies, compares exact expected root sets, and separately rejects nonstandard axioms and unexpected `sorryAx` (`ClosureAxioms.lean:23–46,87–99`). All 23 library expectations are empty; the log records them at lines 4–26. Three headline checks are empty and the two campaign roots have the specified values at lines 27–31; exit is zero at line 33. The log prints roots, not the actual axiom arrays; the program enforces the subset test. The separate whole-Build count of 1,171 and its generated-declaration/export checks remain P4-report evidence, not checks reproducible from the attached program. See finding 2. |
    | **5. Policy** | **Current counts and documentation practice corroborated; historical exception entries unverified.** The lint log has 8 TuringMachine warnings and 1 ClassNP warning, with zero failures (`ch1-libfill-lint.log:1–13,45–61`). Exactly two warnings are the grown Build files; the other seven are outside Build. Current sizes match the source recount. Helper invariant sketches and harvest attributions are present. The reports justify the two size exceptions, but their integration decision-log entries and claims of byte-identical preservation require the missing historical evidence. |
    | **6. Deviations** | **Consistent with reports, not independently reproduced.** P3 explicitly records the campaign branch name (`batchP3.md:8–11`); L2 records the procfs/cache workaround and unchanged-pin claim (`batchL2.md:102–113`), as does P2 (`batchP2.md:86–97`). The archive top-level layout, host recovery logs, actual dependency checkouts, and unchanged manifests are not supplied. Nothing in the delivered Lean sources reveals a proof or pin workaround. The ordinary-host verification claim belongs to the maintainer execution record. |

    These qualifications are evidence limits, not findings that the attestations are false. To obtain independent historical freeze sign-off, retain the original baseline, whole-span diff, delivery checksums/replay records, and public kernel inventories against the **original** baseline. They are not substituted by current declaration counts or the last P4 baseline comparison. The proof-gate recommendation above is based on the inspected final proofs and supplied final execution evidence, not a claim to have reproduced all six historical attestations.

11. **[note] D6: approve post-gate serial promotion of both generic lemmas.**

    **References:** `Build/Wrappers.lean:456–502`; `audits/ch1-libfill-pack.md:67–76`; `audits/ch1-lib-agent-reports/batchW.md:94–98`.

    `timed_input_bound` is a useful general run-calculus bound, valid from arbitrary configurations and across halted steps. `timed_rewind` supplies a quantitative interface missing from the qualitative rewind theorem: at most `inputPos+2` transitions, with all work tapes, heads, and accumulated output preserved. Its mandatory first left move handles the right blank correctly and also covers the left boundary and empty input. Both are independent of the conditional controller and are worth promoting.

    Agree with the maintainer's deferral: the present private proofs and their later adaptations are complete, so promotion is deduplication, not a proof-gate prerequisite. Perform it as a separate serial API change, preserving the current hypotheses and field-preservation conclusion; replace local copies only after the promoted lemmas and affected clients elaborate.

12. **[note] D7: allow the size split to trail the gate and E2 consumption.**

    **References:** `audits/ch1-libfill-pack.md:77–86`; `audits/logs/ch1-libfill-lint.log:1–13`; `Build/Loop.lean:2213–2433`; `Build/Primitives.lean:3686–4399`.

    The sizes materially increase review and maintenance cost, but the inspected phase invariants remain explicit, and E2 clients can consume the proved public contracts without depending on private layout. There is no proof reason to block those clients on a file split. Agree with a separate, serial, ride-along-audited refactor, preferably before substantial further controller growth.

    One implementation qualification to the maintainer position: cross-file use of today's private helpers is not solved by byte-identical relocation alone. Keep dependent private families together, or make any newly required cross-file interface an explicit, separately reviewed visibility change. Compare the ordered relocated declarations and preserved public contracts, then rerun the module-order sweep, target closures, whole-Build traversal, and kernel-export inventory. Do not claim that moving declarations between modules preserves generated private names or export visibility automatically. This qualification affects the future refactor, not the current proof gate.

Notation: `n` is native-input length; `s` is a candidate word and `l=|s|`; `T` is the relevant scalar runtime budget unless written as a function; `T₀,T₁,T₂,Tg` are supplied time functions; `L` is counter width; `R` is fuel value; `C,e` are polynomial parameters; `A` is the split-body coefficient. A *seam* is an exact configuration at a phase boundary. An *admission root* is a declaration directly referring to `sorryAx`, reached through the audited declaration's dependencies.
