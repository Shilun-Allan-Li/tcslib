**Chapter-1 infrastructure audit — round 2**

**Gate: OPEN — 0 blockers, 1 major, 3 minors.** The redesigned loop statements and P13/P14/C1 pass this statement-phase review. D5 does not yet close: the loop's public conclusion does not expose the configuration and per-round witnesses required by the attached, unchanged `enumMachine_contracts`. The previous false-statement counterexample is repaired.

Audited input: `ch1-infra-r2-bundle.md`, SHA-256 `9517118a3bdb1ccfdaca6e82df05f168c2b29b327e8cacc4d7fdd6d4141618c6`. The manifest is correct: 35 attachments after the pack. References use repository file-local lines. `Build/` abbreviates `TCSlib/Complexity/TuringMachine/Build/`; `NP.lean`, `EXP.lean`, and `TMSAT.lean` have prefix `TCSlib/Complexity/ClassNP/`. Evidence filenames have prefix `audits/evidence/ch1-infra/`; log filenames have prefix `audits/logs/`.

This is a mathematical/source audit with independent byte, patch, and log checks. No Lean executable or complete build tree is present, so it is **not a fresh kernel run or a fully formalized construction proof**. “Pass” means no false statement or unrealizable budget was found, with the construction obligations described below; the stubs remain stubs. The unchanged bridge proofs, model results, `loop_run`, and previously passed contracts were not re-audited.

1. **[MAJOR] D5's enumerator row supplies the final decider contract, not the configuration contract the named customer requires.**

   **References:** `audits/ch1-infra-r2-pack.md:73`; `machine-library-design.md:300–310`; `Build/Loop.lean:189–194`; `EXP.lean:735–764,773–787`.

   The enumerator instantiation gives a machine computing the correct singleton existential verdict in exponential-times-polynomial total time. This is the conclusion shape of `enumDecider`. The actual pending theorem named by D5 is `enumMachine_contracts`, which additionally requires, for the same machine and every input:

   - a configuration family `cfg` and polynomially bounded startup reaching `cfg 0`;
   - a halted `[false]` terminal configuration at index `2^width`;
   - a polynomially bounded accept-or-advance segment from **each** candidate configuration, using that candidate's verifier indicator.

   None of these witnesses or bounds occurs in `exists_loopTM`'s conclusion. They cannot be recovered merely by unpacking its existential machine. Supplying `hstart`/`hround` for the **body** does not expose corresponding facts about the existential **host**.

   The missing timing information is substantive. Take `V` to accept every word and choose `C = c = 1`, so the width is \(n+1\). A machine that first counts down \(2^{n+1}-1\) entries and then emits `[true]` satisfies the loop's final-answer contract for a suitable polynomial `T` and constant multiplier. But if this machine satisfied the customer's configuration contract, candidate zero already accepts, so startup and its first accepting segment would give
   \[
     \text{halting time on }x
       \le 2b\bigl(n+(n+1)+1\bigr)^e
       =2b(2n+2)^e.
   \]
   Its deliberate delay instead gives
   \[
     2^{n+1}-1\le \text{halting time on }x.
   \]
   For every fixed \(b,e\), these inequalities conflict for sufficiently large \(n\). Thus a witness permitted by the public final-answer contract need not have the required configuration contract. This does **not** refute either existence theorem; it refutes the claimed direct customer coverage by that interface.

   **Repair:** export the host's startup, configuration family, terminal rejection, and per-round bounds as a stronger loop contract, and derive the present final-answer theorem from it. Alternatively, explicitly arrange a shared host construction with a separate customer-facing configuration theorem. Bypassing `enumMachine_contracts` and reproving `enumDecider` directly is another design change, but it does not fill the unchanged pending theorem. Re-audit the chosen interface before marking the enumerator row covered.

2. **[MINOR] The corrected policy attestation still miscounts the full lint output.**

   **References:** `audits/ch1-infra-r2-pack.md:54–63,137–138`; `ch1-infra-r2-lint.log:1–6,42–44,58`.

   The attached output has **0 FAIL and 7 WARN across 38 files**, from two invocations: 6 WARN over 28 machine files and 1 WARN over 10 ClassNP files. “The one WARN is TMSAT” describes only the second invocation. The other warned files are `MathlibBridge`, `Oblivious`, `ObliviousCandidate`, `ObliviousSetup`, `Universal`, and `UniversalInterpreter`.

   **Repair:** report both invocations and their combined totals. The quoted Universal/TMSAT escalation records support those two named exceptions; they do not establish disposition of the other five warnings. This finding does not reopen those unchanged modules or establish that their existing exceptions are absent.

3. **[MINOR] The axiom attestation incorrectly says both Convention lemmas print the standard triple.**

   **References:** `audits/ch1-infra-r2-pack.md:34–39`; `ch1-infra-r2-axioms.log:28–29`.

   The actual prints are:

   | Declaration | Printed axioms |
   |---|---|
   | `Turing.initCfg_ofWords` | `[propext, Quot.sound]` |
   | `Turing.Cfg.ofWords_workTapes` | `[propext]` |

   Both are admission-free, as required. **Repair:** say “only axioms from the standard triple,” or give the exact subsets. The reported 25 `sorryAx` prints are correct.

4. **[MINOR] P10's introductory construction claim still names the Boolean loop.**

   **References:** `Build/Primitives.lean:293–305`.

   Lines 293–296 still claim realization as an `exists_loopTM` instance, whereas the repaired sketch correctly names `exists_loopFindTM` at line 301. The decision form returns `[any …]` and cannot directly return the selected encoded split.

   **Repair:** change the introductory reference to `exists_loopFindTM`. The corrected payload sketch itself passes; this is a stale, contradictory reference, not a new defect in `splitSolve`.

5. **[NOTE — vocabulary resolved] The split-search equality requires the coefficient shift \(C\mapsto C+1\).**

   **References:** `Build/Convention.lean:101–120`; `NP.lean:101–105,128–131,195–196,256–259`; `EXP.lean:103–106`.

   The correct equalities are
   \[
   \begin{aligned}
   \mathrm{splitAtLastTrue}(v)&=\mathrm{stripCertificate}(v),\\
   \mathrm{solveSplit}(C+1,c,m)&=\mathrm{certificateSplit}(C,c,m),\\
   \mathrm{incFixed}(s)&=\mathrm{enumInc}(s).
   \end{aligned}
   \]
   They are sufficient for the fills, but the middle equality is **false with the same coefficient on both sides**. For example,
   \[
     \mathrm{solveSplit}(0,0,0)=\mathrm{some}(0),\qquad
     \mathrm{certificateSplit}(0,0,0)=\mathrm{none}.
   \]
   The shifted equality follows by unfolding: the two `List.range.find?` expressions then have identical predicates. Consequently the padded-verifier row must use P10 at `(C + 1, c)`, while retaining P8 at `(C, c)` for the original witness bound.

   For stripping, if \(v\) has no true bit, both definitions return `none`. Otherwise it has a unique decomposition
   \[
       v=u\mathbin{++}[\mathrm{true}]
           \mathbin{++}\mathrm{replicate}(r,\mathrm{false})
   \]
   at its last true bit. The reverse/dropWhile definition returns `some u`, and `stripCertificate_spec` gives the same result. This includes an empty prefix, and `[]` belongs to the no-marker case. For increment, structural induction gives equality: both definitions have the same empty, false-head, and recursive true-head equations, including overflow at width zero.

   **Disposition:** approve semantic compatibility with the displayed coefficient translation; do not record unqualified same-parameter equality.

6. **[NOTE — remaining evidence limits] Most historical open items are now decidable; the bundle still does not establish every claimed scope/customer fact.**

   **References:** `audits/ch1-infra-r2-pack.md:23,46–50,74–75,81–82,140–147`; `backlog.md:192–216`.

   The supplied evidence resolves the following round-1 uncertainties:

   | Round-1 open item | Round-2 disposition |
   |---|---|
   | Universal export was append-only | **Verified from the supplied historical diff:** one final hunk, 67 added lines, zero deleted lines. No pre-existing declaration is edited by that diff. |
   | TMSAT relocation/statement byte identity, residual identity, public order | **Verified:** reverse application of the patch reproduces both Git blob IDs; both slice hashes match; the remaining text is identical after removing the moved/extended bridge region. It crosses only the five private lemmas, so public theorem order is preserved. |
   | Original loop and B→C repair | **Verified:** reversing the supplied B→C patch on the `d576814c` text gives the `a418f586` text exactly; both abbreviated Git blob IDs match. The supplied whole-Lean diff reports only `Loop.lean` changed. |
   | Run-A/B admission counts and order | **Verified from the attached logs:** see item 11. |
   | Traversal actually inspects opaque values and types | **Verified from the now-attached program:** see item 11. |
   | Lint output and named size exceptions | **Output verified, attestation corrected by item 2.** The two exception texts are now quoted; full originating decision-log rows are not attached. |
   | Whole-tree Build-import claim | **Supported by the supplied unfiltered grep:** 9 textual hits, comprising 7 import directives and 2 documentation references. The four facade imports are the only imports outside Build. |
   | Three vocabulary comparisons | **Resolved:** item 5. |
   | D4 promotion request existed | **Verified:** `batchC.md:139–148` explicitly requests both promotions. Their linear-time subsumption remains approved; their private HALT implementations are not attached for a source comparison. |
   | Full E3/E4 obligation coverage | **Still not established:** the backlog is an inheritance index, not the referenced briefs, six-stage/boundary tables, product-encoding specification, or serialization ledger. |
   | All Lean changes from run C to run D confined to three Build files | **Not fully established:** the referenced run-D diff is absent. Current TMSAT does independently match the post-export historical blob, but current Universal and a whole-tree C→D diff are not supplied. |
   | Fresh-olean execution/toolchain and mathlib pin | **Still execution attestations:** the transcripts do not independently demonstrate cache removal or reproduce the toolchain/pin. No fresh execution was possible here. |
   | 2B simulation-core/customer details | **Not independently checked:** the relevant Nondeterminism source and detailed branch contracts are not attached. The explicitly bespoke NDTM scope is a reasonable boundary, not a verified fill. |

   These limitations are not counterexamples. They prevent upgrading the stated claims to independently verified facts. The original run-C log is also not reattached; its counts are inherited from the verbatim round-1 findings, not newly recounted.

   A small historical arithmetic correction follows from the Universal diff: its final hunk covers old lines 2831–2834 and adds 67 lines, giving 2901. The immediate pre-export file therefore had **2834** lines, not the round-1 pack's “2831 → 2901.” The quoted earlier escalation at 2831 lines can still be genuine historical context.

7. **[PASS — revised loops] The zero-step and state-domain repairs survive re-attack; the stated budgets remain realizable.**

   **References:** `Build/Loop.lean:68–78,159–194,213–251`.

   Define only for this argument
   \[
       s_i=(\mathrm{stepF}\ x)^{[i]}(s_0(x)).
   \]
   By `hInv0` and induction using `hInvStep`, \(\mathrm{Inv}(x,s_i)\) holds for every \(i\). Starting at its seam:

   - a rejecting round cannot halt or emit anything: halting is absorbing and output is append-only, whereas its endpoint is live with empty output;
   - positive duration and the no-interior-anchor clause make its endpoint the first anchor return after at least one simulated action;
   - an accepting round halts with the specified output. If its witness time includes an already-halted tail, the actual halt occurs no later. Capture includes any halting-transition emission.

   A finite controller can therefore run the fuel machine and startup, allow the initial seam for free, then count subsequent anchor returns. It executes precisely rounds \(0,\ldots,R(n)\) unless an earlier round accepts. After the last rejection, the next counter debit underflows and produces `[false]` or `[]`. A one-step anchor self-loop is counted once per actual action; it does not recreate the zero-step loophole.

   The fuel output has width at most \(T(n)\). Input rewinds need only traverse the positions reached in at most \(T(n)\) steps; no unexplained \(n\)-term is needed when \(T\) is sublinear. Even a full-width counter operation per boundary costs a constant multiple of \(T(n)+1\). Fuel setup, body startup, at most \(R(n)+1\) rounds, and final dispatch/replay thus fit
   \[
       c\,(T(n)+1)(R(n)+2)
   \]
   for a fixed construction constant. The find-form payload also has length at most \(T(n)\), since it starts with empty output and emits at most one bit per step. Replay fits the same bound. This argument already suffices without amortization; the stated amortized decrement strategy is valid as well.

   The host must use distinct controller phases for counter handling, startup, active body execution, and capture return. In particular, it must execute one body transition after releasing a seam before recognizing another return. These are finite control choices, not additional theorem hypotheses.

   Further edge dispositions:

   | Attack | Result |
   |---|---|
   | `R = 0`, empty fuel word | Exactly the initial orbit point is tested before underflow. |
   | `Inv := True` | Restores a stronger premise; does not refute the implication. |
   | Empty successful payload | Halt detection distinguishes success internally; the output function deliberately identifies its result with exhaustion. |
   | `body.k = 0` | State words are unrepresented; determinism plus `hround` forces compatible behavior on admissible words sharing that seam. No contradiction follows. |
   | `q₀ = anchor` | Startup may be zero. If `body.k > 0`, a nonempty initial state word prevents it; with zero tapes, nonempty words are invisible. Thus the pack's unconditional “unsatisfiable” claim needs this qualification. |
   | “Noncomputable `acceptF`” | Its values outside `Inv` may be arbitrary and noncomputable. Only behavior on admissible states is constrained by the executable first-return/halt experiment. The pack's blanket unsatisfiability claim is too broad. |

   The last two qualifications correct the attack commentary, not the loop statements. No new false-statement counterexample was found. The concrete Lean host and its simulation invariants remain fill work.

8. **[PASS, with item 1's customer qualification] Both §9b invariants and orbit descriptions are consistent; P10 and P5's substantive sketch repairs work.**

   **References:** `machine-library-design.md:297–314`; `Build/Primitives.lean:90–127,301–325`; `EXP.lean:103–164,750–777`.

   For the enumerator, successful `incFixed` preserves length, and overflow returns the original word under `getD s`. Hence
   \[
     |s|=m(n)\Longrightarrow
     |(\mathrm{incFixed}(s)).\mathrm{getD}(s)|=m(n).
   \]
   This covers the all-true word and width zero. Starting with all false bits, the little-endian value rises by one at each nonoverflow step; the \(2^{m(n)}\) points with indices \(0,\ldots,2^{m(n)}-1\) are precisely the width-\(m(n)\) words. At width zero there is one candidate, `[]`, checked with zero fuel.

   Its fuel is exactly `replicate (m n) true`, including the empty case. Startup, candidate assembly, verifier simulation, carry, and scratch restoration have a common polynomial bound in \(n+m(n)+1\). For example, choose a sufficiently large coefficient and degree at least the verifier degree, the P5 startup degree, and one. Use a distinct startup control state and a nonzero-time overflow stall. This makes the stated hypotheses realizable, subject to constructing the body. The resulting **output** is correct; the missing host-configuration interface is item 1.

   For P10, let \(\ell=|s|\le n+1\). Then
   \[
     |\mathrm{stepF}(x,s)|=
       \begin{cases}\ell+1,&\ell\le n,\\ \ell,&\ell>n,\end{cases}
       \quad\le n+1.
   \]
   Thus `hInvStep` really holds at the extra state of length \(n+1\). At that length acceptance is impossible because
   \[
       n+1+C(n+2)^e>n.
   \]
   A positive-time silent stall is available. Importantly, `Inv` admits **arbitrary bit patterns**, not just unary words: a conforming body must use their length and preserve their existing bits when appending or stalling. Alternatively, a fill may strengthen the invariant to all-true words and prove that version explicitly.

   On the actual orbit, \(s_i=\mathrm{replicate}(i,\mathrm{true})\) for \(0\le i\le n\). The acceptance predicate and payload therefore give exactly `solveSplit` and the required encoded split. Fuel is supplied by P4. The map \(i\mapsto i+C(i+1)^e\) is strictly increasing, since for \(i<j\),
   \[
       i+C(i+1)^e\le i+C(j+1)^e<j+C(j+1)^e.
   \]
   This includes \(C=0\) and \(e=0\). At \(n=0\), success occurs precisely when \(C=0\), with payload `pairEncode [] [] = [false,true]`.

   A length-based body can use a common bound \(T(n)=A(n+1)^{e+1}\): the invariant gives \(\ell+1\le n+2\le2(n+1)\), so candidate evaluation, restoration, and an output of length at most \(2n+2\) fit after increasing \(A\). The loop then gives
   \[
   \begin{aligned}
     c\bigl(A(n+1)^{e+1}+1\bigr)(n+2)
       &\le 2c(A+1)(n+1)^{e+2},
   \end{aligned}
   \]
   exactly P10's allowed exponent. The tables are not completed Lean instances—they omit concrete machines and proof terms—but their semantic and budget requirements are consistent.

   P5's revised harvest indexing is correct: for \(e>0\), \((e-1)+1=e\); for \(e=0\), a fixed emission chain returns exactly \(C\) trues. Binary-length composition preserves the stated polynomial time allowance. The countdown repair also correctly handles the initially free seam.

9. **[PASS — P13/P14/C1] The new plumbing contracts are true at their stated budgets, including malformed and empty cases.**

   **References:** `Build/Primitives.lean:190–246`; `TuringMachine/Encoding.lean:113–125`.

   P13 buffers the decoded first component until an aligned separator establishes validity, then emits it and the untouched suffix. P14 emits a doubled input, separator, and a second input pass. Their output lengths on valid inputs are respectively
   \[
     |a|+|b|\le |\mathrm{pairEncode}(a,b)|,\qquad 3|x|+2,
   \]
   so constant multiples of \(n+1\) cover emission and a fixed number of scans. P13 emits nothing on malformed input, including a long doubled prefix lacking its separator.

   For C1, if \(z=\mathrm{pairEncode}(a,b)\), then
   \[
   \begin{aligned}
     |z|&=2|a|+2+|b|,\\
     |g(b)|&\le T_g(|b|)\le T_g(|z|),\\
     |\mathrm{pairEncode}(a,g(b))|
       &\le |z|+T_g(|z|).
   \end{aligned}
   \]
   Parsing, retaining \(a\), relocating/capturing the total machine on \(b\), and replay fit a constant multiple of \(|z|+1+T_g(|z|)\). The second inequality is precisely where monotonicity is used. Blank payloads and blank transformed outputs cause no difficulty. Parsing failure is decided before any physical output, so the malformed `[]` clause is compatible with append-only output.

10. **[D5 — partial approval] Dynamic assembly is repaired; the full disposition remains open for item 1 and the evidence limits in item 6.**

    P13 closes D-WRAP's concrete concatenation gap when guarded by `pairValid`/W3. C1's premise does require an already computed payload function, but P13/P14/C1 and the extractors together can build the paired unary generator for D-EMIT. There is no remaining general-pairing obstruction of the round-1 kind.

    Here is an explicit derivation, to avoid treating that generator as free glue. Given polynomial-time functions \(f,g\), first construct
    \[
      H(x)=\mathrm{pairEncode}(f(x),[]).
    \]
    This uses \(f\), P14, and C1 with the constant-empty function. Next construct
    \[
    \begin{aligned}
      s(x)&=\mathrm{pairEncode}(x,H(x)),\\
      t(x)&=\mathrm{pairEncode}(s(x),g(x)).
    \end{aligned}
    \]
    The first line uses P14 then C1 with \(H\). The second uses P14 on \(s(x)\), then C1 with \(g\circ\mathrm{pairFst}\). Finally,
    \[
    \begin{aligned}
      \mathrm{pairSnd}(\mathrm{pairConcat}(t(x)))
        &=\mathrm{pairSnd}(s(x)\mathbin{++}g(x))\\
        &=H(x)\mathbin{++}g(x)\\
        &=\mathrm{pairEncode}(f(x),g(x)).
    \end{aligned}
    \]
    Every intermediate pair is valid. Monotone polynomial envelopes and the timed composition theorem preserve polynomial time. Applying this to the two **exact** P5 unary outputs, then retaining \(x\) and adding the fixed outer code, supplies the D-EMIT layout, including zero certificate coefficient and degree.

    The other concrete mapping qualifications are:

    | Customer | Disposition |
    |---|---|
    | 2A `enumMachine_contracts` | **Not covered by the exported conclusion:** item 1. |
    | P10 / split search | **Covered** by the find loop at the level checked in item 8. |
    | 2C `pairedVerifier` | Exact width is required, not merely P8's one-sided inequality. It can be built from the available pieces: form the unary polynomial value, compare the two lengths in both directions, and conjoin. For arbitrary \(u,v\), P8 at \((1,1)\) on `pairEncode u (false :: v)` tests \(|v|\le|u|\); apply the derived pairing construction to supply both orientations. |
    | 2C `paddedVerifier` | Use P10 at \((C+1,c)\), strip, and P8 at \((C,c)\); guard failures before consulting the old verifier. This preserves the original-bound recheck. |
    | D-WRAP | **Covered** by guarded P13 and verifier composition. |
    | D-EMIT | **Covered** by the explicit construction above and the fixed outer encoder. |
    | D-MEM | Dynamic request assembly is now supported by the derived pairing construction. P10 at \((1,1)\) also supplies the required odd split. The row is not a completed verifier recipe: it still must identify the timed extraction of `w.take n` from the parsed unary \(n\), unary-shape checks, and the complete-answer test. These are remaining parser/body fill obligations, not consequences of applying C1 to `w` alone. |
    | 2B, E3, E4 | Component roles are plausible; complete customer-contract approval exceeds the attached interface evidence (item 6). W1 alone does not certify the unprovided six-stage/boundary/ledger tables. |
    | Clearing | Accept the explicit decision to keep it internal. A rejected body round still owes an actual scratch-restoration proof; the policy sentence is not such a proof. |

    In particular, a C1 call on `pairEncode a b` cannot make its new payload depend on \(a\): it computes \(g(b)\). Cross-component operations must be supplied as functions of a retained whole request and then assembled, as in the derivation above. This prevents accidentally declaring D-MEM's variable prefix extraction finished just because the request is retained.

11. **[Evidence verification] The substantive byte, sweep, and dependency claims pass within the stated source boundary.**

    Recounted sweep results:

    | Run | Ordered module headers | Errors | Build admission warnings | Other admission warnings | Total |
    |---|---:|---:|---:|---:|---:|
    | A | 57/57, exact order | 0 | 18 | 29 | 47 |
    | B | 57/57, exact order | 0 | 18 | 28 | 46 |
    | D | 57/57, exact order | 0 | 22 | 28 | 50 |

    Each attached sweep has unique headers numbered 1–57 and ends in `SWEEP_PASS modules=57`. Run D's Build distribution is exactly 4 wrapper, 3 loop, 15 primitive warnings. Run B and D's non-Build admission-warning lines are identical. These are declaration-warning counts, not counts of individual `sorry` expressions.

    Reversing `diff-tmsat-e8dd3e57.patch` on the attached current TMSAT file gives:

    | Check | Recomputed result |
    |---|---|
    | Old full-file Git blob | `b513ff433c52d25c6f1dd9126f3cc48869c3dc42` |
    | New full-file Git blob | `8492aea5a04daf1e6f79debd2b110392c90b66fa` |
    | Five-lemma slice, both versions | 4,022 characters; 4,085 UTF-8 bytes |
    | Five-lemma SHA-256, both versions | `13f1d70ebb2a5d1818c524dd6b05e06fed7f98675f948fd0c55eeb80f1267987` |
    | Bridge statement, both versions | 625 characters; 651 UTF-8 bytes |
    | Statement SHA-256, both versions | `6284da9ec00cb364a445d3d4b0383f8774591ad0357c8511df0923f30bc4bd0a` |

    The old bridge docstring prose is an exact prefix of the extended prose. The current TMSAT blob matches the historical patch's new blob, so its present identity is established without re-auditing its proofs. The historical loop snapshots likewise match the patch's blob prefixes `259f4309` and `ea6deada`.

    The axiom transcript contains 39 print lines, exactly 25 containing `sorryAx`, and eight root reports. `audits/programs/ch1-infra-BridgeExportAxioms.lean:33–48` traverses each checked declaration's type and value with `allowOpaque := true`, records direct `sorryAx` users, follows dependencies, and visits inductive constructors. Lines 61–84 compare the resulting roots against explicit expectations and reject unexpected axioms. The transcript matches those expectations.

    This traversal certifies **declaration roots**, not individual syntax sites: the two D-WRAP/D-EMIT admissions share the root `TMSAT_NPHard`. The attached source independently locates D-MEM at `TMSAT.lean:964` and D-WRAP/D-EMIT at `1152/1190`. Thus the combined source/program/log evidence supports the claimed site interpretation; the root list alone would not distinguish two admissions from one.

12. **Round-1 finding dispositions.**

    | Round-1 finding | Round-2 verdict |
    |---|---|
    | 1 — zero-step blocker | **Discharged.** Positive round duration repairs the refutation; item 7. |
    | 2 — unconstrained state-word domain | **Discharged as a statement/domain defect.** Both invariants are step-closed and permit bounded bodies; item 8. The separately exposed customer-output mismatch is item 1. |
    | 3 — D5, dynamic assembly/result-bearing search | **Partially discharged.** The two specific missing operations are now available; blanket D5 approval still fails at the actual enumerator contract, with further evidence limits recorded. |
    | 4 — initial countdown off by one | **Discharged.** Initial seam is free, including zero fuel. |
    | 5 — P5 wrong harvest degree | **Discharged.** Positive-degree indexing and degree-zero emission are corrected. |
    | 6 — characters labeled as bytes | **Discharged.** Both corrected counts and hashes independently match. |
    | 7 — import-leaf wording | **Discharged.** The external-boundary wording is supported by the supplied grep. |
    | 8 — historical/customer evidence absent | **Mostly resolved; residual limits itemized in item 6.** They are not silently promoted to verified claims. |

    D4's semantic/time-bound subsumption remains approved and its promotion-request provenance is now supplied. The unchanged bridge/export proof verdict is carried forward. Closing this gate requires repairing item 1; items 2–4 should also be corrected in the next resolution record.

**Notation glossary.** \(n=|x|\) is input length; \(|s|\) is list length; \(++\) is list concatenation; \(\mathrm{replicate}(r,b)\) is \(r\) copies of bit \(b\); \(s_i\) is the iterated state word defined in item 7; \(\ell=|s|\); \(m(n)=C(n+1)^c\) is the enumerator width. \(A\) is a sufficiently large fixed body-time coefficient; \(b,e\) in item 1 are the customer's hypothetical polynomial-bound witnesses. \(f,g\) are the two component functions in item 10, and \(H,s,t\) are its explicitly defined intermediate functions (distinct from the loop's state word). Other symbols and declaration names are those of the attached contracts.

