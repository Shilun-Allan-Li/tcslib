# External audit pack — Chapter 2, epoch-3/4 fill gate, round 2

Round-2 review of the repairs to the two majors and one minor from
`audits/ch2-epoch34-findings.md` (attached verbatim). The round-1 pack
and bundle are immutable and unchanged; this supplement is additive.
Scope of this round: findings 1–3 and any challenge to the new
evidence; the round-1 notes confirmed the mathematics and need no
re-review. Gate closes on zero blockers/majors across both rounds'
open items. Record findings in `audits/ch2-epoch34-r2-findings.md`.

Summary of repairs (full detail in the attached resolutions):

1. **Finding 1 (major)** — `audits/programs/ch2-epoch34-R2Axioms.lean`
   (attached, with its run log and the fresh 65/65 sweep log): all 21
   targets explicit with roots and permitted axioms; a memoized
   transitive axiom-closure walk over every checked declaration of the
   six owned modules AND the whole TCSlib import closure (11,510
   declarations) — the probe class (`private axiom … : False`) now
   fails the run; missing checked declarations panic; per-module kernel
   surface against source-derived public lists (cross-validated by
   lint); all 65 order modules asserted imported. Two self-caught
   disclosures are recorded in the resolutions: the prior programs'
   three-umbrella import gap, and 11 itemized generated kernel
   artifacts in the owned modules (eight imported-definition equation
   lemmas + the derived instance trio of a private structure).
2. **Finding 2 (major)** — the merge evidence supplement:
   `merge2-owned-diffs.md` (both owned-file first-parent diffs with
   blob identities, plus merge #1's Tautology diff closing note 12's
   caveat); the cited `colleague-merge2-sweep.log`; the substituted
   shared sources `PolyTimePairing.lean` and `Composition.lean` in
   full; and `final-source-manifest.md` — repository commit, source
   SHA-256 and fresh-olean SHA-256 for all 65 modules of the round-2
   run.
3. **Finding 3 (minor)** — `ch2-epoch34-r2-lint.log`: the scoped lint
   over all six owned files, 0 FAIL, the five exceptions named,
   TMSAT's standing epoch-2 exception identified.
4. **Notes 4 and 13** — the mechanical 22+76 deletion itemization
   (resolutions §4) and `duplicate-run-record.md`: archive and patch
   SHA-256s for both runs and the mechanically re-verified binding of
   β's patch to the integrated tree.

Severity scheme as always; this round-2 pack is immutable once sent.

## Bundle manifest — 12 attachments after this pack

The resolutions; the round-1 findings (verbatim); the R2 program; its
run log; the fresh sweep log; the scoped lint log; the merge diffs; the
source/olean manifest; the duplicate-run record; the merge sweep log;
`PolyTimePairing.lean`; `Composition.lean`.

## ===== audits/ch2-epoch34-resolutions.md =====

# Chapter 2, epoch-3/4 fill gate — resolutions (round 1 → round 2)

Status: **round-2 repairs complete; re-review requested.** The round-1
report (`audits/ch2-epoch34-findings.md`, preserved verbatim) returned
0 blockers / 2 majors / 1 minor / 11 notes. Both majors concern the
maintainer's verification evidence, not the audited proofs; the notes
confirm every priority item at source level. Each finding is addressed
below; the round-2 bundle (`audits/ch2-epoch34-r2-bundle.md`) attaches
the new evidence. The round-1 pack and bundle are immutable and
unchanged.

## Finding 1 (major) — closure-program coverage and the axiom bound

Accepted in full, including the probe counterexample: the prior
programs' whole-module passes tested direct `sorryAx` mention only, and
their target arrays named 13 (4B) / 12 (A5) of the 21 targets.

**Repair**: a new program, `audits/programs/ch2-epoch34-R2Axioms.lean`,
run against a fresh 65/65 sweep of the final snapshot
(log attached). Its five passes implement the prescribed resolution:

1. **All 21 frozen targets explicitly**, each checked for empty
   admission roots *and* `collectAxioms` within
   `propext`/`Classical.choice`/`Quot.sound`.
2. **Every checked kernel declaration of the six owned modules** —
   generated and unconsumed declarations included — passed through a
   memoized **transitive axiom-closure walk** that fails the run if any
   closure contains *any* axiom outside the permitted triple. This
   subsumes `sorryAx` and catches the auditor's `private axiom … :
   False` probe class: an `axiomInfo` constant outside the triple
   anywhere in any closure is a hard error. A missing checked
   declaration panics (it cannot pass silently).
3. **Kernel public surface per owned module** against source-derived
   public lists (embedded in the program; extraction cross-validated
   against the independent lint INFO counts — 8/8/5/14/5/5 — and the
   six files contain no anonymous instances, so prefix descent is
   sound).
4. **The same transitive axiom bound over every `TCSlib` declaration**
   in the import closure — restoring the whole-campaign claim at the
   strength actually advertised.
5. **Explicit inclusion of all 65 order modules** in the import
   closure (the embedded list is generated from the committed order
   file with count assertions).

Two further facts from the strengthened run, disclosed rather than
hidden: (i) pass 5 initially **failed against the prior programs' own
three-umbrella import set** — `ClassP.ModelInvariance` and its branch
were never in those programs' closures, confirming the auditor's
coverage point from a second direction; the round-2 program imports all
six umbrellas, and pass 4's total rose from the round-1 figure of
11,436 to **11,510** checked declarations accordingly. (ii) Pass 3
surfaced **11 generated kernel artifacts** in the owned modules that
the batch-level checks never listed: eight auto-generated equation
lemmas for public definitions *imported* from `Nondeterministic.lean`,
`Build/Convention.lean`, and `CNFEncoding.lean` (definitional
restatements, no new claims), and the `deriving DecidableEq` instance
trio of the *private* `SatStreamState` in `SAT.lean`, non-private in
name by a known Lean quirk. They are itemized in the program as a fixed
`generatedExceptions` array and printed in the log; all eleven pass the
full axiom bound. Source hygiene fixes are queued to the routine-layer
retrofit rather than editing frozen audited sources mid-gate.

Identity of the run: the attached
`audits/evidence/ch2-epoch34/final-source-manifest.md` records the
repository commit, per-module source SHA-256 for all 65 modules, and
the per-module olean SHA-256 of the fresh verification tree the program
ran against. No target statement was altered.

## Finding 2 (major) — merge #2 owned-file preservation evidence

Accepted: the round-1 bundle cited but did not attach the merge sweep
log, and supplied neither the owned-file merge diffs nor the
substituted shared sources.

**Repair** (all attached in round 2):

- `audits/evidence/ch2-epoch34/merge2-owned-diffs.md` — the complete
  first-parent diffs of merge #2 on `SAT.lean` and `EXP.lean`, with git
  blob identities on both sides; the before side (`5dc0881a`) is the
  exact post-A5-integration state, and the after side is asserted
  byte-identical to the audited HEAD state. The same file now also
  carries **merge #1's first-parent diff on `Tautology.lean`** with its
  blob identities, closing note 12's historical caveat.
- `audits/logs/colleague-merge2-sweep.log` — the cited merge sweep,
  including the honest first-attempt failure at the old order's module
  53 and the post-extension resume.
- The substituted shared sources:
  `TCSlib/Complexity/ClassNP/PolyTimePairing.lean` (home of
  `polyTimeComputable_of_linear`/`_const`/`_ite`/`_and`) and
  `TCSlib/Complexity/TuringMachine/Composition.lean` (home of
  `FinTM.exists_comp_on_image`) — the complete definitions and proofs
  now inside the owned closures, for review at contract and
  implementation.
- The 65-module source/olean manifest (above) as the reproducible
  final build identity.

The corrected closure program (finding 1) covers the post-merge
dependency closures at the final snapshot, including the two new
`EXP.lean` publics.

## Finding 3 (minor) — lint coverage

**Repair**: `audits/logs/ch2-epoch34-r2-lint.log` (attached) — a scoped
final lint over both subtrees, listing all six owned files: 0 FAIL; the
five owned size exceptions named; Snapshot under target; `TMSAT.lean`'s
WARN identified as the standing epoch-2 exception outside this gate's
owned set.

## Finding 4 (note) — deletion-residual itemization and census

The aggregate framing in the span attestation §3 is corrected here (the
pack is immutable): the mechanical per-commit decomposition of the 98
fill deletions is **22 `sorry`-line deletions + 76 others** — the 22nd
`sorry` line is E3-A's relocated local-admission line (created by
`bf6a06f8` when it reduced target 1, deleted by `1c824071` at closure),
so "21 targets" and "22 sorry-line deletions" are both exact. Per
commit: `bf6a06f8` 1+1, `3be8aed4` 2+0, `42f99b0f` 0+5, `c606476d`
5+0, `22f110b9` 1+0, `96d5b017` 0+1, `07bbad98` 1+1, `1c824071` 5+35,
`24bd4cd9` 1+0, `e3abb0d2` 1+0, `06ce95fa` 4+33, `9e9494aa` 1+0
(sorry+other; A2/A3/A4 were pure insertions). The attestation's "34
sanctioned scaffolding" reads correctly as 35 non-sorry deletions of
which 34 are scaffolding and one a splice. The 59-commit census with
classifications is reproducible from the public branch history at the
recorded endpoints; the round-2 manifest pins those endpoints.

## Findings 5–12 (notes) — confirmations

No action beyond retention; all confirmed routes and invariants are
frozen as audited. Note 12's historical-bytes caveat is closed by the
merge #1 diff now attached (finding 2). The finding-10/11 request to
include the omitted padding and locality targets in explicit coverage
is satisfied by finding 1's pass 1.

## Finding 13 (note) — duplicate-dispatch execution record

**Repair**: `audits/evidence/ch2-epoch34/duplicate-run-record.md`
(attached) — the checksum layer requested: all three archive SHA-256s
(α ≡ α-duplicate; β distinct), both runs' patch SHA-256s, and a
**mechanically re-verified binding**: β's patch, `git am`-replayed in an
isolated worktree at the integration parent, reproduces the integrated
commit's tree hash exactly. α was never applied; no blob of α's archive
exists in the repository.

## Finding 14 (note) — dispositions

The three approvals are recorded with their conditions. The
live/dead guidance is adopted verbatim into the E5-dedup backlog item:
`clFillTM`/`clFill_run`/`clNative_fill` are **live** (on the producer
path); `clCertificateCall` and `clTrack_schedule` are dead at source
level; the `e3c*` stratum is mixed (`e3c_bits_injective` live); SAT's
maximum-pass prefix is live. Dedup will proceed from a kernel-derived
inventory, never by prefix or checkpoint label. The 65-module surface's
certification conditions are discharged by findings 1–2 above.

---

Round-2 review scope: findings 1–3 (the repairs), plus any challenge to
the new evidence. The confirmed notes need no re-review. Gate closes on
zero blockers/majors across both rounds' open items.

## ===== audits/ch2-epoch34-findings.md =====

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

## ===== audits/programs/ch2-epoch34-R2Axioms.lean =====

import TCSlib.Complexity.TuringMachine
import TCSlib.Complexity.ClassP
import TCSlib.Complexity.ClassNP
import TCSlib.Complexity.CookLevin
import TCSlib.Complexity.Formulas
import TCSlib.Complexity.Uncomputability
import Lean
import Std.Data.HashMap

set_option maxHeartbeats 0

/- Round-2 closure program for the epoch-3/4 fill gate, per finding 1 of
`audits/ch2-epoch34-findings.md`:
 (1) all 21 frozen targets explicitly, roots AND permitted axioms;
 (2) every checked declaration of the six owned modules, rejecting missing
     entries, with the FULL permitted-axiom bound on each transitive
     closure (a bare non-permitted axiom -- sorryAx included -- anywhere in
     any closure fails the run; this strengthens the direct-sorryAx test
     the auditor's probe defeated);
 (3) kernel public surface of each owned module against its source-derived
     public list (no anonymous instances exist in these files);
 (4) the same full axiom bound over every TCSlib declaration in the import
     closure;
 (5) explicit inclusion of all 65 modules of the committed order. -/

open Lean Elab Command

namespace R2Audit

def allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

abbrev AxM := ReaderT Environment (StateM (Std.HashMap Name Bool))

/-- `true` iff every axiom in the transitive closure is permitted.
Panics on a missing checked declaration. -/
partial def clean (name : Name) : AxM Bool := do
  if let some r := (← get).get? name then return r
  modify fun m => m.insert name true
  let env ← read
  match env.checked.get.find? name with
  | none => panic! s!"Missing checked kernel declaration: {name}"
  | some ci =>
    let mut ok := true
    if let .axiomInfo _ := ci then
      unless allowed.contains name do ok := false
    let mut deps := ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque := true) then
      deps := deps ++ v.getUsedConstants
    if let .inductInfo i := ci then
      deps := deps ++ i.ctors.toArray
    for d in deps do
      unless (← clean d) do ok := false
    modify fun m => m.insert name ok
    return ok

structure WalkState where
  visited : NameSet := {}
  roots : Array Name := #[]

abbrev WalkM := ReaderT Environment (StateM WalkState)

partial def visit (name : Name) : WalkM Unit := do
  if (← get).visited.contains name then return
  modify fun s => { s with visited := s.visited.insert name }
  let env ← read
  match env.checked.get.find? name with
  | none => panic! s!"Missing checked kernel declaration: {name}"
  | some ci =>
    let mut deps := ci.type.getUsedConstants
    if let some value := ci.value? (allowOpaque := true) then
      deps := deps ++ value.getUsedConstants
    if deps.contains ``sorryAx then
      modify fun s => { s with roots := s.roots.push name }
    deps.forM visit
    match ci with
    | .inductInfo i => i.ctors.forM visit
    | _ => pure ()

def userRoots (env : Environment) (name : Name) : List Name :=
  ((((visit name).run env).run {}).2.roots.map privateToUserName).toList.eraseDups

def publicsNondeterminism : Array Name := #[`Complexity.EXP_eq_NEXP_of_P_eq_NP, `Complexity.NEXP_eq_iUnion_NTIME, `Complexity.NEXP_subset_iUnion_NTIME, `Complexity.NP_eq_iUnion_NTIME, `Complexity.NP_subset_iUnion_NTIME, `Complexity.P_ne_NP_of_EXP_ne_NEXP, `Complexity.ntime_expPow_subset_NEXP, `Complexity.ntime_poly_subset_NP]
def publicsEXP : Array Name := #[`Complexity.EXP, `Complexity.EXP_subset_NEXP, `Complexity.ExpBound, `Complexity.NEXP, `Complexity.NP_subset_EXP, `Complexity.P_subset_EXP, `Complexity.enumWord, `Complexity.exists_proj_decider]
def publicsSAT : Array Name := #[`Complexity.SAT, `Complexity.SAT3, `Complexity.SAT3_mem_NP, `Complexity.SAT_mem_NP, `Complexity.SAT_reducible_SAT3]
def publicsSnapshot : Array Name := #[`Complexity.Snapshot, `Complexity.emitted, `Complexity.inputBitAt, `Complexity.inputPosAt, `Complexity.oblivious_schedule_eq, `Complexity.prevVisit, `Complexity.snapshotAt, `Complexity.snapshotAt_inputSymbol, `Complexity.snapshotAt_state_succ, `Complexity.snapshotAt_workSymbol, `Complexity.snapshotAt_zero, `Complexity.stepState, `Complexity.workPosAt, `Complexity.writtenOrKept]
def publicsTautology : Array Name := #[`Complexity.TAUTOLOGY, `Complexity.TAUTOLOGY_coNPComplete, `Complexity.TAUTOLOGY_mem_coNP, `Complexity.coNPComplete, `Complexity.coNPHard]
def publicsHardness : Array Name := #[`Complexity.NPHard.polyTimeReducible, `Complexity.SAT3_NPComplete, `Complexity.SAT3_NPHard, `Complexity.SAT_NPComplete, `Complexity.SAT_NPHard]

def ownedModules : Array (Name × Array Name) := #[
  (`TCSlib.Complexity.ClassNP.Nondeterminism, publicsNondeterminism),
  (`TCSlib.Complexity.ClassNP.EXP, publicsEXP),
  (`TCSlib.Complexity.ClassNP.SAT, publicsSAT),
  (`TCSlib.Complexity.CookLevin.Snapshot, publicsSnapshot),
  (`TCSlib.Complexity.ClassNP.Tautology, publicsTautology),
  (`TCSlib.Complexity.CookLevin.Hardness, publicsHardness)]

def orderModules : Array Name := #[`TCSlib.Complexity.TuringMachine.Configuration, `TCSlib.Complexity.TuringMachine.Deterministic, `TCSlib.Complexity.TuringMachine.StateRenaming, `TCSlib.Complexity.TuringMachine.Finite, `TCSlib.Complexity.TuringMachine.Oracle, `TCSlib.Complexity.TuringMachine.Simulation, `TCSlib.Complexity.TuringMachine.Sweep, `TCSlib.Complexity.TuringMachine.Composition, `TCSlib.Complexity.TuringMachine.Build.Convention, `TCSlib.Complexity.TuringMachine.Build.Wrappers, `TCSlib.Complexity.TuringMachine.Build.Loop, `TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction, `TCSlib.Complexity.TuringMachine.Robustness.SingleTape, `TCSlib.Complexity.TuringMachine.Robustness.Bidirectional, `TCSlib.Complexity.ClassP.DTIME, `TCSlib.Complexity.TuringMachine.Encoding, `TCSlib.Complexity.ClassP.TimeConstructible, `TCSlib.Complexity.TuringMachine.Robustness.ObliviousSchedule, `TCSlib.Complexity.TuringMachine.Robustness.ObliviousCandidate, `TCSlib.Complexity.TuringMachine.Robustness.ObliviousSetup, `TCSlib.Complexity.TuringMachine.Robustness.ObliviousLedger, `TCSlib.Complexity.TuringMachine.Robustness.Oblivious, `TCSlib.Complexity.ClassP.P, `TCSlib.Complexity.ClassP.ModelInvariance, `TCSlib.Complexity.ClassP.Examples, `TCSlib.Complexity.TuringMachine.Build.Primitives, `TCSlib.Complexity.TuringMachine.CodeParser, `TCSlib.Complexity.TuringMachine.MathlibBridge, `TCSlib.Complexity.TuringMachine.UniversalStartup, `TCSlib.Complexity.TuringMachine.UniversalInterpreter, `TCSlib.Complexity.TuringMachine.UniversalBlock, `TCSlib.Complexity.TuringMachine.Universal, `TCSlib.Complexity.Uncomputability.Computable, `TCSlib.Complexity.Uncomputability.Diagonalization, `TCSlib.Complexity.Uncomputability.Halting, `TCSlib.Complexity.TuringMachine.Nondeterministic, `TCSlib.Complexity.Formulas.CNF, `TCSlib.Complexity.Formulas.CNFEncoding, `TCSlib.Complexity.Formulas.DNF, `TCSlib.Complexity.ClassNP.PolyTime, `TCSlib.Complexity.ClassNP.PolyTimePairing, `TCSlib.Complexity.ClassNP.NP, `TCSlib.Complexity.ClassNP.CoNP, `TCSlib.Complexity.ClassNP.EXP, `TCSlib.Complexity.ClassNP.Reductions, `TCSlib.Complexity.ClassNP.NTIME, `TCSlib.Complexity.ClassNP.Nondeterminism, `TCSlib.Complexity.ClassNP.SAT, `TCSlib.Complexity.ClassNP.TMSAT, `TCSlib.Complexity.CookLevin.Snapshot, `TCSlib.Complexity.CookLevin.Hardness, `TCSlib.Complexity.ClassNP.Tautology, `TCSlib.Complexity.TuringMachine.UnaryTape, `TCSlib.Complexity.TuringMachine.CounterProg, `TCSlib.Complexity.TuringMachine.CounterProgRun, `TCSlib.Complexity.TuringMachine, `TCSlib.Complexity.ClassP, `TCSlib.Complexity.Uncomputability, `TCSlib.Complexity.Formulas, `TCSlib.Complexity.CookLevin, `TCSlib.Complexity.ClassNP.Transducer, `TCSlib.Complexity.ClassNP.CounterProgPolyTime, `TCSlib.Complexity.ClassNP.PClosure, `TCSlib.Complexity.ClassNP.ExpPoly, `TCSlib.Complexity.ClassNP]

/-- Disclosed generated kernel artifacts in the owned modules, itemized for
the auditor (round-2 resolutions, finding 1): eight equation lemmas
auto-generated inside owned modules for PUBLIC definitions IMPORTED from
`TuringMachine/Nondeterministic.lean`, `Build/Convention.lean`, and
`Formulas/CNFEncoding.lean` (definitional restatements, no new claims, no
axioms), and the `deriving DecidableEq` instance of the PRIVATE structure
`SatStreamState` in `SAT.lean`, whose generated name is non-private by a
known Lean naming quirk. Source fixes are queued to the routine-layer
retrofit; the frozen audited sources are not edited mid-gate. -/
def generatedExceptions : Array Name := #[
  `Turing.NDTM.runWith.eq_def, `Turing.NDTM.runWith.eq_1, `Turing.NDTM.runWith.eq_2,
  `Turing.NDTM.stepWith.eq_1, `Turing.solveSplitWith.eq_1,
  `Std.Sat.CNF.WidthAtMost.eq_1, `Std.Sat.CNF.numVars.eq_1, `Std.Sat.CNF.fallback.eq_1,
  `Complexity.instDecidableEqSatStreamState,
  `Complexity.instDecidableEqSatStreamState.decEq,
  `Complexity.instDecidableEqSatStreamState.decEq.match_1]

def targets : Array Name := #[
  ``Complexity.ntime_expPow_subset_NEXP, ``Complexity.NEXP_eq_iUnion_NTIME,
  ``Complexity.NEXP_subset_iUnion_NTIME, ``Complexity.EXP_eq_NEXP_of_P_eq_NP,
  ``Complexity.P_ne_NP_of_EXP_ne_NEXP, ``Complexity.EXP_subset_NEXP,
  ``Complexity.SAT_mem_NP, ``Complexity.SAT3_mem_NP, ``Complexity.SAT_reducible_SAT3,
  ``Complexity.snapshotAt_zero, ``Complexity.snapshotAt_state_succ,
  ``Complexity.snapshotAt_inputSymbol, ``Complexity.snapshotAt_workSymbol,
  ``Complexity.oblivious_schedule_eq, ``Complexity.TAUTOLOGY_mem_coNP,
  ``Complexity.NPHard.polyTimeReducible, ``Complexity.SAT_NPHard,
  ``Complexity.SAT_NPComplete, ``Complexity.SAT3_NPHard,
  ``Complexity.SAT3_NPComplete, ``Complexity.TAUTOLOGY_coNPComplete]

run_cmd do
  let env ← getEnv
  -- Pass 5 first: module inclusion.
  let present : NameSet := env.header.moduleNames.foldl (fun s m => s.insert m) {}
  for m in orderModules do
    unless present.contains m do
      throwError "Order module not imported: {m}"
  logInfo m!"PASS 5: all {orderModules.size} order modules are in the import closure."
  -- Pass 1: the 21 targets, roots and axioms.
  for name in targets do
    let found := userRoots env name
    logInfo m!"TARGET {name}: roots {found}"
    unless found == [] do throwError "Admission roots remain for {name}: {found}"
    let ax ← collectAxioms name
    unless ax.all allowed.contains do throwError "Unexpected axiom for {name}: {ax}"
  logInfo m!"PASS 1: all {targets.size} frozen targets have empty roots and axioms within the permitted triple."
  -- Passes 2-4 share the memoized axiom walk.
  let mut cache : Std.HashMap Name Bool := {}
  let mut tcslibTotal := 0
  let mut tcslibBad : Array Name := #[]
  let mut moduleTotals : Array (Name × Nat) := #[]
  let mut surfaceBad : Array Name := #[]
  for (modName, pubs) in ownedModules do
    let mut cnt := 0
    for (name, _) in env.constants.toList do
      if env.getModuleIdxFor? name |>.any (fun i => env.header.moduleNames[i.toNat]! == modName) then
        cnt := cnt + 1
        let (ok, c) := ((clean name).run env).run cache
        cache := c
        unless ok do tcslibBad := tcslibBad.push name
        let isPriv := privateToUserName name != name
        let fromPublic := pubs.any (fun t => t == name || t.isPrefixOf name)
        unless isPriv || fromPublic || name.isInternal || generatedExceptions.contains name do
          surfaceBad := surfaceBad.push name
    moduleTotals := moduleTotals.push (modName, cnt)
  unless surfaceBad.isEmpty do
    throwError "Kernel surface beyond the source publics: {surfaceBad}"
  for (name, _) in env.constants.toList do
    match env.getModuleIdxFor? name with
    | none => pure ()
    | some idx =>
      if (`TCSlib).isPrefixOf (env.header.moduleNames[idx.toNat]!) then
        tcslibTotal := tcslibTotal + 1
        let (ok, c) := ((clean name).run env).run cache
        cache := c
        unless ok do tcslibBad := tcslibBad.push name
  unless tcslibBad.isEmpty do
    throwError "Declarations whose closures exceed the permitted axioms: {tcslibBad}"
  for (m, n) in moduleTotals do
    logInfo m!"PASS 2/3 {m}: {n} checked declarations, all closures within the permitted triple, kernel surface = the source publics."
  logInfo m!"PASS 3 EXCEPTIONS (disclosed, itemized): {generatedExceptions}"
  logInfo m!"PASS 4: {tcslibTotal} checked TCSlib declarations in the import closure; every transitive closure is within propext/Classical.choice/Quot.sound (sorryAx and any other axiom would fail this run)."
  logInfo "R2 CLOSURE AUDIT PASS: finding-1 resolutions discharged on the final snapshot."

end R2Audit

## ===== audits/logs/ch2-epoch34-r2-axioms.log =====

PASS 5: all 65 order modules are in the import closure.
TARGET Complexity.ntime_expPow_subset_NEXP: roots []
TARGET Complexity.NEXP_eq_iUnion_NTIME: roots []
TARGET Complexity.NEXP_subset_iUnion_NTIME: roots []
TARGET Complexity.EXP_eq_NEXP_of_P_eq_NP: roots []
TARGET Complexity.P_ne_NP_of_EXP_ne_NEXP: roots []
TARGET Complexity.EXP_subset_NEXP: roots []
TARGET Complexity.SAT_mem_NP: roots []
TARGET Complexity.SAT3_mem_NP: roots []
TARGET Complexity.SAT_reducible_SAT3: roots []
TARGET Complexity.snapshotAt_zero: roots []
TARGET Complexity.snapshotAt_state_succ: roots []
TARGET Complexity.snapshotAt_inputSymbol: roots []
TARGET Complexity.snapshotAt_workSymbol: roots []
TARGET Complexity.oblivious_schedule_eq: roots []
TARGET Complexity.TAUTOLOGY_mem_coNP: roots []
TARGET Complexity.NPHard.polyTimeReducible: roots []
TARGET Complexity.SAT_NPHard: roots []
TARGET Complexity.SAT_NPComplete: roots []
TARGET Complexity.SAT3_NPHard: roots []
TARGET Complexity.SAT3_NPComplete: roots []
TARGET Complexity.TAUTOLOGY_coNPComplete: roots []
PASS 1: all 21 frozen targets have empty roots and axioms within the permitted triple.
PASS 2/3 TCSlib.Complexity.ClassNP.Nondeterminism: 820 checked declarations, all closures within the permitted triple, kernel surface = the source publics.
PASS 2/3 TCSlib.Complexity.ClassNP.EXP: 490 checked declarations, all closures within the permitted triple, kernel surface = the source publics.
PASS 2/3 TCSlib.Complexity.ClassNP.SAT: 786 checked declarations, all closures within the permitted triple, kernel surface = the source publics.
PASS 2/3 TCSlib.Complexity.CookLevin.Snapshot: 41 checked declarations, all closures within the permitted triple, kernel surface = the source publics.
PASS 2/3 TCSlib.Complexity.ClassNP.Tautology: 439 checked declarations, all closures within the permitted triple, kernel surface = the source publics.
PASS 2/3 TCSlib.Complexity.CookLevin.Hardness: 1550 checked declarations, all closures within the permitted triple, kernel surface = the source publics.
PASS 3 EXCEPTIONS (disclosed, itemized): [Turing.NDTM.runWith.eq_def,
 Turing.NDTM.runWith.eq_1,
 Turing.NDTM.runWith.eq_2,
 Turing.NDTM.stepWith.eq_1,
 Turing.solveSplitWith.eq_1,
 Std.Sat.CNF.WidthAtMost.eq_1,
 Std.Sat.CNF.numVars.eq_1,
 Std.Sat.CNF.fallback.eq_1,
 Complexity.instDecidableEqSatStreamState,
 Complexity.instDecidableEqSatStreamState.decEq,
 Complexity.instDecidableEqSatStreamState.decEq.match_1]
PASS 4: 11510 checked TCSlib declarations in the import closure; every transitive closure is within propext/Classical.choice/Quot.sound (sorryAx and any other axiom would fail this run).
R2 CLOSURE AUDIT PASS: finding-1 resolutions discharged on the final snapshot.

## ===== audits/logs/ch2-epoch34-r2-sweep.log =====

HEAD 154ecb189633c08b3a76ce1d0aac74e16e335021
[1/65] TCSlib/Complexity/TuringMachine/Configuration
TCSlib/Complexity/TuringMachine/Configuration.lean:137:17: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Configuration.lean:140:61: warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
TCSlib/Complexity/TuringMachine/Configuration.lean:155:17: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
[2/65] TCSlib/Complexity/TuringMachine/Deterministic
[3/65] TCSlib/Complexity/TuringMachine/StateRenaming
[4/65] TCSlib/Complexity/TuringMachine/Finite
[5/65] TCSlib/Complexity/TuringMachine/Oracle
[6/65] TCSlib/Complexity/TuringMachine/Simulation
[7/65] TCSlib/Complexity/TuringMachine/Sweep
[8/65] TCSlib/Complexity/TuringMachine/Composition
[9/65] TCSlib/Complexity/TuringMachine/Build/Convention
[10/65] TCSlib/Complexity/TuringMachine/Build/Wrappers
[11/65] TCSlib/Complexity/TuringMachine/Build/Loop
TCSlib/Complexity/TuringMachine/Build/Loop.lean:2932:8: warning: This simp argument is unused:
  Fin.val_zero

Hint: Omit it from the simp argument list.
  simp only [emCallClearCfg, MultiTapeTM.step, emCallClearTM, Cfg.workTapeSymbols, F̵i̵n̵.̵v̵a̵l̵_̵z̵e̵r̵o̵,̵ ̵Fin.val_one,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲Nat.one_ne_zero, ↓reduceIte, hmark, reduceCtorEq, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:2932:22: warning: This simp argument is unused:
  Fin.val_one

Hint: Omit it from the simp argument list.
  simp only [emCallClearCfg, MultiTapeTM.step, emCallClearTM, Cfg.workTapeSymbols, Fin.val_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲F̵i̵n̵.̵v̵a̵l̵_̵o̵n̵e̵,̵ ̵Nat.one_ne_zero, ↓reduceIte, hmark, reduceCtorEq, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:2932:35: warning: This simp argument is unused:
  Nat.one_ne_zero

Hint: Omit it from the simp argument list.
  simp only [emCallClearCfg, MultiTapeTM.step, emCallClearTM, Cfg.workTapeSymbols, Fin.val_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲Fin.val_one, N̵a̵t̵.̵o̵n̵e̵_̵n̵e̵_̵z̵e̵r̵o̵,̵ ̵↓reduceIte, hmark, reduceCtorEq, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:2974:27: warning: This simp argument is unused:
  Fin.val_zero

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emCallClearCfg, emCallClearTM, Cfg.workTapeSymbols, F̵i̵n̵.̵v̵a̵l̵_̵z̵e̵r̵o̵,̵ ̵Fin.val_one,
  ̲  ̲ ̲ ̲ ̲ ̲Nat.one_ne_zero, ↓reduceIte, hmark, reduceCtorEq, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:2974:41: warning: This simp argument is unused:
  Fin.val_one

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emCallClearCfg, emCallClearTM,
  ̵  ̵ ̵ ̵ ̵ ̵Cfg.workTapeSymbols, Fin.val_zero,
  ̲ F̵i̵n̵.̵v̵a̵l̵_̵o̵n̵e̵,̵  ̲ ̲ ̲ ̲Nat.one_ne_zero, ↓reduceIte, hmark,
  ̵  ̵ ̵ ̵ ̵ ̵reduceCtorEq, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:2974:54: warning: This simp argument is unused:
  Nat.one_ne_zero

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emCallClearCfg, emCallClearTM, Cfg.workTapeSymbols, Fin.val_zero,
  ̲  ̲ ̲ ̲ ̲ ̲Fin.val_one, N̵a̵t̵.̵o̵n̵e̵_̵n̵e̵_̵z̵e̵r̵o̵,̵ ̵↓reduceIte, hmark, reduceCtorEq, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3021:8: warning: This simp argument is unused:
  Fin.val_zero

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emCallClearCfg, emCallClearTM, Cfg.workTapeSymbols, F̵i̵n̵.̵v̵a̵l̵_̵z̵e̵r̵o̵,̵ ̵Fin.val_one,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲Nat.one_ne_zero, ↓reduceIte, hblank, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3021:22: warning: This simp argument is unused:
  Fin.val_one

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emCallClearCfg, emCallClearTM, Cfg.workTapeSymbols, Fin.val_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲F̵i̵n̵.̵v̵a̵l̵_̵o̵n̵e̵,̵ ̵Nat.one_ne_zero, ↓reduceIte, hblank, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3021:35: warning: This simp argument is unused:
  Nat.one_ne_zero

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emCallClearCfg, emCallClearTM, Cfg.workTapeSymbols, Fin.val_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲Fin.val_one, N̵a̵t̵.̵o̵n̵e̵_̵n̵e̵_̵z̵e̵r̵o̵,̵ ̵↓reduceIte, hblank, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3053:6: warning: This simp argument is unused:
  Fin.val_zero

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emCallClearCfg, emCallClearTM, Cfg.workTapeSymbols, F̵i̵n̵.̵v̵a̵l̵_̵z̵e̵r̵o̵,̵ ̵Fin.val_one,
  ̲  ̲ ̲ ̲ ̲ ̲Nat.one_ne_zero, ↓reduceIte, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3053:20: warning: This simp argument is unused:
  Fin.val_one

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emCallClearCfg, emCallClearTM, Cfg.workTapeSymbols, Fin.val_zero,
  ̲  ̲ ̲ ̲ ̲ ̲F̵i̵n̵.̵v̵a̵l̵_̵o̵n̵e̵,̵ ̵Nat.one_ne_zero, ↓reduceIte, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3053:33: warning: This simp argument is unused:
  Nat.one_ne_zero

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emCallClearCfg, emCallClearTM, Cfg.workTapeSymbols, Fin.val_zero,
  ̲  ̲ ̲ ̲ ̲ ̲Fin.val_one, N̵a̵t̵.̵o̵n̵e̵_̵n̵e̵_̵z̵e̵r̵o̵,̵ ̵↓reduceIte, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3082:22: warning: This simp argument is unused:
  min_le_right

Hint: Omit it from the simp argument list.
  simp [emCallSpan, m̵i̵n̵_̵l̵e̵_̵r̵i̵g̵h̵t̵,̵ ̵le_max_right]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3082:36: warning: This simp argument is unused:
  le_max_right

Hint: Omit it from the simp argument list.
  simp [emCallSpan, min_le_right,̵ ̵l̵e̵_̵m̵a̵x̵_̵r̵i̵g̵h̵t̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3270:24: warning: This simp argument is unused:
  hspan

Hint: Omit it from the simp argument list.
  simp [emCallSpan, h̵s̵p̵a̵n̵,̵ ̵bufferTape, hn, List.getElem?_eq_none hlen]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3271:24: warning: This simp argument is unused:
  hspan

Hint: Omit it from the simp argument list.
  simp [emCallSpan, h̵s̵p̵a̵n̵,̵ ̵bufferTape, hn]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3579:27: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3579:27: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3832:19: warning: This simp argument is unused:
  show (1 : Fin 2) ≠ 0 by decide

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emCallFinishCfg, emCallFinishTM, Cfg.workTapeSymbols, Fin.isValue,
  ̲  ̲ ̲ ̲ ̲ ̲s̵h̵o̵w̵ ̵(̵1̵ ̵:̵ ̵F̵i̵n̵ ̵2̵)̵ ̵≠̵ ̵0̵ ̵b̵y̵ ̵d̵e̵c̵i̵d̵e̵,̵ ̵↓reduceIte, hblank]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3834:50: warning: This simp argument is unused:
  emCallFinishCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, e̵m̵C̵a̵l̵l̵F̵i̵n̵i̵s̵h̵C̵f̵g̵,̵ ̵sub_eq_add_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3849:21: warning: This simp argument is unused:
  show (1 : Fin 2) ≠ 0 by decide

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emCallFinishCfg, emCallFinishTM, Cfg.workTapeSymbols,
          Fin.isValue, s̵h̵o̵w̵ ̵(̵1̵ ̵:̵ ̵F̵i̵n̵ ̵2̵)̵ ̵≠̵ ̵0̵ ̵b̵y̵ ̵d̵e̵c̵i̵d̵e̵,̵ ̵↓reduceIte, hread]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3852:30: warning: This simp argument is unused:
  emCallFinishCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, emCallF̵i̵n̵i̵s̵h̵C̵f̵g̵,̵ ̵e̵m̵C̵a̵l̵l̵_erase_last]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3853:54: warning: This simp argument is unused:
  emCallFinishCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, e̵m̵C̵a̵l̵l̵F̵i̵n̵i̵s̵h̵C̵f̵g̵,̵ ̵sub_eq_add_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3881:50: warning: This simp argument is unused:
  emCallFinishCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, e̵m̵C̵a̵l̵l̵F̵i̵n̵i̵s̵h̵C̵f̵g̵,̵ ̵sub_eq_add_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3881:67: warning: This simp argument is unused:
  sub_eq_add_neg

Hint: Omit it from the simp argument list.
  simp [Action.apply, emCallFinishCfg,̵ ̵s̵u̵b̵_̵e̵q̵_̵a̵d̵d̵_̵n̵e̵g̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3892:52: warning: This simp argument is unused:
  emCallFinishCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, e̵m̵C̵a̵l̵l̵F̵i̵n̵i̵s̵h̵C̵f̵g̵,̵ ̵sub_eq_add_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3925:26: warning: This simp argument is unused:
  emCallFinishCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, e̵m̵C̵a̵l̵l̵F̵i̵n̵i̵s̵h̵C̵f̵g̵,̵ ̵sub_eq_add_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3941:30: warning: This simp argument is unused:
  emCallFinishCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, e̵m̵C̵a̵l̵l̵F̵i̵n̵i̵s̵h̵C̵f̵g̵,̵ ̵bufferTape_append]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3943:30: warning: This simp argument is unused:
  emCallFinishCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, e̵m̵C̵a̵l̵l̵F̵i̵n̵i̵s̵h̵C̵f̵g̵,̵ ̵sub_eq_add_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3943:47: warning: This simp argument is unused:
  sub_eq_add_neg

Hint: Omit it from the simp argument list.
  simp [Action.apply, emCallFinishCfg,̵ ̵s̵u̵b̵_̵e̵q̵_̵a̵d̵d̵_̵n̵e̵g̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3944:43: warning: This simp argument is unused:
  emCallFinishCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, e̵m̵C̵a̵l̵l̵F̵i̵n̵i̵s̵h̵C̵f̵g̵,̵ ̵sub_eq_add_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3944:60: warning: This simp argument is unused:
  sub_eq_add_neg

Hint: Omit it from the simp argument list.
  simp [Action.apply, emCallFinishCfg,̵ ̵s̵u̵b̵_̵e̵q̵_̵a̵d̵d̵_̵n̵e̵g̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3968:65: warning: This simp argument is unused:
  emCallFinishCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, e̵m̵C̵a̵l̵l̵F̵i̵n̵i̵s̵h̵C̵f̵g̵,̵ ̵sub_eq_add_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3968:82: warning: This simp argument is unused:
  sub_eq_add_neg

Hint: Omit it from the simp argument list.
  simp [Action.apply, emCallFinishCfg,̵ ̵s̵u̵b̵_̵e̵q̵_̵a̵d̵d̵_̵n̵e̵g̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3979:54: warning: This simp argument is unused:
  emCallFinishCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, emCallF̵i̵n̵i̵s̵h̵C̵f̵g̵,̵ ̵e̵m̵C̵a̵l̵l̵_erase_last]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3981:30: warning: This simp argument is unused:
  emCallFinishCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, e̵m̵C̵a̵l̵l̵F̵i̵n̵i̵s̵h̵C̵f̵g̵,̵ ̵sub_eq_add_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4040:21: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4040:33: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4077:2: warning: 'all_goals
  repeat
    first
    | rfl
    | omega
    | split' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4077:12: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4168:47: warning: This simp argument is unused:
  Fin.addCases_right

Hint: Omit it from the simp argument list.
  simp only [emCallSlots, Fin.addCases_left,̵ ̵F̵i̵n̵.̵a̵d̵d̵C̵a̵s̵e̵s̵_̵r̵i̵g̵h̵t̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4182:28: warning: This simp argument is unused:
  Fin.addCases_left

Hint: Omit it from the simp argument list.
  simp only [emCallSlots, Fin.addCases_l̵e̵f̵t̵,̵ ̵F̵i̵n̵.̵a̵d̵d̵C̵a̵s̵e̵s̵_̵right]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4189:67: warning: This simp argument is unused:
  emCallSlots

Hint: Omit it from the simp argument list.
  simp [emCallLayout, emCallPairIndex, tapeBlocks, e̵m̵C̵a̵l̵l̵S̵l̵o̵t̵s̵,̵
  ̵ ̵ ̵ ̵ ̵Fin.addCases, bufferedCompTM,
  ̲  ̲ ̲ ̲emCallIdleTM, emCallRightTM, emCallTrackTM]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4199:2: warning: 'all_goals
  repeat
    first
    | rfl
    | omega
    | split' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4200:2: warning: 'all_goals
  repeat
    first
    | rfl
    | omega
    | split' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4199:12: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4200:12: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4213:4: warning: 'all_goals
  repeat
    first
    | rfl
    | omega
    | split' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4214:4: warning: 'all_goals
  repeat
    first
    | rfl
    | omega
    | split' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4213:14: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4214:14: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4489:32: warning: This simp argument is unused:
  emCall_pair_inverse

Hint: Omit it from the simp argument list.
  simp [emCallCfg, e̵m̵C̵a̵l̵l̵_̵p̵a̵i̵r̵_̵i̵n̵v̵e̵r̵s̵e̵,̵ ̵emCallFinishCfg, Cfg.ofWords, stateWord, emCallPairIndex,
  ̲  ̲ ̲ ̲ ̲ ̲emCallPairSelect]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4491:32: warning: This simp argument is unused:
  emCall_pair_inverse

Hint: Omit it from the simp argument list.
  simp [emCallCfg, e̵m̵C̵a̵l̵l̵_̵p̵a̵i̵r̵_̵i̵n̵v̵e̵r̵s̵e̵,̵ ̵emCallFinishCfg, Cfg.ofWords, stateWord, emCallPairIndex,
  ̲  ̲ ̲ ̲ ̲ ̲emCallPairSelect, bufferedCompTM, emCallIdleTM, emCallRightTM, emCallTrackTM]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4622:37: warning: This simp argument is unused:
  hi

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, hs, hi̵,̵ ̵h̵w]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4622:41: warning: This simp argument is unused:
  hw

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, hs, hi,̵ ̵h̵w̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:5466:33: warning: This simp argument is unused:
  Function.comp_def

Hint: Omit it from the simp argument list.
  simp [List.append_assoc,̵ ̵F̵u̵n̵c̵t̵i̵o̵n̵.̵c̵o̵m̵p̵_̵d̵e̵f̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
[12/65] TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction
[13/65] TCSlib/Complexity/TuringMachine/Robustness/SingleTape
[14/65] TCSlib/Complexity/TuringMachine/Robustness/Bidirectional
[15/65] TCSlib/Complexity/ClassP/DTIME
[16/65] TCSlib/Complexity/TuringMachine/Encoding
[17/65] TCSlib/Complexity/ClassP/TimeConstructible
[18/65] TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule
[19/65] TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:473:6: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:501:37: warning: This simp argument is unused:
  hl

Hint: Omit it from the simp argument list.
  simp [inputTag, clippedMove, hl̵,̵ ̵h̵r]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:533:45: warning: This simp argument is unused:
  hw

Hint: Omit it from the simp argument list.
  simp [h̵w̵,̵ ̵Cfg.workTapeSymbols]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:535:49: warning: This simp argument is unused:
  hw

Hint: Omit it from the simp argument list.
  simp [hz, h̵w̵,̵ ̵Function.update_of_ne hn]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:535:53: warning: This simp argument is unused:
  Function.update_of_ne hn

Hint: Omit it from the simp argument list.
  simp [hz, hw,̵ ̵F̵u̵n̵c̵t̵i̵o̵n̵.̵u̵p̵d̵a̵t̵e̵_̵o̵f̵_̵n̵e̵ ̵h̵n̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:614:44: warning: This simp argument is unused:
  List.append_nil

Hint: Omit it from the simp argument list.
  simp only [payloadZone, List.reverse_cons, FinTM.sweepFold_append, he, ih, FinTM.sweepFold,
  ̲  ̲ ̲ ̲ ̲ ̲p̵a̵y̵l̵o̵a̵d̵B̵a̵c̵k̵w̵a̵r̵d̵_̵r̵o̵w̵,̵ ̵L̵i̵s̵t̵.̵a̵p̵p̵e̵n̵d̵_̵n̵i̵l̵]̵p̲a̲y̲l̲o̲a̲d̲B̲a̲c̲k̲w̲a̲r̲d̲_̲r̲o̲w̲]̲

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:764:27: warning: This simp argument is unused:
  act

Hint: Omit it from the simp argument list.
  simp only [a̵c̵t̵,̵ ̵Option.map_none]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:768:21: warning: This simp argument is unused:
  act

Hint: Omit it from the simp argument list.
  simp only [a̵c̵t̵,̵ ̵Option.map_some, Function.update_self]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:769:21: warning: This simp argument is unused:
  act

Hint: Omit it from the simp argument list.
  simp only [a̵c̵t̵,̵ ̵Option.map_some, Function.update_of_ne hz]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:774:29: warning: This simp argument is unused:
  act

Hint: Omit it from the simp argument list.
  simp only [a̵c̵t̵,̵ ̵Option.toList_none, List.append_nil]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:776:21: warning: This simp argument is unused:
  act

Hint: Omit it from the simp argument list.
  simp only [a̵c̵t̵,̵ ̵Option.toList_some, clockTape_append]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:784:65: warning: This simp argument is unused:
  ho

Hint: Omit it from the simp argument list.
  simp [act, List.length_append,̵ ̵h̵o̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:784:73: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:784:73: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:881:25: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
[20/65] TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:191:25: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:217:4: warning: This simp argument is unused:
  SignType.coe_neg_one

Hint: Omit it from the simp argument list.
  simp only [setupWrite, moveInputPos_zero, SignType.coe_zero, add_zero, S̵i̵g̵n̵T̵y̵p̵e̵.̵c̵o̵e̵_̵n̵e̵g̵_̵o̵n̵e̵,̵ ̵zero_add]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:249:56: warning: This simp argument is unused:
  SignType.coe_one

Hint: Omit it from the simp argument list.
  simp only [setupWrite, SignType.coe_zero, add_zero, S̵i̵g̵n̵T̵y̵p̵e̵.̵c̵o̵e̵_̵o̵n̵e̵,̵ ̵copyGuide_next]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:313:64: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:313:23: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:313:35: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:313:64: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:405:16: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:405:41: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:405:16: warning: 'simp [SignType.cast]' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:405:41: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:600:25: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:686:26: warning: This simp argument is unused:
  hg

Hint: Omit it from the simp argument list.
  simp_all ̵[̵h̵g̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:731:38: warning: This simp argument is unused:
  layoutPhase

Hint: Omit it from the simp argument list.
  simp [layoutP̵h̵a̵s̵e̵,̵ ̵l̵a̵y̵o̵u̵t̵Move, hi]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:747:36: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:747:48: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:756:32: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:778:15: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only [F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵,̵ ̵Nat.cast_add, Nat.cast_one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:778:27: warning: This simp argument is unused:
  Nat.cast_add

Hint: Omit it from the simp argument list.
  simp only [Fin.val_mk, Nat.cast_a̵d̵d̵,̵ ̵N̵a̵t̵.̵c̵a̵s̵t̵_̵one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:778:41: warning: This simp argument is unused:
  Nat.cast_one

Hint: Omit it from the simp argument list.
  simp only [Fin.val_mk, Nat.cast_add,̵ ̵N̵a̵t̵.̵c̵a̵s̵t̵_̵o̵n̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:879:17: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only [F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵,̵ ̵Nat.cast_add, Nat.cast_one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:879:29: warning: This simp argument is unused:
  Nat.cast_add

Hint: Omit it from the simp argument list.
  simp only [Fin.val_mk, Nat.cast_a̵d̵d̵,̵ ̵N̵a̵t̵.̵c̵a̵s̵t̵_̵one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:879:43: warning: This simp argument is unused:
  Nat.cast_one

Hint: Omit it from the simp argument list.
  simp only [Fin.val_mk, Nat.cast_add,̵ ̵N̵a̵t̵.̵c̵a̵s̵t̵_̵o̵n̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
[21/65] TCSlib/Complexity/TuringMachine/Robustness/ObliviousLedger
[22/65] TCSlib/Complexity/TuringMachine/Robustness/Oblivious
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:182:25: warning: This simp argument is unused:
  hc

Hint: Omit it from the simp argument list.
  simp only [hfirst,̵ ̵h̵c̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:240:19: warning: This simp argument is unused:
  hd

Hint: Omit it from the simp argument list.
  simp only [h̵d̵,̵ ̵SignType.cast, add_zero, ← sub_eq_add_neg, hleft', hc]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:379:26: warning: This simp argument is unused:
  hw

Hint: Omit it from the simp argument list.
  simp [setupWrite, h̵w̵,̵ ̵Function.update_of_ne hz, h, hz]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:379:30: warning: This simp argument is unused:
  Function.update_of_ne hz

Hint: Omit it from the simp argument list.
  simp [setupWrite, hw, F̵u̵n̵c̵t̵i̵o̵n̵.̵u̵p̵d̵a̵t̵e̵_̵o̵f̵_̵n̵e̵ ̵h̵z̵,̵ ̵h, hz]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:737:38: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:743:6: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:756:24: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:756:24: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:695:64: warning: This simp argument is unused:
  Fin.reduceFinMk

Hint: Omit it from the simp argument list.
  simp only [prepInvariant, Action.apply, Fin.addCases_right, Fin.r̵e̵d̵u̵c̵e̵F̵i̵n̵M̵k̵,̵ ̵F̵i̵n̵.̵val_one, Nat.one_ne_zero,
  ̲  ̲ ̲ ̲ ̲ ̲show (2 : ℕ) ≠ 0 by decide, ↓reduceIte,
  ̵  ̵ ̵ ̵ ̵ ̵SignType.coe_zero, add_zero]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:695:111: warning: This simp argument is unused:
  show (2 : ℕ) ≠ 0 by decide

Hint: Omit it from the simp argument list.
  simp only [prepInvariant, Action.apply, Fin.addCases_right, Fin.reduceFinMk, Fin.val_one,
  ̲  ̲ ̲ ̲ ̲ ̲Nat.one_ne_zero, s̵h̵o̵w̵ ̵(̵2̵ ̵:̵ ̵ℕ̵)̵ ̵≠̵ ̵0̵ ̵b̵y̵ ̵d̵e̵c̵i̵d̵e̵,̵ ̵↓reduceIte, SignType.coe_zero, add_zero]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:725:52: warning: This simp argument is unused:
  hi

Hint: Omit it from the simp argument list.
  simp only [obliviousSchedule, obliviousVisit, h̵i̵,̵ ̵setupWrite, Option.toList_none, List.append_nil]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:729:52: warning: This simp argument is unused:
  hi

Hint: Omit it from the simp argument list.
  simp only [obliviousSchedule, obliviousVisit, h̵i̵,̵ ̵setupWrite, Option.toList_none, List.append_nil]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
[23/65] TCSlib/Complexity/ClassP/P
[24/65] TCSlib/Complexity/ClassP/ModelInvariance
[25/65] TCSlib/Complexity/ClassP/Examples
[26/65] TCSlib/Complexity/TuringMachine/Build/Primitives
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2492:42: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2498:72: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2492:42: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2498:72: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2490:82: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2520:72: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2520:72: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2508:38: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2512:38: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2570:29: warning: This simp argument is unused:
  List.append_nil

Hint: Omit it from the simp argument list.
  simp only [↓reduceIte,̵ ̵L̵i̵s̵t̵.̵a̵p̵p̵e̵n̵d̵_̵n̵i̵l̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2533:42: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2538:42: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2541:42: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2580:46: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2604:43: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2927:25: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2927:25: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3026:59: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3174:34: warning: This simp argument is unused:
  splitRestoreScan

Hint: Omit it from the simp argument list.
  simp [Action.apply,̵ ̵s̵p̵l̵i̵t̵R̵e̵s̵t̵o̵r̵e̵S̵c̵a̵n̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3204:79: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3204:79: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3267:6: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3312:52: warning: This simp argument is unused:
  Nat.cast_one

Hint: Omit it from the simp argument list.
  simp only [List.length_nil, Nat.zero_add, N̵a̵t̵.̵c̵a̵s̵t̵_̵o̵n̵e̵,̵ ̵Fin.ext_iff, Fin.val_one] at h₁

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3312:66: warning: This simp argument is unused:
  Fin.ext_iff

Hint: Omit it from the simp argument list.
  simp only [List.length_nil, Nat.zero_add, Nat.cast_one, Fin.e̵x̵t̵_̵i̵f̵f̵,̵ ̵F̵i̵n̵.̵val_one] at h₁

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3312:79: warning: This simp argument is unused:
  Fin.val_one

Hint: Omit it from the simp argument list.
  simp only [List.length_nil, Nat.zero_add, Nat.cast_one, Fin.ext_iff,̵ ̵F̵i̵n̵.̵v̵a̵l̵_̵o̵n̵e̵] at h₁

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3352:20: warning: This simp argument is unused:
  MultiTapeTM.step

Hint: Omit it from the simp argument list.
  simp [M̵u̵l̵t̵i̵T̵a̵p̵e̵T̵M̵.̵s̵t̵e̵p̵,̵ ̵catalogPolyUnaryTM, Action.apply, catalogPolyCfg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3352:38: warning: This simp argument is unused:
  catalogPolyUnaryTM

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.step, c̵a̵t̵a̵l̵o̵g̵P̵o̵l̵y̵U̵n̵a̵r̵y̵T̵M̵,̵ ̵Action.apply, catalogPolyCfg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3352:72: warning: This simp argument is unused:
  catalogPolyCfg

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.step, catalogPolyUnaryTM, Action.apply,̵ ̵c̵a̵t̵a̵l̵o̵g̵P̵o̵l̵y̵C̵f̵g̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3353:10: warning: This simp argument is unused:
  MultiTapeTM.step

Hint: Omit it from the simp argument list.
  simp [M̵u̵l̵t̵i̵T̵a̵p̵e̵T̵M̵.̵s̵t̵e̵p̵,̵ ̵catalogPolyUnaryTM, Action.apply, catalogPolyCfg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3353:28: warning: This simp argument is unused:
  catalogPolyUnaryTM

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.step, c̵a̵t̵a̵l̵o̵g̵P̵o̵l̵y̵U̵n̵a̵r̵y̵T̵M̵,̵ ̵Action.apply, catalogPolyCfg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3353:62: warning: This simp argument is unused:
  catalogPolyCfg

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.step, catalogPolyUnaryTM, Action.apply,̵ ̵c̵a̵t̵a̵l̵o̵g̵P̵o̵l̵y̵C̵f̵g̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3400:23: warning: This simp argument is unused:
  Prod.mk.injEq

Hint: Omit it from the simp argument list.
  simp only [ht0, MultiTapeTM.runFrom_zero, splitRestoreScan, Cfg.ofWords,
      Option.some.injEq,̵ ̵P̵r̵o̵d̵.̵m̵k̵.̵i̵n̵j̵E̵q̵] at hstate

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:4917:8: warning: This simp argument is unused:
  Fin.val_zero

Hint: Omit it from the simp argument list.
  simp only [emitterClearCfg, MultiTapeTM.step, emitterClearTM, Cfg.workTapeSymbols,
          Fin.val_z̵e̵r̵o,̵ ̵F̵i̵n.̵v̵a̵l̵_̵o̵n̵e, Nat.one_ne_zero, ↓reduceIte, hmark, reduceCtorEq, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:4917:22: warning: This simp argument is unused:
  Fin.val_one

Hint: Omit it from the simp argument list.
  simp only [emitterClearCfg, MultiTapeTM.step, emitterClearTM, Cfg.workTapeSymbols,
          Fin.val_zero, F̵i̵n̵.̵v̵a̵l̵_̵o̵n̵e̵,̵ ̵Nat.one_ne_zero, ↓reduceIte, hmark, reduceCtorEq, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:4917:35: warning: This simp argument is unused:
  Nat.one_ne_zero

Hint: Omit it from the simp argument list.
  simp only [emitterClearCfg, MultiTapeTM.step, emitterClearTM, Cfg.workTapeSymbols,
          Fin.val_zero, Fin.val_one, N̵a̵t̵.̵o̵n̵e̵_̵n̵e̵_̵z̵e̵r̵o̵,̵ ̵↓reduceIte, hmark, reduceCtorEq, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:4959:27: warning: This simp argument is unused:
  Fin.val_zero

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emitterClearCfg, emitterClearTM, Cfg.workTapeSymbols, F̵i̵n̵.̵v̵a̵l̵_̵z̵e̵r̵o̵,̵ ̵Fin.val_one,
  ̲  ̲ ̲ ̲ ̲ ̲Nat.one_ne_zero, ↓reduceIte, hmark, reduceCtorEq, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:4959:41: warning: This simp argument is unused:
  Fin.val_one

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emitterClearCfg, emitterClearTM,
  ̵  ̵ ̵ ̵ ̵ ̵Cfg.workTapeSymbols, Fin.val_zero,
  ̲ F̵i̵n̵.̵v̵a̵l̵_̵o̵n̵e̵,̵  ̲ ̲ ̲ ̲Nat.one_ne_zero, ↓reduceIte, hmark,
  ̵  ̵ ̵ ̵ ̵ ̵reduceCtorEq, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:4959:54: warning: This simp argument is unused:
  Nat.one_ne_zero

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emitterClearCfg, emitterClearTM, Cfg.workTapeSymbols, Fin.val_zero,
  ̲  ̲ ̲ ̲ ̲ ̲Fin.val_one, N̵a̵t̵.̵o̵n̵e̵_̵n̵e̵_̵z̵e̵r̵o̵,̵ ̵↓reduceIte, hmark, reduceCtorEq, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5006:8: warning: This simp argument is unused:
  Fin.val_zero

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emitterClearCfg, emitterClearTM, Cfg.workTapeSymbols,
          Fin.val_z̵e̵r̵o,̵ ̵F̵i̵n.̵v̵a̵l̵_̵o̵n̵e, Nat.one_ne_zero, ↓reduceIte, hblank, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5006:22: warning: This simp argument is unused:
  Fin.val_one

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emitterClearCfg, emitterClearTM, Cfg.workTapeSymbols,
          Fin.val_zero, F̵i̵n̵.̵v̵a̵l̵_̵o̵n̵e̵,̵ ̵Nat.one_ne_zero, ↓reduceIte, hblank, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5006:35: warning: This simp argument is unused:
  Nat.one_ne_zero

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emitterClearCfg, emitterClearTM, Cfg.workTapeSymbols,
          Fin.val_zero, Fin.val_one, N̵a̵t̵.̵o̵n̵e̵_̵n̵e̵_̵z̵e̵r̵o̵,̵ ̵↓reduceIte, hblank, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5038:6: warning: This simp argument is unused:
  Fin.val_zero

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emitterClearCfg, emitterClearTM, Cfg.workTapeSymbols, F̵i̵n̵.̵v̵a̵l̵_̵z̵e̵r̵o̵,̵ ̵Fin.val_one,
  ̲  ̲ ̲ ̲ ̲ ̲Nat.one_ne_zero, ↓reduceIte, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5038:20: warning: This simp argument is unused:
  Fin.val_one

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emitterClearCfg, emitterClearTM, Cfg.workTapeSymbols, Fin.val_zero,
  ̲  ̲ ̲ ̲ ̲ ̲F̵i̵n̵.̵v̵a̵l̵_̵o̵n̵e̵,̵ ̵Nat.one_ne_zero, ↓reduceIte, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5038:33: warning: This simp argument is unused:
  Nat.one_ne_zero

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emitterClearCfg, emitterClearTM, Cfg.workTapeSymbols, Fin.val_zero,
  ̲  ̲ ̲ ̲ ̲ ̲Fin.val_one, N̵a̵t̵.̵o̵n̵e̵_̵n̵e̵_̵z̵e̵r̵o̵,̵ ̵↓reduceIte, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5067:23: warning: This simp argument is unused:
  min_le_right

Hint: Omit it from the simp argument list.
  simp [emitterSpan, m̵i̵n̵_̵l̵e̵_̵r̵i̵g̵h̵t̵,̵ ̵le_max_right]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5067:37: warning: This simp argument is unused:
  le_max_right

Hint: Omit it from the simp argument list.
  simp [emitterSpan, min_le_right,̵ ̵l̵e̵_̵m̵a̵x̵_̵r̵i̵g̵h̵t̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5255:25: warning: This simp argument is unused:
  hspan

Hint: Omit it from the simp argument list.
  simp [emitterSpan, h̵s̵p̵a̵n̵,̵ ̵bufferTape, hn, List.getElem?_eq_none hlen]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5256:25: warning: This simp argument is unused:
  hspan

Hint: Omit it from the simp argument list.
  simp [emitterSpan, h̵s̵p̵a̵n̵,̵ ̵bufferTape, hn]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5573:37: warning: This simp argument is unused:
  emitterBankCfg

Hint: Omit it from the simp argument list.
  simp [e̵m̵i̵t̵t̵e̵r̵B̵a̵n̵k̵C̵f̵g̵,̵ ̵MultiTapeTM.step, hs, controlAction, Action.apply]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5573:53: warning: This simp argument is unused:
  MultiTapeTM.step

Hint: Omit it from the simp argument list.
  simp [emitterBankCfg, M̵u̵l̵t̵i̵T̵a̵p̵e̵T̵M̵.̵s̵t̵e̵p̵,̵ ̵hs, controlAction, Action.apply]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5573:90: warning: This simp argument is unused:
  Action.apply

Hint: Omit it from the simp argument list.
  simp [emitterBankCfg, MultiTapeTM.step, hs, controlAction,̵ ̵A̵c̵t̵i̵o̵n̵.̵a̵p̵p̵l̵y̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5578:44: warning: This simp argument is unused:
  MultiTapeTM.step

Hint: Omit it from the simp argument list.
  simp [emitterBankCfg, emitterSlots, M̵u̵l̵t̵i̵T̵a̵p̵e̵T̵M̵.̵s̵t̵e̵p̵,̵ ̵hs, controlAction, Action.apply, -Fin.natAdd_eq_addNat]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5583:44: warning: This simp argument is unused:
  MultiTapeTM.step

Hint: Omit it from the simp argument list.
  simp [emitterBankCfg, emitterSlots, M̵u̵l̵t̵i̵T̵a̵p̵e̵T̵M̵.̵s̵t̵e̵p̵,̵ ̵hs, controlAction, Action.apply, -Fin.natAdd_eq_addNat]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5589:44: warning: This simp argument is unused:
  MultiTapeTM.step

Hint: Omit it from the simp argument list.
  simp [emitterBankCfg, emitterSlots, M̵u̵l̵t̵i̵T̵a̵p̵e̵T̵M̵.̵s̵t̵e̵p̵,̵ ̵hs, controlAction, Action.apply, -Fin.natAdd_eq_addNat]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5594:44: warning: This simp argument is unused:
  MultiTapeTM.step

Hint: Omit it from the simp argument list.
  simp [emitterBankCfg, emitterSlots, M̵u̵l̵t̵i̵T̵a̵p̵e̵T̵M̵.̵s̵t̵e̵p̵,̵ ̵hs, controlAction, Action.apply, -Fin.natAdd_eq_addNat]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5802:27: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5802:27: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:6228:52: warning: This simp argument is unused:
  emitterP2PrepareCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, e̵m̵i̵t̵t̵e̵r̵P̵2̵P̵r̵e̵p̵a̵r̵e̵C̵f̵g̵,̵ ̵hwrite]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:6229:52: warning: This simp argument is unused:
  emitterP2PrepareCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply,̵ ̵e̵m̵i̵t̵t̵e̵r̵P̵2̵P̵r̵e̵p̵a̵r̵e̵C̵f̵g̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:6264:37: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:6284:50: warning: This simp argument is unused:
  emitterP2PrepareCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply,̵ ̵e̵m̵i̵t̵t̵e̵r̵P̵2̵P̵r̵e̵p̵a̵r̵e̵C̵f̵g̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:6295:52: warning: This simp argument is unused:
  emitterP2PrepareCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, e̵m̵i̵t̵t̵e̵r̵P̵2̵P̵r̵e̵p̵a̵r̵e̵C̵f̵g̵,̵ ̵sub_eq_add_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:6314:50: warning: This simp argument is unused:
  emitterP2PrepareCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply,̵ ̵e̵m̵i̵t̵t̵e̵r̵P̵2̵P̵r̵e̵p̵a̵r̵e̵C̵f̵g̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:6325:52: warning: This simp argument is unused:
  emitterP2PrepareCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, e̵m̵i̵t̵t̵e̵r̵P̵2̵P̵r̵e̵p̵a̵r̵e̵C̵f̵g̵,̵ ̵sub_eq_add_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:6705:74: warning: This simp argument is unused:
  emitterP2RightIndex

Hint: Omit it from the simp argument list.
  simp [emitterP2LeftIndex,̵ ̵e̵m̵i̵t̵t̵e̵r̵P̵2̵R̵i̵g̵h̵t̵I̵n̵d̵e̵x̵] at hv

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:6719:54: warning: This simp argument is unused:
  emitterP2LeftIndex

Hint: Omit it from the simp argument list.
  simp [emitterP2L̵e̵f̵t̵I̵n̵d̵e̵x̵,̵ ̵e̵m̵i̵t̵t̵e̵r̵P̵2̵RightIndex] at hv

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:6726:56: warning: This simp argument is unused:
  emitterP2LeftIndex

Hint: Omit it from the simp argument list.
  simp [emitterP2L̵e̵f̵t̵I̵n̵d̵e̵x̵,̵ ̵e̵m̵i̵t̵t̵e̵r̵P̵2̵RightIndex] at hv

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:7455:6: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:7455:6: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:7458:6: warning: 'simp [MultiTapeTM.step, emitterTokenTM, Action.apply, scanCfg, List.append_assoc]' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:7458:6: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:7509:63: warning: This simp argument is unused:
  List.append_assoc

Hint: Omit it from the simp argument list.
  simp [emitterTokenTM, Action.apply, scanCfg, pairEncode, L̵i̵s̵t̵.̵a̵p̵p̵e̵n̵d̵_̵a̵s̵s̵o̵c̵,̵ ̵hlen]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
[27/65] TCSlib/Complexity/TuringMachine/CodeParser
TCSlib/Complexity/TuringMachine/CodeParser.lean:339:13: warning: This simp argument is unused:
  codeBitsNat_bits

Hint: Omit it from the simp argument list.
  simp only [c̵o̵d̵e̵B̵i̵t̵s̵N̵a̵t̵_̵b̵i̵t̵s̵,̵ ̵List.append_assoc, codeReadFin_append, bind, Option.bind,
  ̵  ̵ ̵ ̵codeReadTable_append,
  ̲  ̲ ̲ ̲List.all_replicate, id_eq, Bool.true_eq, or_true,
  ̵  ̵ ̵ ̵ite_self, ↓reduceIte, pure]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:339:70: warning: This simp argument is unused:
  bind

Hint: Omit it from the simp argument list.
  simp only [codeBitsNat_bits, List.append_assoc, codeReadFin_append, b̵i̵n̵d̵,̵ ̵Option.bind,
      codeReadTable_append, List.all_replicate, id_eq, Bool.true_eq, or_true,
  ̵  ̵ ̵ ̵ite_self, ↓reduceIte,
  ̲  ̲ ̲ ̲pure]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:339:76: warning: This simp argument is unused:
  Option.bind

Hint: Omit it from the simp argument list.
  simp only [codeBitsNat_bits, List.append_assoc, codeReadFin_append, bind, O̵p̵t̵i̵o̵n̵.̵b̵i̵n̵d̵,̵
  ̵ ̵ ̵ ̵ ̵codeReadTable_append,
  ̲  ̲ ̲ ̲List.all_replicate, id_eq, Bool.true_eq, or_true,
  ̵  ̵ ̵ ̵ite_self, ↓reduceIte, pure]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:340:53: warning: This simp argument is unused:
  Bool.true_eq

Hint: Omit it from the simp argument list.
  simp only [codeBitsNat_bits, List.append_assoc, codeReadFin_append, bind, Option.bind,
      codeReadTable_append, List.all_replicate, id_eq, B̵oo̵l̵.̵t̵ru̵e̵_e̵q̵,̵ ̵o̵r̵_̵true,
  ̵  ̵ ̵ ̵ite_self, ↓reduceIte, pure]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:340:67: warning: This simp argument is unused:
  or_true

Hint: Omit it from the simp argument list.
  simp only [codeBitsNat_bits, List.append_assoc, codeReadFin_append, bind, Option.bind,
      codeReadTable_append, List.all_replicate, id_eq, Bool.true_eq, o̵r̵_̵t̵r̵u̵e̵,̵
  ̵ ̵ ̵ ̵ ̵ite_self, ↓reduceIte, pure]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:420:43: warning: This simp argument is unused:
  h₁

Hint: Omit it from the simp argument list.
  simp [pairDecode, h₁̵,̵ ̵h̵₂, h₃] at h

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:420:47: warning: This simp argument is unused:
  h₂

Hint: Omit it from the simp argument list.
  simp [pairDecode, h₁, h₂̵,̵ ̵h̵₃] at h

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:420:51: warning: This simp argument is unused:
  h₃

Hint: Omit it from the simp argument list.
  simp [pairDecode, h₁, h₂,̵ ̵h̵₃̵] at h

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
[28/65] TCSlib/Complexity/TuringMachine/MathlibBridge
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:450:8: warning: This simp argument is unused:
  Function.update_self

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index, F̵u̵n̵c̵t̵i̵o̵n̵.̵u̵p̵d̵a̵t̵e̵_̵s̵e̵l̵f̵,̵ ̵hs]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:456:12: warning: This simp argument is unused:
  Action.apply_workTapes

Hint: Omit it from the simp argument list.
  simp [A̵c̵t̵i̵o̵n̵.̵a̵p̵p̵l̵y̵_̵w̵o̵r̵k̵T̵a̵p̵e̵s̵,̵ ̵bridgeOne, bridgeCfg, hi, hk]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:461:8: warning: This simp argument is unused:
  Function.update_self

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index, F̵u̵n̵c̵t̵i̵o̵n̵.̵u̵p̵d̵a̵t̵e̵_̵s̵e̵l̵f̵,̵ ̵hs,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲SignType.pos_eq_one, SignType.coe_one, List.length_cons, Nat.cast_add, Nat.cast_one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:486:8: warning: This simp argument is unused:
  Function.update_self

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index,
          F̵u̵n̵c̵t̵i̵o̵n̵.̵u̵p̵d̵a̵t̵e̵_̵s̵e̵l̵f̵,̵ ̵SignType.neg_eq_neg_one, SignType.coe_neg_one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:492:12: warning: This simp argument is unused:
  Action.apply_workTapes

Hint: Omit it from the simp argument list.
  simp [A̵c̵t̵i̵o̵n̵.̵a̵p̵p̵l̵y̵_̵w̵o̵r̵k̵T̵a̵p̵e̵s̵,̵ ̵bridgeOne, bridgeCfg, hi, hk]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:497:8: warning: This simp argument is unused:
  Function.update_self

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index,
          F̵u̵n̵c̵t̵i̵o̵n̵.̵u̵p̵d̵a̵t̵e̵_̵s̵e̵l̵f̵,̵ ̵SignType.neg_eq_neg_one, SignType.coe_neg_one, SignType.zero_eq_zero, SignType.coe_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲List.length_cons, Nat.cast_add, Nat.cast_one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:498:50: warning: This simp argument is unused:
  List.length_cons

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index,
          Function.update_self, SignType.neg_eq_neg_one, SignType.coe_neg_one, SignType.zero_eq_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲SignType.coe_zero, L̵i̵s̵t̵.̵l̵e̵n̵g̵t̵h̵_̵c̵o̵n̵s̵,̵ ̵Nat.cast_add, Nat.cast_one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:498:68: warning: This simp argument is unused:
  Nat.cast_add

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index,
          Function.update_self, SignType.neg_eq_neg_one, SignType.coe_neg_one, SignType.zero_eq_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲SignType.coe_zero, List.length_cons, N̵a̵t̵.̵c̵a̵s̵t̵_̵a̵d̵d̵,̵ ̵Nat.cast_one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:498:82: warning: This simp argument is unused:
  Nat.cast_one

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index,
          Function.update_self, SignType.neg_eq_neg_one, SignType.coe_neg_one, SignType.zero_eq_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲SignType.coe_zero, List.length_cons, N̵a̵t̵.̵c̵a̵s̵t̵_̵a̵d̵d̵,̵ ̵N̵a̵t̵.̵c̵a̵s̵t̵_̵o̵n̵e̵]̵N̲a̲t̲.̲c̲a̲s̲t̲_̲a̲d̲d̲]̲

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:721:32: warning: This simp argument is unused:
  Num.cast_zero

Hint: Omit it from the simp argument list.
  simp only [Num.to_of_nat,̵ ̵N̵u̵m̵.̵c̵a̵s̵t̵_̵z̵e̵r̵o̵] at hz

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:823:75: warning: This simp argument is unused:
  hk

Hint: Omit it from the simp argument list.
  simp [bridgeStore, PartrecToTM2.K'.elim, hi, hk̵,̵ ̵h̵] at *

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:871:15: warning: This simp argument is unused:
  Action.apply

Hint: Omit it from the simp argument list.
  simp only [̵A̵c̵t̵i̵o̵n̵.̵a̵p̵p̵l̵y̵,̵ ̵b̵r̵i̵d̵g̵e̵C̵f̵g̵,̵[̲b̲r̲i̲d̲g̲e̲C̲f̲g̲,̲ bridgeOne, SignType.zero_eq_zero, moveInputPos_zero]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:871:40: warning: This simp argument is unused:
  bridgeOne

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeCfg, b̵r̵i̵d̵g̵e̵O̵n̵e̵,̵ ̵SignType.zero_eq_zero, moveInputPos_zero]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:880:41: warning: This simp argument is unused:
  SignType.coe_zero

Hint: Omit it from the simp argument list.
  simp only [bridgeCfg, bridgeStore_at, ↓reduceIte, List.length_nil, Nat.cast_zero, neg_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲SignType.zero_eq_zero, S̵i̵g̵n̵T̵y̵p̵e̵.̵c̵o̵e̵_̵z̵e̵r̵o̵,̵ ̵SignType.neg_eq_neg_one, SignType.coe_neg_one, zero_add]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
[29/65] TCSlib/Complexity/TuringMachine/UniversalStartup
TCSlib/Complexity/TuringMachine/UniversalStartup.lean:160:54: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalStartup.lean:164:54: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalStartup.lean:190:52: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalStartup.lean:197:54: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalStartup.lean:215:52: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalStartup.lean:274:46: warning: This simp argument is unused:
  VirtualTag

Hint: Omit it from the simp argument list.
  simp_all ̵[̵V̵i̵r̵t̵u̵a̵l̵T̵a̵g̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
[30/65] TCSlib/Complexity/TuringMachine/UniversalInterpreter
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:330:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:353:6: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:378:83: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:439:60: warning: This simp argument is unused:
  zero_add

Hint: Omit it from the simp argument list.
  simp only [universalStateWindow, Nat.cast_zero, add_zero,̵ ̵z̵e̵r̵o̵_̵a̵d̵d̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:503:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:510:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:519:71: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:519:83: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:546:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:553:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:563:39: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:1020:75: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:1021:16: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:1021:28: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
[31/65] TCSlib/Complexity/TuringMachine/UniversalBlock
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:68:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:83:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:62:10: warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:79:64: warning: This simp argument is unused:
  universalSkipDone

Hint: Omit it from the simp argument list.
  simp [universalInterpreter, universalFour, hr, h, hz,̵ ̵u̵n̵i̵v̵e̵r̵s̵a̵l̵S̵k̵i̵p̵D̵o̵n̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:93:50: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:93:62: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:108:10: warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:164:53: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:164:65: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:185:50: warning: This simp argument is unused:
  Nat.add_zero

Hint: Omit it from the simp argument list.
  simp only [List.length_nil, List.flatMap_nil, Nat.a̵d̵d̵_̵zero,̵ ̵N̵a̵t̵.̵z̵e̵r̵o̵_add,
  ̵  ̵ ̵ ̵ ̵ ̵Nat.cast_zero, add_zero,
  ̲  ̲ ̲ ̲ ̲ ̲MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:244:40: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:271:40: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:289:6: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:289:61: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:289:73: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:289:6: warning: 'simp only [Fin.val_mk, Nat.cast_add, Nat.cast_one]' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:289:61: warning: 'congr 1' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:289:73: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:313:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:321:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:426:40: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:574:68: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
[32/65] TCSlib/Complexity/TuringMachine/Universal
TCSlib/Complexity/TuringMachine/Universal.lean:310:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:333:6: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:358:83: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:423:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:430:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:439:71: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:439:83: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:466:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:473:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:483:39: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:617:75: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:618:16: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:618:28: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:640:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:655:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:634:10: warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
TCSlib/Complexity/TuringMachine/Universal.lean:651:85: warning: This simp argument is unused:
  universalSkipDone

Hint: Omit it from the simp argument list.
  simp [timedCutInterpreter, universalInterpreter, universalFour, hr, h, hz,̵ ̵u̵n̵i̵v̵e̵r̵s̵a̵l̵S̵k̵i̵p̵D̵o̵n̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Universal.lean:665:50: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:665:62: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:680:10: warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
TCSlib/Complexity/TuringMachine/Universal.lean:736:53: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:736:65: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:757:50: warning: This simp argument is unused:
  Nat.add_zero

Hint: Omit it from the simp argument list.
  simp only [List.length_nil, List.flatMap_nil, Nat.a̵d̵d̵_̵zero,̵ ̵N̵a̵t̵.̵z̵e̵r̵o̵_add,
  ̵  ̵ ̵ ̵ ̵ ̵Nat.cast_zero, add_zero,
  ̲  ̲ ̲ ̲ ̲ ̲MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Universal.lean:816:40: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:843:40: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:861:6: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:861:61: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:861:73: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:861:6: warning: 'simp only [Fin.val_mk, Nat.cast_add, Nat.cast_one]' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:861:61: warning: 'congr 1' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:861:73: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:885:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:893:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:1002:40: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:1102:68: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Universal.lean:1480:16: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1480:34: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1480:61: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1480:16: warning: 'apply Fin.ext' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1480:34: warning: 'simp only [Fin.val_mk]' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1480:61: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1574:30: warning: This simp argument is unused:
  Nat.reduceAdd

Hint: Omit it from the simp argument list.
  simp only [Nat.add_assoc,̵ ̵N̵a̵t̵.̵r̵e̵d̵u̵c̵e̵A̵d̵d̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Universal.lean:1579:16: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1579:34: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1579:61: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1579:16: warning: 'apply Fin.ext' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1579:34: warning: 'simp only [Fin.val_mk]' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1579:61: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1602:28: warning: This simp argument is unused:
  Nat.reduceAdd

Hint: Omit it from the simp argument list.
  simp only [Nat.add_assoc,̵ ̵N̵a̵t̵.̵r̵e̵d̵u̵c̵e̵A̵d̵d̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Universal.lean:1604:43: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Universal.lean:1604:10: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:1604:28: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:1604:55: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:2274:46: warning: This simp argument is unused:
  VirtualTag

Hint: Omit it from the simp argument list.
  simp_all ̵[̵V̵i̵r̵t̵u̵a̵l̵T̵a̵g̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
[33/65] TCSlib/Complexity/Uncomputability/Computable
[34/65] TCSlib/Complexity/Uncomputability/Diagonalization
[35/65] TCSlib/Complexity/Uncomputability/Halting
[36/65] TCSlib/Complexity/TuringMachine/Nondeterministic
[37/65] TCSlib/Complexity/Formulas/CNF
[38/65] TCSlib/Complexity/Formulas/CNFEncoding
[39/65] TCSlib/Complexity/Formulas/DNF
[40/65] TCSlib/Complexity/ClassNP/PolyTime
[41/65] TCSlib/Complexity/ClassNP/PolyTimePairing
[42/65] TCSlib/Complexity/ClassNP/NP
[43/65] TCSlib/Complexity/ClassNP/CoNP
[44/65] TCSlib/Complexity/ClassNP/EXP
TCSlib/Complexity/ClassNP/EXP.lean:2755:66: warning: This simp argument is unused:
  bufferTape

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.initCfg, Cfg.init, a3LoadCfg,̵ ̵b̵u̵f̵f̵e̵r̵T̵a̵p̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/EXP.lean:2781:88: warning: This simp argument is unused:
  bufferTape

Hint: Omit it from the simp argument list.
  simp [Action.apply, Cfg.ofWords, stateWord, b̵u̵f̵f̵e̵r̵T̵a̵p̵e̵,̵ ̵hz]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/EXP.lean:2799:66: warning: This simp argument is unused:
  a3LoadCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, a̵3̵L̵o̵a̵d̵C̵f̵g̵,̵ ̵hz]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/EXP.lean:2800:66: warning: This simp argument is unused:
  a3LoadCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, a̵3̵L̵o̵a̵d̵C̵f̵g̵,̵ ̵hz, sub_eq_add_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
[45/65] TCSlib/Complexity/ClassNP/Reductions
[46/65] TCSlib/Complexity/ClassNP/NTIME
TCSlib/Complexity/ClassNP/NTIME.lean:215:8: warning: `Set.eq_empty_iff_forall_not_mem` has been deprecated: Use `Set.eq_empty_iff_forall_notMem` instead
[47/65] TCSlib/Complexity/ClassNP/Nondeterminism
TCSlib/Complexity/ClassNP/Nondeterminism.lean:3247:8: warning: This simp argument is unused:
  Fin.val_zero

Hint: Omit it from the simp argument list.
  simp only [e3cClearCfg, MultiTapeTM.step, e3cClearTM, Cfg.workTapeSymbols, F̵i̵n̵.̵v̵a̵l̵_̵z̵e̵r̵o̵,̵ ̵Fin.val_one,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲Nat.one_ne_zero, ↓reduceIte, hmark, reduceCtorEq, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:3247:22: warning: This simp argument is unused:
  Fin.val_one

Hint: Omit it from the simp argument list.
  simp only [e3cClearCfg, MultiTapeTM.step, e3cClearTM, Cfg.workTapeSymbols, Fin.val_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲F̵i̵n̵.̵v̵a̵l̵_̵o̵n̵e̵,̵ ̵Nat.one_ne_zero, ↓reduceIte, hmark, reduceCtorEq, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:3247:35: warning: This simp argument is unused:
  Nat.one_ne_zero

Hint: Omit it from the simp argument list.
  simp only [e3cClearCfg, MultiTapeTM.step, e3cClearTM, Cfg.workTapeSymbols, Fin.val_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲Fin.val_one, N̵a̵t̵.̵o̵n̵e̵_̵n̵e̵_̵z̵e̵r̵o̵,̵ ̵↓reduceIte, hmark, reduceCtorEq, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:3289:27: warning: This simp argument is unused:
  Fin.val_zero

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, e3cClearCfg, e3cClearTM, Cfg.workTapeSymbols, F̵i̵n̵.̵v̵a̵l̵_̵z̵e̵r̵o̵,̵ ̵Fin.val_one,
  ̲  ̲ ̲ ̲ ̲ ̲Nat.one_ne_zero, ↓reduceIte, hmark, reduceCtorEq, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:3289:41: warning: This simp argument is unused:
  Fin.val_one

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, e3cClearCfg, e3cClearTM,
  ̵  ̵ ̵ ̵ ̵ ̵Cfg.workTapeSymbols, Fin.val_zero,
  ̲ F̵i̵n̵.̵v̵a̵l̵_̵o̵n̵e̵,̵  ̲ ̲ ̲ ̲Nat.one_ne_zero, ↓reduceIte, hmark,
  ̵  ̵ ̵ ̵ ̵ ̵reduceCtorEq, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:3289:54: warning: This simp argument is unused:
  Nat.one_ne_zero

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, e3cClearCfg, e3cClearTM, Cfg.workTapeSymbols, Fin.val_zero,
  ̲  ̲ ̲ ̲ ̲ ̲Fin.val_one, N̵a̵t̵.̵o̵n̵e̵_̵n̵e̵_̵z̵e̵r̵o̵,̵ ̵↓reduceIte, hmark, reduceCtorEq, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:3336:8: warning: This simp argument is unused:
  Fin.val_zero

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, e3cClearCfg, e3cClearTM, Cfg.workTapeSymbols, F̵i̵n̵.̵v̵a̵l̵_̵z̵e̵r̵o̵,̵ ̵Fin.val_one,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲Nat.one_ne_zero, ↓reduceIte, hblank, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:3336:22: warning: This simp argument is unused:
  Fin.val_one

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, e3cClearCfg, e3cClearTM, Cfg.workTapeSymbols, Fin.val_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲F̵i̵n̵.̵v̵a̵l̵_̵o̵n̵e̵,̵ ̵Nat.one_ne_zero, ↓reduceIte, hblank, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:3336:35: warning: This simp argument is unused:
  Nat.one_ne_zero

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, e3cClearCfg, e3cClearTM, Cfg.workTapeSymbols, Fin.val_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲Fin.val_one, N̵a̵t̵.̵o̵n̵e̵_̵n̵e̵_̵z̵e̵r̵o̵,̵ ̵↓reduceIte, hblank, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:3368:6: warning: This simp argument is unused:
  Fin.val_zero

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, e3cClearCfg, e3cClearTM, Cfg.workTapeSymbols, F̵i̵n̵.̵v̵a̵l̵_̵z̵e̵r̵o̵,̵ ̵Fin.val_one,
  ̲  ̲ ̲ ̲ ̲ ̲Nat.one_ne_zero, ↓reduceIte, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:3368:20: warning: This simp argument is unused:
  Fin.val_one

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, e3cClearCfg, e3cClearTM, Cfg.workTapeSymbols, Fin.val_zero,
  ̲  ̲ ̲ ̲ ̲ ̲F̵i̵n̵.̵v̵a̵l̵_̵o̵n̵e̵,̵ ̵Nat.one_ne_zero, ↓reduceIte, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:3368:33: warning: This simp argument is unused:
  Nat.one_ne_zero

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, e3cClearCfg, e3cClearTM, Cfg.workTapeSymbols, Fin.val_zero,
  ̲  ̲ ̲ ̲ ̲ ̲Fin.val_one, N̵a̵t̵.̵o̵n̵e̵_̵n̵e̵_̵z̵e̵r̵o̵,̵ ̵↓reduceIte, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:3397:19: warning: This simp argument is unused:
  min_le_right

Hint: Omit it from the simp argument list.
  simp [e3cSpan, m̵i̵n̵_̵l̵e̵_̵r̵i̵g̵h̵t̵,̵ ̵le_max_right]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:3397:33: warning: This simp argument is unused:
  le_max_right

Hint: Omit it from the simp argument list.
  simp [e3cSpan, min_le_right,̵ ̵l̵e̵_̵m̵a̵x̵_̵r̵i̵g̵h̵t̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:3585:21: warning: This simp argument is unused:
  hspan

Hint: Omit it from the simp argument list.
  simp [e3cSpan, h̵s̵p̵a̵n̵,̵ ̵bufferTape, hn, List.getElem?_eq_none hlen]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:3586:21: warning: This simp argument is unused:
  hspan

Hint: Omit it from the simp argument list.
  simp [e3cSpan, h̵s̵p̵a̵n̵,̵ ̵bufferTape, hn]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:3695:62: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:4147:27: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:4147:27: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:4656:52: warning: This simp argument is unused:
  bufferTape

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.initCfg, Cfg.init, a2LoadCfg,̵ ̵b̵u̵f̵f̵e̵r̵T̵a̵p̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:4686:36: warning: This simp argument is unused:
  a2LoadCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, a̵2̵L̵o̵a̵d̵C̵f̵g̵,̵ ̵sub_eq_add_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5176:40: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5182:42: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5198:78: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5168:55: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5169:54: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5171:61: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5180:55: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5188:58: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5176:40: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5182:42: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5198:78: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5216:65: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5222:58: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5238:60: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5210:55: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5211:54: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5212:61: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5221:55: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5228:58: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5216:65: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5222:58: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5238:60: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5249:55: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5283:34: warning: This simp argument is unused:
  a3nEqCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply,̵ ̵a̵3̵n̵E̵q̵C̵f̵g̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5294:36: warning: This simp argument is unused:
  a3nEqCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, a̵3̵n̵E̵q̵C̵f̵g̵,̵ ̵sub_eq_add_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5333:17: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5304:55: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5306:42: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5314:42: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5316:92: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5359:51: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5352:65: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5359:51: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5387:63: warning: This simp argument is unused:
  bufferTape

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.initCfg, Cfg.init, a3nEqCfg,̵ ̵b̵u̵f̵f̵e̵r̵T̵a̵p̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5556:63: warning: This simp argument is unused:
  Bool.true_eq

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.indicator, hmem, Function.comp_apply, a3n_fst, a3n_snd, a3n_concat, hw,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲hx', pairDecode_pairEncode, Option.map_some, Option.getD_some, Option.isSome_some, B̵o̵o̵l̵.̵t̵r̵u̵e̵_̵e̵q̵,̵if_true,
          e3c_bits_injective.eq_iff, decide_eq_true_eq, ite_and]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
[48/65] TCSlib/Complexity/ClassNP/SAT
TCSlib/Complexity/ClassNP/SAT.lean:164:51: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:176:47: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:371:33: warning: Try `simp at h` instead of `simpa using h`

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/ClassNP/SAT.lean:494:63: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:646:56: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:671:59: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:708:55: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:718:58: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:729:88: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:758:60: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/ClassNP/SAT.lean:769:27: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/ClassNP/SAT.lean:791:91: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/ClassNP/SAT.lean:758:60: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/ClassNP/SAT.lean:769:27: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/ClassNP/SAT.lean:791:91: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/ClassNP/SAT.lean:787:84: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:847:56: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/ClassNP/SAT.lean:847:56: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/ClassNP/SAT.lean:830:63: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:854:51: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:915:48: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:955:55: warning: This simp argument is unused:
  FinTM.bufferTape

Hint: Omit it from the simp argument list.
  simp [captureCfg, MultiTapeTM.initCfg, Cfg.init,̵ ̵F̵i̵n̵T̵M̵.̵b̵u̵f̵f̵e̵r̵T̵a̵p̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:1017:26: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:1296:8: warning: This simp argument is unused:
  satSafeValue

Hint: Omit it from the simp argument list.
  simp [satVerdict, satSplitValid, satSplit, hs, pairDecode_pairEncode, s̵a̵t̵S̵a̵f̵e̵V̵a̵l̵u̵e̵,̵ ̵satGood, satInstance,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲satWitness, satSyntax_spec, hp, CNF.decode, CNF.fallback, satWidth]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:1296:22: warning: This simp argument is unused:
  satGood

Hint: Omit it from the simp argument list.
  simp [satVerdict, satSplitValid, satSplit, hs, pairDecode_pairEncode,
  ̵  ̵ ̵ ̵ ̵ ̵ ̵ ̵satSafeValue,
  ̲ s̵a̵t̵G̵o̵o̵d̵,̵  ̲ ̲ ̲ ̲ ̲ ̲satInstance, satWitness, satSyntax_spec, hp,
  ̵  ̵ ̵ ̵ ̵ ̵ ̵ ̵CNF.decode, CNF.fallback, satWidth]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:1296:44: warning: This simp argument is unused:
  satWitness

Hint: Omit it from the simp argument list.
  simp [satVerdict, satSplitValid, satSplit, hs, pairDecode_pairEncode, satSafeValue, satGood,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲satInstance, s̵a̵t̵W̵i̵t̵n̵e̵s̵s̵,̵ ̵satSyntax_spec, hp, CNF.decode, CNF.fallback, satWidth]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:1395:80: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:1523:11: warning: Try `simp at h` instead of `simpa using h`

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/ClassNP/SAT.lean:1990:12: warning: This simp argument is unused:
  he

Hint: Omit it from the simp argument list.
  simp [h̵e̵,̵ ̵satRedCounter_read, show r < n by omega]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:1987:39: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:2001:17: warning: unused variable `hj`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
TCSlib/Complexity/ClassNP/SAT.lean:2007:52: warning: This simp argument is unused:
  max_eq_left

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.runFrom_zero, m̵a̵x̵_̵e̵q̵_̵l̵e̵f̵t̵,̵ ̵*]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:2022:59: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/ClassNP/SAT.lean:2022:59: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/ClassNP/SAT.lean:2077:19: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/ClassNP/SAT.lean:2077:19: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/ClassNP/SAT.lean:2042:40: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:2087:82: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:2091:73: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:2093:41: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:2150:40: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/ClassNP/SAT.lean:2150:40: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/ClassNP/SAT.lean:2156:51: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:2175:47: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:2208:48: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:2228:28: warning: This simp argument is unused:
  Function.update_of_ne hz

Hint: Omit it from the simp argument list.
  simp [satRedBuffer, hz, F̵u̵n̵c̵t̵i̵o̵n̵.̵u̵p̵d̵a̵t̵e̵_̵o̵f̵_̵n̵e̵ ̵h̵z̵,̵ ̵FinTM.bufferTape]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:2315:19: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/ClassNP/SAT.lean:2501:52: warning: This simp argument is unused:
  List.append_assoc

Hint: Omit it from the simp argument list.
  simp [satStreamTail, CNF.serializeClause, hp, L̵i̵s̵t̵.̵a̵p̵p̵e̵n̵d̵_̵a̵s̵s̵o̵c̵,̵ ̵Nat.add_assoc]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:2543:69: warning: This simp argument is unused:
  List.append_assoc

Hint: Omit it from the simp argument list.
  simp [satStreamRun, satStreamClause, CNF.serializeClause, hp₁, L̵i̵s̵t̵.̵a̵p̵p̵e̵n̵d̵_̵a̵s̵s̵o̵c̵,̵ ̵Nat.add_assoc]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:2606:52: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:2633:44: warning: This simp argument is unused:
  List.append_nil

Hint: Omit it from the simp argument list.
  simp only [List.length_nil, Nat.zero_add,̵ ̵L̵i̵s̵t̵.̵a̵p̵p̵e̵n̵d̵_̵n̵i̵l̵] at h

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:2648:24: warning: This simp argument is unused:
  Function.comp_apply

Hint: Omit it from the simp argument list.
  simp only [satStreamRun, ih, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map,
  ̲  ̲ ̲ ̲ ̲ ̲F̵u̵n̵c̵t̵i̵o̵n̵.̵c̵o̵m̵p̵_̵a̵p̵p̵l̵y̵,̵ ̵Function.iterate_zero_apply, Function.iterate_succ_apply]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:2683:29: warning: This simp argument is unused:
  Nat.mul_add

Hint: Omit it from the simp argument list.
  simp [List.length_flatMap, Nat.m̵u̵l̵_̵add,̵ ̵N̵a̵t̵.̵a̵d̵d̵_assoc, Nat.add_comm, Nat.add_left_comm,
  ̵  ̵ ̵ ̵Nat.mul_comm]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:2684:18: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:2968:67: warning: This simp argument is unused:
  FinTM.bufferTape

Hint: Omit it from the simp argument list.
  simp [captureCfg, MultiTapeTM.initCfg, Cfg.init,̵ ̵F̵i̵n̵T̵M̵.̵b̵u̵f̵f̵e̵r̵T̵a̵p̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:3094:30: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/ClassNP/SAT.lean:3094:30: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/ClassNP/SAT.lean:3093:82: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:3234:90: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/ClassNP/SAT.lean:3234:90: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/ClassNP/SAT.lean:3234:39: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:3301:33: warning: This simp argument is unused:
  Function.comp_def

Hint: Omit it from the simp argument list.
  simp [F̵u̵n̵c̵t̵i̵o̵n̵.̵c̵o̵m̵p̵_̵d̵e̵f̵,̵ ̵h]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:3396:73: warning: This simp argument is unused:
  List.append_assoc

Hint: Omit it from the simp argument list.
  simp [satRedAction, satRedCfg, Action.apply, List.replicate_succ',̵ ̵L̵i̵s̵t̵.̵a̵p̵p̵e̵n̵d̵_̵a̵s̵s̵o̵c̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:3440:68: warning: This simp argument is unused:
  hp

Hint: Omit it from the simp argument list.
  simp [satStreamCanonical, satSyntax_spec, CNF.decode, h̵p̵,̵ ̵sat_parse_repr hp,
  ̲  ̲ ̲ ̲CNF.parse_serialize]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:3459:25: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/ClassNP/SAT.lean:3459:25: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/ClassNP/SAT.lean:3656:26: warning: This simp argument is unused:
  hw

Hint: Omit it from the simp argument list.
  simp only [satDropTM, h̵w̵,̵ ̵Option.isSome_none, Bool.false_eq_true, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:3656:30: warning: This simp argument is unused:
  Option.isSome_none

Hint: Omit it from the simp argument list.
  simp only [satDropTM, hw, O̵p̵t̵i̵o̵n̵.̵i̵s̵S̵o̵m̵e̵_̵n̵o̵n̵e̵,̵ ̵Bool.false_eq_true, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:3656:50: warning: This simp argument is unused:
  Bool.false_eq_true

Hint: Omit it from the simp argument list.
  simp only [satDropTM, hw, Option.isSome_none, B̵o̵o̵l̵.̵f̵a̵l̵s̵e̵_̵e̵q̵_̵t̵r̵u̵e̵,̵ ̵↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:3656:70: warning: This simp argument is unused:
  ↓reduceIte

Hint: Omit it from the simp argument list.
  simp only [satDropTM, hw, Option.isSome_none, Bool.false_eq_true,̵ ̵↓̵r̵e̵d̵u̵c̵e̵I̵t̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:3662:45: warning: This simp argument is unused:
  he

Hint: Omit it from the simp argument list.
  simp [satDropCfg, Cfg.workTapeSymbols, h̵e̵,̵ ̵satRedCounter_read, show r < n by omega]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:3762:82: warning: This simp argument is unused:
  FinTM.bufferTape

Hint: Omit it from the simp argument list.
  simp [satDropCfg, satRedCounter, MultiTapeTM.initCfg, Cfg.init,̵ ̵F̵i̵n̵T̵M̵.̵b̵u̵f̵f̵e̵r̵T̵a̵p̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:3750:29: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:3950:50: warning: This simp argument is unused:
  List.replicate_succ

Hint: Omit it from the simp argument list.
  simp_all [satReqStep, satReqEmit, satReqPack, satStreamWord,
              satStreamRound, List.replicate_succ',̵ ̵L̵i̵s̵t̵.̵r̵e̵p̵l̵i̵c̵a̵t̵e̵_̵s̵u̵c̵c̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:3974:74: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:4104:55: warning: This simp argument is unused:
  sub_eq_add_neg

Hint: Omit it from the simp argument list.
  simp [satAppendCfg, Action.apply, SignType.cast, s̵u̵b̵_̵e̵q̵_̵a̵d̵d̵_̵n̵e̵g̵,̵ ̵add_assoc]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:4104:71: warning: This simp argument is unused:
  add_assoc

Hint: Omit it from the simp argument list.
  simp [satAppendCfg, Action.apply, SignType.cast, sub_eq_add_neg,̵ ̵a̵d̵d̵_̵a̵s̵s̵o̵c̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:4145:34: warning: This simp argument is unused:
  List.getElem?_cons_zero

Hint: Omit it from the simp argument list.
  simp only [satAppendTM, hr,̵ ̵L̵i̵s̵t̵.̵g̵e̵t̵E̵l̵e̵m̵?̵_̵c̵o̵n̵s̵_̵z̵e̵r̵o̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:4151:67: warning: This simp argument is unused:
  sub_eq_add_neg

Hint: Omit it from the simp argument list.
  simp [satAppendCfg, Action.apply, SignType.cast, s̵u̵b̵_̵e̵q̵_̵a̵d̵d̵_̵n̵e̵g̵,̵ ̵add_assoc]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:4175:69: warning: This simp argument is unused:
  add_assoc

Hint: Omit it from the simp argument list.
  simp [satAppendCfg, Action.apply, SignType.cast, sub_eq_add_neg,̵ ̵a̵d̵d̵_̵a̵s̵s̵o̵c̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:4312:62: warning: This simp argument is unused:
  hi

Hint: Omit it from the simp argument list.
  simp [satPadCfg, Cfg.ofWords,̵ ̵h̵i̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:4541:43: warning: This simp argument is unused:
  Nat.mul_assoc

Hint: Omit it from the simp argument list.
  simp only [Nat.add_mul, Nat.one_mul, N̵a̵t̵.̵m̵u̵l̵_̵a̵s̵s̵o̵c̵,̵ ̵two_mul]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:4588:55: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:4660:79: warning: This simp argument is unused:
  FinTM.bufferTape

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.initCfg, Cfg.init, Cfg.ofWords, stateWord,̵ ̵F̵i̵n̵T̵M̵.̵b̵u̵f̵f̵e̵r̵T̵a̵p̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:4675:30: warning: This simp argument is unused:
  Nat.mul_one

Hint: Omit it from the simp argument list.
  simp only [Nat.add_mul,̵ ̵N̵a̵t̵.̵m̵u̵l̵_̵o̵n̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
[49/65] TCSlib/Complexity/ClassNP/TMSAT
[50/65] TCSlib/Complexity/CookLevin/Snapshot
[51/65] TCSlib/Complexity/CookLevin/Hardness
TCSlib/Complexity/CookLevin/Hardness.lean:2011:35: warning: This simp argument is unused:
  hw

Hint: Omit it from the simp argument list.
  simp only ̵[̵h̵w̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:2011:39: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/CookLevin/Hardness.lean:2035:12: warning: This simp argument is unused:
  MultiTapeTM.step

Hint: Omit it from the simp argument list.
  simp [M̵u̵l̵t̵i̵T̵a̵p̵e̵T̵M̵.̵s̵t̵e̵p̵,̵ ̵hs, FinTM.controlAction, Action.apply]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:2035:55: warning: This simp argument is unused:
  Action.apply

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.step, hs, FinTM.controlAction,̵ ̵A̵c̵t̵i̵o̵n̵.̵a̵p̵p̵l̵y̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:2038:23: warning: This simp argument is unused:
  MultiTapeTM.step

Hint: Omit it from the simp argument list.
  simp [clBankCfg, M̵u̵l̵t̵i̵T̵a̵p̵e̵T̵M̵.̵s̵t̵e̵p̵,̵ ̵hs, FinTM.controlAction, Action.apply]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:2041:23: warning: This simp argument is unused:
  MultiTapeTM.step

Hint: Omit it from the simp argument list.
  simp [clBankCfg, M̵u̵l̵t̵i̵T̵a̵p̵e̵T̵M̵.̵s̵t̵e̵p̵,̵ ̵hs, FinTM.controlAction, Action.apply]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:2171:31: warning: This simp argument is unused:
  MultiTapeTM.step_of_halt hs

Hint: Omit it from the simp argument list.
  simp [clMoves, hs,̵ ̵M̵u̵l̵t̵i̵T̵a̵p̵e̵T̵M̵.̵s̵t̵e̵p̵_̵o̵f̵_̵h̵a̵l̵t̵ ̵h̵s̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:2480:13: warning: This simp argument is unused:
  Fin.cases_zero

Hint: Omit it from the simp argument list.
  simp only [clCopyTM, ↓reduceIte, clCopyCfg, Cfg.workTapeSymbols, clTwo, F̵i̵n̵.̵c̵a̵s̵e̵s̵_̵z̵e̵r̵o̵,̵ ̵hr]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:2486:43: warning: This simp argument is unused:
  Fin.cases_zero

Hint: Omit it from the simp argument list.
  simp only [clCopyTM, show (1 : Fin 5) ≠ 0 by decide, ↓reduceIte, clCopyCfg, Cfg.workTapeSymbols,
  ̲  ̲ ̲ ̲clTwo, F̵i̵n̵.̵c̵a̵s̵e̵s̵_̵z̵e̵r̵o̵,̵ ̵hr, Option.getD_some]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:2520:13: warning: This simp argument is unused:
  Fin.cases_zero

Hint: Omit it from the simp argument list.
  simp only [clCopyTM, ↓reduceIte, clCopyCfg, Cfg.workTapeSymbols, clTwo, F̵i̵n̵.̵c̵a̵s̵e̵s̵_̵z̵e̵r̵o̵,̵ ̵hr]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:2558:59: warning: This simp argument is unused:
  Fin.cases_zero

Hint: Omit it from the simp argument list.
  simp only [clCopyTM, show (3 : Fin 5) ≠ 0 by decide, show (3 : Fin 5) ≠ 1 by decide,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲show (3 : Fin 5) ≠ 2 by decide, ↓reduceIte, clCopyCfg, Cfg.workTapeSymbols, clTwo, F̵i̵n̵.̵c̵a̵s̵e̵s̵_̵z̵e̵r̵o̵,̵ ̵hr]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:2560:47: warning: This simp argument is unused:
  clCopyCfg

Hint: Omit it from the simp argument list.
  simp [clTwo, c̵l̵C̵o̵p̵y̵C̵f̵g̵,̵ ̵Action.apply]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:2561:47: warning: This simp argument is unused:
  clCopyCfg

Hint: Omit it from the simp argument list.
  simp [clTwo, c̵l̵C̵o̵p̵y̵C̵f̵g̵,̵ ̵Action.apply, sub_eq_add_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:2784:8: warning: Try this: intro j hj q hq heq
TCSlib/Complexity/CookLevin/Hardness.lean:2916:62: warning: This simp argument is unused:
  List.append_assoc

Hint: Omit it from the simp argument list.
  simp [pairEncode, List.flatMap_cons,̵ ̵L̵i̵s̵t̵.̵a̵p̵p̵e̵n̵d̵_̵a̵s̵s̵o̵c̵] at ⊢ ih

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:3251:95: warning: This simp argument is unused:
  clRight_ne_left

Hint: Omit it from the simp argument list.
  simp [clRecCfg, clRecClockIndex, Action.apply, FinTM.tapeBlocks, clLeft_ne_right,
  ̲ c̵l̵R̵i̵g̵h̵t̵_̵n̵e̵_̵l̵e̵f̵t̵,̵  ̲ ̲-Fin.natAdd_eq_addNat]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:3254:97: warning: This simp argument is unused:
  clRight_ne_left

Hint: Omit it from the simp argument list.
  simp [clRecCfg, clRecClockIndex, Action.apply, FinTM.tapeBlocks, clLeft_ne_right,
  ̲ c̵l̵R̵i̵g̵h̵t̵_̵n̵e̵_̵l̵e̵f̵t̵,̵  ̲ ̲ ̲ ̲-Fin.natAdd_eq_addNat]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:3260:73: warning: This simp argument is unused:
  clLeft_ne_right

Hint: Omit it from the simp argument list.
  simp [clRecCfg, clRecClockIndex, Action.apply, FinTM.tapeBlocks, c̵l̵L̵e̵f̵t̵_̵n̵e̵_̵r̵i̵g̵h̵t̵,̵ ̵clRight_ne_left,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲ ̲ ̲-Fin.natAdd_eq_addNat]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:3260:90: warning: This simp argument is unused:
  clRight_ne_left

Hint: Omit it from the simp argument list.
  simp [clRecCfg, clRecClockIndex, Action.apply, FinTM.tapeBlocks, clLeft_ne_right,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲ ̲ ̲c̵l̵R̵i̵g̵h̵t̵_̵n̵e̵_̵l̵e̵f̵t̵,̵ ̵-Fin.natAdd_eq_addNat]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:3261:82: warning: This simp argument is unused:
  clLeft_ne_right

Hint: Omit it from the simp argument list.
  simp [clRecCfg, clRecClockIndex, Action.apply, FinTM.tapeBlocks, c̵l̵L̵e̵f̵t̵_̵n̵e̵_̵r̵i̵g̵h̵t̵,̵ ̵clRight_ne_left,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲-Fin.natAdd_eq_addNat]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:3880:46: warning: This simp argument is unused:
  ↓reduceIte

Hint: Omit it from the simp argument list.
  simp only [clSignedWords,̵ ̵↓̵r̵e̵d̵u̵c̵e̵I̵t̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:3960:29: warning: This simp argument is unused:
  Option.bind_some

Hint: Omit it from the simp argument list.
  simp only [List.length_cons, clReadFields, clFields, clPair_append, p̵a̵i̵r̵D̵e̵c̵o̵d̵e̵_̵p̵a̵i̵r̵E̵n̵c̵o̵d̵e̵,̵ ̵O̵p̵t̵i̵o̵n̵.̵b̵i̵n̵d̵_̵s̵o̵m̵e̵]̵p̲a̲i̲r̲D̲e̲c̲o̲d̲e̲_̲p̲a̲i̲r̲E̲n̲c̲o̲d̲e̲]̲

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:4031:57: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/CookLevin/Hardness.lean:4112:77: warning: This simp argument is unused:
  if_false

Hint: Omit it from the simp argument list.
  simp only [clReadTM, clReadCfg, Cfg.workTapeSymbols, clTwo,
  ̵  ̵ ̵ ̵ ̵ ̵ ̵ ̵show (1 : Fin 2) ≠ 0 by decide,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲↓reduceIte, hr, Option.some_ne_none,̵ ̵i̵f̵_̵f̵a̵l̵s̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:4136:27: warning: This simp argument is unused:
  ih

Hint: Omit it from the simp argument list.
  simp ̵[̵i̵h̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:4208:49: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/CookLevin/Hardness.lean:4425:65: warning: This simp argument is unused:
  if_false

Hint: Omit it from the simp argument list.
  simp only [clWipeTM, clWipeCfg, Cfg.workTapeSymbols, clTwo, ↓reduceIte,
          show (1 : Fin 2) ≠ 0 by decide, hr, Option.some_ne_none,̵ ̵i̵f̵_̵f̵a̵l̵s̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:4457:59: warning: This simp argument is unused:
  if_false

Hint: Omit it from the simp argument list.
  simp only [clWipeTM, show (1 : Fin 3) ≠ 0 by decide, i̵f̵_̵f̵a̵l̵s̵e̵,̵ ̵if_true, clWipeCfg, Cfg.workTapeSymbols,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲clTwo, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte, hr, Option.some_ne_none]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:4457:69: warning: This simp argument is unused:
  if_true

Hint: Omit it from the simp argument list.
  simp only [clWipeTM, show (1 : Fin 3) ≠ 0 by decide, if_false, i̵f̵_̵t̵r̵u̵e̵,̵clWipeCfg, Cfg.workTapeSymbols,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲clTwo, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte, hr, Option.some_ne_none]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:4869:22: warning: This simp argument is unused:
  funext_iff

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.step, clInputTM, clInputCfg, Cfg.inputSymbol, Action.apply, m̵o̵v̵e̵I̵n̵p̵u̵t̵P̵o̵s̵,̵ ̵f̵u̵n̵e̵x̵t̵_̵i̵f̵f̵]̵m̲o̲v̲e̲I̲n̲p̲u̲t̲P̲o̲s̲]̲

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:4894:82: warning: This simp argument is unused:
  funext_iff

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.initCfg, Cfg.init, clInputCfg, clInputTM,̵ ̵f̵u̵n̵e̵x̵t̵_̵i̵f̵f̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:4902:8: warning: This simp argument is unused:
  FinTM.moveInputPos_neg_val

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.step, clInputTM, clInputCfg, Cfg.inputSymbol, Action.apply, F̵i̵n̵T̵M̵.̵m̵o̵v̵e̵I̵n̵p̵u̵t̵P̵o̵s̵_̵n̵e̵g̵_̵v̵a̵l̵,̵ ̵funext_iff,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲sub_eq_add_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:4902:36: warning: This simp argument is unused:
  funext_iff

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.step, clInputTM, clInputCfg, Cfg.inputSymbol, Action.apply,
          FinTM.moveInputPos_neg_val, f̵u̵n̵e̵x̵t̵_̵i̵f̵f̵,̵ ̵sub_eq_add_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:5317:59: warning: This simp argument is unused:
  hne

Hint: Omit it from the simp argument list.
  simp [clMatchCmpSelect, clMatchCmpIndex, hne,̵ ̵h̵n̵e̵.symm,
  ̵  ̵ ̵ ̵-Fin.natAdd_eq_addNat]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:5517:54: warning: This simp argument is unused:
  ↓reduceIte

Hint: Omit it from the simp argument list.
  simp only [clMatchWords,̵ ̵↓̵r̵e̵d̵u̵c̵e̵I̵t̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:5554:54: warning: This simp argument is unused:
  Nat.add_assoc

Hint: Omit it from the simp argument list.
  simp [clRows, ih, List.append_assoc,̵ ̵N̵a̵t̵.̵a̵d̵d̵_̵a̵s̵s̵o̵c̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:5678:64: warning: This simp argument is unused:
  if_false

Hint: Omit it from the simp argument list.
  simp only [clTwo, ↓reduceIte, show (1 : Fin 2) ≠ 0 by decide, i̵f̵_̵f̵a̵l̵s̵e̵,̵ ̵clNum_bits]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:5713:62: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/CookLevin/Hardness.lean:5831:90: warning: This simp argument is unused:
  funext_iff

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.step, clReplayTM, clReplayCfg, Cfg.workTapeSymbols, Action.apply,̵ ̵f̵u̵n̵e̵x̵t̵_̵i̵f̵f̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:5862:90: warning: This simp argument is unused:
  funext_iff

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.step, clReplayTM, clReplayCfg, Cfg.workTapeSymbols, Action.apply,̵ ̵f̵u̵n̵e̵x̵t̵_̵i̵f̵f̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:5873:44: warning: This simp argument is unused:
  funext_iff

Hint: Omit it from the simp argument list.
  simp [Action.apply,̵ ̵f̵u̵n̵e̵x̵t̵_̵i̵f̵f̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:5886:69: warning: This simp argument is unused:
  funext_iff

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.step, clReplayTM, clReplayCfg, Action.apply, f̵u̵n̵e̵x̵t̵_̵i̵f̵f̵,̵ ̵sub_eq_add_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:6185:96: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/CookLevin/Hardness.lean:6391:69: warning: This simp argument is unused:
  funext_iff

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.step, clReplayTM, clReplayCfg, Action.apply, f̵u̵n̵e̵x̵t̵_̵i̵f̵f̵,̵ ̵sub_eq_add_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:6642:62: warning: This simp argument is unused:
  ↓reduceIte

Hint: Omit it from the simp argument list.
  simp only [target, clSearchTarget, clTwo,̵ ̵↓̵r̵e̵d̵u̵c̵e̵I̵t̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:7078:63: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/CookLevin/Hardness.lean:7134:65: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/CookLevin/Hardness.lean:7383:63: warning: This simp argument is unused:
  hi

Hint: Omit it from the simp argument list.
  simp [clA5PadCfg, Cfg.ofWords,̵ ̵h̵i̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:7611:43: warning: This simp argument is unused:
  Nat.mul_assoc

Hint: Omit it from the simp argument list.
  simp only [Nat.add_mul, Nat.one_mul, N̵a̵t̵.̵m̵u̵l̵_̵a̵s̵s̵o̵c̵,̵ ̵two_mul]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:7687:65: warning: This simp argument is unused:
  FinTM.bufferTape

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.initCfg, Cfg.init, Cfg.ofWords, stateWord,̵ ̵F̵i̵n̵T̵M̵.̵b̵u̵f̵f̵e̵r̵T̵a̵p̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:7781:65: warning: This simp argument is unused:
  FinTM.bufferTape

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.initCfg, Cfg.init, Cfg.ofWords, stateWord,̵ ̵F̵i̵n̵T̵M̵.̵b̵u̵f̵f̵e̵r̵T̵a̵p̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:7910:90: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/CookLevin/Hardness.lean:7910:90: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/CookLevin/Hardness.lean:7910:39: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/CookLevin/Hardness.lean:7977:33: warning: This simp argument is unused:
  Function.comp_def

Hint: Omit it from the simp argument list.
  simp [F̵u̵n̵c̵t̵i̵o̵n̵.̵c̵o̵m̵p̵_̵d̵e̵f̵,̵ ̵h]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:8000:108: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only [clRepeatWords,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲Fin.addCases_left, stateWord, F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵,̵ ̵if_pos rfl, if_pos True.intro]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:8000:120: warning: This simp argument is unused:
  if_pos rfl

Hint: Omit it from the simp argument list.
  simp only [clRepeatWords,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲Fin.addCases_left, stateWord, Fin.val_mk, if_pos r̵f̵l̵,̵ ̵i̵f̵_̵p̵o̵s̵ ̵True.intro]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:8373:69: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/CookLevin/Hardness.lean:8644:57: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/CookLevin/Hardness.lean:8672:45: warning: This simp argument is unused:
  Nat.mul_comm

Hint: Omit it from the simp argument list.
  simp [pairEncode, List.length_flatMap,̵ ̵N̵a̵t̵.̵m̵u̵l̵_̵c̵o̵m̵m̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:8672:59: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/CookLevin/Hardness.lean:8739:64: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/CookLevin/Hardness.lean:9069:15: warning: This simp argument is unused:
  List.getElem?_range h

Hint: Omit it from the simp argument list.
  simp [h,̵ ̵L̵i̵s̵t̵.̵g̵e̵t̵E̵l̵e̵m̵?̵_̵r̵a̵n̵g̵e̵ ̵h̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:9077:10: warning: This simp argument is unused:
  h0

Hint: Omit it from the simp argument list.
  simp [h̵0̵,̵ ̵rangeGet, h0]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:9077:14: warning: This simp argument is unused:
  rangeGet

Hint: Omit it from the simp argument list.
  simp [h0, r̵a̵n̵g̵e̵G̵e̵t̵,̵ ̵h0]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:9084:18: warning: This simp argument is unused:
  rangeGet

Hint: Omit it from the simp argument list.
  simp [h2,̵ ̵r̵a̵n̵g̵e̵G̵e̵t̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:9087:20: warning: This simp argument is unused:
  rangeGet

Hint: Omit it from the simp argument list.
  simp [h3,̵ ̵r̵a̵n̵g̵e̵G̵e̵t̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
[52/65] TCSlib/Complexity/ClassNP/Tautology
[53/65] TCSlib/Complexity/TuringMachine/UnaryTape
[54/65] TCSlib/Complexity/TuringMachine/CounterProg
[55/65] TCSlib/Complexity/TuringMachine/CounterProgRun
[56/65] TCSlib/Complexity/TuringMachine
[57/65] TCSlib/Complexity/ClassP
[58/65] TCSlib/Complexity/Uncomputability
[59/65] TCSlib/Complexity/Formulas
[60/65] TCSlib/Complexity/CookLevin
[61/65] TCSlib/Complexity/ClassNP/Transducer
[62/65] TCSlib/Complexity/ClassNP/CounterProgPolyTime
[63/65] TCSlib/Complexity/ClassNP/PClosure
[64/65] TCSlib/Complexity/ClassNP/ExpPoly
[65/65] TCSlib/Complexity/ClassNP
SWEEP_OK 65/65 2026-10-06T20:28:40Z

## ===== audits/logs/ch2-epoch34-r2-lint.log =====

# Scoped final lint over the six owned files (finding 3)

WARN  TCSlib/Complexity/CookLevin/Hardness.lean  9937 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
INFO  TCSlib/Complexity/CookLevin/Hardness.lean  9937 lines; 5 public / 618 private declarations
INFO  TCSlib/Complexity/CookLevin/Snapshot.lean  368 lines; 14 public / 4 private declarations
WARN  TCSlib/Complexity/ClassNP/EXP.lean                  3268 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/ClassNP/Nondeterminism.lean       5835 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/ClassNP/SAT.lean                  4815 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/ClassNP/TMSAT.lean                1755 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/ClassNP/Tautology.lean            1749 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
INFO  TCSlib/Complexity/ClassNP/EXP.lean                  3268 lines; 8 public / 147 private declarations
INFO  TCSlib/Complexity/ClassNP/Nondeterminism.lean       5835 lines; 8 public / 271 private declarations
INFO  TCSlib/Complexity/ClassNP/SAT.lean                  4815 lines; 5 public / 288 private declarations
INFO  TCSlib/Complexity/ClassNP/TMSAT.lean                1755 lines; 6 public / 76 private declarations
INFO  TCSlib/Complexity/ClassNP/Tautology.lean            1749 lines; 5 public / 95 private declarations

The five owned-file size exceptions of this gate: Hardness 9,937; Nondeterminism 5,835; SAT 4,815; EXP 3,268; Tautology 1,749 (Snapshot, 368, is under target). TMSAT.lean's WARN (1,755) is the standing epoch-2 exception, out of this gate's owned set, shown because the subtree scan covers it. FAIL count in both subtree runs: 0. The INFO public counts independently confirm the round-2 program's source-derived public lists on all six owned files (8/8/5/14/5/5).

## ===== audits/evidence/ch2-epoch34/merge2-owned-diffs.md =====

# Merge #2 owned-file evidence (finding 2)

First-parent diffs of merge commit `53072100` (bringing `f70c57c2`) on the two
owned files it touched, with git blob identities on both sides. The before
side is `5dc0881a` (= the A5 brief tip, the last pre-merge state of these
files, identical to their state at the 4A-5 integration); the after side is
the merge result, byte-identical to the current HEAD state audited by the
round-2 closure program.

## TCSlib/Complexity/ClassNP/SAT.lean

- before blob (git SHA-1): `d32714839d08b08412faefbef1f7d5c0fa5417e5`
- after blob (git SHA-1): `75cacb8164d2054dc4ae9f4358ed0df0ad6ce96d` (= HEAD)

```diff
diff --git a/TCSlib/Complexity/ClassNP/SAT.lean b/TCSlib/Complexity/ClassNP/SAT.lean
index d3271483..75cacb81 100644
--- a/TCSlib/Complexity/ClassNP/SAT.lean
+++ b/TCSlib/Complexity/ClassNP/SAT.lean
@@ -70,6 +70,44 @@ namespace Complexity
 open Std.Sat (CNF)
 open Turing
 
+/-! Local names for the shared polynomial-time toolkit (`ClassNP/PolyTimePairing.lean`,
+`TuringMachine/Composition.lean`), kept so this file's proofs can keep using its
+historical `sat_*` names. -/
+
+/-- A function computed in linear time is polynomial-time computable
+(`polyTimeComputable_of_linear`). -/
+private lemma sat_pt_linear (f : List Bool → List Bool)
+    (h : ∃ (M : FinTM Bool) (C : ℕ),
+      M.ComputesFunInTime f (fun n => C * (n + 1))) : PolyTimeComputable f :=
+  polyTimeComputable_of_linear h
+
+/-- A fixed word is polynomial-time computable (`polyTimeComputable_const`). -/
+private lemma sat_pt_const (w : List Bool) : PolyTimeComputable (fun _ => w) :=
+  polyTimeComputable_const w
+
+/-- Polynomial-time branching on a polynomial-time bit (`polyTimeComputable_ite`). -/
+private lemma sat_pt_cond {p : List Bool → Bool} {f g : List Bool → List Bool}
+    (hp : PolyTimeComputable (fun x => [p x]))
+    (hf : PolyTimeComputable f) (hg : PolyTimeComputable g) :
+    PolyTimeComputable (fun x => if p x then f x else g x) :=
+  polyTimeComputable_ite hp hf hg
+
+/-- The conjunction of two polynomial-time bits is polynomial-time
+(`polyTimeComputable_and`). -/
+private lemma sat_pt_and {p q : List Bool → Bool}
+    (hp : PolyTimeComputable (fun x => [p x]))
+    (hq : PolyTimeComputable (fun x => [q x])) :
+    PolyTimeComputable (fun x => [p x && q x]) :=
+  polyTimeComputable_and hp hq
+
+/-- Composition of a function machine with a machine correct on its image
+(`FinTM.exists_comp_on_image`). -/
+private lemma sat_comp_on_image (M U : FinTM Bool) (f g : List Bool → List Bool)
+    (T₁ T₂ : ℕ → ℕ) (hM : M.ComputesFunInTime f T₁)
+    (hU : ∀ x, U.ComputesInTime (f x) (g x) (T₂ x.length)) :
+    ∃ N : FinTM Bool, N.ComputesFunInTime g (fun n => 2 * T₁ n + T₂ n + 2) :=
+  FinTM.exists_comp_on_image M U f g T₁ T₂ hM hU
+
 /-- **The language `SAT`** [AB09, §2.3.1]: binary strings whose decoded CNF
 formula is satisfiable. Decoding is total ([AB09, footnote 3]), with the empty —
 satisfiable — formula as fallback, so every non-well-formed string is in `SAT`
@@ -981,79 +1019,6 @@ private lemma satEval_computes : ∃ (E : FinTM Bool) (A : ℕ),
   simp only [Nat.add_mul]
   omega
 
-/-- Compose a computed request with a machine proved only on that request image.
-The budget is measured at the original input length, as in the audited TMSAT construction. -/
-private lemma sat_comp_on_image (M U : FinTM Bool) (f g : List Bool → List Bool)
-    (T₁ T₂ : ℕ → ℕ) (hM : M.ComputesFunInTime f T₁)
-    (hU : ∀ x, U.ComputesInTime (f x) (g x) (T₂ x.length)) :
-    ∃ N : FinTM Bool, N.ComputesFunInTime g (fun n => 2 * T₁ n + T₂ n + 2) := by
-  refine ⟨FinTM.bufferedCompTM M U, ?_⟩
-  intro x
-  obtain ⟨a, p, tapes, heads, ha, hstart⟩ :=
-    FinTM.bufferedComp_start M U x (f x) (T₁ x.length) (hM x)
-  have hlen : (f x).length ≤ T₁ x.length := by
-    have ho := ((FinTM.computesInTime_iff _ _ _ _).mp (hM x)).2
-    simpa only [ho] using M.tm.output_length_le x (T₁ x.length)
-  obtain ⟨b, _, hr⟩ := FinTM.bufferedSecondCfg_run M U (U.tm.initCfg (f x)) true
-    (by simp [FinTM.VirtualTag, MultiTapeTM.initCfg, Cfg.init]) p tapes heads (T₂ x.length)
-  have hu := (FinTM.computesInTime_iff _ _ _ _).mp (hU x)
-  have hbase : (FinTM.bufferedCompTM M U).ComputesInTime x (g x) (a + T₂ x.length) := by
-    apply (FinTM.computesInTime_iff _ _ _ _).mpr
-    rw [MultiTapeTM.runFrom_add, hstart, hr]
-    exact ⟨by simpa only [FinTM.bufferedSecondCfg, Option.map_eq_none_iff] using hu.1, hu.2⟩
-  exact hbase.mono (by dsimp only; omega)
-
-/-- Linear-time catalog contracts are instances of the polynomial calculus. -/
-private lemma sat_pt_linear (f : List Bool → List Bool)
-    (h : ∃ (M : FinTM Bool) (C : ℕ),
-      M.ComputesFunInTime f (fun n => C * (n + 1))) : PolyTimeComputable f := by
-  obtain ⟨M, C, hM⟩ := h
-  exact ⟨M, C, 1, by simpa only [Nat.pow_one] using hM⟩
-
-/-- A fixed word is emitted from finite control. -/
-private lemma sat_pt_const (w : List Bool) : PolyTimeComputable (fun _ => w) := by
-  exact sat_pt_linear _ (FinTM.computesFunInTime_const w)
-
-/-- Polynomial-time branches on the original input, using W3's captured
-single-bit decision. All three budgets fit their maximum degree.
-
-**Proof sketch.** Use the audited conditional constructor on the three witnessing machines. Bound each
-monomial by the common maximum exponent and absorb the constructor overhead into one
-coefficient. -/
-private lemma sat_pt_cond {p : List Bool → Bool} {f g : List Bool → List Bool}
-    (hp : PolyTimeComputable (fun x => [p x]))
-    (hf : PolyTimeComputable f) (hg : PolyTimeComputable g) :
-    PolyTimeComputable (fun x => if p x then f x else g x) := by
-  obtain ⟨P, A, a, hP⟩ := hp
-  obtain ⟨F, B, b, hF⟩ := hf
-  obtain ⟨G, C, c, hG⟩ := hg
-  obtain ⟨M, K, hM⟩ := FinTM.computesFunInTime_cond hP hF hG
-  let e := max a (max b c)
-  refine ⟨M, K * (A + B + C + 1), e, fun x => (hM x).mono ?_⟩
-  have ha := Nat.mul_le_mul_left A
-    (Nat.pow_le_pow_right (Nat.succ_pos x.length) (show a ≤ e by exact Nat.le_max_left _ _))
-  have hb := Nat.mul_le_mul_left B
-    (Nat.pow_le_pow_right (Nat.succ_pos x.length) (show b ≤ e by omega))
-  have hc := Nat.mul_le_mul_left C
-    (Nat.pow_le_pow_right (Nat.succ_pos x.length) (show c ≤ e by omega))
-  have h1 : 1 ≤ (x.length + 1) ^ e := Nat.one_le_pow _ _ (Nat.succ_pos _)
-  simp only [Nat.succ_eq_add_one] at ha hb hc
-  calc
-    _ ≤ K * ((A + B + C + 1) * (x.length + 1) ^ e) :=
-      Nat.mul_le_mul_left K (by simp only [Nat.add_mul, Nat.one_mul]; omega)
-    _ = _ := by ring
-
-
-/-- Short-circuit conjunction preserves the order of two polynomial tests. -/
-private lemma sat_pt_and {p q : List Bool → Bool}
-    (hp : PolyTimeComputable (fun x => [p x]))
-    (hq : PolyTimeComputable (fun x => [q x])) :
-    PolyTimeComputable (fun x => [p x && q x]) := by
-  have h := sat_pt_cond hp hq (sat_pt_const [false])
-  convert h using 1
-  funext x
-  cases p x <;> rfl
-
 /-- The catalog split emits an encoded pair, or an empty failure result. -/
 private def satSplit (z : List Bool) : List Bool :=
   match solveSplit 1 1 z.length with
@@ -1141,11 +1106,11 @@ private lemma sat_pipeline_poly :
   obtain ⟨M, A, hM⟩ := FinTM.computesFunInTime_splitSolve 1 1
   have hs : PolyTimeComputable satSplit := ⟨M, A, 3, hM⟩
   have hv : PolyTimeComputable (fun z => [satSplitValid z]) :=
-    (sat_pt_linear _ FinTM.computesFunInTime_pairValid).comp hs
+    (polyTimeComputable_of_linear FinTM.computesFunInTime_pairValid).comp hs
   have hx : PolyTimeComputable satInstance :=
-    (sat_pt_linear _ FinTM.computesFunInTime_pairFst).comp hs
+    (polyTimeComputable_of_linear FinTM.computesFunInTime_pairFst).comp hs
   have hp : PolyTimeComputable (fun z => [satSyntax (satInstance z)]) := satSyntax_poly.comp hx
-  exact ⟨hv, hx, hp, sat_pt_cond (sat_pt_and hv hp) hs (sat_pt_const _)⟩
+  exact ⟨hv, hx, hp, polyTimeComputable_ite (polyTimeComputable_and hv hp) hs (polyTimeComputable_const _)⟩
 
 /-- The evaluator is polynomial on all safe requests.
 
@@ -1164,7 +1129,7 @@ private lemma satSafeValue_poly : PolyTimeComputable (fun z => [satSafeValue z])
       have hout := ((FinTM.computesInTime_iff _ _ _ _).mp (hM z)).2
       simpa only [hout] using M.tm.output_length_le z (C * (z.length + 1) ^ e)
     exact h.mono (Nat.mul_le_mul_left A (by omega))
-  obtain ⟨N, hN⟩ := sat_comp_on_image M E satSafe (fun z => [satSafeValue z])
+  obtain ⟨N, hN⟩ := FinTM.exists_comp_on_image M E satSafe (fun z => [satSafeValue z])
     (fun n => C * (n + 1) ^ e) (fun n => A * (C * (n + 1) ^ e + 1)) hM heval
   refine ⟨N, 2 * C + A * (C + 1) + 2, e, fun z => (hN z).mono ?_⟩
   have hp : 1 ≤ (z.length + 1) ^ e := Nat.one_le_pow _ _ (Nat.succ_pos _)
@@ -1177,7 +1142,7 @@ private lemma satSafeValue_poly : PolyTimeComputable (fun z => [satSafeValue z])
 /-- The SAT verifier rejects failed splits and otherwise uses the safe
 evaluation pipeline. Failed parses take its accepting fallback branch. -/
 private lemma satVerdict_false_poly : PolyTimeComputable (fun z => [satVerdict false z]) := by
-  have h := sat_pt_cond sat_pipeline_poly.1 satSafeValue_poly (sat_pt_const [false])
+  have h := polyTimeComputable_ite sat_pipeline_poly.1 satSafeValue_poly (polyTimeComputable_const [false])
   convert h using 1
   funext z
   cases hs : solveSplit 1 1 z.length with
@@ -1317,9 +1282,9 @@ only successfully parsed inputs reach the width scan. -/
 private lemma satVerdict_true_poly : PolyTimeComputable (fun z => [satVerdict true z]) := by
   have hw : PolyTimeComputable (fun z => [satWidthScan (satInstance z)]) :=
     satWidthScan_poly.comp sat_pipeline_poly.2.1
-  have hsem := sat_pt_and hw satSafeValue_poly
-  have hparse := sat_pt_cond sat_pipeline_poly.2.2.1 hsem (sat_pt_const [true])
-  have h := sat_pt_cond sat_pipeline_poly.1 hparse (sat_pt_const [false])
+  have hsem := polyTimeComputable_and hw satSafeValue_poly
+  have hparse := polyTimeComputable_ite sat_pipeline_poly.2.2.1 hsem (polyTimeComputable_const [true])
+  have h := polyTimeComputable_ite sat_pipeline_poly.1 hparse (polyTimeComputable_const [false])
   convert h using 1
   funext z
   cases hs : solveSplit 1 1 z.length with
```

## TCSlib/Complexity/ClassNP/EXP.lean

- before blob (git SHA-1): `ccf0254ac26c7edb12ab11eef6c1fb69b7c57ebd`
- after blob (git SHA-1): `fb8ee4382039df80004916680f0c78bc2dc3c65c` (= HEAD)

```diff
diff --git a/TCSlib/Complexity/ClassNP/EXP.lean b/TCSlib/Complexity/ClassNP/EXP.lean
index ccf0254a..fb8ee438 100644
--- a/TCSlib/Complexity/ClassNP/EXP.lean
+++ b/TCSlib/Complexity/ClassNP/EXP.lean
@@ -58,7 +58,7 @@ declarations in all — was removed under the epoch-2 gate's binding
 live/dead inventory (`audits/ch2-epoch2-resolutions.md`): the
 continuation's `exists_loopCfgTM` route replaced it, and the auditor's
 kernel walk confirmed it absent from every final target closure. The
-live checkpoint route `enumLoop_run` (consumed by `enumDecider`) is
+live checkpoint route `enumLoop_run` (consumed by `exists_proj_decider`) is
 retained unchanged.
 -/
 
@@ -117,8 +117,9 @@ private def enumInc : List Bool → Option (List Bool)
   | false :: bs => some (true :: bs)
   | true :: bs => (enumInc bs).map (false :: ·)
 
-/-- A width-`w` little-endian representation of the low `w` bits of `i`. -/
-private def enumWord : ℕ → ℕ → List Bool
+/-- **The width-`w` little-endian binary word** of `i`: its low `w` bits, least
+significant first (high zeros kept). -/
+def enumWord : ℕ → ℕ → List Bool
   | 0, _ => []
   | w + 1, i => decide (i % 2 = 1) :: enumWord w (i / 2)
 
@@ -1263,9 +1264,9 @@ private lemma enumCont_round_seam (MV : FinTM Bool) (x s : List Bool) (phase : B
 /-- The prepared verifier call accepts the exact assembled input `x ++ s`.
 Its bound includes assembly, the buffer rewind, and the verifier's actual
 polynomial budget on that input. -/
-private lemma enumCont_verifier_call (MV : FinTM Bool) (V : Language Bool) (a d : ℕ)
-    (hV : MV.DecidesInTime V (fun n => a * (n + 1) ^ d)) (x s : List Bool) :
-    ∃ t ≤ a * (x.length + s.length + 1) ^ d + 2 * (x.length + s.length) + 4,
+private lemma enumCont_verifier_call (MV : FinTM Bool) (V : Language Bool) (Tv : ℕ → ℕ)
+    (hV : MV.DecidesInTime V Tv) (x s : List Bool) :
+    ∃ t ≤ Tv (x.length + s.length) + 2 * (x.length + s.length) + 4,
       ((bufferedCompTM enumCont_concatTM MV).tm.runFrom
         (Cfg.ofWords (input := x) (bufferedCompTM enumCont_concatTM MV).tm.q₀
           (stateWord (bufferedCompTM enumCont_concatTM MV).k s)) t).state = none ∧
@@ -1276,7 +1277,7 @@ private lemma enumCont_verifier_call (MV : FinTM Bool) (V : Language Bool) (a d
   obtain ⟨t, ht, hh, ho⟩ := enumCont_prepared_comp enumCont_concatTM MV
     (Cfg.ofWords (input := x) false (fun _ => s)) (x ++ s)
     [MultiTapeTM.indicator V (x ++ s)] (x.length + s.length + 2)
-    (a * ((x ++ s).length + 1) ^ d)
+    (Tv (x ++ s).length)
     (by rw [enumCont_concat_run]; rfl) (by rw [enumCont_concat_run]; rfl) (hV (x ++ s))
   rw [enumCont_round_seam MV x s false] at hh ho
   simp only [List.length_append] at ht
@@ -1325,17 +1326,17 @@ private lemma enumCont_return_run {k : ℕ} {S H : Type} {x : List Bool}
 repeatable call: the candidate is retained, all other original source work
 is restored to blank, and the sole verdict is held on the capture tape.
 The concrete body still has to dispatch, clear that verdict, and increment. -/
-private lemma enumCont_clean_verifier (MV : FinTM Bool) (V : Language Bool) (a d : ℕ)
-    (hV : MV.DecidesInTime V (fun n => a * (n + 1) ^ d)) (x s : List Bool) :
+private lemma enumCont_clean_verifier (MV : FinTM Bool) (V : Language Bool) (Tv : ℕ → ℕ)
+    (hV : MV.DecidesInTime V Tv) (x s : List Bool) :
     let Q := bufferedCompTM enumCont_concatTM MV
     let c₀ := Cfg.ofWords (input := x) Q.tm.q₀ (stateWord Q.k s)
-    ∃ t ≤ 3 * (a * (x.length + s.length + 1) ^ d + 2 * (x.length + s.length) + 4) +
+    ∃ t ≤ 3 * (Tv (x.length + s.length) + 2 * (x.length + s.length) + 4) +
         x.length + 9,
       (enumCont_cleanTM Q).tm.runFrom
         (captureCfg Sum.inl (.inr (.inl 0)) [] [] (enumCont_logCfg c₀ [])) t =
         enumCont_cleanCfg Q c₀ [MultiTapeTM.indicator V (x ++ s)] none 1 0 := by
   dsimp only
-  obtain ⟨t, ht, hh, ho⟩ := enumCont_verifier_call MV V a d hV x s
+  obtain ⟨t, ht, hh, ho⟩ := enumCont_verifier_call MV V Tv hV x s
   obtain ⟨r, hr, he⟩ := enumCont_clean_complete (bufferedCompTM enumCont_concatTM MV)
     (Cfg.ofWords (input := x) (bufferedCompTM enumCont_concatTM MV).tm.q₀
       (stateWord (bufferedCompTM enumCont_concatTM MV).k s))
@@ -2222,31 +2223,6 @@ private lemma enumCont_lift_init (M B : FinTM Bool) (hk : M.k ≤ B.k)
   rw [hh]
   rfl
 
-/-- One input-independent polynomial bounds both body phases. The degree
-dominates the verifier degree, unary-generator degree, and linear scans;
-the coefficient absorbs every fixed administrative transition. -/
-private lemma enumCont_common_bound (a d f c j n w : ℕ) :
-    let P := (n + w + 1) ^ (d + c + 2)
-    let A := 3 * a + 3 * f + 3 * j + 60
-    3 * (f * (n + 1) ^ (c + 1)) + n + 3 * w + 10 ≤ A * P ∧
-      3 * (a * (n + w + 1) ^ d + 2 * (n + w) + 4) +
-        3 * ((j + 3) * (w + 1)) + 2 * n + 3 * w + 22 ≤ A * P := by
-  dsimp only
-  let P := (n + w + 1) ^ (d + c + 2)
-  have hn : n + w + 1 ≤ P := by
-    calc n + w + 1 = (n + w + 1) ^ 1 := by simp
-      _ ≤ P := Nat.pow_le_pow_right (by omega) (by omega)
-  have hd : (n + w + 1) ^ d ≤ P := Nat.pow_le_pow_right (by omega) (by omega)
-  have hf : (n + 1) ^ (c + 1) ≤ P :=
-    (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) (by omega))
-  have ha' := Nat.mul_le_mul_left a hd
-  have hf' := Nat.mul_le_mul_left f hf
-  have hj' := Nat.mul_le_mul_left (j + 3) (show w + 1 ≤ P by omega)
-  change _ ≤ (3 * a + 3 * f + 3 * j + 60) * P ∧
-    _ ≤ (3 * a + 3 * f + 3 * j + 60) * P
-  simp only [Nat.add_mul, Nat.mul_assoc] at hj' ⊢
-  omega
-
 /-- A concrete body with polynomial startup and exact seam restoration gives
 the frozen enumerator configuration contract by the audited loop export.
 This lemma is conditional only on the two explicit body obligations below.
@@ -2256,15 +2232,15 @@ the common coefficient and degree to cover both fuel and body. Instantiate
 The terminal is `(2^w-1)+1=2^w`; on candidate indices use `enumCont_orbit`.
 Finally absorb the export's additive one using `1 ≤ (n+w+1)^D`, exactly as
 in infrastructure round 3, item 5. All constants are fixed before the input. -/
-private lemma enumCont_from_body (C c A D : ℕ) (V : Language Bool)
+private lemma enumCont_from_body (C c : ℕ) (G : ℕ → ℕ) (V : Language Bool)
     (body : FinTM Bool) (anchor : body.State)
     (hstart : ∀ x : List Bool,
-      ∃ t ≤ A * (x.length + C * (x.length + 1) ^ c + 1) ^ D,
+      ∃ t ≤ G x.length,
         (∀ t' < t, (body.tm.runFrom (body.tm.initCfg x) t').state ≠ some anchor) ∧
         body.tm.runFrom (body.tm.initCfg x) t =
           Cfg.ofWords anchor (stateWord body.k (List.replicate (C * (x.length + 1) ^ c) false)))
     (hround : ∀ (x s : List Bool), s.length = C * (x.length + 1) ^ c →
-      ∃ t, 0 < t ∧ t ≤ A * (x.length + C * (x.length + 1) ^ c + 1) ^ D ∧
+      ∃ t, 0 < t ∧ t ≤ G x.length ∧
         (∀ t', 0 < t' → t' < t →
           (body.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t').state
             ≠ some anchor) ∧
@@ -2274,32 +2250,28 @@ private lemma enumCont_from_body (C c A D : ℕ) (V : Language Bool)
         else
           body.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t =
             Cfg.ofWords anchor (stateWord body.k ((incFixed s).getD s))) :
-    ∃ (b e : ℕ) (E : FinTM Bool), ∀ x : List Bool,
+    ∃ (b : ℕ) (E : FinTM Bool), ∀ x : List Bool,
       ∃ (cfg : ℕ → Cfg E.k Bool E.State x) (startup : ℕ),
-        startup ≤ b * (x.length + C * (x.length + 1) ^ c + 1) ^ e ∧
+        startup ≤ b * (G x.length + (x.length + 1) ^ (c + 1) + 1) ∧
         E.tm.runFrom (E.tm.initCfg x) startup = cfg 0 ∧
         (cfg (2 ^ (C * (x.length + 1) ^ c))).state = none ∧
         (cfg (2 ^ (C * (x.length + 1) ^ c))).output = [false] ∧
         ∀ i, i < 2 ^ (C * (x.length + 1) ^ c) → ∃ t,
-          t ≤ b * (x.length + C * (x.length + 1) ^ c + 1) ^ e ∧
+          t ≤ b * (G x.length + (x.length + 1) ^ (c + 1) + 1) ∧
           if MultiTapeTM.indicator V (x ++ enumWord (C * (x.length + 1) ^ c) i) then
             (E.tm.runFrom (cfg i) t).state = none ∧
               (E.tm.runFrom (cfg i) t).output = [true]
           else E.tm.runFrom (cfg i) t = cfg (i + 1) := by
   obtain ⟨F, f, hF⟩ := computesFunInTime_polyUnary C c
-  let T := fun n => (A + f) * (n + C * (n + 1) ^ c + 1) ^ (D + c + 1)
-  have hbody (n : ℕ) : A * (n + C * (n + 1) ^ c + 1) ^ D ≤ T n := by
-    exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
+  let T := fun n => G n + f * (n + 1) ^ (c + 1)
+  have hbody (n : ℕ) : G n ≤ T n := Nat.le_add_right _ _
   have hfuel : F.ComputesFunInTime
       (fun x => Nat.bits (2 ^ (C * (x.length + 1) ^ c) - 1)) T := by
     intro x
     dsimp only
     rw [enumCont_fuel_bits]
     apply (hF x).mono
-    exact Nat.mul_le_mul (by omega)
-      ((Nat.pow_le_pow_left (by omega : x.length + 1 ≤
-        x.length + C * (x.length + 1) ^ c + 1) (c + 1)).trans
-        (Nat.pow_le_pow_right (by omega) (by omega)))
+    exact Nat.le_add_left _ _
   obtain ⟨E, K, hE⟩ := exists_loopCfgTM body F anchor
     (fun x s => s.length = C * (x.length + 1) ^ c)
     (fun _ s => (incFixed s).getD s)
@@ -2316,51 +2288,50 @@ private lemma enumCont_from_body (C c A D : ℕ) (V : Language Bool)
       intro x s hs
       obtain ⟨t, htpos, ht, hi, hh⟩ := hround x s hs
       exact ⟨t, htpos, ht.trans (hbody x.length), hi, hh⟩)
-  refine ⟨K * (A + f + 1), D + c + 1, E, fun x => ?_⟩
+  refine ⟨K * (f + 1), E, fun x => ?_⟩
   obtain ⟨cfg, startup, ht, hi, _, hend, hout, hr⟩ := hE x
   have hone : 1 ≤ 2 ^ (C * (x.length + 1) ^ c) := Nat.one_le_two_pow
   have hterminal : 2 ^ (C * (x.length + 1) ^ c) - 1 + 1 =
       2 ^ (C * (x.length + 1) ^ c) := Nat.sub_add_cancel hone
   rw [hterminal] at hend hout
-  have hbudget : K * (T x.length + 1) ≤ K * (A + f + 1) *
-      (x.length + C * (x.length + 1) ^ c + 1) ^ (D + c + 1) := by
-    have hp : 1 ≤ (x.length + C * (x.length + 1) ^ c + 1) ^ (D + c + 1) :=
-      Nat.one_le_pow _ _ (by omega)
-    calc K * (T x.length + 1) ≤ K * (T x.length +
-        (x.length + C * (x.length + 1) ^ c + 1) ^ (D + c + 1)) :=
-          Nat.mul_le_mul_left K (Nat.add_le_add_left hp _)
-      _ = _ := by dsimp [T]; ring
+  have hbudget : K * (T x.length + 1) ≤ K * (f + 1) *
+      (G x.length + (x.length + 1) ^ (c + 1) + 1) := by
+    rw [Nat.mul_assoc]
+    apply Nat.mul_le_mul_left K
+    dsimp only [T]
+    have e : (f + 1) * (G x.length + (x.length + 1) ^ (c + 1) + 1) =
+        f * G x.length + f * (x.length + 1) ^ (c + 1) + f + G x.length +
+          (x.length + 1) ^ (c + 1) + 1 := by ring
+    rw [e]
+    omega
   refine ⟨cfg, startup, ht.trans hbudget, hi, hend, hout, ?_⟩
   intro i hi
   obtain ⟨t, ht, hh⟩ := hr i (by omega)
   rw [enumCont_orbit _ i hi] at hh
   exact ⟨t, ht.trans hbudget, hh⟩
 
-/-- **Continuation frontier; admitted in this partial delivery.** There is one
-uniform finite machine with a polynomial startup and a polynomially bounded
-accept-or-advance segment for each exact-width candidate. The configuration
-after the last rejected candidate is a halted singleton rejection.
-
-**Proof sketch / remaining construction.** Evaluate `C(n+1)^c` and construct
-the all-false candidate while retaining the instance; assemble `x ++ u` on
-the virtual input buffer. Use `enumCapture_returns` for the captured call.
-On rejection, clear the bounded visited work region, reset all source and
-buffer heads and the captured bit, and use `enumCarry_correct` to increment.
-Its `enumBump_inc`/`enumInc_word` specification supplies the next rank or the
-overflow signal. Emit the single final answer only on acceptance or overflow.
-Prove the startup and per-round configuration equalities below with a uniform
-polynomial budget. These machine assembly and reset obligations are NOT
-discharged by the counter, capture, and abstract loop lemmas alone. -/
-private theorem enumMachine_contracts (C c a d : ℕ) (V : Language Bool)
-    (MV : FinTM Bool) (hV : MV.DecidesInTime V (fun n => a * (n + 1) ^ d)) :
-    ∃ (b e : ℕ) (E : FinTM Bool), ∀ x : List Bool,
+/-- **The enumerator's configuration contract** (generalized verifier budget): one
+uniform finite machine, from its initial configuration, reaches the round of the first
+candidate within `b (Tv(n + w) + (n + w + 1)^{c+1})` steps (`w = C(n+1)^c`); each round
+either accepts (when `x ++ u ∈ V`) or advances to the next candidate within the same
+budget; after the last candidate it halts rejecting.
+
+**Proof sketch.** Instantiate `enumCont_from_body` with the body of the original
+construction (unary width generator, captured verifier call on `x ++ u`, reversible
+cleanup, fixed-width increment), bounding its startup and round costs by
+`A (n + w + 1)^{c+1} + 3 Tv(n + w)`. -/
+private theorem enumMachine_contracts (C c : ℕ) (V : Language Bool) (Tv : ℕ → ℕ)
+    (MV : FinTM Bool) (hV : MV.DecidesInTime V Tv) :
+    ∃ (b : ℕ) (E : FinTM Bool), ∀ x : List Bool,
       ∃ (cfg : ℕ → Cfg E.k Bool E.State x) (startup : ℕ),
-        startup ≤ b * (x.length + C * (x.length + 1) ^ c + 1) ^ e ∧
+        startup ≤ b * (Tv (x.length + C * (x.length + 1) ^ c) +
+          (x.length + C * (x.length + 1) ^ c + 1) ^ (c + 1)) ∧
         E.tm.runFrom (E.tm.initCfg x) startup = cfg 0 ∧
         (cfg (2 ^ (C * (x.length + 1) ^ c))).state = none ∧
         (cfg (2 ^ (C * (x.length + 1) ^ c))).output = [false] ∧
         ∀ i, i < 2 ^ (C * (x.length + 1) ^ c) → ∃ t,
-          t ≤ b * (x.length + C * (x.length + 1) ^ c + 1) ^ e ∧
+          t ≤ b * (Tv (x.length + C * (x.length + 1) ^ c) +
+            (x.length + C * (x.length + 1) ^ c + 1) ^ (c + 1)) ∧
           if MultiTapeTM.indicator V (x ++ enumWord (C * (x.length + 1) ^ c) i) then
             (E.tm.runFrom (cfg i) t).state = none ∧
               (E.tm.runFrom (cfg i) t).output = [true]
@@ -2378,32 +2349,73 @@ private theorem enumMachine_contracts (C c a d : ℕ) (V : Language Bool)
   have hRB : R.k ≤ B.k := by dsimp [B, enumCont_sources]; omega
   have hUB : U.k ≤ B.k := by dsimp [B, enumCont_sources]; omega
   have hB : 0 < B.k := lt_of_lt_of_le hQ hQB
-  apply enumCont_from_body C c (3 * a + 3 * f + 3 * j + 60) (d + c + 2) V
-    (enumCont_bodyTM B qv qi false) (.inr 0)
-  · intro x
-    have hu := enumCont_lift_init U B hUB (fun q => .inr (.inr q))
-      (by intro q inp work; rfl) x (List.replicate (C * (x.length + 1) ^ c) true)
-      (f * (x.length + 1) ^ (c + 1)) (hU x)
-    obtain ⟨t, ht, hn, he⟩ := enumCont_body_start_guarded B hB qv qi x
-      (C * (x.length + 1) ^ c) (f * (x.length + 1) ^ (c + 1)) hu.1 hu.2
-    exact ⟨t, ht.trans (enumCont_common_bound a d f c j x.length
-      (C * (x.length + 1) ^ c)).1, hn, he⟩
-  · intro x s hs
-    obtain ⟨tv, htv, hhv, hov⟩ := enumCont_verifier_call MV V a d hV x s
-    obtain ⟨ti, hti, hhi, hoi⟩ := enumCont_increment_call I j hI x s
-    have hv := enumCont_lift_call Q B hQ hQB Sum.inl
-      (by intro q inp work; rfl) Q.tm.q₀ x s [MultiTapeTM.indicator V (x ++ s)] tv hhv hov
-    have hi := enumCont_lift_call R B hR hRB (fun q => .inr (.inl q))
-      (by intro q inp work; rfl) (.inl (some true)) x s ((incFixed s).getD []) ti hhi hoi
-    obtain ⟨t, htpos, ht, hn, he⟩ := enumCont_body_round_guarded B hB qv qi x s
-      (MultiTapeTM.indicator V (x ++ s)) tv ti hv hi
-    refine ⟨t, htpos, ?_, hn, he⟩
-    have hb := (enumCont_common_bound a d f c j x.length s.length).2
-    rw [hs] at hb
-    apply le_trans (show t ≤ 3 * (a * (x.length + s.length + 1) ^ d +
-      2 * (x.length + s.length) + 4) + 3 * ((j + 3) * (s.length + 1)) +
-      2 * x.length + 3 * s.length + 22 by omega)
-    simpa only [hs] using hb
+  let A := 3 * f + 3 * j + 60
+  let P := fun n => (n + C * (n + 1) ^ c + 1) ^ (c + 1)
+  let G := fun n => A * P n + 3 * Tv (n + C * (n + 1) ^ c)
+  have hP1 : ∀ n, n + C * (n + 1) ^ c + 1 ≤ P n := by
+    intro n
+    calc n + C * (n + 1) ^ c + 1 = (n + C * (n + 1) ^ c + 1) ^ 1 := (pow_one _).symm
+      _ ≤ P n := Nat.pow_le_pow_right (by omega) (by omega)
+  have hP2 : ∀ n, (n + 1) ^ (c + 1) ≤ P n := fun n => Nat.pow_le_pow_left (by omega) _
+  obtain ⟨b, E, hE⟩ := enumCont_from_body C c G V (enumCont_bodyTM B qv qi false) (.inr 0)
+    (by
+      intro x
+      have hu := enumCont_lift_init U B hUB (fun q => .inr (.inr q))
+        (by intro q inp work; rfl) x (List.replicate (C * (x.length + 1) ^ c) true)
+        (f * (x.length + 1) ^ (c + 1)) (hU x)
+      obtain ⟨t, ht, hn, he⟩ := enumCont_body_start_guarded B hB qv qi x
+        (C * (x.length + 1) ^ c) (f * (x.length + 1) ^ (c + 1)) hu.1 hu.2
+      refine ⟨t, ht.trans ?_, hn, he⟩
+      have h1 := hP1 x.length
+      have h2 := Nat.mul_le_mul_left f (hP2 x.length)
+      have e : (3 * f + 3 * j + 60) * P x.length =
+          3 * (f * P x.length) + 3 * (j * P x.length) + 60 * P x.length := by ring
+      show _ ≤ (3 * f + 3 * j + 60) * P x.length + 3 * Tv (x.length + C * (x.length + 1) ^ c)
+      rw [e]
+      have : 0 ≤ j * P x.length := Nat.zero_le _
+      omega)
+    (by
+      intro x s hs
+      obtain ⟨tv, htv, hhv, hov⟩ := enumCont_verifier_call MV V Tv hV x s
+      obtain ⟨ti, hti, hhi, hoi⟩ := enumCont_increment_call I j hI x s
+      have hv := enumCont_lift_call Q B hQ hQB Sum.inl
+        (by intro q inp work; rfl) Q.tm.q₀ x s [MultiTapeTM.indicator V (x ++ s)] tv hhv hov
+      have hi := enumCont_lift_call R B hR hRB (fun q => .inr (.inl q))
+        (by intro q inp work; rfl) (.inl (some true)) x s ((incFixed s).getD []) ti hhi hoi
+      obtain ⟨t, htpos, ht, hn, he⟩ := enumCont_body_round_guarded B hB qv qi x s
+        (MultiTapeTM.indicator V (x ++ s)) tv ti hv hi
+      refine ⟨t, htpos, ?_, hn, he⟩
+      have h1 := hP1 x.length
+      have h3 : (j + 3) * (s.length + 1) ≤ (j + 3) * P x.length :=
+        Nat.mul_le_mul_left _ (by rw [hs]; omega)
+      have ht' : t ≤ 3 * (Tv (x.length + s.length) + 2 * (x.length + s.length) + 4) +
+          3 * ((j + 3) * (s.length + 1)) + 2 * x.length + 3 * s.length + 22 := by omega
+      rw [hs] at ht' h3
+      have e : (3 * f + 3 * j + 60) * P x.length =
+          3 * (f * P x.length) + 3 * ((j + 3) * P x.length) + 51 * P x.length := by ring
+      show _ ≤ (3 * f + 3 * j + 60) * P x.length + 3 * Tv (x.length + C * (x.length + 1) ^ c)
+      rw [e]
+      have : 0 ≤ f * P x.length := Nat.zero_le _
+      omega)
+  refine ⟨b * (A + 3), E, fun x => ?_⟩
+  obtain ⟨cfg, startup, hst, hi, hend, hout, hr⟩ := hE x
+  have hbound : b * (G x.length + (x.length + 1) ^ (c + 1) + 1) ≤
+      b * (A + 3) * (Tv (x.length + C * (x.length + 1) ^ c) + P x.length) := by
+    rw [Nat.mul_assoc]
+    apply Nat.mul_le_mul_left b
+    have h1 := hP1 x.length
+    have h2 := hP2 x.length
+    show (A * P x.length + 3 * Tv (x.length + C * (x.length + 1) ^ c)) +
+      (x.length + 1) ^ (c + 1) + 1 ≤ (A + 3) * (Tv (x.length + C * (x.length + 1) ^ c) + P x.length)
+    have e : (A + 3) * (Tv (x.length + C * (x.length + 1) ^ c) + P x.length) =
+        A * Tv (x.length + C * (x.length + 1) ^ c) + 3 * Tv (x.length + C * (x.length + 1) ^ c) +
+          A * P x.length + 3 * P x.length := by ring
+    rw [e]
+    have : 0 ≤ A * Tv (x.length + C * (x.length + 1) ^ c) := Nat.zero_le _
+    omega
+  refine ⟨cfg, startup, hst.trans hbound, hi, hend, hout, fun i hi' => ?_⟩
+  obtain ⟨t, ht, hh⟩ := hr i hi'
+  exact ⟨t, ht.trans hbound, hh⟩
 
 /-! **Continuation completion note (batch E2-cont A).** The historical
 partial-fill descriptions above and below are retained under the statement
@@ -2415,24 +2427,28 @@ in-place candidate replacement, and positive first-return round contracts.
 catalog-generated `2^w-1` fuel, bounded rank orbit, terminal `2^w`, and
 uniform startup/round budgets. -/
 
-/-- Assuming the single machine-construction frontier, the proved loop
-invariant gives a decider with the audited exponential-times-polynomial
-budget. This lemma inherits exactly that pending admission.
-**Proof sketch.** Start the loop after initialization, apply `enumLoop_run`
-for all `2^width` candidates, and identify its Boolean answer using exact
-candidate coverage. Since `2^width ≥ 1`, startup is absorbed by doubling the
-coefficient. The final computation has exactly one output bit. -/
-private theorem enumDecider (C c a d : ℕ) (V : Language Bool)
-    (MV : FinTM Bool) (hV : MV.DecidesInTime V (fun n => a * (n + 1) ^ d)) :
-    ∃ (b e : ℕ) (E : FinTM Bool),
+/-- **Brute-force enumeration with an arbitrary-time verifier** [AB09, Claim 2.4, the
+enumeration argument]: if `MV` decides `V` within `Tv`, then some machine decides the
+existential projection `{x | ∃ u, |u| = C(|x|+1)^c ∧ x ++ u ∈ V}` within
+`b · 2^{C(n+1)^c} · (Tv(n + C(n+1)^c) + (n + C(n+1)^c + 1)^{c+1})`.
+
+**Proof sketch.** The loop combinator runs one round per candidate `u` of width
+`w = C(n+1)^c` (in fixed-width binary, starting from `0^w`); each round calls `MV` on
+the assembled input `x ++ u` (at most `Tv(n + w)` steps plus polynomial overhead),
+captures the verdict, restores the scratch tapes from a reversible log, and either halts
+accepting or increments `u`; after `2^w` rejecting rounds it halts rejecting. -/
+theorem exists_proj_decider (C c : ℕ) (V : Language Bool) (Tv : ℕ → ℕ)
+    (MV : FinTM Bool) (hV : MV.DecidesInTime V Tv) :
+    ∃ (b : ℕ) (E : FinTM Bool),
       E.DecidesInTime {x | ∃ u, u.length = C * (x.length + 1) ^ c ∧ x ++ u ∈ V}
-        (fun n => b * 2 ^ (C * (n + 1) ^ c) * (n + C * (n + 1) ^ c + 1) ^ e) := by
+        (fun n => b * 2 ^ (C * (n + 1) ^ c) *
+          (Tv (n + C * (n + 1) ^ c) + (n + C * (n + 1) ^ c + 1) ^ (c + 1))) := by
   classical
-  obtain ⟨b, e, E, hE⟩ := enumMachine_contracts C c a d V MV hV
-  refine ⟨2 * b, e, E, fun x => ?_⟩
+  obtain ⟨b, E, hE⟩ := enumMachine_contracts C c V Tv MV hV
+  refine ⟨2 * b, E, fun x => ?_⟩
   obtain ⟨cfg, startup, hstartup, hinit, hend, hout, hround⟩ := hE x
   let w := C * (x.length + 1) ^ c
-  let B := b * (x.length + w + 1) ^ e
+  let B := b * (Tv (x.length + w) + (x.length + w + 1) ^ (c + 1))
   let accept := fun i => MultiTapeTM.indicator V (x ++ enumWord w i)
   obtain ⟨t, ht, hh, ho⟩ := enumLoop_run E x cfg accept B 0 (2 ^ w)
     (by simpa only [Nat.zero_add] using And.intro hend hout)
@@ -2465,54 +2481,54 @@ private theorem enumDecider (C c a d : ℕ) (V : Language Bool)
   calc startup + t ≤ B + 2 ^ w * B := Nat.add_le_add hstartup ht
        _ ≤ 2 ^ w * B + 2 ^ w * B := Nat.add_le_add_right hB _
        _ = 2 * b * 2 ^ (C * (x.length + 1) ^ c) *
-           (x.length + C * (x.length + 1) ^ c + 1) ^ e := by dsimp [B, w]; ring
+           (Tv (x.length + C * (x.length + 1) ^ c) +
+             (x.length + C * (x.length + 1) ^ c + 1) ^ (c + 1)) := by dsimp [B, w]; ring
+
 
 /-- **`NP ⊆ EXP`** [AB09, Claim 2.4]: brute-force certificate enumeration.
 
 **Proof sketch.** Let `L ∈ NP` with certificate length exactly `Q n = C(n+1)^c`
 and verifier `V ∈ P` decided by machine `MV`. The deciding machine, on input
-`x` of length `n`: evaluate the explicit formula `Q n` (a polynomial-evaluation
-machine — a **new obligation**; the explicit formula is what makes the width
-computable at all, phase-1 audit finding 1 and question 4) and lay out a
-width-`Q n` all-`false` candidate certificate; in each round, assemble
-`x ++ u` on a buffer, run `MV`, accept if it accepts, else increment the
-candidate as a **fixed-width** counter and repeat, rejecting on width overflow
-after the `2^(Q n)`-th round. Enumeration is over certificates of exactly the
-definition's length — no majorant mismatch (audit question 4). The remaining
-machine obligations, named for the fill per phase-1 finding 5 and round-2
-finding 2: fixed-width increment with overflow detection (the private
-`counterInc` layer of `ClassP/TimeConstructible.lean` extends on overflow and
-is a template, not a citable API — promotion or private re-derivation is a
-fill-time decision); retention of `x` and the candidate across rounds;
-**a verifier-call simulation that captures `MV`'s decision bit in finite
-control, suppresses its physical emissions, and redirects its halt to the
-loop controller** — the output tape is append-only, so forwarding per-round
-emissions would accumulate (`[false, true]` across two rounds) and violate
-`DecidesInTime`'s singleton contract; the real output stays empty until the
-final answer (the capture-wrapper pattern of `Turing.universalCaptureTM` is
-the in-repo precedent); reset of `MV`'s simulated state, heads, work region,
-and the captured bit between rounds (a bounded region — each head moves at
-most one cell per step); and a timed loop invariant covering all of the above
-(the untimed `exists_cond` does not supply one; at `C = 0` the single round on
-the empty certificate still executes). Budget: at most `2^(Q n)` rounds of cost polynomial in
-`n + Q n + 1`, i.e. `a · 2^(Q n) (n + Q n + 1)^d ≤ 2^(n^e)` for a fixed degree
-`e`, small lengths absorbed into `DTIME`'s constant (the audit's own estimate):
-`L ∈ EXP`.
-+
-+**Partial-fill appendix.** The fixed-width carry, buffered captured-call
-+simulation, abstract timed-loop invariant, and final budget normalization
-+are proved below the class definitions. The machine's initialization,
-+reset, and controller assembly remain the single private admission
-+`enumMachine_contracts`; the present theorem still depends on `sorryAx`. -/
+`x` of length `n`: evaluate the explicit formula `Q n` (the explicit formula is
+what makes the width computable at all, phase-1 audit finding 1 and question 4)
+and lay out a width-`Q n` all-`false` candidate certificate; in each round,
+assemble `x ++ u` on a buffer, run `MV`, accept if it accepts, else increment
+the candidate as a **fixed-width** counter and repeat, rejecting on width
+overflow after the `2^(Q n)`-th round. Enumeration is over certificates of
+exactly the definition's length — no majorant mismatch (audit question 4). The
+verifier call is simulated with its decision bit captured in finite control, its
+physical emissions suppressed and its halt redirected to the loop controller, so
+the real output stays empty until the final answer (the output tape is
+append-only); `MV`'s simulated state, heads, work region and the captured bit are
+reset between rounds. This is the enumerator `Complexity.exists_proj_decider`
+(the fixed-width carry, buffered captured call, timed loop invariant and budget
+normalization are proved above), instantiated at `Tv = a (n+1)^d`. Budget: at
+most `2^(Q n)` rounds of cost polynomial in `n + Q n + 1`, i.e.
+`a · 2^(Q n) (n + Q n + 1)^d ≤ 2^(n^e)` for a fixed degree `e`, small lengths
+absorbed into `DTIME`'s constant: `L ∈ EXP`. -/
 theorem NP_subset_EXP : NP ⊆ EXP := by
   rintro L ⟨C, c, V, hV, hL⟩
   obtain ⟨a, d, MV, hMV⟩ := mem_P_iff.mp hV
-  obtain ⟨b, e, E, hE⟩ := enumDecider C c a d V MV hMV
-  obtain ⟨A, f, hbound⟩ := enumBudget_bound b C c e
+  obtain ⟨b, E, hE⟩ := exists_proj_decider C c V (fun n => a * (n + 1) ^ d) MV hMV
+  obtain ⟨A, f, hbound⟩ := enumBudget_bound (b * (a + 1)) C c (d + c + 1)
+  have hpoly : ∀ n : ℕ, b * 2 ^ (C * (n + 1) ^ c) *
+      (a * (n + C * (n + 1) ^ c + 1) ^ d + (n + C * (n + 1) ^ c + 1) ^ (c + 1)) ≤
+      b * (a + 1) * 2 ^ (C * (n + 1) ^ c) * (n + C * (n + 1) ^ c + 1) ^ (d + c + 1) := by
+    intro n
+    set X := n + C * (n + 1) ^ c + 1
+    have h1 : X ^ d ≤ X ^ (d + c + 1) := Nat.pow_le_pow_right (by omega) (by omega)
+    have h2 : X ^ (c + 1) ≤ X ^ (d + c + 1) := Nat.pow_le_pow_right (by omega) (by omega)
+    have h3 : a * X ^ d + X ^ (c + 1) ≤ (a + 1) * X ^ (d + c + 1) := by
+      have := Nat.mul_le_mul_left a h1
+      rw [Nat.add_mul, one_mul]; omega
+    calc b * 2 ^ (C * (n + 1) ^ c) * (a * X ^ d + X ^ (c + 1)) ≤
+        b * 2 ^ (C * (n + 1) ^ c) * ((a + 1) * X ^ (d + c + 1)) := Nat.mul_le_mul_left _ h3
+      _ = _ := by ring
   have heq : {x | ∃ u, u.length = C * (x.length + 1) ^ c ∧ x ++ u ∈ V} = L :=
     Set.ext (fun x => (hL x).symm)
   rw [heq] at hE
-  exact Set.mem_iUnion.mpr ⟨f, A, E, fun x => (hE x).mono (hbound x.length)⟩
+  exact Set.mem_iUnion.mpr ⟨f, A, E, fun x =>
+    (hE x).mono ((hpoly x.length).trans (hbound x.length))⟩
 
 /-! ### A3 exponential split and clean padding verifier
 The binary evaluator below is re-derived from the pinned `e3ShiftTM`
```

## Merge #1 (`e688a482`) on `TCSlib/Complexity/ClassNP/Tautology.lean` (note 12's historical caveat)

First-parent diff; before blob `301f469537143b268ba3cc781df54039ec7d4df0`, after blob `c92b7063863ce8c1b6fe58c04f78fc432b234842`.

```diff
diff --git a/TCSlib/Complexity/ClassNP/Tautology.lean b/TCSlib/Complexity/ClassNP/Tautology.lean
index 301f4695..c92b7063 100644
--- a/TCSlib/Complexity/ClassNP/Tautology.lean
+++ b/TCSlib/Complexity/ClassNP/Tautology.lean
@@ -35,7 +35,7 @@ over the **DNF fragment**, and states Example 2.21.
   content (its hardness *is* Example 2.21's argument), while general Boolean
   formulas remain unformalized, per the audit's do-not-silently-identify
   guidance. Strings are read through the **shared** audited serialization
-  (`Std.Sat.CNF.decode`), evaluated dually. **Seeded design question (e) for
+  (`Std.Sat.DNF.decode`, delegating to `Std.Sat.CNF.decode`), as a `Std.Sat.DNF`. **Seeded design question (e) for
   the phase-4 audit.**
 * **The fallback flips sides**: the empty formula is a CNF tautology but the
   empty *disjunction* is false, so under the DNF reading non-well-formed
@@ -68,7 +68,7 @@ over the **DNF fragment**, and states Example 2.21.
 
 namespace Complexity
 
-open Std.Sat (CNF)
+open Std.Sat (CNF DNF)
 
 /-- **`coNP`-hardness** [AB09, §2.6.1]: every `coNP` language Karp-reduces to
 `L` — the mirror of the audited `Complexity.NPHard`. -/
@@ -87,31 +87,27 @@ assignment. Under the DNF reading the fallback (the empty formula, an empty
 disjunction) is *not* a tautology, so non-well-formed strings lie outside
 `TAUTOLOGY` (see the deviations list). -/
 def TAUTOLOGY : Language Bool :=
-  {x | (CNF.decode x).DNFTautology}
+  {x | (DNF.decode x).Tautology}
 
 /-! **Epoch-3 fill addition.** Private certificate and verifier machinery for
 the audited membership proof. No concurrent SAT fill is used. -/
 
-/-- Negating the literal polarities twice restores the syntax. -/
-private lemma taut_dual_dual (φ : CNF ℕ) : CNF.dual (CNF.dual φ) = φ := by
-  delta CNF.dual
-  simp [List.map_map, Function.comp_def]
-
 /-- Changing literal polarities preserves the mentioned-variable bound. -/
-private lemma taut_numVars_dual (φ : CNF ℕ) : (CNF.dual φ).numVars = φ.numVars := by
-  delta CNF.numVars CNF.dual
+private lemma taut_numVars_dual (ψ : DNF) : (DNF.dual ψ).numVars = CNF.numVars ψ.terms := by
+  delta CNF.numVars DNF.dual
   simp [List.flatMap_map, List.map_map, Function.comp_def]
 
 /-- DNF evaluation depends only on the mentioned variables.
 
 **Proof sketch.** Apply CNF evaluation congruence to the literal-negated
-formula. The proved De Morgan identity negates both values; involutivity
-and preservation of the variable bound transfer the equality back. -/
-private lemma taut_eval_congr {φ : CNF ℕ} {a b : ℕ → Bool}
-    (h : ∀ v < φ.numVars, a v = b v) : φ.evalDNF a = φ.evalDNF b := by
-  have he := eval_congr_of_lt_numVars (φ := CNF.dual φ)
+formula `DNF.dual ψ`. The proved De Morgan identity `CNF.eval_dual` negates both
+values; `DNF.dual_dual` and preservation of the variable bound transfer the
+equality back. -/
+private lemma taut_eval_congr {ψ : DNF} {a b : ℕ → Bool}
+    (h : ∀ v < CNF.numVars ψ.terms, a v = b v) : ψ.eval a = ψ.eval b := by
+  have he := eval_congr_of_lt_numVars (φ := DNF.dual ψ)
     (a := a) (b := b) (by simpa only [taut_numVars_dual] using h)
-  rw [← taut_dual_dual φ, CNF.evalDNF_dual, CNF.evalDNF_dual, he]
+  rw [← DNF.dual_dual ψ, CNF.eval_dual, CNF.eval_dual, he]
 
 /-- A finite certificate supplies false outside its explicitly stored bits. -/
 private def tautAssignment (u : List Bool) : ℕ → Bool := fun v => u.getD v false
@@ -126,19 +122,19 @@ falsifying assignment. This includes malformed strings and the empty input. -/
 private lemma taut_certificate_equiv (x : List Bool) :
     x ∈ (TAUTOLOGYᶜ : Language Bool) ↔
       ∃ u : List Bool, u.length = x.length + 1 ∧
-        (CNF.decode x).evalDNF (tautAssignment u) = false := by
+        (DNF.decode x).eval (tautAssignment u) = false := by
   classical
   have hn : x ∈ (TAUTOLOGYᶜ : Language Bool) ↔
-      ∃ a : ℕ → Bool, (CNF.decode x).evalDNF a = false := by
-    change (¬ ∀ a : ℕ → Bool, (CNF.decode x).evalDNF a = true) ↔ _
+      ∃ a : ℕ → Bool, (DNF.decode x).eval a = false := by
+    change (¬ ∀ a : ℕ → Bool, (DNF.decode x).eval a = true) ↔ _
     simp only [not_forall, Bool.not_eq_true]
   rw [hn]
   constructor
   · rintro ⟨a, ha⟩
     let u := List.ofFn (fun i : Fin (x.length + 1) => a i.val)
     refine ⟨u, List.length_ofFn, ?_⟩
-    have he : (CNF.decode x).evalDNF (tautAssignment u) =
-        (CNF.decode x).evalDNF a := by
+    have he : (DNF.decode x).eval (tautAssignment u) =
+        (DNF.decode x).eval a := by
       apply taut_eval_congr
       intro v hv
       have hv' : v < x.length + 1 := lt_of_lt_of_le hv
@@ -171,14 +167,14 @@ negates the decoded DNF only after that split has succeeded. -/
 private def tautVerifierBit (z : List Bool) : Bool :=
   match Turing.solveSplit 1 1 z.length with
   | none => false
-  | some i => !((CNF.decode (z.take i)).evalDNF (tautAssignment (z.drop i)))
+  | some i => !((DNF.decode (z.take i)).eval (tautAssignment (z.drop i)))
 
 /-- The verifier language is the accepting set of its single buffered bit. -/
 private def tautVerifier : Language Bool := {z | tautVerifierBit z = true}
 
 /-- Correctly sized certificates recover their own split and evaluation. -/
 private lemma taut_verifier_append (x u : List Bool) (hu : u.length = x.length + 1) :
-    x ++ u ∈ tautVerifier ↔ (CNF.decode x).evalDNF (tautAssignment u) = false := by
+    x ++ u ∈ tautVerifier ↔ (DNF.decode x).eval (tautAssignment u) = false := by
   have hs := taut_split_exists (x ++ u).length x.length (by simp [hu])
   change tautVerifierBit (x ++ u) = true ↔ _
   simp only [tautVerifierBit, hs, List.take_left, List.drop_left, Bool.not_eq_true']
@@ -198,8 +194,8 @@ fallback has false DNF value, so it belongs to the complement. -/
 private lemma taut_malformed (x u : List Bool) (hx : CNF.parse x = none)
     (hu : u.length = x.length + 1) :
     x ∈ (TAUTOLOGYᶜ : Language Bool) ∧ x ++ u ∈ tautVerifier := by
-  have hv : (CNF.decode x).evalDNF (tautAssignment u) = false := by
-    simp only [CNF.decode, hx, Option.getD_none]
+  have hv : (DNF.decode x).eval (tautAssignment u) = false := by
+    simp only [DNF.decode, CNF.decode, hx, Option.getD_none]
     rfl
   exact ⟨(taut_certificate_equiv x).mpr ⟨u, hu, hv⟩,
     (taut_verifier_append x u hu).mpr hv⟩
@@ -1024,7 +1020,7 @@ private lemma taut_formula_run (φ : CNF ℕ) (u : List Bool)
       tautTM.tm.runFrom
         (tautCfg x (some (.evalFirst .formula)) pre.length
           (by simp [hx, universal_pair_length]) u 0) t =
-      tautCfg x none i hi u 0 [!(φ.evalDNF (tautAssignment u))] := by
+      tautCfg x none i hi u 0 [!((DNF.mk φ).eval (tautAssignment u))] := by
   induction φ with
   | nil =>
     intro x pre hx
@@ -1073,7 +1069,7 @@ private lemma taut_formula_run (φ : CNF ℕ) (u : List Bool)
       · simp only [hs, List.length_cons, List.length_append]
         omega
       · rw [MultiTapeTM.runFrom_succ_eq_step', hprefix, taut_verdict]
-        delta CNF.evalDNF
+        delta DNF.eval
         simp [hv]
     | false =>
       simp only [hv, Bool.false_eq_true, ↓reduceIte] at hprefix
@@ -1082,7 +1078,7 @@ private lemma taut_formula_run (φ : CNF ℕ) (u : List Bool)
       · simp only [hs, List.length_cons, List.length_append]
         omega
       · rw [MultiTapeTM.runFrom_add, hprefix, htail]
-        delta CNF.evalDNF
+        delta DNF.eval
         simp [hv]
 
 /-- Every member of the variable-contribution list is bounded by its maximum. -/
@@ -1111,13 +1107,13 @@ with the formula run. Empty terms and the empty disjunction are covered by
 the two structural base cases; only the final verdict emits a bit. -/
 private lemma taut_machine_pair (x u : List Bool) (hu : u.length = x.length+1) :
     tautTM.ComputesInTime (pairEncode x u)
-      [!((CNF.decode x).evalDNF (tautAssignment u))] (10*((pairEncode x u).length+1)) := by
+      [!((DNF.decode x).eval (tautAssignment u))] (10*((pairEncode x u).length+1)) := by
   cases hp : CNF.parse x with
   | none =>
     have h := taut_machine_malformed x u hp
     have hm := h.mono (show 2*x.length+3 ≤ 10*((pairEncode x u).length+1) by
       rw [universal_pair_length]; omega)
-    simpa only [CNF.decode, hp, Option.getD_none] using hm
+    simpa only [DNF.decode, CNF.decode, hp, Option.getD_none] using hm
   | some φ =>
     have hx := taut_parse_shape hp
     subst x
@@ -1133,11 +1129,11 @@ private lemma taut_machine_pair (x u : List Bool) (hu : u.length = x.length+1) :
       (pairEncode (CNF.serialize φ) u) [] rfl
     simp only [List.length_nil] at heval
     have hcomp : tautTM.ComputesInTime (pairEncode (CNF.serialize φ) u)
-        [!(φ.evalDNF (tautAssignment u))] (a+b) := by
+        [!((DNF.mk φ).eval (tautAssignment u))] (a+b) := by
       apply (FinTM.computesInTime_iff _ _ _ _).mpr
       rw [MultiTapeTM.runFrom_add, hstart, heval]
       exact ⟨rfl, rfl⟩
-    rw [CNF.decode_serialize]
+    rw [DNF.decode_cnf_serialize]
     apply hcomp.mono
     rw [universal_pair_length] at ha ⊢
     omega
@@ -1237,20 +1233,20 @@ the complement.
 
 **Proof sketch.** By the definition of `Complexity.coNP`, exhibit
 `TAUTOLOGYᶜ ∈ NP`: `x ∈ TAUTOLOGYᶜ` iff some assignment falsifies the DNF
-reading of `CNF.decode x`. Certificate parameters `(1, 1)` exactly as in
+`DNF.decode x`. Certificate parameters `(1, 1)` exactly as in
 `Complexity.SAT_mem_NP` — a certificate of length `|x| + 1` carries the
 assignment on the mentioned variables (`Std.Sat.CNF.numVars_decode_le`
-bounds them by `|x|`; the evaluation-congruence bridge transfers to `evalDNF`
+bounds them by `|x|`; the evaluation-congruence bridge transfers to `DNF.eval`
 by the same mentioned-variable argument, a named obligation mirroring
 `Complexity.eval_congr_of_lt_numVars`). The verifier machine reuses the
 `SAT_mem_NP` obligations — odd-length split with explicit even rejection,
 the shared parsing machine, the assignment walk — with the **dual**
 evaluation loop: accept iff **every** term contains an unsatisfied literal,
-i.e. evaluate `evalDNF` and answer its negation (an empty term forces
+i.e. evaluate `DNF.eval` and answer its negation (an empty term forces
 rejection, the empty formula forces acceptance — round-1 audit, finding 2,
 correcting the drafted some-term phrasing) — and the buffered verdict. Malformed
 strings: the fallback is not a DNF tautology, so they lie in `TAUTOLOGYᶜ`,
-and the verifier accepts them with any certificate (`evalDNF` of `[]` is
+and the verifier accepts them with any certificate (`DNF.eval` of `⟨[]⟩` is
 `false` — consistent on both sides). -/
 theorem TAUTOLOGY_mem_coNP : TAUTOLOGY ∈ coNP := by
   exact taut_membership_of_verifier taut_verifier_mem_P
@@ -1260,11 +1256,11 @@ theorem TAUTOLOGY_mem_coNP : TAUTOLOGY ∈ coNP := by
 **Proof sketch.** Membership is `Complexity.TAUTOLOGY_mem_coNP`. Hardness:
 let `L ∈ coNP`, so `Lᶜ ∈ NP`, and `Complexity.SAT_NPHard` (Lemma 2.11)
 supplies `f` with `z ∈ Lᶜ ↔ f z ∈ SAT`. Set
-`g z := Std.Sat.CNF.serialize (Std.Sat.CNF.dual (CNF.decode (f z)))` — parse
+`g z := Std.Sat.DNF.serialize (Std.Sat.CNF.dual (CNF.decode (f z)))` — parse
 the Cook-Levin output, take the De Morgan dual, re-serialize. Then for every
 `z`: `z ∈ L` iff `f z ∉ SAT` iff `CNF.decode (f z)` is unsatisfiable iff its
-dual is a DNF tautology (`Std.Sat.CNF.dnfTautology_dual_iff`) iff
-`g z ∈ TAUTOLOGY` (`Std.Sat.CNF.decode_serialize` re-reads the emitted
+dual is a tautology (`Std.Sat.CNF.tautology_dual_iff`) iff
+`g z ∈ TAUTOLOGY` (`Std.Sat.DNF.decode_serialize` re-reads the emitted
 string; the decode-dual-serialize round trip is exact on every string since
 decoding is total). `Complexity.PolyTimeComputable g`: compose `f`'s machine
 (`Complexity.PolyTimeComputable.comp`) with the parse-dual-serialize
```

## ===== audits/evidence/ch2-epoch34/final-source-manifest.md =====

# Final source/olean manifest — round-2 closure run (finding 1/2)

- Repository commit: `154ecb189633c08b3a76ce1d0aac74e16e335021`
- Toolchain: Lean 4.25.0 `cdd38ac5115b`; mathlib `029db123ddaa`

| # | Module | source SHA-256 | olean SHA-256 (round-2 fresh tree) |
|---|---|---|---|
| 1 | `TCSlib/Complexity/TuringMachine/Configuration` | `8633cd44271265c3844387cdc4d9cb8f14c3ed819f3d3aaf4d50f31d30e61ba4` | `0cab868b7fb2438d6d0682945e4e5acf8d1d8ef9e3dba755ed9372df3d703ca5` |
| 2 | `TCSlib/Complexity/TuringMachine/Deterministic` | `cf0c8eb00232665b492b4547116298515829002c3bf8acd2ca7d1e4da2fb99a3` | `c5548097854e31ebb447e17aee47510cc5fc8508a2a83ce5a2c3f6548d108386` |
| 3 | `TCSlib/Complexity/TuringMachine/StateRenaming` | `98168241c6ae33bcbaf2d847536596b356a333bd05797cb141cb1ab5d8029759` | `c0219044dbe2f36527d90da3f9557b4d56225bfbf9b73e8e37efa8933cfc7058` |
| 4 | `TCSlib/Complexity/TuringMachine/Finite` | `af7d8ff3214ba6a3495f516e8eb0cab2f36b20eda82333932cc5d938c45273a9` | `907ff31c88de154e18f8c13143050366582268a1c075a972d6519d82f005cd1e` |
| 5 | `TCSlib/Complexity/TuringMachine/Oracle` | `346cbef36ad5b82cc7a5da3a7216f3b5358544e273ceb2682e3239bb4f735ec2` | `1c670b2df70fb55195af215a496aebea98ad3d854ba1a5b4d57d346a3319bde2` |
| 6 | `TCSlib/Complexity/TuringMachine/Simulation` | `e012266744dc960804aa6ed770c3c467e066716f635c6fbbd0fbfa489b4941dd` | `6bf4f454933af270e496c3b836756976f03b4b14fe2b124d4d9c6b6a5837faca` |
| 7 | `TCSlib/Complexity/TuringMachine/Sweep` | `d43e9b6dd7bdc291f8c657b12f72e068e96fbe0a74ffec60137eb27295a1b4c3` | `1615718b1145577a5b0d3d5fb697858acf95f1f8a7790bfcd1389eec2a7abe4b` |
| 8 | `TCSlib/Complexity/TuringMachine/Composition` | `264430fafd3c760d9d0a9f44207213dbdb20bba87a898f438e9a6b3e5daebc64` | `416c82c644ab860ce060ad1911342d7646e3034a5d18f606f003381c44fe7df8` |
| 9 | `TCSlib/Complexity/TuringMachine/Build/Convention` | `a75f9d377b91d668a47dfb6e7b7f791b05b8cc8bbd88d1f0c315bbb8d34c13c6` | `cf387b9fd33f7d7252c9093de6eb02592cbb14e8e4ca61d71dc86dff4942c530` |
| 10 | `TCSlib/Complexity/TuringMachine/Build/Wrappers` | `027a1fb63939cfcf44a803b6b34a31d08e2e0ca9230ab94d57a6472245949bea` | `9db501745b89734ac2ef2e50d0a443d02fe70fb5ada2fe326f1a188200128814` |
| 11 | `TCSlib/Complexity/TuringMachine/Build/Loop` | `ef9c86dc0aef2eba3611527b3084a0472ce99a37532e64c9037ff8c6c6179ea8` | `adeac2ea499c8bb7e0d010941bd39ffca09021c1e6764d09de0e0a461178a9fb` |
| 12 | `TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction` | `d72f44208bec6777a9575a1009f5522a3bb36ba2cc9a77b4aa5ec0922ed8c0be` | `0fc30815bf00bbbf1c039b781e0b2c0ab728ae1e41f03f58e3351385c15a3e24` |
| 13 | `TCSlib/Complexity/TuringMachine/Robustness/SingleTape` | `5ba229cffdf7dd3040e34d7982c7fb389185ede40794a611c7fe48e8d941add3` | `d26b5467eae7e011caebdffa8947f2e3492904e46ffcd10c6ac72cfe7b56126a` |
| 14 | `TCSlib/Complexity/TuringMachine/Robustness/Bidirectional` | `326dfc6633a6e7ec681b0abde3f5597ae6ae75ec044c4a0ae6139ad6aed1d44c` | `947559cd62ff46d084b236299bd9f3dce7a9cb97db5737bff4fe2dfbfdea4729` |
| 15 | `TCSlib/Complexity/ClassP/DTIME` | `54795908ce0a394d59cc7ca91a0c9f9377ff687e1bc805af3e65889212c3cc84` | `517d1cb340b855bde31e38e3f00dfb789ecdc16b6c7c4a26b7d3d2eaee4c2ae2` |
| 16 | `TCSlib/Complexity/TuringMachine/Encoding` | `f810afae8655039d9344baa39cd5d65126180d88e9e8b144741fe160e3f0e6ea` | `02de17da1aa0fdb7c92397e8a8ec7d4ed719db306ea438eebca88ae206d8c60e` |
| 17 | `TCSlib/Complexity/ClassP/TimeConstructible` | `5b2cad43f72120bc74378d25c48cf48dc7a96bc9637dc13bcc1bfbae7a20889d` | `61f6c2c59dd454705b598fca6f80f8fb3b926cee7c8af9632cd8cca6515d85ff` |
| 18 | `TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule` | `357c9d98f62a574b487abb6833cb33f2602e6f75a3b1d95a11fec5212b79fd67` | `5ff641a830f6ae26ad5807f35d40f03dba1414174bf9d5f42de52d05f89f4b02` |
| 19 | `TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate` | `f0e69ed8fa9fbd5c73068694a5e8a162e77cffd671742b5e156e764cd4a6f771` | `4d66eaf9e67953ede16400070a7ea08f0d23b2af654d66f5597a77982e1f75a2` |
| 20 | `TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup` | `924bf2ef064c12636cacb42babdf4e06b44c6ea298e256aeb44aa2b7e6fa3110` | `ab2c3f62510293425c21b05a0e8ea7b3e460f4e06c16cf05c2fe14098359c0a1` |
| 21 | `TCSlib/Complexity/TuringMachine/Robustness/ObliviousLedger` | `88847a586b0b8656e57c4be0f927838cd636040410d838293c4a2afb9ae92649` | `be2141bf57bc3cbbb153974bfcaca73f0e55383866162626fbd9379c3a822101` |
| 22 | `TCSlib/Complexity/TuringMachine/Robustness/Oblivious` | `4dd19cb547a78ca15f39fc72f88c03d050ed88f087494c824c965e63f210166e` | `e842a9f81f752ee11a77032814b7ef2e1298b701d1dc72fc71694ee9de1ab9f9` |
| 23 | `TCSlib/Complexity/ClassP/P` | `b9a52ed504708642a83705fcd597f5afe99e902deb1cd0ace2fd56d4bd4a66e7` | `5ed8450b54b197f7107946f3ba49533a322cac9711de063b1645e18655b697f2` |
| 24 | `TCSlib/Complexity/ClassP/ModelInvariance` | `fdfdf250d8571091e71b6cb0d6fbd57eeef9306019475757d33b601bd835c51c` | `96c20b6fddbe2375faf238c30a01dc1be170ac319bb594bbf8e5a7b40bda8854` |
| 25 | `TCSlib/Complexity/ClassP/Examples` | `637ea8be576264eb09054d02f81509b90d8ebf79fec5d868966a444308068c67` | `789d3b86f9d4f488da4d618fd3b549ade48d324aa3ca97bb088ec1185ad89237` |
| 26 | `TCSlib/Complexity/TuringMachine/Build/Primitives` | `3a2f5d2649ac6c5cdcbd53fcf0f9ac3d6e40b0134f41b33222e3953da2ebb3d6` | `691d35b824dac70b728bdd603986ab92c279f7fb04d15d9e1fa5c3e46d3de61b` |
| 27 | `TCSlib/Complexity/TuringMachine/CodeParser` | `14f936c18352f7eda28839e144533f381d7345e39f1e4e776a8d732bb4f44517` | `f6dbc34f6d3d6a90eb8c85981d67f62e9cadebcfd6f6af932b12ee4e5b6723f8` |
| 28 | `TCSlib/Complexity/TuringMachine/MathlibBridge` | `3e93f31bb3cd538325d921dc58a96babc966582a070c8a0b9ef0ef54109021f3` | `960b88151cfd911c6897be68d7bd8c596bc03bc748d4ce70e259afee953f887a` |
| 29 | `TCSlib/Complexity/TuringMachine/UniversalStartup` | `b9a6f832fe89a59f1c01252204352b773ba16829ec77479736f29f2888ba5cce` | `62579dc6d7e8f259e117c421c9c38e49c8029e62f2c09d516d36480e82f82003` |
| 30 | `TCSlib/Complexity/TuringMachine/UniversalInterpreter` | `5c510df8f730907665319e6bc9b82e5c8b0423a37008e97cae02c1d02368b19f` | `dae30cb37fcbdce3eec385ad5e0dea143305a04ec2e74c270f9f60580d8d1aeb` |
| 31 | `TCSlib/Complexity/TuringMachine/UniversalBlock` | `d5daaa75eb962584b03dc958421a4d07d0a529441e1a28afd5015552882e627d` | `234c9b3f05c952339af00920c83d605d7ff45cfdc0f770b568cbdc5709fca71e` |
| 32 | `TCSlib/Complexity/TuringMachine/Universal` | `ce7d66f32b08b70c549d329a784696a8d87461df3724799e1b18837312563871` | `5bbab8f310ce5a7f794ce779666b4ac71e5b456f8474e1b386fbc5516b244e6f` |
| 33 | `TCSlib/Complexity/Uncomputability/Computable` | `1ad827bd15a8a492e11de0f2cd1a5167e358be927f274aedb6c0a0ed35aecaf6` | `69b3d16123db430a4055fd3a0d59c65691484fb1802c12ff55ec96751ca8be44` |
| 34 | `TCSlib/Complexity/Uncomputability/Diagonalization` | `089dffc34eb4477569053134279c111541af2c3c0daa10ffa3da78cc06497473` | `fbe4672063d62a927c5018e819b4f628550e8277e7b79de9a9be0da88ad305f8` |
| 35 | `TCSlib/Complexity/Uncomputability/Halting` | `f1e7985f40ca01e0871fedda45e1b3a31eef220192a44ea80ee9ec7acf222581` | `a9f67e9799ff8f7e58d80d53b519c26f06ef142aeae79aad81c358e7eb474a70` |
| 36 | `TCSlib/Complexity/TuringMachine/Nondeterministic` | `c0f14885c58c1abb36dfac5ab058b77db980a01f5aac95f5397bb8ddb2aa2a67` | `a9036211c8a0d1b23cadcb66af92cce6b8077183a9cca41fcbd660f51598eb46` |
| 37 | `TCSlib/Complexity/Formulas/CNF` | `3c51f5305cf957ad7de5f29e922c093f618f9c8aca76ad69ad81a337f4799a18` | `468c724e4e4d19d45ba5561166001a97ff206eb72f46e1c2f08d619fc01c5dec` |
| 38 | `TCSlib/Complexity/Formulas/CNFEncoding` | `7af5886d9df12d512dfd6fa444c0de1726baef851947d5d51c03ea82fcf7dde2` | `0ae3e4e1528725b841b41702bd7b61208f229b0cc6ed3c8a03b6ba799dda83bf` |
| 39 | `TCSlib/Complexity/Formulas/DNF` | `fb6888fbc5d9c4f4035e73bcb1a05a8bb75b2c71124c7fd98c6fbdda53aa36dd` | `79f3536a8560a897abfd254f6dbc83d6f03c86356c38b3e96e0bf7c7109f8770` |
| 40 | `TCSlib/Complexity/ClassNP/PolyTime` | `333fc6e93739bc4e977308e0ccf16ff9e837fd638e48a91270f8c56a85371bd1` | `6bdaf3a6ce7906c38ab16c3c2a5236e8de1a75f5c307f5f88603a32f05dd0606` |
| 41 | `TCSlib/Complexity/ClassNP/PolyTimePairing` | `31a44bda2c205dfd92903417e636112cf9947222c5d87ab122870f4881cd1c82` | `257c74336e63322191bb9cc8ba94a393a2b01a515da7e3c510d69767321e0b98` |
| 42 | `TCSlib/Complexity/ClassNP/NP` | `efe31055353bf652e3ca410a7f58e2e578af0b4ccaf036586095b1e03a5dbf68` | `3579687317c5f898cf048e72985f732e8b12a47664b6d98b679d1aff8b7ef60b` |
| 43 | `TCSlib/Complexity/ClassNP/CoNP` | `bcf23fe2e091282f6ed51d417e47d04503e2247180edfbe093a8905ffdd0955c` | `01583fb8bf0afe961fb80a6f85f489c776b630280eb1891f44e6eee61771d503` |
| 44 | `TCSlib/Complexity/ClassNP/EXP` | `3c602cfdfa1aa564fd5edbcc326d7e2e79d5aed8b3b610e33d801819010dbef6` | `595404960e175e67ea3f8234dbe488e86b7e94e31b315cd24106c9cb39afccb8` |
| 45 | `TCSlib/Complexity/ClassNP/Reductions` | `71b52fc82ecce4cdba174e3a7461c784e1e7478103001ab067500a5775b8e04d` | `449a48288ff35256f96140772fcda2d6efbdbda2625688e8c69e94c14f1059ee` |
| 46 | `TCSlib/Complexity/ClassNP/NTIME` | `8776fab1ba5edc3b2945963aee7d7086cea2a5792fe33fb3d111c3c097cb7494` | `b6a997af75faf66bcb8a5150ada668395174acdd52ba8820de362d6fd73660f7` |
| 47 | `TCSlib/Complexity/ClassNP/Nondeterminism` | `29c4b93514d68578d36050dcd774facdc113e978af59506596a7b90e61482736` | `3457d4620e8f81a74c03b6b5384232d1b292a73ef2cd3f3f8aaf7f526517ad69` |
| 48 | `TCSlib/Complexity/ClassNP/SAT` | `a82cfb33e47eef7a3368f5c46267662824ef4bb974783638708d23621247e740` | `69dc4906af464096ec9e88006387fc164e6ed42da3c37361c787643408a54189` |
| 49 | `TCSlib/Complexity/ClassNP/TMSAT` | `d8eafec343641ca04e6e71b7ceecb1dbefa4a0f5f96486c9fc5a4d040ebae63d` | `f5bcbe4b8c9b1f9dad43f07ca7322777f9c6a643062081ff491dcff299fbf055` |
| 50 | `TCSlib/Complexity/CookLevin/Snapshot` | `d30d4ef5746e14dd011e038906baed120b1dcd71f5bd6e8f2e6ef8bf3ef8bc77` | `7d72000426d55a91cacffa4ea680572e25172943835272833f71b6b01d9214dc` |
| 51 | `TCSlib/Complexity/CookLevin/Hardness` | `e3d6b63f2852c7fe8a049dbc7bbb87273cd39150fd0c14580ef70b06fdefc951` | `99afd4a5ffcf2034435a9b88b797f82eabac1ce69ddadc8ff5379604b999f201` |
| 52 | `TCSlib/Complexity/ClassNP/Tautology` | `2f2814d285ee2a477ed8e135885ce5f0987612bd861a78b7d1c9e62a685979d9` | `301922542269bbb788790381ded818486cce308a7b6b99808f0c2ea684cc3603` |
| 53 | `TCSlib/Complexity/TuringMachine/UnaryTape` | `3c7c639b324fa577af524310b93e7ec8c39494cbd5ddf5f5482ed90ae6d134d4` | `c4fca9a3bc6fa4ff043057b1054db236617f67ac211528461e8108dd4d0521be` |
| 54 | `TCSlib/Complexity/TuringMachine/CounterProg` | `a9d858f6cb848fef51d41cf44589328e363a02ea98e1e431a6f9fba1969658c4` | `8e212501f3b03676f1a6a13820320eea5f478df2db7b1ea5588e8b52e24255b3` |
| 55 | `TCSlib/Complexity/TuringMachine/CounterProgRun` | `eaa539b25ee9c050598d475bcda08cec15a9522cafdde7a0167543c08afb9911` | `e3e2b419e500a62849632b1bea3616a879df2d95438573b08a84e8099bfb207e` |
| 56 | `TCSlib/Complexity/TuringMachine` | `16a6e718ab5f0178ffdadd295034999d1b791a561aa7d1accd5e0b7f3fe1eb5d` | `9ef68e07ed1d798080d3d4a89b970f80c84ab1048e60f56e4570b0d31070387c` |
| 57 | `TCSlib/Complexity/ClassP` | `002c5000c89b40bd56213b748fdfbaba848f5b4de10244d61be4f41ff202b481` | `5fc9db3e8db28485a6245087ea87f3c081cf6520d182f384dda53a7de101b43e` |
| 58 | `TCSlib/Complexity/Uncomputability` | `220977febf5490ebade043999b78c6df576cc1ba85c7a380fe560f443820f766` | `fb3a1d510169c8f59965cce47cef231278f9399a098c98015ecca00b9d38b66b` |
| 59 | `TCSlib/Complexity/Formulas` | `d85932e65718ca00656ae679513006890abf6cae2c84bbf15002496e1c53f5a3` | `86a937cdd1b9223f2d2ece9b09085bc6190991babbd6fa8c06777b9e036e6892` |
| 60 | `TCSlib/Complexity/CookLevin` | `1867b5b18261f0508f4e8c33e7364779027970fd0eb709fab650bd6cb4c6f2ca` | `bc02dbd6fb13276fc36bcef6b800b4444fef817c962e96ff9d16517422fe312b` |
| 61 | `TCSlib/Complexity/ClassNP/Transducer` | `31a050f543c0945037ed254bc48ee4f86b2751e6abde68d85062186b22e09b05` | `2fa597679fcb4f35c6684069109250571967050fe25ff16d471523ae188f50bf` |
| 62 | `TCSlib/Complexity/ClassNP/CounterProgPolyTime` | `a40e9e33042e619444ae2d89f46a55113bdcc92aa6e84536524720f95c988428` | `fd05df7282f4ee25b2ba959a6ab1e39449259dafb58da52eb760cba5565cb955` |
| 63 | `TCSlib/Complexity/ClassNP/PClosure` | `0df0275cb4248ddad98c46b4ecb126d07f06d747cc1de686383a7b44b4b3cc2d` | `d7ef50e39db374d96cbad0e13c52b3fd73f79d2615cc97b0bf11865ee018f058` |
| 64 | `TCSlib/Complexity/ClassNP/ExpPoly` | `12ac7599c58475f48847f325785acb120565842e58f94ed5b97e4fb063fd6d31` | `a1ac8e201ba502f436455853216549dc765eecce60f309c14daab678d5105f15` |
| 65 | `TCSlib/Complexity/ClassNP` | `313d2eca566335038c131563faf5bf346164cb49ba74fac8f6d8f90128addda2` | `65ef924684a020416478b920c588b3885ce8f5f3199747bea1808c27a87a60ae` |

## ===== audits/evidence/ch2-epoch34/duplicate-run-record.md =====

# Duplicate A-3 dispatch: checksum-verified two-run comparison (finding 13)

All three delivered archives remain at `ch2_local/epoch3/` (maintainer-side;
binary archives are not bundle-attachable, so this record carries their
identities and the verified binding).

| Artifact | SHA-256 |
|---|---|
| `fill-ch2-e3cont-A3.zip` (run alpha) | `a5d7948ee3e14749e2c27ae72a8ffd43dc547f39d93c29781dd6b5dcee99767f` |
| `fill-ch2-e3cont-A3 (2).zip` | identical to alpha (same SHA-256) |
| `fill-ch2-e3cont-A3 (1).zip` (run beta, selected) | `161e6cc7ea4b038294e3f51d52803d910acd462419b1f96973d2a08c24d2e9f1` |
| beta's patch `0001-close-padding-cluster.patch` | `f78fde614d5f01f63e434e513ba57b7efce6c4e86aa8ee9937402bdcd996176e` |
| alpha's patch `0001-Close-the-E3-continuation-padding-cluster.patch` | `92bb4d3801f3092a3c85943154acf001be26124636d2d478298446b562b65c54` |

**Binding, mechanically re-verified 2026-10-06 for this record**: applying
beta's patch with `git am` in an isolated worktree at `1c824071^`
(= `61cf5958`, whose owned-file contents are byte-identical to the brief
base `f57cf9c1` — the intervening commit adds briefs only) reproduces tree
`8e1c03588179ae0457ea4b388521aa7bfc43cbe6`, exactly the tree of the
integrated commit `1c824071`. The integration therefore contains beta's
delivery and nothing else.

Alpha was never applied to any branch; no blob from alpha's archive appears
in the repository (its sources remain only inside the archived zip). Alpha's
REPORT opens:

> # E3 continuation A3 — complete padding-cluster delivery

The selection criteria and their application are recorded in the decision
log (2026-10-05) and summarized in the span attestation §6; this record
supplies the checksum layer that finding 13 requested. The no-hybridization
claim is witnessed by the tree identity above.

## ===== audits/logs/colleague-merge2-sweep.log =====

[1/58] TCSlib/Complexity/TuringMachine/Configuration
TCSlib/Complexity/TuringMachine/Configuration.lean:137:17: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Configuration.lean:140:61: warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
TCSlib/Complexity/TuringMachine/Configuration.lean:155:17: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
[2/58] TCSlib/Complexity/TuringMachine/Deterministic
[3/58] TCSlib/Complexity/TuringMachine/StateRenaming
[4/58] TCSlib/Complexity/TuringMachine/Finite
[5/58] TCSlib/Complexity/TuringMachine/Oracle
[6/58] TCSlib/Complexity/TuringMachine/Simulation
[7/58] TCSlib/Complexity/TuringMachine/Sweep
[8/58] TCSlib/Complexity/TuringMachine/Composition
[9/58] TCSlib/Complexity/TuringMachine/Build/Convention
[10/58] TCSlib/Complexity/TuringMachine/Build/Wrappers
[11/58] TCSlib/Complexity/TuringMachine/Build/Loop
TCSlib/Complexity/TuringMachine/Build/Loop.lean:2932:8: warning: This simp argument is unused:
  Fin.val_zero

Hint: Omit it from the simp argument list.
  simp only [emCallClearCfg, MultiTapeTM.step, emCallClearTM, Cfg.workTapeSymbols, F̵i̵n̵.̵v̵a̵l̵_̵z̵e̵r̵o̵,̵ ̵Fin.val_one,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲Nat.one_ne_zero, ↓reduceIte, hmark, reduceCtorEq, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:2932:22: warning: This simp argument is unused:
  Fin.val_one

Hint: Omit it from the simp argument list.
  simp only [emCallClearCfg, MultiTapeTM.step, emCallClearTM, Cfg.workTapeSymbols, Fin.val_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲F̵i̵n̵.̵v̵a̵l̵_̵o̵n̵e̵,̵ ̵Nat.one_ne_zero, ↓reduceIte, hmark, reduceCtorEq, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:2932:35: warning: This simp argument is unused:
  Nat.one_ne_zero

Hint: Omit it from the simp argument list.
  simp only [emCallClearCfg, MultiTapeTM.step, emCallClearTM, Cfg.workTapeSymbols, Fin.val_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲Fin.val_one, N̵a̵t̵.̵o̵n̵e̵_̵n̵e̵_̵z̵e̵r̵o̵,̵ ̵↓reduceIte, hmark, reduceCtorEq, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:2974:27: warning: This simp argument is unused:
  Fin.val_zero

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emCallClearCfg, emCallClearTM, Cfg.workTapeSymbols, F̵i̵n̵.̵v̵a̵l̵_̵z̵e̵r̵o̵,̵ ̵Fin.val_one,
  ̲  ̲ ̲ ̲ ̲ ̲Nat.one_ne_zero, ↓reduceIte, hmark, reduceCtorEq, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:2974:41: warning: This simp argument is unused:
  Fin.val_one

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emCallClearCfg, emCallClearTM,
  ̵  ̵ ̵ ̵ ̵ ̵Cfg.workTapeSymbols, Fin.val_zero,
  ̲ F̵i̵n̵.̵v̵a̵l̵_̵o̵n̵e̵,̵  ̲ ̲ ̲ ̲Nat.one_ne_zero, ↓reduceIte, hmark,
  ̵  ̵ ̵ ̵ ̵ ̵reduceCtorEq, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:2974:54: warning: This simp argument is unused:
  Nat.one_ne_zero

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emCallClearCfg, emCallClearTM, Cfg.workTapeSymbols, Fin.val_zero,
  ̲  ̲ ̲ ̲ ̲ ̲Fin.val_one, N̵a̵t̵.̵o̵n̵e̵_̵n̵e̵_̵z̵e̵r̵o̵,̵ ̵↓reduceIte, hmark, reduceCtorEq, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3021:8: warning: This simp argument is unused:
  Fin.val_zero

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emCallClearCfg, emCallClearTM, Cfg.workTapeSymbols, F̵i̵n̵.̵v̵a̵l̵_̵z̵e̵r̵o̵,̵ ̵Fin.val_one,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲Nat.one_ne_zero, ↓reduceIte, hblank, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3021:22: warning: This simp argument is unused:
  Fin.val_one

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emCallClearCfg, emCallClearTM, Cfg.workTapeSymbols, Fin.val_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲F̵i̵n̵.̵v̵a̵l̵_̵o̵n̵e̵,̵ ̵Nat.one_ne_zero, ↓reduceIte, hblank, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3021:35: warning: This simp argument is unused:
  Nat.one_ne_zero

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emCallClearCfg, emCallClearTM, Cfg.workTapeSymbols, Fin.val_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲Fin.val_one, N̵a̵t̵.̵o̵n̵e̵_̵n̵e̵_̵z̵e̵r̵o̵,̵ ̵↓reduceIte, hblank, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3053:6: warning: This simp argument is unused:
  Fin.val_zero

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emCallClearCfg, emCallClearTM, Cfg.workTapeSymbols, F̵i̵n̵.̵v̵a̵l̵_̵z̵e̵r̵o̵,̵ ̵Fin.val_one,
  ̲  ̲ ̲ ̲ ̲ ̲Nat.one_ne_zero, ↓reduceIte, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3053:20: warning: This simp argument is unused:
  Fin.val_one

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emCallClearCfg, emCallClearTM, Cfg.workTapeSymbols, Fin.val_zero,
  ̲  ̲ ̲ ̲ ̲ ̲F̵i̵n̵.̵v̵a̵l̵_̵o̵n̵e̵,̵ ̵Nat.one_ne_zero, ↓reduceIte, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3053:33: warning: This simp argument is unused:
  Nat.one_ne_zero

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emCallClearCfg, emCallClearTM, Cfg.workTapeSymbols, Fin.val_zero,
  ̲  ̲ ̲ ̲ ̲ ̲Fin.val_one, N̵a̵t̵.̵o̵n̵e̵_̵n̵e̵_̵z̵e̵r̵o̵,̵ ̵↓reduceIte, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3082:22: warning: This simp argument is unused:
  min_le_right

Hint: Omit it from the simp argument list.
  simp [emCallSpan, m̵i̵n̵_̵l̵e̵_̵r̵i̵g̵h̵t̵,̵ ̵le_max_right]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3082:36: warning: This simp argument is unused:
  le_max_right

Hint: Omit it from the simp argument list.
  simp [emCallSpan, min_le_right,̵ ̵l̵e̵_̵m̵a̵x̵_̵r̵i̵g̵h̵t̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3270:24: warning: This simp argument is unused:
  hspan

Hint: Omit it from the simp argument list.
  simp [emCallSpan, h̵s̵p̵a̵n̵,̵ ̵bufferTape, hn, List.getElem?_eq_none hlen]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3271:24: warning: This simp argument is unused:
  hspan

Hint: Omit it from the simp argument list.
  simp [emCallSpan, h̵s̵p̵a̵n̵,̵ ̵bufferTape, hn]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3579:27: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3579:27: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3832:19: warning: This simp argument is unused:
  show (1 : Fin 2) ≠ 0 by decide

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emCallFinishCfg, emCallFinishTM, Cfg.workTapeSymbols, Fin.isValue,
  ̲  ̲ ̲ ̲ ̲ ̲s̵h̵o̵w̵ ̵(̵1̵ ̵:̵ ̵F̵i̵n̵ ̵2̵)̵ ̵≠̵ ̵0̵ ̵b̵y̵ ̵d̵e̵c̵i̵d̵e̵,̵ ̵↓reduceIte, hblank]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3834:50: warning: This simp argument is unused:
  emCallFinishCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, e̵m̵C̵a̵l̵l̵F̵i̵n̵i̵s̵h̵C̵f̵g̵,̵ ̵sub_eq_add_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3849:21: warning: This simp argument is unused:
  show (1 : Fin 2) ≠ 0 by decide

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emCallFinishCfg, emCallFinishTM, Cfg.workTapeSymbols,
          Fin.isValue, s̵h̵o̵w̵ ̵(̵1̵ ̵:̵ ̵F̵i̵n̵ ̵2̵)̵ ̵≠̵ ̵0̵ ̵b̵y̵ ̵d̵e̵c̵i̵d̵e̵,̵ ̵↓reduceIte, hread]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3852:30: warning: This simp argument is unused:
  emCallFinishCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, emCallF̵i̵n̵i̵s̵h̵C̵f̵g̵,̵ ̵e̵m̵C̵a̵l̵l̵_erase_last]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3853:54: warning: This simp argument is unused:
  emCallFinishCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, e̵m̵C̵a̵l̵l̵F̵i̵n̵i̵s̵h̵C̵f̵g̵,̵ ̵sub_eq_add_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3881:50: warning: This simp argument is unused:
  emCallFinishCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, e̵m̵C̵a̵l̵l̵F̵i̵n̵i̵s̵h̵C̵f̵g̵,̵ ̵sub_eq_add_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3881:67: warning: This simp argument is unused:
  sub_eq_add_neg

Hint: Omit it from the simp argument list.
  simp [Action.apply, emCallFinishCfg,̵ ̵s̵u̵b̵_̵e̵q̵_̵a̵d̵d̵_̵n̵e̵g̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3892:52: warning: This simp argument is unused:
  emCallFinishCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, e̵m̵C̵a̵l̵l̵F̵i̵n̵i̵s̵h̵C̵f̵g̵,̵ ̵sub_eq_add_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3925:26: warning: This simp argument is unused:
  emCallFinishCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, e̵m̵C̵a̵l̵l̵F̵i̵n̵i̵s̵h̵C̵f̵g̵,̵ ̵sub_eq_add_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3941:30: warning: This simp argument is unused:
  emCallFinishCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, e̵m̵C̵a̵l̵l̵F̵i̵n̵i̵s̵h̵C̵f̵g̵,̵ ̵bufferTape_append]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3943:30: warning: This simp argument is unused:
  emCallFinishCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, e̵m̵C̵a̵l̵l̵F̵i̵n̵i̵s̵h̵C̵f̵g̵,̵ ̵sub_eq_add_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3943:47: warning: This simp argument is unused:
  sub_eq_add_neg

Hint: Omit it from the simp argument list.
  simp [Action.apply, emCallFinishCfg,̵ ̵s̵u̵b̵_̵e̵q̵_̵a̵d̵d̵_̵n̵e̵g̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3944:43: warning: This simp argument is unused:
  emCallFinishCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, e̵m̵C̵a̵l̵l̵F̵i̵n̵i̵s̵h̵C̵f̵g̵,̵ ̵sub_eq_add_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3944:60: warning: This simp argument is unused:
  sub_eq_add_neg

Hint: Omit it from the simp argument list.
  simp [Action.apply, emCallFinishCfg,̵ ̵s̵u̵b̵_̵e̵q̵_̵a̵d̵d̵_̵n̵e̵g̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3968:65: warning: This simp argument is unused:
  emCallFinishCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, e̵m̵C̵a̵l̵l̵F̵i̵n̵i̵s̵h̵C̵f̵g̵,̵ ̵sub_eq_add_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3968:82: warning: This simp argument is unused:
  sub_eq_add_neg

Hint: Omit it from the simp argument list.
  simp [Action.apply, emCallFinishCfg,̵ ̵s̵u̵b̵_̵e̵q̵_̵a̵d̵d̵_̵n̵e̵g̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3979:54: warning: This simp argument is unused:
  emCallFinishCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, emCallF̵i̵n̵i̵s̵h̵C̵f̵g̵,̵ ̵e̵m̵C̵a̵l̵l̵_erase_last]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:3981:30: warning: This simp argument is unused:
  emCallFinishCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, e̵m̵C̵a̵l̵l̵F̵i̵n̵i̵s̵h̵C̵f̵g̵,̵ ̵sub_eq_add_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4040:21: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4040:33: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4077:2: warning: 'all_goals
  repeat
    first
    | rfl
    | omega
    | split' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4077:12: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4168:47: warning: This simp argument is unused:
  Fin.addCases_right

Hint: Omit it from the simp argument list.
  simp only [emCallSlots, Fin.addCases_left,̵ ̵F̵i̵n̵.̵a̵d̵d̵C̵a̵s̵e̵s̵_̵r̵i̵g̵h̵t̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4182:28: warning: This simp argument is unused:
  Fin.addCases_left

Hint: Omit it from the simp argument list.
  simp only [emCallSlots, Fin.addCases_l̵e̵f̵t̵,̵ ̵F̵i̵n̵.̵a̵d̵d̵C̵a̵s̵e̵s̵_̵right]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4189:67: warning: This simp argument is unused:
  emCallSlots

Hint: Omit it from the simp argument list.
  simp [emCallLayout, emCallPairIndex, tapeBlocks, e̵m̵C̵a̵l̵l̵S̵l̵o̵t̵s̵,̵
  ̵ ̵ ̵ ̵ ̵Fin.addCases, bufferedCompTM,
  ̲  ̲ ̲ ̲emCallIdleTM, emCallRightTM, emCallTrackTM]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4199:2: warning: 'all_goals
  repeat
    first
    | rfl
    | omega
    | split' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4200:2: warning: 'all_goals
  repeat
    first
    | rfl
    | omega
    | split' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4199:12: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4200:12: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4213:4: warning: 'all_goals
  repeat
    first
    | rfl
    | omega
    | split' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4214:4: warning: 'all_goals
  repeat
    first
    | rfl
    | omega
    | split' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4213:14: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4214:14: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4489:32: warning: This simp argument is unused:
  emCall_pair_inverse

Hint: Omit it from the simp argument list.
  simp [emCallCfg, e̵m̵C̵a̵l̵l̵_̵p̵a̵i̵r̵_̵i̵n̵v̵e̵r̵s̵e̵,̵ ̵emCallFinishCfg, Cfg.ofWords, stateWord, emCallPairIndex,
  ̲  ̲ ̲ ̲ ̲ ̲emCallPairSelect]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4491:32: warning: This simp argument is unused:
  emCall_pair_inverse

Hint: Omit it from the simp argument list.
  simp [emCallCfg, e̵m̵C̵a̵l̵l̵_̵p̵a̵i̵r̵_̵i̵n̵v̵e̵r̵s̵e̵,̵ ̵emCallFinishCfg, Cfg.ofWords, stateWord, emCallPairIndex,
  ̲  ̲ ̲ ̲ ̲ ̲emCallPairSelect, bufferedCompTM, emCallIdleTM, emCallRightTM, emCallTrackTM]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4622:37: warning: This simp argument is unused:
  hi

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, hs, hi̵,̵ ̵h̵w]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:4622:41: warning: This simp argument is unused:
  hw

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, hs, hi,̵ ̵h̵w̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Loop.lean:5466:33: warning: This simp argument is unused:
  Function.comp_def

Hint: Omit it from the simp argument list.
  simp [List.append_assoc,̵ ̵F̵u̵n̵c̵t̵i̵o̵n̵.̵c̵o̵m̵p̵_̵d̵e̵f̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
[12/58] TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction
[13/58] TCSlib/Complexity/TuringMachine/Robustness/SingleTape
[14/58] TCSlib/Complexity/TuringMachine/Robustness/Bidirectional
[15/58] TCSlib/Complexity/ClassP/DTIME
[16/58] TCSlib/Complexity/TuringMachine/Encoding
[17/58] TCSlib/Complexity/ClassP/TimeConstructible
[18/58] TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule
[19/58] TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:473:6: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:501:37: warning: This simp argument is unused:
  hl

Hint: Omit it from the simp argument list.
  simp [inputTag, clippedMove, hl̵,̵ ̵h̵r]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:533:45: warning: This simp argument is unused:
  hw

Hint: Omit it from the simp argument list.
  simp [h̵w̵,̵ ̵Cfg.workTapeSymbols]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:535:49: warning: This simp argument is unused:
  hw

Hint: Omit it from the simp argument list.
  simp [hz, h̵w̵,̵ ̵Function.update_of_ne hn]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:535:53: warning: This simp argument is unused:
  Function.update_of_ne hn

Hint: Omit it from the simp argument list.
  simp [hz, hw,̵ ̵F̵u̵n̵c̵t̵i̵o̵n̵.̵u̵p̵d̵a̵t̵e̵_̵o̵f̵_̵n̵e̵ ̵h̵n̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:614:44: warning: This simp argument is unused:
  List.append_nil

Hint: Omit it from the simp argument list.
  simp only [payloadZone, List.reverse_cons, FinTM.sweepFold_append, he, ih, FinTM.sweepFold,
  ̲  ̲ ̲ ̲ ̲ ̲p̵a̵y̵l̵o̵a̵d̵B̵a̵c̵k̵w̵a̵r̵d̵_̵r̵o̵w̵,̵ ̵L̵i̵s̵t̵.̵a̵p̵p̵e̵n̵d̵_̵n̵i̵l̵]̵p̲a̲y̲l̲o̲a̲d̲B̲a̲c̲k̲w̲a̲r̲d̲_̲r̲o̲w̲]̲

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:764:27: warning: This simp argument is unused:
  act

Hint: Omit it from the simp argument list.
  simp only [a̵c̵t̵,̵ ̵Option.map_none]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:768:21: warning: This simp argument is unused:
  act

Hint: Omit it from the simp argument list.
  simp only [a̵c̵t̵,̵ ̵Option.map_some, Function.update_self]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:769:21: warning: This simp argument is unused:
  act

Hint: Omit it from the simp argument list.
  simp only [a̵c̵t̵,̵ ̵Option.map_some, Function.update_of_ne hz]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:774:29: warning: This simp argument is unused:
  act

Hint: Omit it from the simp argument list.
  simp only [a̵c̵t̵,̵ ̵Option.toList_none, List.append_nil]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:776:21: warning: This simp argument is unused:
  act

Hint: Omit it from the simp argument list.
  simp only [a̵c̵t̵,̵ ̵Option.toList_some, clockTape_append]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:784:65: warning: This simp argument is unused:
  ho

Hint: Omit it from the simp argument list.
  simp [act, List.length_append,̵ ̵h̵o̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:784:73: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:784:73: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean:881:25: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
[20/58] TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:191:25: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:217:4: warning: This simp argument is unused:
  SignType.coe_neg_one

Hint: Omit it from the simp argument list.
  simp only [setupWrite, moveInputPos_zero, SignType.coe_zero, add_zero, S̵i̵g̵n̵T̵y̵p̵e̵.̵c̵o̵e̵_̵n̵e̵g̵_̵o̵n̵e̵,̵ ̵zero_add]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:249:56: warning: This simp argument is unused:
  SignType.coe_one

Hint: Omit it from the simp argument list.
  simp only [setupWrite, SignType.coe_zero, add_zero, S̵i̵g̵n̵T̵y̵p̵e̵.̵c̵o̵e̵_̵o̵n̵e̵,̵ ̵copyGuide_next]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:313:64: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:313:23: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:313:35: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:313:64: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:405:16: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:405:41: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:405:16: warning: 'simp [SignType.cast]' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:405:41: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:600:25: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:686:26: warning: This simp argument is unused:
  hg

Hint: Omit it from the simp argument list.
  simp_all ̵[̵h̵g̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:731:38: warning: This simp argument is unused:
  layoutPhase

Hint: Omit it from the simp argument list.
  simp [layoutP̵h̵a̵s̵e̵,̵ ̵l̵a̵y̵o̵u̵t̵Move, hi]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:747:36: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:747:48: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:756:32: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:778:15: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only [F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵,̵ ̵Nat.cast_add, Nat.cast_one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:778:27: warning: This simp argument is unused:
  Nat.cast_add

Hint: Omit it from the simp argument list.
  simp only [Fin.val_mk, Nat.cast_a̵d̵d̵,̵ ̵N̵a̵t̵.̵c̵a̵s̵t̵_̵one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:778:41: warning: This simp argument is unused:
  Nat.cast_one

Hint: Omit it from the simp argument list.
  simp only [Fin.val_mk, Nat.cast_add,̵ ̵N̵a̵t̵.̵c̵a̵s̵t̵_̵o̵n̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:879:17: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only [F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵,̵ ̵Nat.cast_add, Nat.cast_one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:879:29: warning: This simp argument is unused:
  Nat.cast_add

Hint: Omit it from the simp argument list.
  simp only [Fin.val_mk, Nat.cast_a̵d̵d̵,̵ ̵N̵a̵t̵.̵c̵a̵s̵t̵_̵one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean:879:43: warning: This simp argument is unused:
  Nat.cast_one

Hint: Omit it from the simp argument list.
  simp only [Fin.val_mk, Nat.cast_add,̵ ̵N̵a̵t̵.̵c̵a̵s̵t̵_̵o̵n̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
[21/58] TCSlib/Complexity/TuringMachine/Robustness/ObliviousLedger
[22/58] TCSlib/Complexity/TuringMachine/Robustness/Oblivious
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:182:25: warning: This simp argument is unused:
  hc

Hint: Omit it from the simp argument list.
  simp only [hfirst,̵ ̵h̵c̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:240:19: warning: This simp argument is unused:
  hd

Hint: Omit it from the simp argument list.
  simp only [h̵d̵,̵ ̵SignType.cast, add_zero, ← sub_eq_add_neg, hleft', hc]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:379:26: warning: This simp argument is unused:
  hw

Hint: Omit it from the simp argument list.
  simp [setupWrite, h̵w̵,̵ ̵Function.update_of_ne hz, h, hz]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:379:30: warning: This simp argument is unused:
  Function.update_of_ne hz

Hint: Omit it from the simp argument list.
  simp [setupWrite, hw, F̵u̵n̵c̵t̵i̵o̵n̵.̵u̵p̵d̵a̵t̵e̵_̵o̵f̵_̵n̵e̵ ̵h̵z̵,̵ ̵h, hz]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:737:38: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:743:6: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:756:24: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:756:24: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:695:64: warning: This simp argument is unused:
  Fin.reduceFinMk

Hint: Omit it from the simp argument list.
  simp only [prepInvariant, Action.apply, Fin.addCases_right, Fin.r̵e̵d̵u̵c̵e̵F̵i̵n̵M̵k̵,̵ ̵F̵i̵n̵.̵val_one, Nat.one_ne_zero,
  ̲  ̲ ̲ ̲ ̲ ̲show (2 : ℕ) ≠ 0 by decide, ↓reduceIte,
  ̵  ̵ ̵ ̵ ̵ ̵SignType.coe_zero, add_zero]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:695:111: warning: This simp argument is unused:
  show (2 : ℕ) ≠ 0 by decide

Hint: Omit it from the simp argument list.
  simp only [prepInvariant, Action.apply, Fin.addCases_right, Fin.reduceFinMk, Fin.val_one,
  ̲  ̲ ̲ ̲ ̲ ̲Nat.one_ne_zero, s̵h̵o̵w̵ ̵(̵2̵ ̵:̵ ̵ℕ̵)̵ ̵≠̵ ̵0̵ ̵b̵y̵ ̵d̵e̵c̵i̵d̵e̵,̵ ̵↓reduceIte, SignType.coe_zero, add_zero]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:725:52: warning: This simp argument is unused:
  hi

Hint: Omit it from the simp argument list.
  simp only [obliviousSchedule, obliviousVisit, h̵i̵,̵ ̵setupWrite, Option.toList_none, List.append_nil]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:729:52: warning: This simp argument is unused:
  hi

Hint: Omit it from the simp argument list.
  simp only [obliviousSchedule, obliviousVisit, h̵i̵,̵ ̵setupWrite, Option.toList_none, List.append_nil]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
[23/58] TCSlib/Complexity/ClassP/P
[24/58] TCSlib/Complexity/ClassP/ModelInvariance
[25/58] TCSlib/Complexity/ClassP/Examples
[26/58] TCSlib/Complexity/TuringMachine/Build/Primitives
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2492:42: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2498:72: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2492:42: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2498:72: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2490:82: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2520:72: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2520:72: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2508:38: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2512:38: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2570:29: warning: This simp argument is unused:
  List.append_nil

Hint: Omit it from the simp argument list.
  simp only [↓reduceIte,̵ ̵L̵i̵s̵t̵.̵a̵p̵p̵e̵n̵d̵_̵n̵i̵l̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2533:42: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2538:42: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2541:42: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2580:46: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2604:43: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2927:25: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:2927:25: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3026:59: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3174:34: warning: This simp argument is unused:
  splitRestoreScan

Hint: Omit it from the simp argument list.
  simp [Action.apply,̵ ̵s̵p̵l̵i̵t̵R̵e̵s̵t̵o̵r̵e̵S̵c̵a̵n̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3204:79: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3204:79: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3267:6: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3312:52: warning: This simp argument is unused:
  Nat.cast_one

Hint: Omit it from the simp argument list.
  simp only [List.length_nil, Nat.zero_add, N̵a̵t̵.̵c̵a̵s̵t̵_̵o̵n̵e̵,̵ ̵Fin.ext_iff, Fin.val_one] at h₁

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3312:66: warning: This simp argument is unused:
  Fin.ext_iff

Hint: Omit it from the simp argument list.
  simp only [List.length_nil, Nat.zero_add, Nat.cast_one, Fin.e̵x̵t̵_̵i̵f̵f̵,̵ ̵F̵i̵n̵.̵val_one] at h₁

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3312:79: warning: This simp argument is unused:
  Fin.val_one

Hint: Omit it from the simp argument list.
  simp only [List.length_nil, Nat.zero_add, Nat.cast_one, Fin.ext_iff,̵ ̵F̵i̵n̵.̵v̵a̵l̵_̵o̵n̵e̵] at h₁

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3352:20: warning: This simp argument is unused:
  MultiTapeTM.step

Hint: Omit it from the simp argument list.
  simp [M̵u̵l̵t̵i̵T̵a̵p̵e̵T̵M̵.̵s̵t̵e̵p̵,̵ ̵catalogPolyUnaryTM, Action.apply, catalogPolyCfg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3352:38: warning: This simp argument is unused:
  catalogPolyUnaryTM

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.step, c̵a̵t̵a̵l̵o̵g̵P̵o̵l̵y̵U̵n̵a̵r̵y̵T̵M̵,̵ ̵Action.apply, catalogPolyCfg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3352:72: warning: This simp argument is unused:
  catalogPolyCfg

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.step, catalogPolyUnaryTM, Action.apply,̵ ̵c̵a̵t̵a̵l̵o̵g̵P̵o̵l̵y̵C̵f̵g̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3353:10: warning: This simp argument is unused:
  MultiTapeTM.step

Hint: Omit it from the simp argument list.
  simp [M̵u̵l̵t̵i̵T̵a̵p̵e̵T̵M̵.̵s̵t̵e̵p̵,̵ ̵catalogPolyUnaryTM, Action.apply, catalogPolyCfg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3353:28: warning: This simp argument is unused:
  catalogPolyUnaryTM

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.step, c̵a̵t̵a̵l̵o̵g̵P̵o̵l̵y̵U̵n̵a̵r̵y̵T̵M̵,̵ ̵Action.apply, catalogPolyCfg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3353:62: warning: This simp argument is unused:
  catalogPolyCfg

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.step, catalogPolyUnaryTM, Action.apply,̵ ̵c̵a̵t̵a̵l̵o̵g̵P̵o̵l̵y̵C̵f̵g̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:3400:23: warning: This simp argument is unused:
  Prod.mk.injEq

Hint: Omit it from the simp argument list.
  simp only [ht0, MultiTapeTM.runFrom_zero, splitRestoreScan, Cfg.ofWords,
      Option.some.injEq,̵ ̵P̵r̵o̵d̵.̵m̵k̵.̵i̵n̵j̵E̵q̵] at hstate

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:4917:8: warning: This simp argument is unused:
  Fin.val_zero

Hint: Omit it from the simp argument list.
  simp only [emitterClearCfg, MultiTapeTM.step, emitterClearTM, Cfg.workTapeSymbols,
          Fin.val_z̵e̵r̵o,̵ ̵F̵i̵n.̵v̵a̵l̵_̵o̵n̵e, Nat.one_ne_zero, ↓reduceIte, hmark, reduceCtorEq, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:4917:22: warning: This simp argument is unused:
  Fin.val_one

Hint: Omit it from the simp argument list.
  simp only [emitterClearCfg, MultiTapeTM.step, emitterClearTM, Cfg.workTapeSymbols,
          Fin.val_zero, F̵i̵n̵.̵v̵a̵l̵_̵o̵n̵e̵,̵ ̵Nat.one_ne_zero, ↓reduceIte, hmark, reduceCtorEq, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:4917:35: warning: This simp argument is unused:
  Nat.one_ne_zero

Hint: Omit it from the simp argument list.
  simp only [emitterClearCfg, MultiTapeTM.step, emitterClearTM, Cfg.workTapeSymbols,
          Fin.val_zero, Fin.val_one, N̵a̵t̵.̵o̵n̵e̵_̵n̵e̵_̵z̵e̵r̵o̵,̵ ̵↓reduceIte, hmark, reduceCtorEq, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:4959:27: warning: This simp argument is unused:
  Fin.val_zero

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emitterClearCfg, emitterClearTM, Cfg.workTapeSymbols, F̵i̵n̵.̵v̵a̵l̵_̵z̵e̵r̵o̵,̵ ̵Fin.val_one,
  ̲  ̲ ̲ ̲ ̲ ̲Nat.one_ne_zero, ↓reduceIte, hmark, reduceCtorEq, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:4959:41: warning: This simp argument is unused:
  Fin.val_one

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emitterClearCfg, emitterClearTM,
  ̵  ̵ ̵ ̵ ̵ ̵Cfg.workTapeSymbols, Fin.val_zero,
  ̲ F̵i̵n̵.̵v̵a̵l̵_̵o̵n̵e̵,̵  ̲ ̲ ̲ ̲Nat.one_ne_zero, ↓reduceIte, hmark,
  ̵  ̵ ̵ ̵ ̵ ̵reduceCtorEq, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:4959:54: warning: This simp argument is unused:
  Nat.one_ne_zero

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emitterClearCfg, emitterClearTM, Cfg.workTapeSymbols, Fin.val_zero,
  ̲  ̲ ̲ ̲ ̲ ̲Fin.val_one, N̵a̵t̵.̵o̵n̵e̵_̵n̵e̵_̵z̵e̵r̵o̵,̵ ̵↓reduceIte, hmark, reduceCtorEq, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5006:8: warning: This simp argument is unused:
  Fin.val_zero

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emitterClearCfg, emitterClearTM, Cfg.workTapeSymbols,
          Fin.val_z̵e̵r̵o,̵ ̵F̵i̵n.̵v̵a̵l̵_̵o̵n̵e, Nat.one_ne_zero, ↓reduceIte, hblank, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5006:22: warning: This simp argument is unused:
  Fin.val_one

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emitterClearCfg, emitterClearTM, Cfg.workTapeSymbols,
          Fin.val_zero, F̵i̵n̵.̵v̵a̵l̵_̵o̵n̵e̵,̵ ̵Nat.one_ne_zero, ↓reduceIte, hblank, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5006:35: warning: This simp argument is unused:
  Nat.one_ne_zero

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emitterClearCfg, emitterClearTM, Cfg.workTapeSymbols,
          Fin.val_zero, Fin.val_one, N̵a̵t̵.̵o̵n̵e̵_̵n̵e̵_̵z̵e̵r̵o̵,̵ ̵↓reduceIte, hblank, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5038:6: warning: This simp argument is unused:
  Fin.val_zero

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emitterClearCfg, emitterClearTM, Cfg.workTapeSymbols, F̵i̵n̵.̵v̵a̵l̵_̵z̵e̵r̵o̵,̵ ̵Fin.val_one,
  ̲  ̲ ̲ ̲ ̲ ̲Nat.one_ne_zero, ↓reduceIte, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5038:20: warning: This simp argument is unused:
  Fin.val_one

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emitterClearCfg, emitterClearTM, Cfg.workTapeSymbols, Fin.val_zero,
  ̲  ̲ ̲ ̲ ̲ ̲F̵i̵n̵.̵v̵a̵l̵_̵o̵n̵e̵,̵ ̵Nat.one_ne_zero, ↓reduceIte, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5038:33: warning: This simp argument is unused:
  Nat.one_ne_zero

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, emitterClearCfg, emitterClearTM, Cfg.workTapeSymbols, Fin.val_zero,
  ̲  ̲ ̲ ̲ ̲ ̲Fin.val_one, N̵a̵t̵.̵o̵n̵e̵_̵n̵e̵_̵z̵e̵r̵o̵,̵ ̵↓reduceIte, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5067:23: warning: This simp argument is unused:
  min_le_right

Hint: Omit it from the simp argument list.
  simp [emitterSpan, m̵i̵n̵_̵l̵e̵_̵r̵i̵g̵h̵t̵,̵ ̵le_max_right]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5067:37: warning: This simp argument is unused:
  le_max_right

Hint: Omit it from the simp argument list.
  simp [emitterSpan, min_le_right,̵ ̵l̵e̵_̵m̵a̵x̵_̵r̵i̵g̵h̵t̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5255:25: warning: This simp argument is unused:
  hspan

Hint: Omit it from the simp argument list.
  simp [emitterSpan, h̵s̵p̵a̵n̵,̵ ̵bufferTape, hn, List.getElem?_eq_none hlen]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5256:25: warning: This simp argument is unused:
  hspan

Hint: Omit it from the simp argument list.
  simp [emitterSpan, h̵s̵p̵a̵n̵,̵ ̵bufferTape, hn]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5573:37: warning: This simp argument is unused:
  emitterBankCfg

Hint: Omit it from the simp argument list.
  simp [e̵m̵i̵t̵t̵e̵r̵B̵a̵n̵k̵C̵f̵g̵,̵ ̵MultiTapeTM.step, hs, controlAction, Action.apply]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5573:53: warning: This simp argument is unused:
  MultiTapeTM.step

Hint: Omit it from the simp argument list.
  simp [emitterBankCfg, M̵u̵l̵t̵i̵T̵a̵p̵e̵T̵M̵.̵s̵t̵e̵p̵,̵ ̵hs, controlAction, Action.apply]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5573:90: warning: This simp argument is unused:
  Action.apply

Hint: Omit it from the simp argument list.
  simp [emitterBankCfg, MultiTapeTM.step, hs, controlAction,̵ ̵A̵c̵t̵i̵o̵n̵.̵a̵p̵p̵l̵y̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5578:44: warning: This simp argument is unused:
  MultiTapeTM.step

Hint: Omit it from the simp argument list.
  simp [emitterBankCfg, emitterSlots, M̵u̵l̵t̵i̵T̵a̵p̵e̵T̵M̵.̵s̵t̵e̵p̵,̵ ̵hs, controlAction, Action.apply, -Fin.natAdd_eq_addNat]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5583:44: warning: This simp argument is unused:
  MultiTapeTM.step

Hint: Omit it from the simp argument list.
  simp [emitterBankCfg, emitterSlots, M̵u̵l̵t̵i̵T̵a̵p̵e̵T̵M̵.̵s̵t̵e̵p̵,̵ ̵hs, controlAction, Action.apply, -Fin.natAdd_eq_addNat]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5589:44: warning: This simp argument is unused:
  MultiTapeTM.step

Hint: Omit it from the simp argument list.
  simp [emitterBankCfg, emitterSlots, M̵u̵l̵t̵i̵T̵a̵p̵e̵T̵M̵.̵s̵t̵e̵p̵,̵ ̵hs, controlAction, Action.apply, -Fin.natAdd_eq_addNat]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5594:44: warning: This simp argument is unused:
  MultiTapeTM.step

Hint: Omit it from the simp argument list.
  simp [emitterBankCfg, emitterSlots, M̵u̵l̵t̵i̵T̵a̵p̵e̵T̵M̵.̵s̵t̵e̵p̵,̵ ̵hs, controlAction, Action.apply, -Fin.natAdd_eq_addNat]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5802:27: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:5802:27: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:6228:52: warning: This simp argument is unused:
  emitterP2PrepareCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, e̵m̵i̵t̵t̵e̵r̵P̵2̵P̵r̵e̵p̵a̵r̵e̵C̵f̵g̵,̵ ̵hwrite]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:6229:52: warning: This simp argument is unused:
  emitterP2PrepareCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply,̵ ̵e̵m̵i̵t̵t̵e̵r̵P̵2̵P̵r̵e̵p̵a̵r̵e̵C̵f̵g̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:6264:37: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:6284:50: warning: This simp argument is unused:
  emitterP2PrepareCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply,̵ ̵e̵m̵i̵t̵t̵e̵r̵P̵2̵P̵r̵e̵p̵a̵r̵e̵C̵f̵g̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:6295:52: warning: This simp argument is unused:
  emitterP2PrepareCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, e̵m̵i̵t̵t̵e̵r̵P̵2̵P̵r̵e̵p̵a̵r̵e̵C̵f̵g̵,̵ ̵sub_eq_add_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:6314:50: warning: This simp argument is unused:
  emitterP2PrepareCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply,̵ ̵e̵m̵i̵t̵t̵e̵r̵P̵2̵P̵r̵e̵p̵a̵r̵e̵C̵f̵g̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:6325:52: warning: This simp argument is unused:
  emitterP2PrepareCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, e̵m̵i̵t̵t̵e̵r̵P̵2̵P̵r̵e̵p̵a̵r̵e̵C̵f̵g̵,̵ ̵sub_eq_add_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:6705:74: warning: This simp argument is unused:
  emitterP2RightIndex

Hint: Omit it from the simp argument list.
  simp [emitterP2LeftIndex,̵ ̵e̵m̵i̵t̵t̵e̵r̵P̵2̵R̵i̵g̵h̵t̵I̵n̵d̵e̵x̵] at hv

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:6719:54: warning: This simp argument is unused:
  emitterP2LeftIndex

Hint: Omit it from the simp argument list.
  simp [emitterP2L̵e̵f̵t̵I̵n̵d̵e̵x̵,̵ ̵e̵m̵i̵t̵t̵e̵r̵P̵2̵RightIndex] at hv

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:6726:56: warning: This simp argument is unused:
  emitterP2LeftIndex

Hint: Omit it from the simp argument list.
  simp [emitterP2L̵e̵f̵t̵I̵n̵d̵e̵x̵,̵ ̵e̵m̵i̵t̵t̵e̵r̵P̵2̵RightIndex] at hv

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:7455:6: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:7455:6: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:7458:6: warning: 'simp [MultiTapeTM.step, emitterTokenTM, Action.apply, scanCfg, List.append_assoc]' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:7458:6: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:7509:63: warning: This simp argument is unused:
  List.append_assoc

Hint: Omit it from the simp argument list.
  simp [emitterTokenTM, Action.apply, scanCfg, pairEncode, L̵i̵s̵t̵.̵a̵p̵p̵e̵n̵d̵_̵a̵s̵s̵o̵c̵,̵ ̵hlen]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
[27/58] TCSlib/Complexity/TuringMachine/CodeParser
TCSlib/Complexity/TuringMachine/CodeParser.lean:339:13: warning: This simp argument is unused:
  codeBitsNat_bits

Hint: Omit it from the simp argument list.
  simp only [c̵o̵d̵e̵B̵i̵t̵s̵N̵a̵t̵_̵b̵i̵t̵s̵,̵ ̵List.append_assoc, codeReadFin_append, bind, Option.bind,
  ̵  ̵ ̵ ̵codeReadTable_append,
  ̲  ̲ ̲ ̲List.all_replicate, id_eq, Bool.true_eq, or_true,
  ̵  ̵ ̵ ̵ite_self, ↓reduceIte, pure]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:339:70: warning: This simp argument is unused:
  bind

Hint: Omit it from the simp argument list.
  simp only [codeBitsNat_bits, List.append_assoc, codeReadFin_append, b̵i̵n̵d̵,̵ ̵Option.bind,
      codeReadTable_append, List.all_replicate, id_eq, Bool.true_eq, or_true,
  ̵  ̵ ̵ ̵ite_self, ↓reduceIte,
  ̲  ̲ ̲ ̲pure]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:339:76: warning: This simp argument is unused:
  Option.bind

Hint: Omit it from the simp argument list.
  simp only [codeBitsNat_bits, List.append_assoc, codeReadFin_append, bind, O̵p̵t̵i̵o̵n̵.̵b̵i̵n̵d̵,̵
  ̵ ̵ ̵ ̵ ̵codeReadTable_append,
  ̲  ̲ ̲ ̲List.all_replicate, id_eq, Bool.true_eq, or_true,
  ̵  ̵ ̵ ̵ite_self, ↓reduceIte, pure]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:340:53: warning: This simp argument is unused:
  Bool.true_eq

Hint: Omit it from the simp argument list.
  simp only [codeBitsNat_bits, List.append_assoc, codeReadFin_append, bind, Option.bind,
      codeReadTable_append, List.all_replicate, id_eq, B̵oo̵l̵.̵t̵ru̵e̵_e̵q̵,̵ ̵o̵r̵_̵true,
  ̵  ̵ ̵ ̵ite_self, ↓reduceIte, pure]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:340:67: warning: This simp argument is unused:
  or_true

Hint: Omit it from the simp argument list.
  simp only [codeBitsNat_bits, List.append_assoc, codeReadFin_append, bind, Option.bind,
      codeReadTable_append, List.all_replicate, id_eq, Bool.true_eq, o̵r̵_̵t̵r̵u̵e̵,̵
  ̵ ̵ ̵ ̵ ̵ite_self, ↓reduceIte, pure]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:420:43: warning: This simp argument is unused:
  h₁

Hint: Omit it from the simp argument list.
  simp [pairDecode, h₁̵,̵ ̵h̵₂, h₃] at h

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:420:47: warning: This simp argument is unused:
  h₂

Hint: Omit it from the simp argument list.
  simp [pairDecode, h₁, h₂̵,̵ ̵h̵₃] at h

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/CodeParser.lean:420:51: warning: This simp argument is unused:
  h₃

Hint: Omit it from the simp argument list.
  simp [pairDecode, h₁, h₂,̵ ̵h̵₃̵] at h

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
[28/58] TCSlib/Complexity/TuringMachine/MathlibBridge
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:450:8: warning: This simp argument is unused:
  Function.update_self

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index, F̵u̵n̵c̵t̵i̵o̵n̵.̵u̵p̵d̵a̵t̵e̵_̵s̵e̵l̵f̵,̵ ̵hs]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:456:12: warning: This simp argument is unused:
  Action.apply_workTapes

Hint: Omit it from the simp argument list.
  simp [A̵c̵t̵i̵o̵n̵.̵a̵p̵p̵l̵y̵_̵w̵o̵r̵k̵T̵a̵p̵e̵s̵,̵ ̵bridgeOne, bridgeCfg, hi, hk]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:461:8: warning: This simp argument is unused:
  Function.update_self

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index, F̵u̵n̵c̵t̵i̵o̵n̵.̵u̵p̵d̵a̵t̵e̵_̵s̵e̵l̵f̵,̵ ̵hs,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲SignType.pos_eq_one, SignType.coe_one, List.length_cons, Nat.cast_add, Nat.cast_one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:486:8: warning: This simp argument is unused:
  Function.update_self

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index,
          F̵u̵n̵c̵t̵i̵o̵n̵.̵u̵p̵d̵a̵t̵e̵_̵s̵e̵l̵f̵,̵ ̵SignType.neg_eq_neg_one, SignType.coe_neg_one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:492:12: warning: This simp argument is unused:
  Action.apply_workTapes

Hint: Omit it from the simp argument list.
  simp [A̵c̵t̵i̵o̵n̵.̵a̵p̵p̵l̵y̵_̵w̵o̵r̵k̵T̵a̵p̵e̵s̵,̵ ̵bridgeOne, bridgeCfg, hi, hk]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:497:8: warning: This simp argument is unused:
  Function.update_self

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index,
          F̵u̵n̵c̵t̵i̵o̵n̵.̵u̵p̵d̵a̵t̵e̵_̵s̵e̵l̵f̵,̵ ̵SignType.neg_eq_neg_one, SignType.coe_neg_one, SignType.zero_eq_zero, SignType.coe_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲List.length_cons, Nat.cast_add, Nat.cast_one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:498:50: warning: This simp argument is unused:
  List.length_cons

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index,
          Function.update_self, SignType.neg_eq_neg_one, SignType.coe_neg_one, SignType.zero_eq_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲SignType.coe_zero, L̵i̵s̵t̵.̵l̵e̵n̵g̵t̵h̵_̵c̵o̵n̵s̵,̵ ̵Nat.cast_add, Nat.cast_one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:498:68: warning: This simp argument is unused:
  Nat.cast_add

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index,
          Function.update_self, SignType.neg_eq_neg_one, SignType.coe_neg_one, SignType.zero_eq_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲SignType.coe_zero, List.length_cons, N̵a̵t̵.̵c̵a̵s̵t̵_̵a̵d̵d̵,̵ ̵Nat.cast_one]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:498:82: warning: This simp argument is unused:
  Nat.cast_one

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index,
          Function.update_self, SignType.neg_eq_neg_one, SignType.coe_neg_one, SignType.zero_eq_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲SignType.coe_zero, List.length_cons, N̵a̵t̵.̵c̵a̵s̵t̵_̵a̵d̵d̵,̵ ̵N̵a̵t̵.̵c̵a̵s̵t̵_̵o̵n̵e̵]̵N̲a̲t̲.̲c̲a̲s̲t̲_̲a̲d̲d̲]̲

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:721:32: warning: This simp argument is unused:
  Num.cast_zero

Hint: Omit it from the simp argument list.
  simp only [Num.to_of_nat,̵ ̵N̵u̵m̵.̵c̵a̵s̵t̵_̵z̵e̵r̵o̵] at hz

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:823:75: warning: This simp argument is unused:
  hk

Hint: Omit it from the simp argument list.
  simp [bridgeStore, PartrecToTM2.K'.elim, hi, hk̵,̵ ̵h̵] at *

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:871:15: warning: This simp argument is unused:
  Action.apply

Hint: Omit it from the simp argument list.
  simp only [̵A̵c̵t̵i̵o̵n̵.̵a̵p̵p̵l̵y̵,̵ ̵b̵r̵i̵d̵g̵e̵C̵f̵g̵,̵[̲b̲r̲i̲d̲g̲e̲C̲f̲g̲,̲ bridgeOne, SignType.zero_eq_zero, moveInputPos_zero]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:871:40: warning: This simp argument is unused:
  bridgeOne

Hint: Omit it from the simp argument list.
  simp only [Action.apply, bridgeCfg, b̵r̵i̵d̵g̵e̵O̵n̵e̵,̵ ̵SignType.zero_eq_zero, moveInputPos_zero]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/MathlibBridge.lean:880:41: warning: This simp argument is unused:
  SignType.coe_zero

Hint: Omit it from the simp argument list.
  simp only [bridgeCfg, bridgeStore_at, ↓reduceIte, List.length_nil, Nat.cast_zero, neg_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲SignType.zero_eq_zero, S̵i̵g̵n̵T̵y̵p̵e̵.̵c̵o̵e̵_̵z̵e̵r̵o̵,̵ ̵SignType.neg_eq_neg_one, SignType.coe_neg_one, zero_add]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
[29/58] TCSlib/Complexity/TuringMachine/UniversalStartup
TCSlib/Complexity/TuringMachine/UniversalStartup.lean:160:54: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalStartup.lean:164:54: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalStartup.lean:190:52: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalStartup.lean:197:54: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalStartup.lean:215:52: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalStartup.lean:274:46: warning: This simp argument is unused:
  VirtualTag

Hint: Omit it from the simp argument list.
  simp_all ̵[̵V̵i̵r̵t̵u̵a̵l̵T̵a̵g̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
[30/58] TCSlib/Complexity/TuringMachine/UniversalInterpreter
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:330:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:353:6: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:378:83: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:439:60: warning: This simp argument is unused:
  zero_add

Hint: Omit it from the simp argument list.
  simp only [universalStateWindow, Nat.cast_zero, add_zero,̵ ̵z̵e̵r̵o̵_̵a̵d̵d̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:503:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:510:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:519:71: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:519:83: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:546:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:553:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:563:39: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:1020:75: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:1021:16: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean:1021:28: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
[31/58] TCSlib/Complexity/TuringMachine/UniversalBlock
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:68:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:83:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:62:10: warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:79:64: warning: This simp argument is unused:
  universalSkipDone

Hint: Omit it from the simp argument list.
  simp [universalInterpreter, universalFour, hr, h, hz,̵ ̵u̵n̵i̵v̵e̵r̵s̵a̵l̵S̵k̵i̵p̵D̵o̵n̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:93:50: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:93:62: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:108:10: warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:164:53: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:164:65: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:185:50: warning: This simp argument is unused:
  Nat.add_zero

Hint: Omit it from the simp argument list.
  simp only [List.length_nil, List.flatMap_nil, Nat.a̵d̵d̵_̵zero,̵ ̵N̵a̵t̵.̵z̵e̵r̵o̵_add,
  ̵  ̵ ̵ ̵ ̵ ̵Nat.cast_zero, add_zero,
  ̲  ̲ ̲ ̲ ̲ ̲MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:244:40: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:271:40: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:289:6: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:289:61: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:289:73: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:289:6: warning: 'simp only [Fin.val_mk, Nat.cast_add, Nat.cast_one]' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:289:61: warning: 'congr 1' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:289:73: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:313:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:321:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:426:40: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/UniversalBlock.lean:574:68: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
[32/58] TCSlib/Complexity/TuringMachine/Universal
TCSlib/Complexity/TuringMachine/Universal.lean:310:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:333:6: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:358:83: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:423:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:430:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:439:71: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:439:83: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:466:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:473:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:483:39: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:617:75: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:618:16: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:618:28: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:640:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:655:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:634:10: warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
TCSlib/Complexity/TuringMachine/Universal.lean:651:85: warning: This simp argument is unused:
  universalSkipDone

Hint: Omit it from the simp argument list.
  simp [timedCutInterpreter, universalInterpreter, universalFour, hr, h, hz,̵ ̵u̵n̵i̵v̵e̵r̵s̵a̵l̵S̵k̵i̵p̵D̵o̵n̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Universal.lean:665:50: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:665:62: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:680:10: warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
TCSlib/Complexity/TuringMachine/Universal.lean:736:53: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:736:65: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:757:50: warning: This simp argument is unused:
  Nat.add_zero

Hint: Omit it from the simp argument list.
  simp only [List.length_nil, List.flatMap_nil, Nat.a̵d̵d̵_̵zero,̵ ̵N̵a̵t̵.̵z̵e̵r̵o̵_add,
  ̵  ̵ ̵ ̵ ̵ ̵Nat.cast_zero, add_zero,
  ̲  ̲ ̲ ̲ ̲ ̲MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Universal.lean:816:40: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:843:40: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:861:6: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:861:61: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:861:73: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:861:6: warning: 'simp only [Fin.val_mk, Nat.cast_add, Nat.cast_one]' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:861:61: warning: 'congr 1' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:861:73: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:885:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:893:15: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:1002:40: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Universal.lean:1102:68: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Universal.lean:1480:16: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1480:34: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1480:61: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1480:16: warning: 'apply Fin.ext' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1480:34: warning: 'simp only [Fin.val_mk]' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1480:61: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1574:30: warning: This simp argument is unused:
  Nat.reduceAdd

Hint: Omit it from the simp argument list.
  simp only [Nat.add_assoc,̵ ̵N̵a̵t̵.̵r̵e̵d̵u̵c̵e̵A̵d̵d̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Universal.lean:1579:16: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1579:34: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1579:61: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1579:16: warning: 'apply Fin.ext' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1579:34: warning: 'simp only [Fin.val_mk]' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1579:61: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Universal.lean:1602:28: warning: This simp argument is unused:
  Nat.reduceAdd

Hint: Omit it from the simp argument list.
  simp only [Nat.add_assoc,̵ ̵N̵a̵t̵.̵r̵e̵d̵u̵c̵e̵A̵d̵d̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Universal.lean:1604:43: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Universal.lean:1604:10: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:1604:28: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:1604:55: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Universal.lean:2274:46: warning: This simp argument is unused:
  VirtualTag

Hint: Omit it from the simp argument list.
  simp_all ̵[̵V̵i̵r̵t̵u̵a̵l̵T̵a̵g̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
[33/58] TCSlib/Complexity/Uncomputability/Computable
[34/58] TCSlib/Complexity/Uncomputability/Diagonalization
[35/58] TCSlib/Complexity/Uncomputability/Halting
[36/58] TCSlib/Complexity/TuringMachine/Nondeterministic
[37/58] TCSlib/Complexity/Formulas/CNF
[38/58] TCSlib/Complexity/Formulas/CNFEncoding
[39/58] TCSlib/Complexity/Formulas/DNF
[40/58] TCSlib/Complexity/ClassNP/PolyTime
[41/58] TCSlib/Complexity/ClassNP/PolyTimePairing
[42/58] TCSlib/Complexity/ClassNP/NP
[43/58] TCSlib/Complexity/ClassNP/CoNP
[44/58] TCSlib/Complexity/ClassNP/EXP
TCSlib/Complexity/ClassNP/EXP.lean:2755:66: warning: This simp argument is unused:
  bufferTape

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.initCfg, Cfg.init, a3LoadCfg,̵ ̵b̵u̵f̵f̵e̵r̵T̵a̵p̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/EXP.lean:2781:88: warning: This simp argument is unused:
  bufferTape

Hint: Omit it from the simp argument list.
  simp [Action.apply, Cfg.ofWords, stateWord, b̵u̵f̵f̵e̵r̵T̵a̵p̵e̵,̵ ̵hz]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/EXP.lean:2799:66: warning: This simp argument is unused:
  a3LoadCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, a̵3̵L̵o̵a̵d̵C̵f̵g̵,̵ ̵hz]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/EXP.lean:2800:66: warning: This simp argument is unused:
  a3LoadCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, a̵3̵L̵o̵a̵d̵C̵f̵g̵,̵ ̵hz, sub_eq_add_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
[45/58] TCSlib/Complexity/ClassNP/Reductions
[46/58] TCSlib/Complexity/ClassNP/NTIME
TCSlib/Complexity/ClassNP/NTIME.lean:215:8: warning: `Set.eq_empty_iff_forall_not_mem` has been deprecated: Use `Set.eq_empty_iff_forall_notMem` instead
[47/58] TCSlib/Complexity/ClassNP/Nondeterminism
TCSlib/Complexity/ClassNP/Nondeterminism.lean:3247:8: warning: This simp argument is unused:
  Fin.val_zero

Hint: Omit it from the simp argument list.
  simp only [e3cClearCfg, MultiTapeTM.step, e3cClearTM, Cfg.workTapeSymbols, F̵i̵n̵.̵v̵a̵l̵_̵z̵e̵r̵o̵,̵ ̵Fin.val_one,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲Nat.one_ne_zero, ↓reduceIte, hmark, reduceCtorEq, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:3247:22: warning: This simp argument is unused:
  Fin.val_one

Hint: Omit it from the simp argument list.
  simp only [e3cClearCfg, MultiTapeTM.step, e3cClearTM, Cfg.workTapeSymbols, Fin.val_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲F̵i̵n̵.̵v̵a̵l̵_̵o̵n̵e̵,̵ ̵Nat.one_ne_zero, ↓reduceIte, hmark, reduceCtorEq, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:3247:35: warning: This simp argument is unused:
  Nat.one_ne_zero

Hint: Omit it from the simp argument list.
  simp only [e3cClearCfg, MultiTapeTM.step, e3cClearTM, Cfg.workTapeSymbols, Fin.val_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲Fin.val_one, N̵a̵t̵.̵o̵n̵e̵_̵n̵e̵_̵z̵e̵r̵o̵,̵ ̵↓reduceIte, hmark, reduceCtorEq, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:3289:27: warning: This simp argument is unused:
  Fin.val_zero

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, e3cClearCfg, e3cClearTM, Cfg.workTapeSymbols, F̵i̵n̵.̵v̵a̵l̵_̵z̵e̵r̵o̵,̵ ̵Fin.val_one,
  ̲  ̲ ̲ ̲ ̲ ̲Nat.one_ne_zero, ↓reduceIte, hmark, reduceCtorEq, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:3289:41: warning: This simp argument is unused:
  Fin.val_one

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, e3cClearCfg, e3cClearTM,
  ̵  ̵ ̵ ̵ ̵ ̵Cfg.workTapeSymbols, Fin.val_zero,
  ̲ F̵i̵n̵.̵v̵a̵l̵_̵o̵n̵e̵,̵  ̲ ̲ ̲ ̲Nat.one_ne_zero, ↓reduceIte, hmark,
  ̵  ̵ ̵ ̵ ̵ ̵reduceCtorEq, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:3289:54: warning: This simp argument is unused:
  Nat.one_ne_zero

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, e3cClearCfg, e3cClearTM, Cfg.workTapeSymbols, Fin.val_zero,
  ̲  ̲ ̲ ̲ ̲ ̲Fin.val_one, N̵a̵t̵.̵o̵n̵e̵_̵n̵e̵_̵z̵e̵r̵o̵,̵ ̵↓reduceIte, hmark, reduceCtorEq, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:3336:8: warning: This simp argument is unused:
  Fin.val_zero

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, e3cClearCfg, e3cClearTM, Cfg.workTapeSymbols, F̵i̵n̵.̵v̵a̵l̵_̵z̵e̵r̵o̵,̵ ̵Fin.val_one,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲Nat.one_ne_zero, ↓reduceIte, hblank, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:3336:22: warning: This simp argument is unused:
  Fin.val_one

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, e3cClearCfg, e3cClearTM, Cfg.workTapeSymbols, Fin.val_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲F̵i̵n̵.̵v̵a̵l̵_̵o̵n̵e̵,̵ ̵Nat.one_ne_zero, ↓reduceIte, hblank, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:3336:35: warning: This simp argument is unused:
  Nat.one_ne_zero

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, e3cClearCfg, e3cClearTM, Cfg.workTapeSymbols, Fin.val_zero,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲Fin.val_one, N̵a̵t̵.̵o̵n̵e̵_̵n̵e̵_̵z̵e̵r̵o̵,̵ ̵↓reduceIte, hblank, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:3368:6: warning: This simp argument is unused:
  Fin.val_zero

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, e3cClearCfg, e3cClearTM, Cfg.workTapeSymbols, F̵i̵n̵.̵v̵a̵l̵_̵z̵e̵r̵o̵,̵ ̵Fin.val_one,
  ̲  ̲ ̲ ̲ ̲ ̲Nat.one_ne_zero, ↓reduceIte, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:3368:20: warning: This simp argument is unused:
  Fin.val_one

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, e3cClearCfg, e3cClearTM, Cfg.workTapeSymbols, Fin.val_zero,
  ̲  ̲ ̲ ̲ ̲ ̲F̵i̵n̵.̵v̵a̵l̵_̵o̵n̵e̵,̵ ̵Nat.one_ne_zero, ↓reduceIte, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:3368:33: warning: This simp argument is unused:
  Nat.one_ne_zero

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.step, e3cClearCfg, e3cClearTM, Cfg.workTapeSymbols, Fin.val_zero,
  ̲  ̲ ̲ ̲ ̲ ̲Fin.val_one, N̵a̵t̵.̵o̵n̵e̵_̵n̵e̵_̵z̵e̵r̵o̵,̵ ̵↓reduceIte, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:3397:19: warning: This simp argument is unused:
  min_le_right

Hint: Omit it from the simp argument list.
  simp [e3cSpan, m̵i̵n̵_̵l̵e̵_̵r̵i̵g̵h̵t̵,̵ ̵le_max_right]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:3397:33: warning: This simp argument is unused:
  le_max_right

Hint: Omit it from the simp argument list.
  simp [e3cSpan, min_le_right,̵ ̵l̵e̵_̵m̵a̵x̵_̵r̵i̵g̵h̵t̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:3585:21: warning: This simp argument is unused:
  hspan

Hint: Omit it from the simp argument list.
  simp [e3cSpan, h̵s̵p̵a̵n̵,̵ ̵bufferTape, hn, List.getElem?_eq_none hlen]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:3586:21: warning: This simp argument is unused:
  hspan

Hint: Omit it from the simp argument list.
  simp [e3cSpan, h̵s̵p̵a̵n̵,̵ ̵bufferTape, hn]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:3695:62: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:4147:27: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:4147:27: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:4656:52: warning: This simp argument is unused:
  bufferTape

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.initCfg, Cfg.init, a2LoadCfg,̵ ̵b̵u̵f̵f̵e̵r̵T̵a̵p̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:4686:36: warning: This simp argument is unused:
  a2LoadCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, a̵2̵L̵o̵a̵d̵C̵f̵g̵,̵ ̵sub_eq_add_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5176:40: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5182:42: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5198:78: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5168:55: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5169:54: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5171:61: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5180:55: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5188:58: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5176:40: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5182:42: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5198:78: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5216:65: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5222:58: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5238:60: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5210:55: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5211:54: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5212:61: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5221:55: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5228:58: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5216:65: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5222:58: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5238:60: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5249:55: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5283:34: warning: This simp argument is unused:
  a3nEqCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply,̵ ̵a̵3̵n̵E̵q̵C̵f̵g̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5294:36: warning: This simp argument is unused:
  a3nEqCfg

Hint: Omit it from the simp argument list.
  simp [Action.apply, a̵3̵n̵E̵q̵C̵f̵g̵,̵ ̵sub_eq_add_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5333:17: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only ̵[̵F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5304:55: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5306:42: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5314:42: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5316:92: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5359:51: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5352:65: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5359:51: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5387:63: warning: This simp argument is unused:
  bufferTape

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.initCfg, Cfg.init, a3nEqCfg,̵ ̵b̵u̵f̵f̵e̵r̵T̵a̵p̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/Nondeterminism.lean:5556:63: warning: This simp argument is unused:
  Bool.true_eq

Hint: Omit it from the simp argument list.
  simp only [MultiTapeTM.indicator, hmem, Function.comp_apply, a3n_fst, a3n_snd, a3n_concat, hw,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲hx', pairDecode_pairEncode, Option.map_some, Option.getD_some, Option.isSome_some, B̵o̵o̵l̵.̵t̵r̵u̵e̵_̵e̵q̵,̵if_true,
          e3c_bits_injective.eq_iff, decide_eq_true_eq, ite_and]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
[48/58] TCSlib/Complexity/ClassNP/SAT
TCSlib/Complexity/ClassNP/SAT.lean:164:51: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:176:47: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:371:33: warning: Try `simp at h` instead of `simpa using h`

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/ClassNP/SAT.lean:494:63: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:646:56: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:671:59: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:708:55: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:718:58: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:729:88: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:758:60: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/ClassNP/SAT.lean:769:27: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/ClassNP/SAT.lean:791:91: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/ClassNP/SAT.lean:758:60: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/ClassNP/SAT.lean:769:27: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/ClassNP/SAT.lean:791:91: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/ClassNP/SAT.lean:787:84: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:847:56: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/ClassNP/SAT.lean:847:56: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/ClassNP/SAT.lean:830:63: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:854:51: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:915:48: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:955:55: warning: This simp argument is unused:
  FinTM.bufferTape

Hint: Omit it from the simp argument list.
  simp [captureCfg, MultiTapeTM.initCfg, Cfg.init,̵ ̵F̵i̵n̵T̵M̵.̵b̵u̵f̵f̵e̵r̵T̵a̵p̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:1017:26: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:1296:8: warning: This simp argument is unused:
  satSafeValue

Hint: Omit it from the simp argument list.
  simp [satVerdict, satSplitValid, satSplit, hs, pairDecode_pairEncode, s̵a̵t̵S̵a̵f̵e̵V̵a̵l̵u̵e̵,̵ ̵satGood, satInstance,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲satWitness, satSyntax_spec, hp, CNF.decode, CNF.fallback, satWidth]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:1296:22: warning: This simp argument is unused:
  satGood

Hint: Omit it from the simp argument list.
  simp [satVerdict, satSplitValid, satSplit, hs, pairDecode_pairEncode,
  ̵  ̵ ̵ ̵ ̵ ̵ ̵ ̵satSafeValue,
  ̲ s̵a̵t̵G̵o̵o̵d̵,̵  ̲ ̲ ̲ ̲ ̲ ̲satInstance, satWitness, satSyntax_spec, hp,
  ̵  ̵ ̵ ̵ ̵ ̵ ̵ ̵CNF.decode, CNF.fallback, satWidth]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:1296:44: warning: This simp argument is unused:
  satWitness

Hint: Omit it from the simp argument list.
  simp [satVerdict, satSplitValid, satSplit, hs, pairDecode_pairEncode, satSafeValue, satGood,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲satInstance, s̵a̵t̵W̵i̵t̵n̵e̵s̵s̵,̵ ̵satSyntax_spec, hp, CNF.decode, CNF.fallback, satWidth]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:1395:80: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:1523:11: warning: Try `simp at h` instead of `simpa using h`

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/ClassNP/SAT.lean:1990:12: warning: This simp argument is unused:
  he

Hint: Omit it from the simp argument list.
  simp [h̵e̵,̵ ̵satRedCounter_read, show r < n by omega]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:1987:39: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:2001:17: warning: unused variable `hj`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
TCSlib/Complexity/ClassNP/SAT.lean:2007:52: warning: This simp argument is unused:
  max_eq_left

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.runFrom_zero, m̵a̵x̵_̵e̵q̵_̵l̵e̵f̵t̵,̵ ̵*]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:2022:59: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/ClassNP/SAT.lean:2022:59: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/ClassNP/SAT.lean:2077:19: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/ClassNP/SAT.lean:2077:19: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/ClassNP/SAT.lean:2042:40: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:2087:82: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:2091:73: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:2093:41: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:2150:40: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/ClassNP/SAT.lean:2150:40: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/ClassNP/SAT.lean:2156:51: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:2175:47: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:2208:48: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:2228:28: warning: This simp argument is unused:
  Function.update_of_ne hz

Hint: Omit it from the simp argument list.
  simp [satRedBuffer, hz, F̵u̵n̵c̵t̵i̵o̵n̵.̵u̵p̵d̵a̵t̵e̵_̵o̵f̵_̵n̵e̵ ̵h̵z̵,̵ ̵FinTM.bufferTape]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:2315:19: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/ClassNP/SAT.lean:2501:52: warning: This simp argument is unused:
  List.append_assoc

Hint: Omit it from the simp argument list.
  simp [satStreamTail, CNF.serializeClause, hp, L̵i̵s̵t̵.̵a̵p̵p̵e̵n̵d̵_̵a̵s̵s̵o̵c̵,̵ ̵Nat.add_assoc]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:2543:69: warning: This simp argument is unused:
  List.append_assoc

Hint: Omit it from the simp argument list.
  simp [satStreamRun, satStreamClause, CNF.serializeClause, hp₁, L̵i̵s̵t̵.̵a̵p̵p̵e̵n̵d̵_̵a̵s̵s̵o̵c̵,̵ ̵Nat.add_assoc]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:2606:52: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:2633:44: warning: This simp argument is unused:
  List.append_nil

Hint: Omit it from the simp argument list.
  simp only [List.length_nil, Nat.zero_add,̵ ̵L̵i̵s̵t̵.̵a̵p̵p̵e̵n̵d̵_̵n̵i̵l̵] at h

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:2648:24: warning: This simp argument is unused:
  Function.comp_apply

Hint: Omit it from the simp argument list.
  simp only [satStreamRun, ih, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map,
  ̲  ̲ ̲ ̲ ̲ ̲F̵u̵n̵c̵t̵i̵o̵n̵.̵c̵o̵m̵p̵_̵a̵p̵p̵l̵y̵,̵ ̵Function.iterate_zero_apply, Function.iterate_succ_apply]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:2683:29: warning: This simp argument is unused:
  Nat.mul_add

Hint: Omit it from the simp argument list.
  simp [List.length_flatMap, Nat.m̵u̵l̵_̵add,̵ ̵N̵a̵t̵.̵a̵d̵d̵_assoc, Nat.add_comm, Nat.add_left_comm,
  ̵  ̵ ̵ ̵Nat.mul_comm]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:2684:18: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:2968:67: warning: This simp argument is unused:
  FinTM.bufferTape

Hint: Omit it from the simp argument list.
  simp [captureCfg, MultiTapeTM.initCfg, Cfg.init,̵ ̵F̵i̵n̵T̵M̵.̵b̵u̵f̵f̵e̵r̵T̵a̵p̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:3094:30: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/ClassNP/SAT.lean:3094:30: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/ClassNP/SAT.lean:3093:82: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:3234:90: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/ClassNP/SAT.lean:3234:90: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/ClassNP/SAT.lean:3234:39: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:3301:33: warning: This simp argument is unused:
  Function.comp_def

Hint: Omit it from the simp argument list.
  simp [F̵u̵n̵c̵t̵i̵o̵n̵.̵c̵o̵m̵p̵_̵d̵e̵f̵,̵ ̵h]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:3396:73: warning: This simp argument is unused:
  List.append_assoc

Hint: Omit it from the simp argument list.
  simp [satRedAction, satRedCfg, Action.apply, List.replicate_succ',̵ ̵L̵i̵s̵t̵.̵a̵p̵p̵e̵n̵d̵_̵a̵s̵s̵o̵c̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:3440:68: warning: This simp argument is unused:
  hp

Hint: Omit it from the simp argument list.
  simp [satStreamCanonical, satSyntax_spec, CNF.decode, h̵p̵,̵ ̵sat_parse_repr hp,
  ̲  ̲ ̲ ̲CNF.parse_serialize]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:3459:25: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/ClassNP/SAT.lean:3459:25: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/ClassNP/SAT.lean:3656:26: warning: This simp argument is unused:
  hw

Hint: Omit it from the simp argument list.
  simp only [satDropTM, h̵w̵,̵ ̵Option.isSome_none, Bool.false_eq_true, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:3656:30: warning: This simp argument is unused:
  Option.isSome_none

Hint: Omit it from the simp argument list.
  simp only [satDropTM, hw, O̵p̵t̵i̵o̵n̵.̵i̵s̵S̵o̵m̵e̵_̵n̵o̵n̵e̵,̵ ̵Bool.false_eq_true, ↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:3656:50: warning: This simp argument is unused:
  Bool.false_eq_true

Hint: Omit it from the simp argument list.
  simp only [satDropTM, hw, Option.isSome_none, B̵o̵o̵l̵.̵f̵a̵l̵s̵e̵_̵e̵q̵_̵t̵r̵u̵e̵,̵ ̵↓reduceIte]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:3656:70: warning: This simp argument is unused:
  ↓reduceIte

Hint: Omit it from the simp argument list.
  simp only [satDropTM, hw, Option.isSome_none, Bool.false_eq_true,̵ ̵↓̵r̵e̵d̵u̵c̵e̵I̵t̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:3662:45: warning: This simp argument is unused:
  he

Hint: Omit it from the simp argument list.
  simp [satDropCfg, Cfg.workTapeSymbols, h̵e̵,̵ ̵satRedCounter_read, show r < n by omega]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:3762:82: warning: This simp argument is unused:
  FinTM.bufferTape

Hint: Omit it from the simp argument list.
  simp [satDropCfg, satRedCounter, MultiTapeTM.initCfg, Cfg.init,̵ ̵F̵i̵n̵T̵M̵.̵b̵u̵f̵f̵e̵r̵T̵a̵p̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:3750:29: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:3950:50: warning: This simp argument is unused:
  List.replicate_succ

Hint: Omit it from the simp argument list.
  simp_all [satReqStep, satReqEmit, satReqPack, satStreamWord,
              satStreamRound, List.replicate_succ',̵ ̵L̵i̵s̵t̵.̵r̵e̵p̵l̵i̵c̵a̵t̵e̵_̵s̵u̵c̵c̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:3974:74: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:4104:55: warning: This simp argument is unused:
  sub_eq_add_neg

Hint: Omit it from the simp argument list.
  simp [satAppendCfg, Action.apply, SignType.cast, s̵u̵b̵_̵e̵q̵_̵a̵d̵d̵_̵n̵e̵g̵,̵ ̵add_assoc]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:4104:71: warning: This simp argument is unused:
  add_assoc

Hint: Omit it from the simp argument list.
  simp [satAppendCfg, Action.apply, SignType.cast, sub_eq_add_neg,̵ ̵a̵d̵d̵_̵a̵s̵s̵o̵c̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:4145:34: warning: This simp argument is unused:
  List.getElem?_cons_zero

Hint: Omit it from the simp argument list.
  simp only [satAppendTM, hr,̵ ̵L̵i̵s̵t̵.̵g̵e̵t̵E̵l̵e̵m̵?̵_̵c̵o̵n̵s̵_̵z̵e̵r̵o̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:4151:67: warning: This simp argument is unused:
  sub_eq_add_neg

Hint: Omit it from the simp argument list.
  simp [satAppendCfg, Action.apply, SignType.cast, s̵u̵b̵_̵e̵q̵_̵a̵d̵d̵_̵n̵e̵g̵,̵ ̵add_assoc]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:4175:69: warning: This simp argument is unused:
  add_assoc

Hint: Omit it from the simp argument list.
  simp [satAppendCfg, Action.apply, SignType.cast, sub_eq_add_neg,̵ ̵a̵d̵d̵_̵a̵s̵s̵o̵c̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:4312:62: warning: This simp argument is unused:
  hi

Hint: Omit it from the simp argument list.
  simp [satPadCfg, Cfg.ofWords,̵ ̵h̵i̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:4541:43: warning: This simp argument is unused:
  Nat.mul_assoc

Hint: Omit it from the simp argument list.
  simp only [Nat.add_mul, Nat.one_mul, N̵a̵t̵.̵m̵u̵l̵_̵a̵s̵s̵o̵c̵,̵ ̵two_mul]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:4588:55: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/ClassNP/SAT.lean:4660:79: warning: This simp argument is unused:
  FinTM.bufferTape

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.initCfg, Cfg.init, Cfg.ofWords, stateWord,̵ ̵F̵i̵n̵T̵M̵.̵b̵u̵f̵f̵e̵r̵T̵a̵p̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/ClassNP/SAT.lean:4675:30: warning: This simp argument is unused:
  Nat.mul_one

Hint: Omit it from the simp argument list.
  simp only [Nat.add_mul,̵ ̵N̵a̵t̵.̵m̵u̵l̵_̵o̵n̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
[49/58] TCSlib/Complexity/ClassNP/TMSAT
[50/58] TCSlib/Complexity/CookLevin/Snapshot
[51/58] TCSlib/Complexity/CookLevin/Hardness
TCSlib/Complexity/CookLevin/Hardness.lean:2011:35: warning: This simp argument is unused:
  hw

Hint: Omit it from the simp argument list.
  simp only ̵[̵h̵w̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:2011:39: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/CookLevin/Hardness.lean:2035:12: warning: This simp argument is unused:
  MultiTapeTM.step

Hint: Omit it from the simp argument list.
  simp [M̵u̵l̵t̵i̵T̵a̵p̵e̵T̵M̵.̵s̵t̵e̵p̵,̵ ̵hs, FinTM.controlAction, Action.apply]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:2035:55: warning: This simp argument is unused:
  Action.apply

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.step, hs, FinTM.controlAction,̵ ̵A̵c̵t̵i̵o̵n̵.̵a̵p̵p̵l̵y̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:2038:23: warning: This simp argument is unused:
  MultiTapeTM.step

Hint: Omit it from the simp argument list.
  simp [clBankCfg, M̵u̵l̵t̵i̵T̵a̵p̵e̵T̵M̵.̵s̵t̵e̵p̵,̵ ̵hs, FinTM.controlAction, Action.apply]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:2041:23: warning: This simp argument is unused:
  MultiTapeTM.step

Hint: Omit it from the simp argument list.
  simp [clBankCfg, M̵u̵l̵t̵i̵T̵a̵p̵e̵T̵M̵.̵s̵t̵e̵p̵,̵ ̵hs, FinTM.controlAction, Action.apply]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:2171:31: warning: This simp argument is unused:
  MultiTapeTM.step_of_halt hs

Hint: Omit it from the simp argument list.
  simp [clMoves, hs,̵ ̵M̵u̵l̵t̵i̵T̵a̵p̵e̵T̵M̵.̵s̵t̵e̵p̵_̵o̵f̵_̵h̵a̵l̵t̵ ̵h̵s̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:2480:13: warning: This simp argument is unused:
  Fin.cases_zero

Hint: Omit it from the simp argument list.
  simp only [clCopyTM, ↓reduceIte, clCopyCfg, Cfg.workTapeSymbols, clTwo, F̵i̵n̵.̵c̵a̵s̵e̵s̵_̵z̵e̵r̵o̵,̵ ̵hr]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:2486:43: warning: This simp argument is unused:
  Fin.cases_zero

Hint: Omit it from the simp argument list.
  simp only [clCopyTM, show (1 : Fin 5) ≠ 0 by decide, ↓reduceIte, clCopyCfg, Cfg.workTapeSymbols,
  ̲  ̲ ̲ ̲clTwo, F̵i̵n̵.̵c̵a̵s̵e̵s̵_̵z̵e̵r̵o̵,̵ ̵hr, Option.getD_some]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:2520:13: warning: This simp argument is unused:
  Fin.cases_zero

Hint: Omit it from the simp argument list.
  simp only [clCopyTM, ↓reduceIte, clCopyCfg, Cfg.workTapeSymbols, clTwo, F̵i̵n̵.̵c̵a̵s̵e̵s̵_̵z̵e̵r̵o̵,̵ ̵hr]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:2558:59: warning: This simp argument is unused:
  Fin.cases_zero

Hint: Omit it from the simp argument list.
  simp only [clCopyTM, show (3 : Fin 5) ≠ 0 by decide, show (3 : Fin 5) ≠ 1 by decide,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲show (3 : Fin 5) ≠ 2 by decide, ↓reduceIte, clCopyCfg, Cfg.workTapeSymbols, clTwo, F̵i̵n̵.̵c̵a̵s̵e̵s̵_̵z̵e̵r̵o̵,̵ ̵hr]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:2560:47: warning: This simp argument is unused:
  clCopyCfg

Hint: Omit it from the simp argument list.
  simp [clTwo, c̵l̵C̵o̵p̵y̵C̵f̵g̵,̵ ̵Action.apply]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:2561:47: warning: This simp argument is unused:
  clCopyCfg

Hint: Omit it from the simp argument list.
  simp [clTwo, c̵l̵C̵o̵p̵y̵C̵f̵g̵,̵ ̵Action.apply, sub_eq_add_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:2784:8: warning: Try this: intro j hj q hq heq
TCSlib/Complexity/CookLevin/Hardness.lean:2916:62: warning: This simp argument is unused:
  List.append_assoc

Hint: Omit it from the simp argument list.
  simp [pairEncode, List.flatMap_cons,̵ ̵L̵i̵s̵t̵.̵a̵p̵p̵e̵n̵d̵_̵a̵s̵s̵o̵c̵] at ⊢ ih

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:3251:95: warning: This simp argument is unused:
  clRight_ne_left

Hint: Omit it from the simp argument list.
  simp [clRecCfg, clRecClockIndex, Action.apply, FinTM.tapeBlocks, clLeft_ne_right,
  ̲ c̵l̵R̵i̵g̵h̵t̵_̵n̵e̵_̵l̵e̵f̵t̵,̵  ̲ ̲-Fin.natAdd_eq_addNat]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:3254:97: warning: This simp argument is unused:
  clRight_ne_left

Hint: Omit it from the simp argument list.
  simp [clRecCfg, clRecClockIndex, Action.apply, FinTM.tapeBlocks, clLeft_ne_right,
  ̲ c̵l̵R̵i̵g̵h̵t̵_̵n̵e̵_̵l̵e̵f̵t̵,̵  ̲ ̲ ̲ ̲-Fin.natAdd_eq_addNat]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:3260:73: warning: This simp argument is unused:
  clLeft_ne_right

Hint: Omit it from the simp argument list.
  simp [clRecCfg, clRecClockIndex, Action.apply, FinTM.tapeBlocks, c̵l̵L̵e̵f̵t̵_̵n̵e̵_̵r̵i̵g̵h̵t̵,̵ ̵clRight_ne_left,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲ ̲ ̲-Fin.natAdd_eq_addNat]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:3260:90: warning: This simp argument is unused:
  clRight_ne_left

Hint: Omit it from the simp argument list.
  simp [clRecCfg, clRecClockIndex, Action.apply, FinTM.tapeBlocks, clLeft_ne_right,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲ ̲ ̲c̵l̵R̵i̵g̵h̵t̵_̵n̵e̵_̵l̵e̵f̵t̵,̵ ̵-Fin.natAdd_eq_addNat]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:3261:82: warning: This simp argument is unused:
  clLeft_ne_right

Hint: Omit it from the simp argument list.
  simp [clRecCfg, clRecClockIndex, Action.apply, FinTM.tapeBlocks, c̵l̵L̵e̵f̵t̵_̵n̵e̵_̵r̵i̵g̵h̵t̵,̵ ̵clRight_ne_left,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲-Fin.natAdd_eq_addNat]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:3880:46: warning: This simp argument is unused:
  ↓reduceIte

Hint: Omit it from the simp argument list.
  simp only [clSignedWords,̵ ̵↓̵r̵e̵d̵u̵c̵e̵I̵t̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:3960:29: warning: This simp argument is unused:
  Option.bind_some

Hint: Omit it from the simp argument list.
  simp only [List.length_cons, clReadFields, clFields, clPair_append, p̵a̵i̵r̵D̵e̵c̵o̵d̵e̵_̵p̵a̵i̵r̵E̵n̵c̵o̵d̵e̵,̵ ̵O̵p̵t̵i̵o̵n̵.̵b̵i̵n̵d̵_̵s̵o̵m̵e̵]̵p̲a̲i̲r̲D̲e̲c̲o̲d̲e̲_̲p̲a̲i̲r̲E̲n̲c̲o̲d̲e̲]̲

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:4031:57: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/CookLevin/Hardness.lean:4112:77: warning: This simp argument is unused:
  if_false

Hint: Omit it from the simp argument list.
  simp only [clReadTM, clReadCfg, Cfg.workTapeSymbols, clTwo,
  ̵  ̵ ̵ ̵ ̵ ̵ ̵ ̵show (1 : Fin 2) ≠ 0 by decide,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲↓reduceIte, hr, Option.some_ne_none,̵ ̵i̵f̵_̵f̵a̵l̵s̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:4136:27: warning: This simp argument is unused:
  ih

Hint: Omit it from the simp argument list.
  simp ̵[̵i̵h̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:4208:49: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/CookLevin/Hardness.lean:4425:65: warning: This simp argument is unused:
  if_false

Hint: Omit it from the simp argument list.
  simp only [clWipeTM, clWipeCfg, Cfg.workTapeSymbols, clTwo, ↓reduceIte,
          show (1 : Fin 2) ≠ 0 by decide, hr, Option.some_ne_none,̵ ̵i̵f̵_̵f̵a̵l̵s̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:4457:59: warning: This simp argument is unused:
  if_false

Hint: Omit it from the simp argument list.
  simp only [clWipeTM, show (1 : Fin 3) ≠ 0 by decide, i̵f̵_̵f̵a̵l̵s̵e̵,̵ ̵if_true, clWipeCfg, Cfg.workTapeSymbols,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲clTwo, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte, hr, Option.some_ne_none]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:4457:69: warning: This simp argument is unused:
  if_true

Hint: Omit it from the simp argument list.
  simp only [clWipeTM, show (1 : Fin 3) ≠ 0 by decide, if_false, i̵f̵_̵t̵r̵u̵e̵,̵clWipeCfg, Cfg.workTapeSymbols,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲clTwo, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte, hr, Option.some_ne_none]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:4869:22: warning: This simp argument is unused:
  funext_iff

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.step, clInputTM, clInputCfg, Cfg.inputSymbol, Action.apply, m̵o̵v̵e̵I̵n̵p̵u̵t̵P̵o̵s̵,̵ ̵f̵u̵n̵e̵x̵t̵_̵i̵f̵f̵]̵m̲o̲v̲e̲I̲n̲p̲u̲t̲P̲o̲s̲]̲

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:4894:82: warning: This simp argument is unused:
  funext_iff

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.initCfg, Cfg.init, clInputCfg, clInputTM,̵ ̵f̵u̵n̵e̵x̵t̵_̵i̵f̵f̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:4902:8: warning: This simp argument is unused:
  FinTM.moveInputPos_neg_val

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.step, clInputTM, clInputCfg, Cfg.inputSymbol, Action.apply, F̵i̵n̵T̵M̵.̵m̵o̵v̵e̵I̵n̵p̵u̵t̵P̵o̵s̵_̵n̵e̵g̵_̵v̵a̵l̵,̵ ̵funext_iff,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲sub_eq_add_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:4902:36: warning: This simp argument is unused:
  funext_iff

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.step, clInputTM, clInputCfg, Cfg.inputSymbol, Action.apply,
          FinTM.moveInputPos_neg_val, f̵u̵n̵e̵x̵t̵_̵i̵f̵f̵,̵ ̵sub_eq_add_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:5317:59: warning: This simp argument is unused:
  hne

Hint: Omit it from the simp argument list.
  simp [clMatchCmpSelect, clMatchCmpIndex, hne,̵ ̵h̵n̵e̵.symm,
  ̵  ̵ ̵ ̵-Fin.natAdd_eq_addNat]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:5517:54: warning: This simp argument is unused:
  ↓reduceIte

Hint: Omit it from the simp argument list.
  simp only [clMatchWords,̵ ̵↓̵r̵e̵d̵u̵c̵e̵I̵t̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:5554:54: warning: This simp argument is unused:
  Nat.add_assoc

Hint: Omit it from the simp argument list.
  simp [clRows, ih, List.append_assoc,̵ ̵N̵a̵t̵.̵a̵d̵d̵_̵a̵s̵s̵o̵c̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:5678:64: warning: This simp argument is unused:
  if_false

Hint: Omit it from the simp argument list.
  simp only [clTwo, ↓reduceIte, show (1 : Fin 2) ≠ 0 by decide, i̵f̵_̵f̵a̵l̵s̵e̵,̵ ̵clNum_bits]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:5713:62: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/CookLevin/Hardness.lean:5831:90: warning: This simp argument is unused:
  funext_iff

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.step, clReplayTM, clReplayCfg, Cfg.workTapeSymbols, Action.apply,̵ ̵f̵u̵n̵e̵x̵t̵_̵i̵f̵f̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:5862:90: warning: This simp argument is unused:
  funext_iff

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.step, clReplayTM, clReplayCfg, Cfg.workTapeSymbols, Action.apply,̵ ̵f̵u̵n̵e̵x̵t̵_̵i̵f̵f̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:5873:44: warning: This simp argument is unused:
  funext_iff

Hint: Omit it from the simp argument list.
  simp [Action.apply,̵ ̵f̵u̵n̵e̵x̵t̵_̵i̵f̵f̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:5886:69: warning: This simp argument is unused:
  funext_iff

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.step, clReplayTM, clReplayCfg, Action.apply, f̵u̵n̵e̵x̵t̵_̵i̵f̵f̵,̵ ̵sub_eq_add_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:6185:96: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/CookLevin/Hardness.lean:6391:69: warning: This simp argument is unused:
  funext_iff

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.step, clReplayTM, clReplayCfg, Action.apply, f̵u̵n̵e̵x̵t̵_̵i̵f̵f̵,̵ ̵sub_eq_add_neg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:6642:62: warning: This simp argument is unused:
  ↓reduceIte

Hint: Omit it from the simp argument list.
  simp only [target, clSearchTarget, clTwo,̵ ̵↓̵r̵e̵d̵u̵c̵e̵I̵t̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:7078:63: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/CookLevin/Hardness.lean:7134:65: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/CookLevin/Hardness.lean:7383:63: warning: This simp argument is unused:
  hi

Hint: Omit it from the simp argument list.
  simp [clA5PadCfg, Cfg.ofWords,̵ ̵h̵i̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:7611:43: warning: This simp argument is unused:
  Nat.mul_assoc

Hint: Omit it from the simp argument list.
  simp only [Nat.add_mul, Nat.one_mul, N̵a̵t̵.̵m̵u̵l̵_̵a̵s̵s̵o̵c̵,̵ ̵two_mul]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:7687:65: warning: This simp argument is unused:
  FinTM.bufferTape

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.initCfg, Cfg.init, Cfg.ofWords, stateWord,̵ ̵F̵i̵n̵T̵M̵.̵b̵u̵f̵f̵e̵r̵T̵a̵p̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:7781:65: warning: This simp argument is unused:
  FinTM.bufferTape

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.initCfg, Cfg.init, Cfg.ofWords, stateWord,̵ ̵F̵i̵n̵T̵M̵.̵b̵u̵f̵f̵e̵r̵T̵a̵p̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:7910:90: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/CookLevin/Hardness.lean:7910:90: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/CookLevin/Hardness.lean:7910:39: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/CookLevin/Hardness.lean:7977:33: warning: This simp argument is unused:
  Function.comp_def

Hint: Omit it from the simp argument list.
  simp [F̵u̵n̵c̵t̵i̵o̵n̵.̵c̵o̵m̵p̵_̵d̵e̵f̵,̵ ̵h]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:8000:108: warning: This simp argument is unused:
  Fin.val_mk

Hint: Omit it from the simp argument list.
  simp only [clRepeatWords,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲Fin.addCases_left, stateWord, F̵i̵n̵.̵v̵a̵l̵_̵m̵k̵,̵ ̵if_pos rfl, if_pos True.intro]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:8000:120: warning: This simp argument is unused:
  if_pos rfl

Hint: Omit it from the simp argument list.
  simp only [clRepeatWords,
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲Fin.addCases_left, stateWord, Fin.val_mk, if_pos r̵f̵l̵,̵ ̵i̵f̵_̵p̵o̵s̵ ̵True.intro]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:8373:69: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/CookLevin/Hardness.lean:8644:57: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/CookLevin/Hardness.lean:8672:45: warning: This simp argument is unused:
  Nat.mul_comm

Hint: Omit it from the simp argument list.
  simp [pairEncode, List.length_flatMap,̵ ̵N̵a̵t̵.̵m̵u̵l̵_̵c̵o̵m̵m̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:8672:59: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/CookLevin/Hardness.lean:8739:64: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/CookLevin/Hardness.lean:9069:15: warning: This simp argument is unused:
  List.getElem?_range h

Hint: Omit it from the simp argument list.
  simp [h,̵ ̵L̵i̵s̵t̵.̵g̵e̵t̵E̵l̵e̵m̵?̵_̵r̵a̵n̵g̵e̵ ̵h̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:9077:10: warning: This simp argument is unused:
  h0

Hint: Omit it from the simp argument list.
  simp [h̵0̵,̵ ̵rangeGet, h0]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:9077:14: warning: This simp argument is unused:
  rangeGet

Hint: Omit it from the simp argument list.
  simp [h0, r̵a̵n̵g̵e̵G̵e̵t̵,̵ ̵h0]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:9084:18: warning: This simp argument is unused:
  rangeGet

Hint: Omit it from the simp argument list.
  simp [h2,̵ ̵r̵a̵n̵g̵e̵G̵e̵t̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/CookLevin/Hardness.lean:9087:20: warning: This simp argument is unused:
  rangeGet

Hint: Omit it from the simp argument list.
  simp [h3,̵ ̵r̵a̵n̵g̵e̵G̵e̵t̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
[52/58] TCSlib/Complexity/ClassNP/Tautology
TCSlib/Complexity/ClassNP/Tautology.lean:1271:8: warning: declaration uses 'sorry'
[53/58] TCSlib/Complexity/TuringMachine
TCSlib/Complexity/TuringMachine.lean:6:0: error: object file '/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/sweep-oleans-merge2/TCSlib/Complexity/TuringMachine/UnaryTape.olean' of module TCSlib.Complexity.TuringMachine.UnaryTape does not exist
FAIL(TCSlib/Complexity/TuringMachine): lean exited with status 1
FAIL(TCSlib/Complexity/TuringMachine): error diagnostics reported
FAIL(TCSlib/Complexity/TuringMachine): no fresh .olean produced
SWEEP_FAIL at TCSlib/Complexity/TuringMachine
--- RESUME from module 53 (UnaryTape) after order extension to 65; modules 1-52 fresh-checked above ---
[53/65] TCSlib/Complexity/TuringMachine/UnaryTape
[54/65] TCSlib/Complexity/TuringMachine/CounterProg
[55/65] TCSlib/Complexity/TuringMachine/CounterProgRun
[56/65] TCSlib/Complexity/TuringMachine
[57/65] TCSlib/Complexity/ClassP
[58/65] TCSlib/Complexity/Uncomputability
[59/65] TCSlib/Complexity/Formulas
[60/65] TCSlib/Complexity/CookLevin
[61/65] TCSlib/Complexity/ClassNP/Transducer
[62/65] TCSlib/Complexity/ClassNP/CounterProgPolyTime
[63/65] TCSlib/Complexity/ClassNP/PClosure
[64/65] TCSlib/Complexity/ClassNP/ExpPoly
[65/65] TCSlib/Complexity/ClassNP
SWEEP_OK 65/65 (1-52 fresh above, 53-65 this pass) 2026-10-06T18:21:58Z

## ===== TCSlib/Complexity/ClassNP/PolyTimePairing.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.ClassNP.PolyTime
import TCSlib.Complexity.TuringMachine.Build.Primitives

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Polynomial-time pairing, projections and branching

Closure facts for the function class FP (`Complexity.PolyTimeComputable`, implicit
throughout [AB09, ch. 2]) needed when a reduction must keep its input while computing
from it: constant functions, the threaded payload map, pairing of two polynomial-time
functions through `Turing.pairEncode`, the total pair projections, concatenation,
Boolean branching and length tests, and the unary length maps `x ↦ 1^|x|` and
`x ↦ 1^{C(|x|+1)^d}` (the input of a uniformity machine, [AB09, Def 6.12]). All are
assembled from the proved machine catalog of
`TCSlib.Complexity.TuringMachine.Build.Primitives`. The closure facts for the class `P`
built on them are in `TCSlib.Complexity.ClassNP.PClosure`.

## Main definitions

* `Complexity.pairMapSnd` — on `pairEncode a b`, output `pairEncode a (g b)`; malformed
  words go to `[]`.
* `Complexity.pairFstD`, `Complexity.pairSndD` — total pair projections (`[]` on
  malformed words).

## Main results

* `Complexity.polyTimeComputable_of_linear` — a linear-time machine contract gives a
  polynomial-time computable function.
* `Complexity.polyTimeComputable_const` — constant functions are polynomial-time.
* `Complexity.PolyTimeComputable.pairMapSnd` — the threaded payload map preserves
  polynomial time.
* `Complexity.PolyTimeComputable.pairEncode` — `x ↦ pairEncode (f x) (g x)` is
  polynomial-time when `f` and `g` are.
* `Complexity.polyTimeComputable_unary` — `x ↦ 1^|x|` is polynomial-time;
  `Complexity.polyTimeComputable_polyUnary` — so is `x ↦ 1^{C(|x|+1)^d}`.
* `Complexity.PolyTimeComputable.append` — FP is closed under concatenation.
* `Complexity.polyTimeComputable_pairFstD`, `polyTimeComputable_pairSndD`,
  `polyTimeComputable_pairSwap`, `polyTimeComputable_pairConcat`,
  `polyTimeComputable_prepend` — projections and rearrangements of pairs.
* `Complexity.polyTimeComputable_ite`, `polyTimeComputable_and` — Boolean branching.
* `Complexity.polyTimeComputable_lenLe`, `polyTimeComputable_lenEq` — length tests on
  pairs.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Ch. 2; §6.2, Definition 6.12.)
-/

namespace Complexity

open Turing

/-- A function computed by a finite binary machine within a linear bound `a · (n + 1)`
is polynomial-time computable. -/
theorem polyTimeComputable_of_linear {f : List Bool → List Bool}
    (h : ∃ (M : FinTM Bool) (a : ℕ), M.ComputesFunInTime f (fun n => a * (n + 1))) :
    PolyTimeComputable f := by
  obtain ⟨M, a, hM⟩ := h
  exact ⟨M, a, 1, by simpa only [Nat.pow_one] using hM⟩

/-- Every constant function `fun _ => w` is polynomial-time computable. -/
theorem polyTimeComputable_const (w : List Bool) : PolyTimeComputable (fun _ => w) :=
  polyTimeComputable_of_linear (FinTM.computesFunInTime_const w)

/-- The threaded payload map of `g`: on a pair `pairEncode a b` it outputs
`pairEncode a (g b)` (the first component is carried unchanged), and on a word that is
not a pair it outputs `[]`. -/
def pairMapSnd (g : List Bool → List Bool) (z : List Bool) : List Bool :=
  match pairDecode z with
  | some (a, b) => pairEncode a (g b)
  | none => []

/-- On a pair, the threaded payload map transforms the second component. -/
@[simp]
theorem pairMapSnd_pairEncode (g : List Bool → List Bool) (a b : List Bool) :
    pairMapSnd g (pairEncode a b) = pairEncode a (g b) := by
  simp [pairMapSnd, pairDecode_pairEncode]

/-- If `g` is polynomial-time computable, so is its threaded payload map
`Complexity.pairMapSnd g`.

**Proof sketch.** `Turing.FinTM.computesFunInTime_pairMapSnd` with the monotone
majorant `C (n+1)^c` of `g`'s bound gives a budget `K (n + 1 + C (n+1)^c)`, which is at
most `K (C + 1) (n+1)^(c+1)`. -/
theorem PolyTimeComputable.pairMapSnd {g : List Bool → List Bool}
    (hg : PolyTimeComputable g) : PolyTimeComputable (Complexity.pairMapSnd g) := by
  obtain ⟨G, C, c, hG⟩ := hg
  obtain ⟨M, K, hM⟩ := FinTM.computesFunInTime_pairMapSnd hG
    (by
      intro m n h
      exact Nat.mul_le_mul_left C (Nat.pow_le_pow_left (Nat.add_le_add_right h 1) c))
  refine ⟨M, K * (C + 1), c + 1, fun x => (hM x).mono ?_⟩
  have hn : x.length + 1 ≤ (x.length + 1) ^ (c + 1) := by
    simpa only [Nat.pow_one] using
      Nat.pow_le_pow_right (Nat.succ_pos x.length) (show 1 ≤ c + 1 by omega)
  have hc := Nat.mul_le_mul_left C
    (Nat.pow_le_pow_right (Nat.succ_pos x.length) (Nat.le_succ c))
  calc
    _ ≤ K * ((x.length + 1) ^ (c + 1) + C * (x.length + 1) ^ (c + 1)) :=
      Nat.mul_le_mul_left K (Nat.add_le_add hn hc)
    _ = _ := by ring

/-- Appending to a pair appends to its second component. -/
private lemma pairEncode_append (a b c : List Bool) :
    pairEncode a b ++ c = pairEncode a (b ++ c) := by
  simp [pairEncode, List.append_assoc]

/-- **Pairing two polynomial-time functions is polynomial-time**: if `f` and `g` are
polynomial-time computable, so is `x ↦ pairEncode (f x) (g x)`.

**Proof sketch.** Only the second component of a pair can be transformed in place
(`Complexity.pairMapSnd`), so the first component is built with an empty payload and
then retained. Duplicating `x` (`Turing.FinTM.computesFunInTime_pairDup`) and mapping
the payload gives `H x = pairEncode (f x) []`; duplicating `x` and mapping `H` gives
`s x = pairEncode x (H x)`; duplicating `s x` and mapping `g ∘ fst` gives
`t x = pairEncode (s x) (g x)`. Concatenating the components of `t x`
(`Turing.FinTM.computesFunInTime_pairConcat`) yields
`pairEncode x (pairEncode (f x) (g x))`, whose second component is the result. -/
theorem PolyTimeComputable.pairEncode {f g : List Bool → List Bool}
    (hf : PolyTimeComputable f) (hg : PolyTimeComputable g) :
    PolyTimeComputable (fun x => Turing.pairEncode (f x) (g x)) := by
  have hd := polyTimeComputable_of_linear FinTM.computesFunInTime_pairDup
  have hp := polyTimeComputable_of_linear FinTM.computesFunInTime_pairFst
  have hs := polyTimeComputable_of_linear FinTM.computesFunInTime_pairSnd
  have hc := polyTimeComputable_of_linear FinTM.computesFunInTime_pairConcat
  -- `H x = pairEncode (f x) []`, `s x = pairEncode x (H x)`, `t x = pairEncode (s x) (g x)`
  have hH := (((polyTimeComputable_const []).pairMapSnd).comp hd).comp hf
  have hS := hH.pairMapSnd.comp hd
  have hT := ((hg.comp hp).pairMapSnd.comp hd).comp hS
  -- concatenate, then project the second component
  have h := hs.comp (hc.comp hT)
  convert h using 1
  funext x
  simp only [Function.comp_apply, pairMapSnd_pairEncode, pairDecode_pairEncode,
    Option.map_some, Option.getD_some]
  rw [pairEncode_append, pairEncode_append]
  simp [pairDecode_pairEncode]

/-- The last `true` of `1^(n+1)` is its last letter: stripping it leaves `1ⁿ`. -/
private lemma splitAtLastTrue_replicate_succ (n : ℕ) :
    splitAtLastTrue (List.replicate (n + 1) true) = some (List.replicate n true) := by
  rw [splitAtLastTrue, List.reverse_replicate, List.replicate_succ]
  simp [List.reverse_replicate]

/-- **The unary length map is polynomial-time**: `x ↦ 1^|x|` is polynomial-time
computable. (This is how the input `1ⁿ` of a uniformity machine [AB09, Def 6.12] is
produced from an input of length `n`.)

**Proof sketch.** Pair `x` with `1^(|x|+1)` (the unary polynomial generator at
`1 · (n + 1)¹`, `Turing.FinTM.computesFunInTime_polyUnary`), strip the last `true` of the
second component (`Turing.FinTM.computesFunInTime_stripLast`), and project the second
component (`Turing.FinTM.computesFunInTime_pairSnd`). -/
theorem polyTimeComputable_unary :
    PolyTimeComputable (fun x => List.replicate x.length true) := by
  have hu : PolyTimeComputable (fun x => List.replicate (1 * (x.length + 1) ^ 1) true) := by
    obtain ⟨M, c, hM⟩ := FinTM.computesFunInTime_polyUnary 1 1
    exact ⟨M, c, 2, hM⟩
  have hpair := polyTimeComputable_id.pairEncode hu
  have hstrip : PolyTimeComputable (fun x => match pairDecode x with
      | some (a, v) =>
        match splitAtLastTrue v with
        | some u => Turing.pairEncode a u
        | none => []
      | none => []) := by
    obtain ⟨M, c, hM⟩ := FinTM.computesFunInTime_stripLast
    exact ⟨M, c, 2, hM⟩
  have hs := polyTimeComputable_of_linear FinTM.computesFunInTime_pairSnd
  convert hs.comp (hstrip.comp hpair) using 1
  funext x
  simp only [Function.comp_apply, id, pairDecode_pairEncode, Nat.pow_one, Nat.one_mul,
    splitAtLastTrue_replicate_succ, Option.map_some, Option.getD_some]

/-- **FP is closed under concatenation**: if `f` and `g` are polynomial-time computable,
so is `x ↦ f x ++ g x`. (Pair the two results, `PolyTimeComputable.pairEncode`, then
concatenate the components, `Turing.FinTM.computesFunInTime_pairConcat`.) -/
theorem PolyTimeComputable.append {f g : List Bool → List Bool}
    (hf : PolyTimeComputable f) (hg : PolyTimeComputable g) :
    PolyTimeComputable (fun x => f x ++ g x) := by
  have hc := polyTimeComputable_of_linear FinTM.computesFunInTime_pairConcat
  convert hc.comp (hf.pairEncode hg) using 1
  funext x
  simp [pairDecode_pairEncode]

/-- `x ↦ 1^{C (|x| + 1)^d}` is polynomial-time computable. -/
theorem polyTimeComputable_polyUnary (C d : ℕ) :
    PolyTimeComputable fun x => List.replicate (C * (x.length + 1) ^ d) true := by
  obtain ⟨M, a, hM⟩ := FinTM.computesFunInTime_polyUnary C d
  exact ⟨M, a, d + 1, hM⟩

/-- Prepending a fixed word is polynomial-time. -/
theorem polyTimeComputable_prepend (w : List Bool) : PolyTimeComputable (fun x => w ++ x) :=
  polyTimeComputable_of_linear (FinTM.computesFunInTime_prepend w)

/-! ### Total pair projections -/

/-- The total first projection of a `Turing.pairEncode` pair (`[]` on malformed words). -/
def pairFstD (z : List Bool) : List Bool := ((pairDecode z).map Prod.fst).getD []

/-- The total second projection of a `Turing.pairEncode` pair (`[]` on malformed words). -/
def pairSndD (z : List Bool) : List Bool := ((pairDecode z).map Prod.snd).getD []

/-- The first projection of a pair is its first component. -/
@[simp] theorem pairFstD_pairEncode (a b : List Bool) : pairFstD (pairEncode a b) = a := by
  simp [pairFstD, pairDecode_pairEncode]

/-- The second projection of a pair is its second component. -/
@[simp] theorem pairSndD_pairEncode (a b : List Bool) : pairSndD (pairEncode a b) = b := by
  simp [pairSndD, pairDecode_pairEncode]

/-- The first projection of a word is no longer than the word. -/
theorem length_pairFstD_le (z : List Bool) : (pairFstD z).length ≤ z.length := by
  cases h : pairDecode z with
  | none => simp [pairFstD, h]
  | some ab =>
    obtain ⟨a, b⟩ := ab
    have hz := Turing.eq_pairEncode_of_pairDecode z a b h
    subst hz
    simp [length_pairEncode]
    omega

/-- The first projection is polynomial-time computable. -/
theorem polyTimeComputable_pairFstD : PolyTimeComputable pairFstD :=
  polyTimeComputable_of_linear FinTM.computesFunInTime_pairFst

/-- The second projection is polynomial-time computable. -/
theorem polyTimeComputable_pairSndD : PolyTimeComputable pairSndD :=
  polyTimeComputable_of_linear FinTM.computesFunInTime_pairSnd

/-- Iterated first projections (the root of a nested tuple) are polynomial-time. -/
theorem polyTimeComputable_iterate_pairFstD (n : ℕ) : PolyTimeComputable (pairFstD^[n]) := by
  induction n with
  | zero => simp only [Function.iterate_zero]; exact polyTimeComputable_id
  | succ n ih =>
    rw [Function.iterate_succ']
    exact polyTimeComputable_pairFstD.comp ih

/-- Concatenating the two components of a pair is polynomial-time. -/
theorem polyTimeComputable_pairConcat :
    PolyTimeComputable (fun z => pairFstD z ++ pairSndD z) := by
  have h := polyTimeComputable_of_linear FinTM.computesFunInTime_pairConcat
  convert h using 1
  funext z
  cases hz : pairDecode z with
  | none => simp [pairFstD, pairSndD, hz]
  | some p => cases p; simp [pairFstD, pairSndD, hz]

/-- Swapping the components of a pair is polynomial-time. -/
theorem polyTimeComputable_pairSwap :
    PolyTimeComputable (fun z => pairEncode (pairSndD z) (pairFstD z)) :=
  polyTimeComputable_pairSndD.pairEncode polyTimeComputable_pairFstD

/-! ### Branching and length tests -/

/-- **Polynomial-time branching**: if the test `p` (as a one-bit output) and both branches
are polynomial-time computable, so is `x ↦ if p x then f x else g x`.

**Proof sketch.** The timed branch contract `Turing.FinTM.computesFunInTime_cond` runs
the test, then the selected branch; enlarge the three degrees to their maximum and
absorb the constants. -/
theorem polyTimeComputable_ite {p : List Bool → Bool} {f g : List Bool → List Bool}
    (hp : PolyTimeComputable (fun x => [p x]))
    (hf : PolyTimeComputable f) (hg : PolyTimeComputable g) :
    PolyTimeComputable (fun x => if p x then f x else g x) := by
  obtain ⟨D, A, a, hD⟩ := hp
  obtain ⟨F, B, b, hF⟩ := hf
  obtain ⟨G, C, c, hG⟩ := hg
  obtain ⟨M, K, hM⟩ := FinTM.computesFunInTime_cond hD hF hG
  let e := max a (max b c)
  refine ⟨M, K * (A + B + C + 1), e, fun x => (hM x).mono ?_⟩
  have hpow (d : ℕ) (hd : d ≤ e) : (x.length + 1) ^ d ≤ (x.length + 1) ^ e :=
    Nat.pow_le_pow_right (Nat.succ_pos _) hd
  have ha := Nat.mul_le_mul_left A (hpow a (Nat.le_max_left _ _))
  have hb := Nat.mul_le_mul_left B (hpow b
    ((Nat.le_max_left b c).trans (Nat.le_max_right a (max b c))))
  have hc := Nat.mul_le_mul_left C (hpow c
    ((Nat.le_max_right b c).trans (Nat.le_max_right a (max b c))))
  have hbc : max (B * (x.length + 1) ^ b) (C * (x.length + 1) ^ c) ≤
      B * (x.length + 1) ^ e + C * (x.length + 1) ^ e :=
    max_le (by omega) (by omega)
  have hone := Nat.one_le_pow e (x.length + 1) (Nat.succ_pos _)
  calc
    _ ≤ K * (A * (x.length + 1) ^ e +
        (B * (x.length + 1) ^ e + C * (x.length + 1) ^ e) +
        (x.length + 1) ^ e) :=
      Nat.mul_le_mul_left K (Nat.add_le_add (Nat.add_le_add ha hbc) hone)
    _ = _ := by ring

/-- Polynomial-time Boolean conjunction of two one-bit tests. -/
theorem polyTimeComputable_and {p q : List Bool → Bool}
    (hp : PolyTimeComputable (fun x => [p x])) (hq : PolyTimeComputable (fun x => [q x])) :
    PolyTimeComputable (fun x => [p x && q x]) := by
  convert polyTimeComputable_ite hp hq (polyTimeComputable_const [false]) using 1
  funext x
  cases p x <;> rfl

/-- The length test `|snd z| ≤ |fst z|` on pairs is polynomial-time.

**Proof sketch.** The catalog's threaded length check at `(C, e) = (1, 1)` decides
`|b| ≤ |a| + 1` on `⟨a, b⟩`; apply it to `⟨fst z, 1 :: snd z⟩`. -/
theorem polyTimeComputable_lenLe :
    PolyTimeComputable (fun z => [decide ((pairSndD z).length ≤ (pairFstD z).length)]) := by
  have hchk : PolyTimeComputable (fun x => [match pairDecode x with
      | some (a, b) => decide (b.length ≤ 1 * (a.length + 1) ^ 1)
      | none => false]) := by
    obtain ⟨M, a, hM⟩ := FinTM.computesFunInTime_pairLenCheck 1 1
    exact ⟨M, a, 2, hM⟩
  have hpair : PolyTimeComputable (fun z => pairEncode (pairFstD z) (true :: pairSndD z)) :=
    polyTimeComputable_pairFstD.pairEncode
      ((polyTimeComputable_prepend [true]).comp polyTimeComputable_pairSndD)
  convert hchk.comp hpair using 1
  funext z
  simp [pairDecode_pairEncode]

/-- The length-equality test `|fst z| = |snd z|` on pairs is polynomial-time. -/
theorem polyTimeComputable_lenEq :
    PolyTimeComputable (fun z => [decide ((pairFstD z).length = (pairSndD z).length)]) := by
  have h := polyTimeComputable_and polyTimeComputable_lenLe
    (polyTimeComputable_lenLe.comp polyTimeComputable_pairSwap)
  convert h using 1
  funext z
  simp only [pairFstD_pairEncode, pairSndD_pairEncode]
  congr 1
  by_cases h1 : (pairFstD z).length = (pairSndD z).length
  · simp [h1]
  · rcases Nat.lt_or_gt_of_ne h1 with h2 | h2
    · simp [h1, Nat.not_le_of_lt h2]
    · simp [h1, Nat.not_le_of_lt h2]

end Complexity

## ===== TCSlib/Complexity/TuringMachine/Composition.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Order.Monotone.Defs
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option
import TCSlib.Complexity.TuringMachine.Simulation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Composition of Turing machine computations

Basic computability combinators for the bundled machines: the identity and constant
functions are linear-time computable, and time-bounded computability is closed under
composition. Composition is the load-bearing lemma of the whole development — the
universal machine (phase 3) and the `HALT` reduction (phase 4) are built from it — and
it is the part [AB09] never spells out, dispatching it with "high-level descriptions"
of machines. The Isabelle AFP `Cook_Levin` entry spends a large fraction of its effort
exactly here.

## Design

Composition is stated at the *specification* level (`ComputesFunInTime`), not as an
operator on raw machines: the composed machine is existentially produced. Internally
(proof obligation, not API) the construction simulates `M₁` with its emissions
redirected to a fresh work tape, then simulates `M₂` reading that tape in place of its
input tape.

**Convention obligation status** (phase-1 audit finding 4; phase-2 audit finding 3):
this file does *not* formally discharge the append-only vs read-write output-tape
bridge. Every statement here — hypotheses and conclusions alike — lives in the
append-only model, and [AB09]'s read-write-output machine is not formalized in this
development, so no simulation between the two conventions can even be stated yet. The
obligation is recorded in the plan's decision log as **waived**, with the compensating
restriction that no exact-step-count transfer from [AB09] is ever claimed: every bound
*adapted from the source* carries an existential constant (purely internal results,
such as the oracle lockstep lemmas, are legitimately exact but never cross a
convention), and every result is self-contained in-model. A formal bridge (a
read-write-output machine variant plus a simulation theorem) will be added if and only
if a downstream result needs it. What this file *does* provide is the buffer-and-flush
technique — an emission can be deferred to a work tape and flushed at the end — which
is what delayed or revisable output looks like *within this model*; whether the
append-only convention matches [AB09]'s read-write one remains formally unestablished,
per the waiver.

The generic simulation gadgets this file's machines are assembled from — emission
chains, control actions, disjoint tape-block embeddings with their lockstep run
lemmas, the input-head rewind, and the two-machine branch union — live in
`TCSlib.Complexity.TuringMachine.Simulation` (split out at the epoch-1/epoch-2
boundary, per the epoch-1 audit findings 5 and 11 and the policy file-size
standard); this file keeps only its concrete machines and their theorems.

## Main results

* Time-bounded combinators (all over the binary alphabet):
  `Turing.FinTM.computesFunInTime_id`, `Turing.FinTM.computesFunInTime_const`,
  `Turing.FinTM.computesFunInTime_ifEq`, `Turing.FinTM.computesFunInTime_comp`.
* **Partial (guarded) combinators** — the phase-4 API mandated by the phase-3 audit
  (round 2, finding 10 and Argument F: the total-function composition cannot take
  the partially computing universal evaluator as a component):
  `Turing.FinTM.exists_comp_partial` composes two arbitrary machines at the level of
  their halting relations, with the intermediate output buffered on a work tape;
  `Turing.FinTM.exists_cond` branches between two machines on a decided predicate.
  Both are stated untimed; the forward time bound of the buffered composition is
  `Turing.FinTM.bufferedCompTM_computesInTime`, and `Turing.FinTM.exists_comp_on_image`
  composes with a second machine that is correct only on the first one's image.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2-§1.3; the "high-level description"
  convention on p. 14.)
* [Balbach22] F. J. Balbach, *The Cook-Levin theorem*, Archive of Formal Proofs
  (Isabelle), 2022 — the composition-combinator architecture this file follows in
  spirit.
-/

namespace Turing.FinTM

/-- The one-state copy machine: emits each input bit moving right, and halts on the
boundary blank. -/
private def idTM : FinTM Bool where
  k := 0
  State := Unit
  tm :=
    { q₀ := ()
      tr := fun _ inp _ =>
        match inp with
        | some b => ⟨SignType.pos, fun i => i.elim0, some b, some ()⟩
        | none => ⟨SignType.zero, fun i => i.elim0, none, none⟩ }

/-- Run invariant of the copy machine: after `t ≤ n` steps it is live, its input head
sits at position `t + 1`, and it has emitted exactly the first `t` input bits. -/
private lemma idTM_run (x : List Bool) : ∀ t, t ≤ x.length →
    (idTM.tm.runFrom (idTM.tm.initCfg x) t).state = some () ∧
    (((idTM.tm.runFrom (idTM.tm.initCfg x) t).inputPos : ℕ) = t + 1) ∧
    (idTM.tm.runFrom (idTM.tm.initCfg x) t).output = x.take t := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨rfl, ?_, rfl⟩
    simp [MultiTapeTM.runFrom]
  | succ t ih =>
    intro ht
    obtain ⟨hstate, hpos, hout⟩ := ih (Nat.le_of_succ_le ht)
    have hrun1 : idTM.tm.runFrom (idTM.tm.initCfg x) (t + 1) =
        (idTM.tm.tr () (some (x[t]'(by omega)))
          ((idTM.tm.runFrom (idTM.tm.initCfg x) t).workTapeSymbols)).apply
          (idTM.tm.runFrom (idTM.tm.initCfg x) t) := by
      rw [MultiTapeTM.runFrom_succ_eq_step']
      unfold MultiTapeTM.step
      rw [hstate]
      dsimp only
      rw [inputSymbolInner (p := t) (by omega) (by omega)]
    refine ⟨?_, ?_, ?_⟩
    · rw [hrun1]
      simp [idTM, Action.apply]
    · rw [hrun1]
      simp only [idTM, Action.apply]
      rw [moveInputPos_pos_of_ne_right _ (by omega)]
      show ((idTM.tm.runFrom (idTM.tm.initCfg x) t).inputPos : ℕ) + 1 = t + 2
      omega
    · rw [hrun1]
      simp only [idTM, Action.apply]
      rw [hout, List.take_succ, List.getElem?_eq_getElem (by omega)]

/-- The identity function is computable in linear time: the copy machine halts within
`n + 1` steps having emitted its input verbatim (invariant `idTM_run`, then one
halting step on the boundary blank). -/
theorem computesFunInTime_id :
    ∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime id fun n => c * (n + 1) := by
  refine ⟨idTM, 1, fun x => ?_⟩
  obtain ⟨hstate, hpos, hout⟩ := idTM_run x x.length (le_refl _)
  have h0 : (idTM.tm.runFrom (idTM.tm.initCfg x) x.length).inputPos ≠ 0 := by
    intro h
    rw [h] at hpos
    simp at hpos
  have hsym : (idTM.tm.runFrom (idTM.tm.initCfg x) x.length).inputSymbol = none := by
    unfold Cfg.inputSymbol
    rw [dif_neg h0, dif_pos (by omega)]
  have hrun1 : idTM.tm.runFrom (idTM.tm.initCfg x) (x.length + 1) =
      (idTM.tm.tr () none
        ((idTM.tm.runFrom (idTM.tm.initCfg x) x.length).workTapeSymbols)).apply
        (idTM.tm.runFrom (idTM.tm.initCfg x) x.length) := by
    rw [MultiTapeTM.runFrom_succ_eq_step']
    unfold MultiTapeTM.step
    rw [hstate]
    dsimp only
    rw [hsym]
  have hbase : idTM.ComputesInTime x x (x.length + 1) := by
    refine ⟨_, ?_, ?_, rfl⟩
    · rw [hrun1]
      simp [idTM, Action.apply]
    · rw [hrun1]
      simp only [idTM, Action.apply]
      rw [hout]
      simp
  exact hbase.mono (le_of_eq (one_mul _).symm)

/-- The zero-work-tape machine whose states form the emission chain for `w`. -/
private def constTM (w : List Bool) : FinTM Bool where
  k := 0
  State := Fin (w.length + 1)
  tm := { q₀ := 0, tr := fun i _ _ => emitAction w id i }

/-- Every constant function is computable in linear time (in fact in time `|w| + 1`,
which the stated bound dominates once `c ≥ |w| + 1`).

**Proof sketch.** A zero-work-tape machine with `|w| + 1` states `s₀, …, s_{|w|}`:
state `sᵢ` emits the `i`-th symbol of `w` and moves to `s_{i+1}`, ignoring the input;
`s_{|w|}` halts. -/
theorem computesFunInTime_const (w : List Bool) :
    ∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime (fun _ => w) fun n => c * (n + 1) := by
  refine ⟨constTM w, w.length + 1, fun x => ?_⟩
  obtain ⟨hs, ho⟩ := emit_halts (constTM w).tm w id (fun _ _ _ => rfl)
    ((constTM w).tm.initCfg x) rfl
  have hbase : (constTM w).ComputesInTime x w (w.length + 1) := by
    exact ⟨_, hs, by simpa only [MultiTapeTM.initCfg, Cfg.init, List.nil_append] using ho, rfl⟩
  exact hbase.mono (Nat.le_mul_of_pos_right _ (by omega))

/-- The hardcoded comparator, followed by the chosen fixed-word emission chain. -/
private def ifEqTM (w₀ u v : List Bool) : FinTM Bool where
  k := 0
  State := Fin (w₀.length + 1) ⊕ (Fin (u.length + 1) ⊕ Fin (v.length + 1))
  tm :=
    { q₀ := .inl 0
      tr := fun q inp _ => match q with
        | .inl i =>
          if h : i.val < w₀.length then
            if inp = some w₀[i.val] then
              controlAction .pos (some (.inl ⟨i.val + 1, by omega⟩))
            else controlAction 0 (some (.inr (.inr 0)))
          else if inp = none then controlAction 0 (some (.inr (.inl 0)))
            else controlAction 0 (some (.inr (.inr 0)))
        | .inr (.inl i) => emitAction u (fun j => .inr (.inl j)) i
        | .inr (.inr i) => emitAction v (fun j => .inr (.inr j)) i }

/-- Once the comparator has chosen its output chain, that chain emits the selected
word and halts, independently of the input-head position. -/
private lemma ifEq_finish (w₀ u v x : List Bool) (b : Bool)
    (cfg : Cfg 0 Bool (ifEqTM w₀ u v).State x)
    (hs : cfg.state = some (.inr (cond b (.inl 0) (.inr 0)))) (ho : cfg.output = []) :
    ((ifEqTM w₀ u v).tm.runFrom cfg ((cond b u v).length + 1)).state = none ∧
    ((ifEqTM w₀ u v).tm.runFrom cfg ((cond b u v).length + 1)).output = cond b u v := by
  cases b
  · simpa only [Bool.cond_false, ho, List.nil_append] using
      emit_halts (ifEqTM w₀ u v).tm v (fun j => .inr (.inr j))
        (fun _ _ _ => rfl) cfg hs
  · simpa only [Bool.cond_true, ho, List.nil_append] using
      emit_halts (ifEqTM w₀ u v).tm u (fun j => .inr (.inl j))
        (fun _ _ _ => rfl) cfg hs

/-- Comparison invariant: the first `i` symbols match, and the head is at `i + 1`.

**Proof sketch.** Induct on the number of remaining comparison symbols. A matching
symbol advances the invariant. A mismatch selects the second emission chain. With
no symbols remaining, the boundary blank selects the first chain and an extra
symbol selects the second. The emission-chain lemma supplies the remaining time. -/
private lemma ifEq_run (w₀ u v x : List Bool) : ∀ (r i : ℕ) (hlen : w₀.length = i + r), i ≤ x.length → x.take i = w₀.take i →
    ∀ (cfg : Cfg 0 Bool (ifEqTM w₀ u v).State x),
      cfg.state = some (.inl ⟨i, by omega⟩) → cfg.inputPos.val = i + 1 → cfg.output = [] →
      ∃ t, t ≤ r + max u.length v.length + 2 ∧
        ((ifEqTM w₀ u v).tm.runFrom cfg t).state = none ∧
        ((ifEqTM w₀ u v).tm.runFrom cfg t).output = if x = w₀ then u else v := by
  intro r
  induction r with
  | zero =>
    intro i hlen hix hprefix cfg hs hp ho
    have hi : ¬i < w₀.length := by omega
    have hsym := inputSymbol_at cfg i hix hp
    by_cases he : x = w₀
    · subst x
      have hb : w₀[i]? = none := List.getElem?_eq_none_iff.mpr (by omega)
      have hstep : (ifEqTM w₀ u v).tm.step cfg =
          (controlAction 0 (some (.inr (.inl 0)))).apply cfg := by
        unfold MultiTapeTM.step
        rw [hs]
        simp only [ifEqTM, hsym, dif_neg hi, hb, ite_true]
      have hs' : ((ifEqTM w₀ u v).tm.step cfg).state = some (.inr (.inl 0)) := by
        rw [hstep]
        rfl
      have ho' : ((ifEqTM w₀ u v).tm.step cfg).output = [] := by
        simp [hstep, controlAction, Action.apply, ho]
      have hf := ifEq_finish w₀ u v w₀ true _ hs' ho'
      refine ⟨u.length + 1 + 1, by omega, ?_⟩
      rw [MultiTapeTM.runFrom_succ_eq_step]
      simpa only [Bool.cond_true, if_pos rfl] using hf
    · have hx : i < x.length := by
        by_contra hh
        have hxt : x.take i = x := List.take_of_length_le (by omega)
        have hwt : w₀.take i = w₀ := List.take_of_length_le (by omega)
        exact he (by rw [← hxt, ← hwt]; exact hprefix)
      have hb : x[i]? = some x[i] := List.getElem?_eq_getElem hx
      have hstep : (ifEqTM w₀ u v).tm.step cfg =
          (controlAction 0 (some (.inr (.inr 0)))).apply cfg := by
        unfold MultiTapeTM.step
        rw [hs]
        simp only [ifEqTM, hsym, dif_neg hi, hb, Option.some_ne_none, ite_false]
      have hs' : ((ifEqTM w₀ u v).tm.step cfg).state = some (.inr (.inr 0)) := by
        rw [hstep]
        rfl
      have ho' : ((ifEqTM w₀ u v).tm.step cfg).output = [] := by
        simp [hstep, controlAction, Action.apply, ho]
      have hf := ifEq_finish w₀ u v x false _ hs' ho'
      refine ⟨v.length + 1 + 1, by omega, ?_⟩
      rw [MultiTapeTM.runFrom_succ_eq_step]
      simpa only [Bool.cond_false, if_neg he] using hf
  | succ r ih =>
    intro i hlen hix hprefix cfg hs hp ho
    have hi : i < w₀.length := by omega
    have hsym := inputSymbol_at cfg i hix hp
    by_cases hm : x[i]? = some w₀[i]
    · obtain ⟨hx, hbit⟩ := List.getElem?_eq_some_iff.mp hm
      have hstep : (ifEqTM w₀ u v).tm.step cfg =
          (controlAction .pos (some (.inl ⟨i + 1, by omega⟩))).apply cfg := by
        unfold MultiTapeTM.step
        rw [hs]
        simp only [ifEqTM, hsym, dif_pos hi, hm, ite_true]
      have hs' : ((ifEqTM w₀ u v).tm.step cfg).state =
          some (.inl ⟨i + 1, by omega⟩) := by rw [hstep]; rfl
      have hp' : ((ifEqTM w₀ u v).tm.step cfg).inputPos.val = (i + 1) + 1 := by
        rw [hstep]
        change (moveInputPos cfg.inputPos .pos).val = i + 1 + 1
        rw [moveInputPos_pos_of_ne_right _ (by omega)]
        simp only
        omega
      have ho' : ((ifEqTM w₀ u v).tm.step cfg).output = [] := by
        simp [hstep, controlAction, Action.apply, ho]
      have hprefix' : x.take (i + 1) = w₀.take (i + 1) := by
        rw [List.take_succ, List.take_succ, hprefix, hm, List.getElem?_eq_getElem hi]
      obtain ⟨t, ht, htstate, htout⟩ := ih (i + 1) (by omega) (by omega) hprefix'
        ((ifEqTM w₀ u v).tm.step cfg) hs' hp' ho'
      refine ⟨t + 1, by omega, ?_⟩
      rw [MultiTapeTM.runFrom_succ_eq_step]
      exact ⟨htstate, htout⟩
    · have he : x ≠ w₀ := by
        intro he
        subst x
        exact hm (List.getElem?_eq_getElem hi)
      have hstep : (ifEqTM w₀ u v).tm.step cfg =
          (controlAction 0 (some (.inr (.inr 0)))).apply cfg := by
        unfold MultiTapeTM.step
        rw [hs]
        simp only [ifEqTM, hsym, dif_pos hi, if_neg hm]
      have hs' : ((ifEqTM w₀ u v).tm.step cfg).state = some (.inr (.inr 0)) := by
        rw [hstep]
        rfl
      have ho' : ((ifEqTM w₀ u v).tm.step cfg).output = [] := by
        simp [hstep, controlAction, Action.apply, ho]
      have hf := ifEq_finish w₀ u v x false _ hs' ho'
      refine ⟨v.length + 1 + 1, by omega, ?_⟩
      rw [MultiTapeTM.runFrom_succ_eq_step]
      simpa only [Bool.cond_false, if_neg he] using hf

/-- Testing equality with a fixed string is computable in linear time: for any fixed
`w₀ u v`, the function `w ↦ u` if `w = w₀` and `w ↦ v` otherwise. (Instantiated by
the `HALT` reduction as the postprocessor `w ↦ if w = [true] then [false] else
[true]`; see `TCSlib.Complexity.Uncomputability.Halting`.)

**Proof sketch.** Hardcode `w₀`, `u`, and `v` in the states. The machine walks the
input left to right comparing it against `w₀` symbol by symbol (`|w₀| + 1`
comparison states); on the first mismatch — including the input ending early (blank
read) or running long (a symbol where `w₀` is exhausted) — it switches to an
emission chain for `v`, and after matching all of `w₀` and then reading the boundary
blank it switches to an emission chain for `u` (at most `|u| + |v| + 2` further
states, one emitted symbol per step). Every run halts within
`|w₀| + max |u| |v| + 3` steps — a constant, absorbed as `c * (n + 1)`. -/
theorem computesFunInTime_ifEq (w₀ u v : List Bool) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun w => if w = w₀ then u else v) fun n => c * (n + 1) := by
  refine ⟨ifEqTM w₀ u v, w₀.length + max u.length v.length + 3, fun x => ?_⟩
  obtain ⟨t, ht, hs, ho⟩ := ifEq_run w₀ u v x w₀.length 0 (by omega) (by omega) rfl
    ((ifEqTM w₀ u v).tm.initCfg x) rfl (by simp) rfl
  have hbase : (ifEqTM w₀ u v).ComputesInTime x (if x = w₀ then u else v) t :=
    ⟨_, hs, ho, rfl⟩
  exact hbase.mono (Nat.le_trans (by omega) (Nat.le_mul_of_pos_right _ (by omega)))

/-- **Timed partial composition.** If `M₁` halts on `x` with output `y` within `t₁`
steps and `M₂` halts on `y` with output `o` within `t₂` steps, then
`bufferedCompTM M₁ M₂` halts on `x` with output `o` within `t₁ + |y| + 2 + t₂` steps.
No totality is assumed of either machine (cf. `computesFunInTime_comp`, which
requires it).

**Proof sketch.** `Turing.FinTM.bufferedComp_start` reaches the second phase, with
`M₂`'s initial configuration on virtual input `y`, within `t₁ + |y| + 2` steps;
`Turing.FinTM.bufferedSecondCfg_run` then tracks `M₂`'s run step for step, and the
embedding preserves halting and output. -/
theorem bufferedCompTM_computesInTime (M₁ M₂ : FinTM Bool) {x y o : List Bool} {t₁ t₂ : ℕ}
    (h₁ : M₁.ComputesInTime x y t₁) (h₂ : M₂.ComputesInTime y o t₂) :
    (bufferedCompTM M₁ M₂).ComputesInTime x o (t₁ + y.length + 2 + t₂) := by
  obtain ⟨a, p, tapes, heads, ha, hstart⟩ := bufferedComp_start M₁ M₂ x y t₁ h₁
  obtain ⟨b, _, hr⟩ := bufferedSecondCfg_run M₁ M₂ (M₂.tm.initCfg y) true
    (by simp [VirtualTag, MultiTapeTM.initCfg, Cfg.init]) p tapes heads t₂
  have hc := (computesInTime_iff _ _ _ _).mp h₂
  have hbase : (bufferedCompTM M₁ M₂).ComputesInTime x o (a + t₂) := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_add, hstart, hr]
    exact ⟨by simpa only [bufferedSecondCfg, Option.map_eq_none_iff] using hc.1, hc.2⟩
  exact hbase.mono (by omega)

/-- **Composition.** If `f` is computable within `T₁` and `g` within a monotone `T₂`,
then `g ∘ f` is computable within `c · (T₁ n + T₂ (T₁ n) + 1)`.

The inner bound `T₂ (T₁ n)` is valid because the intermediate string is no longer than
the time that produced it: `|f x| ≤ T₁ |x|` by `Turing.MultiTapeTM.output_length_le`.
Monotonicity of `T₂` is genuinely needed to convert that length bound into a time
bound.

**Proof sketch.** Build `M` with `M₁.k + M₂.k + 1` work tapes over `Bool`. Phase one
simulates `M₁` step for step on the true input, with `M₁`'s emissions written instead
onto the dedicated intermediate tape (constant overhead per step; this is the
append-only-output buffering discussed in the module docstring). Phase two rewinds the
intermediate tape head (at most `T₁ n` steps) and simulates `M₂` step for step, with
`M₂`'s input-head reads served from the intermediate tape and `M₂`'s emissions going to
the real output tape. Phase two costs constant overhead per step of `M₂`, which halts
within `T₂ |f x| ≤ T₂ (T₁ n)` steps. Bookkeeping (phase switching, boundary detection
on the intermediate tape) is absorbed into `c`.

**Implementation note (epoch 2).** The shared `bufferedCompTM` has
`M₁.k + (1 + M₂.k)` tapes and uses one physical step per simulated step.
The first halting time is at most `T₁ |x|`; rewind and dispatch take exactly
`|f x| + 2` steps, including the unconditional first left move. Consequently
`2 * T₁ |x| + T₂ (T₁ |x|) + 2` suffices, and the theorem uses `c = 2`. -/
theorem computesFunInTime_comp {M₁ M₂ : FinTM Bool} {f g : List Bool → List Bool}
    {T₁ T₂ : ℕ → ℕ}
    (h₁ : M₁.ComputesFunInTime f T₁) (h₂ : M₂.ComputesFunInTime g T₂)
    (hT₂ : Monotone T₂) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (g ∘ f) fun n => c * (T₁ n + T₂ (T₁ n) + 1) := by
  refine ⟨bufferedCompTM M₁ M₂, 2, fun x => ?_⟩
  have hlen : (f x).length ≤ T₁ x.length := by
    have ho := ((computesInTime_iff _ _ _ _).mp (h₁ x)).2
    simpa only [ho] using M₁.tm.output_length_le x (T₁ x.length)
  -- This is the only use of monotonicity: transfer the intermediate length bound.
  have htime : T₂ (f x).length ≤ T₂ (T₁ x.length) := hT₂ hlen
  exact (bufferedCompTM_computesInTime M₁ M₂ (h₁ x) (h₂ (f x))).mono
    (by dsimp only; omega)

/-- **Composition with a second machine correct only on the image.** If `M` computes `f`
within `T₁` and, for every input `x`, `U` maps `f x` to `g x` within `T₂ |x|` steps (the
budget measured at the *original* input length), then some machine computes `g` within
`2 T₁ n + T₂ n + 2`. Unlike `computesFunInTime_comp`, `U` need not be total, and no
monotonicity is assumed.

**Proof sketch.** `bufferedCompTM M U` runs both phases
(`bufferedCompTM_computesInTime`); the intermediate output is no longer than `M`'s
running time, so capture and rewind cost at most `T₁ n + 2` more steps. -/
theorem exists_comp_on_image (M U : FinTM Bool) (f g : List Bool → List Bool)
    (T₁ T₂ : ℕ → ℕ) (hM : M.ComputesFunInTime f T₁)
    (hU : ∀ x, U.ComputesInTime (f x) (g x) (T₂ x.length)) :
    ∃ N : FinTM Bool, N.ComputesFunInTime g (fun n => 2 * T₁ n + T₂ n + 2) := by
  refine ⟨bufferedCompTM M U, fun x => ?_⟩
  have hlen : (f x).length ≤ T₁ x.length := by
    have ho := ((computesInTime_iff _ _ _ _).mp (hM x)).2
    simpa only [ho] using M.tm.output_length_le x (T₁ x.length)
  exact (bufferedCompTM_computesInTime M U (hM x) (hU x)).mono (by dsimp only; omega)

/-- **Partial (guarded) sequential composition** — the phase-4 API obligation
identified by the phase-3 audit (round 2, finding 10 and Argument F):
`Turing.FinTM.computesFunInTime_comp` requires both components to compute *total*
functions, so it cannot take a partially computing machine — such as the universal
evaluator — as a component. This lemma composes two arbitrary machines at the level
of their halting relations, with **no totality or time hypotheses**: `M` behaves on
`x` exactly as `M₂` behaves on `M₁`'s completed output — halting, completed outputs,
and divergence all correspond.

Statement notes. The intermediate string `y` is existentially quantified, but by
`Turing.FinTM.ComputesInTime.output_unique` at most one `y` satisfies the first
conjunct, so the right-hand side reads "`M₁` halts on `x` (necessarily with a unique
`y`), and then `M₂` halts on `y` with `w`". If `M₁` diverges on `x`, or halts but
`M₂` diverges on its output, both sides are empty — `M` diverges. A time-bounded
refinement is deliberately not stated; it will be added if and when a result needs
it.

**Proof sketch** (buffered intermediate output, per the audit's design). `M` carries
`M₁`'s and `M₂`'s work tapes plus a fresh *buffer* tape. Phase one simulates `M₁` on
the true input step for step, with each emission of `M₁` written to the buffer tape
(write, move right) instead of the output tape; the append-only output discipline
makes the buffer region a verbatim copy of `M₁`'s output, contiguous from the
initial head cell. If `M₁` never halts, neither does `M`. On `M₁`'s halting
transition, `M` rewinds the buffer head to the leftmost written cell — the head
rests on the blank immediately *right* of the written word, so the rewind's first
left move is unconditional (testing the current cell before moving would stop at the
wrong end; phase-4 audit, finding 3), then left while reading a symbol, then one
step right. Phase two simulates `M₂` with its *input-tape
reads served from the buffer*: the buffer holds exactly `y` with blank cells on both
sides, and `M` maintains `M₂`'s virtual input position on it, mirroring the clamped
input-head semantics of `Turing.moveInputPos` at both boundaries — the same
virtual-boundary emulation as the universal machine's sketch
(`TCSlib.Complexity.TuringMachine.Universal`); a blank read identifies a boundary,
and *which* boundary is determined by the direction of arrival, tracked in the
state — for an empty intermediate word the simulation starts with the right-boundary
tag already set, the left boundary one inward move away (phase-4 audit, finding 3).
`M₂`'s work-tape actions go to its own fresh tapes and its emissions to the
real output tape, untouched during phase one. `M` halts exactly when the simulated
`M₂` halts; step-for-step run correspondence in each phase gives both directions of
the iff.

**Implementation note (epoch 2).** The buffer and virtual-input invariants are
public in `Simulation.lean`. The arrival tag is constrained only at boundaries;
stationary moves preserve it, including suppressed outward moves. Dispatch always
sets it to true, which is already the right-boundary tag when the word is empty.
A simulated phase-one halt remains live through the exact `|y| + 2` rewind.
For the forward implication, phase-one divergence contradicts a completed run;
otherwise extend that completed run beyond the verified phase-two start using
absorbing halting, and recover the second completed computation by lockstep. -/
theorem exists_comp_partial (M₁ M₂ : FinTM Bool) :
    ∃ M : FinTM Bool, ∀ x w : List Bool,
      (∃ t, M.ComputesInTime x w t) ↔
        ∃ y : List Bool,
          (∃ t, M₁.ComputesInTime x y t) ∧ ∃ t, M₂.ComputesInTime y w t := by
  classical
  refine ⟨bufferedCompTM M₁ M₂, fun x w => ?_⟩
  constructor
  · rintro ⟨t, ht⟩
    -- A divergent first component would keep every composite configuration live.
    have hh : ∃ s, (M₁.tm.runFrom (M₁.tm.initCfg x) s).state = none := by
      by_contra h
      have hr := bufferedFirstCfg_run M₁ M₂ (M₁.tm.initCfg x) t
        (fun s _ hs => h ⟨s, hs⟩)
      rw [← bufferedFirstCfg_init] at hr
      have hc := ((computesInTime_iff _ _ _ _).mp ht).1
      rw [hr] at hc
      simp only [bufferedFirstCfg, Option.some_ne_none] at hc
    obtain ⟨s, hs⟩ := hh
    let y := (M₁.tm.runFrom (M₁.tm.initCfg x) s).output
    have hy : M₁.ComputesInTime x y s := (computesInTime_iff _ _ _ _).mpr ⟨hs, rfl⟩
    obtain ⟨a, p, tapes, heads, _, ha⟩ := bufferedComp_start M₁ M₂ x y s hy
    -- Extend a completed run past the verified administrative prefix.
    have hc := (computesInTime_iff _ x w (a + t)).mp (ht.mono (by omega))
    rw [MultiTapeTM.runFrom_add, ha] at hc
    obtain ⟨b, _, hr⟩ := bufferedSecondCfg_run M₁ M₂ (M₂.tm.initCfg y) true
      (by simp [VirtualTag, MultiTapeTM.initCfg, Cfg.init]) p tapes heads t
    rw [hr] at hc
    refine ⟨y, ⟨s, hy⟩, t, (computesInTime_iff _ _ _ _).mpr ?_⟩
    exact ⟨by simpa only [bufferedSecondCfg, Option.map_eq_none_iff] using hc.1, hc.2⟩
  · rintro ⟨y, ⟨s, hs⟩, ⟨t, ht⟩⟩
    obtain ⟨a, p, tapes, heads, _, ha⟩ := bufferedComp_start M₁ M₂ x y s hs
    obtain ⟨b, _, hr⟩ := bufferedSecondCfg_run M₁ M₂ (M₂.tm.initCfg y) true
      (by simp [VirtualTag, MultiTapeTM.initCfg, Cfg.init]) p tapes heads t
    have hc := (computesInTime_iff _ _ _ _).mp ht
    refine ⟨a + t, (computesInTime_iff _ _ _ _).mpr ?_⟩
    rw [MultiTapeTM.runFrom_add, ha, hr]
    exact ⟨by simpa only [bufferedSecondCfg, Option.map_eq_none_iff] using hc.1, hc.2⟩

/-- A finite controller runs `D` with its first emission captured in a register,
rewinds, then enters the selected branch on disjoint fresh tapes. A simulated halt
is represented by a live control state so that dispatch occurs only after `D` halts.
An empty register at dispatch halts safely. -/
private def condTM (D M₁ M₂ : FinTM Bool) : FinTM Bool where
  k := D.k + (M₁.k + M₂.k)
  State := (Option D.State × Option Bool) ⊕ (Option Bool ⊕ (M₁.State ⊕ M₂.State))
  tm :=
    { q₀ := .inl (some D.tm.q₀, none)
      tr := fun q inp work => match q with
        | .inl (some q, reg) =>
          let a := D.tm.tr q inp (fun i => work (Fin.castAdd (M₁.k + M₂.k) i))
          ⟨a.inputTape, Fin.addCases a.workTapes (fun _ => (none, 0)), none,
            some (.inl (a.state, reg.or a.output))⟩
        | .inl (none, reg) => controlAction .neg (some (.inr (.inl reg)))
        | .inr (.inl reg) => match inp with
          | some _ => controlAction .neg (some (.inr (.inl reg)))
          | none => controlAction .pos
              (reg.map (fun b => .inr (.inr (branchTM M₁ M₂ b).tm.q₀)))
        | .inr (.inr q) => rightAction D.k (fun s => .inr (.inr s))
            ((branchTM M₁ M₂ false).tm.tr q inp (fun i => work (Fin.natAdd D.k i))) }

/-- Embed a controller configuration with its output suppressed and the first
output symbol stored in the finite register. All branch tapes remain blank. -/
private def controlCfg (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg D.k Bool D.State x) : Cfg (condTM D M₁ M₂).k Bool (condTM D M₁ M₂).State x where
  state := some (.inl (c.state, c.output.head?))
  inputPos := c.inputPos
  workTapes := Fin.addCases c.workTapes (fun _ _ => none)
  workTapePos := Fin.addCases c.workTapePos (fun _ => 0)
  output := []

/-- Before the simulated controller halts, one composite step exactly updates its
configuration and the first-emission register. The head-of-append identity makes
this invariant valid even without any assumption on the controller's output. -/
private lemma controlCfg_step (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg D.k Bool D.State x) (hs : c.state ≠ none) :
    (condTM D M₁ M₂).tm.step (controlCfg D M₁ M₂ c) =
      controlCfg D M₁ M₂ (D.tm.step c) := by
  unfold MultiTapeTM.step
  cases hq : c.state with
  | none => exact False.elim (hs hq)
  | some q =>
    have hs' : (controlCfg D M₁ M₂ c).state = some (.inl (some q, c.output.head?)) := by
      simp [controlCfg, hq]
    rw [hs']
    dsimp only [condTM]
    have hr : (fun i => (controlCfg D M₁ M₂ c).workTapeSymbols
        (Fin.castAdd (M₁.k + M₂.k) i)) = c.workTapeSymbols := by
      funext i
      simp [controlCfg, Cfg.workTapeSymbols]
    have hi : (controlCfg D M₁ M₂ c).inputSymbol = c.inputSymbol := rfl
    rw [hr, hi]
    refine Cfg.ext ?_ rfl ?_ ?_ ?_
    · simp [controlCfg, Action.apply, List.head?_append, Option.head?_toList]
    · funext i
      refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [controlCfg, Action.apply]
    · funext i
      refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [controlCfg, Action.apply]
    · simp [controlCfg, Action.apply]

/-- Controller lockstep holds through its first halting step. Subsequent composite
steps perform the rewind, so no claim of lockstep after halting is made. -/
private lemma controlCfg_run (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg D.k Bool D.State x) (t : ℕ)
    (h : ∀ s, s < t → (D.tm.runFrom c s).state ≠ none) :
    (condTM D M₁ M₂).tm.runFrom (controlCfg D M₁ M₂ c) t =
      controlCfg D M₁ M₂ (D.tm.runFrom c t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (fun s hs => h s (by omega)),
      controlCfg_step D M₁ M₂ _ (h t (by omega)), MultiTapeTM.runFrom_succ_eq_step']

/-- A completed singleton controller computation reaches the selected branch's
fresh initial configuration after a finite prefix.

**Proof sketch.** Choose the first halting time of `D` and use controller lockstep.
Output uniqueness identifies its completed output with `[b]`, so the register is
`some b`, including when that bit was emitted early. Rewind from the resulting
input position; the branch tapes and real output have remained untouched. -/
private lemma condTM_start (D M₁ M₂ : FinTM Bool) (x : List Bool) (b : Bool)
    (hD : ∃ t, D.ComputesInTime x [b] t) :
    ∃ (t : ℕ) (tapes : Fin D.k → ℤ → Option Bool) (heads : Fin D.k → ℤ),
      (condTM D M₁ M₂).tm.runFrom ((condTM D M₁ M₂).tm.initCfg x) t =
        rightCfg (fun q => .inr (.inr q)) ((branchTM M₁ M₂ b).tm.initCfg x) tapes heads := by
  classical
  obtain ⟨tD, hDc⟩ := hD
  have hh : ∃ t, (D.tm.runFrom (D.tm.initCfg x) t).state = none :=
    ⟨tD, ((computesInTime_iff D x [b] tD).mp hDc).1⟩
  let t := Nat.find hh
  let cf := D.tm.runFrom (D.tm.initCfg x) t
  have hstop : cf.state = none := Nat.find_spec hh
  have hc : D.ComputesInTime x cf.output t :=
    (computesInTime_iff D x cf.output t).mpr ⟨hstop, rfl⟩
  have hout : cf.output = [b] := hc.output_unique hDc
  have hi : (condTM D M₁ M₂).tm.initCfg x = controlCfg D M₁ M₂ (D.tm.initCfg x) := by
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    · funext i
      refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [controlCfg]
    · funext i
      refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [controlCfg]
  have hrun : (condTM D M₁ M₂).tm.runFrom ((condTM D M₁ M₂).tm.initCfg x) t =
      controlCfg D M₁ M₂ cf := by
    rw [hi]
    exact controlCfg_run D M₁ M₂ (D.tm.initCfg x) t (fun s hs => Nat.find_min hh hs)
  obtain ⟨r, hr⟩ := rewind_from_any (condTM D M₁ M₂).tm
    (.inl (none, some b)) (.inr (.inl (some b)))
    (some (.inr (.inr (branchTM M₁ M₂ b).tm.q₀)))
    (fun _ _ => rfl) (fun inp _ => by cases inp <;> rfl)
    (controlCfg D M₁ M₂ cf) (by simp [controlCfg, hstop, hout])
  refine ⟨t + r, cf.workTapes, cf.workTapePos, ?_⟩
  rw [MultiTapeTM.runFrom_add, hrun, hr]
  rfl

/-- **Branching on a decided predicate** — the second phase-4 combinator (phase-3
audit, round 2, Argument F, step 2 of the `HALT → UC` reduction): given a total
decider `D` for `p` and two branch machines, some machine behaves on every input
exactly as the branch selected by `p` does *on that same input*. The input tape is
read-only, so both branches see the original input.

**Proof sketch.** `D` computes the singleton output `[p x]` on every input, and
output is append-only, so along any run `D` emits exactly one symbol; simulate `D`
with that single emission recorded in a state register instead of emitted (no buffer
tape needed). On `D`'s halting transition, rewind the true input head to its initial
position: one step left, then left while reading a symbol, then one step right —
from any position this ends at input position `1`, the initial position, the clamp
at position `0` making the walk safe (including on empty input). Then transfer
control to a disjoint copy of `M₁` or `M₂` according to the register. The branches'
work tapes are fresh tapes `D` never touched, the output tape is untouched by phase
one, and the input head is back at its initial position, so the selected branch's
run is reproduced verbatim; determinism (`Turing.FinTM.ComputesInTime.output_unique`)
identifies `D`'s completed output with `[p x]`, so the selected branch is
`cond (p x) M₁ M₂`.

The implementation retains the first emission, with the exact invariant that the
register is the head of the simulated output. A live administrative state follows
the simulated halt before the first left move. For the forward implication, extend
any completed composite run beyond the verified branch-start prefix using absorbing
halting, then apply branch lockstep; the reverse implication concatenates that
prefix with the selected branch run. -/
theorem exists_cond (D M₁ M₂ : FinTM Bool) (p : List Bool → Bool)
    (hD : D.Computes fun x => [p x]) :
    ∃ M : FinTM Bool, ∀ x w : List Bool,
      (∃ t, M.ComputesInTime x w t) ↔
        ∃ t, (cond (p x) M₁ M₂).ComputesInTime x w t := by
  refine ⟨condTM D M₁ M₂, fun x w => ?_⟩
  obtain ⟨a, tapes, heads, ha⟩ := condTM_start D M₁ M₂ x (p x) (hD x)
  have hr (t : ℕ) :
      (condTM D M₁ M₂).tm.runFrom ((condTM D M₁ M₂).tm.initCfg x) (a + t) =
        rightCfg (fun q => .inr (.inr q))
          ((branchTM M₁ M₂ (p x)).tm.runFrom ((branchTM M₁ M₂ (p x)).tm.initCfg x) t)
          tapes heads := by
    rw [MultiTapeTM.runFrom_add, ha]
    exact rightCfg_run (branchTM M₁ M₂ (p x)).tm (condTM D M₁ M₂).tm
      (fun q => .inr (.inr q)) (fun _ _ _ => rfl) _ tapes heads t
  constructor
  · rintro ⟨t, ht⟩
    have hc := (computesInTime_iff (condTM D M₁ M₂) x w (a + t)).mp
      (ht.mono (by omega))
    rw [hr t] at hc
    have hb : (branchTM M₁ M₂ (p x)).ComputesInTime x w t :=
      (computesInTime_iff _ x w t).mpr
        ⟨by simpa only [rightCfg, Option.map_eq_none_iff] using hc.1, hc.2⟩
    exact ⟨t, (branchTM_computes M₁ M₂ (p x) x w t).mp hb⟩
  · rintro ⟨t, ht⟩
    have hb := (computesInTime_iff (branchTM M₁ M₂ (p x)) x w t).mp
      ((branchTM_computes M₁ M₂ (p x) x w t).mpr ht)
    refine ⟨a + t, (computesInTime_iff _ x w (a + t)).mpr ?_⟩
    rw [hr t]
    exact ⟨by simpa only [rightCfg, Option.map_eq_none_iff] using hb.1, hb.2⟩

end Turing.FinTM
