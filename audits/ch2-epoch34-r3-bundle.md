# External audit pack — Chapter 2, epoch-3/4 fill gate, round 3

Round-3 review of the single open major from round 2
(`audits/ch2-epoch34-r2-findings.md`, attached verbatim): the kernel
public-surface certification of the six owned modules. All other
round-1/2 items are closed or frozen. Record findings in
`audits/ch2-epoch34-r3-findings.md`; the gate closes on zero
blockers/majors across all rounds' open items.

The repair (detail in the attached resolutions, round-2→3 section):
`audits/programs/ch2-epoch34-R3Axioms.lean` replaces pass 3 with exact
two-directional set equality against an embedded, reviewed 87-name
inventory — no prefix inference, no `isInternal` exemption, no
exceptions array; absent expected names and unlisted actual names both
fail the run; source publics are existence- and ownership-checked. The
inventory review binds each of the 87 names to its class and generating
declaration, and corrects round 2's undercount of the private-structure
derived-instance family (7 members, not 3 — the rest had been masked by
the rejected `isInternal` exemption). Passes 1/2/4/5 are unchanged; the
run used the same pinned snapshot, sources hash-asserted against the
round-2 manifest, and passed.

Both round-2 probes are now answered mechanically: `SurfaceProbe.a.extra`
(an unlisted public under an allowed prefix) fails check (i);
`SurfaceProbe.b` (an expected name that does not exist) fails check (ii).

## Bundle manifest — 5 attachments after this pack

The resolutions (with the round-2→3 addendum); the round-2 findings
(verbatim); the R3 program; its run log; the reviewed kernel-surface
inventory.

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


---

# Round 2 → round 3

The round-2 report (`audits/ch2-epoch34-r2-findings.md`, preserved
verbatim) closed findings 2 and 3 and the axiom/target/coverage
components of finding 1, leaving **one open major**: pass 3's kernel
public-surface certification, with both probes accepted (prefix descent
and `isInternal` are not provenance; no reverse existence check; the 11
exceptions unbound).

**Repair — exact two-directional inventory equality.**
`audits/programs/ch2-epoch34-R3Axioms.lean` (attached, with its run log)
replaces pass 3 entirely: no prefix inference, no `isInternal`
exemption, no exceptions array. The program embeds, per owned module,
the exact expected list of non-private kernel names — **87 names in
total** — and asserts (i) every actual non-private name in the module is
in the expected list, (ii) every expected name actually exists and is
owned by exactly that module (the auditor's absent-`SurfaceProbe.b`
case now throws), (iii) every source public is present and owned
(reverse existence), and (iv) actual and expected sizes agree. An
unlisted `a.extra`-style public theorem now fails the run; an absent
expected declaration now fails the run. The 87-name list is reviewed
name-by-name in the attached
`audits/evidence/ch2-epoch34/kernel-surface-inventory.md`, each entry
bound to its class and generating declaration: 45 source publics, 27
generated auxiliaries of those publics, the 8 imported-definition
equation lemmas, and — a correction the exact enumeration itself forced —
the derived-instance family of the private `SatStreamState` has **seven**
members, not the three round 2 disclosed: its four `._proof_N` members
had been masked by precisely the `isInternal` exemption the auditor
rejected. Passes 1, 2, 4, 5 are unchanged from round 2; the run is
against the same pinned snapshot (the 65 sources were hash-asserted
byte-identical to `final-source-manifest.md` before the run, the
records-only commits since being source-free), and completed
**R3 CLOSURE AUDIT PASS**, exit 0.

**Wording corrections requested by the round-2 notes**, accepted: the
round-2 resolutions' claim that the manifest "pins those endpoints" was
too broad — the manifest pins the final-run commit only, and the
59-commit census remains reproducible-from-history maintainer
provenance, not supplied evidence (finding 6); the duplicate-run
record's replay and the campaign execution logs are correctly labeled
**maintainer-verified** evidence (findings 4 and 7).

Round-3 review scope: the pass-3 repair and the inventory review alone.

## ===== audits/ch2-epoch34-r2-findings.md =====

Input SHA-256: `691ced8681da68a8d6f248e8eed3dc1a5fb86ecbb58ba3cc7d6fb0f58b83da6f`. The received `ch2-epoch34-r2-bundle.md` is 480,926 bytes and contains exactly **12 attachments**, under 12 distinct `## ===== <path> =====` headers matching the advertised manifest. No attachment-count discrepancy.

**FAIL — cumulative open defects across both rounds: 0 blockers / 1 major / 0 minors.** Round-1 finding 1 remains open only for kernel public-surface certification; its axiom, target, and module-coverage components are repaired. Round-1 findings 2 and 3 close. The 11 round-1 notes are retained, with the evidence qualifications and dispositions below; they are not additional blockers or majors.

This report, dated 2026-10-06, reviews the supplement and the specified repairs. The round-1 mathematical confirmations remain frozen. I consulted no repository history, changed no supplied artifact, and did not rerun the campaign. Independently recomputed results below are distinguished from supplied execution evidence.

For isolated checker tests, I used Lean 4.25.0, commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`, on Linux x86-64, Python 3.12.14, glibc 2.39. The available Lean binary initially reported “failed to locate application.” An auditor-local, per-command `LD_PRELOAD` shim redirects only `/proc/<current-pid>/exe` to `/proc/self/exe`; it changes no Lean proof-checking code. Its C source SHA-256 is `1b5db08f7b4105d445c1228bddfc54dd6e587e70e79f1315eea5c8b8ba4379fa`. The isolated probes are not campaign elaboration. The supplement does not supply the complete campaign source/olean tree; its campaign runs remain maintainer evidence.

1. **[major; round-1 finding 1, narrowed] Pass 3 does not establish the claimed kernel public surface.**

   **Files/declarations:** `audits/programs/ch2-epoch34-R2Axioms.lean`: `R2Audit.ownedModules`, the six `publics*` arrays, `generatedExceptions`, and the `run_cmd` variables `isPriv`, `fromPublic`, and `surfaceBad`; `audits/ch2-epoch34-resolutions.md`, finding 1, pass 3.

   **Argument:** The rejection test is:
   
   ```lean
   let isPriv := privateToUserName name != name
   let fromPublic := pubs.any (fun t => t == name || t.isPrefixOf name)
   unless isPriv || fromPublic || name.isInternal || generatedExceptions.contains name do
     surfaceBad := surfaceBad.push name
   ```

   A name being a descendant of an allowed name does not establish that Lean generated it from that declaration. An ordinary, explicitly declared public theorem can have that name. Absence of anonymous instances does not prevent this.

   I compiled an isolated imported module containing exactly these two public source declarations and no anonymous instances:

   ```lean
   namespace SurfaceProbe
   theorem a : True := True.intro
   theorem a.extra : True := True.intro
   end SurfaceProbe
   ```

   Applying the supplied predicate with `pubs = #[SurfaceProbe.a, SurfaceProbe.b]` and no generated exceptions produced:

   ```text
   SURFACE SurfaceProbe.a: private=false, internal=false, fromPublic=true
   SURFACE SurfaceProbe.a.extra: private=false, internal=false, fromPublic=true
   EXPECTED=[SurfaceProbe.a, SurfaceProbe.b]; OBSERVED_COUNT=2;
   EXPECTED_COUNT=2; BAD=[]; b_EXISTS=false
   SurfaceProbe.a.extra : True
   ```

   Both compilation commands exited 0. Thus an unlisted public theorem passes, an expected declaration can be absent, and equal public counts do not detect the substitution. The current program contains no reverse existence/ownership check for every entry of the public lists. The 21 target checks establish existence for those targets, not for all 45 public-list entries.

   There is also an independent broad exemption: Lean's `Name.isInternal` is a naming test, not a certificate of generated provenance or `private` visibility. An ordinary public `Complexity._auditR2Extra : True` passed an additional isolated test. Finally, printing the fixed `generatedExceptions` array does not verify that each item exists in its asserted owning module or is the disclosed generated artifact.

   This challenges the certification procedure, not the frozen mathematics: I do not claim either probe declaration occurs in the campaign. The supplied lint counts agree with the list lengths, but those counts do not supply the missing name-by-name comparison. Consequently “kernel surface = the source publics” and the resolutions' assertion that prefix descent is sound are not established by this repair. The required public-surface part of round-1 finding 1 remains a major evidence gap.

   **Proposed resolution:** Append a per-module inventory of actual non-private kernel names, including the currently exempt internal names. Check exact membership against the source public declarations and an explicitly reviewed generated-name inventory, or validate generated ancestry using appropriate metadata. Check expected source declarations for existence and correct module ownership. Bind each of the 11 disclosed exceptions to its actual module and generating declaration/type. Remove unrestricted prefix/internal-name acceptance as a substitute for this verification, and rerun against the pinned final snapshot. No frozen target statement or owned proof needs changing.

2. **[note; round-1 finding 1, partial closure] The axiom, target, and advertised-module coverage repairs address the original counterexample.**

   **Files/declarations:** `audits/programs/ch2-epoch34-R2Axioms.lean`: `allowed`, `clean`, `visit`, `userRoots`, `targets`, `orderModules`, and passes 1, 2, 4, 5; `audits/logs/ch2-epoch34-r2-axioms.log`.

   **Argument:** I independently counted 21 distinct targets and verified exact agreement with the 21 logged empty-root rows. The program applies `collectAxioms` to each. I counted 65 distinct order entries and verified their ordered equality with both the manifest and fresh sweep. Pass 5 tests inclusion of each entry; the restored six-umbrella import set includes the previously omitted branch.

   The new walk inspects checked declaration types, values including opaque bodies, and inductive constructors. These are the relevant dependency cases used by the pinned Lean `CollectAxioms` implementation. It rejects any `axiomInfo` outside the permitted triple. In an isolated imported module, the copied walk returned `false` for both an unused private `axiom ... : False` and a private theorem depending on it. A missing-name probe returned `false`, printed the panic, and exited 1 when passed through the rejection branch. The old silent-success counterexample is repaired.

   The provisional `true` cache entries break recursive dependency cycles. They should not be read as independently proved per-name results while traversal is in progress. They do not conceal a bad axiom from a successful whole run: its first discovery returns false, which propagates along the active calls to an enumerated root; that root is retained in `tcslibBad`, causing rejection.

   The log's six owned-module totals sum to
   `820 + 490 + 786 + 41 + 439 + 1550 = 4126`.
   Its whole-import total is 11,510, an increase of `11510 − 11436 = 74`. These are consistent supplied runtime counts, not independently reproduced campaign counts. The axiom walk applies before the surface exemptions, so the 11 disclosed generated artifacts receive no axiom exemption.

   **Proposed resolution:** Close the axiom, target, and module-inclusion components of round-1 finding 1. Retain these checks while repairing pass 3 under finding 1 above.

3. **[note; round-1 finding 2 closed] The merge supplement supplies the missing changes and substituted proof implementations.**

   **Files/declarations:** `audits/evidence/ch2-epoch34/merge2-owned-diffs.md`; `SAT.lean`: the five `sat_*` toolkit aliases and their changed callers; `EXP.lean`: `enumWord`, `enumCont_verifier_call`, `enumCont_clean_verifier`, `enumCont_from_body`, `enumMachine_contracts`, `exists_proj_decider`, `NP_subset_EXP`; `PolyTimePairing.lean`: `polyTimeComputable_of_linear`, `polyTimeComputable_const`, `polyTimeComputable_ite`, `polyTimeComputable_and`; `Composition.lean`: `bufferedCompTM_computesInTime`, `exists_comp_on_image`.

   **Argument:** I parsed every supplied diff hunk and checked its old/new line counts and cumulative offsets. The independently counted changes are:

   | Diff | Added | Deleted |
   |---|---:|---:|
   | Merge #2, SAT | 46 | 81 |
   | Merge #2, EXP | 171 | 155 |
   | Merge #2 total | **217** | **236** |
   | Merge #1, Tautology | 35 | 39 |

   The SAT aliases retain their former contracts. Linear-time inclusion chooses polynomial degree 1; constants use the existing finite-control emitter. Branching raises the three degrees to their maximum and pays for the test, the larger branch budget, and the constructor's additive overhead. Conjunction is the true branch's second bit and the constant false branch. These substitutions preserve the Boolean behavior.

   The image-only composition proof uses the same buffered machine. Its intermediate length bound is `(f x).length ≤ T₁ x.length`, so the shared timed contract gives:
   
   ```text
   T₁ x.length + (f x).length + 2 + T₂ x.length
     ≤ 2 * T₁ x.length + T₂ x.length + 2.
   ```

   The second budget remains measured at the original input length; the proof does not introduce a totality or monotonicity assumption on the second machine.

   The EXP diff promotes the unchanged fixed-width enumeration function and generalizes the verifier budget to `Tv`. The changed calls evaluate it at the exact assembled length, so no monotonicity of `Tv` is needed. The guarded startup/round interfaces and endpoint configurations are preserved. The replacement common budget pays `3 * Tv` explicitly; the loop assembly retains fuel and startup costs. The final NP specialization bounds both powers by degree `d + c + 1`, using the positive base, before applying the existing exponential normalization. These are the changes under review; the previously confirmed endpoint mathematics is not reopened.

   Merge #1's supplied diff documents the DNF carrier/evaluation substitutions and totals already described in round 1. It supplies the missing change record for note 12. Its historical blob associations, like merge #2's asserted equality to HEAD, remain supplied provenance rather than independently fetched Git objects.

   **Proposed resolution:** Close round-1 finding 2 at the supplied-diff and source-review level. Retain the carrier approval and unchanged mathematical confirmations. The remaining gate failure is finding 1, not an identified merge-proof defect.

4. **[note] The manifest and sweep transcripts are consistent; the historical sweep is not an admission-free final run.**

   **Files/declarations:** `audits/evidence/ch2-epoch34/final-source-manifest.md`; `audits/logs/ch2-epoch34-r2-sweep.log`; `audits/logs/colleague-merge2-sweep.log`; the two supplied shared source modules.

   **Argument:** The manifest has exactly 65 distinct modules, numbered 1–65, with well-formed source and olean SHA-256 entries. Its commit `154ecb189633c08b3a76ce1d0aac74e16e335021` agrees with the fresh sweep's HEAD. Removing bundle framing, I recomputed exact matches for both supplied complete source files:
   
   - `PolyTimePairing.lean`: `31a44bda2c205dfd92903417e636112cf9947222c5d87ab122870f4881cd1c82`.
   - `Composition.lean`: `264430fafd3c760d9d0a9f44207213dbdb20bba87a898f438e9a6b3e5daebc64`.

   The fresh sweep contains the same 65 entries in order, no `error:` lines, no sorry warnings, and the final `SWEEP_OK 65/65` at 20:28:40Z.

   The historical transcript contains 66 attempts: the first 52 modules, the failed old-order module 53 (`TuringMachine`, missing `UnaryTape.olean`), and the 13-module extended-order resume. Its successful modules agree with the final order. It also contains `Tautology.lean:1271:8: warning: declaration uses 'sorry'`. This historical warning is consistent with a later fill; it is absent from the fresh final sweep. The historical `SWEEP_OK` must therefore not be represented as an admission-free final verification.

   Only the two supplied complete source hashes could be recomputed here. The other source identities, all olean hashes, freshness, and the linkage of those oleans to the closure run are maintainer evidence. The supplement now supplies the requested manifest; this qualification does not impose a new requirement to rebuild excluded campaign internals.

   **Proposed resolution:** Retain the manifest and distinguish the historical merge run from the final sweep. Describe campaign execution as supplied evidence and the two source-hash comparisons as independently checked.

5. **[note; round-1 finding 3 closed] The scoped lint repairs the missing Cook–Levin coverage.**

   **Files/declarations:** `audits/logs/ch2-epoch34-r2-lint.log`; module-wide policy coverage for all six owned files.

   **Argument:** All six files now have INFO rows. The five owned size exceptions are explicitly identified: Hardness 9,937; Nondeterminism 5,835; SAT 4,815; EXP 3,268; Tautology 1,749. Snapshot is 368 lines. The separate 1,755-line TMSAT warning is correctly identified as the standing epoch-2 exception.

   The reported public counts, in the closure program's owned-module order, are `8/8/5/14/5/5`, exactly the lengths of its six public arrays. This confirms count agreement, subject to finding 1's name-comparison limitation. The log reports zero FAIL across the two subtree runs. I did not independently rerun the lint.

   **Proposed resolution:** Close round-1 finding 3. Preserve the already approved size exceptions and post-gate retrofit deferral.

6. **[note; round-1 note 4] The deletion arithmetic is repaired; the historical census remains an attestation.**

   **Files/declarations:** `audits/ch2-epoch34-resolutions.md`, finding 4; `final-source-manifest.md`; historical fill-deletion inventory.

   **Argument:** I summed all 12 listed nonzero deletion rows: 22 sorry-line deletions and 76 other deletions. The relationship to the original residual is:
   
   ```text
   98 = 22 + 76
      = (21 + 1) + (34 + 1 + 33 + 8).
   98 − 21 − 34 − 33 = 1 + 1 + 8 = 10.
   ```

   The explanation assigns one extra sorry deletion to the relocated local admission and one splice to the 35-line non-sorry deletion group. The remaining eight are itemized as `1 + 5 + 1 + 1` in commits `bf6a06f8`, `42f99b0f`, `96d5b017`, and `07bbad98`. The numerical residual is fully accounted for.

   These are recomputations of the supplied rows, not verification against commit diffs. The 59-commit classification/no-touch claim remains outside independently inspected evidence. The resolution's assertion that the round-2 manifest “pins those endpoints” is too broad: that manifest names the final run commit, not both census endpoints or the complete census.

   **Proposed resolution:** Accept the arithmetic correction. Preserve the historical-provenance qualification and correct the endpoint wording in a subsequent resolutions record; do not amend the immutable pack.

7. **[note; round-1 note 13] The requested checksum record is present, but its replay and selection claims are maintainer verification.**

   **Files/declarations:** `audits/evidence/ch2-epoch34/duplicate-run-record.md`; `audits/ch2-epoch34-resolutions.md`, finding 13; the selected beta patch and integration `1c824071`.

   **Argument:** The record identifies all three archive deliveries, assigning the duplicate alpha archive the same digest, and provides separate alpha/beta patch digests. It states that replaying beta at `61cf5958` reproduces integration tree `8e1c03588179ae0457ea4b388521aa7bfc43cbe6`.

   This is now an inspectable record of the requested maintainer-side replay. If the stated replay and identities are correct, equality of the complete result trees establishes byte-for-byte equality with beta's replayed result. It does not, by itself, establish alpha's eligibility, comparative economy, or the historical claim that alpha was never applied anywhere. The archives, patch bytes, replay transcript, and object trees are not supplied, so I cannot independently recompute those digests or the replay.

   **Proposed resolution:** Accept provision of the checksum/binding record while retaining round-1 note 13's independent-verification qualification. Label the replay as maintainer-verified. Retain whole-run selection and its approved criterion order; no new gate-blocking defect is inferred from the unavailable archives.

The round-1 mathematical notes and the two approved post-gate deferrals remain unchanged. Closure of this gate requires the public-surface evidence repair in finding 1.

Glossary of probe notation: `SurfaceProbe.a` and `SurfaceProbe.a.extra` are ordinary public test theorems; `SurfaceProbe.b` is an absent expected test name. All other code identifiers retain their meanings in the supplied sources.

## ===== audits/programs/ch2-epoch34-R3Axioms.lean =====

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

namespace R3Audit

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

def inventoryNondeterminism : Array Name := #[`Complexity.EXP_eq_NEXP_of_P_eq_NP, `Complexity.NEXP_eq_iUnion_NTIME, `Complexity.NEXP_subset_iUnion_NTIME, `Complexity.NP_eq_iUnion_NTIME, `Complexity.NP_subset_iUnion_NTIME, `Complexity.P_ne_NP_of_EXP_ne_NEXP, `Complexity.ntime_expPow_subset_NEXP, `Complexity.ntime_expPow_subset_NEXP._proof_1_2, `Complexity.ntime_expPow_subset_NEXP._proof_1_3, `Complexity.ntime_expPow_subset_NEXP._proof_1_4, `Complexity.ntime_poly_subset_NP, `Turing.NDTM.runWith.eq_1, `Turing.NDTM.runWith.eq_2, `Turing.NDTM.runWith.eq_def, `Turing.NDTM.stepWith.eq_1]

def inventoryEXP : Array Name := #[`Complexity.EXP, `Complexity.EXP_subset_NEXP, `Complexity.ExpBound, `Complexity.NEXP, `Complexity.NP_subset_EXP, `Complexity.NP_subset_EXP._proof_1_1, `Complexity.NP_subset_EXP._proof_1_2, `Complexity.NP_subset_EXP._proof_1_3, `Complexity.NP_subset_EXP._proof_1_4, `Complexity.NP_subset_EXP._proof_1_5, `Complexity.P_subset_EXP, `Complexity.P_subset_EXP._proof_1_1, `Complexity.enumWord, `Complexity.enumWord._sunfold, `Complexity.enumWord._unsafe_rec, `Complexity.enumWord.eq_1, `Complexity.enumWord.eq_2, `Complexity.enumWord.eq_def, `Complexity.enumWord.match_1, `Complexity.exists_proj_decider, `Complexity.exists_proj_decider._proof_1_1, `Turing.solveSplitWith.eq_1]

def inventorySAT : Array Name := #[`Complexity.SAT, `Complexity.SAT3, `Complexity.SAT3_mem_NP, `Complexity.SAT_mem_NP, `Complexity.SAT_reducible_SAT3, `Complexity.instDecidableEqSatStreamState, `Complexity.instDecidableEqSatStreamState.decEq, `Complexity.instDecidableEqSatStreamState.decEq._proof_1, `Complexity.instDecidableEqSatStreamState.decEq._proof_2, `Complexity.instDecidableEqSatStreamState.decEq._proof_3, `Complexity.instDecidableEqSatStreamState.decEq._proof_4, `Complexity.instDecidableEqSatStreamState.decEq.match_1, `Std.Sat.CNF.WidthAtMost.eq_1, `Std.Sat.CNF.fallback.eq_1, `Std.Sat.CNF.numVars.eq_1]

def inventorySnapshot : Array Name := #[`Complexity.Snapshot, `Complexity.emitted, `Complexity.inputBitAt, `Complexity.inputBitAt.eq_1, `Complexity.inputPosAt, `Complexity.oblivious_schedule_eq, `Complexity.prevVisit, `Complexity.snapshotAt, `Complexity.snapshotAt.eq_1, `Complexity.snapshotAt_inputSymbol, `Complexity.snapshotAt_inputSymbol._proof_1_2, `Complexity.snapshotAt_inputSymbol._proof_1_3, `Complexity.snapshotAt_state_succ, `Complexity.snapshotAt_workSymbol, `Complexity.snapshotAt_workSymbol._proof_1_1, `Complexity.snapshotAt_workSymbol._proof_1_2, `Complexity.snapshotAt_workSymbol.match_1, `Complexity.snapshotAt_zero, `Complexity.stepState, `Complexity.stepState.eq_1, `Complexity.stepState.match_1, `Complexity.workPosAt, `Complexity.writtenOrKept, `Complexity.writtenOrKept.eq_1]

def inventoryTautology : Array Name := #[`Complexity.TAUTOLOGY, `Complexity.TAUTOLOGY_coNPComplete, `Complexity.TAUTOLOGY_coNPComplete._simp_1_1, `Complexity.TAUTOLOGY_mem_coNP, `Complexity.coNPComplete, `Complexity.coNPHard]

def inventoryHardness : Array Name := #[`Complexity.NPHard.polyTimeReducible, `Complexity.SAT3_NPComplete, `Complexity.SAT3_NPHard, `Complexity.SAT_NPComplete, `Complexity.SAT_NPHard]

def ownedModules : Array (Name × Array Name × Array Name) := #[
  (`TCSlib.Complexity.ClassNP.Nondeterminism, publicsNondeterminism, inventoryNondeterminism),
  (`TCSlib.Complexity.ClassNP.EXP, publicsEXP, inventoryEXP),
  (`TCSlib.Complexity.ClassNP.SAT, publicsSAT, inventorySAT),
  (`TCSlib.Complexity.CookLevin.Snapshot, publicsSnapshot, inventorySnapshot),
  (`TCSlib.Complexity.ClassNP.Tautology, publicsTautology, inventoryTautology),
  (`TCSlib.Complexity.CookLevin.Hardness, publicsHardness, inventoryHardness)]

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
  for (modName, pubs, expected) in ownedModules do
    let mut cnt := 0
    let mut actual : Array Name := #[]
    for (name, _) in env.constants.toList do
      if env.getModuleIdxFor? name |>.any (fun i => env.header.moduleNames[i.toNat]! == modName) then
        cnt := cnt + 1
        let (ok, c) := ((clean name).run env).run cache
        cache := c
        unless ok do tcslibBad := tcslibBad.push name
        if privateToUserName name == name then
          actual := actual.push name
          unless expected.contains name do
            surfaceBad := surfaceBad.push name
    -- Reverse direction: every expected inventory entry (hence every source
    -- public) exists and is owned by exactly this module.
    for e in expected do
      unless actual.contains e do
        throwError "Expected kernel name missing from {modName}: {e}"
    for p in pubs do
      unless expected.contains p && actual.contains p do
        throwError "Source public missing or mis-owned in {modName}: {p}"
    unless actual.size == expected.size do
      throwError "Inventory size mismatch in {modName}: actual {actual.size} vs expected {expected.size}"
    moduleTotals := moduleTotals.push (modName, cnt)
  unless surfaceBad.isEmpty do
    throwError "Kernel names outside the reviewed exact inventory: {surfaceBad}"
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
    logInfo m!"PASS 2/3 {m}: {n} checked declarations, all closures within the permitted triple; non-private kernel names match the reviewed 87-name inventory exactly (both directions)."
  logInfo m!"PASS 4: {tcslibTotal} checked TCSlib declarations in the import closure; every transitive closure is within propext/Classical.choice/Quot.sound (sorryAx and any other axiom would fail this run)."
  logInfo "R3 CLOSURE AUDIT PASS: the round-2 finding-1 surface repair discharged -- exact two-directional inventory equality on all six owned modules; axiom, target, and coverage passes unchanged from round 2."

end R3Audit

## ===== audits/logs/ch2-epoch34-r3-axioms.log =====

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
PASS 2/3 TCSlib.Complexity.ClassNP.Nondeterminism: 820 checked declarations, all closures within the permitted triple; non-private kernel names match the reviewed 87-name inventory exactly (both directions).
PASS 2/3 TCSlib.Complexity.ClassNP.EXP: 490 checked declarations, all closures within the permitted triple; non-private kernel names match the reviewed 87-name inventory exactly (both directions).
PASS 2/3 TCSlib.Complexity.ClassNP.SAT: 786 checked declarations, all closures within the permitted triple; non-private kernel names match the reviewed 87-name inventory exactly (both directions).
PASS 2/3 TCSlib.Complexity.CookLevin.Snapshot: 41 checked declarations, all closures within the permitted triple; non-private kernel names match the reviewed 87-name inventory exactly (both directions).
PASS 2/3 TCSlib.Complexity.ClassNP.Tautology: 439 checked declarations, all closures within the permitted triple; non-private kernel names match the reviewed 87-name inventory exactly (both directions).
PASS 2/3 TCSlib.Complexity.CookLevin.Hardness: 1550 checked declarations, all closures within the permitted triple; non-private kernel names match the reviewed 87-name inventory exactly (both directions).
PASS 4: 11510 checked TCSlib declarations in the import closure; every transitive closure is within propext/Classical.choice/Quot.sound (sorryAx and any other axiom would fail this run).
R3 CLOSURE AUDIT PASS: the round-2 finding-1 surface repair discharged -- exact two-directional inventory equality on all six owned modules; axiom, target, and coverage passes unchanged from round 2.

## ===== audits/evidence/ch2-epoch34/kernel-surface-inventory.md =====

# Reviewed kernel-surface inventory — the six owned modules (round 3)

Generated from the round-2/3 verification snapshot (sources byte-identical
to `audits/evidence/ch2-epoch34/final-source-manifest.md`, asserted before
the run) by enumerating every checked kernel declaration whose name is
non-private, with no `isInternal` exemption and no prefix inference. Every
name below is bound to its class and generating declaration; the round-3
program `audits/programs/ch2-epoch34-R3Axioms.lean` embeds exactly these 87
names and asserts two-directional set equality per module. The round-2
disclosure undercounted the SAT instance family (3 of its 7 members; the
four `._proof_N` members were masked by the `isInternal` exemption the
auditor rejected) — corrected here in full.

## `TCSlib.Complexity.ClassNP.Nondeterminism` — 15 names

- `Complexity.EXP_eq_NEXP_of_P_eq_NP` — **source public** (declared in this module)
- `Complexity.NEXP_eq_iUnion_NTIME` — **source public** (declared in this module)
- `Complexity.NEXP_subset_iUnion_NTIME` — **source public** (declared in this module)
- `Complexity.NP_eq_iUnion_NTIME` — **source public** (declared in this module)
- `Complexity.NP_subset_iUnion_NTIME` — **source public** (declared in this module)
- `Complexity.P_ne_NP_of_EXP_ne_NEXP` — **source public** (declared in this module)
- `Complexity.ntime_expPow_subset_NEXP` — **source public** (declared in this module)
- `Complexity.ntime_expPow_subset_NEXP._proof_1_2` — proof-extraction auxiliary auto-generated for the source public `Complexity.ntime_expPow_subset_NEXP`
- `Complexity.ntime_expPow_subset_NEXP._proof_1_3` — proof-extraction auxiliary auto-generated for the source public `Complexity.ntime_expPow_subset_NEXP`
- `Complexity.ntime_expPow_subset_NEXP._proof_1_4` — proof-extraction auxiliary auto-generated for the source public `Complexity.ntime_expPow_subset_NEXP`
- `Complexity.ntime_poly_subset_NP` — **source public** (declared in this module)
- `Turing.NDTM.runWith.eq_1` — equation lemma auto-generated in this module for the imported public definition `Turing.NDTM.runWith` (TuringMachine/Nondeterministic.lean:129); a definitional restatement, no new claim
- `Turing.NDTM.runWith.eq_2` — equation lemma auto-generated in this module for the imported public definition `Turing.NDTM.runWith` (TuringMachine/Nondeterministic.lean:129); a definitional restatement, no new claim
- `Turing.NDTM.runWith.eq_def` — equation lemma auto-generated in this module for the imported public definition `Turing.NDTM.runWith` (TuringMachine/Nondeterministic.lean:129); a definitional restatement, no new claim
- `Turing.NDTM.stepWith.eq_1` — equation lemma auto-generated in this module for the imported public definition `Turing.NDTM.stepWith` (TuringMachine/Nondeterministic.lean:115); a definitional restatement, no new claim

## `TCSlib.Complexity.ClassNP.EXP` — 22 names

- `Complexity.EXP` — **source public** (declared in this module)
- `Complexity.EXP_subset_NEXP` — **source public** (declared in this module)
- `Complexity.ExpBound` — **source public** (declared in this module)
- `Complexity.NEXP` — **source public** (declared in this module)
- `Complexity.NP_subset_EXP` — **source public** (declared in this module)
- `Complexity.NP_subset_EXP._proof_1_1` — proof-extraction auxiliary auto-generated for the source public `Complexity.NP_subset_EXP`
- `Complexity.NP_subset_EXP._proof_1_2` — proof-extraction auxiliary auto-generated for the source public `Complexity.NP_subset_EXP`
- `Complexity.NP_subset_EXP._proof_1_3` — proof-extraction auxiliary auto-generated for the source public `Complexity.NP_subset_EXP`
- `Complexity.NP_subset_EXP._proof_1_4` — proof-extraction auxiliary auto-generated for the source public `Complexity.NP_subset_EXP`
- `Complexity.NP_subset_EXP._proof_1_5` — proof-extraction auxiliary auto-generated for the source public `Complexity.NP_subset_EXP`
- `Complexity.P_subset_EXP` — **source public** (declared in this module)
- `Complexity.P_subset_EXP._proof_1_1` — proof-extraction auxiliary auto-generated for the source public `Complexity.P_subset_EXP`
- `Complexity.enumWord` — **source public** (declared in this module)
- `Complexity.enumWord._sunfold` — structural-recursion unfolding auxiliary auto-generated for the source public `Complexity.enumWord`
- `Complexity.enumWord._unsafe_rec` — structural-recursion unfolding auxiliary auto-generated for the source public `Complexity.enumWord`
- `Complexity.enumWord.eq_1` — equation lemma auto-generated for the source public `Complexity.enumWord`
- `Complexity.enumWord.eq_2` — equation lemma auto-generated for the source public `Complexity.enumWord`
- `Complexity.enumWord.eq_def` — equation lemma auto-generated for the source public `Complexity.enumWord`
- `Complexity.enumWord.match_1` — match auxiliary auto-generated for the source public `Complexity.enumWord`
- `Complexity.exists_proj_decider` — **source public** (declared in this module)
- `Complexity.exists_proj_decider._proof_1_1` — proof-extraction auxiliary auto-generated for the source public `Complexity.exists_proj_decider`
- `Turing.solveSplitWith.eq_1` — equation lemma auto-generated in this module for the imported public definition `Turing.solveSplitWith` (TuringMachine/Build/Convention.lean:130); a definitional restatement, no new claim

## `TCSlib.Complexity.ClassNP.SAT` — 15 names

- `Complexity.SAT` — **source public** (declared in this module)
- `Complexity.SAT3` — **source public** (declared in this module)
- `Complexity.SAT3_mem_NP` — **source public** (declared in this module)
- `Complexity.SAT_mem_NP` — **source public** (declared in this module)
- `Complexity.SAT_reducible_SAT3` — **source public** (declared in this module)
- `Complexity.instDecidableEqSatStreamState` — member of the `deriving DecidableEq` family of the **private** `structure SatStreamState` (SAT.lean:2301); non-private name by Lean's derive-handler naming; unusable downstream (its type mentions a private structure)
- `Complexity.instDecidableEqSatStreamState.decEq` — member of the `deriving DecidableEq` family of the **private** `structure SatStreamState` (SAT.lean:2301); non-private name by Lean's derive-handler naming; unusable downstream (its type mentions a private structure)
- `Complexity.instDecidableEqSatStreamState.decEq._proof_1` — member of the `deriving DecidableEq` family of the **private** `structure SatStreamState` (SAT.lean:2301); non-private name by Lean's derive-handler naming; unusable downstream (its type mentions a private structure)
- `Complexity.instDecidableEqSatStreamState.decEq._proof_2` — member of the `deriving DecidableEq` family of the **private** `structure SatStreamState` (SAT.lean:2301); non-private name by Lean's derive-handler naming; unusable downstream (its type mentions a private structure)
- `Complexity.instDecidableEqSatStreamState.decEq._proof_3` — member of the `deriving DecidableEq` family of the **private** `structure SatStreamState` (SAT.lean:2301); non-private name by Lean's derive-handler naming; unusable downstream (its type mentions a private structure)
- `Complexity.instDecidableEqSatStreamState.decEq._proof_4` — member of the `deriving DecidableEq` family of the **private** `structure SatStreamState` (SAT.lean:2301); non-private name by Lean's derive-handler naming; unusable downstream (its type mentions a private structure)
- `Complexity.instDecidableEqSatStreamState.decEq.match_1` — member of the `deriving DecidableEq` family of the **private** `structure SatStreamState` (SAT.lean:2301); non-private name by Lean's derive-handler naming; unusable downstream (its type mentions a private structure)
- `Std.Sat.CNF.WidthAtMost.eq_1` — equation lemma auto-generated in this module for the imported public definition `Std.Sat.CNF.WidthAtMost` (Formulas/CNFEncoding.lean); a definitional restatement, no new claim
- `Std.Sat.CNF.fallback.eq_1` — equation lemma auto-generated in this module for the imported public definition `Std.Sat.CNF.fallback` (Formulas/CNFEncoding.lean:158); a definitional restatement, no new claim
- `Std.Sat.CNF.numVars.eq_1` — equation lemma auto-generated in this module for the imported public definition `Std.Sat.CNF.numVars` (Formulas/CNFEncoding.lean); a definitional restatement, no new claim

## `TCSlib.Complexity.CookLevin.Snapshot` — 24 names

- `Complexity.Snapshot` — **source public** (declared in this module)
- `Complexity.emitted` — **source public** (declared in this module)
- `Complexity.inputBitAt` — **source public** (declared in this module)
- `Complexity.inputBitAt.eq_1` — equation lemma auto-generated for the source public `Complexity.inputBitAt`
- `Complexity.inputPosAt` — **source public** (declared in this module)
- `Complexity.oblivious_schedule_eq` — **source public** (declared in this module)
- `Complexity.prevVisit` — **source public** (declared in this module)
- `Complexity.snapshotAt` — **source public** (declared in this module)
- `Complexity.snapshotAt.eq_1` — equation lemma auto-generated for the source public `Complexity.snapshotAt`
- `Complexity.snapshotAt_inputSymbol` — **source public** (declared in this module)
- `Complexity.snapshotAt_inputSymbol._proof_1_2` — proof-extraction auxiliary auto-generated for the source public `Complexity.snapshotAt_inputSymbol`
- `Complexity.snapshotAt_inputSymbol._proof_1_3` — proof-extraction auxiliary auto-generated for the source public `Complexity.snapshotAt_inputSymbol`
- `Complexity.snapshotAt_state_succ` — **source public** (declared in this module)
- `Complexity.snapshotAt_workSymbol` — **source public** (declared in this module)
- `Complexity.snapshotAt_workSymbol._proof_1_1` — proof-extraction auxiliary auto-generated for the source public `Complexity.snapshotAt_workSymbol`
- `Complexity.snapshotAt_workSymbol._proof_1_2` — proof-extraction auxiliary auto-generated for the source public `Complexity.snapshotAt_workSymbol`
- `Complexity.snapshotAt_workSymbol.match_1` — match auxiliary auto-generated for the source public `Complexity.snapshotAt_workSymbol`
- `Complexity.snapshotAt_zero` — **source public** (declared in this module)
- `Complexity.stepState` — **source public** (declared in this module)
- `Complexity.stepState.eq_1` — equation lemma auto-generated for the source public `Complexity.stepState`
- `Complexity.stepState.match_1` — match auxiliary auto-generated for the source public `Complexity.stepState`
- `Complexity.workPosAt` — **source public** (declared in this module)
- `Complexity.writtenOrKept` — **source public** (declared in this module)
- `Complexity.writtenOrKept.eq_1` — equation lemma auto-generated for the source public `Complexity.writtenOrKept`

## `TCSlib.Complexity.ClassNP.Tautology` — 6 names

- `Complexity.TAUTOLOGY` — **source public** (declared in this module)
- `Complexity.TAUTOLOGY_coNPComplete` — **source public** (declared in this module)
- `Complexity.TAUTOLOGY_coNPComplete._simp_1_1` — simp auxiliary lemma auto-generated for the source public `Complexity.TAUTOLOGY_coNPComplete`
- `Complexity.TAUTOLOGY_mem_coNP` — **source public** (declared in this module)
- `Complexity.coNPComplete` — **source public** (declared in this module)
- `Complexity.coNPHard` — **source public** (declared in this module)

## `TCSlib.Complexity.CookLevin.Hardness` — 5 names

- `Complexity.NPHard.polyTimeReducible` — **source public** (declared in this module)
- `Complexity.SAT3_NPComplete` — **source public** (declared in this module)
- `Complexity.SAT3_NPHard` — **source public** (declared in this module)
- `Complexity.SAT_NPComplete` — **source public** (declared in this module)
- `Complexity.SAT_NPHard` — **source public** (declared in this module)

**Total: 87 names** = 45 source publics + 27 generated auxiliaries of
source publics + 8 imported-definition equation lemmas + the 7-member
derived-instance family of a private structure.
