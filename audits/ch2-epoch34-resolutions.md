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


---

# Round 3 → GATE CLOSED

Round 3 (`audits/ch2-epoch34-r3-findings.md`, preserved verbatim)
returned **PASS — cumulative 0 blockers / 0 majors / 1 minor**. The
surface major closed at the supplied-evidence standard, the auditor
verifying the checker's executable semantics against eight negative
fixture classes and independently re-deriving the 87-name accounting
(45 + 27 + 8 + 7, per-module 15/22/15/24/6/5).

Closing sweep (this record's commit):

- **Finding 3 (minor)**: the inventory's seven derived-instance rows no
  longer claim downstream unusability — the auditor's compiling
  consumer refuted that rationale — and now state only that these are
  non-private generated constants whose types mention a private
  structure; a dated correction appendix is in the inventory file. All
  seven remain certified inventory members.
- **Note 4a**: the dead 11-entry `generatedExceptions` array is retired
  from the committed `ch2-epoch34-R3Axioms.lean`; the cleaned program
  was re-run against the same pinned snapshot and tree —
  `R3 CLOSURE AUDIT PASS`, exit 0, identical pass lines
  (`audits/logs/ch2-epoch34-close-axioms.log`). The round-3 pack's
  literal "no exceptions array" claim is hereby corrected to "no
  exception-based acceptance" for the as-sent program; the as-committed
  program now satisfies the literal reading too.
- **Note 4b**: `enumWord._unsafe_rec` is reclassified as the
  partial-recursive implementation companion
  (`addAndCompilePartialRec`), `_sunfold` as the smart-unfolding
  auxiliary.
- The round-2/3 evidence-boundary qualifications (maintainer-verified
  execution records; census provenance) stand as permanent annotations.

**Gate position: CLOSED — three rounds, final tally 0 blockers /
0 majors; every minor swept or corrected on record.** The 21 epoch-3/4
targets, their 1,206 net new privates, the carrier retype, the merge
drift, and the duplicate-dispatch governance are audited. With the
epoch-1, epoch-2, emitter-statement, and emitter-fill gates, every fill
of the Chapter-2 campaign is externally audited; the campaign tree
stands at zero admissions.
