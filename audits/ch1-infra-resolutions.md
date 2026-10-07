# Shared infrastructure audit — resolutions. GATE: CLOSED

Three adversarial rounds over the machine-construction library's spec
layer and the timed-universal bridge export
(`audits/ch1-infra-{pack,bundle}.md` → `…-findings.md` →
`…-r2-{pack,bundle}.md` → `…-r2-findings.md` → `…-r3-{pack,bundle}.md` →
`…-r3-findings.md`). Round 3: **0 blockers, 0 majors, 3 minors — gate
condition met**; the three minors are documentation-only and are swept in
the closing commit (ledger below). This disposition authorizes **no**
claim that any sorried contract has been filled: the library's 23
contracts are now audited-true statements awaiting their fill batches.

## Round ledger

| Round | Verdict | Substance |
|---|---|---|
| 1 | 1 blocker, 2 majors, 4 minors, 1 note | `exists_loopTM` refuted (zero-step advance; the auditor's one-state instantiation plus the input-head information bound); round domain over all state words excluded the customers; D5 rejected (no dynamic assembly, no result-bearing search). The bridge export and discharge passed the completed-proof audit with **no findings** — that verdict was carried forward unchanged through rounds 2–3. |
| 2 | 0 blockers, 1 major, 3 minors | The redesigned loops (positive duration; input-indexed invariant; input-dependent step/accept), `exists_loopFindTM`, P13/P14/C1, and the §9b instantiation tables all **passed re-attack**; both round-1 refutations formally discharged. The major: the final-answer conclusion cannot discharge the frozen configuration-level `enumMachine_contracts` (the delay-machine separation). Nearly all historical attestations verified down to git blob identity. |
| 3 | **0 blockers, 0 majors, 3 minors — CLOSED** | `exists_loopCfgTM` (the configuration-level export) passed, with the auditor supplying the worst-case segment ledger and the **exact** translation onto the unchanged `enumMachine_contracts` (terminal index `2^w = R+1`, bounded orbit bridge `s_i = enumWord w i` for `i < 2^w`, budget domination `b = K(A+1)`, `e = D`) — "no customer-statement edit or replacement decider theorem is needed". D5 v3 approved per row. Stability verified byte-exactly against the hash-matched round-2 bundle. |

## Closing sweep (round-3 minors, repaired in the closing commit)

| # | Finding | Sweep |
|---|---|---|
| R3-1 | The "`loop_run` + monotonicity" corollary description is incompatible with `loop_run`'s empty-output terminal hypothesis (the exported terminal is `[false]`), and "forms" overstated the find form | All four description sites corrected (Loop module docstring, the cfg export's docstring, the decision form's note, design doc §9c): the decision form is a corollary through an **already-halted-terminal summation lemma** (the `enumLoop_run` shape), added at fill time without touching the frozen `loop_run`; the find form shares the host construction with the payload surfaced and is not claimed as a `loop_run` corollary. |
| R3-2 | The cfg sketch read an amortized aggregate bound off individual segments | Sketch rewritten with the width-based worst case: the fuel word has length ≤ `T \|x\|` and never grows, so every debit, rewind, and the final underflow-plus-emission each cost `O(T \|x\| + 1)` — no amortization needed per segment. |
| R3-3 | "The middle one is false without the shift" pointed at `incFixed = enumInc` | §9c now names the split-search equality. |

All closing edits are **comment-only**: statement slices of all four loop
declarations byte-identical, and the comment-stripped module is
byte-identical to the round-3-audited state (checked with the corrected
stripper recipe of the phase-3 erratum); `Build/Loop` re-elaborated
clean, lint 0 FAIL / 0 WARN on `Build/`.

## Errata ledger (maintainer, acknowledged across the rounds; packs preserved unmodified per precedent)

1. Round-1 attestation 4 labeled Unicode character counts as bytes
   (4,022/625 chars vs 4,085/651 bytes); corrected attestation with
   per-slice SHA-256 supplied in round 2, independently reproduced by the
   auditor.
2. Round-1 attestation 5's "import leaves" was literally false
   (`Convention` is imported by its Build siblings); restated as the
   outside-Build boundary claim with unfiltered grep evidence.
3. Round-1's lint claim described one invocation; full totals are 0 FAIL,
   7 WARN over 38 files, all seven under recorded escalations (quoted in
   the round-3 pack, attestation 6).
4. "Standard triple" overstated the Convention lemmas' prints (proper
   subsets: `[propext, Quot.sound]`; `[propext]`).
5. The immediate pre-export `Universal.lean` baseline was 2,834 lines,
   not 2,831 (the epoch-4A figure).
6. Two round-2 attack-commentary claims (zero-tape `q₀ = anchor`
   startup; off-invariant noncomputable `acceptF`) were too broad and are
   withdrawn without replacement.
7. The round-3 pack's "`loop_run` + monotonicity" corollary wording —
   R3-1 above.
   (Round-1's pre-ship manifest miscount, 17 vs 19, was caught and fixed
   by the maintainer before sending and is recorded in the session log,
   not an auditor finding.)

## Dispositions (final)

* **D4 — approved** (round 1, carried through): 2C's
  `prefixTM`/`fixedPair` promotion requests are subsumed by P3/P6; the
  proved budgets are instances of the stated linear forms; provenance
  verified from the attached batch-C report.
* **D5 — approved as version 3** (round-3 item 7), scoped to the epoch-2
  frontiers and P10: 2A at statement/interface level via
  `exists_loopCfgTM` + the §9b/§9c instantiation; P10, `pairedVerifier`
  (both orientations of P8 via the recorded pairing assembly),
  `paddedVerifier` (P10 at `(C+1, c)`, P8 at `(C, c)` — the coefficient
  shift), D-WRAP (guarded P13), D-EMIT (the canonical `H/s/t` pairing
  derivation + exact P5 unary outputs) approved; **D-MEM approved as
  explicitly limited** (timed variable-prefix extraction, unary-shape
  checks, and complete-answer recognition are named continuation
  obligations); 2B component-level only (the NDTM reverse direction is
  outside library coverage by design); clearing accepted as an internal
  discipline with per-body restoration proofs owed at fill; **E3/E4
  deferred** to those epochs' brief audits.
* **Vocabulary equalities** (round-2 note 5): `splitAtLastTrue =
  stripCertificate`; `incFixed = enumInc`;
  `solveSplit (C+1) c = certificateSplit C c` — the shift is mandatory
  and is recorded in §9c and the P10 pipeline parameters.
* The audit's pairing derivation and the C1 cross-component caveat are
  adopted as the canonical assembly recipe (§9c).

## Residual evidence limits (recorded, not defects)

Fresh-olean execution, toolchain, and mathlib-pin claims remain
execution attestations (the auditor had no Lean executable); 2B's
detailed simulation-core customer verification awaits its continuation
round with the `Nondeterminism.lean` source in scope; the escalation
records' provenance is the decision logs, attested but not attached.

## What closes, what opens

Closed: the library spec surface — `Convention` (proved) plus **23
audited-true sorried contracts** (4 wrapper, 4 loop, 15 primitive) — and
the bridge export + TMSAT discharge (proof-audited in round 1, blob-pinned
unchanged since). Next per the frozen sequencing
(`machine-library-design.md` §10): the **library fill batches**
(harvest-adaptation; the loop fill flagged for continuation budget, now
with the auditor's items 4–5 as its construction ledger), then the E2
continuation briefs citing the library.
