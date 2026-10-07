# Epoch 4 (final fill round + campaign closure) — audit loop resolutions (CLOSED)

Protocol: `AroraBarakChapter1Plan.md` §5 "Fill campaign". External auditor:
cross-vendor LLM per decision log.

## Round 1 (`epoch4-pack.md` → `epoch4-findings.md`, audited at `fd7bb18e`)

**Zero blockers, zero majors.** The most thoroughly reproduced round of the
campaign. The auditor confirmed the bundle SHA-256, verified the 34 extracted
modules byte-identical to the audited commit, and — with a working Lean
environment — independently reproduced the kernel-level evidence that previous
rounds could only assess at source level:

- **A fresh full sweep** on a separate checkout at `fd7bb18e` with an initially
  empty campaign olean directory: 34/34, exit 0, zero errors, zero gate
  failures, **zero admission warnings**, 34 fresh oleans, at the pinned
  Lean 4.25.0 / mathlib `029db123ddaa`.
- **All eight headline axiom prints** reproduced exactly
  (`[propext, Classical.choice, Quot.sound]`), plus a dependency traversal of
  **3,984 imported campaign constants** (private and generated declarations
  included) finding **zero** depending on `sorryAx`.
- **The timed fill certified**: all five binding obligations traced to the
  delivered lemmas (clock/code separation with the canonizer receiving exactly
  `α`; lane-5 buffering with the halting transition's emission captured via the
  `emitStart` mapping before the flush; exactly one fixed-width borrow per
  source transition; the stopped controller confined to proofs — no leakage
  into `timedUniversalTM`; both deadline boundaries). The **divergent-source
  timeout** was singled out and certified: the induction is on remaining
  numeric credit with an arbitrary source configuration, exactly `t`
  transitions are applied before the underflow branch really halts with
  `[false]`, and the apparent eventual-halting premise in `timedCapture_start`
  concerns only the canonizer stage, discharged by the scheme's total
  contract. The cost ledger was re-summed phase by phase to
  `C = S + B + 14`, including the every-step-emitter case and the terminal
  unsuccessful lookup.
- **Merge-refactor conformance reproduced end-to-end** from the fetched span
  endpoints: 168/107/240 declarations per split with identical ordered
  sequences, the exact 21/53/77 promotion sets each with a syntactic
  cross-module use, byte-identical relocation blocks, and the single added
  `rfl` — ablated in an isolated copy to confirm it repairs exactly one
  residual reflexive goal. Public surface: 227 → 378 names, zero lost, the 151
  gains exactly the promotions; all eight headline headers byte-identical to
  the epoch-3 audited commit.
- **Delivery provenance** verified from a cached copy of the `epoch4-A.zip`:
  manifest digests, flat-source identity with the integrated tree,
  patch-application reproducing the bundle commit's tree, and blob identity of
  the agent commit and the integrated commit.
- All six specific questions answered in the construction's favor, including
  deadline zero against a source first halting at time one (timeout, success
  antecedent vacuous) and the final transition that both halts and emits (bit
  retained).

Three minors, resolved in the closing commit:

| Finding | Resolution |
|---|---|
| 1 minor — pack attestation 2 described the post-refactor and post-fill sweeps as runs "at this tree content"; the trees differ (`ff2161e4` still carried the `timed_universal` admission, correctly recorded in the plan) | Erratum acknowledged; the shipped pack is preserved as the historical artifact (standing precedent). The correct statement: the post-refactor sweep had exactly one expected admission warning; only the post-fill sweep of `fd7bb18e` — the tree this pack audits — is admission-free |
| 2 minor — the promoted `universalEval_step`'s docstring was a bare label ("Read-based administrative step rule"), so the pack's promotion-wide statement-prose claim held only for mechanical presence, not quality | Docstring upgraded to a full natural-language statement per the auditor's proposal (comment-only, verified by comment-stripped diff; tail re-check from `UniversalInterpreter` through the facades clean). The pack's overclaim is acknowledged; statement-prose *quality* remains review judgment, as `style_lint.py` documents |
| 3 minor — three stale location descriptions: pack attestation 1 counted `exists_codeTM` among declarations that "changed file" (it moved *within* `Encoding.lean`); `Universal.lean`'s module docstring still said the file "holds only the public statements" (it now also holds the 130-declaration epoch-4 private layer); plan §5 design question 1 still said the bridge "stays private in `Encoding.lean`" (it lives in `MathlibBridge.lean` since the merge) | Pack erratum acknowledged (preserved as shipped); the module docstring and the plan sentence corrected — the plan text now records the implemented quarantine while explicitly keeping all three parts of design question 1 open. Both Lean edits verified comment-only |

Note-level dispositions:

- **Findings 4–6** (obligations, divergence, cost): certifications — recorded
  above; no change identified.
- **Finding 7** (refactor methodology): adopted — future freeze attestations
  retain ordered declaration/signature comparisons **and** namespace/`open`/
  `section` context checks alongside name counts and multisets.
- **Finding 8** (closure evidence): the distinction between *reproduced
  artifact properties* and *historical maintainer executions* is preserved
  here and in the record: what stands audited is the tree at `fd7bb18e` as
  independently re-elaborated, not any log of past runs.
- **Finding 9**: no architectural verdict was issued; **both human-reserved
  design questions remain open** (plan §5, questions 1 and 2 — question 1's
  text now reflects the implemented quarantine without closing it).

**Epoch-4 audit gate closed — the campaign's final gate.** All 21 audited
sorries are proved, integrated, and audited; the tree is admission-free and
independently re-elaborated at the pin. Remaining post-campaign work, none of
it proof: the blueprint extraction (`/blueprint-extract`), the two open design
questions (human), and the deferred phase 5 (§1.7 `O(T log T)`, RAM-TM,
further Mathlib bridging).
