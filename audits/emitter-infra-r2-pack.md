# External audit pack — the emitter increment, round 2

Round 1 (`audits/emitter-infra-findings.md`): **0 blockers, 2 majors, 3
minors** — no false statement among the five contracts; both majors were
adequacy obligations. This round audits the repairs and the previously
missing evidence. The round-1 pack is immutable and stands; the design
record of every repair is `machine-library-design.md` **§11b** (attached,
inside the design document). Gate closes on **zero blockers/majors**
across the cumulative findings. Record findings in
`audits/emitter-infra-r2-findings.md`.

## Repairs under audit (map to round-1 findings)

1. **Finding 1 (major) → the clean-call bridge.** Two new sorried
   contracts in `Loop.lean`, both with canonical
   `Cfg.ofWords`/`stateWord` entry **and** exit seams, first-positive-
   visit exit discipline, arbitrary untouched native input, and
   envelopes `c·(T |arg| + |arg| + |f arg| + 1)`:
   `exists_installCallTM` (result installed as the tape-resident word,
   nothing emitted) and `exists_emitCallTM` (argument preserved, chunk
   forwarded). Audit their **truth** (the log/undo sandbox route: run
   the witness captured and logged, undo charging the visited region to
   elapsed time, install or replay, erase, rewind — the A-continuation's
   proved in-file pattern is the template) and **adequacy** (they, plus
   the function contracts, now close what finding 1 showed the function
   contracts alone cannot: the seam entry problem for loop and
   emit-loop bodies). Check the seam choice (argument as the sole
   `stateWord` word) against the embedding vocabulary consumers will
   use, and the envelope's `|f arg|` term against install/replay costs.
2. **Finding 1's required resolution → the 3B normalization mapping**
   (§11b item 2). The committed instantiation plan names the encoded
   state data `(cursor, consumed-prefix length, phase tag)`, eliminates
   `satRed_start`'s permanent marker, handles buffering round-locally,
   fixes `R` = serialized input length with an absorbing finished phase
   emitting empty chunks, and routes token reads / counter updates /
   chunk emission through the bridges and the token/append contracts.
   Audit feasibility against the **attached** `SAT.lean` (the full
   `satRedTM` table, its proved startup stages, and the banked
   `satReduction_*` semantics): is any step of this mapping
   structurally blocked? Positive round duration, input-length-only
   budgets, and the function identity with the banked semantics are the
   points to press.
3. **Finding 2 (major) → the evidence addendum.** This bundle attaches
   everything round 1 found missing: the model definitions
   (`Configuration`, `Deterministic`, `Simulation` — `step`,
   `Action.apply`, boundary machinery, the embedding vocabulary); the
   phase-4 records (`ch2-phase4-{findings,resolutions}.md` — the
   six-stage output-silence contract and the exact serialization
   ledger); the customer grammars and statement layers
   (`Formulas/{CNF,CNFEncoding,DNF}.lean`, `ClassNP/SAT.lean`,
   `ClassNP/Tautology.lean`, `CookLevin/{Snapshot,Hardness}.lean`); the
   closure program and the lint program; and the **pinned diffs of both
   spec commits** (round 1's `883ebc79` and this round's repairs
   commit), which make the append-only/no-deletion attestations
   independently checkable. Re-audit the round-1 model-level
   derivations (findings 6–9) against the now-attached definitions, and
   certify or refute the customer-fit claims that round 1 correctly
   refused to certify from missing evidence.
4. **Finding 2's required resolution → the 4A stage mapping** (§11b
   item 3): all-string validation as a decision prefix **before any
   irreversible emission** (W3 over the parser/boundary checks; invalid
   branch emits the fixed fallback by finite control); `R` = the
   snapshot-index bound; one clause group per round through the emit
   call; the exact ledger as the sum of per-round chunk lengths;
   terminators as the last chunk's tail or a post-loop constant. Audit
   this against the attached phase-4 records per decision 11.3 — 4A's
   brief waits on this gate.
5. **Finding 3 (minor) → the host-routing sketch correction** in
   `exists_emitLoopTM`'s docstring (forwarding variant through
   `emitAction`; new prefix-summation lemma; the refuting witness
   acknowledged). The statement is unchanged — verify the corrected
   sketch is now feasible.
6. **Finding 4 (minor) → the token-convention correction** in
   `unaryTokenSplit`'s docstring, with the auditor's separating example
   embedded; markers/polarity are scanner grammar states.
7. **Finding 5 (minor) → documentation.** The four definitions now
   carry customers and construction notes. The round-1 attestation-4
   claim is restated precisely: the **seven contracts** each carry
   statement prose, construction sketch, named customers, and the
   spec-phase flag; the **four definitions** each carry statement
   prose, customers, and a construction note.
8. **§11a item 1 corrected** (P17): fixed finite-control chunks are
   emitted directly by body control; unbounded chunks via
   `exists_emitCallTM`; no appeal to the private `constTM` (§11b
   item 6).

## Maintainer attestations (verify or challenge)

1. Fresh 57/57 sweep on the repaired tree, zero `error:` lines,
   admissions **20 = 13 campaign + the 7 spec contracts**
   (`audits/logs/emitter-r2-sweep.log`, attached).
2. The epoch-2 closure regression program re-run **with full root
   prints** at the repaired tree, exit 0, every expectation unchanged
   (`audits/logs/emitter-r2-axioms.log`, attached — round 1's
   provenance qualification on the truncated log is thereby addressed;
   the program itself is attached).
3. Both spec commits attached as pinned patches: round 1's `883ebc79`
   (1,467 insertions, 0 deletions) and this round's repairs commit
   (docstring corrections on the new material + the two bridge
   contracts + §11b; **no pre-existing declaration touched in
   either**).
4. Lint on `Build/`: 0 FAIL / 2 WARN, the standing size exceptions
   (`audits/logs/emitter-r2-lint.log`, attached).

Severity scheme as always; findings to
`audits/emitter-infra-r2-findings.md`; this pack is immutable once sent.

## Bundle manifest

**31 attachments** after the pack: the 4 repaired `Build/` sources; the
5 model files (`Finite`, `Composition`, `Configuration`,
`Deterministic`, `Simulation`); the design document (§11–§11b); the 3
grammar files (`Formulas/{CNF,CNFEncoding,DNF}`); the 4 customer files
(`ClassNP/SAT`, `ClassNP/Tautology`, `CookLevin/Snapshot`,
`CookLevin/Hardness`); the 2 customer frontier REPORTs (epoch-3 A and
B); the 2 phase-4 records; the prior infra-gate record
(`ch1-infra-resolutions.md`); the closure program; the lint program;
the 2 pinned spec-commit patches; the 3 round-2 logs; the 57-module
order list; the round-1 findings (for cumulative reference).
Total 4+5+1+3+4+2+2+1+1+1+2+3+1+1 = 31.
