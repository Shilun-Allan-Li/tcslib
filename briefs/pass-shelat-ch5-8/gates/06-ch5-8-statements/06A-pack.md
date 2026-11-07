# Gate 06A (Pass–shelat ch. 5, authentication): external statement audit pack

**Status: internal reconciliation draft (2026-11-07); not issued or staged.** Reviewed source
reference: `e9d64158461bfe24ddc88ab885bc4017899b4c16` on the pushed integration branch. This is
not an issued audit pin: Rule-10 seals remain pending. The current 467-module source/object
manifest has zero stale records; any subsequent source repair requires an affected replay.
Historical prong heads are provenance only. The recorded auditor choice is Codex (findings
Markdown in chat); the user dispatches the job. No readiness attestation is made here.

**What is audited:** [PS10] ch. 5 as formalized in `TCSlib/Cryptography/Authentication/`: definitions, statements, docstrings and proof sketches, against the
sources. Proofs are out of scope, except the short ones that carry a definition's correctness
(`correct` fields, length lemmas). The deliverable is **`gate06A-findings.md`**.

**Sources required at issue (availability is not yet attested):** [PS10] R. Pass, a. shelat, *A Course in Cryptography*, 3rd ed.,
January 2010 (book page = PDF page − 12), §5.1–5.6, book pp. 133–145.

## Scope

| Item | Where | State |
|---|---|---|
| Defs 134.1, 134.2 (MACs and their security) | `Authentication/Defs.lean` | defined |
| Defs 135.1, 136.2, 136.a (signatures; many-message and one-time security) | `Defs.lean` | defined |
| Def 140.1 (CRH families) | `Defs.lean` | defined, with the domain repair |
| Prot 134.3 and Thm 135.4 (a PRF gives a MAC) | `PRFMAC.lean` | Thm stated |
| Prot 137.1 and Thm 137.2 (Lamport) | `Lamport.lean` | correctness proved; Thm stated |
| Prot 142.2 and Thm 142.3 (the discrete-log hash) | `DLHash.lean` | Thm stated |
| Prot 144.2 and Thm 144.1 (hash-and-sign) | `HashAndSign.lean` | correctness proved; Thm stated; the existence corollary proved |

## Prior findings (verify the repairs)

1. **`CRH` carries membership tests for `D_i` and `R_i`**, compression is a proved property from a
   threshold on, and the collision game requires both inputs in `D_i`. With fixed-length domains
   and no tests, Thm 142.3 had trivial collisions.
2. **Thm 142.3 is stated for full groups** (`m = p − 1`) with `D_i = {(x, b) : x < m}`: the
   source's "`n`-bit `x`" needs exponents below `p − 1`.
3. **Thm 144.1 needs a full-domain CRH:** the CRH game counts only in-domain collisions, so
   without the hypothesis the theorem is false.
4. **Thm 137.2:** p. 138's "greater than" means "at least".

## Integrated API and dedup context

Public ordinary-function/predicate readers, explicit structure-field equations, machine
run/coin contracts, and topic/root exports are present. Lamport uses the shared
`TCSlib.Cryptography.coinBlock` and length lemma from `Asymptotic/Adversary.lean`. Its local
padding theorem is deleted in favor of `Collection.ofFn_padFin_of_le` from
`Asymptotic/CollectionsHelpers.lean`, with the empty padding suffix simplified at equal
length (DL-6/DL-7). These interface repairs do not fill the substantive security admissions.

## Brief for the auditor

You are auditing the **trusted surface**. Hunt for:
1. **Infidelity:** a definition or statement that differs from the source's other than by a
   declared deviation; check that each declared deviation is benign or that its cost is stated.
2. **Wrong semantics:** a definition that does not compute what its docstring says.
3. **Trivialization:** vacuous hypotheses; games won or lost for degenerate reasons (`n = 0`,
   empty domains, a budget of 0).
4. **Wrong strength:** a theorem weaker or stronger than its docstring claims.
5. **Attribution:** `policy.md` §2.

For **every definition**, restate it in your own words before reading its docstring. For
**every theorem**, say in 1–3 sentences whether the statement is what its docstring claims. Attempt
at least **three adversarial instantiations**. Do not give a blanket approval.

## Specific questions

1. **The search games** (`forgeGame`, `collisionGame`). Is "`m` unqueried" checked against every
   query? Is the one-time game's budget exactly one signing query? Is a forger's output read at
   the right lengths?
2. **CRH (Def 140.1).** Is the repaired `CRH` (membership tests, `Compresses` from a threshold)
   the source's definition? Does the threshold weaken it?
3. **Thm 142.3.** Is the discrete-log hypothesis (`G.DLHard`, with `ExpValid` and `m = p − 1`)
   the source's assumption? Is the one-bit compression real at every large `n`?
4. **Thm 144.1.** Is the full-domain hypothesis the minimal repair? Is `exists_oneTimeSecure_of_crh_owf`
   the source's conclusion?
5. **Lamport.** Is the key layout (`lamportPkBlock`) and `Ver`'s length check faithful?

## Pending issue-time attestations

- Exact final source/records commits and matching source bundle/manifest, after the common
  preparation in `PLAN.md`; the internal source reference above is not an issued pin.
- Final source-matched affected replay/downstream checks, `sorry` census and axiom records.
- Rule-10 elaborated-term/anonymous-command coverage, installed seals, sensitivity controls and
  explicit-unfold scan; inherited failures classified against the actual PR base.
- Style/API lint comparison and precise existing exceptions; source attachments with hashes.
  Earlier union/API replay summaries concern staged sources. The later
  `evidence-run/seal-ready-pinned.json` reconciles all 467 current source/object/prerequisite
  records; seal-driven repairs must be checked again in their affected closure.


## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide:
- **blocker:** a downstream phase would build on a wrong statement;
- **major:** a statement is fixable but materially misleading as it stands, or accumulated debt
  that the gate may not close over without explicit human acknowledgment;
- **minor:** an edge case, or a naming or attribution defect;
- **note:** an observation; no change required.

The gate closes at **0 blockers and 0 majors**.

**Not yet clear to merge — common verification, source attachments and user dispatch remain.**
