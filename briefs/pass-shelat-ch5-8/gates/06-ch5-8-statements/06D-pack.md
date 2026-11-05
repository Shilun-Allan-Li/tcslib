# Gate 06D (Pass–shelat ch. 8, randomness): external statement audit pack

**Status: draft** (2026-11-05). It pins to the integration commit of gate 06 (`PLAN.md`: after
#195 lands, prongs A–D merged onto it, one fresh replay). The content below is prong D (`cryptography/pass-shelat-ch5-8-prong-d`) at
`6ea900ae`, complete in the statement phase. The attestations are filled at staging.

**What is audited:** [PS10] ch. 8 as formalized in `TCSlib/Cryptography/Randomness/`, with the PAC layer of gate 05 as context: definitions, statements, docstrings and proof sketches, against the
sources. Proofs are out of scope, except the short ones that carry a definition's correctness
(`correct` fields, length lemmas). The deliverable is **`gate06D-findings.md`**.

**Sources attached separately:** [PS10] R. Pass, a. shelat, *A Course in Cryptography*, 3rd ed.,
January 2010 (book page = PDF page − 12), §8.1–8.3, book pp. 179–184.

## Scope

| Item | Where | State |
|---|---|---|
| Def 179.a (the learning game) | the PAC layer (`TCSlib/LearningTheory/PAC/`, gate 05), with `Randomness/Learning.lean` | defined |
| Thm 179.1 (PRFs give an unlearnable class) | `Randomness/Learning.lean` | (a), (c) proved; (b) stated |
| Thm 180.1 (PRGs give `BPP ⊆ DTIME(2^{n^ε})`) | `Randomness/Derandomization.lean`, with `BPPBridge.lean` | stated; the bridge proved |
| Thm 183.6 (no efficient one-bit extractor for efficient sources) | `Randomness/Extraction.lean` | stated |

## Findings already made (check the repairs, do not re-find them)

1. **Thm 183.6 needs a polynomial-time `Ext`** (source gap: "`X` is computable since `Ext` is").
   It is stated at every `n`, which is stronger than the source's existential.
2. **Thm 179.1** is read through the information-theoretic PAC layer (#194, gate 05): the
   prediction game, then weak PAC learning under the uniform distribution.

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

1. **Thm 179.1.** Is `prfConcept` (the first output bit) the source's class? Is `learnerOf` a
   faithful non-adaptive learner? Does (c) follow from (b) as the docstring says?
2. **Thm 180.1.** Does the S3c bridge (`verifier_toNUPPT`, `randProb_eq_uprob`) make `main`'s
   BPP and the NUPPT model meet without changing either? Is `subexpBound` the source's
   `2^{n^ε}`?
3. **Thm 183.6.** Are `samplerLaw` and `effSources` the source's "efficiently computable
   `(n − 2)`-sources"? Is `extBit` the right one-bit function of `Ext`?

## Attestations (filled at staging)

- Elaboration (the integration replay), `sorry` list, axioms, lint.

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
