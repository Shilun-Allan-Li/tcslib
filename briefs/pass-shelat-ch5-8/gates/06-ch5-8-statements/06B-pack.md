# Gate 06B (Pass–shelat §6.2, secure computation): external statement audit pack

**Status: internal reconciliation draft (2026-11-07); not issued or staged.** Reviewed source
reference: `e9d64158461bfe24ddc88ab885bc4017899b4c16` on the pushed integration branch. This is
not an issued audit pin: Rule-10 seals remain pending. The current 467-module source/object
manifest has zero stale records; any subsequent source repair requires an affected replay.
Historical prong heads are provenance only. The recorded auditor choice is Codex (findings
Markdown in chat); the user dispatches the job. No readiness attestation is made here.

**What is audited:** [PS10] §6.2 as formalized in `TCSlib/Cryptography/SecureComputation/`:
definitions, statements, docstrings and proof sketches, against the sources. Proofs are out of
scope, except the short ones that carry a definition's correctness (correctness of OT, of the
special encryption, of garbling and of Yao; the composition's phase lemmas). The deliverable is
**`gate06B-findings.md`**.

**Sources required at issue (availability is not yet attested):** [PS10] R. Pass, a. shelat, *A Course in Cryptography*, 3rd ed.,
January 2010 (book page = PDF page − 12), §6.2, book pp. 154–164. [Gol04] O. Goldreich,
*Foundations of Cryptography, Volume 2*, §7.3 (including Theorem 7.3.3) and Appendix C.1.
Locate and supply the source/excerpts for these comparisons; this draft does not replace
access to the cited source with standard knowledge.

## Scope

| Item | Where | State |
|---|---|---|
| Def 155.1 (honest-but-curious security; polynomial-time parties, ruled) | `SecureComputation/Defs.lean` | defined |
| Def 160.a, Prot 160.4, Prop 161.5 (OT) | `ObliviousTransfer.lean` | correctness proved; Prop 161.5 stated |
| Alg 157.2, Claim 157.a (special encryption) | `SpecialEncryption.lean`, `SpecialEncryptionSecurity.lean` | correctness proved; claim stated |
| Constr 158.a, Claim 159.a (garbling) | `Garbling.lean`, `GarblingSpecial.lean`, `GarblingSecurity.lean` | deterministic part proved; probabilistic part stated |
| The hybrid model and [Gol04, Thm 7.3.3] | `Hybrid.lean`, `Compose.lean`, `ComposePhases.lean`, `ComposeSecurity.lean` | phase lemmas proved; theorem stated |
| Prot 162.6, Thm 163.7 (Yao) | `Yao.lean` (OT-hybrid), `YaoReal.lean` (real protocol) | correctness proved; Thm 163.7 stated, the real form by composition |

## Prior findings (verify the repairs)

1. **OT has five messages:** D8 reads a party's output as its next-message function on its
   complete history.
2. **Prop 161.5 no longer assumes sampler canonicity.** `SamplerCanonical` is a theorem from
   `Collection.sample_eq_encD`. Canonical decoding derives the local decoder-wide `hspec`
   through `Collection.apply_of_decD` from the retained canonical-only equation
   `henc : ∀ i x, H (pairEncode i (T.encD i x)) = [h i x]`. The explicit polynomial-time
   evaluator hypothesis `hH : PolyTimeComputable H` and **`EnhancedHardCore` remain**.
   Bob's sampler coins remain visible in his view, so ordinary hard-core security does not
   replace the enhanced hypothesis. Real Yao retains these OT hypotheses.
3. **Garbling: `Good`** means correct opening under every assignment's keys.
4. **Efficiency is in Def 155.1** (ruled): `Efficient` strategies and bounded honest messages.
5. **Yao in the OT-hybrid model, then composition** (ruled, Q-5).

## Integrated API and construction context

All thirteen secure-computation modules and the topic facade are included. Public interfaces
cover real/ideal sampler equations, predicate characterizations, functionality/strategy/protocol
fields, and simulator run/coin contracts. Composition and Yao read the shared interaction
layer through public lemmas. Correctness/phase lemmas remain distinct from admitted security
and efficiency statements. Rule-10 seals remain pending; the current native source/object
manifest is reconciled, with affected rechecks required after further source repairs.

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

1. **Def 155.1** (`HBCSecure`, `Functionality.PolyTime`). Is the reading (private outputs,
   polynomial lengths, one negligible bound for all inputs of a length) faithful? Is the
   efficiency requirement (`Efficient` strategies and polynomially bounded honest messages; ruled)
   the source's p.p.t. protocol in this model? Does the output clause still force correctness?
2. **OT (Prot 160.4, Prop 161.5).** Are the five messages (D8's output convention) harmless? Are
   collection-derived canonicity and the canonical-only `henc` interface correct? Does
   `Collection.apply_of_decD` supply the specification correctness uses? Are the retained
   `hH` and **enhanced** hard-core hypothesis (`EnhancedHardCore`, with sampler coins visible)
   correctly propagated to `yaoProtocol_hbcSecure`? Compare with [Gol04, App. C.1].
3. **Garbling (Alg 157.2, Constr 158.a, Claims 157.a, 159.a).** Is `nestedSpecial` Alg 157.2
   applied in layers? Is `Good` the right notion? Is the bound of `garbling_good_whp` stated over
   the right distribution?
4. **The hybrid model and composition** (`Hybrid.lean`, `Compose*.lean`). Is "ideal calls first"
   a faithful special case of [Gol04, §7.3.1]'s oracle-aided protocols for Yao? Is the composed
   protocol's layout (pairs with fillers, a lead filler, no trailing filler) the sequential
   composition? Check the phase lemmas' statements. Is `hbcSecure_compose`'s added hypothesis
   (`main` has at least one move) necessary (the worker's counterexample) and sufficient?
5. **Yao (Prot 162.6, Thm 163.7).** Compare `yaoHybrid` with the source's protocol. Check each
   declared deviation: the XOR-shift row order, the output decoding pairs, sink output vertices
   (`outs_sink`: without it the decoding pairs leak), `n` bit OTs per input wire, the joint PRF
   hypothesis `hG₁₂`, the uniform circuit family. Is `yaoProtocol_hbcSecure` (real protocol, by
   composition) the source's Thm 163.7?

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
