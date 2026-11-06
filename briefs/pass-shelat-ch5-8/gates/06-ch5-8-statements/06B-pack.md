# Gate 06B (Pass–shelat §6.2, secure computation): external statement audit pack

**Status: draft** (2026-11-05). It pins to the integration commit of gate 06 (`PLAN.md`: after
#195 lands, prongs A–D merged onto it, one fresh replay). The content below is prong B
(`cryptography/pass-shelat-ch5-8-prong-b`) at `587843c7`, complete in the statement phase. The
attestations are filled at staging.

**What is audited:** [PS10] §6.2 as formalized in `TCSlib/Cryptography/SecureComputation/`:
definitions, statements, docstrings and proof sketches, against the sources. Proofs are out of
scope, except the short ones that carry a definition's correctness (correctness of OT, of the
special encryption, of garbling and of Yao; the composition's phase lemmas). The deliverable is
**`gate06B-findings.md`**.

**Sources attached separately:** [PS10] R. Pass, a. shelat, *A Course in Cryptography*, 3rd ed.,
January 2010 (book page = PDF page − 12), §6.2, book pp. 154–164. [Gol04] O. Goldreich,
*Foundations of Cryptography, Volume 2* (§7.3, App. C.1), if available to the auditor; otherwise
standard knowledge of it.

## Scope

| Item | Where | State |
|---|---|---|
| Def 155.1 (honest-but-curious security; polynomial-time parties, ruled) | `SecureComputation/Defs.lean` | defined |
| Def 160.a, Prot 160.4, Prop 161.5 (OT) | `ObliviousTransfer.lean` | correctness proved; Prop 161.5 stated |
| Alg 157.2, Claim 157.a (special encryption) | `SpecialEncryption.lean`, `SpecialEncryptionSecurity.lean` | correctness proved; claim stated |
| Constr 158.a, Claim 159.a (garbling) | `Garbling.lean`, `GarblingSpecial.lean`, `GarblingSecurity.lean` | deterministic part proved; probabilistic part stated |
| The hybrid model and [Gol04, Thm 7.3.3] | `Hybrid.lean`, `Compose.lean`, `ComposePhases.lean`, `ComposeSecurity.lean` | phase lemmas proved; theorem stated |
| Prot 162.6, Thm 163.7 (Yao) | `Yao.lean` (OT-hybrid), `YaoReal.lean` (real protocol) | correctness proved; Thm 163.7 stated, the real form by composition |

## Findings already made (check the repairs, do not re-find them)

1. **OT has five messages:** D8 reads a party's output as its next-message function on its
   complete history.
2. **Prop 161.5 assumes `SamplerCanonical`** (non-canonical raw samples would leak `b`) and an
   **enhanced hard-core predicate** (the gate 03b review: Bob's sampler coins may reveal the
   preimage of `y_{1−b}`). With the gate 03b repair (#198), `SamplerCanonical` is derivable and
   is dropped at integration.
3. **Garbling: `Good`** means correct opening under every assignment's keys.
4. **Efficiency is in Def 155.1** (ruled): `Efficient` strategies and bounded honest messages.
5. **Yao in the OT-hybrid model, then composition** (ruled, Q-5).

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
   `SamplerCanonical` and the **enhanced** hard-core hypothesis (`EnhancedHardCore`) the minimal
   repairs (both found in the statement phase)? Is the enhanced predicate [Gol04, App. C.1]'s?
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
