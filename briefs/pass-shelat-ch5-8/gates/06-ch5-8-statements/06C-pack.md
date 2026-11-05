# Gate 06C (Pass–shelat ch. 7, composability): external statement audit pack

**Status: draft** (2026-11-05). It pins to the integration commit of gate 06 (`PLAN.md`: after
#195 lands, prongs A–D merged onto it, one fresh replay). The content below is prong C's head
`aa71d0e784a84c68172895fd5db79a253fba79c9`, complete in the statement phase. The attestations are
filled at staging.

**What is audited:** the trusted surface of [PS10] ch. 7 as formalized in
`TCSlib/Cryptography/Composability/`: definitions, statements, docstrings and proof sketches,
against the sources. Proofs are out of scope, except the short ones that carry a definition's
correctness (for example `correct` fields and the phase lemma of `seqRep`). The deliverable is
**`gate06C-findings.md`**.

**Sources attached separately:**
- [PS10] R. Pass, a. shelat, *A Course in Cryptography*, 3rd ed., January 2010. Book page = PDF
  page − 12. §7.1–7.2, book pp. 167–176.
- [PSV06] Pass, shelat, Vaikuntanathan, CRYPTO 2006, LNCS 4117, pp. 271–289 (Definition 3).
- [PSV07] Pass, shelat, Vaikuntanathan, ASIACRYPT 2007, LNCS 4833, pp. 519–535 (Definitions 1–4,
  Theorems 3 and 4, Corollary 1).

## Scope

| Item | Where | State |
|---|---|---|
| Def 168.1 (CPA, CCA1, CCA2 for private-key schemes) | `Composability/Defs.lean` | defined |
| Thm 168.2 (Algorithm 99.1 is CPA- and CCA1-secure) | `PRFScheme.lean` | stated |
| Claim 169.a (Algorithm 99.1 is not CCA2-secure) | `PRFScheme.lean` | proved from an advantage-1 adversary |
| Alg 169.3 (`π′`: encrypt, then tag) and Thm 170.4 (`π′` is CCA2-secure) | `CCA2Scheme.lean` | correctness proved; Thm 170.4 stated |
| Def 171.5 (public-key CPA/CCA) and Claim 172.a (Construction 104.3 is CPA-secure) | `PublicKey.lean` | Claim 172.a proved from a stated lemma and Thm 104.4 |
| Def 172.6 (non-malleability) and Thm 175.9 (CCA2: secrecy ⇔ non-malleability) | `NonMalleable.lean` | Thm 175.9 stated |
| Def 173.7 (relation-based non-malleability) and Thm 174.8 | `SimNonMalleable.lean` | in [PSV07]'s form; both directions stated |
| Thm 175.1 (sequential composition of ZK) | `SequentialZK.lean` | stated; `seqRep`'s phase lemma proved |

## Findings already made (check the repairs, do not re-find them)

1. **The `Dec` guard** ([Shilun-Allan-Li/tcslib#193](https://github.com/Shilun-Allan-Li/tcslib/pull/193), ch. 2–4): Algorithm 99.1's `Dec`
   refuses malformed ciphertexts. Without the guard, Thm 168.2's CCA1 half is false.
2. **`π′`'s tag covers `(r, c₁)`** (inventory erratum, Alg-169.3): tagging `c₁` alone is not
   CCA2-secure.
3. **Public-key games pad ciphertexts** (ruling): canonical padding, with non-canonical strings
   refused. Otherwise a CCA2 adversary queries a re-padding of the challenge.
4. **Non-malleability follows [PSV06] and [PSV07]** (ruling). Thm 174.8 is false as written:
   Def 173.7's simulator gets no public key, and the quantifiers of Defs 172.6 and 173.7 do not
   line up. [PSV07] shows the equivalence holds under CPA only.
5. **Thm 175.1 assumes `ProverBounded`** (ruling on Q-1): under D8, a verifier may double its
   message length each phase, so the views of a sequential repetition can grow exponentially.

## Brief for the auditor

You are auditing the **trusted surface**. Hunt for:
1. **Infidelity:** a definition or statement that differs from the source's other than by a
   declared deviation; check that each declared deviation is benign or that its cost is stated.
2. **Wrong semantics:** a definition that does not compute what its docstring says.
3. **Trivialization:** vacuous hypotheses; games an adversary wins or loses for degenerate
   reasons (message length 0, an empty ciphertext space, a budget of 0).
4. **Wrong strength:** a theorem weaker or stronger than its docstring claims.
5. **Attribution:** `policy.md` §2.

For **every definition**, restate it in your own words before reading its docstring. For
**every theorem**, say in 1–3 sentences whether the statement is what its docstring claims. Attempt
at least **three adversarial instantiations**. Do not give a blanket approval.

## Specific questions

1. **The oracle games.** In `indImpl` (private and public key), is `Dec`'s availability per attack
   (`decOpen`) Def 168.1's `[Enc, Dec; Enc, Dec*]` table? Is the challenge asked at most once in
   effect (`indImpl_challenge_repeat`)? Does fixing message lengths (`FixedLengthScheme`) lose
   anything?
2. **Padding (Def 171.5).** Is `FixedLengthPKScheme` with `padCt`/`isPadded` a faithful reading
   of a public-key scheme with variable-length ciphertexts? Can an adversary exploit the
   refusal of non-canonical strings?
3. **Def 172.6.** At CPA, is `nmGame` [PSV06, Definition 3]? Under CCA, are the oracles those of
   Def 171.5? Is it right that a copy of the challenge and an invalid ciphertext are both `⊥`?
4. **Def 173.7 as SIM-NME′.** Compare `snmReal`/`snmIdeal` with [PSV07, Definition 1] at one
   message. In particular:
   - the sampler: here a sampler `M` is quantified with the adversary, and `A₁` outputs its
     parameter (with a universal clocked sampler, [PSV07]'s form). Is this equivalent?
   - the `COPY` encoding, the simulator's single query, and its lack of a `Dec` oracle;
   - the convention when no challenge is asked.
5. **Thm 174.8.** Is "under CPA, plus SIM ⇒ IND for every attack" the strongest true reading,
   given [PSV07, Theorems 3 and 4, Corollary 1]? [PSV07] defers both proofs; **check the
   maintainer's two sketches** (`nmSecure_of_simNMSecure`, `simNMSecure_of_nmSecure_cpa`) as
   arguments.
6. **Thm 175.1.** Is `seqRep` the source's `Q(n)`-phase repetition, with fresh coins per phase?
   Is `ProverBounded` the minimal repair, and is it satisfied by the source's protocols?

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
