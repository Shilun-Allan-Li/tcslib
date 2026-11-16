# GSW phase: modelling questions for Seyoon

Each question is multiple choice, with the recommended option first and marked **(rec.)**.
Section numbers refer to `plan-section.md`. Questions Q1–Q11 decide phase 5 before its
statement gate. Questions Q12–Q16 record roadmap choices now, so phase 5 does not block them.

## Phase 5 (leveled GSW)

**Q1. Circuit model for homomorphic evaluation** (§G5)
- **A (rec.)** Evaluate the library's `BoolCircuit.DAGCircuit` (`∧`, `∨`, `¬`, fan-in ≤ 2) with
  the existing `runWith` host:
  - `∧` is a product chain, `¬` is `G − ·`, and `∨` is De Morgan;
  - the depth theorem gives `(N+1)^{depth}·β`;
  - the gate-agnostic algebra (`Encrypts`, asymmetric `mul`, `sum`, `chain`) is exposed
    separately, so branching programs and permutation matrices can reuse it later.
- **B** A minimal NAND-circuit type local to GSW. Its proofs are shorter, but it is a second
  circuit model, and phases 6–7 would need a conversion to `DAGCircuit` (`NCAC.lean`,
  Barrington).
- **C** No circuit theorem in phase 5: only the gate algebra, with circuits deferred to
  phase 6.

**Q2. The shared change to `Complexity/CircuitComplexity/DAGCircuit.lean`**
(`draft/shared/DAGCircuit-additions.lean`)
- **A (rec.)** Approve one small owner-side PR that adds to `DAGCircuit.lean`:
  - the readers `DAGGate.depth_eq`, `DAGGate.getD_lt_depth`, `DAGCircuit.depths_eq`,
    `depthAt_eq` and `depth_eq`;
  - the relational host lemma `runWith_rel`.

  `Garbling.lean` (#323) is untouched. Harvesting `runWith_sim` onto `runWith_rel` goes on the
  dedup queue.
- **B** Put the readers in `DAGCircuit.lean`, as Rule 10 requires, but put `runWith_rel` in a
  new `CircuitComplexity/DAGSimulation.lean`.
- **C** Prove the relational lemma privately in `GSW/Eval.lean`. Not recommended: that makes a
  private host, which policy forbids.

**Q3. Modulus regime** (§G4)
- **A (rec.)** Keep every phase-5 statement concrete and regime-agnostic (explicit
  `n, m, q, ℓ, B, L`). The asymptotic profile is set later:
  - superpolynomial dyadic `q = 2^{ℓ(κ)}` for the leveled headline;
  - quasi-polynomial `q` for phase 6;
  - polynomial `q` for phase 7.

  The existing `LWE.Family` (`residueBits : PolyExpr`) already admits all three, so no
  existing definition changes.
- **B** Fix the superpolynomial regime now in a GSW family structure.
- **C** Polynomial `q` only. Not recommended: for a fixed polynomial ratio this gives
  **constant** depth, not logarithmic (§G4 correction).

**Q4. Symmetric versus public-key GSW**
- **A (rec.)** Public-key GSW as the headline (GSW13 §3.1), plus the small optional unit F7:
  batched secret-key GSW.
  - F7 has noise `B` instead of `m·B`.
  - Its security comes from DLWE with `k·N` rows and needs no leftover hashing.
  - BV14 Lemma 3.6 and AP14 §3 use secret-key encryption for bootstrapping.
- **B** Public-key only. Secret-key GSW would wait until phase 6 needs it.
- **C** Secret-key only. This drops the leftover-hash unit (F5) but loses GSW13's
  public-key result.

**Q5. Shape of the correctness statement**
- **A (rec.)** Worst-case and every-coin, under `χ.Bounded B`, with explicit natural-number
  bounds (`(N+1)^L·m·B`), as the existing perfect-correctness structures and decision D3
  require.
- **B** Probabilistic, "with overwhelming probability" (BV14 Lemmas 3.3 and 3.6, AP14
  Lemma 5.3). This needs Gaussian or subgaussian tail machinery, which is outside the plan.
- **C** Both: the worst-case form now, and a probabilistic refinement as a later unit.

**Q6. Decryption rule** (§G2)
- **A (rec.)** Decrypt the column `C·G⁻¹(⌊q/2⌋·e_{n+1})` with the existing `Regev.decrypt`.
  - It works for every `q ≥ 2` and reuses the audited decoder.
  - Its noise condition is `2·(ℓβ) < ⌊q/2⌋`.
  - A dyadic corollary drops the factor `ℓ`.
- **B** AP14's penultimate column (codepoint `2^{ℓ−2}`). It matches the sources' `q/8`
  exactly, but needs a new decoder for a general codepoint.
- **C** Dyadic `q = 2^ℓ` only, reading the last gadget column.

**Q7. Product-chain lemma in phase 5**
- **A (rec.)** Yes. Include `encrypts_chain` (noise `β₀ + k·N·β`, with the fresh ciphertext
  on the left) and `Encrypts.sum`, about 45 lines in all. These are the exact hooks for BV14
  Claim 3.4.2 and Lemma 3.6 and AP14 Corollary 3.6 and Lemma 4.1.
- **B** Only the asymmetric `Encrypts.mul`. Chains would be proved in phase 7.
- **C** Only the symmetric `(N+1)·max` bound. Not recommended: BV14 and AP14 both need the
  asymmetry.

**Q8. Level of the security statement**
- **A (rec.)** Concrete function-level hybrids now: two DLWE advantages plus `2·N·ε_LHL`, as
  for Regev PKE. The `NUPPT` bridge to `BitPublicKeyScheme.SingleBitSecure` comes as a later
  unit after the Regev PKE bridge lands, reusing its machine pattern.
- **B** Also an asymptotic statement now, conditional on an explicit reduction-efficiency
  hypothesis.
- **C** The full machine bridge inside phase 5.

**Q9. Module names and location**
- **A (rec.)** `TCSlib/Cryptography/Encryption/Homomorphic/GSW/{Gadget,Noise,Scheme,Eval,
  Security,Symmetric}.lean`.
  - The namespace is `TCSlib.Cryptography.Encryption.Homomorphic.GSW`, with facades
    `Encryption/Homomorphic.lean` and `…/GSW.lean`.
  - The column leftover-hash lemma goes in `Hashing/SIS/Columns.lean`.
  - This follows the plan's rule that constructions sit under their primitive.
- **B** `TCSlib/Cryptography/FHE/GSW/…`, with namespace `TCSlib.Cryptography.FHE.GSW`.
- **C** `TCSlib/Cryptography/Encryption/PublicKey/GSW/…`, beside Regev.

**Q10. Home of the gadget**
- **A (rec.)** Reuse the audited `TrapdoorFunctions.Lossy.gadget` and `digits` in place, by
  importing that light file. Moving it to `Encoding/Gadget.lean` can be a later dedup
  window.
- **B** First harvest the gadget into `Encoding/Gadget.lean`. That moves audited code before
  phase 5.
- **C** A new GSW-owned gadget. Not recommended: it would be a third copy.

**Q11. Type-level reuse of `Regev.hashParameters`**
- **A (rec.)** A GSW-local `columnHashParameters`, field-for-field equal and disclosed as a
  definition duplicate. Under Rule 10, GSW's `Fin (n+1)`-typed matrices cannot reach Regev's
  record by unfolding.
- **B** Regev publishes readers or a domain equivalence that let consumers transport
  `Fin (hashParameters P).dimension` to `Fin (n+1)`, and GSW uses those.

## Roadmap (phases 6–7), recorded now

**Q12. Route to polynomial-ratio bootstrapping** (§G9)
- **A (rec.)** BV14 (§3, Theorem 3.7 form).
  - It uses Barrington and width-5 permutation branching programs, evaluated with phase-5
    `mul` and `add`.
  - Its assumptions are weak circular security plus the existing uniform-secret
    `DLWEAssumption` at a polynomial ratio.
  - It reuses `DAGCircuit`, `NC¹` and phase 6's decryption circuit.
  - It needs about 1.7–2.3k lines beyond phase 6.
- **B** AP14 (§4–5).
  - It uses homomorphic accumulators: permutation matrices for `Z_q ⊂ S_q`, `Eq?` and Round.
  - It needs about 1.5–2.4k lines, and it skips phase 6's boolean decryption circuit
    (1.5–2.5k), so its total is smaller.
  - But it needs normal-form (small-secret) LWE, or the ACPS09 transfer, plus modulus
    switching.
  - Its tight bounds use randomized `G⁻¹`, which is excluded, so the formal version would be a
    worst-case variant.
- **C** Decide after phase 6, once the decryption-circuit cost is known.

**Q13. Barrington's theorem as its own complexity unit**
- **A (rec.)** Yes. A permutation-branching-program model registered in
  `TCSlib/ComputationalModels.lean`, in `Complexity/BranchingPrograms/{Basic,Barrington}.lean`.
  - Its theorem: `NC¹` (fan-in-2 `DAGCircuit` of depth `d`) is contained in width-5 programs of
    length `4^d` [Bar89; BV14, Thm. 3.5].
  - It is statement-gated on its own and sourced to Bar89, which needs a PDF.
- **B** Prove it inside the FHE files. This conflicts with the model-registry and
  "hosts come first" rules.
- **C** Take it as an explicit hypothesis of the phase-7 theorem (conditional endpoint).

**Q14. Source ingestion**
- **A (rec.)** Ingest GSW13 into `blueprint/src/references/` in the phase-5 statement PR.
  Pei16 is already ingested. Ingest BV14 and AP14 with their phases. Committing the PDFs needs
  your go-ahead, because this brief commits none.
- **B** Ingest all three now, in a records-only change.
- **C** Defer all ingestion, as with the earlier source-policy deferral.

**Q15. Form of the circular-security assumption (phase 6)**
- **A (rec.)** Weak circular security [BV14, Thm. 2.14]: CPA security given encryptions of the
  secret-key bits under the same key. It is an explicit `Prop` on the scheme, never derived
  from LWE.
- **B** General key-dependent-message (KDM) security for a function class.
- **C** No circular assumption. Leveled FHE only, by a key chain of `L+1` keys.

**Q16. The LWE "gap" for phases 6–7**
- **A (rec.)** Record it in the finite-noise model as `DLWEAssumption F` together with a new
  ratio predicate on `F`: `q(κ) ≤ p(κ)·B(κ)`, where `p` is quasi-polynomial in phase 6 and
  polynomial in phase 7. The sources' worst-case approximation factors stay as context:
  - BV14 Thm. 3.7 and 1.1;
  - AP14 Thm. 5.1 (`Õ(n³)`).
- **B** Also formalize the worst-case meaning. This needs Gaussian noise and worst-case
  reductions, both excluded by the plan.
