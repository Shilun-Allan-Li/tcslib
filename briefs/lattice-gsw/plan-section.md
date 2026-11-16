# Proposed plan section: GSW homomorphic encryption (phase 5 of the lattice campaign)

Proposed text for `LatticeCryptographyPlan.md`, prepared for the maintainer. The plan itself
is not edited. Seyoon approved the scope on 2026-11-16, and the 2026-11-16 scope update (the
target sequence to full FHE with a polynomial modulus-to-noise ratio) is folded in.
Everything here is design and statement drafting. No Lean or `lake` was run, so nothing in
`draft/` has been elaborated. Paths are relative to `TCSlib/` unless stated otherwise.

Companion files:
- `draft/`: draft Lean statement files at their proposed paths.
- `draft/shared/DAGCircuit-additions.lean`: the proposed shared-file change.
- `questions.md`: the modelling questions for Seyoon, as multiple choice with the
  recommendation first.

---

## G0. Scope and ownership

This phase runs inside the existing lattice campaign. It reuses the merged LWE layer, the
Regev PKE and the SIS leftover-hash results. The maintainer runs it.
- **PR target:** `cryptography/pass-shelat-ch2-4`. The campaign's central branch
  `cryptography/lwe-sis-constructions` has been idle since 2026-11-09 and is already merged
  into that branch.
- **Lean changes** go by PR, and Seyoon approves and merges them. This brief is records only.

**In scope (phase 5, "leveled GSW"):**
1. The gadget `G = I_{n+1} ⊗ gᵗ` and its deterministic binary decomposition `G⁻¹`.
2. Public-key GSW on the existing Regev/LWE key: `Enc`, `Dec`, and fresh-noise correctness.
3. A key-agnostic noise invariant. Under it the scheme has:
   - homomorphic addition, negation and finite sums;
   - **asymmetric** multiplication `C₁ · G⁻¹(C₂)`;
   - NAND, and right-associative product chains.
4. Homomorphic evaluation of the library's `BoolCircuit.DAGCircuit`, with leveled
   correctness for depth `L` and the explicit noise bound `(N+1)^L · m·B`.
5. IND-CPA security of public-key GSW from DLWE: concrete Regev-style hybrids with column
   leftover hashing.
6. Optionally (Q4), batched secret-key GSW with its direct DLWE bound.

**Out of this phase, recorded in the roadmap (§G9):**
- bootstrapping, circular security, and decryption circuits;
- Barrington's theorem and permutation branching programs;
- homomorphic accumulators;
- the `NUPPT` primitive bridge, and machine efficiency (for example GSW13 Theorem 3's
  runtime).

**Plan exclusions that still apply:**
- short lattice bases;
- lattice Gaussian sampling, including [AP14, Claim 3.1]'s randomized subgaussian `G⁻¹`;
- search/decision and worst-case reductions.

Phase 5 needs none of these. Normal-form (small-secret) LWE stays a forbidden implicit
equivalence (D1). It becomes relevant only on the AP14 route of phase 7 (§G9).

## G1. Sources

| Tag | Reference | Version used | SHA-256 of the uploaded PDF | PDF status |
|---|---|---|---|---|
| GSW13 | C. Gentry, A. Sahai, B. Waters, *Homomorphic Encryption from Learning with Errors: Conceptually-Simpler, Asymptotically-Faster, Attribute-Based*, CRYPTO 2013, LNCS 8042, pp. 75–92; full version IACR ePrint 2013/340 | Version dated 8 June 2013, 25 pages | `8edb94cfd852a88a8684adbf81b73e78bd21466514b7bb7000d7df1e4431bf00` | Uploaded by Seyoon. Not in the repository. |
| BV14 | Z. Brakerski, V. Vaikuntanathan, *Lattice-Based FHE as Secure as PKE*, ITCS 2014, pp. 1–12; IACR ePrint 2013/541 | ePrint PDF created 28 August 2013, 21 pages | `eab2d1667a8e8a07155968141c72d0ff0be15b1185dd0fd34f291fb41fb812ca` | Uploaded. Used in phases 6–7. |
| AP14 | J. Alperin-Sheriff, C. Peikert, *Faster Bootstrapping with Polynomial Error*, CRYPTO 2014, LNCS 8616, pp. 297–314; IACR ePrint 2014/094 | Version dated 13 June 2014, 18 pages | `cecd346d2e879ff865c23fe977e172e1068f20b01c7f555a419d2f3d5ec2c0da` | Uploaded. Its §3 variant is the presentation used in phase 5. |
| Pei16 | C. Peikert, *A Decade of Lattice Cryptography* (already in the plan's source table) | Author version dated 17 February 2016 | already archived (phase-1 provenance record) | Already ingested as `blueprint/src/references/peikert2016-lattice-survey{,.raw}.md`. §5.4.3 (gadget) and §6.1.3 (GSW, Eqs. (6.1.4)–(6.1.7)) are present. |
| Bar89 | D. A. Mix Barrington, *Bounded-width polynomial-size branching programs recognize exactly those languages in NC¹*, J. Comput. Syst. Sci. 38(1):150–164, 1989 (STOC 1986) | — | — | **Needed** if phase 7 takes the BV14 route. |
| BV11 | Z. Brakerski, V. Vaikuntanathan, *Efficient Fully Homomorphic Encryption from (Standard) LWE*, FOCS 2011, pp. 97–106; ePrint 2011/344 | — | — | **Needed for phase 6.** Its Lemma 4.1 gives the decryption-circuit depth ([BV14, Prop. 3.4]), and its modulus/dimension reduction is AP14 §5.1's preprocessing. |
| AB09 | S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, CUP 2009, Def. 6.1 | — | — | Already cited by `DAGCircuit.lean`. |

**Provenance.** The three uploads were read with `pdftotext -layout` from copies placed in a
scratch directory. Their SHA-256 values match the values Seyoon supplied. The PDFs are **not**
committed. Policy §2 asks for reference ingestion (`blueprint/src/references/` plus
`scripts/sources.py add`) "in the change that formalizes it", and that needs Seyoon's go-ahead
(Q14). The version facts above come from each PDF's own header or creation date. GSW13's ePrint
number is taken from BV14's bibliography. The LNCS volume and page ranges were not read from
the PDFs; check them at ingestion.

**Anchors used by the draft:**
- **GSW13:** §1.3.1–1.3.4, §3.1 (Setup, SecretKeyGen, PublicKeyGen, Enc, Dec), §3.2 and
  Lemma 1 (security), §3.3 (Add, Mult, NAND, "Circuits": `(N+1)^L·B`), and §3.4 (NAND
  `(N+1)B`, condition `q/B > 8(N+1)^L`, Theorem 3).
- **AP14:** §3.1 (Eq. (3.1), Claim 3.1), §3.2 (GSW variant), Definitions 3.2–3.3, Claim 3.4,
  Lemma 3.5 (asymmetric error `e₁ᵗX + μ₁e₂ᵗ`), Corollary 3.6 (chains), and §4–5 for the
  roadmap.
- **BV14:** Def. 2.12–2.13, Thm. 2.14 (bootstrapping, weak circular security), §3.1
  (`NCCrypt`), Claims 3.4.1–3.4.2, §3.3 (width-5 PBPs, Eq. (4)–(6), Thm. 3.5 Barrington,
  Lemma 3.6), Thm. 3.7, and §4.

## G2. Design: GSW on the existing LWE and noise layer

**Convention.** Phase 5 uses the gadget form, which follows [AP14, §3.2] and [Pei16, §6.1.3].
It does not use GSW13's original `Flatten`/`BitDecomp` form.
- **Ciphertext:** `C ∈ Z_q^{(n+1)×N}` with `N = (n+1)·ℓ`.
- **Key vector:** `t = (−s, 1)`. `t` is a *left* approximate singular vector:
  `tᵗC = x·tᵗG + eᵗ`.
- **Multiplication:** `C₁ ⊡ C₂ = C₁·G⁻¹(C₂)`.

GSW13 instead uses square `{0,1}` matrices `C ∈ {0,1}^{N×N}` with `C·v ≈ μ·v` and
`v = Powersof2(s)`. GSW13 §3.2 observes that `BitDecomp⁻¹(C) = μG + RA`, and AP14 §3.2 says
the two forms are "purely syntactic[ally]" interchangeable. The gadget form is chosen because
it reuses the LWE layer's matrices directly, with no `Flatten`.

**Mapping onto the existing layer:**

| GSW object | Formal definition | Built on |
|---|---|---|
| LWE parameters, noise, sample | `GSW.Parameters.lwe : LWE.Parameters`, `χ : LWE.Noise`, `LWE.sample` | unchanged |
| Public key `Ā ∈ Z_q^{(n+1)×m}`, columns are samples | `Regev.augmented P.lwe pk = Fin.snoc Aᵗ b` | the existing, audited augmentation (Regev/Experiments) |
| Secret `t = (−s,1)`, `tᵗĀ = eᵗ` | `GSW.secretVector`, `vecMul_secretVector_augmented` | `LWE.noisyValues_apply` |
| Gadget `G = I ⊗ gᵗ`, `g = (1,…,2^{ℓ−1})` | `GSW.gadget = (Lossy.gadget ℓ (n+1))ᵗ mod q` | the existing little-endian `TrapdoorFunctions.Lossy.gadget` |
| `G⁻¹` | `decomposeVec`/`decompose` = `Randomized.blocksEquiv.symm ∘ digits` (Boolean output) | `Lossy.gadget_mulVec`, `digits_eq`, `digits_val` |
| Enc | `C = Ā·R + μG`, `R : Matrix (Fin m) (Fin N) Bool` | new |
| Dec | `Regev.decrypt` applied to the column `C·G⁻¹(⌊q/2⌋·e_{n+1})` | the existing Regev decryptor and `BitEncoding.decode` |
| Noise | `Encrypts P t x β C : ∃ e, ‖e‖∞ ≤ β ∧ tᵗC = x·tᵗG + e` | new; integer `x`, natural `β` |
| Fresh noise `m·B` and product noise `N·β₁` | `LWE.binaryErrorSum_bound` | reused as is |
| LHL per column | `Hashing.SIS.distAdv_hash_uniform_le` | reused; the column hybrid is new (`Hashing/SIS/Columns.lean`) |
| Ext. error `½√(q^{n+1}/2^m)` | `Regev.extractionError`, `Regev.two_extractionError_le` | reused |

**Decryption (deviation, Q6).** GSW13 reads the row with `vᵢ = 2^i ∈ (q/4, q/2]`. AP14 reads
the penultimate column, `2^{ℓ−2} ∈ [q/4, q/2)`. Both use error `< q/8` and a custom rounding.

The draft instead takes `w = (0,…,0,⌊q/2⌋)` and decrypts the column `C·G⁻¹(w)`, which is a
Regev ciphertext of `μ` in augmented form. So the audited `Regev.decrypt`,
`BitEncoding.decode` and `decode_codepoint_add` are reused for **every** `q ≥ 2`. The cost
is that the decryption error is `⟨e, G⁻¹(w)⟩`, bounded by `ℓ·β`. For `q = 2^ℓ`, `G⁻¹(w)` is a
unit vector and the bound is `β` (`decrypt_of_encrypts_dyadic`).

## G3. Reused and new definitions

**Reused unchanged (read only through published readers, Rule 10):**
- **LWE:** `LWE.Parameters`, `Noise` (with `Bounded` and `bounded_iff`),
  `noisyValues`/`noisyValues_apply`, `sample`/`sample_fst`/`sample_snd`, `decisionAdvantage`
  and `decisionAdvantage_eq`, `binaryErrorSum_bound`, and `BitEncoding.codepoint` and
  `decode_codepoint_add`.
- **Regev PKE:** `Regev.keygen` (`keygen_fst`/`keygen_snd`), `Regev.decrypt`/`decrypt_eq`,
  `Regev.augmented`/`augmented_eq`/`augmented_bijective`, and
  `Regev.extractionError`/`extractionError_eq`/`two_extractionError_le`.
- **Lossy gadget:** `TrapdoorFunctions.Lossy.gadget`/`gadget_eq`/`gadget_mulVec`,
  `digits`/`digits_eq`/`digits_val`, and `Randomized.blocksEquiv`.
- **SIS hashing:** `Hashing.SIS.hash`/`hash_eq` and `distAdv_hash_uniform_le`.
- **Probability:** `distAdv`, `acceptProb`, `acceptProb_comp_equiv`, `uprob_comp_equiv`, and
  `abs_sub_le_sum_hybrids`.
- **Circuits:** `BoolCircuit.DAGCircuit`, `DAGGate.eval_eq`, `runWith` and its lemmas,
  `DAGCircuit.values_eq`, `eval_eq`, `depthAt_gate` and `depthAt_input`.
- **Later, not phase 5:** `PublicKeyScheme.distAdv_multi_le_sum`, for multi-ciphertext
  security.

**New definitions (31):**
- `Gadget`: `Parameters`, `columns` (abbrev), `Ciphertext` (abbrev), `gadget`, `digit`,
  `decomposeVec`, `decompose`, `lift`.
- `Noise`: `mul`, `nand`, `chain`, `Encrypts`.
- `Scheme`: `secretVector`, `encrypt`, `halfVector`, `decryptColumn`, `decrypt`.
- `Eval`: `homAnd`, `homNot`, `homOr`, `homGate`, `evalValues`, `eval`.
- `Security`: `view`, `realView`, `uniformKeyView`, `reduction`, `columnHashParameters`.
- `Symmetric` (optional): `rowEquiv`, `symEncrypt`.
- `Hashing/SIS/Columns`: `hashColumns`.

Every definition has its reader beside it:
- an `_eq` or `_apply` lemma, `encrypts_iff`, or the three `homAnd` equations;
- non-simp `simps` projections for the views and for `columnHashParameters`.

**Proposed shared-file change (needs approval, Q2):** additions to
`Complexity/CircuitComplexity/DAGCircuit.lean`.
- `DAGGate.depth_eq` and `DAGGate.getD_lt_depth`.
- `DAGCircuit.depths_eq`, `depthAt_eq` and `depth_eq`. These are readers that predate the
  reader rule and are flagged by lint check 8.
- `runWith_rel`: the relational form of the proved `SecureComputation.runWith_sim`. It is a
  host lemma and so belongs in the circuit layer.

`Garbling.lean` (under audit as #323) is not touched. Harvesting `runWith_sim` onto
`runWith_rel` goes on the dedup queue.

**Disclosed definition duplicate.** `GSW.columnHashParameters` is field-for-field equal to
`Regev.hashParameters`. GSW's matrices are typed over `Fin (n+1)`, and reading
`Regev.hashParameters` at the type level would unfold another file's definition (Rule 10).
The alternative is for Regev to publish type-level readers (Q11).

**Exports (a separate small commit, as before):**
- A new facade `TCSlib/Cryptography/AdvancedEncryption.lean` imports `TCSlib.Cryptography.AdvancedEncryption.Homomorphic` (ruling Q9; shared with the pairing campaign's `IdentityBased`), and `TCSlib.lean` imports it.
- `TCSlib/Cryptography/Hashing/SIS.lean` gains `import TCSlib.Cryptography.Hashing.SIS.Columns`.

No other existing owner API changes.

## G4. Modulus and noise parameterisation

**Concrete statements are regime-agnostic.** Every result is stated for explicit
`n, m, q, ℓ, B, L` with `N = (n+1)ℓ`:
- noise is a natural number;
- multiplicative growth is the natural number `(N+1)^L·(m·B)`;
- the leveled condition is `2·(ℓ·((N+1)^L·(m·B))) < ⌊q/2⌋`, about `4ℓ(N+1)^L·mB < q`.

For dyadic `q`, the factor `ℓ` drops out. Compare GSW13 §3.4's `q/B > 8(N+1)^L`: the fresh
noise `m·B` is folded in there, and their `B` is the fresh-ciphertext bound.

**Both regimes fit the existing layer:**

| Regime | Where it is used | Fits the existing layer? |
|---|---|---|
| Superpolynomial `q = 2^{ℓ(κ)}`, `ℓ(κ) = Θ(L log N)`, `L` polynomial | phase-5 headline (deep leveled circuits) | **Yes.** `LWE.Family.modulus_le_pow : q κ ≤ 2^{residueBits.eval κ}` with `residueBits : PolyExpr` allows `log q` polynomial in `κ`. `GSW.Parameters.width` can be taken as `residueBits.eval κ`, since the field is exactly `modulus_le`. The DLWE assumption is then at a superpolynomial modulus-to-noise ratio, a stronger assumption, as GSW13 §3.2 discusses. |
| Quasi-polynomial `q = κ^{Θ(log κ)}` | phase 6 (bootstrapping with depth `O(log κ)`) | Yes, same reasoning. |
| Polynomial `q = poly(κ)` | phase 7 (polynomial ratio) | Yes. Dyadic polynomial moduli also keep exact sampling (`LWE.sampleFromBits_law` needs `q = 2^width`). |

**Correction to the scope note's depth claim.** The note says polynomial `q` gives
logarithmic depth. In fact `(N+1)^L ≲ q/B` gives `L ≲ log(q/B)/log(N+1)`:
- for `q/B = κ^c` this is **constant** depth (about `c`, since `N ≥ κ`);
- logarithmic depth needs a quasi-polynomial ratio (GSW13 §3.4, last paragraph; Pei16 §6.1.2,
  "`λ^{−O(log λ)}` error rate").

The conclusion stands, and is stronger: polynomial `q` admits only constant-depth NAND
evaluation. That is why phase 7 replaces depth-bounded evaluation by additive-noise
sequential evaluation.

**Additive regime.** `encrypts_chain` is stated generally:
- **Chains:** the noise is `β₀ + k·N·β`. A chain of `k = poly` fresh ciphertexts on the
  **left** therefore needs only `q ≳ 4ℓ(β₀ + kNβ)`, which a polynomial `q` can meet.
- **Branching-program steps:** these are sums of two products. Use `Encrypts.add`, plus
  `Encrypts.mul` with its `|x₁|·β₂` term.

**Is any existing definition too narrow?** Not for phase 5. Points for later phases:
1. `LWE.Family` has no noise-magnitude field. The ratio `q/B` cannot be named inside the
   assumption. Phases 6–7 state `DLWEAssumption F` together with a ratio hypothesis on `F`;
   a proposed `RatioBounded F B p : ∀ κ, (F.noise κ).Bounded (B κ) ∧ q κ ≤ p.eval κ · B κ`
   would be new in phase 7. Nothing existing changes.
2. `BitEncoding.decode` is fixed at codepoint `⌊q/2⌋`. That is fine for phase 5 through the
   `G⁻¹(w)` trick. It is too narrow for AP14's arbitrary rounding `f : Z_q → {0,1}` (§5.1), and
   for a penultimate-column decoder (Q6, option B), both of which need a new decoder.
3. The LWE secret is uniform only. AP14 §3.2 draws `s̄ ← χ`, and modulus switching (AP14 §5.1
   preprocessing, BV14 §4) needs a short secret. Under D1 this is an explicit new assumption
   or a proved transfer (ACPS09), not a reinterpretation.
4. Noise is a worst-case bounded finite-seed law. BV14 Claim 3.4.2 (with `Rand`) and AP14
   Lemma 3.5 and Corollary 3.6 use Gaussian or subgaussian analyses, which cannot be expressed
   in this layer. Worst-case bounds lose polynomial factors (a `k`-chain grows like `kN` rather
   than `√k`) but keep a **polynomial** ratio, which is what phase 7 needs.
5. Exact dyadic sampling requires `q = 2^ℓ`. AP14's inner modulus `q = ∏ rᵢ` is not dyadic,
   but it is reached by modulus switching, not sampled, so no sampler is needed.

## G5. Homomorphic-evaluation interface (Q1, Q7)

**Recommendation:** evaluate the library's `BoolCircuit.DAGCircuit` directly through the
existing `runWith` host. Expose the gate-agnostic algebra separately, as the real interface.

- **Layer 1, the algebra (`Noise.lean`):**
  - `Encrypts` with `add`, `neg`, `sub`, `sum`, `mono`;
  - asymmetric `mul`, `mul_bit`, the symmetric `mul_le`, and `nand`;
  - `encrypts_chain`.

  Any evaluator uses this layer: circuits, product chains, BV14's width-5 permutation
  branching programs (Eq. (5)–(6) are a sum of two products), and AP14's entrywise-encrypted
  permutation matrices (Eq. (4.1) is a sum of products). None of them needs a new GSW
  primitive.
- **Layer 2, circuits (`Eval.lean`):**
  - `homGate` mirrors `DAGGate.eval`: `∧` is a product chain, `¬` is `G − ·`, and `∨` is De
    Morgan;
  - each gate of fan-in at most 2 costs a factor `N+1`;
  - `eval_encrypts` gives `(N+1)^{depth}·β` by `runWith_rel`.

**Alternative (not recommended): a minimal NAND-circuit type.** Its proofs are slightly
shorter. But it is a second circuit model outside the model registry, and phases 6–7 would
need a conversion to `DAGCircuit` anyway, because the decryption circuit, `NC¹` (`NCAC.lean`)
and Barrington are all stated over `DAGCircuit`.

**Product chain in phase 5: yes (Q7).** It costs about 30 lines. It is the exact hook for
BV14 Claim 3.4.2 and Lemma 3.6, AP14 Corollary 3.6 (with `acc = G`) and Pei16 §6.1.3.

**Orientation.** In the AP14 convention used here, the chain is additive when the **fresh**
ciphertext multiplies on the **left**: the noise is `N·β_fresh + |x_fresh|·β_acc`. BV14
writes it mirrored, with the fresh ciphertext on the right of `C̃₁·C₂`. The docstrings say so
explicitly.

## G6. Statements

The draft has 35 phase-5 targets with `sorry` bodies and sketches, plus 2 in the shared
proposal, 37 in all. All other declarations are closed `rfl` or `Iff.rfl` readers. The size column estimates the
**fill** (proof) lines.

| # | Statement (file) | Source | Est. fill |
|---|---|---|---|
| 1 | `digits_decomposeVec` (Gadget) | Pei16 §5.4.3 | 5 |
| 2 | `gadget_mulVec_decomposeVec`: `G·G⁻¹(u)=u` | Pei16 §5.4.3, (5.4.1) | 30 |
| 3 | `gadget_mul_decompose`: `G·G⁻¹(M)=M` | Pei16 §5.4.3; AP14 (3.1) | 10 |
| 4 | `decomposeVec_block_eq_false` | glue | 25 |
| 5 | `errorSum_decomposeVec_le`: `≤ ℓβ` | glue for GSW13 §3.1 Dec | 40 |
| 6–7 | `encrypts_gadget`, `encrypts_zero` (Noise) | AP14 §3.3 | 5+5 |
| 8–12 | `Encrypts.mono`, `.add`, `.neg`, `.sub`, `.sum` | AP14 Lemma 3.5; GSW13 §3.3 Add; BV14 Claim 3.4.1; AP14 (4.1) | 50 |
| 13 | **`Encrypts.mul`**: noise `N·β₁ + |x₁|·β₂` | AP14 Lemma 3.5; Pei16 (6.1.6); BV14 Claim 3.4.2 (mirrored) | 50 |
| 14–15 | `Encrypts.mul_bit`, `Encrypts.mul_le` (`(N+1)·β`) | GSW13 §3.3–3.4 | 20 |
| 16 | `Encrypts.nand`: `N·β₁+β₂` | GSW13 §3.3–3.4 NAND | 20 |
| 17 | **`encrypts_chain`**: `β₀ + k·N·β` | AP14 Cor. 3.6; Pei16 §6.1.3; BV14 Lemma 3.6 proof | 30 |
| 18 | `vecMul_secretVector_augmented`: `tᵗĀ=eᵗ` (Scheme) | Pei16 (6.1.7); GSW13 §3.1 | 30 |
| 19–20 | `encrypts_encrypt` (`m·B`), `encrypts_keygen_encrypt` | GSW13 §3.1 | 30+10 |
| 21 | `decrypt_of_encrypts`: `2(ℓβ) < ⌊q/2⌋` | GSW13 §3.1 Dec; AP14 Claim 3.4; BV14 Lemma 3.2 | 60 |
| 22 | `decrypt_of_encrypts_dyadic`: `2β < q/2` | AP14 Claim 3.4 | 40 |
| 23 | `decrypt_keygen_encrypt` | GSW13 §3.1 | 5 |
| 24 | `homAnd_encrypts` (Eval) | Pei16 §6.1.3; AP14 Cor. 3.6 | 40 |
| 25 | `homGate_encrypts`: `(N+1)β` | GSW13 §3.3 | 60 |
| 26 | **`eval_encrypts`**: `(N+1)^{depth}·β` | GSW13 §3.3 "Circuits" | 60 |
| 27 | **`decrypt_keygen_eval`**: leveled correctness | GSW13 §3.3–3.4 | 15 |
| 28 | `hashColumns_eq_mul` (Hashing/SIS/Columns) | glue | 10 |
| 29 | `distAdv_hashColumns_uniform_le`: `≤ N·ε` | GSW13 Lemma 1 (statistical half); Pei16 §6.1.3 | 120 |
| 30 | `real_uniformKey_advantage` = DLWE adv. (Security) | GSW13 §3.2, Lemma 1 | 25 |
| 31 | `uniformKey_uniform_advantage_le`: `≤ N·ε_LHL` | GSW13 §3.2 | 80 |
| 32 | **`distAdv_encrypt_le`**: two DLWE + `2Nε` | GSW13 §3.2 | 25 |
| 33 | `distAdv_encrypt_le_of_width`: `… + N·2^{−κ}` | GSW13 §3.2 ("`m > 2n log q`") | 10 |
| 34 | `encrypts_symEncrypt` (Symmetric, optional): noise `B` | AP14 §3.2; BV14 §3.1 SecEnc | 30 |
| 35 | `distAdv_symEncrypt_le`: two DLWE, `k·N` rows | AP14 §3.2; Wu24 L21 pattern | 80 |
| S1 | `DAGGate.getD_lt_depth` (shared) | AB09 Def. 6.1 | 15 |
| S2 | `runWith_rel` (shared host) | glue; generalizes `runWith_sim` | 30 |

Row numbers count targets, so a range such as 8–12 is five targets. Rows 1–35 are the 35
phase-5 targets.

**Estimated sizes:**
- **Draft statement surface:** about 1,400 lines in 9 files, plus a 70-line shared proposal.
- **Filled:** about 2,600 lines, with every math file under 600 lines.

## G7. Fill units

| Unit | Content | Targets | Depends on | Est. fill |
|---|---|---|---|---|
| F0 | Shared circuit readers and `runWith_rel` (owner-side PR, Q2) | 2 | — | ~50 |
| F1 | `GSW/Gadget` | 5 | — | ~110 |
| F2 | `GSW/Noise` | 12 | F1 (statements) | ~190 |
| F3 | `GSW/Scheme` | 6 | F1, F2 | ~175 |
| F4 | `GSW/Eval` | 4 | F0, F2, F3 | ~175 |
| F5 | `Hashing/SIS/Columns` | 2 | — | ~130 |
| F6 | `GSW/Security` | 4 | F3, F5 | ~140 |
| F7 | `GSW/Symmetric` (optional, Q4) | 2 | F3 | ~110 |

**Sequence:**
1. One statement gate covers the whole frozen surface: definitions, the 37 statements and
   the shared proposal.
2. Fills then follow the usual proved-modulo rule, so units citing frozen statements may run
   in parallel: F0, F1 and F5 first, then F2, then F3 and F7, then F4 and F6.
3. Each fill keeps every definition and signature fixed, and carries:
   - a per-module native check;
   - an admission and axiom inventory;
   - a seal probe for Rule 10;
   - a style lint.

Seyoon selects the worker and dispatches.

## G8. Risks

1. **Type-level Rule 10.** Matrix index types must never be reached by unfolding another
   file's definition.
   - The draft avoids `LWE.Parameters.withSamples` for the secret-key batch. It uses
     `hN : m = k·N` and the published `rowEquiv` instead.
   - It duplicates `columnHashParameters` (disclosed, Q11).
   - The seal probe must cover `Regev.augmented`, `LWE.sample`, `Lossy.gadget`,
     `Randomized.blocksEquiv` and `BitEncoding.codepoint`.
2. **Unelaborated API uses.** These are marked `UNCHECKED` in the drafts:
   - the `open Encryption.PublicKey` used to reach `Regev.*`;
   - `Fin.snoc (α := fun _ => …)`, and `Fin.init` at a non-dependent family;
   - `Matrix.submatrix`, and products of `Fin`-indexed matrices with `Fin m` inner
     dimension;
   - `ZMod.val_lt` under the `NeZero` instance from `LWE.Basic`;
   - the `homAnd` pattern-matching equations as `rfl`;
   - identifiers use the Greek `μ` (U+03BC); the micro sign `µ` (U+00B5) is not a Lean
     identifier character, so a fill must not reintroduce it.
3. **Decryption factor `ℓ`.** For non-dyadic `q`, the decryption threshold is weaker than
   the sources' `q/8` by a factor of up to `ℓ`. This is disclosed. The dyadic corollary removes
   it, and Q6 option B recovers the sources' bound with a new decoder.
4. **Worst-case versus probabilistic noise.** None of the sources' parameter theorems are
   reproduced verbatim: GSW13 Theorem 3, BV14 Theorem 1.1 and 3.7, AP14 Theorem 5.1. Only
   their worst-case analogues are. The approximation factors (`n^{1.5+ε}`, `Õ(n³)`) are
   worst-case-lattice statements, which the plan excludes, so they are recorded as context and
   not formalized.
5. **Fan-in.** `DAGCircuit` allows unbounded fan-in. The depth theorem assumes
   `∀ g ∈ gates, g.args.length ≤ 2`, which `IsFaninTwo` implies.
   - The library's depth counts `¬` gates. That is harmless, because the bound is monotone.
   - GSW13's "NAND-depth" relates to it by a constant factor for a translated circuit.
6. **Shared-file overlap.** The phase touches three shared files:
   - `DAGCircuit.lean` (readers and `runWith_rel`, Q2);
   - the `Encryption` and `Hashing/SIS` facades.

   It overlaps nothing in `Garbling.lean` (#323).
7. **Cross-topic import.** `AdvancedEncryption/Homomorphic` imports
   `TrapdoorFunctions/Lossy/Gadget.lean`, a light file that imports only `RandomBits` and
   Mathlib. Q10 offers moving the gadget to `Encoding/` later.
8. **Asymptotic bridge.** It is deferred, as for Regev PKE. Until then no `SingleBitSecure`
   or `NUPPT` claim is made (Q8).
9. **Source ingestion and matching** remain open, as in the rest of the campaign (Q14).

## G9. Roadmap to FHE (phases 6–7; not drafted)

Phase 5 is designed not to block these phases:
- its asymmetric `mul` keeps the exact `|x₁|·β₂` term (BV14 needs that term to vanish when
  `x = 0`);
- it has `encrypts_chain` and `Encrypts.sum`;
- its evaluation algebra is gate-agnostic;
- its concrete statements fit polynomial, quasi-polynomial and superpolynomial `q`.

**Assumptions recorded now:**
- **(A1) Weak circular security** [BV14, Thm. 2.14; Pei16 §6.1.2; AP14 §5.3]. CPA security
  holds even given GSW encryptions of the secret-key bits, or of `Gᵗt` for AP14, under the same
  key. It is stated as an explicit `Prop` hypothesis on the scheme, never derived from LWE:
  "It is unknown whether it is provably secure …" (Pei16 §6.1.2). Without it, only leveled FHE
  follows, through a key chain (BV14 Thm. 2.14, first part).
- **(A2) The LWE ratio.** `DLWEAssumption F` for a family with `q(κ) ≤ p(κ)·B(κ)`:
  - `p` is quasi-polynomial in phase 6;
  - `p` is **polynomial** in phase 7.

  This is the formal "gap" in the finite-noise model. The sources' worst-case translations are
  context only:
  - BV14 Thm. 3.7: `α ≤ 1/Θ̃((n log q)^{2c+1/2})`;
  - BV14 Thm. 1.1: `n^{1.5+ε}`, using §4 dimension-modulus reduction;
  - AP14 Thm. 5.1: `Õ(n²λ)`, so `Õ(n³)`.
- **(A3) Normal-form, small-secret LWE.** Needed only on the AP14 route. It is an explicit
  assumption or a proved transfer [ACPS09, Lemma 2], per D1.

**Phase 6: bootstrapping (Gentry), quasi-polynomial ratio.**
- **Statements:**
  - a homomorphic-scheme interface with compactness [BV14, Def. 2.12];
  - the augmented decryption functions `f_{c₁,c₂}(x) = NAND(Dec_x(c₁), Dec_x(c₂))` [BV14,
    Def. 2.13];
  - the bootstrapping theorem [BV14, Thm. 2.14; Gen09]: a scheme that evaluates its augmented
    decryption circuits is leveled FHE, and FHE under (A1);
  - GSW instantiated with depth `O(log(n log q))` decryption [BV14, Prop. 3.4; BV11, Lemma 4.1]
    and a quasi-polynomial ratio.
- **New substrate:**
  - the decryption circuit in `DAGCircuit`, with a depth bound: iterated addition of
    `(n+1)ℓ` residues mod `q` and rounding, which needs the circuit-arithmetic gadget layer
    that policy §1 anticipates;
  - a `WeakCircularSecure` predicate.
- **Size:** about 2,500–3,500 lines, of which the decryption circuit is 1,500–2,500.
- **PDFs:** BV11; Gentry's thesis is optional, since BV14 Thm. 2.14 states the theorem.

**Phase 7: polynomial-ratio bootstrapping. Two routes:**

| | **BV14 (§3, Theorem 3.7 form)** | **AP14 (§4–5)** |
|---|---|---|
| Idea | Barrington: a depth-`d` NAND circuit becomes a width-5 permutation branching program of length `4^d` [Thm. 3.5]; evaluate it with `V_{t,i} = V_{t−1,γ₀} ⊡ C̄ + V_{t−1,γ₁} ⊡ C` [Eq. (5)–(6)]; noise grows by an additive term per step [Lemma 3.6] | Embed `Z_q` in `S_q` (cyclic or Cayley) or, by CRT, in `∏ S_{rᵢ}`; encrypt permutation matrices entrywise (HEPerm); composition [Lemma 4.1, Cor. 4.2], `Eq?`, and Round [Eq. (5.1)–(5.2), Lemma 5.2] compute `f(⟨s,c⟩)` arithmetically |
| Assumptions | (A1) plus (A2) with polynomial `p` and a **uniform secret**: the existing `DLWEAssumption` unchanged | (A1) plus (A2) **plus (A3)**. Modulus switching to a small inner `q` needs a short secret; AP14 §3.2 uses `s̄ ← χ`, citing ACPS09. Its tight bounds use randomized subgaussian `G⁻¹` (Claim 3.1), which counts as Gaussian sampling and is excluded; a deterministic worst-case variant is a disclosed deviation that is still polynomial |
| Factor (source, not formalized) | `(n log q)^{2c+1/2}` with `c > c_dec`; `n^{1.5+ε}` only with §4 | `Õ(n³)` |
| New substrate | (i) a permutation-branching-program model; (ii) **Barrington's theorem** (S₅ commutators, conjugate 5-cycles, `NC¹ ⊆ PBP₅`), a complexity-library unit (Q13); (iii) homomorphic PBP evaluation, which is phase-5 `mul` plus `add` only | (i) the cyclic embedding `Z_r → S_r` and HEPerm, with composition, `Eq?` and Round; (ii) modulus switching and binary decomposition (phase-5 `G⁻¹`) as preprocessing [§5.1, BV11]; (iii) (A3), or the ACPS09 transfer; (iv) optionally CRT `q = ∏ rᵢ` and Lemma 2.2's prime-power product bound. Taking `t = 1` (a single `S_q`) avoids that number theory at a polynomial cost |
| Reuse of phase 5 | `Encrypts.mul` (with `|x|`), `.add`, `encrypts_chain`, `G − C` for `C̄` | `Encrypts.mul`, `.sum`, `encrypts_chain` (with `acc = G`), `G⁻¹` |
| Reuse of the circuit model | **High.** Barrington's input is a `DAGCircuit` of depth `d` (NC¹ in `NCAC.lean`), and the decryption circuit comes from phase 6 | **None.** Decryption is arithmetic, so phase 6's boolean decryption circuit is bypassed |
| Size beyond phase 6 | Barrington and PBP 1,200–1,700 lines; homomorphic PBP 300–400; instantiation about 200; **about 1.7–2.3k** | HEPerm and Bootstrap 800–1,200; error analysis about 200; modulus switching 400–600; (A3) about 50 as an assumption, or 400 for the ACPS09 transfer; **about 1.5–2.4k**, and it does not need phase 6's 1.5–2.5k decryption circuit |
| PDFs | Bar89 | ACPS09, if (A3) is to be proved; BV11 |

**Recommendation (Q12): BV14.**
- It needs no LWE variant beyond the existing uniform-secret `DLWEAssumption` (D1 intact).
- It uses phase 5 exactly as drafted and the library's own circuit model and `NC¹`.
- It turns Barrington into an independently useful complexity theorem.

AP14 is the better choice only if Seyoon wants the smallest total. In that case phase 6 would
drop its concrete boolean decryption circuit and keep only the generic bootstrapping theorem,
and Seyoon would accept (A3) and modulus switching. That total is about 2.2–3.4k lines against
about 4.2–5.8k for BV14 including phase 6.

## G10. Proposed plan rows

Proposed additions to the organization table:

| Directory under `TCSlib/Cryptography/` | Owner-side content |
|---|---|
| `AdvancedEncryption/Homomorphic/GSW/` | Gadget and `G⁻¹`, noise invariant, public-key and secret-key GSW, circuit evaluation, leveled correctness, IND-CPA hybrids |

The phase table gains one row:

| Phase | Frozen surface to prepare | Fill starts only after |
|---|---|---|
| 5 | GSW gadget/`G⁻¹`, `Encrypts` algebra (asymmetric product, chains), PK GSW, `DAGCircuit` evaluation, leveled correctness, concrete IND-CPA; shared `runWith_rel` and depth readers | GSW statement gate and Seyoon's approval of the shared `DAGCircuit.lean` change |

Proposed decision-log row:

| Date | Decision/evidence | Status |
|---|---|---|
| 2026-11-16 | Seyoon approves GSW as a new phase of the lattice campaign, run by the maintainer, with PRs to `cryptography/pass-shelat-ch2-4`. The scope is leveled GSW, depth-`L` correctness with the explicit bound `(N+1)^L·mB`, and IND-CPA from DLWE. The FHE target sequence is recorded: phase 6 bootstrapping under explicit weak circular security, and phase 7 polynomial-ratio bootstrapping (BV14 or AP14). The design brief and draft statements are under `briefs/lattice-gsw/`; nothing has been elaborated. | Design only; statement gate and questions pending |


> **Status note (2026-11-16, Gate 41 G41-04).** The paths above follow ruling Q9 (`AdvancedEncryption/Homomorphic/GSW/`). Phase 5 statements are compiled in [#333](https://github.com/Shilun-Allan-Li/tcslib/pull/333) (on #332). The decision-log rows proposed in §G10 are recorded in `LatticeCryptographyPlan.md` as dated rows; its organization table is updated when #333 merges.
