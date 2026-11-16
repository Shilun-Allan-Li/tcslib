# Proposed plan section: GSW phase 6, bootstrapping to FHE with a polynomial modulus-to-noise ratio (BV14 route)

**Revision r2 (2026-11-16): statement prep.** r1 was drafted overnight, before Seyoon's rulings
(`briefs/pass-shelat-ch5-8/overnight-2026-11-16.md`, item 7). r2 applies all of them: P6-Q1 to P6-Q13 and the
location ruling in [rulings.md](rulings.md), which are binding. This is proposed text for
`LatticeCryptographyPlan.md`; the plan itself is not edited. No Lean was written or elaborated, so every statement
below is a sketch for the statement phase. Paths are relative to `TCSlib/` unless stated otherwise. Line references
are to the records head `99eae2c1550ee0b0485f115bca76b254dae25064`.

Companion files:
- `rulings.md`: the rulings applied here. `questions.md`: the ruled questions P6-Q1 to P6-Q13 (not edited by r2).
- §H9 below: the new questions raised by the changed rulings, P6-Q14 to P6-Q19, multiple choice, recommended first.
- Sources: the DW-7 ingests under `blueprint/src/references/` (§H1). Citations use `[TAG, location, anchor]`, where
  the anchor is the ingest's block id without its per-source prefix (§H1 lists the prefixes). For example,
  `[BV14, Thm 3.5, p014-b001]` is `brakerski-vaikuntanathan-2014-fhe.md#pdf-eab2d1667a8e-p014-b001`.

**What r2 changes** (the ruling in brackets):
1. One phase 6 with statement gates **45** (6a) and **46** (6b); the quasi-polynomial route is dropped [P6-Q1].
2. Barrington in both directions, BWBP = NC¹, including Thm 2 with its composition-tree circuit [P6-Q3].
3. The general branching-program model of Bar89 §1 (maps `[w] → [w]`) with an `IsPermutation` predicate [P6-Q4].
4. Bootstrapping is NAND only, literally BV14 Def 2.13, through a new `DAGCircuit`-to-NAND conversion [P6-Q9].
5. Concrete **and** asymptotic `WeakCircularSecure` and IND-CPA, with an explicit reduction-efficiency
   hypothesis [P6-Q10].
6. The full leveled scheme: `L+1` keys, correctness, and IND-CPA by a key hybrid from DLWE [P6-Q11].
7. Branching programs, Barrington and the NAND conversion live in `Complexity/` [location ruling]; the formula
   layer in `Complexity/CircuitComplexity/FormulaArith/` [P6-Q6]; `decode_iff_mem_Ico` in `LWE/BitEncoding.lean` by
   an owner-side PR [P6-Q7].
8. Two path adjustments, with reasons in §H4: a fifth branching-program file `NC1.lean`, and a facade for
   `FormulaArith/`.

Unchanged from r1, as ruled: P6-Q2 (`TreeCircuit` input), Q5 (formula-arithmetic layer), Q7, Q8 (evaluation key),
Q12 (ratio statements) and Q13 (computable `barrington`).

---

## H0. Scope, numbering and ownership

**Goal.** Pure (non-leveled) and leveled fully homomorphic encryption from LWE with a **polynomial**
modulus-to-noise ratio, following [BV14, §3] and cross-checked against [AP14, §4–5].

*Complexity layer (6a, Gate 45):*
1. **Barrington, both directions.**
   - Thm 1 with Lemmas 1–3: a fan-in-2 AND/OR formula of depth `d` (negations at the inputs) is five-cycle
     recognized by a width-5 permutation branching program (PBP) of length at most `4^d`
     [Bar89, Thm 1, p003-b002; BV14, Thm 3.5, p014-b001].
   - Thm 2: a width-`w` branching program of length `l` is recognized by a fan-in-2 circuit of depth `O(log l)`,
     the constant depending on `w` [Bar89, Thm 2, p004-b003].
   - Hence BWBP = nonuniform NC¹ = languages of polynomial-length 5-PBPs [Bar89, Corollary, p004-b004].
2. **NAND conversion.** Every `DAGCircuit` with fan-in at most two becomes a NAND-form circuit computing the same
   function, with depth at most twice the original and size linear in the number of gates.
3. **Formula arithmetic.** A shared layer over `TreeCircuit` for the decryption formula: De Morgan negation,
   substitution, `xor3`/`maj3`, carry-save reduction, carry-out comparison, modular interval sum.

*Cryptography layer (6b, Gate 46):*

4. **Homomorphic PBP evaluation.** One selector step per instruction costs an **additive** `2Nβ`
   [BV14, Eq. (4)–(6), Lemma 3.6, p014-b002, p015-b001; AP14, Eq. (4.1), Lemma 4.1, p011-b001, p012-b001].
5. **Decryption formula** of depth `O(log N + log log q)` for public-key GSW
   [BV14, Prop 3.4, p011-b001; BV11, Lemma 4.5, p029-b001].
6. **NAND-only bootstrapping.** Every gate of a NAND-form circuit is evaluated by homomorphically evaluating BV14's
   augmented decryption function `f_{c₁,c₂}` on the evaluation key of P6-Q8
   [BV14, Def 2.13, Thm 2.14, p008-b002, p008-b003; BV11, Defs 3.7–3.8, Thms 3.1–3.2, p014-b002, p015-b001]. The
   output noise is a fixed bound independent of the circuit, so correctness holds for circuits of **every depth**.
7. **Leveled FHE.** `L+1` keys, correctness for NAND circuits of depth at most `L`, and IND-CPA by a hybrid over the
   keys from DLWE [BV14, Thm 2.14 first part, Thm 3.7, p016-b001; BV11, Thm 3.1, Def 3.6, p015-b001,
   p014-b001]. It is the FHE statement that needs no circular-security assumption.
8. **Security.** For pure FHE, concrete and asymptotic statements under an explicit weak-circular-security
   hypothesis [BV11, Def 3.8; BV14, Thm 2.14; Pei16, §6.1.2, p068-b001]. Asymptotic IND-CPA of the `evk`-free view
   and of the leveled scheme from `LWE.DLWEAssumption`, under an explicit reduction-efficiency hypothesis.
9. **Polynomial ratio.** The ruled `RatioBounded F B p` (phase-5 Q16) and a family theorem with an explicit
   `PolyExpr` `pBoot` (P6-Q12).

**Numbering** [P6-Q1]. One phase 6 merges the roadmap's phases 6 and 7. It has two statement gates:
**Gate 45** for 6a (branching programs, Barrington in both directions, the NAND conversion, formula arithmetic) and
**Gate 46** for 6b. Gates 42–44 are taken; 45 and 46 replace r1's provisional 42 and 43. The quasi-polynomial
instantiation is dropped.

**Assumptions.**
- (A1) Weak circular security of public-key GSW for its own key bits. It is an explicit hypothesis (phase-5 Q15),
  concrete and asymptotic (P6-Q10), never derived from LWE, and used only by the pure-FHE security statements.
- (A2) DLWE for a family whose ratio `q/B` is polynomially bounded: the existing `LWE.DLWEAssumption`, unchanged
  (phase-5 Q16).
- (A3) Small-secret LWE is **not** needed; the BV14 route uses the uniform-secret `DLWEAssumption` (rulings
  addendum: A3 is assumed only where used; here it is unused).
- (A4) **Reduction efficiency** (new, P6-Q10): an explicit `Prop` per LWE family stating that the encryption
  reductions are realized by non-uniform PPT machines (§H5.16). It is not an LWE variant. It replaces a
  machine-level GSW encryptor, which stays out of scope. Only the asymptotic IND-CPA theorems use it.

**In scope:** items 1–9; the `DAGCircuit` corollary of Thm 1 (length `≤ 4^depth`); the language classes `BWBP`
and `PBP₅` with `BWBP = NC¹ = PBP₅`; compactness by typing (docstrings, no theorem).

**Out of scope:**
- Gaussian or subgaussian noise, the randomization procedure `Rand` [BV14, §2.4], and randomized `G⁻¹`
  [AP14, Claim 3.1].
- Worst-case lattice reductions and approximation factors. [BV14, Thm 1.1, Cor 4.5] and [AP14, Thm 5.1] are context
  only.
- Dimension-modulus reduction [BV14, §4; BV11].
- Machine efficiency of `Eval` and of GSW encryption. There is no `BitPublicKeyScheme` instance, so the
  reduction-efficiency hypothesis (A4) stays a hypothesis.
- The AP14 accumulator route (phase-5 Q12) and the quasi-polynomial instantiation (P6-Q1).
- From Bar89: uniformity (Bar89 §6), width-4 circuits and the word problem (abstract only), and the traditional
  rectangular branching-program model (Bar89 §1, p002-b001).

**Ownership.** The maintainer runs the phase on `cryptography/pass-shelat-ch2-4`. Lean changes go by PR; Seyoon
approves and merges. Codex audits (standing ruling). The 6a statements go to an external Claude session that Seyoon
dispatches (ruling of 2026-11-16, `PassShelatChapter5-8Plan.md`); the maintainer stages the issue package from this
revision, then reviews and lands the delivery.

## H1. Sources (DW-7 ingests)

Each ingest is a scoped raw file (`.raw.md`) plus a LaTeX transcription (`.md`) with proofmatch anchors; the tags
are registered in `blueprint/src/references/sources.json`. PDFs are not committed (DW-7). Matching against the
blueprint waits for an approved proofmatch run.

| Tag | Ingest key | Anchor prefix | SHA-256 of the upload |
|---|---|---|---|
| Bar89 | `barrington-1989-bounded-width-bp` | `pdf-06fd3eeccecf-` | `06fd3eec…7831` |
| BV14 | `brakerski-vaikuntanathan-2014-fhe` | `pdf-eab2d1667a8e-` | `eab2d166…12ca` |
| BV11 | `brakerski-vaikuntanathan-2011-fhe` | `pdf-d3e95f9b9e01-` | `d3e95f9b…0b00` |
| AP14 | `alperin-sheriff-peikert-2014-bootstrapping` | `pdf-cecd346d2e87-` | `cecd346d…c0da` |
| GSW13 | `gentry-sahai-waters-2013-fhe` | `pdf-8edb94cfd852-` | `8edb94cf…bf00` |
| Pei16 | `peikert2016-lattice-survey` (extended) | `pdf-1a9802b66031-` | `1a9802b6…7488` |

Passages ingested (unchanged from r1):
- **Bar89** (JCSS 38(1):150–164, 15-page scan, read from page images): abstract, §1, and §3 (five-cycle
  recognition, Thm 1, Lemmas 1–3, example, proof of Thm 1, Thm 2 with its proof, Corollary).
- **BV14** (ePrint 2013/541, 21 pp.): fn. 1, Thm 1.1, §2.3, §2.5 (Defs 2.12–2.13, Thm 2.14), all of §3, Lemma 4.4,
  Cor 4.5.
- **BV11** (FOCS 2011 full version, 39 pp.): §3.1 (Defs 3.1–3.6), §3.2 (Def 3.7, Thms 3.1–3.2, Def 3.8, Lemma 3.3),
  §4.5 (Lemma 4.5 with proof, Lemma 4.6, Cor 4.7).
- **AP14** (ePrint 2014/094): §2.2, §3, §4.1–4.2, §5.1–5.3. **GSW13** (ePrint 2013/340): §1.2, §1.3.1–1.3.4, §2.3,
  §3.1–3.4. **Pei16**: extended with §5.4.3, §6.1.2 and §6.1.3.

**Does the Barrington ingest cover Thm 2? Yes.** Block `p004-b003` (printed p. 153) transcribes the statement and
the whole proof. The proof is the paper's single paragraph: represent a map `[w] → [w]` by `w²` Boolean variables
"`f(i) = j`", a constant-depth section per instruction, a binary tree of composition circuits, and a
constant-depth acceptance section at the top. The Corollary (`p004-b004`), the recognition notion (`p001-b002`,
`p002-b001`) and the abstract (`p001-b001`) are also present. Nothing on Thm 2 is missing. Two adjacent items are
not ingested and are not needed for any citation below:
- the bibliography entries [22] and [30], which Thm 2's preamble names for the uniform case (the reference list at
  the end of the paper is not transcribed);
- §2 and §4–§6.

No page needs to be added for Thm 2.

**Gaps found in the sources (no citation is invented for them):**
1. **The leveled key chain.** [BV11, Thm 3.1, p015-b001] and [BV14, Thm 2.14 first part, p008-b003] state the
   leveled theorem. [BV11, Thm 3.1] adds that "only the length of the evaluation key depends on the level L".
   [AP14, §5.3, p015-b002] gives the independent-keys security argument. No ingested passage gives the key-chain
   construction or its hybrid; Gentry's [Gen09] is cited by both papers but not ingested (P6-Q19).
2. **NAND conversion.** No ingested passage states that `{NAND}` is a complete basis or gives a conversion. The
   conversion is glue, motivated by [BV14, Def 2.13, Thm 3.5] ("Every Boolean NAND circuit"). AB09's ingest covers
   chapters 7 and 13 only, and nothing there concerns NAND.
3. **AB09 §6** (Defs 6.1, 6.24) is cited by existing docstrings (`DAGCircuit.lean`, `NCAC.lean`) and is not
   ingested. This plan adds no new AB09 citation.

**Record points from r1 (unchanged; nothing here edits them):**
1. BV14's "[BV11, Lemma 4.1]" (Prop 3.4) is **Lemma 4.5** in the BV11 version held. Docstrings cite
   [BV11, Lemma 4.5] and note BV14's numbering.
2. (Pairings) BB04's §3.1 Decision-BDH advantage has an absolute value on the page images;
   `PairingCryptographyPlan.md`, "Where the papers' formulations differ", item 6, says otherwise.

**Anchors used below:**
- **Bar89.** Abstract `p001-b001`; §1 instructions, yield and recognition `p001-b002`; PBP and BWBP `p002-b001`;
  five-cycle recognition `p003-b001`; Thm 1 `p003-b002`; Lemmas 1–3 `p003-b003`, `p003-b004`, `p003-b005`;
  example `p004-b001`; proof of Thm 1 `p004-b002`; Thm 2 with proof `p004-b003`; Corollary `p004-b004`.
- **BV14.**
  - Fn. 1 (leveled vs pure) `p001-b001`; §2.5 ("adversary is given both pk and evk") `p007-b001`;
    Def 2.12 `p008-b001`; Def 2.13 `p008-b002`; Thm 2.14 `p008-b003`.
  - Security of NCCrypt and Prop 3.4 `p011-b001`; PBPs and Eq. (4) `p013-b002`; Thm 3.5 `p014-b001`;
    Eval and Eq. (5)–(6) `p014-b002`.
  - Lemma 3.6 `p015-b001`, its proof `p015-b002`; Thm 3.7 `p016-b001`; Lemma 4.4 `p019-b001`.
- **BV11.** Def 3.1 (CPA with `evk`) `p013-b002`; Def 3.2 (`(t, ε)`-CPA) `p013-b003`; Defs 3.4–3.6 `p014-b001`;
  Def 3.7 `p014-b002`; Thms 3.1–3.2, Def 3.8, Lemma 3.3 `p015-b001`; Lemma 4.5 `p029-b001`, its proof `p029-b002`.
- **AP14.** Lemma 3.5 `p010-b001`; Cor 3.6 `p010-b003`; Eq. (4.1) `p011-b001`; Lemma 4.1 `p012-b001`;
  §5.1 `p013-b001`, `p014-b001`; §5.3 `p015-b002`.
- **GSW13.** §3.2 security `p009-b002`; Lemma 1 `p010-b001`; §3.4 bootstrapping `p012-b002`.
- **Pei16.** §5.4.3 `p052-b001`, `p053-b001`; §6.1.2 `p068-b001`; Eq. (6.1.6) `p069-b001`; §6.1.3 bootstrapping
  `p070-b001`.

## H2. What the existing Lean already provides (reuse findings)

All references are `file:line` at the records head. "Reuse" means cite or consume. "Near-relative" means checked
and not reused, with the reason.

**Phase 5 (`Cryptography/AdvancedEncryption/Homomorphic/GSW/`).** The statements are merged (#332, #333). The fills
#339 (`gsw-core`) and #338 (`gsw-security`) passed Gate 43 (closed CLEAR); their merge waits for the combined build
(GS-01 is ruled). 6b cites the frozen phase-5 statements under the proved-modulo rule and merges after those fills.
- **Noise algebra** (`Noise.lean`): `Encrypts` :97; `Encrypts.mul` :181, whose noise `N·β₁ + |x₁|·β₂` makes a
  selector step additive; `.add` :139, `.sub` :154, `.sum` :164, `encrypts_gadget` :118, `encrypts_zero` :124;
  `nand`/`Encrypts.nand` :73/:210 is the leveled multiplicative NAND, not used by bootstrapping.
- **Scheme** (`Scheme.lean`): `secretVector` :66, `encrypt` :90, `decrypt` :129, `encrypts_encrypt` :147,
  `encrypts_keygen_encrypt` :160, `decrypt_of_encrypts` :181. **Gadget** (`Gadget.lean`): `Parameters` :59,
  `Ciphertext` :78, `gadget` :90, `decomposeVec` :112, `gadget_mulVec_decomposeVec` :163.
- **Circuit evaluation** (`Eval.lean`): `homGate` :96, `eval` :122, `eval_encrypts` :180, on the `runWith` host;
  `fheEval` mirrors it.
- **Security** (`Security.lean`): `view` :58, `realView` :76, `reduction` :112, `distAdv_encrypt_le` :189,
  `distAdv_encrypt_le_of_width` :205. These are the base of G15, of the leveled hybrid and of the asymptotic forms.

**Complexity layer: model, conversions, classes.** No branching-program, Barrington, permutation-program or NAND
material exists. Searches for `branching`, `Barrington`, five-cycle and NAND found only the items below.
- **Formula model** (`CircuitComplexity/Basic.lean`): `Lit` :103, `TreeCircuit` :122, `TreeCircuit.ind` :130,
  `eval` :144, `eval_node_true_iff`/`_false_iff` :155/:163, `depth` :176, `maxFanin` :194,
  `depth_node`/`maxFanin_node` :213/:223, and `size_succ_le_two_pow` :313, which gives polynomial formula size from
  logarithmic depth (used by Thm 2).
- **Name clash, not reusable:** `NAndCircuit` (`Basic.lean:356`) and `TreeCircuit.toNAnd` (:465) are the
  **AND-rooted alternating normal form** of the LMN development, not NAND gates. The new names avoid `NAnd`
  (`IsNANDForm`, `toNANDForm`, `DAGGate.IsNAND`), and the docstrings cross-reference the old ones.
- **DAG model** (`DAGCircuit.lean`): `DAGGate.eval` :123 and `eval_eq` :131. A `¬` gate evaluates to the
  **negated conjunction** of its arguments, so a `¬` gate with two arguments is natively a NAND gate (P6-Q16).
  Also `runWith` :149, `DAGCircuit` :459, `IsWellFormed` :508 (requires `¬` gates of fan-in exactly 1),
  `IsFaninTwo` :512, `runWith_rel` :625, `constGate` :280, `DAGCircuitFamily` :681.
- **Gate-rewriting host** (`DAGTransform.lean`), reused by the NAND conversion: `GadgetSpec` :55,
  `GadgetCorrect` :68, `rewriteGates` :82, `DAGCircuit.rewrite` :246, `rewrite_eval` :263, `rewrite_depth_le` :269,
  `rewrite_new_gates` :273, `rewrite_length_le` :278, `sum_cost_le` :286. Its two instances are the models for the
  NAND gadget (`DAGFanin.lean`): `deMorganGadget` :475 with `deMorganGadget_correct` :499 and `deMorgan_*`
  :603–636; `emitNots` :384; `GateKind.op` :49; `DAGGate.eval_pair` :65; `binarize` :347.
- **Tree ↔ DAG** (`TreeDAG.lean`):
  - `TreeCircuit.toDAG` :349 with `toDAG_eval` :357, `toDAG_size_le` :363, `toDAG_depth_le` :368 and
    `toDAG_isFaninTwo` :378 (the route from Thm 2's formula to NC¹);
  - `DAGCircuit.toTree` :404 with `toTree_eval` :594, `toTree_depth_le` :623 and `toTree_maxFanin_le` :645
    (Barrington's `DAGCircuit` corollary).
  - Near-relative: `unfoldGate` :388 pushes negations by De Morgan, but on DAG input, so it is not a
    tree-to-tree `neg`.
- **Classes** (`NCAC.lean`, `TreeNCAC.lean`): `Language.InNC` NCAC:55, `Language.InTreeNC.inNC` :149,
  `Language.InNC.inTreeNC_one` :194, `Language.inNC_one_iff` :229; `TreeCircuitFamily` TreeNCAC:90,
  `HasPolylogDepth` :121, `Language.InTreeNC` :130. Both Barrington directions go through `inNC_one_iff`.
- **Balanced fan-in-2 gate:** `combine` (**private**, TreeNCAC:252; `pairUp` :175, `combineFuel` :245;
  `combine_eval`/`_maxFanin`/`_depth`/`_size` :332–351, depth `maxDepth + ⌈log₂ k⌉ + 1`). It is promoted by
  owner-side PR O1 (P6-Q6). `TreeCircuit.toBinary` (:353) is public but rebuilds every child, and its depth bound
  `toBinary_depth_le` (:442) is multiplicative, so it cannot replace `combine`.
- **Dual-rail XOR:** `xorNode`/`IsDual` (**private**, `Parity.lean:60/65`). They are re-pointed to the public
  `neg`/`xor2` later, on the dedup queue (P6-Q6).
- **Number semantics** (`Adder.lean`): `bitsVal` :78, `prefixVal` :82, `prefixVal_lt` :101,
  `bitsVal_eq_prefixVal` :136, `carryBit` :377, `sumBit` :382, `prefixVal_add` :397 (ripple-carry correctness).
  F5–F8 state their semantics through these, and F7's carry-out is exactly `carryBit` at position `b`.
  `fullAdderGates`/`adderGates` are linear-depth DAG adders and are not used.
- **Near-relatives checked and not reused:**
  - `Complexity.BinArith.carry`/`sumBit` (`ClassP/BinaryArith/AddSub.lean:49/52`, with `serial_add` :62) are the
    Boolean full-adder functions. They are not imported: that would pull polynomial-time machinery into the formula
    layer. `maj3`/`xor3` state the same functions with Bool operations.
  - `FormulaKit/Gate.lean` (`template` :90, `gate` :142; P6-Q6 asked for this check) builds truth-table CNF
    templates over `Std.Sat.CNF ℕ`. It is a different model, and generic truth-table gadgets over `log q`-bit values
    are excluded by §H3.3.
  - Also: `dnfDAG` (`BookModelBasics.lean:406`, same exclusion); `stdGateOps` (`LayeredCircuit.lean:115`) and
    `SLOp` (`StraightLine.lean:87`), whose bases are `{id, ¬, ∧}` and `{∧, ∨}` (no NAND); `Formulas.lean`'s
    `CNF`/`DNF`.
- **Permutations:** Mathlib `Equiv.Perm (Fin 5)`, `Equiv.Perm.cycleType`, `Equiv.ofBijective`.

**Cryptography hooks for the new security statements.**
- `LWE.Family` (`LWE/Assumption.lean`), with `advantageAt` and `DLWEAssumption` (`dlweAssumption_iff`); its fields
  `dimensionBound`, `samplesBound`, `residueBits` and `modulus_le_pow` feed `Parameters.ofFamily`.
- `LWE.encodeChallenge` (`LWE/Encoding.lean:42`); `Encoding.Modular.encodeMatrix`/`encodeVector`
  (`Encoding/Modular.lean:65/51`); `NUPPT.distinguisherL` (`Asymptotic/Adversary.lean:351`).
- `Negligible.add`/`.mono`/`.mul_pow` (`Foundations/Negligible.lean:86/74/126`), `negligible_two_pow_neg` :153,
  `negligible_polyExpr_mul` (`Asymptotic/EnsemblesLemmas.lean:377`).
- `distAdv_multi_le_sum` with `hybridPlant` (`Encryption/PublicKey/EnsembleSecurity.lean:134/110`) and
  `abs_sub_le_sum_hybrids` (`Foundations/Probability.lean:218`): the multi-ciphertext and key hybrids.
- `BitPublicKeyScheme.SingleBitSecure` (`EnsembleSecurity.lean:164`) is the machine-level bridge. It is **not**
  used: it needs GSW as a machine-level scheme (out of scope; §H8 item 13).
- `LWE/BitEncoding.lean`: `decode` :108 (`decode_eq` :112), `distance` :51, `codepoint` :42. Owner-side PR O2 adds
  the interval reader (P6-Q7).

**Registries.**
- `ComputationalModels.lean` has a **Models** list (each entry's defining file is imported) and a **Conversions**
  list (pointers only). `BoolCircuit.DAGCircuit.binarize`/`deMorgan` are listed there, so the NAND conversion
  belongs in Conversions.
- `machine-library-design.md` §14 (line 3037) is the host registry, rows H0–H17. The circuit hosts the phase consumes
  are public but **not registered**: `runWith`/`runWith_rel` (consumed by phase 5 and by `fheEval`) and
  `DAGCircuit.rewrite` (consumed by `binarize`, `deMorgan` and now the NAND conversion). See P6-Q17.

## H3. Design

**H3.1 The pipeline (NAND only).** `N = (n+1)ℓ` is the GSW ciphertext width, and `C₁, C₂` are the ciphertexts on
a NAND gate's two input wires.

```
nandFormula P C₁ C₂ : TreeCircuit (N + N)   -- ¬(Dec(C₁) ∧ Dec(C₂)); inputs: two blocks of key bits
barrington (nandFormula …) σ : 5-PBP        -- length ≤ 4^(decDepth P + 1); complexity layer (6a)
homEvalPBP P B (Fin.append evk₁ evk₂)       -- selector steps; noise (length)·2N·β_evk
bootNAND P evk₁ evk₂ C₁ C₂                  -- the coordinate σ 0 of the final state
fheEval P evk Cc cts                        -- Cc in NAND form; runWith over gates, each gate bootNAND evk evk
fheEvalCircuit P evk Cc hC cts              -- any fan-in-2 DAGCircuit: fheEval on Cc.toNANDForm hC (6a)
```

The bootstrapped noise `bootNoise P β = 4^(decDepth P + 1) · (2·(N·β))` does not depend on the input noise. So the
single invariant "encrypts its wire value with noise ≤ β*", with `2·(ℓ·β*) < ⌊q/2⌋`, carries through a circuit of
any depth by `runWith_rel`.

The formula has two key-bit blocks so that one lemma serves both pure FHE (`evk₁ = evk₂ = evk`) and the leveled
scheme (arguments under different keys, §H3.11). BV14's `f_{c₁,c₂}(x)` is the special case of a single block.

**H3.2 Decryption as a binary modular subset sum** (unchanged). Phase-5 decryption reads the column
`c = C·G⁻¹(⌊q/2⌋·e_{n+1})` and outputs `decode(⟨t, c⟩)` with `t = (−s, 1)`. With `x = G⁻¹(t) ∈ {0,1}^N`:

```
⟨t, c⟩ = ⟨G x, c⟩ = Σ_{i<N} x_i · a_i (mod q),   a = Gᵀ c  (public: depends only on C).
```

So decryption, as a function of the key bits, is `x ↦ decode((Σ x_i a_i) mod q)` [AP14, §5.1, p014-b001;
BV11, Lemma 4.5, p029-b002]. The key bits `keyBits P s := decomposeVec P (secretVector P s)` are what the
evaluation key encrypts (P6-Q8).

**H3.3 No depth term linear in `ℓ`** (unchanged). The bootstrapped noise is `4^d·2Nβ_evk` and must stay below
about `q/(4ℓ)`. A depth term `c·ℓ` would contribute `4^{cℓ} ≥ q^{2c}`. Hence:
- no Shannon or DNF construction (`dnfDAG`, FormulaKit templates) on `Θ(log q)`-bit values;
- rounding uses that `decode` is an **interval** test, `decode v ↔ v.val ∈ [lo, hi)` (O2);
- `S = Σ x_i a_i < N·q`, so `S mod q ∈ [lo, hi)` iff `⋁_{j<N} (jq + lo ≤ S < jq + hi)`. This is an OR of `N`
  two-sided comparisons with constants, each of depth `O(log b)` with `b = ℓ + ⌈log₂ N⌉ + 1`.

**H3.4 The formula-arithmetic construction** (unchanged; P6-Q5). Numbers are little-endian lists of formulas with
value `bitsVal (U.map (·.eval x))` (`Adder.lean:78`):
1. masked constants `x_i · a_i`, each bit a literal or a constant;
2. a carry-save (3:2) tree down to two numbers `U, W` with `U + W = S`: one `xor3`/`maj3` layer per level (depth
   +4), about `log_{3/2} N` levels;
3. `U + W ≥ c` as the carry-out of `U + W + (2^b − c)`: one more 3:2 layer, then a generate/propagate carry-out
   formula of depth `2⌈log₂(b+2)⌉ + 2`, whose value is `carryBit` (`Adder.lean:377`);
4. the interval and the OR over `j < N`, by balanced fan-in-2 nodes.

Negation is the depth-preserving De Morgan map `TreeCircuit.neg`. Draft depth target, with constants fixed at the
statement phase: `decDepth N ℓ ≤ 9·⌈log₂ N⌉ + 2·⌈log₂(ℓ + ⌈log₂ N⌉ + 3)⌉ + 21`.

**H3.5 The branching-program model and its host** [P6-Q4].
- **Model.** An instruction is `⟨var, map0, map1⟩` with `map0 map1 : Fin w → Fin w`, applied as `map0` when the
  bit is `0` (BV14's order). Bar89 lists the `x_j = 1` map first; the docstring discloses this. `IsPermutation`
  says every map is a bijection. Recognition follows Bar89 §1: a family with accepting sets
  `F_n ⊆ (Fin w → Fin w)`.
- **Host `evalWith`, push form.** It is generic in the selector `sel : β → α → α → α` and in the value type `α`
  (an additive commutative monoid). One step sends `V` to

  ```
  V'_i = sel (inp var) (Σ_{j : map0 j = i} V_j) (Σ_{j : map1 j = i} V_j).
  ```

  - For **every** map the Boolean semantics hold: with `α = ℕ` and `sel b u v = if b then v else u`, a one-hot
    state stays one-hot at `yield x s` (C8). That is BV14 Eq. (4) generalized.
  - For a **permutation** instruction each sum has exactly one term. The step is then BV14's pull form
    `V'_i = sel x (V_{σ₀⁻¹ i}) (V_{σ₁⁻¹ i})` (C6), which is what GSW's additive noise needs.
  - The fold over instructions carries a step-indexed relational lemma `evalWith_rel` (C7). GSW instantiates it
    with `α = β = Ciphertext P` and `sel = select P`.
- **Why the push form.** A pull form needs inverses, which a general map lacks. The push form keeps the host total
  and computable on the general model (P6-Q13) and confines `IsPermutation` to the consumers that need it.
- **Selector.** With the fresh selector on the left (Gate 41: "fresh ciphertexts belong on the left"),
  `select P C U V := mul P (gadget P − C) U + mul P C V`. If `C` encrypts the bit `b` with noise `β`, and `U, V`
  encrypt bits with noise at most `β_V`, then `select` encrypts `(1−b)·u + b·v` with noise `β_V + 2Nβ`
  (`Encrypts.mul` twice, then `.add`).
- **Start state and growth.** The start state is `Pi.single 0 (gadget P)`: zero noise (AP14's "include `G`").
  After `L` permutation instructions every coordinate has noise `L·2Nβ`, the worst-case form of
  [BV14, Lemma 3.6, p015-b001].

**H3.6 Composition order** (unchanged in substance). Bar89 writes products left to right: the leftmost permutation
acts first. The model fixes **program order**: `yield (B₁ ++ B₂) x = B₂.yield x ∘ B₁.yield x`, which is function
composition on general maps. The AND step's yield, written in Mathlib's `Equiv.Perm` product (right factor first),
is `σ₂⁻¹ * σ₁⁻¹ * σ₂ * σ₁`; this is Bar89's `σ₁σ₂σ₁⁻¹σ₂⁻¹`. Checked by computation for r2, 0-based:
- with `sigma1 = c[0,1,2,3,4]` and `sigma2 = c[0,2,4,3,1]`, the program-order commutator is `c[0,2,1,4,3]`, which
  is Bar89's `(13254)`;
- the right-to-left reading gives `c[0,3,2,4,1]`, Bar89's `(14352)`, as the ingest's transcription note says;
- the Lemma-1 conjugator `θ(σᵏ 0) = τᵏ 0` satisfies `θσθ⁻¹ = τ` for all 24 × 24 pairs of five-cycles.

**H3.7 Output convention** (unchanged). Five-cycle recognition with start state `0` ends in `σ 0 ≠ 0` on the
accepted set and in `0` off it. The output ciphertext is coordinate `σ 0`. BV14 reads coordinate 1; the deviation is
disclosed and harmless.

**H3.8 Evaluation key** (P6-Q8, as ruled). `evk_i = encrypt P pk (keyBits P s i) R_i`: public-key encryptions under
the user's own `pk` of the `N` bits of `G⁻¹(t)`, with noise `m·B` by `encrypts_encrypt`. This is [BV11, Def 3.8]'s
`{Enc_pk(sk[i])}_i`, and it keeps one `GSW.Parameters` record.

**H3.9 The NAND conversion** (new; P6-Q9, location ruling; representation P6-Q16).
- **NAND form.** A NAND gate is the model's own `¬` gate of fan-in at most 2 (`DAGGate.eval_eq`: "negated
  conjunction"): `DAGGate.IsNAND g := g.kind = .not ∧ g.args.length ≤ 2`, and `IsNANDForm` holds when every gate
  is one.
  - Fan-in 1 is negation, `NAND(a) = ¬a`. Fan-in 0 is the constant `false`, because `NAND()` is the negation of
    the empty conjunction.
  - NAND-form circuits are **not** `IsWellFormed`, which demands fan-in-1 `¬` gates (disclosed). Lemmas that
    assume well-formedness (`toTree_eval`, `deMorgan_*`) are not needed on this side.
- **Conversion.** An instance of the existing host `DAGCircuit.rewrite`, with a gadget in the style of
  `deMorganGadget`:

  | old gate | NAND gadget | gates | depth added |
  |---|---|---|---|
  | `∧[a,b]` | `t := NAND[a,b]`, `NAND[t]` | 2 | 2 |
  | `∨[a,b]` | `NAND[a]`, `NAND[b]`, `NAND[¬a,¬b]` | 3 | 2 |
  | `∧[a]`, `∨[a]` | `NAND[a]`, `NAND[that]` | 2 | 2 |
  | `∧[]` (true) | `f := NAND[]`, `NAND[f]` | 2 | 2 (absolute) |
  | `∨[]` (false) | `NAND[]` | 1 | 1 (absolute) |
  | `¬[…]` (≤ 2 args) | copied | 1 | 1 |

  - Every gadget costs at most `fan-in + 2` gates and at most 2 levels, so
    `GadgetCorrect n 2 (fun _ l => l ≤ 2) DAGGate.IsNAND (nandGadget n)` holds and
    the pass's lemmas give semantics, depth `≤ 2·depth` and size `≤ n + 4·#gates`.
  - The domain is the phase-5 hypothesis `∀ g ∈ C.gates, g.args.length ≤ 2`, not `IsFaninTwo`. A `¬` gate of
    fan-in 2 is already a NAND gate and is copied.
- **Bootstrapping.** Each NAND gate goes through BV14's binary `f_{c₁,c₂}`. Fan-in 1 is padded to `(a, a)`
  (`NAND(a, a) = ¬a`), and fan-in 0 to `(G, G)`, since `G` encrypts `1` with zero noise and `NAND(1, 1) = 0`.
  Disclosed.

**H3.10 Thm 2: the composition-tree circuit** (new; P6-Q3; circuit model P6-Q18). Thm 2 is built as a fan-in-2
**formula** (`TreeCircuit`) that mirrors the proof in [Bar89, Thm 2, p004-b003] section by section:
- *constant-depth section per instruction:* the wire "`ι` sends `i` to `j`" is `true`, `false`, `x_var` or
  `¬x_var` (depth ≤ 1);
- *composition circuit:* from the wires of `f` and `g`, the wire `(g ∘ f)(i) = k` is `⋁_j (f(i)=j ∧ g(j)=k)`, a
  balanced fan-in-2 OR (depth `+⌈log₂ w⌉ + 2`), using the promoted `balanced` (O1);
- *binary tree of composition circuits* over the instruction list (split at the midpoint): depth
  `(⌈log₂ w⌉ + 2)·⌈log₂ l⌉ + 1`;
- *constant-depth acceptance section:* `⋁_{f ∈ F} ⋀_i (B(x)(i) = f(i))`, at most `w^w` terms.

The formula has size `l^{O(log w)}`, polynomial for fixed `w`, by `size_succ_le_two_pow`. The family form then
reaches the book's `DAGCircuit` classes through `Language.InTreeNC.inNC`. A direct DAG construction is the
alternative (P6-Q18). `toFormula` need not be computable: P6-Q13 covers only `barrington`.

**H3.11 The leveled scheme** (new; P6-Q11; wiring P6-Q14).
- **Keys.** `L+1` independent honest key pairs `(pk_d, s_d)`, `d ≤ L`.
- **Wiring.** In a NAND-form circuit vertex `v` is kept under key `depthAt v`: inputs are fresh encryptions under
  `pk_0`, and a gate at depth `d` reads arguments of depth `< d` (`DAGGate.getD_lt_depth`). Its two arguments may
  sit at **different** lower depths. So the level-`d` evaluation key holds encryptions under `pk_d` of the key bits
  of **every** lower key `s_i`, `i < d`, and the gate is bootstrapped by the two-key `bootNAND` (H3.1). That is
  `N·L(L+1)/2` ciphertexts, and only the evaluation key depends on `L` [BV11, Thm 3.1].
- **Evaluation.** `runWith` over pairs (depth, ciphertext); the depth component is `DAGCircuit.depths`.
- **Correctness.** Every wire has noise at most `max(m·B, bootNoise P (m·B))`, whatever the circuit, so a NAND
  circuit of depth at most `L` decrypts correctly under `s_{depth}`.
  - The output's key index is the circuit depth, which is public. This is disclosed: BV11 Def 3.6's `Dec` is
    level-agnostic.
  - A general fan-in-2 `DAGCircuit` of depth `L'` needs `2L'+1` keys (N5).
- **Security** (IND-CPA from DLWE). The hybrid runs from the top level down: at step `d` the encryptions under
  `pk_d` are replaced by encryptions of `0`. This is legitimate because `s_d`'s bits occur only under keys above
  `d`, already replaced. A final phase-5 step handles the challenge under `pk_0`. Each step is a multi-ciphertext
  hybrid (`distAdv_multi_le_sum`) over phase-5 `distAdv_encrypt_le`; the independent-keys argument is
  [AP14, §5.3, p015-b002].

**H3.12 Security statements: concrete and asymptotic** (new; P6-Q10).
- **Concrete** (as ruled): `fheView P χ μ = (pk, evalKey, encrypt pk μ)` [BV14, §2.5, p007-b001: "the adversary is
  given both pk and evk"]. `WeakCircularSecure P χ ε` bounds every distinguisher's advantage between the views of
  `0` and `1` (G14). The `evk`-free view inherits phase 5's bound (G15); the leveled view has its key hybrid (L5).
  - Finding: over **all** function-level distinguishers the ruled predicate holds only for `ε` near `1`. An
    unbounded distinguisher recovers `s` from `pk` and decrypts. P6-Q15 proposes the per-distinguisher form.
- **Asymptotic.**
  - Over an `LWE.Family F` with `P_κ = Parameters.ofFamily F κ` and canonical bit encodings of the views (built
    from `encodeChallenge` and `Encoding.Modular.encodeMatrix`):
    - `WeakCircularSecureFamily F`: every NUPPT distinguisher has negligible advantage on the encoded FHE views;
      this is [BV11, Def 3.8] with [BV11, Def 3.1], which are asymptotic;
    - the explicit hypotheses `ReductionEfficient F` and `LeveledReductionEfficient F L` (A4);
    - A1: asymptotic IND-CPA of public-key GSW (the `evk`-free view) from `DLWEAssumption F`, A4 and the width
      condition;
    - A2: the pure-FHE reading of `WeakCircularSecureFamily`;
    - A3: asymptotic IND-CPA of the leveled scheme from `DLWEAssumption F` and A4.
  - **No NUPPT-bridge extension is needed.** `DLWEAssumption`'s interface (`advantageAt`, `distinguisherL`) and
    the `Negligible` closures (`add`, `mono`, `negligible_two_pow_neg`, `negligible_polyExpr_mul`) suffice once A4
    supplies the reduction machines.
  - A4 is a domination statement (some NUPPT has at least the reduction's DLWE advantage), not a machine
    construction. For the leveled hybrid, "worst level and position" is realizable with non-uniform advice
    (§H8 item 13).

## H4. Modules, namespaces, registration and definitions

**6a: complexity (Gate 45).** The model type is at the root (registered); its operations live in its namespace.

| File | Content | Namespace |
|---|---|---|
| `Complexity/BranchingPrograms.lean` | facade (new topic) | — |
| `Complexity/BranchingPrograms/Defs.lean` | model, `IsPermutation`, `yield`, families, classes | `BranchingProgram` |
| `Complexity/BranchingPrograms/Eval.lean` | host `evalWith`, `evalWith_rel` | `BranchingProgram` |
| `Complexity/BranchingPrograms/Barrington.lean` | Thm 1, Lemmas 1–3 | `BranchingProgram` |
| `Complexity/BranchingPrograms/BarringtonConverse.lean` | Thm 2 for one program | `BranchingProgram` |
| `Complexity/BranchingPrograms/NC1.lean` | DAG corollary, class inclusions, Corollary | `BranchingProgram` |
| `Complexity/CircuitComplexity/NANDForm.lean` | NAND form and conversion | `BoolCircuit` |
| `Complexity/CircuitComplexity/FormulaArith.lean` | facade (new sub-folder) | — |
| `…/FormulaArith/{Combinators,CarrySave,Compare,ModSum}.lean` | formula arithmetic | `BoolCircuit` |

**Path adjustments, and why:**
1. **`BranchingPrograms/NC1.lean`** (fifth child). The ruling put "Thm 1, Lemmas 1–3 and the NC¹ corollary" in
   `Barrington.lean` and Thm 2 in `BarringtonConverse.lean`.
   - The two-sided Corollary (BWBP = NC¹ = PBP₅) needs both theorems. `BarringtonConverse` imports `Barrington`, so
     the Corollary can only live downstream of both.
   - The class-level statements also put `Barrington.lean` near 1,000 lines (Thm 1 alone fills to about 550–720).
   - So the `DAGCircuit` corollary, NC¹ ⊆ PBP₅, BWBP ⊆ NC¹ and the Corollary go into `NC1.lean`, following
     `NCAC.lean`'s precedent of classes beside their theorems. `Barrington.lean` keeps Thm 1 with Lemmas 1–3.
2. **`CircuitComplexity/FormulaArith.lean`** (facade). Policy §1 gives every topic folder a facade with a
   `## Contents` list. `CircuitComplexity/` is flat today, so the new sub-folder needs one, imported by
   `CircuitComplexity.lean`.

`NANDForm.lean` sits beside `DAGTransform.lean`/`DAGFanin.lean` as ruled. It is imported by
`CircuitComplexity.lean`. `BranchingPrograms.lean` is imported by `TCSlib.lean` (policy §1, Exports).

**Registration** (P6-Q4).
- `ComputationalModels.lean`, **Models:** `BranchingProgram w n` and `BranchingProgramFamily w`, importing
  `Complexity.BranchingPrograms.Defs`.
- **Conversions:**
  - `BranchingProgram.barrington` (formulas → 5-PBPs, `Barrington.lean`);
  - `BranchingProgram.toFormula` (programs → formulas, `BarringtonConverse.lean`);
  - `BoolCircuit.DAGCircuit.toNANDForm` (DAGs → NAND form, `NANDForm.lean`).
- `machine-library-design.md` §14: the host `BranchingProgram.evalWith` as row H18 (P6-Q17 also proposes H19
  `runWith`/`runWith_rel` and H20 `DAGCircuit.rewrite`). The formula gadgets of F1–F10 become the first rows of a
  circuit/formula gadget registry (policy §1), in a new subsection of the same document.

**6b: cryptography (Gate 46).** Namespace `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW`, except
`LWE/Ratio.lean` (`TCSlib.Cryptography.LWE`). New children of the GSW facade:
`GSW/{Branching,DecryptFormula,Bootstrap,Circular,Leveled,LeveledSecurity,PolyRatio,Asymptotic}.lean`, and
`Cryptography/LWE/Ratio.lean` (`LWE.lean` facade). 6b **imports** the 6a modules and restates none of them.

**Owner-side PRs** (small, maintainer Lean, landing proved, audited as proofs):
- **O1** (P6-Q6, Gate 45). It promotes `TreeNCAC.combine` (and `pairUp`, `combineFuel` and the four lemmas) into
  `FormulaArith/Combinators.lean` as the public `TreeCircuit.balanced`. `TreeNCAC.toBinary` is re-pointed, with its
  statements unchanged. The proofs move unchanged, so nothing is duplicated.
- **O2** (P6-Q7, Gate 46). It adds `decodeLo`, `decodeHi` and `decode_iff_mem_Ico` to `LWE/BitEncoding.lean`.

**New definitions** (each lands with its readers: `_eq`/`_apply`/`_iff`, non-simp `simps` for structures):
- **Defs:**
  - instructions: `Instr`, `Instr.eval`, `Instr.IsPermutation`, `Instr.ofPerm`;
  - programs: `BranchingProgram`, `length`, `append`, `yield`, `IsPermutation`, `conj`, `complementLast`;
  - families and classes: `BranchingProgramFamily` (`language`, `IsPolyLength`, `IsPermutation`),
    `Language.InBWBP`, `Language.InPBP`.
- **Eval:** `Instr.stepWith`, `evalWith`.
- **Barrington:** `IsFiveCycle`, `FiveCycleRecognizes`, `sigma1`, `sigma2`, `conjugator`, `barrington`.
- **BarringtonConverse:** `Instr.wire`, `wireComp`, `compTree`, `toFormula`, `topDepth`.
- **NANDForm:** `DAGGate.IsNAND`, `DAGCircuit.IsNANDForm`, `nandGadget`, `DAGCircuit.toNANDForm`.
- **FormulaArith:**
  - `Combinators`: `TreeCircuit.{neg, subst, rename, const, and2, or2, xor2, xor3, maj3}` (`balanced` from O1);
  - `CarrySave`: `FormulaArith.{val, csaStep, csaReduce, csaLevels}`;
  - `Compare`: `FormulaArith.{bitAt, carryOut, geConst}`;
  - `ModSum`: `FormulaArith.{modSumInterval, modSumDepth}`.
- **GSW:**
  - formulas and bootstrapping: `select`, `homEvalPBP`, `homEvalFormula`, `keyBits`, `decConstants`,
    `decryptFormula`, `nandFormula`, `decDepth`, `bootNoise`, `bootNAND`, `bootGate`, `fheEval`, `fheEvalCircuit`,
    `evalKey`;
  - pure-FHE security: `fheView`, `WeakCircularSecure`;
  - leveled scheme: `levelKey`, `leveledEval`, `leveledView`, `levelReduction`, `levelTerm`;
  - asymptotic: `encodeCiphertext`, `encodeView`, `encodeFheView`, `encodeLeveledView`,
    `WeakCircularSecureFamily`, `ReductionEfficient`, `LeveledReductionEfficient`.
- **LWE:** `Family.RatioBounded`, `decodeLo`, `decodeHi` (O2). **GSW ratio:** `Parameters.ofFamily`, `pBoot`.

## H5. Statements (sketches)

"Target" means a `sorry` statement at the gate. Statements are sketches: names and shapes are fixed at the
statement phase, and constants marked *(fix)* are settled there by hand and by small `decide` checks. Every
docstring opens with a statement in words, then the `[TAG, location, anchor]` tag and any deviation; the proof
sketch follows. Target IDs: the C series is renumbered for the general model; F and G keep their r1 numbers where
the statement survives (F4 became O1, G4 became O2); N, L and A are new.

### H5.1 `Complexity/BranchingPrograms/Defs.lean` (C1–C4)

```lean
/-- An instruction `⟨j, f₀, f₁⟩` of width `w` over `n` inputs: read input `j`; apply `f₀` if it is `0`, `f₁` if
it is `1` [Bar89, §1, p001-b002]. Deviation: Bar89 lists the `x_j = 1` map first; the fields follow BV14's
`(var(t), σ_{t,0}, σ_{t,1})` [BV14, §3.3, p013-b002]. -/
structure BranchingProgram.Instr (w n : ℕ) where
  var : Fin n
  map0 : Fin w → Fin w
  map1 : Fin w → Fin w

/-- A width-`w` branching program on `n` inputs: a finite sequence of instructions [Bar89, §1, p001-b002]. -/
structure BranchingProgram (w n : ℕ) where
  instrs : List (BranchingProgram.Instr w n)

/-- The map `B` yields on `x`: the composition, in program order, of the maps its instructions produce;
`yield ⟨[]⟩ x = id` [Bar89, §1, p001-b002]. -/
def BranchingProgram.yield (B : BranchingProgram w n) (x : Fin n → Bool) : Fin w → Fin w

/-- `B` is a permutation branching program: every map of every instruction is a bijection
[Bar89, §1, p002-b001]. -/
def BranchingProgram.IsPermutation (B : BranchingProgram w n) : Prop

/-- A family of width-`w` programs with accepting sets: `u ∈ language ↔ (program |u|).yield u.get ∈ accept |u|`
[Bar89, §1, p002-b001: "x ∈ L iff B(x) ∈ F_n"]. Registered model. -/
structure BranchingProgramFamily (w : ℕ) where
  program : (n : ℕ) → BranchingProgram w n
  accept : (n : ℕ) → Finset (Fin w → Fin w)

/-- `L ∈ BWBP`: some width and some polynomial-length family (`length ≤ a·(n+1)^k`) recognize `L`
[Bar89, §1, p002-b001]. `L ∈ PBP_w`: the same with a permutation family of width `w`. -/
def Language.InBWBP (L : Language Bool) : Prop
def Language.InPBP (w : ℕ) (L : Language Bool) : Prop

-- C1. Yield in program order [Bar89, §1, p001-b002, "the composition of the functions produced by each of
-- the instructions"]; the Mathlib translation of §H3.6 is in the docstring.
theorem yield_append (B₁ B₂ : BranchingProgram w n) (x : Fin n → Bool) :
    (B₁ ++ B₂).yield x = B₂.yield x ∘ B₁.yield x
theorem yield_nil (x : Fin n → Bool) : (⟨[]⟩ : BranchingProgram w n).yield x = id

-- C2. Conjugating every map by `θ` conjugates the yield; length is unchanged [Bar89, Lemma 1 proof, p003-b003].
theorem yield_conj (B : BranchingProgram w n) (θ : Equiv.Perm (Fin w)) (x : Fin n → Bool) :
    (B.conj θ).yield x = θ ∘ B.yield x ∘ θ.symm
theorem length_conj : (B.conj θ).length = B.length
theorem length_append : (B₁ ++ B₂).length = B₁.length + B₂.length

-- C3. Post-composing the last instruction's two maps with `σ⁻¹` post-composes the yield
-- [Bar89, Lemma 2 proof, p003-b004: "B'(x) = e if x ∈ A and B'(x) = σ⁻¹ if x ∉ A"].
theorem yield_complementLast (B : BranchingProgram w n) (σ : Equiv.Perm (Fin w)) (hB : 0 < B.length)
    (x : Fin n → Bool) : (B.complementLast σ).yield x = σ.symm ∘ B.yield x
theorem length_complementLast : (B.complementLast σ).length = B.length

-- C4. Permutation programs [Bar89, §1, p002-b001]: closure and bijective yields (glue).
theorem isPermutation_iff : B.IsPermutation ↔ ∀ ι ∈ B.instrs, Function.Bijective ι.map0 ∧ Function.Bijective ι.map1
theorem IsPermutation.append; IsPermutation.conj; IsPermutation.complementLast
theorem IsPermutation.bijective_yield (h : B.IsPermutation) (x : Fin n → Bool) : Function.Bijective (B.yield x)
```

### H5.2 `Complexity/BranchingPrograms/Eval.lean` (C5–C8): the host

```lean
/-- One instruction on a state vector, push form: coordinate `i` receives, through `sel` applied to the
instruction's input, the sums of the entries that the `0`-branch and the `1`-branch send to `i`. Host step;
glue generalizing [BV14, Eq. (4), p013-b002]. -/
def Instr.stepWith [AddCommMonoid α] (sel : β → α → α → α) (inp : Fin n → β) (ι : Instr w n) (V : Fin w → α) :
    Fin w → α :=
  fun i => sel (inp ι.var) (∑ j ∈ univ.filter (ι.map0 · = i), V j) (∑ j ∈ univ.filter (ι.map1 · = i), V j)

/-- **The branching-program host**: fold `stepWith` over the instructions in program order. Generic in the
selector and the value type; consumers are the Boolean semantics (C8) and GSW (G2). -/
def evalWith [AddCommMonoid α] (sel : β → α → α → α) (inp : Fin n → β) (B : BranchingProgram w n)
    (V : Fin w → α) : Fin w → α

-- C5. Readers of the fold (glue).
theorem evalWith_nil : (⟨[]⟩ : BranchingProgram w n).evalWith sel inp V = V
theorem evalWith_append : (B₁ ++ B₂).evalWith sel inp V = B₂.evalWith sel inp (B₁.evalWith sel inp V)

-- C6. For a permutation instruction each sum has one term: BV14's pull form
-- `V'_i = sel x (V (σ₀⁻¹ i)) (V (σ₁⁻¹ i))` [BV14, Eq. (4), p013-b002].
theorem Instr.stepWith_of_isPermutation (hι : ι.IsPermutation) (i : Fin w) :
    ι.stepWith sel inp V i =
      sel (inp ι.var) (V ((Equiv.ofBijective _ hι.1).symm i)) (V ((Equiv.ofBijective _ hι.2).symm i))

-- C7. **Step-indexed relational host lemma** (glue): two runs related at step 0 and preserved by every step
-- stay related after `B.length` steps; GSW carries its noise `t·2Nβ` in the index.
theorem evalWith_rel [AddCommMonoid α] [AddCommMonoid α'] (sel : β → α → α → α) (sel' : β' → α' → α' → α')
    (inp : Fin n → β) (inp' : Fin n → β') (B : BranchingProgram w n)
    (R : ℕ → (Fin w → α) → (Fin w → α') → Prop) (V : Fin w → α) (V' : Fin w → α') (h0 : R 0 V V')
    (hstep : ∀ t (ht : t < B.length) U U', R t U U' →
      R (t + 1) ((B.instrs[t]).stepWith sel inp U) ((B.instrs[t]).stepWith sel' inp' U')) :
    R B.length (B.evalWith sel inp V) (B.evalWith sel' inp' V')

-- C8. Boolean semantics for **general** maps: a one-hot state stays one-hot at the yield
-- [BV14, Eq. (4), p013-b002, generalized from permutations; Bar89, §1].
theorem evalWith_single (B : BranchingProgram w n) (x : Fin n → Bool) (s : Fin w) :
    B.evalWith (fun b (u v : ℕ) => if b then v else u) x (Pi.single s 1) = Pi.single (B.yield x s) 1
```

### H5.3 `Complexity/BranchingPrograms/Barrington.lean` (C9–C16)

```lean
/-- `σ` is a five-cycle: `σ.cycleType = {5}` (decidable) [Bar89, §3, p003-b001]. -/
def IsFiveCycle (σ : Equiv.Perm (Fin 5)) : Prop

/-- `B` five-cycle recognizes `A` with output `σ`: `σ` is a five-cycle, and `B.yield x` is `σ` on `A` and `id`
off `A` [Bar89, §3, p003-b001]. -/
def FiveCycleRecognizes (B : BranchingProgram 5 n) (A : (Fin n → Bool) → Prop) (σ : Equiv.Perm (Fin 5)) : Prop

/-- Bar89's `(12345)` and `(13542)`, 0-based: `c[0,1,2,3,4]`, `c[0,2,4,3,1]` [Bar89, Lemma 3, p003-b005]. -/
def sigma1 : Equiv.Perm (Fin 5);  def sigma2 : Equiv.Perm (Fin 5)

/-- The explicit conjugator of two five-cycles, `θ (σ^k 0) = τ^k 0` for `k < 5` [Bar89, Lemma 1 proof,
p003-b003]; computable (P6-Q13). -/
def conjugator (σ τ : Equiv.Perm (Fin 5)) : Equiv.Perm (Fin 5)

/-- Barrington's program for a formula with output `σ` [Bar89, Thm 1 proof, p004-b002]:
- literal `x_i` gives `⟨i, 1, σ⟩` and `¬x_i` gives `⟨i, σ, 1⟩` (BV14's order);
- a constant node gives `⟨0, σ, σ⟩` (`true`) or `⟨0, 1, 1⟩` (`false`), hence `[NeZero n]`;
- a fan-in-1 node gives its child;
- `∧` gives the children with outputs `τ₁, τ₂, τ₁⁻¹, τ₂⁻¹`, where `τᵢ = θ σᵢ θ⁻¹` and `θ` conjugates the
  commutator of `sigma1` and `sigma2` to `σ`;
- `∨` uses De Morgan through `complementLast` (Lemma 2), the step the ingest's transcription note makes explicit.
Computable (P6-Q13). Fan-in above 2 is never used: the theorems assume `c.maxFanin ≤ 2`. -/
def barrington [NeZero n] : BoolCircuit.TreeCircuit n → Equiv.Perm (Fin 5) → BranchingProgram 5 n

-- C9. Lemma 3 in program order: the commutator of the two five-cycles is a five-cycle, `c[0,2,1,4,3]`
-- (Bar89's (13254)) [Bar89, Lemma 3, p003-b005]; kernel `decide`, no `native_decide`.
theorem isFiveCycle_sigma1 : IsFiveCycle sigma1;  theorem isFiveCycle_sigma2 : IsFiveCycle sigma2
theorem isFiveCycle_commutator : IsFiveCycle (sigma2⁻¹ * sigma1⁻¹ * sigma2 * sigma1)

-- C10. The conjugator conjugates [Bar89, Lemma 1 proof, p003-b003] (checked for all 24 × 24 pairs, §H3.6).
theorem conjugator_conj (hσ : IsFiveCycle σ) (hτ : IsFiveCycle τ) :
    conjugator σ τ * σ * (conjugator σ τ)⁻¹ = τ

-- C11. **Lemma 1**: change the output to any five-cycle at the same length [Bar89, Lemma 1, p003-b003].
theorem FiveCycleRecognizes.conj (h : FiveCycleRecognizes B A σ) (hτ : IsFiveCycle τ) :
    FiveCycleRecognizes (B.conj (conjugator σ τ)) A τ

-- C12. **Lemma 2**: the complement, same length, output `σ⁻¹` [Bar89, Lemma 2, p003-b004].
theorem FiveCycleRecognizes.complementLast (h : FiveCycleRecognizes B A σ) (hB : 0 < B.length) :
    FiveCycleRecognizes (B.complementLast σ) (fun x => ¬ A x) σ⁻¹

-- C13. **Barrington's Theorem 1**, recognition [Bar89, Thm 1, p003-b002, proof p004-b002;
-- BV14, Thm 3.5, p014-b001].
theorem barrington_recognizes [NeZero n] (c : BoolCircuit.TreeCircuit n) (hc : c.maxFanin ≤ 2)
    (hσ : IsFiveCycle σ) : FiveCycleRecognizes (barrington c σ) (fun x => c.eval x = true) σ

-- C14. **Theorem 1**, length [Bar89, Thm 1, p003-b002].
theorem barrington_length_le [NeZero n] (hc : c.maxFanin ≤ 2) (σ) : (barrington c σ).length ≤ 4 ^ c.depth
theorem barrington_length_pos [NeZero n] (c) (σ) : 0 < (barrington c σ).length          -- glue for Lemma 2

-- C15. The program is a permutation program (glue; [Bar89, Thm 1]: "a 5-PBP").
theorem isPermutation_barrington [NeZero n] (c) (σ) : (barrington c σ).IsPermutation

-- C16. BV14's reading from start state `0` (§H3.7) [BV14, Thm 3.5, p014-b001].
theorem barrington_yield_zero [NeZero n] (hc : c.maxFanin ≤ 2) (hσ : IsFiveCycle σ) (x : Fin n → Bool) :
    (barrington c σ).yield x 0 = if c.eval x then σ 0 else 0
```

### H5.4 `Complexity/BranchingPrograms/BarringtonConverse.lean` (C17–C21): Thm 2

```lean
-- C17. The constant-depth section per instruction [Bar89, Thm 2 proof, p004-b003]: the wire "ι sends i to j".
def Instr.wire (ι : Instr w n) (i j : Fin w) : BoolCircuit.TreeCircuit n
theorem Instr.wire_eval : (ι.wire i j).eval x = decide (ι.eval x i = j)
theorem Instr.depth_wire_le : (ι.wire i j).depth ≤ 1;  theorem Instr.maxFanin_wire_le : (ι.wire i j).maxFanin ≤ 2

-- C18. One composition circuit, `(wireComp F G) i k = ⋁_j (F i j ∧ G j k)` by `balanced`
-- [Bar89, Thm 2 proof: "may be computed by a fixed circuit whose size depends only on w"].
def wireComp (F G : Fin w → Fin w → BoolCircuit.TreeCircuit n) : Fin w → Fin w → BoolCircuit.TreeCircuit n
theorem wireComp_eval (hF : ∀ x i j, (F i j).eval x = decide (f x i = j))
    (hG : ∀ x i j, (G i j).eval x = decide (g x i = j)) : (wireComp F G i k).eval x = decide (g x (f x i) = k)
theorem depth_wireComp_le (hF : ∀ i j, (F i j).depth ≤ d) (hG : ∀ i j, (G i j).depth ≤ d) :
    (wireComp F G i k).depth ≤ d + Nat.clog 2 w + 2

-- C19. The binary tree of composition circuits over the instruction list, split at the midpoint
-- [Bar89, Thm 2 proof, p004-b003]; the empty list gives the identity wires.
def compTree : List (Instr w n) → Fin w → Fin w → BoolCircuit.TreeCircuit n
theorem compTree_eval (B : BranchingProgram w n) : (compTree B.instrs i j).eval x = decide (B.yield x i = j)
theorem depth_compTree_le : (compTree B.instrs i j).depth ≤ (Nat.clog 2 w + 2) * Nat.clog 2 B.length + 1   -- (fix)
theorem maxFanin_compTree_le : (compTree B.instrs i j).maxFanin ≤ 2

/-- **Barrington's Theorem 2, one program** [Bar89, Thm 2, p004-b003]: the formula
`⋁_{f ∈ F} ⋀_i compTree B i (f i)` (the constant-depth acceptance section on top) decides `B.yield x ∈ F`.
Deviation: built as a formula (fan-out one), not a DAG (P6-Q18); `noncomputable` is allowed. -/
noncomputable def toFormula (B : BranchingProgram w n) (F : Finset (Fin w → Fin w)) : BoolCircuit.TreeCircuit n

-- C20. Semantics [Bar89, Thm 2, p004-b003].
theorem toFormula_eval (B) (F) (x : Fin n → Bool) : (B.toFormula F).eval x = decide (B.yield x ∈ F)

-- C21. Depth `O(log l)` with a constant depending on `w` [Bar89, Thm 2, p004-b003], fan-in two.
theorem depth_toFormula_le : (B.toFormula F).depth ≤ (Nat.clog 2 w + 2) * Nat.clog 2 B.length + topDepth w
theorem maxFanin_toFormula_le : (B.toFormula F).maxFanin ≤ 2
--   with `topDepth w := w * Nat.clog 2 w + Nat.clog 2 w + 4`                                               (fix)
```

### H5.5 `Complexity/BranchingPrograms/NC1.lean` (C22–C25)

```lean
-- C22. **`DAGCircuit` corollary** [BV14, Thm 3.5, p014-b001; Bar89, Thm 1, p003-b002]: a fan-in-two circuit
-- on `n ≥ 1` inputs is five-cycle recognized at length `≤ 4^depth`, through `toTree` (depth-preserving).
theorem exists_fiveCycleRecognizes_of_dagCircuit [NeZero n] (C : BoolCircuit.DAGCircuit n) (hC : C.IsFaninTwo)
    (hσ : IsFiveCycle σ) : ∃ B : BranchingProgram 5 n, B.IsPermutation ∧ B.length ≤ 4 ^ C.depth ∧
      FiveCycleRecognizes B (fun x => C.eval x = true) σ

-- C23. **NC¹ ⊆ polynomial-length width-5 PBPs** [Bar89, Corollary, p004-b004; abstract, p001-b001], through
-- `Language.InNC.inTreeNC_one`; length `4^{b(log₂ n + 1)} ≤ 4^b (n+1)^{2b}`; `n = 0` by the accepting set.
theorem Language.InNC.inPBP_five {L : Language Bool} (h : L.InNC 1) : L.InPBP 5

-- C24. **BWBP ⊆ NC¹**, Theorem 2 for families [Bar89, Thm 2, p004-b003; abstract, p001-b001]: `toFormula` per
-- length gives a fan-in-2 formula family of depth `O(log n)` and size `≤ 2^(depth+1)` (`size_succ_le_two_pow`),
-- so `L.InTreeNC 1`, then `Language.InTreeNC.inNC`.
theorem Language.InBWBP.inNC_one {L : Language Bool} (h : L.InBWBP) : L.InNC 1

-- C25. **Barrington's Corollary** [Bar89, Corollary, p004-b004]: BWBP = nonuniform NC¹ = PBP₅.
theorem Language.inNC_one_iff_inBWBP (L : Language Bool) : L.InNC 1 ↔ L.InBWBP
theorem Language.inNC_one_iff_inPBP_five (L : Language Bool) : L.InNC 1 ↔ L.InPBP 5
```

### H5.6 `Complexity/CircuitComplexity/NANDForm.lean` (N1–N6)

```lean
/-- A NAND gate: a `¬` gate (negated conjunction, `DAGGate.eval_eq`) reading at most two vertices; fan-in 1 is
negation, fan-in 0 the constant `false`. Not `NAndCircuit` (`Basic.lean:356`, an AND-rooted normal form).
Glue; motivated by [BV14, Def 2.13, p008-b002; Thm 3.5, p014-b001]. -/
def DAGGate.IsNAND (g : DAGGate) : Prop := g.kind = .not ∧ g.args.length ≤ 2
/-- Every gate is a NAND gate. Such circuits are not `IsWellFormed` (fan-in-2 `¬` gates). -/
def DAGCircuit.IsNANDForm (C : DAGCircuit n) : Prop := ∀ g ∈ C.gates, g.IsNAND

-- N1. NAND semantics (reader; glue).
theorem DAGGate.eval_of_isNAND (hg : g.IsNAND) (vals : List Bool) :
    g.eval vals = !(g.args.all fun a => vals.getD a false)

-- N2. The gadget of §H3.9 is correct in the sense of `GadgetCorrect` (`DAGTransform.lean:68`), with depth
-- factor 2 and domain "fan-in ≤ 2" (glue; proof as `deMorganGadget_correct`, `DAGFanin.lean:499`).
theorem nandGadget_correct : GadgetCorrect n 2 (fun _ l => l ≤ 2) DAGGate.IsNAND (nandGadget n)

/-- The NAND form of a circuit with fan-in at most two: `C.rewrite (nandGadget n) nandGadget_correct hC`. -/
def DAGCircuit.toNANDForm (C : DAGCircuit n) (hC : ∀ g ∈ C.gates, g.args.length ≤ 2) : DAGCircuit n

-- N3–N6: semantics, form, depth, size (from `rewrite_eval`, `rewrite_new_gates`, `rewrite_depth_le`,
-- `rewrite_length_le`; glue).
theorem toNANDForm_eval (x : Fin n → Bool) : (C.toNANDForm hC).eval x = C.eval x            -- N3
theorem toNANDForm_isNANDForm : (C.toNANDForm hC).IsNANDForm                                -- N4
theorem toNANDForm_depth_le : (C.toNANDForm hC).depth ≤ 2 * C.depth                         -- N5
theorem toNANDForm_size_le : (C.toNANDForm hC).size ≤ n + 4 * C.gates.length                -- N6
```

### H5.7 `Complexity/CircuitComplexity/FormulaArith/` (F1–F3, F5–F10; P6-Q5, P6-Q6)

`Combinators.lean` (`balanced` and its four lemmas arrive proved with O1, §H5.8):

```lean
-- F1. De Morgan negation (literals flip sign, nodes flip kind): depth- and fan-in-preserving (glue).
theorem TreeCircuit.neg_eval : c.neg.eval x = !c.eval x
theorem TreeCircuit.depth_neg : c.neg.depth = c.depth;  theorem TreeCircuit.maxFanin_neg : c.neg.maxFanin = c.maxFanin
-- F2. Substitution of formulas for variables (a negative literal becomes `(f i).neg`); `rename` is the
-- literal case and preserves depth (glue).
theorem subst_eval : (c.subst f).eval x = c.eval (fun i => (f i).eval x)
theorem depth_subst_le : (c.subst f).depth ≤ c.depth + ⨆ i, (f i).depth;  theorem maxFanin_subst_le
theorem rename_eval : (c.rename e).eval x = c.eval (x ∘ e);  theorem depth_rename : (c.rename e).depth = c.depth
-- F3. Gadgets `and2/or2/xor2/xor3/maj3`: value, depth (+1, +1, +2, +4, +3) (fix), fan-in ≤ 2 (glue).
theorem xor3_eval : (xor3 a b c).eval x = (a.eval x ^^ b.eval x ^^ c.eval x)
theorem maj3_eval : (maj3 a b c).eval x = (a.eval x && b.eval x || c.eval x && (a.eval x ^^ b.eval x))
```

`CarrySave.lean`, `Compare.lean`, `ModSum.lean`:

```lean
/-- The value of a little-endian formula number: `val x U = bitsVal (U.map (·.eval x))` (`Adder.lean:78`). -/
def FormulaArith.val (x : Fin n → Bool) (U : List (TreeCircuit n)) : ℕ

-- F5. One 3:2 layer: `val A + val B + val C = val S + val K` (`S` bitwise `xor3`, `K` shifted `maj3`), depth +4
-- [BV11, Lemma 4.5 proof, p029-b002: "the summation … can be done in depth O(log k + log log p)"].
-- Deviation: carry-save tree.
theorem csaStep_val; theorem depth_csaStep_le
-- F6. The reduction to two numbers: value preserved; depth ≤ 4·csaLevels k + d₀; csaLevels k ≤ 2⌈log₂ k⌉ + 3.
theorem csaReduce_val; theorem depth_csaReduce_le; theorem csaLevels_le                                  -- (fix)
-- F7. Carry-out of `U + W` at position `b` (generate/propagate, depth `2⌈log₂(b+1)⌉ + 2`): its value is
-- `carryBit` (`Adder.lean:377`), hence `decide (2^b ≤ val U + val W)` by `prefixVal_add` (`Adder.lean:397`).
theorem carryOut_eval : (carryOut U W).eval x = carryBit (bitAt x U) (bitAt x W) b
theorem carryOut_eval_le (hU : U.length ≤ b) (hW : W.length ≤ b) :
    (carryOut U W).eval x = decide (2 ^ b ≤ FormulaArith.val x U + FormulaArith.val x W)
-- F8. Comparison with a constant: `(geConst U W c).eval x = decide (c ≤ val x U + val x W)`; depth.
theorem geConst_eval; theorem depth_geConst_le
-- F9. **The modular interval sum** [BV11, Lemma 4.5, p029-b001; BV14, Prop 3.4, p011-b001]:
theorem modSumInterval_eval (ha : ∀ i, a i < q) (hlh : lo ≤ hi) (hhq : hi ≤ q) :
    (modSumInterval a q lo hi).eval x =
      decide (lo ≤ (∑ i, (x i).toNat * a i) % q ∧ (∑ i, (x i).toNat * a i) % q < hi)
-- F10. Depth `O(log M + log log q)` with no term linear in `log q` (§H3.3), fan-in two:
theorem depth_modSumInterval_le : (modSumInterval a q lo hi).depth ≤ modSumDepth M q
theorem modSumDepth_le : modSumDepth M q ≤ 9 * Nat.clog 2 M + 2 * Nat.clog 2 (Nat.clog 2 q + Nat.clog 2 M + 3) + 21
theorem maxFanin_modSumInterval_le : (modSumInterval a q lo hi).maxFanin ≤ 2                             -- (fix)
```

### H5.8 The owner-side PRs (O1, O2): proved, not fill units

```lean
-- O1 (P6-Q6; `FormulaArith/Combinators.lean`, moved from TreeNCAC.lean:175–351; TreeNCAC re-pointed).
/-- A balanced binary tree of `b`-gates over `cs`, computing the unbounded `b`-gate (the former private
`TreeNCAC.combine`; its existing docstring tag is kept). -/
def TreeCircuit.balanced (b : Bool) (cs : List (TreeCircuit n)) : TreeCircuit n
theorem balanced_eval : (balanced b cs).eval x = (TreeCircuit.node b cs).eval x
theorem maxFanin_balanced_le : (balanced b cs).maxFanin ≤ max 2 (TreeCircuit.maxFaninL cs)
theorem depth_balanced_le : (balanced b cs).depth ≤ TreeCircuit.maxDepth cs + Nat.clog 2 cs.length + 1
theorem size_balanced_le : (balanced b cs).size ≤ TreeCircuit.sumSize cs + cs.length + 1

-- O2 (P6-Q7; `LWE/BitEncoding.lean`). With h = ⌊q/2⌋: lo = ⌊h/2⌋ + 1, hi = ⌈(q + h)/2⌉. Checked by computation
-- for 2 ≤ q < 300 against Mathlib's `valMinAbs` convention (r2). Glue for the file's `decode`.
def decodeLo (P : LWE.Parameters) : ℕ;  theorem decodeLo_eq : decodeLo P = P.modulus / 2 / 2 + 1
def decodeHi (P : LWE.Parameters) : ℕ;  theorem decodeHi_eq : decodeHi P = (P.modulus + P.modulus / 2 + 1) / 2
theorem decode_iff_mem_Ico (P : LWE.Parameters) (v : ZMod P.modulus) :
    decode P v = true ↔ decodeLo P ≤ v.val ∧ v.val < decodeHi P
```

### H5.9 `GSW/Branching.lean` (G1–G3)

```lean
-- G1. **The selector step** [BV14, Eq. (5)–(6), p014-b002; Lemma 3.6 proof, p015-b002, mirrored;
-- AP14, Eq. (4.1), p011-b001; Lemma 4.1, p012-b001].
theorem Encrypts.select (hC : Encrypts P t b β C) (hU : Encrypts P t u βV U) (hV : Encrypts P t v βV V)
    (hb : b = 0 ∨ b = 1) : Encrypts P t ((1 - b) * u + b * v) (βV + 2 * (P.columns * β)) (select P C U V)

-- G2. **Homomorphic PBP evaluation**: `homEvalPBP P B cts V := B.evalWith (select P) cts V` (C7 with
-- C6), for a permutation program [BV14, Lemma 3.6, p015-b001, worst-case form].
theorem encrypts_homEvalPBP (hB : B.IsPermutation) (hin : ∀ j, Encrypts P t (x j).toNat β (cts j)) (s₀ i) :
    Encrypts P t (decide (B.yield x s₀ = i)).toNat (B.length * (2 * (P.columns * β)))
      (homEvalPBP P B cts (Pi.single s₀ (gadget P)) i)

-- G3. **Homomorphic formula evaluation**: Barrington (C13–C16), then G2; output coordinate `σ 0` (§H3.7)
-- [BV14, Thm 3.5 with Lemma 3.6; Pei16, §6.1.3 bootstrapping, p070-b001].
theorem encrypts_homEvalFormula [NeZero k] (c : TreeCircuit k) (hc : c.maxFanin ≤ 2)
    (hin : ∀ j, Encrypts P t (x j).toNat β (cts j)) :
    Encrypts P t (c.eval x).toNat (4 ^ c.depth * (2 * (P.columns * β))) (homEvalFormula P c cts)
```

### H5.10 `GSW/DecryptFormula.lean` (G5–G8; G4 is O2)

```lean
-- G5. Decryption is a binary subset sum of public constants `Gᵀc` [AP14, §5.1, p014-b001; Pei16, §5.4.3].
theorem vecMul_secretVector_eq_sum :
    secretVector P s ⬝ᵥ c = ∑ i, ((keyBits P s i).toNat : ZMod q) * (decConstants P C i)
-- G6. **The decryption formula** [BV14, Prop 3.4, p011-b001; BV11, Lemma 4.5, p029-b001]: built from F9 and O2.
theorem decryptFormula_eval : (decryptFormula P C).eval (keyBits P s) = decrypt P s C
-- G7. **The augmented NAND formula**, two key blocks [BV14, Def 2.13, p008-b002; BV11, Def 3.7, p014-b002].
-- Deviation: two blocks so that the leveled scheme reuses it; BV14's single key is `s₁ = s₂` (§H3.1).
--   nandFormula P C₁ C₂ := (and2 ((decryptFormula P C₁).rename (Fin.castAdd _))
--                                ((decryptFormula P C₂).rename (Fin.natAdd _))).neg
theorem nandFormula_eval : (nandFormula P C₁ C₂).eval (Fin.append (keyBits P s₁) (keyBits P s₂)) =
    !(decrypt P s₁ C₁ && decrypt P s₂ C₂)
-- G8. Depth and fan-in [BV14, Lemma 4.4, p019-b001: "depth c_dec·log(k log q(k)) + 1"].
theorem depth_nandFormula_le : (nandFormula P C₁ C₂).depth ≤ decDepth P + 1
theorem maxFanin_nandFormula_le : (nandFormula P C₁ C₂).maxFanin ≤ 2
theorem decDepth_le : decDepth P ≤ 9 * Nat.clog 2 P.columns + 2 * Nat.clog 2 (P.width + …) + 21          -- (fix)
```

### H5.11 `GSW/Bootstrap.lean` (G9–G13, G18)

```lean
-- G9. **Bootstrapped NAND, key-switching and two-key form** [BV14, Thm 2.14, p008-b003; Lemma 4.4, p019-b001;
-- BV11, Thm 3.1, p015-b001]. No hypothesis on `C₁, C₂`: the output encrypts the NAND of their decryptions.
--   bootNAND P evk₁ evk₂ C₁ C₂ := homEvalFormula P (nandFormula P C₁ C₂) (Fin.append evk₁ evk₂)
theorem encrypts_bootNAND (h₁ : ∀ i, Encrypts P t' (keyBits P s₁ i).toNat βk (evk₁ i))
    (h₂ : ∀ i, Encrypts P t' (keyBits P s₂ i).toNat βk (evk₂ i)) :
    Encrypts P t' (!(decrypt P s₁ C₁ && decrypt P s₂ C₂)).toNat (bootNoise P βk) (bootNAND P evk₁ evk₂ C₁ C₂)

-- G10. **Pure-FHE correctness for NAND-form circuits of every depth** [BV14, Thm 2.14 second part, p008-b003;
-- BV11, Thm 3.2, Def 3.5, p015-b001, p014-b001]. `bootGate` pads fan-in 1 to (a, a), 0 to (G, G) (§H3.9).
theorem decrypt_fheEval (hNAND : Cc.IsNANDForm)
    (hevk : ∀ i, Encrypts P (secretVector P s) (keyBits P s i).toNat βk (evk i))
    (hin : ∀ j, Encrypts P (secretVector P s) (x j).toNat βin (cts j)) (hβin : 2 * (P.width * βin) < q / 2)
    (hboot : 2 * (P.width * bootNoise P βk) < q / 2) : decrypt P s (fheEval P evk Cc cts) = Cc.eval x

-- G18. **Every fan-in-2 circuit**, through the NAND conversion (N3, N4) [BV14, Thm 2.14; BV11, Def 3.5].
theorem decrypt_fheEvalCircuit (hC : ∀ g ∈ Cc.gates, g.args.length ≤ 2) … :
    decrypt P s (fheEvalCircuit P evk Cc hC cts) = Cc.eval x

-- G11. The evaluation key of P6-Q8 [BV11, Def 3.8, p015-b001; BV14, Lemma 4.4, p019-b001].
theorem encrypts_evalKey : Encrypts P (secretVector P s) (keyBits P s i).toNat (P.lwe.samples * B) (evalKey P pk s R i)
-- G12. **Honest keys, every circuit** [BV14, Thm 3.7, p016-b001, worst-case and any depth].
theorem decrypt_keygen_fheEvalCircuit (hχ : χ.Bounded B)
    (hsep : 2 * (P.width * bootNoise P (P.lwe.samples * B)) < q / 2) … : … = Cc.eval x
-- G13. Closed form of the bootstrapped noise from `decDepth_le` (glue).
theorem bootNoise_le :                                                                             -- (fix)
    bootNoise P β ≤ 4 ^ c₀ * N ^ (2 * c₁ + 1) * (ℓ + Nat.clog 2 N + 3) ^ (2 * c₂) * (2 * β)
```

Compactness [BV14, Def 2.12, p008-b001; BV11, Def 3.4, p014-b001; Lemma 3.3, p015-b001] holds by typing:
`fheEval`, `fheEvalCircuit` and `leveledEval` return a `Ciphertext P` whatever the circuit. Each docstring records
this; there is no separate theorem (P6-Q10).

### H5.12 `GSW/Circular.lean` (G14–G15): concrete

```lean
/-- The FHE view `(pk, evk, Enc_pk(μ))` from honest key generation [BV14, §2.5, p007-b001: "the adversary is
given both pk and evk"; BV11, Def 3.1, p013-b002]. -/
def fheView (P) (χ) (μ : Bool) : Seeds P χ → FheView P

/-- **Weak circular security, concrete** (as ruled, P6-Q10) [BV11, Def 3.8, p015-b001; BV14, Thm 2.14, p008-b003;
Pei16, §6.1.2, p068-b001]: every distinguisher's advantage between the FHE views of `0` and `1` is at most `ε`.
A hypothesis, never derived from LWE (phase-5 Q15). Docstring note: over all functions this holds only for `ε`
near `1` (an unbounded distinguisher recovers `s`); P6-Q15 proposes the per-distinguisher form. -/
def WeakCircularSecure (P) (χ) (ε : ℝ) : Prop :=
  ∀ {ρ : Type} [Fintype ρ] [Nonempty ρ] (D : FheView P → ρ → Bool),
    distAdv (fheView P χ false) (fheView P χ true) D ≤ ε

-- G14. The security half of [BV11, Thm 3.2, p015-b001], deliberately thin: pure-FHE security *is* (A1).
theorem distAdv_fheView_le (h : WeakCircularSecure P χ ε) (D) : distAdv (fheView P χ false) (fheView P χ true) D ≤ ε
-- G15. Without `evk` the view is phase 5's and inherits `distAdv_encrypt_le` (two DLWE + 2Nε)
-- [GSW13, §3.2, p009-b002; AP14, §5.3, p015-b002: "if … generated independently"].
theorem distAdv_fheView_noEvk_le …
```

### H5.13 `GSW/Leveled.lean` (L1–L3): the leveled scheme

```lean
/-- The level-`d` evaluation key (P6-Q14 A): encryptions under `pk_d` of the `N` key bits of every lower key
`s_i`, `i < d` [BV11, Thm 3.1, p015-b001: "only the length of the evaluation key depends on the level L";
BV14, Thm 2.14 first part, p008-b003]. In all, `N·L(L+1)/2` ciphertexts. The key-chain construction is not in an
ingested passage (§H1 gap 1; P6-Q19). -/
def levelKey (P) (pks : Fin (L+1) → PublicKey P) (ss : Fin (L+1) → Secret P) (R : LevelCoins P L)
    (d : Fin (L+1)) (i : Fin d) : Fin P.columns → Ciphertext P

/-- Leveled evaluation of a NAND-form circuit: vertex `v` under key `depthAt v`; a gate at depth `d` is
`bootNAND` with `levelKey d (depth a)` and `levelKey d (depth b)`; `runWith` over (depth, ciphertext) pairs. -/
def leveledEval (P) (lk) (Cc : DAGCircuit k) (cts : Fin k → Ciphertext P) : Ciphertext P

-- L1. Evaluation-key noise `m·B` (glue; `encrypts_encrypt`).
theorem encrypts_levelKey (hχ : χ.Bounded B) … :
    Encrypts P (secretVector P (ss d)) (keyBits P (ss (i.castLT _)) j).toNat (P.lwe.samples * B) (levelKey … d i j)
-- L2. **Leveled correctness, noise form** [BV14, Thm 2.14 first part; BV11, Thm 3.1, Def 3.6, p014-b001]: every
-- vertex `v` encrypts its value under `s_{depthAt v}` with noise ≤ max βin (bootNoise P βk); hence the output.
theorem encrypts_leveledEval (hNAND : Cc.IsNANDForm) (hdepth : Cc.depth ≤ L) … :
    Encrypts P (secretVector P (ss ⟨Cc.depth, _⟩)) (Cc.eval x).toNat (max βin (bootNoise P βk)) (leveledEval …)
-- L3. **Honest keys, every NAND circuit of depth ≤ L** [BV14, Thm 3.7, p016-b001: "a leveled FHE scheme,
-- without additional assumptions"]. Deviation: decryption uses the public output level `Cc.depth` (§H3.11).
theorem decrypt_keygen_leveledEval (hχ : χ.Bounded B)
    (hsep : 2 * (P.width * bootNoise P (P.lwe.samples * B)) < q / 2) (hin : 2 * (P.width * (P.lwe.samples * B)) < q / 2)
    (hNAND : Cc.IsNANDForm) (hdepth : Cc.depth ≤ L) … :
    decrypt P (ss ⟨Cc.depth, _⟩) (leveledEval P lk Cc fun j => encrypt P (pks 0) (x j) (R' j)) = Cc.eval x
```

### H5.14 `GSW/LeveledSecurity.lean` (L4–L5): IND-CPA by a key hybrid from DLWE

```lean
/-- The leveled FHE view: the `L+1` public keys, the leveled evaluation key and `Enc_{pk_0}(μ)`, from independent
honest key generations [BV11, Def 3.1, p013-b002, for the leveled scheme]. -/
def leveledView (P) (χ) (L : ℕ) (μ : Bool) : LeveledSeeds P χ L → LeveledView P L

/-- The explicit level-`d`, position-`j` reduction: it samples the other keys itself, plants the DLWE challenge
key as `pk_d`, encrypts the other positions under it, and runs `D` (composition of `hybridPlant` and phase-5
`reduction`). `levelTerm` is its two DLWE advantages plus `2·(N·ε_LHL)` (`Regev.extractionError`). -/
def levelReduction (P) (χ) (L d : ℕ) (j : ℕ) (μ : Bool) (D) : … → Bool
def levelTerm (P) (χ) (L d j) (D) : ℝ

-- L4. **One level**: replacing the encryptions under `pk_d` by encryptions of `0` costs at most
-- `∑_{j < N·d} levelTerm P χ L d j D` [AP14, §5.3, p015-b002 (independent keys); GSW13, §3.2, Lemma 1,
-- p009-b002, p010-b001]; by `distAdv_multi_le_sum` over phase-5 `distAdv_encrypt_le`.
theorem distAdv_levelHybrid_le …

-- L5. **IND-CPA of leveled GSW-FHE from DLWE** [BV14, Thm 2.14 first part, p008-b003, and Thm 3.7, p016-b001;
-- BV11, Thm 3.1, p015-b001]: hybrids from level `L` down to `1` on both sides, then the phase-5 challenge step.
theorem distAdv_leveledView_le (D) :
    distAdv (leveledView P χ L μ₀) (leveledView P χ L μ₁) D ≤
      2 * ∑ d ∈ Finset.Icc 1 L, ∑ j ∈ Finset.range (P.columns * d), levelTerm P χ L d j D + challengeTerm P χ L D
```

### H5.15 `Cryptography/LWE/Ratio.lean` and `GSW/PolyRatio.lean` (G16–G17; P6-Q12, as ruled)

```lean
/-- The ratio predicate (phase-5 Q16): `B`-bounded noise and `q ≤ p(κ)·B(κ)` at every `κ`; `_iff` reader. -/
def LWE.Family.RatioBounded (F : LWE.Family) (B : ℕ → ℕ) (p : PolyExpr) : Prop
/-- GSW parameters of a family: `lwe := F.parameters κ`, `width := F.residueBits.eval κ`,
`modulus_le := F.modulus_le_pow κ`; non-simp `simps` [GSW13, §3.1; phase-5 §G4]. -/
def Parameters.ofFamily (F : LWE.Family) (κ : ℕ) : Parameters
-- G16. An explicit `PolyExpr` `pBoot` with `4·ℓ·bootNoise (ofFamily F κ) (m·B κ) ≤ pBoot.eval κ · B κ`
-- [BV14, Thm 3.7, p016-b001, worst-case analogue].
theorem bootRatio_le_poly …
-- G17. **Polynomial-ratio correctness**: `pBoot.eval κ · B κ < q κ` and `B`-bounded noise ⇒ pure and leveled
-- bootstrapped GSW at `κ` are correct on every circuit (G12, L3); with `RatioBounded F B p` this is (A2)'s regime
-- [BV14, §3.4, p016-b001].
theorem decrypt_fheEval_of_ratio …
```

### H5.16 `GSW/Asymptotic.lean` (A1–A3): asymptotic forms (P6-Q10)

```lean
/-- Canonical bit encodings: a ciphertext by `Encoding.Modular.encodeMatrix P.width`; the views by
`LWE.encodeChallenge P.lwe P.width` for each public key followed by the ciphertexts (`_eq`, `_length` readers). -/
def encodeCiphertext (P) (C : Ciphertext P) : List Bool
def encodeView (P) : View P → List Bool;  def encodeFheView (P) : FheView P → List Bool
def encodeLeveledView (P) (L) : LeveledView P L → List Bool

/-- **Weak circular security, asymptotic** [BV11, Def 3.8 with Def 3.1, p015-b001, p013-b002; BV14, Thm 2.14]:
every non-uniform PPT distinguisher has negligible advantage on the encoded FHE views at `P_κ = ofFamily F κ`. -/
def WeakCircularSecureFamily (F : LWE.Family) : Prop :=
  ∀ D : NUPPT, Negligible fun κ => distAdv (fheView (ofFamily F κ) (F.noise κ) false)
    (fheView (ofFamily F κ) (F.noise κ) true) (fun v r => D.distinguisherL κ (encodeFheView (ofFamily F κ) v) r)

/-- **(A4) Reduction efficiency, explicit hypothesis** (P6-Q10). For every non-uniform PPT distinguisher `D` of
encoded GSW views and every bit `μ`, some non-uniform PPT `D'` has, at every `κ`, DLWE advantage at least that of
phase 5's encryption reduction run on `D`:
`decisionAdvantage P_κ.lwe χ_κ (reduction P_κ μ D_κ) ≤ F.advantageAt D' κ`, where `P_κ = ofFamily F κ` and
`D_κ v r = D.distinguisherL κ (encodeView P_κ v) r`. It says that encrypting a fixed bit under the challenge key
with fresh binary coins, re-encoding and running `D` is polynomial-time. The library does not prove it: there is
no machine-level GSW encryptor, which is out of scope as for phase 5 (Q8). Real-valued on both sides, so no
transport between `(ofFamily F κ).lwe` and `F.parameters κ` is needed. -/
def ReductionEfficient (F : LWE.Family) : Prop :=
  ∀ (D : NUPPT) (μ : Bool), ∃ D' : NUPPT, ∀ κ,
    LWE.decisionAdvantage (ofFamily F κ).lwe (F.noise κ)
        (reduction (ofFamily F κ) μ fun v r => D.distinguisherL κ (encodeView (ofFamily F κ) v) r) ≤
      F.advantageAt D' κ

/-- **(A4) for the leveled hybrid**: as `ReductionEfficient`, for the level reductions of L4. One `D'` dominates
every level `d ≤ L.eval κ` and position `j` at each `κ`; non-uniform advice can select the worst `(d, j)`. -/
def LeveledReductionEfficient (F : LWE.Family) (L : PolyExpr) : Prop :=
  ∀ (D : NUPPT) (μ : Bool), ∃ D' : NUPPT, ∀ κ, ∀ d ≤ L.eval κ, ∀ j < (ofFamily F κ).columns * d,
    levelDLWEAdvantage F L κ d j μ D ≤ F.advantageAt D' κ
--   where `levelDLWEAdvantage F L κ d j μ D` is `LWE.decisionAdvantage (ofFamily F κ).lwe (F.noise κ)` of
--   `levelReduction (ofFamily F κ) (F.noise κ) (L.eval κ) d j μ D_κ` (L4), with `D_κ` reading `encodeLeveledView`.

-- A1. **Asymptotic IND-CPA of public-key GSW** (the evk-free view) [GSW13, §3.2, p009-b002; BV11, Def 3.1]:
-- phase-5 `distAdv_encrypt_le_of_width` at each κ, (A4), `Negligible.add`, `negligible_polyExpr_mul`,
-- `negligible_two_pow_neg`.
theorem indCPA_of_dlweAssumption (F : LWE.Family) (hF : LWE.DLWEAssumption F) (heff : ReductionEfficient F)
    (hm : ∀ κ, ((F.parameters κ).dimension + 1) * F.residueBits.eval κ + 2 * κ ≤ (F.parameters κ).samples)
    (D : NUPPT) : Negligible fun κ => distAdv (realView (ofFamily F κ) (F.noise κ) false)
      (realView (ofFamily F κ) (F.noise κ) true) (fun v r => D.distinguisherL κ (encodeView (ofFamily F κ) v) r)
-- A2. **Pure FHE**: IND-CPA of the bootstrapped scheme is (A1) [BV11, Thm 3.2; BV14, Thm 2.14 second part]. Thin.
theorem fheView_negligible (h : WeakCircularSecureFamily F) (D : NUPPT) : Negligible fun κ => …
-- A3. **Asymptotic IND-CPA of leveled GSW-FHE from DLWE** [BV14, Thm 3.7, p016-b001; BV11, Thm 3.1]: L5 at each κ,
-- `N·L(L+1)/2` level terms per side (polynomial), each `≤ 2·advantageAt D' κ + 2N·2^{-κ}`.
theorem leveledINDCPA_of_dlweAssumption (L : PolyExpr) (hF : LWE.DLWEAssumption F)
    (heff : LeveledReductionEfficient F L) (hm : …) (D : NUPPT) : Negligible fun κ => …
```

## H6. Noise and ratio ledger

| Quantity | Value | From |
|---|---|---|
| fresh public-key ciphertext (inputs, `evk`, level keys) | `m·B` | `encrypts_encrypt`, G11, L1 |
| selector step (permutation instruction) | `β_V + 2N·β` | G1 (`Encrypts.mul` ×2, `.add`), C6 |
| PBP of length `L` | `L·2N·β_evk` | G2 (C7) |
| formula of depth `d` | `4^d·2N·β_evk` | G3, C14 |
| bootstrapped NAND gate (pure and leveled) | `bootNoise = 4^{decDepth+1}·2N·m·B` | G8, G9 |
| decryption condition | `2·(ℓ·bootNoise) < ⌊q/2⌋` and `2·(ℓ·m·B) < ⌊q/2⌋` | `decrypt_of_encrypts` |
| draft depth target | `decDepth ≤ 9⌈log₂N⌉ + 2⌈log₂(ℓ+⌈log₂N⌉+3)⌉ + 21` | §H3.4, F10 |
| resulting ratio | `q/B > c·ℓ·m·N^{19}·(ℓ+⌈log₂N⌉+3)^4`, `c < 2^{70}` (draft): **polynomial** | G13, G16 |

The two key blocks of G7 double the formula's input count, not its depth, so the ledger is unchanged from r1. The
leveled scheme has the same per-gate bound, so one separation condition serves both schemes. The exponents are
large (BV14 says only "`c > c_dec` large enough"); they are polynomial, which is the claim.

## H7. Sequence, gates and units

**Order** (P6-Q1, location ruling):
1. **O1** (owner-side PR, proved): `TreeCircuit.balanced` into `FormulaArith/Combinators.lean`, `TreeNCAC`
   re-pointed. It lands first, like #332 before #333.
2. **6a statements**: an external Claude job (ruling of 2026-11-16) staged as an issue package from r2.
   - Drafts at the ruled paths, each module compiled with `scripts/lean_check_tree.sh`.
   - It also carries the registration in `ComputationalModels.lean`, the facades and the §14 rows (P6-Q17).
   - One statement PR stacked on O1.
3. **Gate 45** (Codex): the 6a statements and O1.
4. **6a fills** (proved-modulo): U1–U10 in parallel.
   - The **6b statements may overlap** Gate 45 and the 6a fills. They are drafted against the 6a statement PR,
     re-checked if Gate 45 changes a 6a signature, and frozen only after Gate 45 closes. O2 lands with or before
     the 6b statement PR.
5. **Gate 46** (Codex): the 6b statements and O2.
6. **6b fills**: U11–U18 in parallel, after Gate 46 and the merge of the phase-5 fills (#339, #338).

**Merge order:** phase-5 fills (combined build) → O1 → 6a statements → 6a fills → O2 → 6b statements → 6b fills.

**Gate 45 audits** (6a and O1):
- **The model.** General maps, `IsPermutation`, `yield` in program order (`yield_append`'s direction), BV14's
  instruction order against Bar89's (disclosed), and recognition by accepting sets (`BranchingProgramFamily`,
  `InBWBP`, `InPBP`) against Bar89 §1 (`p001-b002`, `p002-b001`).
- **The host contract.** Push-form `evalWith`, generic in selector and value type; the step-indexed `evalWith_rel`;
  C8 for general maps; C6 under `IsPermutation`. Also the §14 rows of P6-Q17.
- **Barrington Thm 1.**
  - The composition-order translation and Lemma 3 by kernel `decide`; the explicit conjugator (P6-Q13).
  - Lemma 2's last-instruction form, the OR case by De Morgan, and constants with `[NeZero n]`.
  - `length ≤ 4^depth`, and the `n = 0` case of C23 through the accepting set.
- **Thm 2.** The composition-tree formula against [Bar89, Thm 2 proof] section by section, the depth constants of
  C19 and C21, and the class route through `InTreeNC` (P6-Q18). The Corollary C25 against `p004-b004`.
- **NAND conversion.** `IsNAND`/`IsNANDForm` (P6-Q16), `nandGadget_correct` against `GadgetCorrect`'s cost and
  depth budget, the factor 2, the size bound, the not-`IsWellFormed` disclosure, and the `NAndCircuit` name clash.
- **Formula arithmetic.** Depth targets F5–F10 with no `Θ(ℓ)` term (§H3.3) and closed forms; F7's semantics
  through `carryBit`/`prefixVal_add`.
- **O1.** Byte comparison of the moved proofs; `toBinary`'s statements unchanged; no duplicate left behind.
- **Rule 10 seals.**
  - Circuits: `TreeCircuit.eval`/`depth`/`maxFanin` (through `eval_node_*_iff`, `depth_node`, `maxFanin_node`);
    `DAGGate.eval` (`eval_eq`); `DAGCircuit.eval`/`depth`; `runWith`; `rewrite` (its four lemmas);
    `toTree`/`toDAG` (their lemmas).
  - Classes and numbers: `Language.InNC`/`InTreeNC`; `bitsVal`/`prefixVal`/`carryBit`.
- **Registration and attribution.** `ComputationalModels.lean` entries and facades; every `[Bar89, …]` against the
  ingest anchors; glue tags for the NAND conversion and the host.

**Gate 46 audits** (6b and O2):
- **Noise ledger** re-derived by hand (§H6): the selector's `2Nβ` under `IsPermutation`, `4^d`, `bootNoise`, and
  `decDepth`'s closed form.
- **NAND-only bootstrapping** against [BV14, Def 2.13]: the two-key generalization, the `(a, a)` and `(G, G)`
  padding, the output coordinate `σ 0`, and the evaluation key of P6-Q8.
- **O2** as a proof: `decodeLo`/`decodeHi` and the interval reader.
- **Correctness.** Pure FHE for every depth (G10, G12), the conversion route (G18), and compactness by typing.
- **The leveled scheme** (P6-Q14). Key and evaluation-key shapes, vertex key indices, correctness for NAND
  circuits of depth `≤ L`, and the output level as public information (disclosed). The key hybrid's order and
  sum structure (L4, L5), with `distAdv_multi_le_sum`/`hybridPlant` and `abs_sub_le_sum_hybrids` reused.
- **Security hypotheses.**
  - `WeakCircularSecure`'s exact form (P6-Q15) and `WeakCircularSecureFamily` against [BV11, Defs 3.1, 3.8].
  - The A4 hypotheses: the exact quantifier structure, domination rather than construction, and the advice
    remark.
  - A1 and A3 from the unchanged `DLWEAssumption`.
- **Ratio** (P6-Q12). `RatioBounded`, `ofFamily` (type-level Rule 10: `(ofFamily F κ).lwe` against
  `F.parameters κ`), and `pBoot` explicit.
- **Rule 10 seals.**
  - Phase 5: `Encrypts`, `encrypt`, `decrypt`, `decomposeVec`, `reduction`, `realView`.
  - LWE and asymptotics: `decode`, `advantageAt`, `encodeChallenge`, `encodeMatrix`, `distinguisherL`.
  - 6a: `barrington`, `evalWith`, `toNANDForm`, `FormulaArith.*`.
- **No restatement:** 6b imports the 6a modules and restates none of them.

**Units.** Each fill unit owns its file(s), so units never share a file. Dependencies are on frozen statements only,
so under the proved-modulo rule every 6a unit can start once Gate 45 closes, and every 6b unit once Gate 46 closes.
Estimates are fill (proof) lines. In the "vs r1" column, *new* means new in r2, *changed* means re-scoped, and
*r1* means unchanged.

| Unit | File | Targets | Statements needed | Est. fill | vs r1 |
|---|---|---|---|---|---|
| O1 | owner PR: `FormulaArith/Combinators` (`balanced`), `TreeNCAC` | 4 (moved, proved) | — | ~170 moved | changed |
| U1 | `BranchingPrograms/Defs` | C1–C4 | — | 120–180 | changed |
| U2 | `BranchingPrograms/Eval` | C5–C8 | U1 | 150–230 | changed |
| U3 | `BranchingPrograms/Barrington` | C9–C16 | U1 | 360–520 | r1 (U2) |
| U4 | `BranchingPrograms/BarringtonConverse` | C17–C21 | U1, O1, U7 | 250–400 | **new** |
| U5 | `BranchingPrograms/NC1` | C22–C25 | U1, U3, U4 | 180–320 | changed |
| U6 | `CircuitComplexity/NANDForm` | N1–N6 | — | 150–250 | **new** |
| U7 | `FormulaArith/Combinators` | F1–F3 | O1 | 150–220 | r1 (U4) |
| U8 | `FormulaArith/CarrySave` | F5–F6 | U7 | 250–400 | r1 (U5) |
| U9 | `FormulaArith/Compare` | F7–F8 | U7 | 150–250 | r1 (U6, split) |
| U10 | `FormulaArith/ModSum` | F9–F10 | U7–U9 | 150–250 | r1 (U6, split) |
| O2 | owner PR: `LWE/BitEncoding` | G4 → `decode_iff_mem_Ico` | — | 60–90 (proved) | changed |
| U11 | `GSW/Branching` | G1–G3 | U2, U3 | 150–250 | r1 (U7) |
| U12 | `GSW/DecryptFormula` | G5–G8 | U7–U10, O2 | 200–330 | changed |
| U13 | `GSW/Bootstrap` | G9–G13, G18 | U6, U11, U12 | 280–440 | changed |
| U14 | `GSW/Circular` | G14–G15 | U13 | 60–120 | r1 (U10, part) |
| U15 | `GSW/Leveled` | L1–L3 | U13 | 200–330 | **new** |
| U16 | `GSW/LeveledSecurity` | L4–L5 | U15 | 250–400 | **new** |
| U17 | `LWE/Ratio`, `GSW/PolyRatio` | G16–G17 | U13, U15 | 140–220 | r1 (U10, part) |
| U18 | `GSW/Asymptotic` | A1–A3 | U14, U16, U17 | 150–280 | **new** |

**Totals.**

| | r1 | r2 |
|---|---|---|
| fill units | 10 (U1–U10) | 18 (6a: 10, 6b: 8) + owner PRs O1, O2 |
| target rows (lemmas) | 39 rows (about 55 lemmas) | 65 rows (about 95 lemmas): C 25, N 6, F 9, G 17, L 5, A 3 |
| fill lines, 6a | 1,350–2,080 (r1 U1–U6) | **1,910–3,020** |
| fill lines, 6b | 800–1,330 (r1 U7–U10) | **1,430–2,370** |
| fill lines, total | **2,150–3,400** | **3,340–5,390**, plus O1 (~170 moved) and O2 (60–90), both proved |
| statement surface | 1,700–2,000 lines in 13 files | about 2,800–3,300 lines in 19 files plus 2 facades |

The r2 growth is +1,190 to +1,990 fill lines:
- Thm 2 (U4, part of U5): +300–520, the ruling's +300–500;
- the leveled scheme (U15, U16): +450–730, the ruling's +400–700;
- the NAND conversion (U6, G18): +180–290;
- the general model and host (U1, U2): +120–190;
- the asymptotic forms (U18): +150–280.

Every math file stays below the 1,000-line split threshold. `Barrington.lean` is the largest, at about 550–720
lines filled; it exceeds the 600-line target only at the top of the range, for one structural induction whose cases
share local lemmas.

## H8. Risks

1. **Depth constants** (r1). A single `Θ(ℓ)` term in the decryption depth makes the ratio condition unsatisfiable
   (§H3.3). Gate 45 checks the closed forms, and no fill may introduce Shannon or DNF steps over `log q`-bit values.
2. **`decode` is an interval** (r1, now settled). `lo`/`hi` are fixed by O2 and checked by computation for
   `2 ≤ q < 300` against Mathlib's `valMinAbs` convention. O2's proof is the remaining work.
3. **Composition order** (r1). A wrong order still yields a five-cycle in Lemma 3, so C9 alone cannot catch it;
   C13's statement is the check, and §H3.6's computation is recorded for the gate.
4. **NAND form is not well-formed** (P6-Q16). `¬` gates of fan-in 2 violate `IsWellFormed`. Lemmas assuming it
   (`toTree_eval`, `deMorgan_*`, `binarize_*`) do not apply to NAND-form circuits; bootstrapping does not need them.
   The size bound `n + 4·#gates` is the generic `rewrite` bound, not the tight `3·#gates`.
5. **Name clash.** `BoolCircuit.NAndCircuit`/`TreeCircuit.toNAnd` (`Basic.lean:356/465`) are AND-rooted normal
   forms. The new names avoid `NAnd`, and the docstrings say so.
6. **Thm 2's circuit model** (P6-Q18). A formula has size `l^{O(log w)}`, polynomial for fixed `w`, which is all
   NC¹ needs. A gate-efficient DAG form would need relocation ledgers like `Adder.lean`'s. Reaching `DAGCircuit` adds
   one level (`toDAG_depth_le`).
7. **Constants and `n = 0`.** Thm 1 needs `[NeZero n]` (constant nodes read variable 0). The family statements
   handle `n = 0` through the accepting set. The decryption formula has `2N ≥ 1` inputs.
8. **Kernel `decide` on `Equiv.Perm (Fin 5)`.** Lemma 3 is cheap. The conjugator over all 24 × 24 pairs may be
   slow; the fallback states C10 over the explicit cycle structure. No `native_decide` (none remains in the
   library).
9. **Computability** (P6-Q13). `barrington` is defined by well-founded recursion on a nested inductive: computable,
   but not kernel-reducible, so `decide` is used only on closed `Fin 5` facts. `evalWith`'s `Finset` sums are
   computable. `toFormula` may be `noncomputable`.
10. **Worst case against probabilistic** (r1). BV14's Lemma 3.6 and Thm 3.7 are probabilistic; the formal versions
    are worst-case and lose polynomial factors. The public-key evaluation key costs one factor `m` (P6-Q8).
11. **Circular security** (r1, extended). Its truth for GSW is open [Pei16, §6.1.2]. In addition, the ruled
    concrete predicate quantifies over all function-level distinguishers, so it is satisfiable only for `ε` near
    `1` (P6-Q15). The asymptotic family predicate is the meaningful form.
12. **Leveled scheme** (P6-Q14, P6-Q19).
    - Wires of unequal depth force the all-lower-keys evaluation key (`N·L(L+1)/2` ciphertexts) or a layering
      conversion.
    - The output level is public information.
    - Each hybrid step's messages (lower keys' bits) are random. The multi-ciphertext lemma takes fixed messages,
      so the step conditions on the lower keys inside the reduction's coins. This is the longest proof of 6b,
      hence U16's estimate.
13. **Asymptotic statements.**
    - No `NUPPT`-bridge extension is needed (§H3.12). `BitPublicKeyScheme.SingleBitSecure` stays out of scope
      because it needs a machine-level GSW.
    - (A4) is a domination hypothesis. For the leveled form, one machine must dominate every `(d, j)`, which holds
      with advice (NUPPT advice picks the worst pair per `κ`); the docstring says so.
    - The view encodings are new definitions over `Encoding.Modular`. `ofFamily` raises the type-level Rule-10
      transport between `(ofFamily F κ).lwe` and `F.parameters κ`; the hypotheses are real-valued to avoid it, and
      `hm` is read through `ofFamily`'s `simps` readers.
14. **Unregistered hosts** (P6-Q17). The phase consumes `runWith` and `DAGCircuit.rewrite`, both public but missing
    from §14. Policy's "gate before a second consumer" is met only if Gate 45 audits their contracts.
15. **Private helpers** (r1). `combine` is promoted by O1. `Parity`'s dual-rail XOR stays private until the dedup
    queue; copying it would be duplication needing approval.
16. **Shared-file changes.** Each needs Seyoon's approval:
    - Lean: `ComputationalModels.lean` (models and conversions), `TreeNCAC.lean` (O1), `LWE/BitEncoding.lean` (O2),
      `TCSlib.lean`, and the `CircuitComplexity`, `LWE` and GSW facades.
    - Records: `machine-library-design.md` §14 and the gadget registry subsection.
17. **Source fidelity.** Disclosed deviations:
    - BV14's coordinate 1 against our `σ 0` (§H3.7);
    - two key blocks in the augmented formula (G7);
    - fan-in padding (§H3.9);
    - the carry-save tree (F5);
    - the reconstructed key chain (§H1 gap 1, P6-Q19).
18. **Scope and schedule.** Fill grows from 2.2–3.4k to 3.3–5.4k lines. 6a is independent of GSW and can land
    while 6b is drafted.

## H9. New questions (P6-Q14 to P6-Q19)

Multiple choice, recommended option first and marked **(rec.)**. These arise from the changed rulings. For Seyoon;
the maintainer moves them into `questions.md`.

**P6-Q14. Leveled scheme: wires of unequal depth** (§H3.11, §H5.13–H5.14)
- **A (rec.)** Keys indexed by vertex depth. The level-`d` evaluation key encrypts under `pk_d` the key bits of
  **every** lower key, and each gate is bootstrapped by the two-key `bootNAND` from its arguments' levels to its own
  level.
  - No layering conversion is needed, and the per-gate lemma is G9 itself.
  - The evaluation key has `N·L(L+1)/2` ciphertexts; it still depends only on `L` [BV11, Thm 3.1].
  - The hybrid replaces the evaluation keys from the top level down.
- **B** Consecutive keys only (`evk_d` encrypts `s_{d−1}`'s bits; `N·L` ciphertexts), as in the textbook chain.
  Circuits must be **layered**, so 6a gains a layering conversion that pads by double-NAND identity chains (about
  +150–250 lines, with parity care for odd gaps).
- **C** As B, but the leveled theorems take "layered" as a hypothesis and provide no conversion. Smallest, but
  general circuits are not covered.

**P6-Q15. The concrete `WeakCircularSecure`** (§H3.12, §H5.12)
- **A (rec.)** Per-distinguisher: `WeakCircularSecure P χ D ε := distAdv (fheView … false) (fheView … true) D ≤ ε`.
  The asymptotic `WeakCircularSecureFamily` (NUPPT, negligible) is the headline hypothesis, faithful to
  [BV11, Def 3.8], which is asymptotic. The ruled form over all function-level distinguishers holds only for `ε`
  near `1`, because an unbounded distinguisher recovers `s` from `pk` and decrypts.
- **B** Keep it as ruled (every distinguisher), with a docstring stating that it is meaningful only for `ε` near
  `1`, and rely on the asymptotic predicate for content.
- **C** A `(t, ε)` form over machines [BV11, Def 3.2, p013-b003]: NUPPT distinguishers of running time `≤ t` at a
  fixed `κ`. This needs a time measure at one security parameter, which the library does not expose yet; larger.

**P6-Q16. Representation of NAND form** (§H3.9, §H5.6)
- **A (rec.)** A predicate on `DAGCircuit`: every gate is a `¬` gate (negated conjunction) of fan-in `≤ 2`.
  - The conversion is an instance of `DAGCircuit.rewrite` with costs within its `fan-in + 2` budget and depth
    factor 2.
  - Bootstrapping pads fan-in 1 to `(a, a)` and fan-in 0 to `(G, G)`.
  - Disclosed: NAND-form circuits are not `IsWellFormed`.
- **B** Binary NAND only (`args.length = 2`, negation as `NAND(a, a)`). The constant `false` then needs three gates
  over an input vertex, above `GadgetCorrect`'s budget of 2 for fan-in 0. That requires an owner-side change to
  `DAGTransform.lean` (a general cost) and `n ≥ 1`.
- **C** A new NAND circuit model type, registered in `ComputationalModels.lean`. It is a second circuit model;
  phase-5 §G5 and P6-Q2 C rejected the same pattern.

**P6-Q17. Host registry rows** (§H2, §H4)
- **A (rec.)** Register `BranchingProgram.evalWith` as **H18**. Also record the two public, unregistered hosts the
  phase consumes: **H19** `runWith`/`runWith_rel` (`DAGCircuit.lean:149/625`) and **H20** `DAGCircuit.rewrite`
  (`DAGTransform.lean:246`). Gate 45 audits their contracts as listed. Records only; no Lean change.
- **B** Register only H18, and put `runWith` and `rewrite` on the registry backlog.

**P6-Q18. Thm 2's circuit model** (§H3.10, §H5.4)
- **A (rec.)** A `TreeCircuit` formula with fan-in 2 that mirrors Bar89's three sections. It reaches `DAGCircuit` and
  `Language.InNC 1` through `Language.InTreeNC.inNC`. Its size `l^{O(log w)}` is polynomial for fixed `w`.
- **B** A `DAGCircuit` built directly, sharing composition subcircuits (size `O(l·w³)`). That is closer to "a
  circuit", but needs vertex relocation ledgers (as in `Adder.lean`), about +200 lines.

**P6-Q19. Source for the leveled key chain** (§H1 gap 1)
- **A (rec.)** No new ingest.
  - Cite [BV11, Thm 3.1, Def 3.6] and [BV14, Thm 2.14 first part, Thm 3.7] for the statement, and [AP14, §5.3]
    for the independent-keys argument.
  - The docstrings disclose that the key-chain construction and its hybrid order are reconstructed: no ingested
    passage gives them.
- **B** Ingest the leveled-bootstrapping passage of Gentry's thesis or STOC 2009 paper ([Gen09], cited by BV11 and
  BV14), and cite it. This needs the PDF.

## H10. Not in this phase (recorded)

- Uniform `NC¹`/BWBP (Bar89 §6), width-4 circuits and the word problem (Bar89 abstract).
- A machine-level GSW (`BitPublicKeyScheme` instance) and a proof of (A4).
- The AP14 accumulator route, small-secret LWE and its ACPS09 equivalence (DW-6), modulus switching.
- Worst-case lattice approximation factors.
- Re-pointing `Parity.lean`'s dual-rail XOR (dedup queue).

## H11. Proposed plan rows (for the maintainer)

Phase table:

| Phase | Frozen surface to prepare | Fill starts only after |
|---|---|---|
| 6a | BP model and host; Barrington Thm 1, Thm 2; BWBP = NC¹; NAND form; formula arithmetic | Gate 45; O1 |
| 6b | PBP evaluation; decryption formula; NAND bootstrapping; pure/leveled FHE; security; ratio | Gate 46; O2; ph. 5 |

In the 6b row, "ph. 5" means that the phase-5 fills (#339, #338) are merged.

Decision-log row:

| Date | Decision/evidence | Status |
|---|---|---|
| 2026-11-16 | Phase-6 plan section r2, under rulings P6-Q1–Q13 and the location ruling. Records only. | Q14–Q19 open |

Detail for the row above: gates 45 (6a) and 46 (6b); units U1–U18 plus owner PRs O1 and O2; fill
3.3–5.4k lines (r1: 2.2–3.4k). Six new questions. The Bar89 ingest covers Thm 2 in full.
