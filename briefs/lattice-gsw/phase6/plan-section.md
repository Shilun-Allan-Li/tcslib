# Proposed plan section: GSW phase 6, bootstrapping to FHE with a polynomial modulus-to-noise ratio (BV14 route)

Proposed text for `LatticeCryptographyPlan.md`, prepared by the maintainer overnight under Seyoon's
authorization (`briefs/pass-shelat-ch5-8/overnight-2026-11-16.md`, item 7). The plan itself is not
edited. Everything here is design: no Lean was written and nothing was elaborated, so every
statement below is a sketch for the statement phase. Paths are relative to `TCSlib/` unless stated
otherwise.

Companion files:
- `questions.md`: the design questions for Seyoon, multiple choice, recommended option first
  (numbered P6-Q1 to P6-Q13 to keep them apart from the ruled phase-5 Q1–Q16).
- Sources: the DW-7 ingests under `blueprint/src/references/` (§H1). Citations below use
  `[TAG, location]` with the ingest file and anchor, e.g. [BV14, Thm 3.5] =
  `brakerski-vaikuntanathan-2014-fhe.md#pdf-eab2d1667a8e-p014-b001`.

---

## H0. Scope, numbering and ownership

**Goal.** Pure (non-leveled) fully homomorphic encryption from LWE with a **polynomial**
modulus-to-noise ratio, following [BV14, §3] and cross-checked against [AP14, §4–5]:

1. Barrington's theorem: a fan-in-2 AND/OR formula of depth `d` (negations at the inputs) is
   five-cycle recognized by a width-5 permutation branching program (PBP) of length at most `4^d`
   [Bar89, Thm 1, Lemmas 1–3; BV14, Thm 3.5]. A separate complexity-layer unit (ruling Q13).
2. Homomorphic evaluation of a PBP with GSW: one **selector step** per instruction,
   `V'_i = (G − C) ⊡ V_{π₀⁻¹ i} + C ⊡ V_{π₁⁻¹ i}`, which costs an **additive** `2Nβ` [BV14,
   Eq. (4)–(6), Lemma 3.6; AP14, Eq. (4.1), Lemma 4.1], so a length-`L` program adds `L·2Nβ`.
3. A decryption formula of depth `O(log N + log log q)` for public-key GSW's own decryption, built
   from a new shared formula-arithmetic layer [BV14, Prop 3.4; BV11, Lemma 4.5].
4. Bootstrapping: every gate of a circuit is evaluated by homomorphically evaluating its
   *augmented decryption formula* on an evaluation key that encrypts the secret-key bits under the
   same key [BV14, Def 2.13, Thm 2.14; BV11, Defs 3.7–3.8, Thms 3.1–3.2]. The output noise is a
   fixed bound independent of the circuit, so correctness holds for circuits of **every depth**.
5. Security: IND-CPA of the FHE view `(pk, evk, Enc(μ))` under an **explicit weak circular
   security hypothesis** [BV14, Thm 2.14 second part; BV11, Def 3.8; Pei16, §6.1.2; AP14, §5.3]
   (ruling Q15), never derived from LWE; and the polynomial-ratio regime stated with the ratio
   predicate of ruling Q16.

**Numbering.** The phase-5 roadmap (`plan-section.md` §G9) split this into phase 6 (generic
bootstrapping, quasi-polynomial ratio) and phase 7 (BV14, polynomial ratio). On the BV14 route the
quasi-polynomial instantiation is subsumed, and both phases need the same decryption circuit, so
this plan treats them as **one phase 6** with two gates (6a complexity, 6b cryptography). P6-Q1 asks
Seyoon to confirm.

**Assumptions** (as recorded in phase 5, §G9):
- (A1) weak circular security of public-key GSW for its own key bits: an explicit hypothesis;
- (A2) DLWE for a family whose ratio `q/B` is polynomially bounded (Q16);
- (A3) small-secret LWE is **not** needed: the BV14 route works with the existing uniform-secret
  `LWE.DLWEAssumption` (rulings addendum: A3 is assumed only where used; here it is unused).

**In scope:** items 1–5; the `DAGCircuit` and `NC¹` corollaries of Barrington (one direction,
P6-Q3); a key-switching form of the bootstrapping lemma (so a leveled key chain is a short
corollary, P6-Q11).

**Out of scope (unchanged plan exclusions):** Gaussian or subgaussian noise, the randomization
procedure `Rand` [BV14, §2.4], randomized `G⁻¹` [AP14, Claim 3.1], worst-case lattice reductions and
approximation factors ([BV14, Thm 1.1, Cor 4.5], [AP14, Thm 5.1] are context only),
dimension-modulus reduction [BV14, §4; BV11], machine efficiency of `Eval` and the `NUPPT` bridge
(as for phase 5, Q8), Barrington's converse [Bar89, Thm 2] unless P6-Q3 says otherwise, and the AP14
accumulator route (ruling Q12).

**Ownership.** The maintainer runs the phase on `cryptography/pass-shelat-ch2-4`. Lean changes go
by PR; Seyoon approves and merges. Codex audits (standing ruling); Claude fills; Seyoon dispatches.

## H1. Sources (DW-7 ingests)

| Tag | Ingest key (`blueprint/src/references/`) | Version | SHA-256 of the upload | Passages ingested |
|---|---|---|---|---|
| BV14 | `brakerski-vaikuntanathan-2014-fhe` | ePrint 2013/541, PDF of 28 Aug 2013, 21 pp. | `eab2d166…12ca` | fn. 1, Thm 1.1, §2.3, §2.5 (Defs 2.12–2.13, Thm 2.14), all of §3 (NCCrypt, Def 3.1, Lemmas 3.2–3.3, Prop 3.4, Claims 3.4.1–3.4.2, PBPs, Eq. (4)–(6), Thm 3.5, Lemma 3.6, Thm 3.7), Lemma 4.4, Cor 4.5 |
| Bar89 | `barrington-1989-bounded-width-bp` | JCSS 38(1):150–164, 1989; 15-page scan, no text layer | `06fd3eec…7831` | abstract, §1, §3 (Thm 1, Lemmas 1–3, example, proof, Thm 2, Corollary); read from page images |
| BV11 | `brakerski-vaikuntanathan-2011-fhe` | FOCS 2011 full version, 39 pp. | `d3e95f9b…0b00` | §3.1 (Defs 3.1–3.6), §3.2 (Def 3.7, Thms 3.1–3.2, Def 3.8, Lemma 3.3), §4.5 (Lemma 4.5 and proof, Lemma 4.6, Cor 4.7) |
| AP14 | `alperin-sheriff-peikert-2014-bootstrapping` | ePrint 2014/094, 13 June 2014, 18 pp. | `cecd346d…c0da` | §2.2, §3, §4.1–4.2, §5.1–5.3 (spec, procedures, Thm 5.1, security, Lemma 5.2) |
| GSW13 | `gentry-sahai-waters-2013-fhe` | ePrint 2013/340, 8 June 2013, 25 pp. | `8edb94cf…bf00` | §1.2 bootstrapping remark, §1.3.1–1.3.4, §2.3, §3.1–3.4 |
| Pei16 | `peikert2016-lattice-survey` (extended) | 17 Feb 2016 | `1a9802b6…7488` | added §5.4.3 (gadgets), §6.1.2, §6.1.3 |
| AB09 | already cited by `DAGCircuit.lean`, `NCAC.lean` | — | — | Defs 6.1, 6.24 |

All SHA-256 values were recomputed from the uploads and match the values in the phase-5 plan, the
rulings addendum and `PairingCryptographyPlan.md`. The PDFs are not committed (DW-7). Each ingest
is a scoped raw file (`.raw.md`, `pdftotext -layout` line ranges; Bar89 a reading of the page
images) plus a LaTeX transcription (`.md`) with proofmatch anchors; the tags are registered in
`sources.json`. Matching against the blueprint waits for an approved proofmatch run, as before.

**Two record points found while ingesting** (for the maintainer; nothing here edits them):
1. BV14's "[BV11, Lemma 4.1]" (Prop 3.4) is **Lemma 4.5** in the BV11 version we hold; Lean
   docstrings should cite [BV11, Lemma 4.5] and note BV14's numbering.
2. (Pairings) The BB04 page images show absolute values in §2.1's advantage, in §3.1's Decision
   BDH advantage and in the proof of Thm 4.1. `PairingCryptographyPlan.md`, "Where the papers'
   formulations differ", item 6, says §3.1 is written without one; that sentence should be
   corrected (the draft's signed form stays a disclosed deviation).

**Anchors used below:**
- BV14: Def 2.13 `p008-b002`; Thm 2.14 `p008-b003`; NCCrypt `p009-b001`; Def 3.1, Lemma 3.2
  `p009-b002`; Prop 3.4 `p011-b001`; Claims 3.4.1–3.4.2 `p011-b002`, `p012-b001/2`; PBPs, Eq. (4)
  `p013-b002`; Thm 3.5 `p014-b001`; Eval, Eq. (5)–(6) `p014-b002`; Lemma 3.6 `p015-b001/2`;
  Thm 3.7 `p016-b001`; Lemma 4.4 (evk = encryptions of key bits) `p019-b001`; key-size remark
  `p020-b001`.
- Bar89: §1 `p001-b002`, `p002-b001`; five-cycle recognition `p003-b001`; Thm 1 `p003-b002`;
  Lemmas 1–3 `p003-b003..b005`; example `p004-b001`; proof of Thm 1 `p004-b002`; Thm 2 `p004-b003`;
  Corollary `p004-b004`.
- BV11: Defs 3.3–3.6 `p013-b004`, `p014-b001`; Def 3.7 `p014-b002`; Thms 3.1–3.2, Def 3.8
  `p015-b001`; Lemma 4.5 `p029-b001/2`.
- AP14: permutation matrices `p007-b001`; Lemma 3.5 `p010-b001`; chains, Cor 3.6 `p010-b003`;
  Eq. (4.1) `p011-b001`; Lemma 4.1 `p012-b001`; Cor 4.2 `p012-b002`; §5.1 `p013-b001`,
  `p014-b001`; §5.3 security `p015-b002`.
- Pei16: §6.1.2 `p068-b001`; Eq. (6.1.6) `p069-b001`; §6.1.3 bootstrapping `p070-b001`.

## H2. What the existing Lean already provides

**Phase 5 (`AdvancedEncryption/Homomorphic/GSW/*`, statements merged in #333; gsw-core fill
delivered and under review, gsw-security running).** Phase 6 cites frozen statements under the
proved-modulo rule; it merges after the phase-5 fills.

| Need | Existing declaration | Note |
|---|---|---|
| key-agnostic noise invariant | `Encrypts P t x β C` (`Noise.lean`) | shared by public-key, secret-key, evaluated ciphertexts; the evaluation key needs no new invariant |
| asymmetric product | `Encrypts.mul`: noise `N·β₁ + \|x₁\|·β₂` | **the hook**: the exact `\|x₁\|·β₂` term makes a selector step cost `2Nβ + β_V`; replacing both products by `mul_bit` would double the accumulated bound (Gate 41, roadmap section) |
| complement `G − C` | `encrypts_gadget`, `Encrypts.sub` | `G − C` encrypts `1 − x` with the noise of `C` [BV14, p014-b002 "C̄_k := I − C_k"] |
| sums, zero | `Encrypts.add`, `.sum`, `encrypts_zero` | one-hot state vectors |
| decryptability | `decrypt_of_encrypts`: `2·(ℓ·β) < ⌊q/2⌋` | used for every wire |
| `G·G⁻¹(u) = u` | `gadget_mulVec_decomposeVec` | turns decryption into a binary subset sum (§H3) |
| fresh noise | `encrypts_encrypt`, `encrypts_keygen_encrypt` (`m·B`) | evaluation key and inputs |
| circuit host | `runWith`, `runWith_rel` (#332), `DAGCircuit` readers | gate-by-gate bootstrapped evaluation |
| IND-CPA without `evk` | `distAdv_encrypt_le` (two DLWE + `2Nε`) | the circular-free part of the FHE view |

**Complexity layer (checked for reuse; no branching-program material exists).**

| Need | Existing | Use |
|---|---|---|
| formulas with negated literals (Barrington's model) | `BoolCircuit.TreeCircuit n` (`CircuitComplexity/Basic.lean`): `lit`, unbounded `node`; `eval`, `depth`, `maxFanin` with `depth_node`, `maxFanin_node`, `eval_node_*_iff` | Barrington's input and the decryption formula |
| DAG → formula | `DAGCircuit.toTree` with `toTree_eval`, `toTree_depth_le`, `toTree_maxFanin_le` (`TreeDAG.lean`) | `DAGCircuit` and `NC¹` corollaries |
| `NC¹` | `Language.InNC`, `DAGCircuitFamily.HasFaninTwo`/`HasPolylogDepth` (`NCAC.lean`) | Bar89 Corollary, one direction |
| balanced fan-in-2 gate over a list | `combine` (**private** in `TreeNCAC.lean`, depth `maxDepth + ⌈log₂ k⌉ + 1`) | must be promoted, not copied (policy §1, P6-Q6) |
| dual-rail XOR formula | `xorNode`, `IsDual` (**private** in `Parity.lean`) | superseded by a public `TreeCircuit.neg`; harvest on the dedup queue (P6-Q6) |
| little-endian value of a bit list | `BoolCircuit.bitsVal` (`Adder.lean`) | value of formula-numbers |
| ripple-carry adder (DAG) | `fullAdderGates`, `adderGates` (`Adder.lean`) | not used: linear depth; noted for the registry |
| permutations | Mathlib `Equiv.Perm (Fin 5)`, `cycleType`, `isConj_iff_cycleType_eq` | Lemmas 1 and 3 |

## H3. Design

**H3.1 The pipeline.** For a gate `g` (kind `∧`/`∨`/`¬`, fan-in ≤ 2) whose input wires carry
ciphertexts `C_a`:

```
augFormula P g (C_a)  : TreeCircuit N         -- g applied to the decryption formulas, inputs = key bits
barrington (augFormula …) σ  : 5-PBP, length ≤ 4^(depth)   -- complexity layer
homEvalPBP P (that PBP) evk : Fin 5 → Ciphertext P          -- selector steps, noise L·2N·β_evk
bootGate P evk g (C_a) := (homEvalPBP …) (σ 0)              -- the coordinate that encrypts g(Dec(C_a))
fheEval P evk Cc cts := runWith (bootGate P evk) Cc.gates …  -- every gate bootstrapped
```

The bootstrapped output noise `bootNoise P β_evk = 4^(decDepth P + 1) · (2N · β_evk)` does not
depend on the input noise, so one invariant ("encrypts its wire value with noise ≤ β*", with
`2·(ℓ·β*) < ⌊q/2⌋`) carries through a circuit of any depth by `runWith_rel`.

**H3.2 Decryption as a binary modular subset sum.** Phase-5 decryption reads the public column
`c = C·G⁻¹(⌊q/2⌋·e_{n+1})` and outputs `decode(⟨t, c⟩)` with `t = (−s, 1)`. With
`x = G⁻¹(t) ∈ {0,1}^N` (so `G·x = t`, `gadget_mulVec_decomposeVec`),

```
⟨t, c⟩ = ⟨G x, c⟩ = Σ_{i<N} x_i · a_i (mod q),   a = Gᵀ c  (public: depends only on C).
```

So the decryption function of `C`, as a function of the key bits `x`, is
`x ↦ decode((Σ x_i a_i) mod q)`. This is [AP14, §5.1]'s "s = Gᵗ s̄, c binary" with the roles of key
and ciphertext exchanged, and it is the inner-product-plus-rounding of [BV11, Lemma 4.5]. The key
bits `x = keyBits P s := decomposeVec P (secretVector P s)` are what the evaluation key encrypts
(P6-Q8).

**H3.3 Why the depth must be `O(log N + log log q)` with no term linear in `ℓ`.** The
bootstrapped noise is `4^d·2Nβ_evk` and must stay below about `q/(4ℓ)`. A formula whose depth has a
term `c·ℓ` (`ℓ = ⌈log₂ q⌉`) contributes `4^{cℓ} ≥ q^{2c}`, which no modulus satisfies. Hence:
- generic "any function of `b` bits" constructions (Shannon expansion, `dnfDAG`) may not be applied
  to `Θ(log q)`-bit values;
- the rounding must use that `decode` is an **interval** test: `decode v ↔ v ∈ [lo, hi)` for
  explicit `lo, hi` (from `h = ⌊q/2⌋`: `lo = ⌊h/2⌋ + 1`, `hi = ⌈(q+h)/2⌉`, to be checked against
  `LWE.BitEncoding.distance` at the statement phase; P6-Q7);
- `S = Σ x_i a_i < N·q`, so `S mod q ∈ [lo, hi)` iff `⋁_{j<N} (jq + lo ≤ S < jq + hi)`: an OR of
  `N` two-sided comparisons with constants, each of depth `O(log b)`, `b = ℓ + ⌈log₂ N⌉ + 1`
  (this replaces BV11's "subtract all multiples of `p` in parallel and select").

**H3.4 The formula-arithmetic construction** (P6-Q5): numbers are little-endian lists of formulas
with value `bitsVal (map eval)`;
1. masked constants `x_i · a_i` (a literal or a constant per bit);
2. a carry-save (3:2) reduction tree to two numbers `U, W` with `U + W = S`: each level is one
   `xor3`/`maj3` layer, depth +4, about `log_{3/2} N` levels;
3. `U + W ≥ c` as the carry-out of `U + W + (2^b − c)` (one more 3:2 layer, then a
   generate/propagate carry-out formula of depth `2⌈log₂(b+2)⌉ + 2`);
4. the interval and the OR over `j < N` with balanced fan-in-2 nodes.

Negation is the depth-preserving De Morgan map `TreeCircuit.neg` (negations end at literals, as
Barrington's model requires). Draft depth target (masked constants 1, carry-save levels `4·(2⌈log₂N⌉+3)`, comparison
`4 + 2⌈log₂(b+2)⌉ + 2`, interval 1, OR over `j` `⌈log₂N⌉ + 1`; constants fixed at the statement
phase by hand and by small `decide` checks): `decDepth N ℓ ≤ 9·⌈log₂ N⌉ + 2·⌈log₂(ℓ + ⌈log₂ N⌉ + 3)⌉ + 21`.

**H3.5 The selector step and the PBP host.** BV14 multiplies the evaluated ciphertext on the left
and the fresh one on the right; phase 5 uses AP14's orientation, so the fresh selector goes on the
**left** (Gate 41: "fresh ciphertexts belong on the left"). For an instruction
`⟨j, π₀, π₁⟩` (π₀ when `x_j = 0`, BV14's order) and state ciphertexts `V : Fin w → Ciphertext P`:

```
select P C U V := mul P (gadget P − C) U + mul P C V
step V := fun i => select P (cts j) (V (π₀.symm i)) (V (π₁.symm i))
```

If `C` encrypts the bit `b` with noise `β` and `U, V` encrypt bits with noise `≤ β_V`, then
`select` encrypts `(1−b)·u + b·v` with noise `N·β + (1−b)·β_V + N·β + b·β_V = β_V + 2Nβ`
(`Encrypts.mul` twice, `Encrypts.add`). Starting from `V₀ = (G at s₀, 0 elsewhere)` (zero noise;
AP14's "include `G` as the rightmost ciphertext"), after `L` instructions every coordinate encrypts
the one-hot state with noise `L·2Nβ` [worst-case form of BV14, Lemma 3.6]. The fold over
instructions is a **host** (an interpreter of PBPs; policy "Hosts come first"): it is published in
the branching-program layer, generic in the selector and the value type, with a relational lemma,
and both the Boolean semantics and GSW consume it (P6-Q4).

**H3.6 Composition order.** Bar89 writes products left to right (the leftmost permutation acts
first: `(12345)(13542)(54321)(24531) = (13254)` holds only in that reading; right to left it is
`(14352)`, also a five-cycle — checked by computation and recorded in the Bar89 ingest). Mathlib's
`Equiv.Perm` product applies the right factor first. The model fixes **program order**: the first
instruction acts first, `yield (B₁ ++ B₂) x = yield B₂ x * yield B₁ x`. The AND step then yields
`σ₂⁻¹ * σ₁⁻¹ * σ₂ * σ₁` (Mathlib order), which is Bar89's `σ₁σ₂σ₁⁻¹σ₂⁻¹`; docstrings state the
translation.

**H3.7 Output convention.** With five-cycle recognition (`yield = σ` on `A`, `1` off `A`) and start
state `0`, the final state is `σ 0 ≠ 0` on `A` and `0` off `A`. The output ciphertext is coordinate
`σ 0`. BV14 outputs coordinate 1 ("the output of the computation is 1 if ζ_L = 1"), so with
five-cycle recognition its program would have to recognize the complement of the true set; reading
`σ 0` avoids that step (a disclosed, harmless deviation).

**H3.8 Evaluation key** (P6-Q8). Recommended: public-key GSW encryptions of the `N` key bits under
the user's own `pk`, `evk_i = encrypt P pk (keyBits P s i) R_i`, noise `m·B` by
`encrypts_encrypt`. This is BV11's Def 3.8 literally (`{Enc_pk(sk[i])}_i`) and keeps one
`GSW.Parameters` record. BV14 uses secret-key encryptions (noise `B`, [BV14, Lemma 4.4]); that is a
factor-`m` improvement in the ratio but needs a second parameter record for the batched
secret-key LWE sample (the type-level Rule-10 issue that phase 5 avoided).

## H4. Definitions needed

**Complexity layer** (namespaces: model type at root, registered; operations in its namespace):
- `PermInstr w n` (structure: `var : Fin n`, `perm0 perm1 : Equiv.Perm (Fin w)`), `PermInstr.perm`
  (`= if x var then perm1 else perm0`).
- `PermBranchingProgram w n` (root, registered in `ComputationalModels.lean`): a list of
  instructions; `length`, `append`, `yield`, `run` (`yield x s`), `mapPerm` (apply a monoid hom to
  every permutation; conjugation), `complementLast` (Bar89 Lemma 2).
- `IsFiveCycle σ` (`σ.cycleType = {5}`), `FiveCycleRecognizes B A σ`.
- Host: `PermBranchingProgram.evalWith (sel : β → α → α → α) (inp : Fin n → β) B (V : Fin w → α)`.
- `sigma1`, `sigma2` (Bar89 Lemma 3, 0-based: `(0 1 2 3 4)`, `(0 2 4 3 1)`), `barrington c σ`.
- Formula layer: `TreeCircuit.neg`, `TreeCircuit.subst`, `TreeCircuit.const`, `and2`, `or2`,
  `xor2`, `xor3`, `maj3`, `TreeCircuit.balanced` (the promoted `combine`), `FNum n`
  (`List (TreeCircuit n)`), `FNum.val`, `csaStep`, `csaReduce`, `carryOut`, `geConst`,
  `modSumInterval`, `modSumDepth`.

**Cryptography layer:**
- `GSW.select`, `GSW.homEvalPBP`, `GSW.homEvalFormula`.
- `GSW.keyBits`, `GSW.decConstants`, `GSW.decInterval` (`lo`, `hi`), `GSW.decryptFormula`,
  `GSW.augFormula`, `GSW.decDepth`.
- `GSW.bootNoise`, `GSW.bootGate`, `GSW.fheEval`, `GSW.evalKey`.
- `GSW.fheView`, `GSW.WeakCircularSecure`.
- `LWE.Family.RatioBounded F B p` (Q16), `GSW.Parameters.ofFamily`.

Every definition lands with its readers (`_eq`/`_apply`/`_iff`, non-simp `simps` for structures),
per the definitions-land-with-lemmas rule.

## H5. Modules and statements

Sizes estimate **fill** lines. "Target" = a `sorry` statement at the gate. Statements are sketches.

### H5.1 `Complexity/BranchingPrograms/Basic.lean` (new topic; facade `Complexity/BranchingPrograms.lean`)

| # | Statement (sketch) | Source | Fill |
|---|---|---|---|
| C1 | `yield_append : (B₁ ++ B₂).yield x = B₂.yield x * B₁.yield x` | Bar89 §1 (`p001-b002`), program order | 15 |
| C2 | `length_append`, `yield_mapPerm : (B.mapPerm f).yield x = f (B.yield x)` | Bar89 Lemma 1 proof | 25 |
| C3 | `evalWith_rel` (relational, step-indexed ledger: `R 0 V W` and a per-instruction step lemma give `R B.length (evalWith … V) (evalWith … W)`) | host; glue | 60 |
| C4 | `evalWith_bool : evalWith boolSel x B (onehot s₀) = onehot (B.run x s₀)` | BV14 Eq. (4) (`p013-b002`) | 50 |

### H5.2 `Complexity/BranchingPrograms/Barrington.lean`

| # | Statement (sketch) | Source | Fill |
|---|---|---|---|
| C5 | `isFiveCycle_commutator : IsFiveCycle (sigma2⁻¹ * sigma1⁻¹ * sigma2 * sigma1)` (`decide`) | Bar89 Lemma 3 (`p003-b005`) | 10 |
| C6 | `FiveCycleRecognizes.conj : … B A σ → IsFiveCycle τ → ∃ θ, FiveCycleRecognizes (B.mapPerm (conj θ)) A τ` (explicit θ: `θ (σᵏ 0) = τᵏ 0`) | Bar89 Lemma 1 (`p003-b003`) | 60 |
| C7 | `FiveCycleRecognizes.complement : … B A σ → 0 < B.length → FiveCycleRecognizes (B.complementLast σ) (! A ·) σ⁻¹`, length preserved | Bar89 Lemma 2 (`p003-b004`) | 40 |
| C8 | **`barrington_recognizes`**: `c.maxFanin ≤ 2 → IsFiveCycle σ → [NeZero n] → FiveCycleRecognizes (barrington c σ) c.eval σ` | Bar89 Thm 1 and proof (`p003-b002`, `p004-b002`); BV14 Thm 3.5 | 200 |
| C9 | **`barrington_length_le`**: `(barrington c σ).length ≤ 4 ^ c.depth` | Bar89 Thm 1 | 60 |
| C10 | `barrington_run : (barrington c σ).run x 0 = if c.eval x then σ 0 else 0` | BV14 Thm 3.5 form, §H3.7 | 20 |

Cases of `barrington`: literal (one instruction), constant node (`⟨0, σ, σ⟩` or `⟨0, 1, 1⟩`; needs
`n ≥ 1`), fan-in-1 node (the child), `∧` (commutator of children with outputs `σ₁, σ₂, σ₁⁻¹, σ₂⁻¹`
conjugated to `σ`), `∨` (De Morgan: complement both children, `∧`, complement; Bar89's "appeal to
Lemma 2" made explicit, as the Bar89 ingest notes).

### H5.3 `Complexity/BranchingPrograms/NC1.lean` (P6-Q3)

| # | Statement (sketch) | Source | Fill |
|---|---|---|---|
| C11 | `DAGCircuit.exists_permBranchingProgram : C.IsWellFormed → C.IsFaninTwo → [NeZero n] → ∃ B : PermBranchingProgram 5 n, B.length ≤ 4 ^ C.depth ∧ ∀ x, (B.run x 0 ≠ 0 ↔ C.eval x = true)` | BV14 Thm 3.5; via `toTree` | 40 |
| C12 | `Language.InNC.exists_polyLength_pbp : L.InNC 1 → ∃ (Bₙ) 5-PBP family of polynomial length recognizing L` | Bar89 Corollary (`p004-b004`), one direction | 100 |

### H5.4 `Complexity/CircuitComplexity/FormulaArith/{Combinators,CarrySave,Compare,ModSum}.lean` (P6-Q5, P6-Q6)

| # | Statement (sketch) | Source | Fill |
|---|---|---|---|
| F1 | `neg_eval : c.neg.eval x = !c.eval x`; `depth_neg`; `maxFanin_neg` | glue (De Morgan) | 40 |
| F2 | `subst_eval`, `depth_subst_le : (c.subst f).depth ≤ c.depth + ⨆ (f i).depth`, `maxFanin_subst_le` | glue | 60 |
| F3 | gadget lemmas: `and2/or2/xor2/xor3/maj3` eval, depth (+1, +1, +2, +4, +3), fan-in ≤ 2 | glue | 70 |
| F4 | `balanced_eval`, `depth_balanced_le : ≤ maxDepth cs + ⌈log₂ \|cs\|⌉ + 1`, fan-in ≤ 2 (promoted `combine`) | AB09 p. 118 (as `TreeNCAC`) | 30 (move) |
| F5 | `csaStep_val : val A + val B + val C = val S + val K` under the width invariant; depth +4 | BV11 Lemma 4.5 proof ("summation … in depth O(log k + log log p)"); deviation: carry-save tree | 90 |
| F6 | `csaReduce_val`, `depth_csaReduce_le : ≤ 4·csaLevels k + d₀`, `csaLevels_le : ≤ 2⌈log₂ k⌉ + 3` | as F5 | 160 |
| F7 | `carryOut_eval : (carryOut U W).eval x = decide (2^b ≤ U.val x + W.val x)`; depth `2⌈log₂(b+1)⌉ + 2` | glue | 100 |
| F8 | `geConst_eval : … = decide (c ≤ U.val x + W.val x)`; depth | glue | 60 |
| F9 | **`modSumInterval_eval`**: `(modSumInterval a q lo hi).eval x = decide (lo ≤ (∑ i, (x i).toNat * a i) % q ∧ (∑ …) % q < hi)` for `lo ≤ hi ≤ q`, `a i < q` | BV11 Lemma 4.5 (`p029-b001/2`); BV14 Prop 3.4 | 120 |
| F10 | **`depth_modSumInterval_le`** `≤ modSumDepth M q`, `modSumDepth_le` (closed form of §H3.4), `maxFanin_modSumInterval_le : ≤ 2` | as F9 | 80 |

### H5.5 `AdvancedEncryption/Homomorphic/GSW/Branching.lean`

| # | Statement (sketch) | Source | Fill |
|---|---|---|---|
| G1 | **`Encrypts.select`**: `Encrypts P t b β C → Encrypts P t u β_V U → Encrypts P t v β_V V → (bits) → Encrypts P t ((1−b)u + b v) (β_V + 2·(N·β)) (select P C U V)` | BV14 Eq. (5)–(6), Lemma 3.6 proof (`p014-b002`, `p015-b002`), mirrored; AP14 Eq. (4.1), Lemma 4.1 | 50 |
| G2 | **`encrypts_homEvalPBP`**: inputs encrypt `x` with noise `β` ⇒ `∀ i, Encrypts P t (decide (B.run x s₀ = i)).toNat (B.length·(2·(N·β))) (homEvalPBP P B cts s₀ i)` | BV14 Lemma 3.6 (`p015-b001`), worst-case | 70 |
| G3 | **`encrypts_homEvalFormula`**: `c.maxFanin ≤ 2` ⇒ `Encrypts P t (c.eval x).toNat (4^c.depth·(2·(N·β))) (homEvalFormula P c cts)` | BV14 Thm 3.5 + Lemma 3.6; Pei16 §6.1.3 bootstrapping (`p070-b001`) | 40 |

### H5.6 `AdvancedEncryption/Homomorphic/GSW/DecryptFormula.lean`

| # | Statement (sketch) | Source | Fill |
|---|---|---|---|
| G4 | `decode_iff_mem_Ico : decode P v ↔ lo ≤ v.val ∧ v.val < hi` (home: P6-Q7) | glue for GSW13 §3.1 Dec | 60 |
| G5 | `vecMul_secretVector_eq_sum : ⟨secretVector P s, c⟩ = ∑ i, (keyBits P s i).toNat • (Gᵀ c) i` | AP14 §5.1 (`p014-b001`); Pei16 §5.4.3 | 50 |
| G6 | **`decryptFormula_eval`**: `(decryptFormula P C).eval (keyBits P s) = decrypt P s C` | BV14 Def 2.13, Prop 3.4; BV11 Lemma 4.5 | 60 |
| G7 | `augFormula_eval : (augFormula P g Cs).eval (keyBits P s) = g.eval (Cs.map (decrypt P s))` (fan-in ≤ 2 gates; `¬` by `neg`) | BV14 Def 2.13 (`p008-b002`) generalized from NAND (P6-Q9) | 40 |
| G8 | `depth_augFormula_le : ≤ decDepth P + 1`; `maxFanin_augFormula_le : ≤ 2`; `decDepth_le` closed form | BV14 Lemma 4.4 ("depth c_dec·log(…) + 1") | 50 |

### H5.7 `AdvancedEncryption/Homomorphic/GSW/Bootstrap.lean`

| # | Statement (sketch) | Source | Fill |
|---|---|---|---|
| G9 | **`encrypts_bootGate`** (key-switching form): `evk` encrypts `keyBits P s` under `t'` with noise `βk`, `g.args.length ≤ 2` ⇒ `Encrypts P t' (g.eval (Cs.map (decrypt P s))).toNat (bootNoise P βk) (bootGate P evk g Cs)` | BV14 Thm 2.14, Lemma 4.4; BV11 Thm 3.1 | 50 |
| G10 | **`decrypt_fheEval`** (pure FHE correctness): `evk` encrypts `keyBits P s` under `t = secretVector P s` with noise `βk`; inputs encrypt `x` with noise `βin`; fan-in ≤ 2; `2·(ℓ·βin) < ⌊q/2⌋`; `2·(ℓ·bootNoise P βk) < ⌊q/2⌋` ⇒ `decrypt P s (fheEval P evk Cc cts) = Cc.eval x`, **for every depth** | BV14 Thm 2.14 second part; BV11 Thm 3.2, Def 3.5 | 120 |
| G11 | `encrypts_evalKey : … Encrypts P (secretVector P s) (keyBits P s i).toNat (m·B) (evalKey P pk s R i)` | BV11 Def 3.8 (`p015-b001`); BV14 Lemma 4.4 | 20 |
| G12 | **`decrypt_keygen_fheEval`**: honest `Regev.keygen`, `χ.Bounded B`, `evalKey`, fresh inputs, `2·(ℓ·bootNoise P (m·B)) < ⌊q/2⌋` ⇒ correct for every circuit | BV14 Thm 3.7 (worst-case, any depth) | 40 |
| G13 | `bootNoise_le : bootNoise P β ≤ 4^c₀ · N^{2c₁+1} · (ℓ + ⌈log₂ N⌉ + 3)^{2c₂} · 2β` (closed form from `decDepth_le`) | glue | 40 |

Compactness [BV14, Def 2.12; BV11, Def 3.4] holds by typing (`fheEval` returns a `Ciphertext P`
whatever the circuit); it is recorded in the docstring, with no separate theorem (P6-Q10, option C
would add an encoded-length statement).

### H5.8 `AdvancedEncryption/Homomorphic/GSW/Circular.lean`

| # | Statement (sketch) | Source | Fill |
|---|---|---|---|
| — | `fheView P χ μ r := (pk, evalKey P pk s R', encrypt P pk μ R)` with readers | BV14 §2.5 ("adversary is given both pk and evk") | — |
| — | `WeakCircularSecure P χ ε : Prop := ∀ D, distAdv (fheView P χ false) (fheView P χ true) D ≤ ε`, `_iff` | BV11 Def 3.8; BV14 Thm 2.14; Pei16 §6.1.2 (`p068-b001`) | — |
| G14 | `distAdv_fheView_le (h : WeakCircularSecure P χ ε) : distAdv … D ≤ ε` | BV11 Thm 3.2 (security half) | 10 |
| G15 | `distAdv_fheView_noEvk_le`: dropping `evk`, the view is the phase-5 view and inherits `distAdv_encrypt_le` (two DLWE + `2Nε`) | GSW13 §3.2; AP14 §5.3 ("if keys are independent") | 40 |

The security content of pure FHE *is* the circular hypothesis (Pei16 §6.1.2: "it is unknown whether
it is provably secure"). G14 is deliberately thin; the plan does not claim more. G15 records what
LWE alone gives.

### H5.9 `Cryptography/LWE/Ratio.lean` and `AdvancedEncryption/Homomorphic/GSW/PolyRatio.lean`

| # | Statement (sketch) | Source | Fill |
|---|---|---|---|
| — | `LWE.Family.RatioBounded F B p : Prop := ∀ κ, (F.noise κ).Bounded (B κ) ∧ (F.parameters κ).modulus ≤ p.eval κ · B κ`, `_iff` | ruling Q16 | — |
| — | `GSW.Parameters.ofFamily F κ` (`lwe := F.parameters κ`, `width := F.residueBits.eval κ`, `modulus_le := F.modulus_le_pow κ`), `simps` | phase-5 §G4 | — |
| G16 | `bootRatio_le_poly`: an explicit `PolyExpr` `pBoot` (from `F.dimensionBound`, `F.samplesBound`, `F.residueBits`) with `4·ℓ·bootNoise (ofFamily F κ) (m·B κ) ≤ pBoot.eval κ · B κ` | BV14 Thm 3.7 ("α ≤ 1/Θ̃((n log q)^{2c+1/2})"), worst-case analogue | 100 |
| G17 | **`decrypt_fheEval_of_ratio`**: `∀ κ, pBoot.eval κ · B κ < (F.parameters κ).modulus` and `χ` `B`-bounded ⇒ bootstrapped GSW at `κ` is correct on every circuit; with `RatioBounded F B p` this is the polynomial-ratio regime of (A2) | BV14 §3.4 (`p016-b001`) | 60 |

## H6. Noise and ratio ledger

| Quantity | Value | From |
|---|---|---|
| fresh public-key ciphertext (inputs and `evk`) | `m·B` | `encrypts_encrypt` |
| selector step | `β_V + 2N·β` | G1 (`Encrypts.mul` ×2, `.add`) |
| PBP of length `L` | `L·2N·β_evk` | G2 |
| formula of depth `d` | `4^d·2N·β_evk` | G3 + C9 |
| bootstrapped gate | `bootNoise = 4^{decDepth+1}·2N·m·B` | G8, G9 |
| decryption condition | `2·(ℓ·bootNoise) < ⌊q/2⌋` and `2·(ℓ·m·B) < ⌊q/2⌋` | `decrypt_of_encrypts` |
| draft depth target | `decDepth ≤ 9⌈log₂N⌉ + 2⌈log₂(ℓ+⌈log₂N⌉+3)⌉ + 21` | §H3.4 |
| resulting ratio | `q/B > c·ℓ·m·N^{19}·(ℓ+⌈log₂N⌉+3)^4` for an absolute constant `c` (below `2^{70}` with the draft constants): **polynomial** in `κ` | G13, G16 |

The exponents are large (BV14 itself only says "`c > c_dec` large enough"); they are polynomial,
which is the claim. Tighter constants are possible but are not a phase-6 goal.

## H7. Sequence

1. **Statement phase 6a (complexity):** draft C1–C12, F1–F10 under
   `briefs/lattice-gsw/phase6/draft/`; compile one module at a time when an olean tree is free;
   promote `combine` (owner-side PR, P6-Q6); register `PermBranchingProgram` in
   `ComputationalModels.lean` and the `evalWith` host in `machine-library-design.md` §14; record the
   formula-arithmetic gadgets as the first rows of a circuit/formula gadget registry (policy §1,
   "once CircuitComplexity's gadget layer exists").
2. **Gate 42 (Codex):** 6a statements, including the Bar89 composition-order translation, the
   depth targets of F6–F10, and the host contract.
3. **Statement phase 6b (cryptography):** G1–G17, `LWE/Ratio.lean`, the `decode` interval lemma
   (P6-Q7). Cites 6a's frozen statements.
4. **Gate 43 (Codex):** 6b statements: noise ledger re-derived by hand, the circular hypothesis's
   exact form, Rule-10 seals over `TreeCircuit.eval`/`depth`, `decode`, `decomposeVec`, `runWith`.
5. **Fills** (proved-modulo; units may run in parallel once their statements are frozen):

| Unit | Content | Targets | Depends on | Est. fill |
|---|---|---|---|---|
| U1 | `BranchingPrograms/Basic` + host | C1–C4 | — | 150–220 |
| U2 | `Barrington` | C5–C10 | U1 (stmts) | 350–550 |
| U3 | `NC1` corollaries | C11–C12 | U2 (stmts) | 120–200 |
| U4 | `FormulaArith/Combinators` (+ `combine` promotion) | F1–F4 | — | 180–260 |
| U5 | `FormulaArith/CarrySave` | F5–F6 | U4 | 250–400 |
| U6 | `FormulaArith/Compare`, `ModSum` | F7–F10 | U4, U5 | 300–450 |
| U7 | `GSW/Branching` | G1–G3 | U1, U2 (stmts); phase 5 | 150–250 |
| U8 | `GSW/DecryptFormula` | G4–G8 | U4–U6 (stmts); phase 5 | 250–400 |
| U9 | `GSW/Bootstrap` | G9–G13 | U7, U8 | 250–400 |
| U10 | `GSW/Circular`, `LWE/Ratio`, `GSW/PolyRatio` | G14–G17 | U9; phase-5 security | 150–280 |

**Totals:** about 55 targets (several rows above bundle two or three lemmas); statement surface about 1,700–2,000 lines in 13 files plus facades;
fill about **2,150–3,400** lines, every math file under 600 lines. (The phase-5 roadmap estimated
4.2–5.8k for "phase 6 + BV14"; the formula route of §H3.4 replaces a gate-list decryption circuit
and is smaller.)

**Merge order:** phase-5 fills first (gsw-core, gsw-security); then 6a (complexity, independent of
GSW); then 6b.

## H8. Risks

1. **Depth constants.** A single `Θ(ℓ)` term in the decryption depth makes the ratio condition
   unsatisfiable (§H3.3). The gate must check `decDepth`'s closed form, and the fill must not
   introduce Shannon/DNF steps over `log q`-bit values.
2. **`decode` is an interval.** G4 depends on `LWE.BitEncoding.distance`'s exact definition; the
   bounds `lo, hi` are fixed only after reading it (the statement phase does this first).
3. **Composition order.** Mathlib's right-to-left product versus Bar89's left-to-right reading
   (§H3.6). A wrong order still yields a five-cycle in Lemma 3, so an error would not be caught by
   C5 alone; C8's statement is the check.
4. **Rule 10 on existing definitions.** Consumers read `TreeCircuit.eval`, `depth`, `maxFanin` only
   through `eval_node_*_iff`, `depth_node`, `maxFanin_node`; `DAGCircuit.toTree` through its four
   lemmas; `decomposeVec` through `gadget_mulVec_decomposeVec`/`digits_decomposeVec`; `decode`
   through `decode_eq` and the new interval lemma. The seal probe covers all of them.
5. **Private hosts.** `TreeNCAC.combine` and `Parity`'s dual-rail XOR are private; copying either is
   duplication needing approval (P6-Q6).
6. **Constants of the instruction model.** Constant gates need one variable (`n ≥ 1`); the
   decryption formula has `N = (n+1)ℓ ≥ 1` inputs, so `[NeZero n]` is harmless.
7. **Worst-case versus probabilistic.** BV14's Lemma 3.6 and Thm 3.7 are probabilistic (Rand,
   discrete Gaussians); the formal versions are worst-case and lose polynomial factors (§H6). The
   evaluation key is public-key (noise `m·B`) rather than BV14's secret-key (noise `B`): one more
   factor `m` (P6-Q8).
8. **Circular security is an assumption.** Its truth for GSW is open (Pei16 §6.1.2). The pure-FHE
   security theorem is only as strong as that hypothesis; the leveled key chain (P6-Q11) is the
   assumption-free alternative.
9. **Efficiency.** `barrington` is computable with explicit conjugators (P6-Q13), but the program length
   `4^{decDepth}` is a large polynomial; no running-time statement is made (out of scope, as for
   phase 5).
10. **Shared-file changes.** `ComputationalModels.lean` (registration), `TreeNCAC.lean`
    (promotion), possibly `LWE/BitEncoding.lean` (P6-Q7), the `CircuitComplexity` and `Complexity`
    facades, `TCSlib.lean`, `machine-library-design.md` §14. Each needs Seyoon's approval.
11. **Source fidelity.** BV14's evaluation reads coordinate 1 and so computes the complement; our
    output coordinate is `σ 0` (§H3.7). BV14's NAND-only augmented circuits are generalized to all
    fan-in-2 gates (P6-Q9). Both are disclosed deviations.

## H9. Not in this phase (recorded)

- Barrington's converse (Bar89 Thm 2, `BWBP ⊆ NC¹`), unless P6-Q3 option B.
- Leveled FHE security by a key chain of `L+1` keys, unless P6-Q11 option B (the key-switching form
  G9 makes its correctness a short corollary).
- The `NUPPT` bridge and asymptotic IND-CPA (with phase 5's bridge).
- The AP14 accumulator route, small-secret LWE and its ACPS09 equivalence (DW-6), modulus switching.
- Worst-case lattice approximation factors.

## H10. Proposed plan rows (for the maintainer)

Phase table:

| Phase | Frozen surface to prepare | Fill starts only after |
|---|---|---|
| 6a | `PermBranchingProgram` model and `evalWith` host, Barrington (Thm 1, `DAGCircuit`/`NC¹` corollaries), formula arithmetic (`neg`, `subst`, carry-save reduction, comparison, modular interval sum) | Gate 42 and Seyoon's approval of the `ComputationalModels`/`TreeNCAC` changes |
| 6b | GSW selector and PBP evaluation, decryption formula, bootstrapped gates, pure-FHE correctness for every depth, weak circular security (explicit), ratio predicate and polynomial-ratio statement | Gate 43; phase-5 fills merged |

Decision-log row:

| Date | Decision/evidence | Status |
|---|---|---|
| 2026-11-16 | DW-7 ingests filed (Jou00, BB04, GSW13, AP14, BV14, BV11, Bar89; Pei16 extended with §5.4.3, §6.1.2–6.1.3) as scoped raw + LaTeX transcriptions, tags registered; PDFs not committed. Phase-6 plan (BV14 route, polynomial ratio; merges roadmap phases 6–7) and questions P6-Q1–P6-Q13 under `briefs/lattice-gsw/phase6/`. Records only; no Lean. | Questions pending |
