# Gate 41 · GSW leveled homomorphic encryption (phase 5) and the DAGCircuit readers (statement)

Round 1. The auditor is Codex, under the standing ruling of 2026-11-11 (Codex for audits and reviews). Two draft PRs
are audited together: the small owner-side `DAGCircuit.lean` PR (GSW ruling Q2) and the GSW statement PR stacked on
it. The lattice campaign's GSW phase keeps its own gate folder (`briefs/lattice-gsw/gates/`); the gate number
continues the global sequence.

- **PRs:**
  - draft [PR #332](https://github.com/Shilun-Allan-Li/tcslib/pull/332) "DAGCircuit: depth readers and runWith_rel"
    at `94eae71b779c4ca0f76c138d699f4d737dbd6cee` (branch `stmt/dagcircuit-readers`, 1 commit);
  - draft [PR #333](https://github.com/Shilun-Allan-Li/tcslib/pull/333) "GSW leveled homomorphic encryption from LWE"
    at `48d796a8a68cd50897047f01825a8132dd19e8d8` (branch `stmt/gsw`, tree `b794328e90b5883ffc6efe60d964710f83fb5849`),
    **stacked on #332**: `48d796a8~2 = 94eae71b`, and #333's diff of `DAGCircuit.lean` is exactly #332's diff
    (`pack-checks/series.txt`). #332 must merge first.
- **Target and base:** both target `cryptography/pass-shelat-ch2-4` with merge base
  `523d80d2d4dd8e4ed6799358831e5b3806c6187b`; for each head the three-dot diff from the records tip equals the diff
  from `523d80d2` byte for byte. `pr.diff.txt` is `523d80d2..48d796a8` (84,963 bytes, SHA-256 `f577be74…`; it
  contains #332's commit).
- **Commits:** 3, all by the maintainer (author and committer Claude, `gpgsig` header present): `94eae71b`
  (#332, `DAGCircuit.lean` only), `8ce56b0d` (GSW modules and facades), `48d796a8` (exports `Hashing/SIS.lean`,
  `TCSlib.lean`).
- **Scope:** a **statement audit** before any fill of the 35 sorried GSW targets, plus an audit **as proofs** of
  #332's two proved results. Design `briefs/lattice-gsw/plan-section.md`; rulings `briefs/lattice-gsw/rulings.md`
  (Q1–Q16 accepted, **Q9 changed**: modules under `AdvancedEncryption/Homomorphic/GSW/`; addendum: small-secret LWE
  may be assumed later, A3); statement-text rulings QS1 (`Matrix.of` in `hashColumns_eq_mul`) and QS2 (`GSW.mul`
  qualified in `Encrypts.mul_bit`/`mul_le`), decision log of `LatticeCryptographyPlan.md` (2026-11-16).
- **Sources** (PDFs not committed; text excerpts of only the passages used are in `source-excerpts/` and in the
  bundle; hashes re-checked when the excerpts were written): [GSW13] author version of 8 June 2013 (`8edb94cf…`),
  §1.3, §2.3, §3.1–§3.4; [AP14] ePrint 2014/094 of 13 June 2014 (`cecd346d…`), §3 and §4 to Corollary 4.2; [BV14]
  ePrint 2013/541 (`eab2d166…`), §2.5 and §3; [Pei16] author version of 17 February 2016, §5.4.3 and §6.1.2–§6.1.3,
  quoted from the committed raw extraction `blueprint/src/references/peikert2016-lattice-survey.raw.md` (the scoped
  `.md` covers only Definitions 4.1.1, 4.2.1, 4.2.3 and the SIS passages).

## What changed

13 files, 1457 insertions, 0 deletions (`pack-checks/files.txt`). Every line is at most 100 characters; every file is
under 1000 lines; the three pre-existing files change by insertion only.

| File | Lines | `sorry` | Content |
|---|---:|---:|---|
| `Complexity/CircuitComplexity/DAGCircuit.lean` (#332) | 627 → 721 | 0 | readers `DAGGate.depth_eq`, `DAGCircuit.depths_eq`, `depthAt_eq`, `depth_eq` (`rfl`); **proved** `DAGGate.getD_lt_depth` and `runWith_rel`; module docstring |
| `…/Homomorphic/GSW/Gadget.lean` | 204 | 5 | `Parameters` (`q ≤ 2^ℓ`), `columns` (`N = (n+1)ℓ`), `Ciphertext`, `gadget = (Lossy.gadget ℓ (n+1))ᵗ mod q`, `digit`, `decomposeVec`, `decompose`, `lift` |
| `…/GSW/Noise.lean` | 235 | 12 | `mul`, `nand`, `chain`, `Encrypts`; the closure algebra |
| `…/GSW/Scheme.lean` | 215 | 6 | `secretVector`, `encrypt = ĀR + μG`, `halfVector`, `decryptColumn`, `decrypt` (through `Regev.decrypt`) |
| `…/GSW/Eval.lean` | 207 | 4 | `homAnd`, `homNot`, `homOr`, `homGate`, `evalValues`, `eval` over `BoolCircuit.DAGCircuit` via `runWith` |
| `…/GSW/Security.lean` | 217 | 4 | `view`, `realView`, `uniformKeyView`, `reduction`, `columnHashParameters` (Q11 duplicate) |
| `…/GSW/Symmetric.lean` | 111 | 2 | optional unit F7: `rowEquiv`, `symEncrypt` |
| `Hashing/SIS/Columns.lean` | 89 | 2 | `hashColumns`; the column leftover-hash hybrid |
| facades `AdvancedEncryption`, `AdvancedEncryption/Homomorphic`, `…/Homomorphic/GSW` | 25, 22, 35 | 0 | each imports and lists every child |
| `Hashing/SIS.lean`, `TCSlib.lean` | +2, +1 | — | exports |

35 `sorry`s, one per target (Gadget 5, Noise 12, Scheme 6, Eval 4, Columns 2, Security 4, Symmetric 2;
`pack-checks/sorries.txt`). Every public definition has a reader (`pack-checks/readers.txt`); no `@[simp]`; the views
carry non-simp `simps!` projections. `pack-checks/names.txt`: no full-name clash with the tip.

### The noise statements the gate must check closely

```lean
def Encrypts (P) (t : Fin (n+1) → ZMod q) (x : ℤ) (β : ℕ) (C : Ciphertext P) : Prop :=
  ∃ e : Fin P.columns → ℤ, (∀ j, (e j).natAbs ≤ β) ∧
    Matrix.vecMul t C = (x : ZMod q) • Matrix.vecMul t (gadget P) + fun j => (e j : ZMod q)

theorem Encrypts.mul (h₁ : Encrypts P t x₁ β₁ C₁) (h₂ : Encrypts P t x₂ β₂ C₂) :
    Encrypts P t (x₁ * x₂) (P.columns * β₁ + x₁.natAbs * β₂) (mul P C₁ C₂)      -- mul = C₁ · lift (G⁻¹ C₂)
theorem encrypts_chain (hs : List.Forall₂ (fun b C => Encrypts P t b.toNat β C) bs Cs)
    (hacc : Encrypts P t x β₀ acc) :
    Encrypts P t ((bs.all id).toNat * x) (β₀ + Cs.length * (P.columns * β)) (chain P Cs acc)
theorem eval_encrypts (Cc : DAGCircuit k) (hfan : ∀ g ∈ Cc.gates, g.args.length ≤ 2)
    (x : Fin k → Bool) (cts : Fin k → Ciphertext P) (β : ℕ)
    (hin : ∀ i, Encrypts P t (x i).toNat β (cts i)) :
    Encrypts P t (Cc.eval x).toNat ((P.columns + 1) ^ Cc.depth * β) (eval P Cc cts)
theorem decrypt_of_encrypts (h : Encrypts P (secretVector P s) b.toNat β C)
    (hsep : 2 * (P.width * β) < P.lwe.modulus / 2) : decrypt P s C = b
theorem decrypt_keygen_eval … (hχ : χ.Bounded B) (hdepth : Cc.depth ≤ L)
    (hsep : 2 * (P.width * ((P.columns + 1) ^ L * (P.lwe.samples * B))) < P.lwe.modulus / 2) :
    decrypt P (Regev.keygen P.lwe χ rg).2 (eval P Cc fun i => encrypt P (Regev.keygen P.lwe χ rg).1 (x i) (R i))
      = Cc.eval x
theorem distAdv_encrypt_le … :
    distAdv (realView P χ μ₀) (realView P χ μ₁) D ≤ LWE.decisionAdvantage P.lwe χ (reduction P μ₀ D) +
      LWE.decisionAdvantage P.lwe χ (reduction P μ₁ D) + 2 * (P.columns * Regev.extractionError P.lwe)
```

The staging re-derived each of these by hand (no Lean) and found no off-by-one: `mul` expands the left error over the
`N` rows of `G⁻¹(C₂)` and scales the right error by `x₁` ([AP14, Lemma 3.5]: `e₁ᵗX + μ₁e₂ᵗ`); the chain adds `N·β` per
fresh left factor; a fan-in-≤2 gate costs at most `((2−1)·N + 1)·β = (N+1)·β` (`homAnd_encrypts` gives
`((k−1)·N + 1)·β` with natural subtraction, so `k = 0, 1` give `β`); `¬` and `∨` add only the noiseless `G`;
decryption reads `⟨t, C·G⁻¹(w)⟩ = b·⌊q/2⌋ + ⟨e, G⁻¹(w)⟩` with `|⟨e, G⁻¹(w)⟩| ≤ ℓβ` because `w = ⌊q/2⌋e_{n+1}` has one
nonzero block, and `LWE.BitEncoding.decode_codepoint_add` needs `2·B < ⌊q/2⌋` with `B = ℓβ`. Codex is asked to
confirm or refute each step.

## Rulings and records in force

- **Phase-5 scope (Seyoon, 2026-11-16):** leveled GSW from ordinary LWE, `(N+1)^L·mB` correctness, IND-CPA from DLWE;
  roadmap phase 6 (bootstrapping under weak circular security) and phase 7 (polynomial ratio, BV14, Q12).
- **Q1–Q16 (A), Q9 changed:** Q1 `DAGCircuit` via `runWith`; Q2 the owner-side `DAGCircuit.lean` PR (readers and
  `runWith_rel`; `Garbling.lean` untouched; `runWith_sim` → `runWith_rel` on the dedup queue); Q3 regime-agnostic
  concrete statements; Q4 public-key headline plus optional F7; Q5 worst-case every-coin correctness; Q6 the
  `C·G⁻¹(⌊q/2⌋·e_{n+1})` column with `Regev.decrypt`; Q7 the chain lemma in phase 5; Q8 concrete hybrids now, the
  `NUPPT` bridge later; Q9 `AdvancedEncryption/Homomorphic/GSW/` (namespace
  `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW`), Columns at `Hashing/SIS/Columns.lean`; Q10 reuse
  `Lossy.gadget` in place; Q11 a GSW-local `columnHashParameters`, disclosed; Q12 BV14 for phase 7; Q13 Barrington as
  its own unit; Q14 ingest GSW13 in the statement PR; Q15 weak circular security as an explicit hypothesis; Q16 the
  LWE gap as a ratio predicate. Addendum: small-secret LWE (A3) may be assumed in later phases.
- **QS1, QS2 (Seyoon, 2026-11-16):** statement texts changed by the API, meaning unchanged (evidence
  `questions-statement-changes.md`).
- **Shared facade (pairing location ruling):** `AdvancedEncryption.lean` is shared with the pairing PR #331; whichever
  lands second adds its child.
- **Standing rules:** Rule 10; policy §§1–3; the #305 facade rule; at most 100 characters per line.

## Questions for the audit

1. **Fidelity of the gadget presentation** to [GSW13], [AP14, §3.2] and [Pei16, §6.1.3], with the differences
   disclosed (`Gadget`, `Noise`, `Scheme` module docstrings): gadget form `C = ĀR + μG` instead of
   `Flatten(μI_N + BitDecomp(R·A))` (GSW13 §3.2 notes `BitDecomp⁻¹(C) = μG + RA`; AP14 calls the variants "purely
   syntactic[ally]" interchangeable); `t = (−s, 1)` with the `1` last; left approximate singular vector
   `tᵗC ≈ x·tᵗG`; deterministic binary `G⁻¹` (AP14's randomized subgaussian `G⁻¹` excluded by the plan); width `ℓ` any
   value with `q ≤ 2^ℓ` (GSW13 `⌊log q⌋+1`, AP14/Pei16 `⌈log₂ q⌉`); worst-case `ℓ∞` noise; public key = the audited
   `Regev.augmented`; NAND as `G − C₁·G⁻¹(C₂)`. Is any difference undisclosed or misdescribed? In particular:
   - the `gadget` docstring writes `G = I_{n+1} ⊗ gᵗ` and cites [AP14, Equation (3.1)], which writes `gᵗ ⊗ I_n`
     (and `diag(gᵗ, …, gᵗ)`); [Pei16, §5.4.3] writes `I_n ⊗ gᵗ`. Same block-diagonal matrix; notation only?
   - is the mirroring statement (GSW13/BV14 expand the *right* operand's error, AP14/Pei16 the *left*; additive chains
     put fresh ciphertexts on the left here, on the right in BV14 Claim 3.4.2) exact?
2. **Truth of every one of the 35 targets.** Pay particular attention to the bounds above. **Flag any off-by-one or
   missing hypothesis.** Specific points:
   - `Encrypts.mul` for **integer** messages (`x₁.natAbs`), `mul_bit` (`(b.toNat).natAbs ≤ 1`), `mul_le` and `nand`
     (message `(!(b₁ && b₂)).toNat` from `1 − b₁b₂`);
   - `encrypts_chain` with `List.Forall₂` (lengths equal) and the accumulator on the right;
   - `homAnd_encrypts` (natural subtraction at `k = 0`), `homGate_encrypts` (`hfan : g.args.length ≤ 2`, the library's
     `¬` gate negating the conjunction of all its arguments, out-of-range arguments read as `false`/`0`, the
     ciphertext `0` encrypting `0` with zero noise), `eval_encrypts` (only `hfan`, not `IsFaninTwo`; acyclicity from
     the structure field `args_lt`; depth counts `¬` gates), `decrypt_keygen_eval` (`Cc.depth ≤ L`);
   - `decrypt_of_encrypts` (every `q ≥ 2`; the factor `ℓ` disclosed, Q6) and `decrypt_of_encrypts_dyadic` (`q = 2^ℓ`;
     `hℓ : 0 < ℓ` is implied by `q ≥ 2` — harmless redundancy?); `errorSum_decomposeVec_le`,
     `decomposeVec_block_eq_false`, `gadget_mul_decompose` (any column index type);
   - `vecMul_secretVector_augmented`, `encrypts_encrypt` (`m·B`), `encrypts_keygen_encrypt` (through `Regev.keygen`
     and `LWE.sample`);
   - `hashColumns_eq_mul` (QS1) and `distAdv_hashColumns_uniform_le` (`N` times the single-column error at the SIS
     shape; `N = 0` gives `0 ≤ 0`);
   - `encrypts_symEncrypt` (noise `B`) and `distAdv_symEncrypt_le` (one DLWE instance with `m = k·N` rows; the uniform
     side is a bijection onto `Fin k → Ciphertext P`).
3. **IND-CPA:** `real_uniformKey_advantage` (an **equality** with one DLWE advantage, by reassociating independent
   seeds as `Regev.real_uniformKey_advantage`), `uniformKey_uniform_advantage_le` (`N · ε_LHL` with
   `ε_LHL = Regev.extractionError = ½√(q^{n+1}/2^m)`, via `columnHashParameters` and the augmentation bijection),
   `distAdv_encrypt_le` (two DLWE advantages plus `2·N·ε`), `distAdv_encrypt_le_of_width` (`m ≥ (n+1)w + 2κ` gives
   `N·2^{−κ}` through `Regev.two_extractionError_le`). Are the views, the reduction and the coin types right? Is the
   fixed-bit, function-level form the ruled level (Q8), with the `NUPPT` bridge deferred?
4. **Reuse of the existing LWE, Regev and `Lossy.gadget` layer, and the disclosed duplicate.** The GSW files read
   `LWE.Parameters`, `Noise.Bounded`, `noisyValues`, `sample`, `decisionAdvantage`, `binaryErrorSum_bound`,
   `BitEncoding.codepoint`/`decode_codepoint_add`, `Regev.keygen/augmented/decrypt/extractionError/
   two_extractionError_le`, `Lossy.gadget/digits/gadget_mulVec/digits_val`, `Randomized.blocksEquiv`,
   `Hashing.SIS.hash/distAdv_hash_uniform_le` (all in `sources.zip`; Regev, Lossy, SIS and BitEncoding also in
   `verification.zip` `context/`). `columnHashParameters` is field-for-field `Regev.hashParameters` (Q11, disclosed in
   its docstring). The GSW `view`/`realView`/`uniformKeyView`/`reduction` and the four Security theorems mirror
   Regev's names in another namespace (`pack-checks/names.txt`). Is anything an undisclosed duplicate, or should a
   shared lemma be harvested instead?
5. **The #332 additions** (`DAGCircuit.lean` at `94eae71b`; `briefs/lattice-gsw/draft/shared/DAGCircuit-additions.lean`
   is the approved draft): the four `rfl` readers and the module-docstring entries; **audit as proofs**
   `DAGGate.getD_lt_depth` (induction over the argument list with `le_max_left`/`le_max_right`, then `omega` with
   `depth_eq`) and `runWith_rel` (strong induction on the vertex; `runWith_getD_of_lt`, `runWith_getD_gate`,
   `runWith_getD_take`, `length_runWith`); is `runWith_rel`'s statement general enough for `eval_encrypts` (relation
   indexed by the vertex, so `R v` can carry the depth of `v`) and does `SecureComputation.runWith_sim`
   (`Garbling.lean`, in `context/`) follow from it, as the dedup note claims? Both are proved with standard axioms
   (evidence `axioms.txt`).
6. **Rule 10, docstrings and sketches.** Seals: 12 files × 4 variants (strict A, `PolyExpr.eval`-sealed B, coe A/B)
   = 48/48 pass, with five sealed negative controls failing once each (through `Encrypts`, `gadget`, `decrypt`,
   `hashColumns`, `DAGCircuit.depth`) and the unsealed and positive controls passing (`rule10/seal-seals-*.tsv`,
   `rule10/controls/`). Every target has a `**Proof sketch.**`; every public declaration has a docstring with a
   source tag where it corresponds to a result. Please rate:
   - `homAnd`'s docstring says "a left-to-right product chain"; the definition is right-associative
     (`C₁ ⊡ (C₂ ⊡ …)`, head on the left), as `chain` and AP14 Corollary 3.6;
   - the 23 `UNCHECKED` places and the four fixes F1–F4 (evidence `unchecked-fixes.md`): all statements unchanged in
     meaning except as ruled by QS1/QS2;
   - the source tags against the papers' numbering (e.g. `[AP14, Definitions 3.2–3.3]`, `Lemma 3.5`, `Corollary 3.6`,
     `Claim 3.4`; `[GSW13, Section 3.3]` "Circuits", `Lemma 1`; `[BV14, Claims 3.4.1–3.4.2, Lemma 3.6]`;
     `[Pei16, Equations (6.1.4)–(6.1.7)]`).
7. **Fit with the phase-6/7 roadmap** (`plan-section.md` §G9; BV14 ruled, Q12): does phase 5 give exactly the hooks
   BV14 §3.3 needs (Equations (5)–(6) are a sum of two products, so `Encrypts.add` and the asymmetric `mul` with the
   `|x|·β` term; `G − C` for `C̄`; the chain bound; `DAGCircuit` as Barrington's input and phase 6's decryption
   circuit), and does any phase-5 choice (worst-case noise, deterministic `G⁻¹`, the `G⁻¹(w)` decryptor, uniform
   secrets, `DAGCircuit` fan-in) block phase 6 or 7?
8. **Policy:** layout per Q9; facades import and list every child; imports precise; the cross-topic import of
   `TrapdoorFunctions/Lossy/Gadget.lean` (Q10).

## Known dispositions (not findings)

- **The shared facade.** `AdvancedEncryption.lean` is added by both #331 (pairings) and #333, and both add an import
  to `TCSlib.lean`: an expected add/add conflict, resolved by union by whichever lands second. A merge condition.
- **Proofs of the 35 targets are out of scope;** the gate asks whether they are true, provable on the sketched routes
  and sufficient for their consumers.
- **Worst-case bounds, the decryption factor `ℓ`, deterministic `G⁻¹`, uniform secrets and the deferred `NUPPT`
  bridge** are ruled (Q3, Q5, Q6, Q8; plan §G8 risks 3–4, 8).
- **The evidence archive** `stmt-gsw.zip` was not in the records when the PRs were opened; this gate files it
  (`briefs/lattice-gsw/statement-phase/evidence/`).

### Open items noted by the staging (please rate; two need a ruling, see the dispatch)

- **Q14 ingestion is not done.** Q14 (A) says "ingest GSW13 into `blueprint/src/references/` in the phase-5 statement
  PR"; #333 contains no ingest (evidence PROVENANCE: "Not done here"). Policy §2 asks for the ingest "in the change
  that formalizes it". This gate files text excerpts only.
- **Pei16 coverage:** the docstrings cite Pei16 §5.4.3 and §6.1.3, which are in the committed raw extraction but not
  in the approved scoped excerpt `peikert2016-lattice-survey.md`.
- **Plan rows:** the proposed rows of `plan-section.md` §G10 (organization table, phase table) are not yet in
  `LatticeCryptographyPlan.md`, and the §G10 row still names `Encryption/Homomorphic/GSW/` (pre-Q9 path).
- **PR descriptions:** #333 describes the gadget results as "`G·G⁻¹ = id`, the digit bounds, and the error sum"; the
  five Gadget targets are `digits_decomposeVec`, the two `G·G⁻¹` identities, the zero-block lemma and the error sum.

## Merge interaction (maintainer merge conditions, not audit items)

From git objects only (`pack-checks/mergetrees.txt`, `pack-checks/mergeall.txt`); records tip during staging
`0542dd9210ccdb844ad125cd95f8488c9f553153` (it contains #318, #319, #323 and #326, merged as `7e85f4c0`).

| Merge | Result | Modules whose closure meets both sides' Lean changes |
|---|---|---|
| #332 with the tip | clean; **both sides change `DAGCircuit.lean`**: #323's `isFaninTwo_iff` (+9 lines near `IsWellFormed`) and #332's +94 lines after `depthAt_gate`, disjoint hunks; the merged file is the tip's plus #332's lines exactly | 281: `DAGCircuit` and its whole downstream |
| #333 with the tip | clean | 291 (the above plus the GSW modules) |
| #332 / #333 with #324 sc-compose | clean | 16 (`SecureComputation/ComposeSecurity/*`, `YaoReal`, facade, root) |
| #332 / #333 with #327 seq-zk | clean | 41 (`Composability/SequentialZK/*`, facade, root) |
| #332 with #331 pairings | clean | `TCSlib` only |
| #333 with #331 pairings | **conflict** in `TCSlib.lean` and `AdvancedEncryption.lean` (add/add) | `AdvancedEncryption`, `TCSlib` |

All open heads merged onto the tip in two orders give the **same tree** `1fc1b521602bd7ac2f4199accdb7f7245f428198` once
the one conflict is resolved by union (`mergeall.txt` prints the resolved facade).

**Merge conditions.** (1) #332 merges before #333. (2) The statement evidence (including the 278-module root build)
was built at base `523d80d2`, before #323's `isFaninTwo_iff`: after merging #332, rebuild `DAGCircuit.lean` and its
downstream on the merged tree, root last; likewise whichever of #332/#333 and #324/#327 lands second rebuilds the
16/41 joint modules. (3) Whichever of #333 and #331 lands second resolves the facade and root by union and re-checks
`AdvancedEncryption` and `TCSlib`.

## Evidence

`verification.zip` (74 entries, SHA-256 `63afa3f69eaa3a5326604e4783916757fc6c5876fd5ff3b2f08a491819a20aea`; its
`SHA256SUMS` lists every other entry; `PROVENANCE.txt` maps each to its source; built at records `aacfa40b`):
- `evidence/`: `stmt-gsw.zip` (SHA-256 `4b144e17…85d3`, 545 files, inner manifest verified) with its manifest
  `SHA256SUMS` and `PROVENANCE.txt`, byte-identical to the files this gate files in the records;
- `evidence-extracts/`: the build (`build/final/summary.txt`: 12/12 rc 0, only the 35 target `sorry`s;
  `build/root/summary.txt`: 278/278 rc 0; `closure-need.txt`, `iterations-summary.txt`), `axioms.txt` (285
  declarations + 56 auxiliary constants; `sorryAx` in exactly the 35 targets; `getD_lt_depth` and `runWith_rel`
  standard), the statement dump and API check (`statements/`, `probe/`), the draft-to-final diff, `unchecked-fixes.md`,
  `questions-statement-changes.md`, the seals and controls (`rule10/`), lint (`style_lint` 0; campaign lint 0 FAIL /
  0 WARN; `dag-base`/`dag-head`), sizes and widths, the series (`git/`), the olean-tree snapshots (`457ba704…` before
  and after);
- `records/`: rulings, questions, plan section, the shared-file draft, `LatticeCryptographyPlan.md` and the
  statement-phase `EVIDENCE.md` (pre-pin versions), `policy.md`;
- `source-excerpts/`: the four excerpt files;
- `context/` (records tip): `SecureComputation/Garbling.lean` (`runWith_sim`), `Regev/Experiments.lean`,
  `Regev/Basic.lean`, `Symmetric/Regev.lean`, `Lossy/Gadget.lean`, `Hashing/SIS/Universality.lean`, `LWE/Basic.lean`,
  `LWE/BitEncoding.lean`;
- `pack-checks/`: `series`, `files`, `decls`, `sorries`, `readers`, `facades`, `names`, `dupscan`, `mergetrees`,
  `mergeall`, with their scripts (git objects and `python3 -I` only; nothing was built).

Also: `pr.diff.txt`, `pr-description.md` (both PR descriptions, fetched 2026-11-16), `source-head.json` (SHA-256
`348d9172…`) and `sources.zip` (the import closure at #333's head of every changed module, 118 files, SHA-256
`e9a78b1f…`).

## Findings delivery

Return `gate41-gsw-statements-findings.md` as a Markdown file in this chat, with findings for #332 and #333 marked by
PR. If you have several evidence files, return a ZIP.

| # | Severity | PR · file · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

**Severities**
- **blocker:** a false or unusable statement, a proved result whose proof is unsound, or a scope violation (a frozen
  or shared file changed beyond the approved additions).
- **major:** a missing or wrong hypothesis or an off-by-one in a bound, a statement too weak or too strong for its
  consumers (leveled correctness, IND-CPA, the phase-6/7 hooks), an undisclosed deviation from the sources or the
  rulings, a forbidden read in a proved declaration, a duplicate public result, or necessary evidence that cannot be
  verified.
- **minor:** documentation or API defects, including an inaccurate formula docstring or proof sketch.
- **note:** anything else.

Report the audited heads and the counts by severity. The gate closes at zero blockers and zero majors.
