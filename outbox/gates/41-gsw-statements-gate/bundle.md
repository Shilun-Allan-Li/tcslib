## ===== briefs/lattice-gsw/gates/41-gsw-statements/pack.md =====

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

## ===== policy.md =====

# TCSlib Contribution Policy

Standards for all Lean contributions to this repository, whether written by humans or by
agents. This document covers three things: **modularity** (how code is organized),
**attribution** (how every result is traced to a source), and **proof sketches** (how every
formal proof is accompanied by readable mathematics).

It complements, and does not replace:

- `workflow.md` — the campaign formalization process (phases, audit gates, fill epochs)
  that produces code meeting these standards.
- `.github/copilot-instructions.md` — build workflows, import rules, CI integration points.
- `AGENTS.md` / `.claude/CLAUDE.md` — the sorry-ladder proof workflow and agent roster.
- `blueprint/BLUEPRINT_PIPELINE.md` — how blueprint entries are generated and validated.

Where this document names an existing mechanism (blueprint macros, hygiene scripts), the
policy is to *use that mechanism*, not to invent a parallel one.

## 1. Modularity

**Layout.** Content lives at `TCSlib/<Area>/<Topic>/<Piece>.lean`, one coherent concept or
lemma cluster per file, with a facade file `TCSlib/<Area>/<Topic>.lean` that imports every
child and carries a `/-! -/` module docstring with a `## Contents` list (one line per child).
See `TCSlib/Complexity/NPReductions.lean` for the reference example.

**File size.** Target 150–600 lines per math file. A file approaching 1000 lines should be
split unless there is a positive reason not to (e.g. a single long proof that cannot be
usefully decomposed).

**Exports.** Every new topic facade must be imported from `TCSlib.lean`. CI only builds what
is reachable from `TCSlib.lean`; an unexported file is invisible to CI, docs, and the
blueprint.

**Imports.** Precise module imports only. A bare `import Mathlib` fails CI. Import only what
the file uses.

**Namespaces.** Namespaces are area-local: pick one namespace root per topic and use it
consistently within that topic. Do not leak auxiliary definitions into the root namespace;
mark internal helpers `private` or put them in a dedicated inner namespace.
*Model registry exception*: a model-defining **type** (a machine, circuit, formula, or
decision-tree model) may live at the root namespace, Mathlib-style, provided it is
registered in the catalog facade `TCSlib/ComputationalModels.lean`; its operations and
lemmas still live in the type's own namespace. Anything else at root is a leak.

**Layering.** Keep definition files separate from heavyweight theorem files, so that
downstream work can import a model or a class definition without pulling in every proof about
it. When a development has both a "raw/general" layer and a "bundled" layer (e.g. a machine
model that is parametric in its types, plus a bundled version carrying finiteness instances),
headline definitions and theorems are stated against the bundled layer; the raw layer is
internal plumbing.

**Helpers.** Foundational helper lemmas that serve a whole area belong in that area's
`Basic.lean`, not in the file that first needed them.

**Definitions land with their lemmas** (user, 2026-10-16). Every new public `def` is published,
in the same PR and beside the definition, with the lemmas that let a consumer read it without
unfolding:
- a structure-valued definition (a contract, a configuration, zone contents): its field
  equations, generated by `simps` with `(config := { isSimp := false })` and explicit
  projections (`simps!` where the body is another constructor's result);
- any other definition: an equation lemma `<name>_eq` (by `rfl` where that holds), or case
  lemmas that together cover every input (`_of_lt`/`_of_le`, `_true`/`_false`, one per
  constructor);
- a predicate: an `_iff` characterization;
- a machine: its run or contract lemma, the only way consumers read a machine.

None carries `@[simp]` unless a gate approves it, and each docstring states its formula. Consumers
never unfold another file's definition (the no-unfolding rule of the briefs, user 2026-10-16). The
rule binds TCSlib's own definitions: core and Mathlib definitions may reduce in a `rfl`, `decide`
or `show` step, but are never passed to `simp`, `rw` or `unfold`; use their equation lemmas
(`Bool.toNat_true`, not `simp [Bool.toNat]`) (user, 2026-10-23).
**Reducible abbreviations are notation** (user, 2026-10-26). Lean unfolds a TCSlib `abbrev` (such
as `Turing.Cfg.Halted`, `cfg.state = none`) at every step, and the standard seal cannot cover it:
under Lean's default reducibility validation, `attribute [local irreducible]` fails on a reducible
declaration (only the unsafe override `set_option allowUnsafeReducibility true`, which the
campaign's seals do not use, lifts the check). So reading an abbreviation through its body,
for example `¬ c.Halted` as `c.state ≠ none`, is allowed and is not a definitional closure. A
consumer names it in `simp`, `rw` or `unfold` only through a published lemma where one exists, and
a new public `abbrev` still lands with its `_iff` or `_eq` lemma.
They read the machine model's primitives (`MultiTapeTM.step`, `runFrom`, `Action.apply`,
`Cfg.mapState`) through the existing lemmas. The style lint's check 8 reports, per file, every
public `def` with no lemma named after it and no `simps` attribute, so a head-against-base diff
of the lint shows any new definition that lacks one. Definitions that predate the rule are listed
by the same check and covered as consumers need them.

**Construction reuse.** Machines are built from the verified construction layers, not from
scratch: the combinators and routine catalog of `TCSlib/Complexity/TuringMachine/Build/`
(conventions, wrappers, loops, primitives, embeddings, seams, and the catalog rows —
`machine-library-design.md` is the registry), the registered hosts (**Hosts come first**,
below), and the program layers (`LogProg.ARM`, `CounterProg`, and the general programming
layer of `machine-library-design.md` §15 once it lands) where a program-level description
suffices. Before writing a transition
table by hand, check the registry; a routine that exists is cited, not re-derived. A routine
that *almost* exists is the interesting case: do not write a third private variant — either
consume the general form, or commission the missing form into the shared layer (during a
fill batch: a `private` local copy plus a "requested shared lemma" in the report, promoted
at the next shared-file window). A hand-built machine is acceptable only when no layer
covers the need, and its docstring must say so and name what was missing — that sentence is
what turns the gap into the next catalog row. The chapter-1/2 files that predate this layer
re-derived the same bank/relocation/dispatch/frame families four times over (`emitterBank*`,
`clBank*`, `clSlot*`, …); the retrofit paying that debt back is the standing cautionary
tale. The same discipline applies to circuit construction once `CircuitComplexity`'s gadget
layer exists: gadgets, wiring combinators, and size/depth ledgers get one shared home and a
registry, and new circuits are assembled from it.

**Hosts come first.** A *host* is a control structure that drives other routines rather than
computing one value: a search or traversal (BFS, DFS, backtracking, an odometer over
assignments), a recursion or evaluation scheme (AND/OR evaluation, Savitch's midpoint
recursion), an interpreter or simulation step block, a clocked or windowed runner, a dispatcher
over a data structure (tables, records), or an input device. Any routine whose natural contract
does not depend on its first consumer counts as a host; leaf rows (copy, compare, seek,
arithmetic) do not. **A host is never built `private` inside the proof that first needs it.**
Its public contract is designed, statement-gated and placed in the shared construction layer
first, generic in the parts its consumers vary (the leaf test, the step relation, the data
domain), with time and space (head-envelope) clauses. Consumers cite it, under the campaign's
proved-modulo rule while its own fill is still running. The host registry is
`machine-library-design.md` §14. A private host already in the tree is harvested into the
shared layer before a second consumer is briefed against it. The rule exists because private
hosts were the main way the library overfitted to single proofs: four configuration encodings,
three reachability notions and a private search host per theorem, each to be re-derived by the
next consumer (assessment of 2026-10-12, recorded in the design document). (User, binding,
2026-10-12.)

**Duplication.** Some duplication is mechanically forced by the campaign discipline —
exclusive file ownership, the statement freeze, and `private` visibility leave a fill batch
no other legal way to use another file's unexported machinery — and occasionally it is the
right engineering call. It is never silently acceptable: **every instance of duplicated
proved material must be human-approved.** A fill batch discloses each copy in its report;
the maintainer's integration ledger totals copied material per file (`workflow.md` §4); and
the audit template treats accumulated duplication as a major finding that a gate cannot
close over without the human maintainer explicitly accepting the debt and naming where and
when it is paid back (the registry's dedup/refactor queue). Duplication that was never
disclosed is a freeze violation, not debt.

**File header.** Every math file begins with the Mathlib-style copyright block, its imports,
the repo-standard options

```
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
```

then a module docstring containing `# Title`, `## Main definitions`, `## Main results`, and
`## References` (see §2).

## 2. Attribution

Every mathematical statement in the library must be traceable to a source, at the level of
precision of a textbook theorem number or a paper section.

**File-level.** Every math file's module docstring contains a `## References` section giving
full citations with short tags, e.g.

```
## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
```

**Declaration-level.** Every definition, theorem, and lemma that corresponds to a result in
a source carries the tag with a precise location in its docstring: `[AB09, Claim 1.6]`,
`[AB09, §1.7]`, `[GRS25, Thm 4.2.1]`. Purely technical glue lemmas with no textbook
counterpart may omit the tag; anything a reader would recognize as "a result" may not.

**Deviations.** If the formal statement deviates from the source — different constants,
strengthened or weakened hypotheses, a reformulation — the docstring must say so and briefly
say why (e.g. "stated with explicit constant 5k rather than O(·), following the proof").

**Statement prose.** Every public declaration's docstring begins with a natural-language
statement of what it asserts (for a definition: what it is), precise enough that a reader
could judge the formalization's fidelity without parsing the Lean. The `[Tag, location]`
citation and any deviation note attach to that statement; the proof sketch (§3) follows it.
A bare label ("Unfolding lemma", "Helper for X") is not a statement. Instances are exempt,
as are vendored files (which follow upstream style). `private` declarations should carry
docstrings too, but at reviewer discretion rather than as a hard requirement. The blueprint
remains the cross-referenced informal layer for dependency structure (see **Blueprint**);
the docstring statement is what external audits compare blind restatements against, so it
is part of the trusted surface.

**Blueprint.** When an ingested reference exists under `blueprint/src/references/`, blueprint
entries use `\statementsource{<ref>}{<anchor>}` and `\proofsource{<ref>}{<anchor>}` to cite
it, subject to the existing rule that these are written only after an approved proofmatch
run. When starting a new chapter or paper, ingest it as a reference pair
(`<name>.raw.md` + `<name>.md`) so these citations are possible: put the PDF under
`blueprint/src/references/` in the change that formalizes it and run
`python3 scripts/dataset_pipeline.py --yes`, which ingests it, matches every text the
blueprint does not cite yet, and carries the new statements into the dataset
(`python3 scripts/sources.py add TAG=<pdf or md>` does the ingest and match alone, with
the docstring tag above; `python3 scripts/sources.py` shows which texts are attached and
which are still missing; see `dataset/INSTRUCTIONS.md`). The dataset builder does not
search outside that directory for sources; an unattached text leaves the theorems with
informalized proof notes instead of citations.

**Vendored code.** Lean code adapted from another project keeps the original copyright
header and license notice, and its file docstring names the source project, the commit it
was taken from, and a summary of local modifications.

**Design adaptation.** When a construction, proof architecture, or module design is
adapted from — or materially inspired by — another project's code, the debt is cited even
when no code is transcribed. The module docstring's `## References` section names the
source project, author, module or archive entry, the commit or version consulted, and its
license, with a short tag usable at declaration level; the precedent is
`TuringMachine/Composition.lean`'s `[Balbach22]` for the Isabelle AFP `Cook_Levin`
composition-combinator architecture. Design documents and blueprint entries built on the
adapted design carry the same citation. Examining external code purely for comparison,
with nothing taken, creates no citation duty, but on a campaign it belongs in the
campaign's records (plan decision log or backlog) so the provenance question is answerable
later. (Maintainer guideline, binding, 2026-10-06.)

## 3. Proof sketches

Every nontrivial formal proof is accompanied by a human-readable English proof sketch, kept
next to the Lean it describes.

**What counts as nontrivial.** Rule of thumb: any proof longer than ~20 lines of tactics, or
that would rate difficulty ≥ 3 on the blueprint scale. One-line `simp`/`omega`/`exact`
proofs need no sketch.

**Where sketches live.** In the Lean file itself:

- For most theorems: a `**Proof sketch.**` paragraph at the end of the theorem's docstring,
  written in mathematical English (not Lean identifiers), naming the key intermediate steps.
- For long proofs: additionally, short comments at the major `have`/section boundaries tying
  the tactics back to the sketch's steps.

The named intermediate steps of a sketch should be visible in the formalization as `have`s
or standalone lemmas — if the sketch says "first reduce to the one-tape case", there should
be a lemma that is that reduction.

**Where sketches do not live.** Not in the blueprint. Blueprint statement entries state
claims only; `scripts/dataset_hygiene.py --strict` hard-fails on proof content there. The
blueprint records *what* is true and its dependency structure; the Lean docstrings record
*why* it is true.

**Sketches and the sorry ladder.** When landing a sorry-skeleton, write the sketch at
skeleton time — the sketch *is* the plan, and each `sorry` should correspond to a named step
of it. A skeleton whose sketch cannot be written is not ready to land.

**Synchronization.** When a proof strategy changes, the sketch changes in the same commit.
A sketch that describes a proof the code no longer performs is worse than no sketch.

## Review checklist

Before merging new Lean content, check:

1. Files follow the Area/Topic layout with a facade, and `TCSlib.lean` exports are updated.
2. Imports are precise; no bare `import Mathlib`.
3. Every file has a `## References` section; every source-derived declaration has a
   `[Tag, location]` in its docstring; deviations from sources are noted.
4. Every nontrivial proof (or sorry-stub standing in for one) has a proof sketch.
5. Every public declaration (instances and vendored files excepted) has a docstring
   opening with a natural-language statement of what it asserts
   (`python3 scripts/style_lint.py` checks presence mechanically; statement quality is
   review judgment).
6. `zsh scripts/lean_check.sh <file>` reports zero errors for each touched file.
7. If blueprint content was touched: `python3 scripts/blueprint_validate.py --strict` and
   `python3 scripts/dataset_hygiene.py --strict` pass.
8. No new private host: every search, recursion, interpreter, runner or input device the
   change introduces is a registered public host, or cites one (§1, **Hosts come first**).

## ===== briefs/lattice-gsw/rulings.md =====

# GSW phase 5 · rulings Q1–Q16 (Seyoon, 2026-11-16)

Seyoon accepted all sixteen recommendations in [questions.md](questions.md), with one change to **Q9**.

- **Q9 (changed): the module location is a new top-level folder.** The modules live at
  `TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/{Gadget,Noise,Scheme,Eval,Security,Symmetric}.lean`.
  - The namespace is `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW`.
  - The facades are `AdvancedEncryption.lean`, `AdvancedEncryption/Homomorphic.lean` and `…/Homomorphic/GSW.lean`.
  - Seyoon's reason: homomorphic encryption is a very different beast from SKE and PKE, so it does not belong under
    `Encryption/`.
  - The column leftover-hash lemma stays at `Hashing/SIS/Columns.lean`, as Q9-A proposed.
- **Accepted as recommended:**
  - Q1 (A): the `DAGCircuit` via `runWith`.
  - Q2 (A): the small owner-side PR to `DAGCircuit.lean` (depth readers and `runWith_rel`).
  - Q3 (A): regime-agnostic, concrete statements.
  - Q4 (A): a public-key headline, plus the optional secret-key unit F7.
  - Q5 (A): worst-case, every-coin correctness.
  - Q6 (A): decryption through the `C·G⁻¹(⌊q/2⌋·e_{n+1})` column with `Regev.decrypt`.
  - Q7 (A): the product-chain lemma is in phase 5.
  - Q8 (A): concrete hybrids now; the `NUPPT` bridge later.
  - Q10 (A): reuse `Lossy.gadget` in place.
  - Q11 (A): a GSW-local `columnHashParameters`, disclosed.
  - Q12 (A): BV14 for phase 7.
  - Q13 (A): Barrington as its own complexity unit.
  - Q14 (A): ingest GSW13 in the statement PR.
  - Q15 (A): weak circular security as an explicit hypothesis.
  - Q16 (A): the LWE gap as a ratio predicate.

**Next:**
1. Move the drafts to the ruled paths and namespace.
2. Compile them in Lean, one module at a time, when an olean tree is free.
3. Open two PRs: the `DAGCircuit.lean` owner PR (Q2) and the GSW statement PR (phase 5).
4. Stage a Codex statement gate for each.

The PDFs still needed for later phases are Barrington (JCSS 1989) and BV11 (FOCS 2011 / ePrint 2011/344), and ACPS09
only if small-secret LWE is to be proved rather than assumed.

## Addendum (Seyoon, 2026-11-16)
- **Sources received; the PDFs are not committed.**
  - Barrington, "Bounded-Width Polynomial-Size Branching Programs Recognize Exactly Those Languages in NC¹",
    JCSS 38(1):150–164, 1989. It is a 15-page scan with no text layer, so read it as page images.
    SHA-256 `06fd3eeccecf8e3e42c0e33f50356588ea9377b2f7d2642b4d3e0370f4ca7831`.
  - Brakerski–Vaikuntanathan, "Efficient Fully Homomorphic Encryption from (Standard) LWE", FOCS 2011, 39 pages.
    SHA-256 `d3e95f9b9e017ea1133064bed227981ec21e38ee6fc6163eb08585dd238b0c00`.
- **ACPS09 is not needed now.** Seyoon is happy to **assume small-secret LWE** for now, and to prove the equivalences
  with standard LWE later. Phase plans state small-secret (normal-form) LWE as an explicit assumption (A3) wherever
  it is used.

## ===== briefs/lattice-gsw/questions.md =====

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

## ===== briefs/lattice-gsw/plan-section.md =====

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
- `TCSlib/Cryptography/Encryption.lean` gains `import TCSlib.Cryptography.Encryption.Homomorphic`.
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
7. **Cross-topic import.** `Encryption/Homomorphic` imports
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
| `Encryption/Homomorphic/GSW/` | Gadget and `G⁻¹`, noise invariant, public-key and secret-key GSW, circuit evaluation, leveled correctness, IND-CPA hybrids |

The phase table gains one row:

| Phase | Frozen surface to prepare | Fill starts only after |
|---|---|---|
| 5 | GSW gadget/`G⁻¹`, `Encrypts` algebra (asymmetric product, chains), PK GSW, `DAGCircuit` evaluation, leveled correctness, concrete IND-CPA; shared `runWith_rel` and depth readers | GSW statement gate and Seyoon's approval of the shared `DAGCircuit.lean` change |

Proposed decision-log row:

| Date | Decision/evidence | Status |
|---|---|---|
| 2026-11-16 | Seyoon approves GSW as a new phase of the lattice campaign, run by the maintainer, with PRs to `cryptography/pass-shelat-ch2-4`. The scope is leveled GSW, depth-`L` correctness with the explicit bound `(N+1)^L·mB`, and IND-CPA from DLWE. The FHE target sequence is recorded: phase 6 bootstrapping under explicit weak circular security, and phase 7 polynomial-ratio bootstrapping (BV14 or AP14). The design brief and draft statements are under `briefs/lattice-gsw/`; nothing has been elaborated. | Design only; statement gate and questions pending |

## ===== briefs/lattice-gsw/statement-phase/EVIDENCE.md =====

# GSW phase-5 statements: evidence

Branches (local, not pushed), from `523d80d2d4dd8e4ed6799358831e5b3806c6187b`:
- `stmt/dagcircuit-readers` `94eae71b779c4ca0f76c138d699f4d737dbd6cee`: `DAGCircuit.lean` +94 lines (Q2): readers
  `DAGGate.depth_eq`, `DAGCircuit.{depths_eq, depthAt_eq, depth_eq}`; `DAGGate.getD_lt_depth` and `runWith_rel`, both
  **proved**.
- `stmt/gsw` `48d796a8a68cd50897047f01825a8132dd19e8d8` on top of it: `8ce56b0d0b5175e6001e1b18a6777f07194e944d`
  (modules and facades) and the exports commit (`Hashing/SIS.lean`, `TCSlib.lean`).

Evidence: `$SP/dl-review/stmt-gsw.zip`, SHA-256 `4b144e17683c3675088a620796bd21e9963d8a43a489145208efda9c5c1f85d3`
(`PROVENANCE.txt`, `SHA256SUMS`, `unchecked-fixes.md`, `questions-statement-changes.md` inside; not committed).
Method as for the pairing statements (`../../pairings/statement-phase/EVIDENCE.md`): one Lean process at a time on
`$SP/dl-oleans-2` only, `scripts/lean_check_tree.sh`, no `lake build`, `python3 -I`.

| Step | Result |
|---|---|
| Files | `AdvancedEncryption/Homomorphic/GSW/{Gadget 204, Noise 235, Scheme 215, Eval 207, Security 217, Symmetric 111}`, `Hashing/SIS/Columns` 89; facades `AdvancedEncryption` 25 (imports only `Homomorphic`), `AdvancedEncryption/Homomorphic` 22, `Homomorphic/GSW` 35; widths at most 100 |
| Build | 33 closure modules rebuilt (21 stale base); final sweep 12/12 rc 0, 0 errors; only the 35 target `sorry`s (Gadget 5, Noise 12, Scheme 6, Eval 4, Columns 2, Security 4, Symmetric 2) |
| Axioms | 285 declarations + 56 auxiliary constants (GSW and Columns 124 + 8); `sorryAx` in exactly the 35 targets; all else standard |
| `UNCHECKED` | 23 markers, all verified as drafted and removed; 4 other fixes (2 statement texts, meaning unchanged: QS1 `Matrix.of` in `hashColumns_eq_mul`; QS2 `GSW.mul` in `Encrypts.mul_bit`/`mul_le`; 2 sketch citations); the facade's missing `-/` |
| Rule 10 | whole-file seals A/B, strict and coe, `-DmaxErrors=0`, 12 files: 48/48 pass; controls: 5/5 sealed negatives fail once each, unsealed and positive pass |
| Lint | `style_lint.py` 0 findings (12 files); `campaign_style_lint.py --check8b` 0 FAIL / 0 WARN (AdvancedEncryption, Hashing); DAGCircuit's check-8 WARN loses `depths` |
| Root `TCSlib` | 278 modules rebuilt (DAGCircuit and Hashing.SIS downstream, GSW): 278/278 rc 0 |
| Tree | snapshot `457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f` before and after (byte-identical) |

Open: GSW13 ingestion (Q14) is not in these branches. The records branch advanced to `a32ad0df` during the job
(#318, #319, #323): all three branches merge cleanly; the only closure overlap is #323's `isFaninTwo_iff` in
`DAGCircuit.lean`, a disjoint hunk.

**Filed (Gate 41, 2026-11-16).** The archive is now in the records at `evidence/stmt-gsw.zip` (SHA-256
`4b144e17683c3675088a620796bd21e9963d8a43a489145208efda9c5c1f85d3`), byte-identical, with its inner manifest
`evidence/SHA256SUMS` (545 files, all verified) and `evidence/PROVENANCE.txt`.

## ===== briefs/lattice-gsw/gates/41-gsw-statements/source-excerpts/GSW13-excerpts.md =====

# GSW13: excerpts of the passages used (Gate 41)

**Reference.** C. Gentry, A. Sahai, B. Waters, *Homomorphic Encryption from Learning with Errors: Conceptually-Simpler, Asymptotically-Faster, Attribute-Based*, CRYPTO 2013; author version dated 8 June 2013 (25 pp.).

**Extraction.** `pdftotext -layout` (poppler) of the uploaded PDF, SHA-256 `8edb94cfd852a88a8684adbf81b73e78bd21466514b7bb7000d7df1e4431bf00` (checked when this file was written); line numbers are those of the extracted text. The PDF itself is not committed (pairing ruling Q12; GSW ruling Q14 and the plan-section provenance). Only the passages below are quoted. Mathematical layout (sub- and superscripts, fraction bars) is flattened by the extraction; read formulas against the Lean statements and the PDF where needed.

**Passages.**

- lines 1–5: title
- lines 167–286: §1.3.1–§1.3.4: homomorphic operations, error bounds, flattening, BitDecomp / Powersof2, key generation and encryption
- lines 374–579: §2.3, §3.1 (Setup, SecretKeyGen, PublicKeyGen, Enc, Dec, MPDec), §3.2 (security, Lemma 1), §3.3 (MultConst, Add, Mult, NAND, "Circuits") and §3.4 (parameters, q/B > 8(N+1)^L, Theorem 3)

## Lines 1–5: title

```text
        Homomorphic Encryption from Learning with Errors:
     Conceptually-Simpler, Asymptotically-Faster, Attribute-Based
                          Craig Gentry∗                Amit Sahai†               Brent Waters‡

                                                      June 8, 2013
```

## Lines 167–286: §1.3.1–§1.3.4: homomorphic operations, error bounds, flattening, BitDecomp / Powersof2, key generation and encryption

```text
1.3     An Overview of Our FHE Scheme
Our main insight is that we can achieve LWE-based homomorphic encryption where homomorphic
addition and multiplication correspond directly to matrix addition and multiplication.

1.3.1     Homomorphic Operations
Let us skip key generation and encryption for the moment, and jump directly to the homomorphic
operations (and decryption).
    In our scheme, for some modulus q and dimension parameter N to be specified later, a ciphertext
C is a N × N matrix over Zq , with “small” entries (much smaller than q) and the secret key ~v is a
N -dimensional vector over Zq with at least one “big” coefficient vi . We restrict the message µ to
be a “small” integer. We say C encrypts µ when C · ~v = µ · ~v + ~e, where ~e is a “small” error vector.
To decrypt, we extract the i-th row Ci from C, compute x ← hCi , ~v i = µ · vi + ei , and output
µ = bx/vi e. In a nutshell, the essence of our scheme is that the secret key ~v is an approximate
eigenvector of the ciphertext matrix C, and the message µ is the eigenvalue.
    Now, let us see why matrix addition and multiplication are correct homomorphic operations.
Suppose C1 and C2 encrypt µ1 and µ2 in that Ci · ~v = µi · ~v + ~ei for small ~ei . Let C + = C1 + C2
and C × = C1 · C2 . For addition, we have C + · ~v = (µ1 + µ2 ) · ~v + (~e1 + ~e2 ), where the error likely
has grown a little, as usual in FHE schemes. But assuming the error is still “small”, the sum of
the ciphertext matrices encrypts the sum of the messages. For multiplication, we have

        C × · ~v = C1 · (µ2 · ~v + ~e2 ) = µ2 · (µ1 · ~v + ~e1 ) + C1 · ~e2 = µ1 · µ2 · ~v + µ2 · ~e1 + C1 · ~e2
                 = µ1 · µ2 · ~v + small

where the final error vector is hopefully “small”, since µ2 , C1 , ~e1 , and ~e2 are all small. If so, the
product of the ciphertext matrices encrypts the product of the messages. Interestingly, C2 · C1 is
also an encryption of µ1 · µ2 , even though matrix multiplication is not commutative.
    To simplify further, it might be helpful to imagine an error-free version of the scheme, where
Ci · ~v = µi · ~v exactly. In this case, the key ~v is an (exact) eigenvector of ciphertext matrices, and
the message µi is the eigenvalue. In general, if matrices C1 and C2 have a common eigenvector ~v
with eigenvalues µ1 and µ2 , then C1 · C2 and C2 · C1 have eigenvector ~v with eigenvalue µ1 · µ2 .


                                                           4

[page break]
    Of course, in our scheme, the secret key ~v is only an approximate eigenvector, not an exact one.
Introducing error is necessary to base the security of our scheme on LWE. The cost of making ~v
only an approximate eigenvector is that certain terms in our scheme must be “small” to ensure
that homomorphic operations do not disrupt the essential form of the ciphertexts. We call our new
approach to LWE-based (homomorphic) encryption the approximate eigenvector method.

1.3.2     Bounding the Error and Somewhat Homomorphic Encryption
Although we have not fully specified the scheme, let us go ahead and estimate how homomorphic
it is. The scheme above works correctly until the coefficients of the error vector begin to approach
q in magnitude. How many homomorphic operations can we perform before that happens?
     Suppose C1 and C2 are B-bounded ciphertexts, in the sense that µi and the coefficients of Ci
and ~ei all have magnitude at most some bound B. Then, C + is 2B-bounded, and C × is (N + 1)B 2 -
                                                         L
bounded. In short, the error level grows worse than B 2 , doubly exponentially with the multiplicative
depth L of the circuit being evaluated. Alternatively, if one wants to consider the degree (rather than
depth) of functions that can be evaluated, if we evaluate a multivariate polynomial P (x1 , . . . , xt ) of
total degree d, on B-bounded ciphertexts as input, the final ciphertext is |P |(N +1)d−1 B d -bounded,
where |P | is the `1 -norm of P ’s coefficient vector. Taking q to comfortably exceed this bound, we
(roughly) can evaluate polynomials of degree logN B q. Since q/B must be subexponential (at most)
in N for security reasons, our scheme-so-far can only evaluate polynomials of (sublinear) polynomial
degree in N (only logarithmic depth). In short, our scheme-so-far is a somewhat homomorphic
encryption (SWHE) scheme [Gen09] that can evaluate log-depth or polynomial degree. Though
not yet fully homomorphic, it is by far the most homomorphic LWE-based encryption scheme that
uses only “natural” homomorphic operations.

1.3.3     Flattening Ciphertexts and Fully Homomorphic Encryption
To obtain a leveled FHE scheme that can evaluate circuits of polynomial depth without bootstrap-
ping or techniques like relinearization, we need to ensure better bounds on the growth of the error.
Let us say that a ciphertext C is B-strongly-bounded if its associated µ and the coefficients of
C all have magnitude at most 1, while the coefficients of its ~e all have magnitude at most B. If
we evaluate a NAND gate on B-strongly-bounded ciphertexts C1 , C2 to obtain a new ciphertext
C3 ← IN − C1 · C2 (where IN is the N -dimensional identity matrix), then the message remains in
{0, 1}, and the coefficients of C3 ’s error vector have magnitude at most (N + 1)B. If we could some-
how additionally ensure that C3 ’s coefficients have magnitude at most 1 so that strong-boundedness
is preserved, then we could evaluate a circuit of depth L while keeping the error magnitude at most
(N + 1)L B. Setting q/B to be subexponential in N , we could evaluate a circuit of polynomial depth
rather than merely polynomial degree. In short, we would have a leveled FHE scheme.
     Here we describe a operation called ciphertext flattening that keeps ciphertexts strongly bounded,
so that we obtain leveled FHE.
     Flattening uses some simple transformations from [BV11b, BGV12, Bra12] that modify vectors
without affecting dot products. Let ~a, ~b be vectors of some dimension k over Zq . Let ` = blog2 qc+1
and N = k · `. Let BitDecomp(~a) be the N -dimensional vector (a1,0 , . . . , a1,`−1 , . . . , ak,0 , . . . , ak,`−1 ),
where ai,j is the j-th bit in ai ’s binary representation, bits ordered least significant                  to most signif-
icant. For ~a0 = (a1,0 , . . . , a1,`−1 , . . . , ak,0 , . . . , ak,`−1 ), let BitDecomp−1 (~a0 ) = ( 2j · a1,j , . . . , 2j ·
                                                                                                     P                   P
ak,j ) be the inverse of BitDecomp, but well-defined even when the input is not a 0/1 vector. For


                                                             5

[page break]
N -dimensional ~a0 , let Flatten(~a0 ) = BitDecomp(BitDecomp−1 (~a0 )), a N -dimensional vector with
0/1 coefficients. When A is a matrix, let BitDecomp(A), BitDecomp−1 , or Flatten(A) be the ma-
trix formed by applying the operation to each row of A separately. Finally, let Powersof2(~b) =
(b1 , 2b1 , . . . , 2`−1 b1 , . . . , bk , 2bk , . . . , 2`−1 bk ), a N -dimensional vector. Here are some obvious facts:
    • hBitDecomp(~a), Powersof2(~b)i = h~a, ~bi.
    • For any N -dimensional ~a0 , h~a0 , Powersof2(~b)i = hBitDecomp−1 (~a0 ), ~bi = hFlatten(~a0 ), Powersof2(~b)i.
 An interesting feature of Flatten is that it makes the coefficients of a vector or matrix small, without
 affecting its product with Powersof2(~b), and without knowing ~b.
     To facilitate ciphertext flattening, we give a special form to our secret key ~v . Specifically, we set
~v = Powersof2(~s) for some secret vector ~s (to be specified later). This form is consistent with our
 earlier requirement that ~v have some big coefficient vi for decryption; indeed, since ~v ’s coefficients
 go up by blog2 qc powers of 2, it must have a big coefficient suitable to recover µ ∈ {0, 1}.
     Now, for any N × N matrix C, we have Flatten(C) · ~v = C · ~v . So, after we compute an
 initial ciphertext C3 ← IN − C1 · C2 for the NAND gate, we set C NAND = Flatten(C3 ) to obtain a
 ciphertext that has 0/1 coefficients and is strongly bounded. Thus, we obtain leveled FHE without
 relinearization, under a fixed approximate eigenvector secret key.

1.3.4    Key Generation, Encryption, and Reduction to LWE
Let us finally circle back to key generation and encryption. We want to base security on LWE. So,
for key generation, we generate an LWE instance. For suitable parameters q, n, m = O(n log q), an
LWE instance over Zq consists of a m×(n+1) matrix A such that there exists a (n+1)-dimensional
vector ~s whose first coefficient is 1 where ~e = A · ~s is a “small” error vector. (See Section 2 for
a formal definition of LWE.) In our scheme, A is public and ~s is secret. We set our approximate
eigenvector to be ~v = Powersof2(~s), a vector of dimension N = (n + 1) · ` for ` = blog2 qc + 1.
    To encrypt µ ∈ Zq , the encrypter generates a random N × m matrix R with 0/1 entries, and
sets C = Flatten(µ · IN + BitDecomp(R · A)), where IN is the N -dimensional identity matrix. Since
Flatten does not affect the product with ~v , we have:

               C · ~v = µ · ~v + BitDecomp(R · A) · ~v = µ · ~v + R · A · ~s = µ · ~v + small

Flatten ensures that the coefficients of C are small, and therefore that C has the proper form of a
ciphertext that permits our homomorphic operations. Decryption works as mentioned previously.
    To show that security is based on LWE, it is now enough to show that C is statistically inde-
pendent of µ when A is a uniformly random m × (n + 1) matrix over Zq . Let C 0 = BitDecomp−1 (C).
Recall that C is Flatten’d, and so C = Flatten(C) = BitDecomp(C 0 ). Therefore, C reveals nothing
more than C 0 . But C 0 = BitDecomp−1 (µ · IN ) + R · A, and R · A is statistically uniform by the
leftover hash lemma when m = O(n log q) is chosen appropriately.
```

## Lines 374–579: §2.3, §3.1 (Setup, SecretKeyGen, PublicKeyGen, Enc, Dec, MPDec), §3.2 (security, Lemma 1), §3.3 (MultConst, Add, Mult, NAND, "Circuits") and §3.4 (parameters, q/B > 8(N+1)^L, Theorem 3)

```text
2.3   Other Preliminaries
For n, q, and ` = blog qc + 1, we define the procedures BitDecomp, BitDecomp−1 , Flatten and
Powersof2 as described in the Introduction. IN denotes the N -dimensional identity matrix.


3     Our LWE-Based FHE Scheme
3.1   Basic Encryption Scheme
Here, we formally describe our basic encryption scheme (without homomorphic operations). This
description matches the description outlined in the Introduction. In our description, we split
up KeyGen into three parts Setup, SecretKeyGen and PublicKeyGen. We provide two decryption
algorithms Dec and MPDec. Dec is sufficient to recover the message µ when it is in a small space
(e.g., {0, 1}). MPDec is an algorithm by Micciancio and Peikert [MP12] that can recover any µ ∈ Zq .

    • Setup(1λ , 1L ): Choose a modulus q of κ = κ(λ, L) bits, lattice dimension parameter n =
      n(λ, L), and error distribution χ = χ(λ, L) appropriately for LWE that achieves at least 2λ
      security against known attacks. Also, choose parameter m = m(λ, L) = O(n log q). Let
      params = (n, q, χ, m). Let ` = blog qc + 1 and N = (n + 1) · `.



                                                    8

[page break]
   • SecretKeyGen(params): Sample ~t ← Znq . Output sk = ~s ← (1, −t1 , . . . , −tn ) ∈ Zn+1
                                                                                         q   . Let
     ~v = Powersof2(~s).

   • PublicKeyGen(params, sk): Generate a matrix B ← Zm×n   q    uniformly and a vector ~e ← χm .
     Set ~b = B · ~t + ~e. Set A to be the (n + 1)-column matrix consisting of ~b followed by the n
     columns of B. Set the public key pk = A. (Remark: Observe that A · ~s = ~e.)

   • Enc(params, pk, µ): To encrypt a message µ ∈ Zq , sample a uniform matrix R ∈ {0, 1}N ×m
     and output the ciphertext C given below.

                                                                         ×N
                              C = Flatten µ · IN + BitDecomp(R · A) ∈ ZN
                                                                   
                                                                       q    .

   • Dec(params, sk, C): Observe that the first ` coefficients of ~v are 1, 2, . . . , 2`−1 . Among these
     coefficients, let vi = 2i be in (q/4, q/2]. Let Ci be the i-th row of C. Compute xi ← hCi , ~v i.
     Output µ0 = bxi /vi e.

   • MPDec(params, sk, C) (for q a power of 2): Observe that q = 2`−1 and the first ` − 1
     coefficients of ~v are 1, 2, . . . , 2`−2 , and therefore if C · ~v = µ · ~v + small, then the first ` − 1
     coefficients of C · ~v are µ · ~g + small, where ~g = (1, 2, . . . , 2`−2 ). Recover LSB(µ) from
     µ · 2`−2 + small, then recover the next-least-significant-bit from (µ − LSB(µ)) · 2`−3 + small,
     etc. (See [MP12] for the general q case.)

   Dec is a BitDecomp’d version of Regev’s decryption procedure, applied to one row of the cipher-
text, which is a BitDecomp’d Regev ciphertext. (The extra rows will come into play in the homo-
morphic operations). If C is properly generated, then by the elementary properties of BitDecomp
and Powersof2, we have

                               C · ~v = µ · ~v + R · A · ~s = µ · ~v + R · ~e.

Dec only uses the i-th coefficient of the above expression, which is xi = µ · vi + hRi , ~ei. The error
hRi , ~ei has magnitude at most k~ek1 . In general, if xi = µ · vi + e0 for some error e0 of magnitude at
most q/8, and if vi ∈ (q/4, q/2], then xi /vi differs from µ by at most (q/8)/vi < 1/2, and Dec uses
rounding to output the correct value of µ. (In the basic scheme, we set χ to ensure that the error
is so bounded with overwhelming probability.)
    For the basic scheme (without homomorphic operations), one can take n to be quasi-linear in
the security parameter λ and κ = O(log n). When allowing homomorphic operations, L repre-
sents the circuit complexity of the functions that the scheme correctly evaluates (roughly, L is the
multiplicative depth); we provide a detailed analysis later of how L affects the other parameters.

3.2   Security
Observe that BitDecomp−1 (C) = µ · G + R · A, where G = BitDecomp−1 (IN ) is (the transpose
of) the “primitive matrix” used by Micciancio and Peikert [MP12] in their construction of lattice
trapdoors, and the rows of R · A are simply Regev [Reg05] encryptions of 0 for dimension n.
Assuming BitDecomp−1 (C) hides µ, C does as well, since C can be derived by applying BitDecomp.
Thus, the security of our basic encryption scheme follows directly from the following lemma, used
to prove the security of Regev’s encryption scheme [Reg05].


                                                        9

[page break]
Lemma 1 (Implicit in [Reg05]). Let params = (n, q, χ, m) be such that the LWEn,q,χ assumption
holds. Then, for m = O(n log q) and A, R as generated above, the joint distribution (A, R · A) is
                                                     m×(n+1)    N ×(n+1)
computationally indistinguishable from uniform over Zq       × Zq        .
    Concretely, it suffices to take m > 2n log q [Reg05].
    Like Brakerski [Bra12], we can also base security on GapSVP via a classical reduction from
LWE [Pei09, BLP+ 13]. Specifically, Peikert [Pei09] gives a classical reduction of GapSVP to LWE,
with the caveat that q must be exponential in n. Brakerski notes that exponential q was unusable
in previous FHE schemes, since the ratio of q to the error level B of “fresh” ciphertexts cannot be
exponential in n for security reasons (since LLL [LLL82] could be used to break such a scheme), and
since B must be very small to permit many homomorphic operations. As in Brakerski’s scheme,
we do not have that problem. The error bound B of fresh ciphertexts in our scheme does not need
to be small to permit many homomorphic operations; we only require q/B to be sub-exponential,
and we can therefore permit q to be exponential. Alternatively, we can use a sub-exponential q and
base security on GapSVP via Brakerski et al.’s [BLP+ 13] recent classical reduction to LWE that
works even for polynomial-size moduli, with the caveat that, in their reduction, the dimension of
the GapSVP instances may be much smaller than the dimension of the LWE instances.

3.3   Homomorphic Operations
Recall that we already described some basic “homomorphic” operations BitDecomp, BitDecomp−1 ,
Flatten, and Powersof2. These will play an important role in analyzing the homomorphic operations
supported by our scheme. We remark that BitDecomp could alternatively decompose with respect
to bases other than 2, or according to the Chinese Remainder Theorem.
    We provide additional homomorphic operations MultConst, Add, Mult, NAND as follows.
   • MultConst(C, α): To multiply a ciphertext C ∈ ZN   ×N by known constant α ∈ Z , set M ←
                                                      q                           q       α
     Flatten(α · IN ) and output Flatten(Mα · C). Observe that:
              MultConst(C, α) · ~v = Mα · C · ~v = Mα · (µ · ~v + ~e) = µ · (Mα · ~v ) + Mα · ~e
                                       = α · µ · ~v + Mα · ~e
      Thus, the error increases by a factor of at most N , regardless of what element α ∈ Zq is
      used for multiplication. As in “classical” additively homomorphic encryption schemes, we
      could alternatively perform multiplication-by-constant α by recursively applying Add. But
      this multiplies the error size by at least α, whereas MultConst increases the error by at most
      a factor of N , regardless of α. An example application of MultConst is that we can perform
      homomorphic fast Fourier transformations (FFTs) natively over Zq without error growth
      dependent on q. Previously, the error growth depended on the size of the field underlying the
      FFT [GHS12a, GHS12b], restricting the choice of field.
   • Add(C1 , C2 ): To add ciphertexts C1 , C2 ∈ ZN ×N , output Flatten(C + C ). The correctness
                                                  q                      1   2
     of this operation is immediate. Note that the addition of messages is over the full base ring
     Zq .
   • Mult(C1 , C2 ): To multiply ciphertexts C1 , C2 ∈ ZN ×N , output Flatten(C · C ). Observe that:
                                                        q                      1   2

              Mult(C1 , C2 ) · ~v = C1 · C2 · ~v = C1 · (µ2 · ~v + ~e2 ) + µ2 · (µ1~v + ~e1 ) + C1 · ~e2
                                  = µ1 · µ2 · ~v + µ2 · ~e1 + C1 · ~e2

                                                      10

[page break]
      As in Add, the multiplication operator is over the full base field Zq . In Mult, the new error
      depends on the old errors, the ciphertext C1 , and the message µ2 . The dependence on the
      old errors seems unavoidable (and normal for LWE-based HE schemes), and observe that C1
      contributes at most a factor N blowup of error, since all components of C1 are restricted to
      {0, 1}. The error growth based on the message µ2 , however, presents a concern. In general,
      we must address this concern by using homomorphic operations in a way that restricts the
      message space to small messages. One way to do this is to consider Boolean circuits using
      only NAND operations: this would restrict the message space to {0, 1}. We elaborate below.

   • NAND(C1 , C2 ): To NAND ciphertexts C1 , C2 ∈ ZN      ×N that are known to encrypt messages
                                                         q
     µ1 , µ2 ∈ {0, 1}, output Flatten(IN − C1 · C2 ). Observe that:

             NAND(C1 , C2 ) · ~v = (IN − C1 · C2 ) · ~v = (1 − µ1 · µ2 ) · ~v − µ2 · ~e1 − C1 · ~e2

      Note here that the NAND homomorphic operation maintains the invariant that if the input
      messages are in {0, 1}, then the output ciphertext will also encryption of {0, 1}, thus guar-
      anteeing small messages. Note that since µ2 ∈ {0, 1}, the error is increased by a factor of at
      most N + 1.

Circuits. By iteratively applying the homomorphic operations above, different types of (bounded-
depth) circuits may be homomorphically computed while maintaining correctness of decryption.
    The simplest case to analyze is the case of Boolean circuits computed over encryptions of
{0, 1} values. In this case, the circuit can be converted to use only NAND gates, and through
appropriate leveled application of the NAND homomorphic operation, the final ciphertext’s error
will be bounded by (N + 1)L · B, where L is the NAND-depth of the circuit, and B is the original
bound on the error of a fresh encryption of {0, 1}.
    More generally, with more care, we may consider arithmetic circuits over Zq that make use of
gates that perform addition, multiplication, or multiplication by a known constant. However, as
we have seen in the case of multiplication gates, the error growth may depend on the values being
encrypted in intermediate computations. One way to deal with this is to focus on situations where
(1) all input values are known to encrypt values bounded by some value T , and (2) the arithmetic
circuit is chosen to guarantee that all intermediate values are also bounded by T 0 whenever the
circuit inputs are constrained to values bounded by T . In such a situation, the final ciphertext’s
error will be bounded by (N + T 0 )L · B, where L is the depth of the arithmetic circuit, and B is the
original bound on the error of fresh encryptions of values smaller than T . For example, in this way,
we can homomorphically evaluate polynomials of degree d in this large-message-space variant when
the initial messages are bounded by roughly q 1/d , achieving a scheme that is “somewhat homomor-
phic” [Gen09]. Another example application would be to convert encryptions of a polynomially
bounded set of small values to encryptions of binary values, by using an appropriate arithmetic
circuit for the conversion. Once converted to encryptions of binary values, a NAND-based Boolean
circuit could be used for further computations.

3.4   Parameters, Performance and Optimizations
Suppose that Flatten’d ciphertexts C1 , C2 encrypt µ1 , µ2 ∈ {0, 1} under approximate eigenvector ~v
with B-bounded error – that is, Ci · ~v = µi · ~v + ~ei where |~ei |∞ ≤ B. Then C NAND ← NAND(C1 , C2 )
encrypts NAND(µ1 , µ2 ) ∈ {0, 1} under ~v with (N +1)B-bounded error. As long as q/B > 8(N +1)L ,

                                                     11

[page break]
we can evaluate a depth-L circuit of NANDs over B-bounded ciphertexts to obtain a q/8-bounded
ciphertext, which Dec will decrypt correctly.
    As in previous LWE-based FHE schemes, n (hence N ) must increase linearly with log(q/B) to
maintain fixed 2λ security against known attacks, so q/B grows more like exp(L log L). We will
brush such issues under the rug and view n as a fixed parameter. Choosing χ so that B is not too
large, and since in practice there is no reason to have κ = log q grow super-linearly with n, we have
κ = O(L log N ) = O(L(log n + log κ)) = O(L log n), similar to [BGV12, Bra12]. Given that the
NAND procedure is dominated by multiplication of two N × N matrices for N = O(nκ) = Õ(nL),
we have the following theorem to characterize the performance of our FHE scheme.

Theorem 3. For dimension parameter n and depth parameter L, our FHE scheme evaluates depth-
L circuits of NAND gates with Õ((nL)ω ) field operations per gate, where ω < 2.3727 is the matrix
multiplication exponent.

This compares favorably with previous LWE-based FHE schemes, which all have at least Õ(n3 L)
field operations per gate [BV11b, BGV12, Bra12].
    Theorem 3 hides some factors, both good and bad. On the good size, it hides the fact that
ciphertext matrices in our scheme have 0/1 entries, and therefore can be multiplied faster than
if they were general matrices over Zq . In previous LWE-based FHE schemes, the field operations
involve multiplying a small number with a general number of Zq , which has complexity Õ(κ) =
Õ(L). So, previous LWE-based FHE schemes have real complexity Õ(n3 L2 ) whereas ours remains
Õ((nL)ω ). On the bad side, Theorem 3 hides logarithmic factors in the dimension of the ciphertext
matrices, since N = O(nκ) = O(nL log n). We note that typically n will dominate L, since for
very deep circuits, one would want to use Gentry’s bootstrapping technique [Gen09] to make the
per-gate computation independent of L.
    Since bootstrapping involves homomorphically evaluating the decryption function, and since
Dec is essentially Regev decryption [Reg05], bootstrapping works as in previous LWE-based FHE
schemes. In particular, we can use techniques from [BV11b] to reduce the dimension and modulus-
size of the ciphertext before bootstrapping, so that the complexity of decryption (and hence boot-
strapping) is completely independent of the depth L of the circuit that was evaluated to arrive
at that ciphertext. Regev decryption can be evaluated in O(log n) depth. Due to the logarithmic
depth, one can take q/B to be quasi-polynomial in n, and base security on LWE for quasi-polynomial
factors.
```

## ===== briefs/lattice-gsw/gates/41-gsw-statements/source-excerpts/AP14-excerpts.md =====

# AP14: excerpts of the passages used (Gate 41)

**Reference.** J. Alperin-Sheriff, C. Peikert, *Faster Bootstrapping with Polynomial Error*, CRYPTO 2014; IACR ePrint 2014/094, version dated 13 June 2014 (18 pp.).

**Extraction.** `pdftotext -layout` (poppler) of the uploaded PDF, SHA-256 `cecd346d2e879ff865c23fe977e172e1068f20b01c7f555a419d2f3d5ec2c0da` (checked when this file was written); line numbers are those of the extracted text. The PDF itself is not committed (pairing ruling Q12; GSW ruling Q14 and the plan-section provenance). Only the passages below are quoted. Mathematical layout (sub- and superscripts, fraction bars) is flattened by the extraction; read formulas against the Lean statements and the PDF where needed.

**Passages.**

- lines 1–3: title
- lines 326–483: §3: §3.1 (gadget g, Claim 3.1, Equation (3.1)), §3.2 (the GSW variant: Gen, Enc, Dec, the operations, IND-CPA remark), §3.3 (Definitions 3.2–3.3, Claim 3.4, Lemma 3.5, Corollary 3.6)
- lines 484–581: §4 to Corollary 4.2: Equation (4.1) (cited by `Encrypts.sum`) and the permutation-matrix chains (phase-7 roadmap, ruled Q12 for BV14)

## Lines 1–3: title

```text
                       Faster Bootstrapping with Polynomial Error
                                    Jacob Alperin-Sheriff∗                   Chris Peikert†
```

## Lines 326–483: §3: §3.1 (gadget g, Claim 3.1, Equation (3.1)), §3.2 (the GSW variant: Gen, Enc, Dec, the operations, IND-CPA remark), §3.3 (Definitions 3.2–3.3, Claim 3.4, Lemma 3.5, Corollary 3.6)

```text
3        GSW Cryptosystem
Here we present a variant of the Gentry-Sahai-Waters homomorphic encryption scheme [GSW13] (hereafter
called GSW), which we believe is simpler to understand at a technical level. We also give a tighter analysis
of its error growth under homomorphic operations.
    3
        This is just a special case of Cayley’s theorem, which saysPthat any group G embeds into the symmetric group S|G| .
    4
        The latter group can be seen as a subgroup of Sr for r = i ri , but it will be more efficient to retain the product structure.




                                                                     6

[page break]
3.1   Background
We first recall some standard background (see, e.g., [MP12] for further details). For a modulus q, let
` = dlog2 qe and define the “gadget” (column) vector g = (1, 2, 4, . . . , 2`−1 ) ∈ Z`q . Note that the penultimate
entry 2`−2 of g is in the interval [q/4, q/2) mod q. It will be convenient to use the following randomized
“decomposition” function.

Claim 3.1 (Adapted from [MP12]). There is a randomized, efficiently computable function g−1 : Zq → Z`
such that x ← g−1 (a) is subgaussian with parameter O(1), and always satisfies hg, xi = a.

     Briefly, the algorithm described in the claim works as follows (though for our application it is not necessary
to understand its internals): let S ∈ Z`×` be the basis of the lattice Λ⊥ (gt ) = {z ∈ Z` : hg, zi = 0 ∈ Zq }
as constructed in [MP12], whose Gram-Schmidt vectors all have Euclidean norm O(1). Given a ∈ Zq ,
run a randomized version of the nearest-plane algorithm [Bab85] with basis S to sample from the coset
Λ⊥    t
  a (g ) = {x : hg, xi = a}, where in each iteration of the algorithm we choose the coefficient of the ith
basis vector to have expectation zero over {ci − 1, ci } for an appropriate ci ∈ 1q Z ∩ [0, 1). In particular, the
                                              √
coefficient is subgaussian with parameter 2π given any fixed values of the previous coefficients. The final
output x is the linear combination of the (orthogonal) Gram-Schmidt vectors of S with these coefficients, and
is therefore subgaussian with parameter O(1).
     For vectors and matrices over Zq , define the randomized function G−1 : Zn×m     q     → Zn`×m by apply-
ing g−1 independently to each entry. Notice that for any A ∈ Zn×m         q   , if X ← G−1 (A) then X has
subgaussian parameter O(1) and

                     G · X = A,       where G = gt ⊗ In = diag(gt , . . . , gt ) ∈ Zqn×n`                    (3.1)

is the block matrix with n copies of gt as diagonal blocks, and zeros elsewhere.

3.2   Cryptosystem and Homomorphic Operations
The GSW scheme is parameterized by a dimension n, a modulus q with ` = dlog2 qe, and some error
distribution χ over Z which we assume to be subgaussian. Formally, the message space is the ring of
integers Z, though for bootstrapping we only work with ciphertexts encrypting messages in {0, 1} ⊂ Z. The
ciphertext space is C = Zn×n`
                         q     . For simplicity we present just a symmetric-key scheme, which is sufficient for
our purposes (it can be converted to a public-key or even attribute-based scheme, as described in [GSW13]).
    Our GSW variant differs from the original scheme described in [GSW13] in two main ways:

   1. In [GSW13], a ciphertext is a square binary matrix C ∈ {0, 1}n` , a secret key is a “structured” mod-q
      vector s ∈ Zn`
                  q (having large entries), and s is an “approximate mod-q eigenvector” of C, in the sense
      that s C ≈ µst (mod q), where µ ∈ Z is the message.
            t

       In our variant, a ciphertext is a rectangular mod-q matrix C ∈ Zn×n`
                                                                       q     , a secret key is some (unstructured,
       short) integer vector s ∈ Zn , and st C ≈ µ · st G (mod q), i.e., s and Gt s are corresponding left- and
       right- “approximate singular vectors” of C.
      The difference between these two variants turns out to be purely syntactic, in that we can efficiently
      and “losslessly” switch between them (without needing the secret key). However, we believe that our
      variant leads to simpler notation and easier-to-understand operations and analysis.



                                                         7

[page break]
   2. The second difference is more substantial: our homomorphic multiplication procedure uses the
      randomized G−1 (·) operation from Claim 3.1. This yields a few important advantages, such as a very
      tight and simple error analysis using subgaussianity (see Lemma 3.5), and the ability to completely
      re-randomize the error in a ciphertext (see Corollary 3.6).

We now describe the scheme formally.

GSW.Gen(): choose s̄ ← χn−1 and output secret key s = (s̄, 1) ∈ Zn .
                                                      (n−1)×n`
GSW.Enc((s̄, 1), µ ∈ Z): choose C̄ ← Zq                          and e ← χm , let bt = et − s̄t C̄ (mod q), and output
    the ciphertext                                          
                                                            C̄
                                                        C=     + µG ∈ C,
                                                            bt
       where G is as defined in Equation (3.1). Notice that st C = et + µ · st G (mod q).
GSW.Dec(s, C ∈ C): let c be the penultimate column of C, and output µ = bhs, cie2 , where b·e2 : Zq →
    {0, 1} indicates whether its argument is closer modulo q to 0 or to 2`−2 (the penultimate entry of g).5
Homomorphic addition is defined as C1 ‘ C2 = C1 + C2 .
Homomorphic multiplication is defined as C1 d C2 ← C1 · G−1 (C2 ), and is right associative. Notice
    that this is a randomized procedure, because G−1 is randomized.

    The IND-CPA security of the scheme follows immediately from the assumed hardness of LWEn−1,q,χ ,
where the entries of the secret are drawn from the error distribution χ (which is no easier than for a uniformly
random secret; see [ACPS09, Lemma 2]). This is because a fresh ciphertext is just µG plus a matrix of n`
independent LWE samples under secret s̄, which are pseudorandom by assumption and hence hide µG.

3.3    Analysis
Here we analyze the scheme’s correctness and homomorphic operations.

Definition 3.2. We say that a ciphertext C is designed to encrypt message µ ∈ Z (under a secret key s) if it
is a fresh encryption of µ, or if C = C1 ‘ C2 where C1 , C2 are respectively designed to encrypt µ1 , µ2 ∈ Z
and µ = µ1 + µ2 , or similarly for homomorphic multiplication.

Definition 3.3. We say that a ciphertext C that is designed to encrypt µ ∈ Z (under s) has error vector
et ∈ Zn` if st C − µ · st G = et (mod q).

     For convenience later on, we also say the matrix µG is designed to encrypt µ, and has error 0. (This is
essentially implied by the above definitions, since µG is indeed a fresh encryption of µ, assuming that zero is
in the support of χ.) The next claim on the correctness of decryption follows immediately from the fact that
s = (s̄, 1) and the penultimate column of G is (0, . . . , 0, 2`−2 ), where 2`−2 ∈ [q/4, q/2) mod q.

Claim 3.4. If C is designed to encrypt some µ ∈ {0, 1} ⊂ Z, and has error vector et whose penultimate
coordinate has magnitude less than q/8, then GSW.Dec(s, C) correctly outputs µ.

We now analyze the behavior of the error terms under homomorphic operations.
   5
     Note that we can decrypt messages in Z ∩ [− 2q , 2q ), or any other canonical set of representatives of Zq , by “decoding” st C to
the nearest multiple of st G. The above decryption algorithm will be sufficient for our purposes.


                                                                  8

[page break]
Lemma 3.5. Suppose C1 , C2 are respectively designed to encrypt µ1 , µ2 ∈ Z and have error vectors et1 , et2 .
Then C1 ‘ C2 has error vector et1 + et2 , and C1 d C2 has error vector et1 X + µ1 et2 , where X ← G−1 (C2 )
is the matrix used in the evaluation of d. In particular, for any values of Ci , ei , µi , the latter error vector is
of the form et + µ1 et2 , where the entries of e are independent and subgaussian with parameter O(ke1 k).

    Importantly, the error in C1 d C2 is quasi-additive and asymmetric with respect to the errors in C1 , C2 :
while the first error vector et1 is multiplied by a short (subgaussian) matrix X, the second error vector et2 is
only multiplied by the (scalar) message µ1 , which we will ensure remains in {0, 1}.

Proof. The first claim is immediate, by linearity. For the second claim, because G · X = C2 we have

                                 st (C1 d C2 ) = st C1 · X
                                                = (et1 + µ1 · st G)X
                                                = et1 X + µ1 (et2 + µ2 · st G)
                                                = (et1 X + µ1 et2 ) + µ1 µ2 · st G.

    As observed in [BV14], the asymmetric noise growth allows for performing a long chain of homomorphic
multiplications while only incurring a polynomial-factor error growth, because d is defined to be right
associative. For convenience of analysis, in such a chain we always include the fixed ciphertext G, which
is designed to encrypt µ = 1 and has zero error, as the rightmost ciphertext in the chain. This ensures that
the error vector of the output ciphertext is subgaussian and essentially independent of the errors in the input
ciphertexts (apart from their lengths), which leads to a simpler and tighter analysis. (In [BV14] a weaker
independence guarantee was achieved by a separate “partial re-randomization” procedure, which requires
additional public key material.)

Corollary 3.6. Suppose that Ci for i ∈ [k] are respectively designed to encrypt µi ∈ {0, ±1} and have
error vectors eti . Then for any fixed values of these variables,
                                  ô
                           C←         Ci d G = C1 d (C2 d (· · · (Ck d G) · · · ))
                                 i∈[k]

has an error vector whose entries are mutually independent and subgaussian with parameter O(kek), where
et = (et1 , . . . , etk ) ∈ Zkn` is the concatenation of the individual error vectors.

Proof. By Lemma 3.5, the error vector in C is i eti Xi , where each eti Xi is a fresh independent vector that
                                              P
has mutually independent coordinates and is subgaussian with parameter O(kei k). The claim then follows by
Pythagorean additivity.
```

## Lines 484–581: §4 to Corollary 4.2: Equation (4.1) (cited by `Encrypts.sum`) and the permutation-matrix chains (phase-7 roadmap, ruled Q12 for BV14)

```text
4    Homomomorphic Encryption for Symmetric Groups
Brakerski and Vaikuntanathan [BV14] showed how to use the GSW encryption scheme to homomorphically
compose permutations of five elements (i.e., to homomorphically compute the group operation in the
symmetric group S5 ) with small additive noise growth; the use of S5 comes from its essential role in
Barrington’s theorem [Bar86]. In [BV14], the homomorphic composition of permutations is intertwined with
the evaluation of a branching program given by Barrington’s theorem. Here we give, as a “first-class object,”
a homomorphic cryptosystem for any symmetric group Sr . The ability to use several different small values
of r, along with a homomorphic equality test that we design, will be central to our bootstrapping algorithm.

                                                         9

[page break]
4.1      Encryption Scheme
We now describe our (symmetric-key) homomorphic encryption scheme for symmetric groups, called
HEPerm. Let C denote the ciphertext space for an appropriate instantiation of the GSW scheme, which we
treat as a “black box.” A secret key sk for HEPerm is simply a secret key for the GSW scheme.

       • HEPerm.Enc(sk, π ∈ Sr ): let P = (pi,j ) ∈ {0, 1}r×r be the permutation matrix associated with π.
         Output an entry-wise encryption of P, i.e., the ciphertext

                                         C = (ci,j ) ∈ C r×r , where ci,j ← Enc(sk, pi,j ).

    (Decryption follows in the obvious manner.) As with the GSW system, we say that a ciphertext C ∈ C r×r
is designed to encrypt a permutation π ∈ Sr (or its permutation matrix Pπ ) if its C-entries are designed
to encrypt the corresponding entries of Pπ . For convenience, we let J ∈ C r×r denote the ciphertext that
encrypts the identity permutation with zero noise, which is built in the expected way from the fixed zero-error
GSW ciphertexts that encrypt 0 and 1.
    We now show how to homomorphically compute two operations: the standard composition operation for
permutations, and an equality test.

Homomorphic composition Cπ e Cσ : on ciphertexts Cπ = (cπi,j ), Cσ = (cσi,j ) ∈ C r×r encrypting permu-
    tations π, σ ∈ Sr respectively, we compute one encrypting the permutation π ◦ σ by homomorphically
    evaluating the naı̈ve matrix-multiplication algorithm.6 That is, output C = (ci,j ) ∈ C r×r where
                                                 ð π
                                         ci,j ←      (ci,` d cσ`,j ) ∈ C.                             (4.1)
                                                              `∈[r]

         Just like d, we define e to be right associative.

Homomorphic equality test Eq?(Cπ = (cπi,j ), σ ∈ Sr ): given a ciphertext encrypting some permutation
    π ∈ Sr and a permutation σ ∈ Sr (in the clear), output a ciphertext c ∈ C encrypting 1 if π = σ and 0
    otherwise, as                               ô π
                                          c←         cσ(i),i d g,
                                                               i∈[r]

         where g ∈ C denotes the fixed zero-error encryption of 1. (Recall that d is right associative.)

    Observe that for the above two operations, the GSW ciphertext(s) in the output are designed to encrypt
the appropriate {0, 1}-message. For Compose this is simply by correctness of the matrix-multiplication
algorithm. For Eq? this is because the output ciphertext is designed to encrypt 1 if and only if every cσ(i),i is
designed to encrypt 1, which is the case if and only if Cπ is in fact designed to encrypt σ. All that remains is
to analyze the behavior of the error terms, which we do next.
   6
     Note that asymptotically faster algorithms (e.g., Strassen’s) do not appear suitable here, because the intermediate steps of these
algorithms can result in values having magnitude greater than one, which can cause the error in the ciphertexts to grow much faster.
In any case, this will not matter much in our application, since r will be small.




                                                                 10

[page break]
4.2   Analysis
Recalling that the GSW scheme is parameterized by n and q, denote its space of error vectors by E = Zm
where m = ndlog2 qe. The Euclidean norm on E r = Zmr is defined in the expected way. In what follows it
is often convenient to consider vectors and matrices over E, i.e., each entry is itself a (row) vector in E = Zm ,
and we switch between E h×w and Zh×wm as is convenient.
     The following lemma describes the behavior of errors under the homomorphic composition operation e.
Note that working with vectors and matrices over E lets us write a statement that is syntactically very similar
to the one from Lemma 3.5, with a very similar proof.
Lemma 4.1. Let Cπ , Cσ ∈ C r×r respectively be designed to encrypt permutation matrices Pπ , Pσ ∈
{0, 1}r×r with error matrices Eπ , Eσ ∈ E r×r . Then for any fixed values of these variables, Cπ e Cσ has
error matrix E + Pπ · Eσ ∈ E r×r , where the Z-entries of E are mutually independent, and those in its ith
row are subgaussian with parameter O(keπi k), where eπi is the ith row of Eπ .

Proof. Let C ← Cπ e Cσ . It suffices to show that for all i, j, its (i, j)th entry ci,j ∈ C has error

                                          ei,j + eσπ−1 (i),j ∈ E = Zm ,

where all the Z-entries of all the ei,j ∈ Zm are mutually independent and subgaussian with parameter
O(keπi k), and eσ`,j is the (`, j)th entry of Eσ . This follows directly from Equation (4.1) and Lemma 3.5:
the error in each ciphertext cπi,` d cσ`,j is pπi,` · eσ`,j plus a fresh vector whose entries are independent and
subgaussian with parameter O(keπi,` k). Since pπi,` = 1 for ` = π −1 (i) and 0 otherwise, the claim follows by
Pythagorean additivity of independent subgaussians.

    Similarly to a multiplication chain of GSW ciphertexts, we can perform a (right-associative) chain of
compositions while incurring only small error growth. For convenience of analysis, we always include the
fixed zero-error ciphertext J ∈ C r×r (which encrypts the identity permutation) as the rightmost ciphertext
in the chain. The following corollary follows directly from Lemma 4.1 in the same way that Corollary 3.6
follows from Lemma 3.5.
Corollary 4.2. Suppose that Ci ∈ C r×r for i ∈ [k] are respectively designed to encrypt permutation matrices
Pi ∈ {0, 1}r×r and have error matrices Ei ∈ E r×r . Then for any fixed values of these variables,
                              õ
                        C←        Ci e J = C1 e (C2 e (· · · (Ck e J) · · · ))
                                 i∈[k]

has an error matrix whose Z-entries are mutually independent, and those in its ith row are subgaussian with
parameter O(kei k), where eti ∈ E kr is the ith row of the concatenated error matrices [E1 | · · · | Ek ].

    Finally, since the Eq? procedure simply performs a chain of (right-associative) multiplications of GSW
ciphertexts, Corollary 3.6 applies.
```

## ===== briefs/lattice-gsw/gates/41-gsw-statements/source-excerpts/Pei16-excerpts.md =====

# Pei16: excerpts of the passages used (Gate 41)

**Reference.** C. Peikert, *A Decade of Lattice Cryptography*, author version dated 17 February 2016 (already ingested: `blueprint/src/references/peikert2016-lattice-survey{,.raw}.md`; the scoped `.md` covers Definitions 4.1.1, 4.2.1, 4.2.3 and SIS passages only, so §5.4.3 and §6.1.2–6.1.3 are quoted from the committed raw extraction).

**Extraction.** Lines of the committed file `blueprint/src/references/peikert2016-lattice-survey.raw.md` (blob 9aa84826712a65f261e9f374be4d45eccdb0bb27 at records e4302a5ee8756728a13c3b1e1398c207e66221a6), whose header names PDF SHA-256 `1a9802b66031a2b863fd498a5de4a71cdb1bd46ac1d47dc1f4a67ae341357488` and `pdftotext -layout`. The PDF itself is not committed (pairing ruling Q12; GSW ruling Q14 and the plan-section provenance). Only the passages below are quoted. Mathematical layout (sub- and superscripts, fraction bars) is flattened by the extraction; read formulas against the Lean statements and the PDF where needed.

**Passages.**

- lines 2530–2586: §5.4.3 "Gadgets": g, G = I_n ⊗ gᵗ, Equation (5.4.1), G · G⁻¹(u) = u
- lines 3374–3499: §6.1.2 (bootstrapping, circular security) and §6.1.3 (third-generation FHE: Equations (6.1.4)–(6.1.7), decryption, NAND, right-associative chains, Barrington)

## Lines 2530–2586: §5.4.3 "Gadgets": g, G = I_n ⊗ gᵗ, Equation (5.4.1), G · G⁻¹(u) = u

```text
5.4.3    Gadget Trapdoors
We now turn from short bases as generic lattice trapdoors, to the “gadget”-based trapdoors for q-ary SIS/LWE
lattices as developed in [MP12], building on techniques from several related works [Ajt99, AP09, PW08,
ABB10].

Gadgets. The first main idea is that there are special, structured matrices G, called “gadgets,” for which
solving SIS and LWE is easy. The simplest gadget is as follows: for a given a modulus q, define the vector

                                             g = (1, 2, 4, . . . , 2`−1 ) ∈ Z`q ,

where ` = dlog2 qe.8 Now observe that given any u ∈ Zq , we can find a short solution x ∈ Zm to

                                            hg, xi = gt · x = u (mod q);

for example, let x correspond to the base-two representation of u’s canonical representative in {0, . . . , q − 1}.
In other words, it is easy to solve the SIS problem with respect to the one-row parity-check “matrix” gt .
Moreover, it is easy to randomly sample from a discrete Gaussian over the lattice coset L⊥      t
                                                                                            u (g ) of solutions.
    A bit more thought reveals that solving LWE with respect to gt is also easy. For simplicity, suppose
that q = 2` ; then given any bt ≈ s · gt (mod q) with errors in the interval [− 4q , 4q ), we can recover the
most-significant bit of s ∈ Zq from

                                       b` ≈ s · 2`−1 = msb(s) · 2q         (mod q).

We can then recover the next-most-significant bit of s from b`−1 ≈ s · 2`−2 (mod q), etc. (This all generalizes
to non-power-of-two moduli as well, but is a bit more technically involved.)
    We extend all of the above to n-dimensional SIS and LWE with respect to the block-diagonal gadget
matrix
                               G := In ⊗ gt = diag(gt , . . . , gt ) ∈ Zn×n`
                                                                         q   ,

just by working blockwise: for LWE, given bt ≈ st G = (s1 g, . . . , sn g)t , just recover each si from the
corresponding block of b. For SIS, to find a short solution to Gx = u for a given u ∈ Znq , just find short
solutions to gt · xi = ui for each entry ui and concatenate the results. It is convenient to express this operation
in terms of the “decomposition” function

                               G−1 : Znq → Zn`                                                                      (5.4.1)
                                        u 7→ a short solution x to Gx = u (mod q),
   8
    This g can be generalized in a variety of ways, e.g., by using a base other than two, mixed bases, the Chinese Remainder
Theorem, etc.


                                                             50


<!-- pdf-page: 53 -->
where the choice of notation is explained by the relation

                                       G · G−1 (u) = u      (mod q).

We stress that G−1 is not a matrix, but rather a function that maps a mod-q input to a short integer vector.
Depending on the context, the G−1 operation may even be randomized, e.g., it could sample a Gaussian-
distribution solution.
    Finally, observe that given any invertible matrix H ∈ Zn×n
                                                            q   , SIS and LWE remain easy with respect to
the matrix HG ∈ Zq   n×n` . Specifically, to solve (HG)x = u, simply output x = G−1 (H−1 · u), and given
```

## Lines 3374–3499: §6.1.2 (bootstrapping, circular security) and §6.1.3 (third-generation FHE: Equations (6.1.4)–(6.1.7), decryption, NAND, right-associative chains, Barrington)

```text
6.1.2    Bootstrapping
Even with all of the above techniques, homomorphic operations still always increase the error rate of a
ciphertext, by as much as a polynomial factor per operation. Therefore, the schemes described so far can
only homomorphically evaluate circuits of an a-priori bounded depth; such systems are frequently called
“somewhat homomorphic” or “leveled” (we ignore the precise technical distinction between these terms).
     A beautiful idea from Gentry’s original work [Gen09b, Gen09a], called bootstrapping or sometimes
refreshing, makes it possible to reduce the error rate of a ciphertext, thus enabling unbounded homomorphic
computation. Suppose we have a ciphertext c that encrypts some (unknown) message µ under a secret key s,
where the error rate of c is too large to perform further homomorphic operations on it. The idea behind
bootstrapping is to homomorphically evaluate the decryption function on a low-error encryption cs = Enc(s)
of the secret key s, which is included as part of the public key. More specifically, we homomorphically
evaluate the function fc (·) = Dec(·, c) on the ciphertext cs . (Note that the ciphertext c to be refreshed is
“hard-coded” into the function fc (·), whereas the secret key is treated as the function argument.) Because
fc (s) = Dec(s, c) = µ, it follows that homomorphic evaluation of fc on an encryption of s (namely, cs )
produces an encryption of µ. Moreover, as long as the circuit depth of fc and the error rate of cs are small
enough, the error rate of the output ciphertext will be substantially smaller than that of the input ciphertext c,
as desired. In particular, decryption can be performed in O(log λ) depth, so it suffices for cs to have some
λ−O(log λ) error rate.
     Because bootstrapping involves the homomorphic evaluation of a somewhat complex function, it is not
very efficient (see, e.g., [GH11b]). However, bootstrapping has been intensively studied and improved in var-
ious ways [GH11a, BGV12], culminating in ring-LWE-based methods that run in only polylogarithmic Õ(1)
time per encrypted bit [GHS12a, AP13], where the hidden logO(1) (λ) factors are not exceedingly large.
     We conclude this discussion by noting that, in order to yield unbounded homomorphic operations,
bootstrapping requires a “circular” encryption of the secret key under itself. It is unknown whether it is
provably secure (under a standard assumption) to reveal such an encryption, but nor are any attacks known.
So to date, all unbounded FHE schemes require an additional assumption of circular security for the secret
key.




                                                       66


<!-- pdf-page: 69 -->
6.1.3   Third-Generation FHE
In 2013, Gentry, Sahai, and Waters (hereafter GSW) [GSW13] proposed an interesting LWE-based FHE
scheme that has some unique and advantageous properties. For example, homomorphic multiplication
does not require any key-switching step, and the scheme can be made identity-based. Moreover, as shown
in [BV14, AP14], the GSW scheme can be used to bootstrap with only a small polynomial-factor growth in
the error rate, as opposed to quasi-polynomial λΘ(log λ) growth for the system described above. This yields
unbounded FHE based on LWE with just an inverse-polynomial n−O(1) error rate (plus a circular-security
assumption). We describe these results in some detail next.

Homomorphic trapdoors. The GSW scheme is presented most simply in terms of the gadget-based trap-
doors described in Section 5.4.3. (The presentation here has evolved through [BGG+ 14, AP14, GVW15b].)
At the heart of GSW are the following additive and multiplicative homomorphisms for tags and trapdoors.
Let Ā ∈ Zn×
           q
              m̄ be arbitrary, and for i = 1, 2 let


                                             Ai = xi G − ĀRi                                            (6.1.4)
                                                                    R 
for some integer xi and short integer matrix Ri . In other words,     I
                                                                          i   is a trapdoor with tag xi (or more
accurately, tag xi I) for the matrix [Ā | Ai ].
    Applying Equation (6.1.4), it is easy to verify that

                                 A1 + A2 = (x1 + x2 )G − Ā(R1 + R2 ),                                   (6.1.5)

and

                          A1 · G−1 (A2 ) = (x1 G − ĀR1 ) · G−1 (A2 )
                                          = x1 A2 − Ā · R1 G−1 (A2 )
                                          = x1 x2 G − Ā (R1 G−1 (A2 ) + x1 R2 ) .                       (6.1.6)
                                                         |        {z          }
                                                                     R
                R +R                                                                      
In other words, 1 I 2 is a trapdoor with tag x1 + x2 for the matrix [Ā | A1 + A2 ], and R   I is a trapdoor
                                            −1
with tag x1 x2 for the matrix [Ā | A1 · G (A2 )]. Note that in the latter case, we need x1 to be a small
integer in order to get a good-quality trapdoor.
    One very important property of homomorphic multiplication is that the growth of the resulting trapdoor
matrix R is asymmetric and quasi-additive: while R1 is expanded by some polynomial factor due to the
multiplication by G−1 (A2 ), the R2 term is only multiplied by x1 . We discuss the implications of this below.

Fully homomorphic encryption. The GSW FHE scheme works as follows. As in prior systems, the public
key is a matrix Ā ∈ Zn×
                      q
                        m̄ whose columns are LWE samples with some secret s̄ ∈ Zn−1 , i.e.,


                                                  st Ā ≈ 0                                              (6.1.7)

where s = (−s̄, 1) is the secret key. An encryption of an integer x is a matrix

                                              A = xG − ĀR




                                                     67


<!-- pdf-page: 70 -->
for some sufficiently short random R. As usual, semantic security follows by a lossiness argument: encrypting
under a uniformly random (“malformed”) public key Ā statistically hides the message, because [Ā | ĀR] is
very close to uniformly distributed.
     To decrypt a ciphertext A using the secret key s, one just computes
                                                        st A ≈ x · st G,

where the approximation holds by Equation (6.1.7), and because R is short. Since it is easy to solve LWE
with respect to G, we can recover x · st and hence x (modulo q). In fact, if x is known to be just a bit, then
because one of the rightmost entries of st G is far from zero modulo q, we can recover x simply by testing
whether st · a ≈ 0 for an appropriate column a of A.
    To homomorphically add or multiply ciphertexts A1 , A2 that encrypt small messages, one just computes
A1 + A2 or A1 · G−1 (A2 ), respectively. As shown above in Equations (6.1.5) and (6.1.6), the resulting
ciphertext is a valid encryption for the sum or product of the messages, respectively. Because it is important
for noise growth that messages remain small integers, we typically only use operations that maintain the
messages as {0, 1}-values. For example, the binary NAND operation, which is sufficient for expressing
arbitrary computations, can be written as (x1 NAND x2 ) = 1 − x1 x2 .

Bootstrapping. As first shown by Brakerski and Vaikuntanathan [BV14], the asymmetric and quasi-
additive growth of the trapdoor matrices under homomorphic multiplication allows certain computations—in
particular, decryption for the purpose of bootstrapping—to be performed with rather small error growth.
The first main observation is that by Equation (6.1.6), any polynomial-length chain of homomorphic bit-
multiplications on fresh ciphertexts, if done in a right-associative manner, incurs only polynomial error
growth. The same also holds when multiplying a sequence of permutation matrices (or more generally,
orthonormal integer matrices), where each matrix is encrypted entry-wise.
    The second main idea is that by using Barrington’s Theorem [Bar86], any depth-d circuit can be converted
into a length-4d branching program of permutation matrices. In particular, the O(log λ)-depth decryption
circuit can be computed homomorphically in polynomial time and with polynomial error growth, albeit
for rather large polynomials. The subsequent work of Alperin-Sheriff and Peikert [AP14] significantly
improved the runtime and growth to small polynomials, by avoiding Barrington’s Theorem and instead
expressing decryption as an arithmetic function that can be embedded directly into permutation matrices.
```

## ===== briefs/lattice-gsw/gates/41-gsw-statements/source-excerpts/BV14-excerpts.md =====

# BV14: excerpts of the passages used (Gate 41)

**Reference.** Z. Brakerski, V. Vaikuntanathan, *Lattice-Based FHE as Secure as PKE*, ITCS 2014; IACR ePrint 2013/541 (PDF created 28 August 2013, 21 pp.).

**Extraction.** `pdftotext -layout` (poppler) of the uploaded PDF, SHA-256 `eab2d1667a8e8a07155968141c72d0ff0be15b1185dd0fd34f291fb41fb812ca` (checked when this file was written); line numbers are those of the extracted text. The PDF itself is not committed (pairing ruling Q12; GSW ruling Q14 and the plan-section provenance). Only the passages below are quoted. Mathematical layout (sub- and superscripts, fraction bars) is flattened by the extraction; read formulas against the Lean statements and the PDF where needed.

**Passages.**

- lines 1–2: title
- lines 345–388: §2.5: Definitions 2.12–2.13, Theorem 2.14 (bootstrapping, weak circular security)
- lines 389–811: §3: §3.1 (NCCrypt, Definition 3.1, Lemmas 3.2–3.3, Proposition 3.4), §3.2 (Claims 3.4.1–3.4.2), §3.3 (width-5 PBPs, Equations (4)–(6), Theorem 3.5, Lemma 3.6), §3.4 (Theorem 3.7)

## Lines 1–2: title

```text
                         Lattice-Based FHE as Secure as PKE
                            Zvika Brakerski∗            Vinod Vaikuntanathan†
```

## Lines 345–388: §2.5: Definitions 2.12–2.13, Theorem 2.14 (bootstrapping, weak circular security)

```text
2.5      Homomorphic Encryption and Bootstrapping
We now define homomorphic encryption and introduce Gentry’s bootstrapping theorem. Our defi-
nitions are mostly taken from [BV11, BGV12].
    A homomorphic (public-key) encryption scheme HE = (HE.Keygen, HE.Enc, HE.Dec, HE.Eval) is
a quadruple of ppt algorithms as follows (κ is the security parameter):
      • Key generation (pk, evk, sk)←HE.Keygen(1κ ): Outputs a public encryption key pk, a public
        evaluation key evk and a secret decryption key sk.2

      • Encryption c←HE.Encpk (µ): Using the public key pk, encrypts a single bit message µ ∈
        {0, 1} into a ciphertext c.

      • Decryption µ←HE.Decsk (c): Using the secret key sk, decrypts a ciphertext c to recover the
        message µ ∈ {0, 1}.

      • Homomorphic evaluation cf ←HE.Evalevk (f, c1 , . . . , c` ): Using the evaluation key evk, ap-
        plies a function f : {0, 1}` → {0, 1} to c1 , . . . , c` , and outputs a ciphertext cf .
  2
      We adopt the terminology of [BV11] that treats the evaluation key as a separate entity from the public key.


                                                          7

[page break]
   A homomorphic encryption scheme is said to be secure if it is semantically secure (note that
the adversary is given both pk and evk).
   Homomorphism w.r.t depth-bounded circuits and full homomorphism are defined next:
Definition 2.12 (compactness and full homomorphism). A homomorphic encryption scheme is
compact if its decryption circuit is independent of the evaluated function. A compact scheme is
(pure) fully homomorphic if it can evaluate any efficiently computable function. The scheme is
leveled fully homomorphic if it takes 1L as additional input in key generation, and can only evaluate
depth L Boolean circuits.
    Gentry’s bootstrapping theorem shows how to go from limited amount of homomorphism to
full homomorphism. This method has to do with the augmented decryption circuit.
Definition 2.13. Consider a homomorphic encryption scheme HE. Let (sk, pk, evk) be properly
generated keys and let C be the set of properly decryptable ciphertexts. Then the set of augmented
decryption functions, {fc1 ,c2 }c1 ,c2 ∈C is defined by fc1 ,c2 (x) = HE.Decx (c1 ) ∧ HE.Decx (c2 ). Namely,
the function that uses its input as secret key, decrypts c1 , c2 and returns the NAND of the results.
    The bootstrapping theorem is thus as follows.
Theorem 2.14 (bootstrapping [Gen09b, Gen09a]). A scheme that can homomorphically evaluate
its family of augmented decryption circuits can be transformed into a leveled fully homomorphic
encryption scheme with the same decryption circuit, ciphertext space and public key.
    Furthermore, if the aforementioned scheme is also weak circular secure (remains secure even
against an adversary who gets encryptions of the bits of the secret key), then it can be made into a
pure fully homomorphic encryption scheme.
```

## Lines 389–811: §3: §3.1 (NCCrypt, Definition 3.1, Lemmas 3.2–3.3, Proposition 3.4), §3.2 (Claims 3.4.1–3.4.2), §3.3 (width-5 PBPs, Equations (4)–(6), Theorem 3.5, Lemma 3.6), §3.4 (Theorem 3.7)

```text
3     Our FHE Scheme
In this section, we describe an FHE scheme secure under a polynomial LWE assumption which,
using known reductions [Reg05, Pei09], translates to the worst-case hardness of solving various
lattice problems to within polynomial approximation factors. We start with the basic encryption
scheme in Section 3.1, and describe “proto-homomorphic” addition and multiplication subroutines
in Section 3.2. Departing from the “conventional wisdom” in FHE, our circuit evaluation procedure
in Section 3.3 will not be a naive combination of these proto-homomorphic operations, but rather
a carefully designed procedure that manages the noise growth effectively.
    Finally, in Section 3.4, we put this all together to get our FHE scheme under the decisional
LWE assumption DLWEn,q,α with α = n−c for some constant c > 0. This polynomial factor is
rather large: thus, in Section 4, we apply a carefully designed variant of the dimension-modulus
reduction procedure of [BV11]pto obtain our final FHE scheme that is secure under the hardness of
DLWEn,q,α with α ≤ 1/O  eκ (n · n log(q)) which is weakest LWE hardness assumption that underlies
the (non-homomorphic) lattice-based PKE schemes [AD97, Reg04, Reg05, Pei09, BLP+ 13].

3.1    The Basic Encryption Scheme
Our basic encryption scheme closely follows the Gentry-Sahai-Waters FHE scheme [GSW13]. We
refer the reader to Section 2.3 for the description of the vector decomposition routines PowersOfTwo,
BitDecomp and Flatten used in the scheme below.

                                                     8

[page break]
System Parameters. Let n be the LWE dimension and q be an LWE modulus. Define N :=
(n + 1) · dlog qe. Let d denote the maximal homomorphism depth that is allowed by the scheme.
Let χ be an error distribution over Z. Typically χ will be a discrete Gaussian DZ,αq for α =
       p
1/Oeκ ( n log(q) · 4d ). Recall that we identify Zq with the set (−q/2, q/2] ∩ Z.

                                                      $
   • NCCrypt.Keygen(1n , q, 4d ): Sample a vector s ← Znq . Let m , (n + 1) · (log q + O(1)). Sample
         $               $
      A ← Zm×n
           q   and e ← χm . Compute b:= [A · s + e]q , and define

                                        P:= [bk − A] ∈ Zm×(n+1)
                                                        q       .

      Output sk = s and pk = evk = P.

      We describe public-key as well as secret-key encryption algorithms. Looking ahead, we remark
      that a secret-key encryption of µ is somewhat less “noisy” than a public-key encryption of µ.

   • NCCrypt.PubEnc(pk, µ): To encrypt a bit µ ∈ {0, 1}, using the public key pk = P, we let
       $
     R ← {0, 1}N ×m , and output the ciphertext

                          C = Flatten (BitDecomp(R · P) + µ · I) ∈ {0, 1}N ×N .

   • NCCrypt.SecEnc(sk, µ): A symmetric encryption of a bit µ ∈ {0, 1}, using the secret key
                                          $     ×n and e ←$
     sk = s, is performed by sampling A ← ZN q              χN , computing b:= [A · s + e]q , and
     defining
                       C = Flatten (BitDecomp ([bk − A]) + µ · I) ∈ {0, 1}N ×N .

   • NCCrypt.Dec(sk, C): Let c be the second row of C. We use standard Regev decryption on c.
     Namely, we output µ∗ = 0 if [hc, PowersOfTwo(1, s)i]q < q/8, and µ∗ = 1 otherwise.

Correctness. In order to show correctness of this scheme, we analyze the noise magnitude of
ciphertexts produced by both the public-key and secret-key encryption algorithms. As we will
show shortly, for ciphertexts C produced by either encryption algorithm, we have

                   C · PowersOfTwo(1, s) = µ · PowersOfTwo(1, s) + e (mod q)

for a noise vector e of “small magnitude”. This motivates our definition of the noise in the ciphertext
C with respect to a secret key vector s and a message µ as follows.

Definition 3.1. For every C ∈ {0, 1}N ×N , s ∈ Znq and µ ∈ Z, we define

                     noises,µ (C) , k(C − µI) · PowersOfTwo(1, s)    (mod q)k∞

   The significance of this definition is captured by the following claims. The first claim shows
that any ciphertext with small noise is decrypted correctly.

Lemma 3.2. For every C ∈ {0, 1}N ×N , s ∈ Znq and µ ∈ Z such that noises,µ (C) < q/8,

                                       NCCrypt.Dec(s, C) = µ

                                                  9

[page break]
Proof. Since noises,µ (C) < q/8, we have
                   C · PowersOfTwo(1, s) = η + µ · PowersOfTwo(1, s)      (mod q)
where kηk∞ < q/8. Thus, for the second row of C it holds that
                       hc, PowersOfTwo(1, s)i = η + 2dlog(q)e−2 · µ   (mod q)
where |η| < q/8. Thus, when µ = 0,

                               [hc, PowersOfTwo(1, s)i]q = |η| < q/8

When µ = 1,
                            [hc, PowersOfTwo(1, s)i]q ≥ q/4 − |η| ≥ q/8

since q/4 ≤ 2dlog(q)e−2 < q/2. This shows correctness of decryption for ciphertexts with small
noise.

   The next claim demonstrates parameter settings for which the (public key and secret key)
encryption algorithms produce ciphertexts with small noise.
Lemma 3.3. Let n be the LWE dimension, q be the LWE modulus and χ = DZ,αq be the discrete
Gaussian distribution. Then, for every s ∈ Znq and µ ∈ {0, 1},
                                                                 eκ (αq · √m).
  • for Cpub ← NCCrypt.PubEnc(pk, µ), we have noises,µ (Cpub ) = O

   • for Csec ← NCCrypt.SecEnc(sk, µ), we have noises,µ (Csec ) = O
                                                                  eκ (αq).

with all but negligible (in κ) probability over the coins of NCCrypt.Keygen.
                                                                                            e κ (√m),
   In particular, we have correctness of decryption for the public key encryption for α < 1/Ω
and for the secret key encryption for α < 1/Ω  e κ (1).

Proof. We first show the analysis for the public-key encryption.
                                                                 
       Cpub · PowersOfTwo(1, s) = Flatten BitDecomp(R · P) + µ · I · PowersOfTwo(1, s)
                                                             
                                 = BitDecomp(R · P) + µ · I · PowersOfTwo(1, s)

                                  = R · P · (1, s)T + µ · PowersOfTwo(1, s)
                                  = R · e + µ · PowersOfTwo(1, s)
Thus, by Proposition 2.3,
                                                            √
                              noise(Cpub ) = kR · ek∞ = O
                                                        eκ ( m · αq)

This is less than q/8 by the choice of α < 1/Ωe κ (√m).
   The analysis for the secret key encryption follows analogously, except that
                       Csec · PowersOfTwo(1, s) = e + µ · PowersOfTwo(1, s)
Thus,
                                   noise(Csec ) = kek∞ = O
                                                         eκ (αq)

which is less than q/8 by the choice of α < 1/Ω
                                              e κ (1).


                                                 10

[page break]
Security. Semantic security of the scheme follows from the decisional LWE assumption DLWEn,q,α ,
similarly to Regev’s encryption scheme (see [Reg05, BV11, GSW13] for similar arguments).

Complexity of Decryption. Our decryption algorithm is essentially the same as the decryption
algorithm in Regev’s encryption scheme, the complexity of which has been thoroughly studied in
the context of FHE. The following is an immediate corollary from [BV11, Lemma 4.1].

Proposition 3.4. There exists a constant cdec such that the decryption circuit of the scheme
NCCrypt, with parameters n, q, has depth at most cdec · log(n log q).

3.2   Proto-Homomorphic Operations
We now describe proto-homomorphic addition and multiplication algorithms which will be used
in Section 3.3 for homomorphic circuit evaluation. Departing from the “conventional wisdom” in
FHE, our circuit evaluation procedure will not be a naive combination of homomorphic addition
and multiplication, but a carefully designed procedure that manages the noise growth effectively.
To further stress the fact that we do not intend for these procedures to be used independently, we
call them proto-homomorphic operations.

Proto-Homomorphic Addition. This is a simple addition of the ciphertext matrices.

   • NCCrypt.ProtoAdd(C1 , C2 ): Output C+ := Flatten(C1 + C2 ).

    Jumping ahead, we note that in our use of NCCrypt.ProtoAdd in Section 3.3, both C1 and C2
will be encryptions of bits, and at most one of them will be an encryption of 1. The following claim
analyzes the noise growth in homomorphic addition.

Claim 3.4.1 (Noise Growth in NCCrypt.ProtoAdd.). For every s ∈ Znq , µ1 , µ2 ∈ Z and C1 , C2 ∈
{0, 1}N ×N , we have

              noises,µ1 +µ2 (NCCrypt.ProtoAdd(C1 , C2 )) ≤ noises,µ1 (C1 ) + noises,µ2 (C2 )

Proof. Let C+ ← NCCrypt.ProtoAdd(C1 , C2 ). We note that

          C+ · PowersOfTwo(1, s) = Flatten(C1 + C2 ) · PowersOfTwo(1, s)
                                      = (C1 + C2 ) · PowersOfTwo(1, s)
                                      = C1 · PowersOfTwo(1, s) + C2 · PowersOfTwo(1, s)
                                      = (e1 + e2 ) + (µ1 + µ2 ) · I

Thus, by the definition of noises,µ1 +µ2 , we have

                          noises,µ1 +µ2 (C+ ) ≤ noises,µ1 (C1 ) + noises,µ2 (C2 )




                                                     11

[page break]
Homomorphic Multiplication. This is essentially a multiplication of the ciphertext matrices,
except that we randomize the first ciphertext.

   • NCCrypt.ProtoMult(evk, C1 , C2 ):

        – Randomize C1 ∈ {0, 1}N ×N into a matrix C
                                                  e 1 ∈ {0, 1}N ×N by replacing each row c in
          C1 by the row
                                c ← BitDecomp(Rand(pk, Combine(c)))
                                e
          where Rand is the LWE randomization procedure from Section 2.4.
                                       
        – Output C× ← Flatten Ce 1 · C2 .

    Jumping ahead, we remark that when we use NCCrypt.ProtoMult in our homomorphic circuit
evaluation in Section 3.3, the first ciphertext will be an “evaluated ciphertext” (namely, a result
of previous homomorphic evaluations), whereas the second ciphertext will be a “fresh ciphertext”
(namely an output of the secret key encryption algorithm).
    The first new idea in this work is that while the order of the arguments does not matter in
homomorphic addition, the homomorphic multiplication algorithm NCCrypt.ProtoMult is inherently
asymmetric, since it is essentially the (non-commutative) matrix multiplication operation. This
asymmetry turns out to be the key to achieving improved noise growth, as Claim 3.4.2 below will
demonstrate.

Claim 3.4.2 (Noise Growth in NCCrypt.ProtoMult.). For every s ∈ Znq , µ1 , µ2 ∈ {0, 1} and C1 ∈
{0, 1}N ×N and C2 ← NCCrypt.SecEnc(sk, µ2 ), we have
                                                                                        p
         noises,µ1 µ2 (NCCrypt.ProtoMult(C1 , C2 )) ≤ |µ2 | · noises,µ1 (C1 ) + O
                                                                                eκ (αq · n log q)

with all but negligible probability over the randomness of NCCrypt.Keygen, NCCrypt.SecEnc and
NCCrypt.ProtoMult.

Remark. In words, Claim 3.4.2 says that if µ2 ∈ {0, 1} (as will be the case in our homomorphic
circuit evaluation in Section 3.3), the noise in C× is at most the noise in C1 , plus a fixed additive
term. What’s more, if µ2 = 0, then the noise in C× is independent of that in C1 ! These two facts
are the key new ideas that enable our main result.

Proof. (of Claim 3.4.2.) Let C× ← NCCrypt.ProtoMult(evk, C1 , C2 ). Note that

            C× · PowersOfTwo(1, s) = Flatten(Ce 1 · C2 ) · PowersOfTwo(1, s)
                                     e 1 · (C2 · PowersOfTwo(1, s))
                                   = C
                                         e 1 · (e2 + µ2 · PowersOfTwo(1, s))
                                       = C
                                         e 1 · e2 + µ2 · C
                                       = C               e 1 · PowersOfTwo(1, s)
                                         e 1 · e2 + µ2 · (e
                                       = C                e1 + µ1 · PowersOfTwo(1, s))
                                          e 1 · e2 + µ2 · e
                                       = (C               e1 ) + µ1 µ2 · PowersOfTwo(1, s)        (1)
            N
Since e2 ← DZ,αq                 e 1 ∈ {0, 1}N ×N is the result of Rand, by Lemma 2.11, we have
                 and each row of C

                                  e 1 · e2                   √
                                  C              ≤O
                                                  eκ (αq ·       n log q)                         (2)
                                             ∞


                                                   12

[page break]
with all but negligible probability.
Also, by lemma 2.10, we have
                                                                  p
                                ke
                                 e1 k∞ ≤ ke1 k∞ + O
                                                  eκ (αq ·         n log q)                                       (3)

with all but negligible probability.
   Putting together Eq. (1),(2) and (3), we have
                                                                                                   p
       noises,µ1 µ2 (C× ) ≤ C
                            e 1 · e2       + |µ2 | · ke                                 eκ (αq ·
                                                      e1 k∞ ≤ |µ2 | · noises,µ1 (C1 ) + O              n log q)
                                       ∞

which finishes the proof.

3.3    Homomorphic Evaluation of Circuits
We now describe how to homomorphically evaluate a Boolean circuit Ψ with two-input NAND gates
that takes ` inputs, and has depth d. In particular, our scheme will be able to evaluate circuits
of depth c · log n (for any constant c) under a polynomial LWE assumption, namely DLWEn,q,χ
where χ = DZ,α and α = 1/nΘ(c) . Since the depth of the decryption circuit is cdec · log(n log(q)) ≤
2cdec · log(n) (for some constant cdec > 0), the scheme is bootstrappable, and by the bootstrapping
theorem (Theorem 2.14), we get a leveled FHE scheme under the same assumption.
    To evaluate a circuit, our scheme first turns it into a width-5 permutation branching pro-
gram [BDFP86, Bar89], a model of computation that we describe below.

Width-5 Permutation Branching Programs. A permutation branching program                  Π of length
                         `
                                                                                   
L with input space {0, 1} is a sequence of L tuples of the form var(t), σt,0 , σt,1 where

   • var : [L] → [`] is a function that associates the t-th tuple with an input bit xvar(t) .

   • σj,0 and σj,1 are permutations on 5 elements. We will think of σj,0 and σj,1 as bijective
     functions from the set {1, 2, 3, 4, 5} to itself.

    The computation of the program Π on input x = (x1 , . . . , x` ) proceeds as follows. The state of
the computation at any point in time t is a number ζt ∈ {1, 2, 3, 4, 5}. Computation starts with the
initial state ζ0 = 1. The state ζt is computed recursively as

                                               ζt = σt,var(t) (ζt−1 )

Finally, after L steps, our state is ζL . The output of the computation is 1 if ζL = 1, and 0 otherwise.
    To manage the growth of noise in homomorphic evaluation, we need to work with bits rather
than numbers. Thus, we prefer to represent the state ζt ∈ {1, 2, 3, 4, 5} by a 0-1 vector vt which is
the unit vector uζt in 5 dimensions.
    The computation then proceeds as follows. The idea is that vt [i] = 1 if and only if σt,var(t) (ζt−1 ) =
i. Turning this around, vt [i] = 1 if and only if either:
            −1
   • vt−1 [σt,0 (i)] = 1 and xvar(t) = 0; or
            −1
   • vt−1 [σt,1 (i)] = 1 and xvar(t) = 1.



                                                        13

[page break]
   The following formula captures this condition. For t = 1, . . . , L, and i ∈ {1, 2, 3, 4, 5}, we have:
                                       −1                                 −1
                      vt [i] := vt−1 [σt,0 (i)] · (1 − xvar(t) ) + vt−1 [σt,1 (i)] · xvar(t)
                            = vt−1 [γt,i,0 ] · (1 − xvar(t) ) + vt−1 [γt,i,1 ] · xvar(t)             (4)
                 −1                   −1
where γt,i,0 , σt,0 (i) and γt,i,1 , σt,1 (i) are constants that are publicly computable given the
description of the branching program. It is this form that we will work with in our homomorphic
evaluation.
   The important property that we will use is that circuits of depth d can be simulated by branching
programs of depth L = 4d .

Theorem 3.5 (Barrington’s Theorem [Bar89]). Every Boolean NAND circuit Ψ that acts on `
inputs and has depth d can be computed by a width-5 permutation branching program Π of length
4d . Given the description of the circuit Ψ, the description of the branching program Π can be
computed in poly(`, 4d ) time.

Homomorphic Evaluation NCCrypt.Eval(Ψ, C1 , . . . , C` ). The homomorphic evaluation proce-
dure will first convert the depth-d circuit Ψ into a width-5 permutation branching program Π of
length L = 4d .

   • [Initialization] We will maintain the encrypted state of the computation of the branching
     program for every step t. We denote this by Vt = (Vt,1 , Vt,2 , Vt,3 , Vt,4 , Vt,5 ), where each
     Vt [i] ∈ {0, 1}N ×N will be an encryption of vt [i].

        – We initialize the state as follows. Compute V0,i := v0 [i] · I.
          Note that V0,i is in fact a valid encryption of the bit v0 [i] with zero noise.
        – We also compute encryptions of the complements of the input bits, for convenience.
          That is, set C̄k := I − Ck . Note that C̄k is an encryption of x̄k = 1 − xk with the same
          noise as Ck .

   • [Evaluation] The evaluation proceeds iteratively for t = 1, . . . , L, where L is the length of
     the branching program Π. Assuming that we have Vt−1 := (Vt−1,1 , Vt−1,2 , . . . , Vt−1,5 ), the
     encryption of the state of the branching program computation at time t − 1, we compute
     Vt := (Vt,1 , Vt,2 , . . . , Vt,5 ) by homomorphically evaluating Eq. (4) above.
     That is, for i ∈ {1, 2, 3, 4, 5}, we compute
                                                
                                                                                  
                     Vt,i := NCCrypt.ProtoAdd NCCrypt.ProtoMult Vt−1,γ0 ,C̄var(t) ,                  (5)
                                                                                
                                                                              
                                          NCCrypt.ProtoMult Vt−1,γ1 , Cvar(t)                        (6)


   • [Output] Upon finishing the evaluation stage, we have VL := (VL,1 , VL,2 , . . . , VL,5 ). Output
     VL,1 as the result of the homomorphic evaluation.

   We now show that the scheme correctly evaluates circuits.


                                                        14

[page break]
Lemma 3.6 (Correctness of Homomorphic Evaluation). Let n be the LWE dimension, q the LWE
modulus, Ψ be any Boolean circuit of depth d, and
                                                    p
                                    α ≤ 1/Θe κ (4d · n log q)

For every x1 , . . . , x` ∈ {0, 1}, every Boolean circuit Ψ of depth at most d, and every secret key
sk, letting Ck ← NCCrypt.SecEnc(sk, xk ) be the secret key encryptions of the inputs, and CΨ ←
NCCrypt.Eval(evk, Ψ, C1 , . . . , Ck ) be the evaluated ciphertext, we have:

                               NCCrypt.Dec(sk, CΨ ) = Ψ(x1 , . . . , x` )

with overwhelming probability over the coin tosses of all the algorithms. NCCrypt.Eval runs in time
poly(4d , `, n, log q).

    Note that we stated the correctness of homomorphic evaluation on ciphertexts produced by
the secret-key encryption algorithm NCCrypt.SecEnc. A√similar lemma can be shown in the case
of public-key encryption, if α is smaller by a factor of n log q. However, in our “optimal FHE”
scheme in Section 4, we will only need to invoke this lemma with secret-key encryption.

Proof. It is easy to see that each step of the homomorphic evaluation algorithm, given by Eq. (5),
simulates the execution of the branching program, given by Eq. (4). It remains to bound the noise
growth during NCCrypt.Eval. We show this by induction.
     In the sequel, we will abbreviate the noise function noises,µ (C) to noise(C) since the secret key
is fixed throughout the evaluation, and the message µ is clear from the context.
     Clearly, noise(V0,i ) = 0, since they V0,i are just the messages, with no noise. Assume, as the
inductive hypothesis, that for all i ∈ {1, 2, 3, 4, 5},
                                                                   p
                                noise(Vt−1,i ) = (t − 1) · O
                                                           eκ (αq · n log q)

We will now bound noise(Vt,i ) for all i ∈ {1, 2, 3, 4, 5}. Note that
                                                                                                   
                                                                                                  
noise Vt,i ≤ noise NCCrypt.ProtoMult Vt−1,γ0 , C̄var(t) + noise NCCrypt.ProtoMult Vt−1,γ1 , Cvar(t)
                                                                                        p
            ≤ |1 − xvar(t) | · noise(Vt−1,γ0 ) + |xvar(t) | · noise(Vt−1,γ1 ) + O
                                                                                eκ (αq · n log q)

where the second inequality holds by Claim 3.4.2 since all the ciphertexts encrypt bits, Cvar(t) is a
fresh secret-key encryption, and C̄var(t) contains exactly the same noise as Cvar(t) .
    Since exactly one of xvar(t) and 1 − xvar(t) is non-zero, we have
                                                                           p
               noise Vt,i ≤ max(noise(Vt−1,γ0 ), noise(Vt−1,γ1 )) + O
                                                                    eκ (αq · n log q)
                                      p
                           ≤t·O
                              eκ (αq · n log q)

by the inductive hypothesis.
   Thus, in particular,
                                                             p
                      noise(VΨ ) = noise VL,1 ≤ 4d · O
                                             
                                                     eκ (αq · n log q) < q/8

by our setting of the parameter α.

                                                  15

[page break]
3.4    Achieving Fully Homomorphic Encryption
We know by Lemma 3.4 that the depth of the decryption circuit of NCCrypt is cdec · log(n log q) =
cdec log N for some constant cdec >√ 0. Setting the depth d = c log N for some constant c > cdec
in Lemma 3.6 and α ≤ 1/Θ  e κ (4d · n log q) gives us a bootstrappable encryption scheme. By the
bootstrapping theorem (Theorem 2.14), this can be turned into a leveled FHE scheme, without
additional assumptions. We state this theorem below:

Theorem 3.7. Let n be the LWE dimension, q be the LWE modulus, N := (n + 1) · dlog qe,
and let c > cdec be a large enough constant (where cdec is the decryption depth constant from
Proposition 3.4), and
                                  α ≤ 1/Θe κ ((n log q)2c+1/2 )

Then, there is a leveled FHE scheme that is secure under the decisional LWE assumption DLWEn,q,α .

    In the next section, we will use a variant of the dimension-modulus reduction of [BV11], the
effect of which will be to reduce the constant c above to a very small  → 0, thus achieving a value
of α that matches the best known lattice-based PKE schemes.
```

## ===== TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean (Lean, at 94eae71b779c4ca0f76c138d699f4d737dbd6cee) =====

```lean
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Computability.Language
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.DeriveFintype

/-!
# Boolean circuits as directed acyclic graphs

The circuit model of [AB09, Def 6.1]: a directed acyclic graph with `n` source vertices
(the inputs) and one sink (the output), whose other vertices are gates labelled `∧`, `∨`
or `¬`.  Vertices are **numbered topologically**: the inputs are vertices `0, …, n - 1`,
gate `i` is vertex `n + i`, and a gate reads only vertices numbered below it, which is
exactly acyclicity.  Gates may feed any number of later gates (unbounded fan-out).

This is the model the book's circuit classes are stated over; `PPoly.lean` defines
`SIZE` and `P/poly` on it and `NCAC.lean` defines `NC` and `AC`.  The two other circuit
models of the library are `BoolCircuit.TreeCircuit` (formulas: fan-out one, negation only
at the inputs) and `BoolCircuit.LayeredCircuit` (layered DAGs over an arbitrary gate set,
the carrier of the Razborov–Smolensky development); the conversions are in `TreeDAG.lean`
and `LayeredDAG.lean`.

## Main definitions

* `BoolCircuit.GateKind`, `BoolCircuit.DAGGate` — a gate label and a gate.
* `BoolCircuit.DAGCircuit n` — a circuit with `n` inputs, with `eval`, `size` (the number
  of vertices, inputs included, as in [AB09, Def 6.1]) and `depth` (the length of the
  longest input-to-output path).
* `BoolCircuit.DAGCircuit.IsWellFormed` — `¬` gates have exactly one input and no gate
  reads a vertex twice (the graph has no parallel edges).
* `BoolCircuit.DAGCircuit.IsFaninTwo` — well formed, and every gate has at most two inputs.
* `BoolCircuit.DAGCircuitFamily` — one circuit per input length, with `language`,
  `IsPolySize`, `HasFaninTwo`, `IsWellFormed` and `HasPolylogDepth`.
* `BoolCircuit.GatesAcyclic` — a bare gate list reads only earlier vertices (the
  acyclicity field of `DAGCircuit`); `BoolCircuit.DAGGate.WellFormed`,
  `BoolCircuit.DAGGate.FaninTwo` — the gate-level well-formedness predicates.
* `BoolCircuit.constGate`, `BoolCircuit.constCircuit` — the model's constant gates
  (fan-in-zero `∧`/`∨`) and constant circuits.
* `BoolCircuit.DAGGate.remap` — rename the vertices a gate reads.

## Main results

* `BoolCircuit.runWith_getD_gate` — the value (or depth) of gate `i` is computed from the
  vertices before it; `BoolCircuit.runWith_getD_of_lt` — appending gates never changes
  the value of an existing vertex.  These two facts drive every proof about the model.
* `BoolCircuit.DAGCircuit.values_getD_gate`, `BoolCircuit.DAGCircuit.depthAt_gate` — the
  evaluation and depth recurrences at a gate vertex.
* `BoolCircuit.DAGGate.getD_lt_depth` — every vertex a gate reads is shallower than the gate;
  with the readers `DAGGate.depth_eq`, `DAGCircuit.depths_eq`, `DAGCircuit.depthAt_eq` and
  `DAGCircuit.depth_eq`.
* `BoolCircuit.runWith_rel` — two evaluators run over one gate list stay related vertex by
  vertex when every gate preserves the relation (the relational host lemma).
* `BoolCircuit.DAGGate.eval_remap`, `BoolCircuit.runWith_remap_rel` — renaming vertices
  commutes with evaluation, gate by gate and along a whole gate list.
* `BoolCircuit.gatesAcyclic_append`, `BoolCircuit.gatesAcyclic_cons` — acyclicity of
  concatenations.

## Divergences from [AB09, Def 6.1]

* **`∧`/`∨` fan-in is at most two, not exactly two.**  [AB09] gives every `∧`/`∨` gate
  fan-in `2` and has no constants.  Taken literally, a circuit on `0` inputs has no
  vertex to output, so no language would be decidable at length `0`; allowing fan-in `0`
  gives the constants (`∧` of nothing is `true`, `∨` of nothing is `false`), and fan-in `1`
  is an identity gate that can always be bypassed.  The literal model is
  `BoolCircuit.DAGCircuit.IsStrict` (`StrictCircuit.lean`).  It has no circuit at all on
  `0` inputs (`DAGCircuit.not_isStrict_zero`).  For `n ≥ 1` the relaxation costs a
  constant factor: `DAGCircuit.exists_isStrict` (`StrictSize.lean`) turns a fan-in-two
  circuit of size `S` into a strict one of size `≤ 4S + 12`.  That circuit has no constants
  or identity gates, and its output is the only sink, so unused gates and inputs are
  attached as well.  `Language.inPPoly_iff_inStrictPPoly` shows `P/poly` is unchanged.
* **Single output, as in the book.**  [AB09, Def 6.1] is single-output; the multi-output
  generalization is only a remark on p. 107 ("it is trivial to generalize the
  definition … though we typically will not need this generalization").  Multi-output
  circuits, where needed (Karp–Lipton, p. 114), are `BoolCircuit.MultiDAGCircuit`.
* **Gates not reaching the output are allowed (divergence).**  [AB09, Def 6.1] demands
  exactly one sink, so every gate of a book circuit lies on a path to the output.  Here
  the output is a designated vertex and other gates may be sinks; they are counted in
  `size`.  The divergence is harmless for every size bound: deleting the gates that do
  not reach the output preserves the computed function and only shrinks the size, so
  dead gates never help an upper bound, and a lower bound here is at least as strong.
  (An unread *input* would also be a second sink under the book's definition.)  The formal
  bridge to the single-sink model is `DAGCircuit.seal` and `DAGCircuit.exists_isStrict`
  (`StrictSize.lean`), which supersede pruning: they attach every dead vertex, unread
  inputs included, neutrally to the output, at linear cost.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§6.1, Definitions 6.1 and 6.2.)
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BoolCircuit

/-- The label of a gate: `∧`, `∨` or `¬`.  [AB09, Def 6.1] -/
inductive GateKind where
  | and
  | or
  | not
  deriving DecidableEq, Repr, Fintype

/-- A gate: its label and the vertices it reads, in order. -/
structure DAGGate where
  /-- The gate's label. -/
  kind : GateKind
  /-- The vertices whose values the gate reads. -/
  args : List ℕ
  deriving DecidableEq, Repr

namespace DAGGate

/-- Evaluate a gate, reading vertex `v`'s value as `vals.getD v false`.  A `¬` gate
negates the conjunction of its inputs, which is the negation of its single input in a
well-formed circuit. -/
def eval (g : DAGGate) (vals : List Bool) : Bool :=
  match g.kind with
  | .and => g.args.all fun a => vals.getD a false
  | .or => g.args.any fun a => vals.getD a false
  | .not => !(g.args.all fun a => vals.getD a false)

/-- A gate evaluates its argument values by conjunction, disjunction, or negated
conjunction according to its kind. -/
theorem eval_eq (g : DAGGate) (vals : List Bool) :
    eval g vals = match g.kind with
      | .and => g.args.all fun a => vals.getD a false
      | .or => g.args.any fun a => vals.getD a false
      | .not => !(g.args.all fun a => vals.getD a false) := rfl

/-- The depth of a gate: one more than the deepest vertex it reads, vertex `v`'s depth
being `ds.getD v 0`. -/
def depth (g : DAGGate) (ds : List ℕ) : ℕ :=
  1 + (g.args.map fun a => ds.getD a 0).foldr max 0

end DAGGate

/-! ## Running a gate list -/

/-- Run a gate list from initial vertex data `init`: each gate appends `f g vs`, computed
from the data `vs` of all earlier vertices.  `DAGCircuit.values` and `DAGCircuit.depths`
are the two instances. -/
def runWith {β : Type} (f : DAGGate → List β → β) (gs : List DAGGate) (init : List β) :
    List β :=
  gs.foldl (fun vs g => vs ++ [f g vs]) init

section RunWith

variable {β : Type} (f : DAGGate → List β → β)

/-- Running the empty gate list leaves the initial vertex data unchanged. -/
@[simp] theorem runWith_nil (init : List β) : runWith f [] init = init := rfl

/-- Running `g :: gs` from `init` is running `gs` from `init` extended by the datum `f g init`
of the first gate. -/
theorem runWith_cons (g : DAGGate) (gs : List DAGGate) (init : List β) :
    runWith f (g :: gs) init = runWith f gs (init ++ [f g init]) := rfl

/-- Running a concatenation `gs ++ hs` is running `hs` from the result of running `gs`. -/
theorem runWith_append (gs hs : List DAGGate) (init : List β) :
    runWith f (gs ++ hs) init = runWith f hs (runWith f gs init) := by
  simp [runWith, List.foldl_append]

/-- Running a single gate `g` from `init` appends exactly the datum `f g init`. -/
theorem runWith_singleton (g : DAGGate) (init : List β) :
    runWith f [g] init = init ++ [f g init] := rfl

/-- Running a gate list appends one datum per gate: the result has length
`init.length + gs.length`. -/
@[simp] theorem length_runWith (gs : List DAGGate) (init : List β) :
    (runWith f gs init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih => rw [runWith_cons, ih]; simp; omega

/-- Running more gates only appends: the old data is a prefix. -/
theorem runWith_eq_append (gs : List DAGGate) (init : List β) :
    ∃ ext, runWith f gs init = init ++ ext := by
  induction gs generalizing init with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨ext, h⟩ := ih (init ++ [f g init])
    exact ⟨[f g init] ++ ext, by rw [runWith_cons, h, List.append_assoc]⟩

/-- Appending gates never changes the data of an existing vertex. -/
theorem runWith_getD_of_lt (gs : List DAGGate) (init : List β) {v : ℕ} (hv : v < init.length)
    (d : β) : (runWith f gs init).getD v d = init.getD v d := by
  obtain ⟨ext, h⟩ := runWith_eq_append f gs init
  rw [h, List.getD_append _ _ _ _ hv]

/-- The data of the last gate of a list. -/
theorem runWith_getD_last (gs : List DAGGate) (g : DAGGate) (init : List β) (d : β) :
    (runWith f (gs ++ [g]) init).getD (init.length + gs.length) d =
      f g (runWith f gs init) := by
  rw [runWith_append, runWith_singleton]
  have : (runWith f gs init).length = init.length + gs.length := length_runWith f gs init
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp [this]

/-- The data of gate `i` is computed from the vertices before it. -/
theorem runWith_getD_gate (gs : List DAGGate) (init : List β) {i : ℕ} (hi : i < gs.length)
    (d : β) :
    (runWith f gs init).getD (init.length + i) d = f gs[i] (runWith f (gs.take i) init) := by
  have hlen : (gs.take i).length = i := List.length_take_of_le hi.le
  have hsplit : runWith f gs init =
      runWith f (gs.drop (i + 1)) (runWith f (gs.take i ++ [gs[i]]) init) := by
    rw [← runWith_append, List.append_assoc, List.singleton_append,
      ← List.drop_eq_getElem_cons hi, List.take_append_drop]
  rw [hsplit, runWith_getD_of_lt]
  · have := runWith_getD_last f (gs.take i) gs[i] init d
    rwa [hlen] at this
  · simp [hi]

/-- Reading only vertices below `k` gives the same data before and after more gates. -/
theorem runWith_getD_take (gs : List DAGGate) (init : List β) {i a : ℕ}
    (hi : i ≤ gs.length) (ha : a < init.length + i) (d : β) :
    (runWith f (gs.take i) init).getD a d = (runWith f gs init).getD a d := by
  conv_rhs => rw [← List.take_append_drop i gs, runWith_append]
  rw [runWith_getD_of_lt f (gs.drop i) (runWith f (gs.take i) init)
    (by rw [length_runWith, List.length_take_of_le hi]; exact ha)]

end RunWith

/-! ## Circuits -/

/-- `List.all` depends only on the predicate's values on the list's members. -/
theorem all_congr_mem {α : Type} {l : List α} {p q : α → Bool} (h : ∀ a ∈ l, p a = q a) :
    l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons, h a (by simp), ih (fun b hb => h b (by simp [hb]))]

/-- `List.any` depends only on the predicate's values on the list's members. -/
theorem any_congr_mem {α : Type} {l : List α} {p q : α → Bool} (h : ∀ a ∈ l, p a = q a) :
    l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons, h a (by simp), ih (fun b hb => h b (by simp [hb]))]

/-- A gate's value depends only on the values of the vertices it reads. -/
theorem DAGGate.eval_congr (g : DAGGate) {vals vals' : List Bool}
    (h : ∀ a ∈ g.args, vals.getD a false = vals'.getD a false) :
    g.eval vals = g.eval vals' := by
  unfold DAGGate.eval
  split
  · exact all_congr_mem h
  · exact any_congr_mem h
  · rw [all_congr_mem h]

/-- A gate's depth depends only on the depths of the vertices it reads. -/
theorem DAGGate.depth_congr (g : DAGGate) {ds ds' : List ℕ}
    (h : ∀ a ∈ g.args, ds.getD a 0 = ds'.getD a 0) :
    g.depth ds = g.depth ds' := by
  unfold DAGGate.depth
  rw [List.map_congr_left h]

/-! ## Gate predicates, constant gates and renamed gates -/

/-- A gate is well formed: no repeated input, and `¬` reads exactly one vertex.  A circuit
is `DAGCircuit.IsWellFormed` iff all its gates are. -/
def DAGGate.WellFormed (g : DAGGate) : Prop :=
  g.args.Nodup ∧ (g.kind = .not → g.args.length = 1)

/-- A gate admissible in a fan-in-two circuit: well formed, reading at most two
vertices. -/
def DAGGate.FaninTwo (g : DAGGate) : Prop :=
  g.WellFormed ∧ g.args.length ≤ 2

/-- The constant gate for the bit `b`: a fan-in-zero `∧` (value `true`) if `b`, a
fan-in-zero `∨` (value `false`) otherwise.  These are the model's constants (see the
fan-in divergence in the module docstring). -/
def constGate (b : Bool) : DAGGate :=
  ⟨if b then .and else .or, []⟩

/-- The constant-`1` gate is the fan-in-zero `∧`. -/
theorem constGate_true : constGate true = ⟨.and, []⟩ := rfl

/-- The constant-`0` gate is the fan-in-zero `∨`. -/
theorem constGate_false : constGate false = ⟨.or, []⟩ := rfl

/-- A constant gate evaluates to its bit, whatever the vertex values. -/
@[simp] theorem constGate_eval (b : Bool) (vals : List Bool) : (constGate b).eval vals = b := by
  cases b <;> rfl

/-- A constant gate has depth `1`. -/
@[simp] theorem constGate_depth (b : Bool) (ds : List ℕ) : (constGate b).depth ds = 1 := by
  cases b <;> rfl

/-- A constant gate reads no vertex. -/
@[simp] theorem constGate_args (b : Bool) : (constGate b).args = [] := rfl

/-- A constant gate is not a `¬` gate. -/
theorem constGate_kind_ne_not (b : Bool) : (constGate b).kind ≠ .not := by
  cases b <;> simp [constGate]

/-- A constant gate is admissible in a fan-in-two circuit. -/
@[simp] theorem constGate_faninTwo (b : Bool) : (constGate b).FaninTwo :=
  ⟨⟨by simp, fun h => absurd h (constGate_kind_ne_not b)⟩, by simp⟩

/-- The gate `g` with every input vertex `a` renamed to `σ a`. -/
def DAGGate.remap (σ : ℕ → ℕ) (g : DAGGate) : DAGGate :=
  ⟨g.kind, g.args.map σ⟩

/-- Renaming by the identity changes nothing. -/
@[simp] theorem DAGGate.remap_id (g : DAGGate) : g.remap id = g := by
  cases g; simp [DAGGate.remap]

/-- A renamed gate has the original gate's value when every renamed input carries the
original input's value. -/
theorem DAGGate.eval_remap (g : DAGGate) (σ : ℕ → ℕ) {vals vals' : List Bool}
    (h : ∀ a ∈ g.args, vals.getD (σ a) false = vals'.getD a false) :
    (g.remap σ).eval vals = g.eval vals' := by
  rcases g with ⟨k, args⟩
  have hall : ((args.map σ).all fun a => vals.getD a false) =
      args.all fun a => vals'.getD a false := by
    rw [List.all_map]; exact all_congr_mem fun a ha => by simpa using h a ha
  have hany : ((args.map σ).any fun a => vals.getD a false) =
      args.any fun a => vals'.getD a false := by
    rw [List.any_map]; exact any_congr_mem fun a ha => by simpa using h a ha
  cases k <;> simp only [DAGGate.remap, DAGGate.eval, hall, hany]

/-- **Renaming vertices commutes with running gates.**  Let `σ` send the `L` initial
vertices of `init` to vertices among the `L'` initial vertices of `init'`, and send gate
vertex `L + i` to `L' + i`.  If the gate step `f` turns a relation `R` between the data
read through `σ` and the original data into `R` between the outputs, and `R` holds
between `init'` (through `σ`) and `init`, then `R` holds at every vertex between running
the renamed gates from `init'` and running the original gates from `init`.

Technical glue with no textbook counterpart; used with `R` equality for values and
`R a b ↔ a ≤ b + 1` for depths.

**Proof sketch.** Induction on the gate list from the right.  Adding a last gate `g`
leaves the data of every earlier vertex unchanged on both sides (gates only append), and
`σ` keeps earlier vertices earlier, so the induction hypothesis covers them.  The new
vertex `L + |old|` is sent by `σ` to `L' + |old|`, where the renamed side holds
`f (g.remap σ)` of the renamed data and the original side `f g` of the original data;
every input of `g` is an earlier vertex by acyclicity, so the hypothesis on `f` applies. -/
theorem runWith_remap_rel {β : Type} (f : DAGGate → List β → β) (R : β → β → Prop) (d : β)
    (σ : ℕ → ℕ)
    (hf : ∀ (g : DAGGate) (vs vs' : List β),
      (∀ a ∈ g.args, R (vs.getD (σ a) d) (vs'.getD a d)) → R (f (g.remap σ) vs) (f g vs'))
    {L L' : ℕ} (init init' : List β) (hL : init.length = L) (hL' : init'.length = L')
    (hσ_lt : ∀ v < L, σ v < L') (hσ_gate : ∀ i, σ (L + i) = L' + i)
    (hinit : ∀ v < L, R (init'.getD (σ v) d) (init.getD v d)) (gs : List DAGGate)
    (hgs : ∀ (i : ℕ) (h : i < gs.length), ∀ a ∈ (gs[i]).args, a < L + i) :
    ∀ v < L + gs.length,
      R ((runWith f (gs.map (DAGGate.remap σ)) init').getD (σ v) d)
        ((runWith f gs init).getD v d) := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro v hv
    simpa using hinit v (by simpa using hv)
  | append_singleton old g ih =>
    have hold : ∀ (i : ℕ) (h : i < old.length), ∀ a ∈ (old[i]).args, a < L + i :=
      fun i hi a ha => hgs i (by simp; omega) a (by rwa [List.getElem_append_left hi])
    have hg : ∀ a ∈ g.args, a < L + old.length := fun a ha =>
      hgs old.length (by simp) a (by simpa using ha)
    have ih := ih hold
    have hlen : (runWith f (old.map (DAGGate.remap σ)) init').length = L' + old.length := by
      simp [hL']
    have hlen0 : (runWith f old init).length = L + old.length := by simp [hL]
    -- vertices below the new gate keep their (renamed) data
    have hσ_old : ∀ v < L + old.length, σ v < L' + old.length := by
      intro v hv
      by_cases hvL : v < L
      · have := hσ_lt v hvL; omega
      · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp hvL)
        rw [hσ_gate]; omega
    intro v hv
    rw [List.map_append, List.map_singleton, runWith_append, runWith_append,
      runWith_singleton, runWith_singleton]
    simp only [List.length_append, List.length_singleton] at hv
    rcases Nat.lt_succ_iff_lt_or_eq.mp (by omega : v < L + old.length + 1) with hv | rfl
    · rw [List.getD_append _ _ _ _ (by rw [hlen]; exact hσ_old v hv),
        List.getD_append _ _ _ _ (by rw [hlen0]; exact hv)]
      exact ih v hv
    · -- the new gate: its inputs carry related data by the induction hypothesis
      rw [hσ_gate, List.getD_append_right _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by omega), hlen, hlen0]
      simp only [Nat.sub_self, List.getD_cons_zero]
      exact hf g _ _ fun a ha => ih a (hg a ha)

/-! ## Gate lists that read only earlier vertices -/

/-- Every gate of `gs` reads only vertices below its own, `n` inputs coming first: the
acyclicity condition `DAGCircuit.args_lt` for a bare gate list. -/
def GatesAcyclic (n : ℕ) (gs : List DAGGate) : Prop :=
  ∀ (i : ℕ) (h : i < gs.length), ∀ a ∈ (gs[i]).args, a < n + i

/-- The empty gate list is acyclic. -/
theorem GatesAcyclic.nil {n : ℕ} : GatesAcyclic n [] := fun i h => absurd h (by simp)

/-- Appending a gate that reads only existing vertices keeps a gate list acyclic. -/
theorem GatesAcyclic.snoc {n : ℕ} {gs : List DAGGate} (h : GatesAcyclic n gs) {g : DAGGate}
    (hg : ∀ a ∈ g.args, a < n + gs.length) : GatesAcyclic n (gs ++ [g]) := by
  intro i hi a ha
  rw [List.length_append, List.length_singleton] at hi
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
  · rw [List.getElem_append_left hlt] at ha
    exact h i hlt a ha
  · simp only [List.getElem_append_right (le_refl _), Nat.sub_self,
      List.getElem_singleton] at ha
    exact hg a ha

/-- Appending a gate list that reads only vertices before each of its own gates (counted
from the end of the first list) keeps the whole list acyclic. -/
theorem GatesAcyclic.append {n : ℕ} {gs hs : List DAGGate} (hg : GatesAcyclic n gs)
    (hh : GatesAcyclic (n + gs.length) hs) : GatesAcyclic n (gs ++ hs) := by
  intro i hi a ha
  by_cases hlt : i < gs.length
  · rw [List.getElem_append_left hlt] at ha
    exact hg i hlt a ha
  · rw [List.getElem_append_right (by omega)] at ha
    have := hh (i - gs.length) (by simp at hi; omega) a ha
    omega

/-- The empty gate list is acyclic (as a `simp` rewrite). -/
@[simp] theorem gatesAcyclic_nil {n : ℕ} : GatesAcyclic n [] ↔ True :=
  iff_true_intro GatesAcyclic.nil

/-- A gate list started at vertex `n` is acyclic iff its first gate reads only vertices
below `n` and the rest, started at `n + 1`, is acyclic. -/
@[simp] theorem gatesAcyclic_cons {n : ℕ} {g : DAGGate} {gs : List DAGGate} :
    GatesAcyclic n (g :: gs) ↔ (∀ a ∈ g.args, a < n) ∧ GatesAcyclic (n + 1) gs := by
  constructor
  · intro h
    refine ⟨fun a ha => by simpa using h 0 (by simp) a (by simpa using ha), ?_⟩
    intro i hi a ha
    have := h (i + 1) (by simp; omega) a (by simpa using ha)
    omega
  · rintro ⟨h0, h⟩ i hi a ha
    cases i with
    | zero => simpa using h0 a (by simpa using ha)
    | succ i =>
      have := h i (by simpa using hi) a (by simpa using ha)
      omega

/-- A concatenation is acyclic iff the first part is, started at `n`, and the second part
is, started after the first. -/
theorem gatesAcyclic_append {n : ℕ} {gs hs : List DAGGate} :
    GatesAcyclic n (gs ++ hs) ↔ GatesAcyclic n gs ∧ GatesAcyclic (n + gs.length) hs := by
  induction gs generalizing n with
  | nil => simp
  | cons g gs ih =>
    simp only [List.cons_append, gatesAcyclic_cons, ih, List.length_cons, and_assoc]
    rw [show n + 1 + gs.length = n + (gs.length + 1) by omega]

/-- A Boolean circuit with `n` inputs and one output: a DAG whose vertices are numbered
topologically.  Vertices `0, …, n - 1` are the inputs, vertex `n + i` is gate `i`, and
gate `i` reads only vertices below `n + i`.  [AB09, Def 6.1] -/
structure DAGCircuit (n : ℕ) where
  /-- The gates, in topological order. -/
  gates : List DAGGate
  /-- The output vertex. -/
  output : ℕ
  /-- Gate `i` reads only earlier vertices: the graph is acyclic. -/
  args_lt : ∀ (i : ℕ) (h : i < gates.length), ∀ a ∈ (gates[i]).args, a < n + i
  /-- The output is a vertex of the circuit. -/
  output_lt : output < n + gates.length

namespace DAGCircuit

variable {n : ℕ} (C : DAGCircuit n)

/-- The values of all vertices on input `x`: the inputs, then each gate in order. -/
def values (x : Fin n → Bool) : List Bool :=
  runWith DAGGate.eval C.gates (List.ofFn x)

/-- The vertex-value equation [AB09, Def 6.1]: `C.values x` runs the gates from `List.ofFn x`. -/
theorem values_eq (x : Fin n → Bool) :
    C.values x = runWith DAGGate.eval C.gates (List.ofFn x) := rfl

/-- The circuit's output on input `x`. -/
def eval (x : Fin n → Bool) : Bool :=
  (C.values x).getD C.output false

/-- The output equation [AB09, Def 6.1]: `C.eval x = (C.values x).getD C.output false`. -/
theorem eval_eq (x : Fin n → Bool) :
    C.eval x = (C.values x).getD C.output false := rfl

/-- The depths of all vertices: `0` at the inputs, one more than the deepest input at a
gate. -/
def depths : List ℕ :=
  runWith DAGGate.depth C.gates (List.replicate n 0)

/-- The depth of vertex `v`: the length of the longest path from an input to `v`. -/
def depthAt (v : ℕ) : ℕ := C.depths.getD v 0

/-- The depth of the circuit: the length of the longest path from an input to the
output.  [AB09, Def 6.1] -/
def depth : ℕ := C.depthAt C.output

/-- The size of the circuit: its number of vertices, inputs included.  [AB09, Def 6.1] -/
def size : ℕ := n + C.gates.length

/-- The size equation [AB09, Def 6.1]: `C.size = n + C.gates.length`. -/
theorem size_eq : C.size = n + C.gates.length := rfl

/-- `¬` gates have exactly one input, and no gate reads a vertex twice. -/
def IsWellFormed : Prop :=
  ∀ g ∈ C.gates, g.args.Nodup ∧ (g.kind = .not → g.args.length = 1)

/-- Well formed, with every gate reading at most two vertices.  [AB09, Def 6.1] -/
def IsFaninTwo : Prop :=
  C.IsWellFormed ∧ ∀ g ∈ C.gates, g.args.length ≤ 2

/-- The vertex-value list of a circuit has one entry per vertex: `n` inputs plus one per
gate. -/
@[simp] theorem length_values (x : Fin n → Bool) :
    (C.values x).length = n + C.gates.length := by
  simp [values]

/-- The vertex-depth list of a circuit has one entry per vertex: `n` inputs plus one per
gate. -/
@[simp] theorem length_depths : C.depths.length = n + C.gates.length := by
  simp [depths]

/-- An input vertex holds its input bit. -/
theorem values_getD_input (x : Fin n → Bool) (i : Fin n) :
    (C.values x).getD i false = x i := by
  rw [values, runWith_getD_of_lt _ _ _ (by simp)]
  simp

/-- An input vertex has depth `0`. -/
theorem depthAt_input {i : ℕ} (hi : i < n) : C.depthAt i = 0 := by
  rw [depthAt, depths, runWith_getD_of_lt _ _ _ (by simpa using hi)]
  simp [hi]

/-- Gate `i`'s value is its gate applied to the values of all vertices. -/
theorem values_getD_gate (x : Fin n → Bool) {i : ℕ} (hi : i < C.gates.length) :
    (C.values x).getD (n + i) false = C.gates[i].eval (C.values x) := by
  have key := runWith_getD_gate DAGGate.eval C.gates (List.ofFn x) hi false
  simp only [List.length_ofFn] at key
  rw [values, key]
  -- the gate reads only vertices below `n + i`, which the prefix already holds
  exact DAGGate.eval_congr _ fun a ha =>
    runWith_getD_take _ _ _ hi.le (by simpa using C.args_lt i hi a ha) false

/-- Gate `i`'s depth is its gate's depth over the depths of all vertices. -/
theorem depthAt_gate {i : ℕ} (hi : i < C.gates.length) :
    C.depthAt (n + i) = C.gates[i].depth C.depths := by
  have key := runWith_getD_gate DAGGate.depth C.gates (List.replicate n 0) hi 0
  simp only [List.length_replicate] at key
  rw [depthAt, depths, key]
  exact DAGGate.depth_congr _ fun a ha =>
    runWith_getD_take _ _ _ hi.le (by simpa using C.args_lt i hi a ha) 0

end DAGCircuit

/-! ## Depth readers and the relational simulation of `runWith` -/

/-- A gate's depth is one more than the maximum depth of the vertices it reads, vertex `v`'s
depth being `ds.getD v 0` [AB09, Def 6.1, depth of a vertex]. -/
theorem DAGGate.depth_eq (g : DAGGate) (ds : List ℕ) :
    g.depth ds = 1 + (g.args.map fun a => ds.getD a 0).foldr max 0 := rfl

/-- Every vertex a gate reads is strictly shallower than the gate:
`ds.getD a 0 < g.depth ds` for `a ∈ g.args`.

**Proof sketch.** By `DAGGate.depth_eq`, it suffices that `ds.getD a 0` is at most the
`foldr max 0` of the mapped list when `a ∈ g.args`; induct on `g.args` with `le_max_left` /
`le_max_right` and `List.mem_cons`. -/
theorem DAGGate.getD_lt_depth (g : DAGGate) (ds : List ℕ) {a : ℕ} (ha : a ∈ g.args) :
    ds.getD a 0 < g.depth ds := by
  have key : ∀ l : List ℕ, a ∈ l → ds.getD a 0 ≤ (l.map fun a => ds.getD a 0).foldr max 0 := by
    intro l hl
    induction l with
    | nil => cases hl
    | cons b l ih =>
      rw [List.map_cons, List.foldr_cons]
      rcases List.mem_cons.mp hl with rfl | hl
      · exact le_max_left _ _
      · exact le_trans (ih hl) (le_max_right _ _)
  rw [DAGGate.depth_eq]
  have := key g.args ha
  omega

namespace DAGCircuit

variable {n : ℕ} (C : DAGCircuit n)

/-- The vertex-depth list runs `DAGGate.depth` from `n` zeros [AB09, Def 6.1]:
`C.depths = runWith DAGGate.depth C.gates (List.replicate n 0)`. -/
theorem depths_eq : C.depths = runWith DAGGate.depth C.gates (List.replicate n 0) := rfl

/-- The depth of vertex `v` is entry `v` of the depth list, `0` out of range:
`C.depthAt v = C.depths.getD v 0`. -/
theorem depthAt_eq (v : ℕ) : C.depthAt v = C.depths.getD v 0 := rfl

/-- The circuit depth is the depth of its output vertex [AB09, Def 6.1]:
`C.depth = C.depthAt C.output`. -/
theorem depth_eq : C.depth = C.depthAt C.output := rfl

end DAGCircuit

/-- **Relational indexed simulation of `runWith`.** Two evaluators run the same gate list from
initial data related vertex by vertex by `R v`. If, at gate `i`, related data on the gate's
inputs always produce related outputs at vertex `L + i`, then the two runs are related at
every vertex `v < L + |gs|`, where `L` is the number of initial vertices. Technical host lemma
with no textbook counterpart; `SecureComputation.runWith_sim` is the functional special case
`R v a b ↔ b = W v a`.

**Proof sketch.** Strong induction on the vertex, exactly as `runWith_sim`: input vertices
are the initial relation (`runWith_getD_of_lt`); a gate vertex `L + i` reads both runs'
prefixes (`runWith_getD_gate`), whose argument entries agree with the full runs
(`runWith_getD_take`) and are related by the induction hypothesis, since acyclicity puts every
argument below `L + i`. -/
theorem runWith_rel {α β : Type} (fA : DAGGate → List α → α) (fB : DAGGate → List β → β)
    (R : ℕ → α → β → Prop) (dA : α) (dB : β) (gs : List DAGGate)
    (initA : List α) (initB : List β) (hlen : initB.length = initA.length)
    (hinit : ∀ v < initA.length, R v (initA.getD v dA) (initB.getD v dB))
    (hacyc : ∀ (i : ℕ) (h : i < gs.length), ∀ a ∈ (gs[i]).args, a < initA.length + i)
    (hgate : ∀ (i : ℕ) (h : i < gs.length) (vA : List α) (vB : List β),
      vA.length = initA.length + i → vB.length = initA.length + i →
      (∀ a ∈ (gs[i]).args, R a (vA.getD a dA) (vB.getD a dB)) →
      R (initA.length + i) (fA gs[i] vA) (fB gs[i] vB)) :
    ∀ v < initA.length + gs.length,
      R v ((runWith fA gs initA).getD v dA) ((runWith fB gs initB).getD v dB) := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro hv
    by_cases hlt : v < initA.length
    · rw [runWith_getD_of_lt _ _ _ hlt, runWith_getD_of_lt _ _ _ (hlen ▸ hlt)]
      exact hinit v hlt
    · obtain ⟨i, rfl⟩ : ∃ i, v = initA.length + i := ⟨v - initA.length, by omega⟩
      have hi : i < gs.length := by omega
      have hB := runWith_getD_gate fB gs initB hi dB
      have hA := runWith_getD_gate fA gs initA hi dA
      rw [hlen] at hB
      rw [hA, hB]
      refine hgate i hi _ _ (by rw [length_runWith, List.length_take_of_le hi.le])
        (by rw [length_runWith, List.length_take_of_le hi.le, hlen]) fun a ha => ?_
      have ha' := hacyc i hi a ha
      rw [runWith_getD_take _ gs initA hi.le ha',
        runWith_getD_take _ gs initB hi.le (by omega)]
      exact ih a ha' (by omega)

/-- The constant circuit on `n` inputs with output `b`: one constant gate
(`constGate b`), which is the output. -/
def constCircuit (n : ℕ) (b : Bool) : DAGCircuit n where
  gates := [constGate b]
  output := n
  args_lt := by intro i hi a ha; simp at hi; subst hi; simp at ha
  output_lt := by simp

/-- The constant circuit outputs its bit. -/
@[simp] theorem constCircuit_eval {n : ℕ} (b : Bool) (x : Fin n → Bool) :
    (constCircuit n b).eval x = b := by
  simp [DAGCircuit.eval, DAGCircuit.values, constCircuit, runWith_cons]

/-- The constant circuit has fan-in two. -/
theorem constCircuit_isFaninTwo (n : ℕ) (b : Bool) : (constCircuit n b).IsFaninTwo := by
  refine ⟨fun g hg => ?_, fun g hg => ?_⟩ <;>
    simp only [constCircuit, List.mem_singleton] at hg <;> subst hg <;>
    cases b <;> simp [constGate]

/-- The constant circuit has `n + 1` vertices. -/
@[simp] theorem constCircuit_size (n : ℕ) (b : Bool) : (constCircuit n b).size = n + 1 := rfl

/-! ## Circuit families -/

/-- A non-uniform family of circuits, one per input length. -/
structure DAGCircuitFamily where
  /-- The circuit handling inputs of length `n`. -/
  circuit : (n : ℕ) → DAGCircuit n

namespace DAGCircuitFamily

variable (C : DAGCircuitFamily)

/-- The family accepts `w` when the circuit for length `w.length` outputs `true`. -/
def Accepts (w : List Bool) : Prop :=
  (C.circuit w.length).eval w.get = true

/-- The language decided by the family. -/
def language : Language Bool :=
  {w | C.Accepts w}

/-- Membership in the decided language, unfolded to the circuit's output. -/
@[simp]
theorem mem_language_iff (w : List Bool) :
    w ∈ C.language ↔ (C.circuit w.length).eval w.get = true :=
  Iff.rfl

/-- Every circuit of the family is well formed (unbounded fan-in, [AB09, Def 6.25]). -/
def IsWellFormed : Prop :=
  ∀ n, (C.circuit n).IsWellFormed

/-- Every circuit of the family has fan-in at most two ([AB09, Def 6.1]). -/
def HasFaninTwo : Prop :=
  ∀ n, (C.circuit n).IsFaninTwo

/-- The family has polynomial size.  [AB09] writes `|C_n| ≤ n ^ c`, which no family meets
(`Language.not_inSIZE_pow`, `PPoly.lean`: `n ^ c` is `0` at `n = 0` for `c ≥ 1`, and `1` at
`n = 2` for `c = 0`); `a * (n + 1) ^ k` repairs this, and differs from the literal bound only
at the lengths `n ≤ 1` (`Language.inPPoly_iff_eventually`). -/
def IsPolySize : Prop :=
  ∃ a k : ℕ, ∀ n, (C.circuit n).size ≤ a * (n + 1) ^ k

/-- The family has depth `O(log^d n)`; the `+ 1` keeps `n ≤ 1` from forcing depth `0`. -/
def HasPolylogDepth (d : ℕ) : Prop :=
  ∃ b : ℕ, ∀ n, (C.circuit n).depth ≤ b * (Nat.log 2 n + 1) ^ d

/-- A fan-in-two circuit family is in particular well formed: each of its circuits reads
distinct inputs at every gate and exactly one input at every `¬` gate. -/
theorem HasFaninTwo.isWellFormed {C : DAGCircuitFamily} (h : C.HasFaninTwo) :
    C.IsWellFormed :=
  fun n => (h n).1

end DAGCircuitFamily

end BoolCircuit
```

## ===== TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Gadget.lean (Lean, at 48d796a8a68cd50897047f01825a8132dd19e8d8) =====

```lean
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.LWE.Basic
import TCSlib.Cryptography.TrapdoorFunctions.Lossy.Gadget
import Mathlib.Data.Matrix.Mul

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The GSW gadget matrix and its binary decomposition

## Main definitions

* `GSW.Parameters`: an LWE parameter bundle with a gadget width `ℓ` satisfying `q ≤ 2^ℓ`.
* `Parameters.columns`: the ciphertext width `N = (n+1)·ℓ` (a reducible abbreviation).
* `gadget`: the block-diagonal gadget `G = I_{n+1} ⊗ gᵗ` with `g = (1,2,…,2^{ℓ-1})`,
  an `(n+1) × N` matrix modulo `q`.
* `digit`, `decomposeVec`, `decompose`: the deterministic binary decomposition `G⁻¹`,
  little-endian inside each block, returning Boolean matrices.
* `lift`: read a Boolean matrix as a `{0,1}` matrix modulo `q`.

## Main results

* `gadget_mulVec_decomposeVec`, `gadget_mul_decompose`: `G · G⁻¹(M) = M` [Pei16, (5.4.1)].
* `decomposeVec_block_eq_false`: a zero coordinate decomposes to an all-zero block.
* `errorSum_decomposeVec_le`: an error vector against the decomposition of a vector that is
  zero outside one coordinate has magnitude at most `ℓ·β`.

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated
  17 February 2016, Section 5.4.3 (gadget `g`, `G = I_n ⊗ gᵗ`, Equation (5.4.1)).
* [GSW13] C. Gentry, A. Sahai, B. Waters, *Homomorphic Encryption from Learning with
  Errors: Conceptually-Simpler, Asymptotically-Faster, Attribute-Based*, CRYPTO 2013;
  author version dated 8 June 2013, Section 1.3.3 (`BitDecomp`, `Powersof2`) and
  Section 3.2 (`G = BitDecomp⁻¹(I_N)`).
* [AP14] J. Alperin-Sheriff, C. Peikert, *Faster Bootstrapping with Polynomial Error*,
  CRYPTO 2014; ePrint 2014/094 version dated 13 June 2014, Section 3.1 (Equation (3.1)).

**Deviations.** The width `ℓ` is any natural number with `q ≤ 2^ℓ`; [GSW13] fixes
`ℓ = ⌊log₂ q⌋ + 1`, [AP14] and [Pei16] `ℓ = ⌈log₂ q⌉`, and BV14 `⌈log q⌉`. All of these
satisfy the hypothesis. `G⁻¹` is deterministic binary decomposition, as in [GSW13]'s
`BitDecomp`; [AP14, Claim 3.1]'s randomized subgaussian `G⁻¹` uses lattice sampling, which
the campaign plan excludes. The gadget reuses the audited little-endian
`TrapdoorFunctions.Lossy.gadget` and `Randomized.blocksEquiv` rather than a third copy.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

/-- GSW parameters [GSW13, Section 3.1, `Setup`; AP14, Section 3.2]: LWE numeric parameters
(dimension `n`, sample count `m`, modulus `q ≥ 2`) and a gadget width `ℓ` large enough that
every residue has an `ℓ`-bit representative. The noise law is a separate argument, as in
the LWE layer, and the depth `L` is not a field: correctness theorems take it explicitly. -/
structure Parameters where
  /-- The LWE dimension, sample count and modulus. -/
  lwe : LWE.Parameters
  /-- The gadget width `ℓ`: the number of binary digits per residue. -/
  width : ℕ
  /-- Every residue modulo `q` fits in `ℓ` bits. -/
  modulus_le : lwe.modulus ≤ 2 ^ width

/-- The ciphertext width `N = (n+1)·ℓ` [GSW13, Section 3.1; AP14, Section 3.2]. A reducible
abbreviation, so `Fin P.columns` is notation for `Fin ((n+1)*ℓ)`, the index type of the
existing `Lossy.gadget`. -/
abbrev Parameters.columns (P : Parameters) : ℕ := (P.lwe.dimension + 1) * P.width

/-- `P.columns` is `(n+1)·ℓ`. -/
theorem Parameters.columns_eq (P : Parameters) :
    P.columns = (P.lwe.dimension + 1) * P.width := rfl

/-- A GSW ciphertext is an `(n+1) × N` matrix modulo `q` [AP14, Section 3.2, ciphertext space
`C = Z_q^{n × nℓ}`; Pei16, Section 6.1.3]. Reducible notation. -/
abbrev Ciphertext (P : Parameters) : Type :=
  Matrix (Fin (P.lwe.dimension + 1)) (Fin P.columns) (ZMod P.lwe.modulus)

/-- `Ciphertext P` is the type of `(n+1) × N` matrices modulo `q`. -/
theorem Ciphertext_eq (P : Parameters) :
    Ciphertext P = Matrix (Fin (P.lwe.dimension + 1)) (Fin P.columns) (ZMod P.lwe.modulus) :=
  rfl

/-- The gadget matrix `G = I_{n+1} ⊗ gᵗ` modulo `q`: entry `(i, (j,k))` is `2^k` if `i = j`
and `0` otherwise, column `(j,k)` sitting at position `j·ℓ + k` [Pei16, Section 5.4.3;
AP14, Equation (3.1)]. It is the transpose of the audited integer gadget
`Lossy.gadget ℓ (n+1)`, reduced modulo `q`. -/
def gadget (P : Parameters) : Ciphertext P :=
  fun i j => ((TrapdoorFunctions.Lossy.gadget P.width (P.lwe.dimension + 1) j i : ℤ) :
    ZMod P.lwe.modulus)

/-- Entry `(i,j)` of the gadget is the integer gadget's `(j,i)` entry cast modulo `q`. -/
theorem gadget_apply (P : Parameters) (i : Fin (P.lwe.dimension + 1)) (j : Fin P.columns) :
    gadget P i j =
      ((TrapdoorFunctions.Lossy.gadget P.width (P.lwe.dimension + 1) j i : ℤ) :
        ZMod P.lwe.modulus) := rfl

/-- The `ℓ`-bit digit of a residue: its canonical representative in `[0,q)`, which is below
`2^ℓ` by `P.modulus_le` [GSW13, Section 1.3.3, `BitDecomp` of one coordinate]. -/
def digit (P : Parameters) (u : ZMod P.lwe.modulus) : Fin (2 ^ P.width) :=
  ⟨u.val, lt_of_lt_of_le (ZMod.val_lt u) P.modulus_le⟩

/-- The digit of `u` has value `u.val`. -/
theorem digit_val (P : Parameters) (u : ZMod P.lwe.modulus) : (digit P u : ℕ) = u.val := rfl

/-- `G⁻¹` on a vector [Pei16, Equation (5.4.1); GSW13, Section 1.3.3, `BitDecomp`]: the
`N` bits whose block `j` is the little-endian binary expansion of `u j`'s representative.
It is the inverse of the existing block equivalence `Randomized.blocksEquiv (n+1) ℓ`
applied to the digit vector. -/
def decomposeVec (P : Parameters) (u : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus) :
    Fin P.columns → Bool :=
  (Randomized.blocksEquiv (P.lwe.dimension + 1) P.width).symm (fun j => digit P (u j))

/-- `decomposeVec P u` is the inverse block equivalence applied to the digits of `u`. -/
theorem decomposeVec_eq (P : Parameters) (u : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus) :
    decomposeVec P u =
      (Randomized.blocksEquiv (P.lwe.dimension + 1) P.width).symm (fun j => digit P (u j)) :=
  rfl

/-- `G⁻¹` on a matrix, column by column [Pei16, Equation (5.4.1); AP14, Section 3.1,
deterministic specialization]: column `c` of `decompose P M` is `decomposeVec P` of column
`c` of `M`. The column index type is arbitrary. -/
def decompose (P : Parameters) {ι : Type*}
    (M : Matrix (Fin (P.lwe.dimension + 1)) ι (ZMod P.lwe.modulus)) :
    Matrix (Fin P.columns) ι Bool :=
  fun i c => decomposeVec P (fun j => M j c) i

/-- Entry `(i,c)` of `decompose P M` is bit `i` of the decomposition of column `c`. -/
theorem decompose_apply (P : Parameters) {ι : Type*}
    (M : Matrix (Fin (P.lwe.dimension + 1)) ι (ZMod P.lwe.modulus))
    (i : Fin P.columns) (c : ι) :
    decompose P M i c = decomposeVec P (fun j => M j c) i := rfl

/-- Read a Boolean matrix as its `{0,1}` matrix modulo `q`. Technical glue: GSW's short
matrices (`R`, `G⁻¹(·)`) are stored as Booleans so their shortness holds by typing. -/
def lift (P : Parameters) {κ ι : Type*} (X : Matrix κ ι Bool) : Matrix κ ι (ZMod P.lwe.modulus) :=
  fun i j => ((X i j).toNat : ZMod P.lwe.modulus)

/-- Entry `(i,j)` of `lift P X` is `(X i j).toNat` modulo `q`. -/
theorem lift_apply (P : Parameters) {κ ι : Type*} (X : Matrix κ ι Bool) (i : κ) (j : ι) :
    lift P X i j = ((X i j).toNat : ZMod P.lwe.modulus) := rfl

/-- The digit map of the existing gadget recovers the residue digits of `u` from
`decomposeVec P u` [Pei16, Section 5.4.3].

**Proof sketch.** Read `Lossy.digits_eq` and `decomposeVec_eq`; the composite is
`blocksEquiv (blocksEquiv.symm _)`, which `Equiv.apply_symm_apply` reduces to the digits. -/
theorem digits_decomposeVec (P : Parameters)
    (u : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus) :
    TrapdoorFunctions.Lossy.digits P.width (P.lwe.dimension + 1) (decomposeVec P u) =
      fun j => digit P (u j) := by
  sorry

/-- `G · G⁻¹(u) = u` [Pei16, Section 5.4.3, relation `G · G⁻¹(u) = u (mod q)`].

**Proof sketch.** Coordinate `j` of the left side is the cast of the integer
`(Lossy.gadget ℓ (n+1))ᵗ · x` at `j`, where `x` is the decomposition read as integers.
`Lossy.gadget_mulVec` evaluates it to the digit value, `digits_decomposeVec` and
`digit_val` identify that with `(u j).val`, and `ZMod.natCast_zmod_val` casts back to `u j`.
The integer-to-residue cast commutes with the finite sum by `Int.cast_sum`/`Int.cast_mul`. -/
theorem gadget_mulVec_decomposeVec (P : Parameters)
    (u : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus) :
    (gadget P).mulVec (fun i => ((decomposeVec P u i).toNat : ZMod P.lwe.modulus)) = u := by
  sorry

/-- `G · G⁻¹(M) = M` for every matrix with `n+1` rows [Pei16, Section 5.4.3; AP14,
Equation (3.1)].

**Proof sketch.** Compare column `c`: it is `G` times the lifted decomposition of column
`c` of `M`, which is `gadget_mulVec_decomposeVec` read through `decompose_apply` and
`lift_apply`. -/
theorem gadget_mul_decompose (P : Parameters) {ι : Type*}
    (M : Matrix (Fin (P.lwe.dimension + 1)) ι (ZMod P.lwe.modulus)) :
    gadget P * lift P (decompose P M) = M := by
  sorry

/-- A coordinate equal to zero decomposes to an all-false block.

**Proof sketch.** `Lossy.digits_val` writes the block-`j` digit of `decomposeVec P u` as
`∑ₖ bitₖ · 2^k`; by `digits_decomposeVec` and `digit_val` it equals `(u j).val = 0`. A sum of
nonnegative terms is zero only if every term is, and `2^k > 0`. -/
theorem decomposeVec_block_eq_false (P : Parameters)
    (u : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus) (j : Fin (P.lwe.dimension + 1))
    (hj : u j = 0) (k : Fin P.width) :
    decomposeVec P u (finProdFinEquiv (j, k)) = false := by
  sorry

/-- If `u` vanishes outside coordinate `j₀`, any error vector with entries bounded by `β`
has inner product with the decomposition of `u` at most `ℓ·β` in absolute value. This is
the decryption-noise bound used for the `G⁻¹`-column decryptor.

**Proof sketch.** Split the sum over `Fin ((n+1)ℓ)` through `finProdFinEquiv` into blocks.
Every block `j ≠ j₀` vanishes by `decomposeVec_block_eq_false`. The surviving block has `ℓ`
terms, each of magnitude at most `β`; apply `LWE.binaryErrorSum_bound` with `m := ℓ`. -/
theorem errorSum_decomposeVec_le (P : Parameters)
    (u : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus) (j₀ : Fin (P.lwe.dimension + 1))
    (hu : ∀ j, j ≠ j₀ → u j = 0) (e : Fin P.columns → ℤ) (β : ℕ)
    (he : ∀ i, (e i).natAbs ≤ β) :
    (∑ i, e i * ((decomposeVec P u i).toNat : ℤ)).natAbs ≤ P.width * β := by
  sorry

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
```

## ===== TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Noise.lean (Lean, at 48d796a8a68cd50897047f01825a8132dd19e8d8) =====

```lean
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Gadget
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The GSW noise invariant and its homomorphic operations

## Main definitions

* `Encrypts P t x β C`: `tᵗ C = x · tᵗ G + eᵗ (mod q)` for an integer error vector `e` with
  every entry of magnitude at most `β`. This is the key-agnostic invariant of [AP14,
  Definitions 3.2–3.3] with an explicit worst-case bound.
* `mul`: `C₁ ⊡ C₂ = C₁ · G⁻¹(C₂)`; `nand`: `G − C₁ ⊡ C₂`; `chain`: the right-associative
  product `C₁ ⊡ (C₂ ⊡ (⋯ ⊡ acc))`.

## Main results

* `encrypts_gadget`, `encrypts_zero`: `G` encrypts `1` and `0` encrypts `0`, both noiseless.
* `Encrypts.add`, `.neg`, `.sub`, `.sum`, `.mono`: additive closure.
* `Encrypts.mul`: **asymmetric** multiplication: the left operand's noise is multiplied by
  `N` (a bound on `‖G⁻¹(C₂)‖`), the right operand's only by `|x₁|`.
* `Encrypts.mul_bit`, `Encrypts.mul_le`: the bit-message and symmetric `(N+1)·max` corollaries.
* `Encrypts.nand`: NAND of two bit encryptions with noise `N·β₁ + β₂ ≤ (N+1)·max`.
* `encrypts_chain`: a right-associative chain of `k` bit encryptions times an accumulator has
  noise `β_acc + k·N·β`, additive in `k`.

## References

* [AP14] J. Alperin-Sheriff, C. Peikert, *Faster Bootstrapping with Polynomial Error*,
  CRYPTO 2014; ePrint 2014/094 version dated 13 June 2014, Section 3.2 (operations),
  Definitions 3.2–3.3, Lemma 3.5, Corollary 3.6.
* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated
  17 February 2016, Section 6.1.3, Equations (6.1.5)–(6.1.6).
* [GSW13] C. Gentry, A. Sahai, B. Waters, CRYPTO 2013; author version dated 8 June 2013,
  Sections 1.3.1, 1.3.3, 3.3 (`Add`, `Mult`, `NAND`) and 3.4.
* [BV14] Z. Brakerski, V. Vaikuntanathan, *Lattice-Based FHE as Secure as PKE*, ITCS 2014;
  ePrint 2013/541, Claims 3.4.1–3.4.2.

**Convention and deviations.** Ciphertexts and keys follow [AP14, Section 3.2] and
[Pei16, Section 6.1.3]: `t` is a *left* approximate singular vector, `tᵗ C ≈ x · tᵗ G`, and
multiplication is `C₁ · G⁻¹(C₂)`. Its error is `e₁ᵗ G⁻¹(C₂) + x₁ e₂ᵗ` [AP14, Lemma 3.5]: the
**left** operand's error is expanded, the **right** operand's is scaled by the left message.
[GSW13] and [BV14] use the transposed convention (`C · v ≈ μ v`, square `{0,1}` ciphertexts
after `Flatten`), in which `C₁ · C₂` has error `μ₂ e₁ + C₁ e₂` [GSW13, Section 3.3]: there the
*right* operand's error is expanded. The two conventions are mirror images; a chain with
additive noise puts fresh ciphertexts on the left here, on the right in [BV14, Claim 3.4.2].
Noise bounds are worst-case (`ℓ∞`, `ℕ`-valued), not [AP14]'s subgaussian parameters, so a
`k`-fold chain grows like `k·N·β` rather than `√k`. [GSW13]'s NAND is `I_N − C₁·C₂` after
`Flatten`; here it is `G − C₁·G⁻¹(C₂)`, with the same `(N+1)·B` bound [GSW13, Section 3.4].
-/

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

/-- Homomorphic multiplication `C₁ ⊡ C₂ = C₁ · G⁻¹(C₂)` [AP14, Section 3.2; Pei16,
Equation (6.1.6)]. Deterministic, right operand decomposed. -/
def mul (P : Parameters) (C₁ C₂ : Ciphertext P) : Ciphertext P :=
  C₁ * lift P (decompose P C₂)

/-- `mul P C₁ C₂` is `C₁` times the lifted binary decomposition of `C₂`. -/
theorem mul_eq (P : Parameters) (C₁ C₂ : Ciphertext P) :
    mul P C₁ C₂ = C₁ * lift P (decompose P C₂) := rfl

/-- Homomorphic NAND `G − C₁ ⊡ C₂` [GSW13, Section 3.3, `NAND`, gadget form; Pei16,
Section 6.1.3, "`(x₁ NAND x₂) = 1 − x₁x₂`"]. -/
def nand (P : Parameters) (C₁ C₂ : Ciphertext P) : Ciphertext P :=
  gadget P - mul P C₁ C₂

/-- `nand P C₁ C₂` is the gadget minus the homomorphic product. -/
theorem nand_eq (P : Parameters) (C₁ C₂ : Ciphertext P) :
    nand P C₁ C₂ = gadget P - mul P C₁ C₂ := rfl

/-- The right-associative product chain `C₁ ⊡ (C₂ ⊡ (⋯ ⊡ (Cₖ ⊡ acc)))` [AP14, Corollary 3.6,
with `acc = G`; Pei16, Section 6.1.3, "Bootstrapping": right-associative chains]. -/
def chain (P : Parameters) (Cs : List (Ciphertext P)) (acc : Ciphertext P) : Ciphertext P :=
  Cs.foldr (mul P) acc

/-- The empty chain is its accumulator. -/
theorem chain_nil (P : Parameters) (acc : Ciphertext P) : chain P [] acc = acc := rfl

/-- A nonempty chain multiplies its head on the left of the remaining chain. -/
theorem chain_cons (P : Parameters) (C : Ciphertext P) (Cs : List (Ciphertext P))
    (acc : Ciphertext P) : chain P (C :: Cs) acc = mul P C (chain P Cs acc) := rfl

/-- **The GSW noise invariant.** `C` encrypts the integer `x` under the key vector `t` with
noise at most `β`: there is an integer error vector `e`, every entry of magnitude at most
`β`, with `tᵗ C = x · tᵗ G + eᵗ` modulo `q` [AP14, Definitions 3.2–3.3; Pei16, Section 6.1.3,
`sᵗ A ≈ x · sᵗ G`; BV14, Definition 3.1, transposed]. The predicate does not fix how `C` was
produced, so it is shared by public-key, secret-key and evaluated ciphertexts. -/
def Encrypts (P : Parameters) (t : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus) (x : ℤ)
    (β : ℕ) (C : Ciphertext P) : Prop :=
  ∃ e : Fin P.columns → ℤ, (∀ j, (e j).natAbs ≤ β) ∧
    Matrix.vecMul t C = (x : ZMod P.lwe.modulus) • Matrix.vecMul t (gadget P) +
      fun j => (e j : ZMod P.lwe.modulus)

/-- `Encrypts P t x β C` holds exactly when some `β`-bounded integer error vector `e` gives
`tᵗ C = x · tᵗ G + e`. -/
theorem encrypts_iff (P : Parameters) (t : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus)
    (x : ℤ) (β : ℕ) (C : Ciphertext P) :
    Encrypts P t x β C ↔ ∃ e : Fin P.columns → ℤ, (∀ j, (e j).natAbs ≤ β) ∧
      Matrix.vecMul t C = (x : ZMod P.lwe.modulus) • Matrix.vecMul t (gadget P) +
        fun j => (e j : ZMod P.lwe.modulus) := Iff.rfl

section Closure

variable (P : Parameters) {t : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus}

/-- The gadget encrypts `1` with zero noise [AP14, Section 3.3, "`μG` … has error 0"].

**Proof sketch.** Take `e = 0`; `1 • v + 0 = v`. -/
theorem encrypts_gadget : Encrypts P t 1 0 (gadget P) := by
  sorry

/-- The zero matrix encrypts `0` with zero noise [AP14, Section 3.3].

**Proof sketch.** Take `e = 0`; `Matrix.vecMul_zero` and `zero_smul`. -/
theorem encrypts_zero : Encrypts P t 0 0 0 := by
  sorry

/-- Weakening the noise bound preserves the invariant.

**Proof sketch.** Reuse the witness; `le_trans` on each entry. -/
theorem Encrypts.mono {x : ℤ} {β β' : ℕ} {C : Ciphertext P} (h : Encrypts P t x β C)
    (hβ : β ≤ β') : Encrypts P t x β' C := by
  sorry

/-- Homomorphic addition adds messages and noise bounds [AP14, Lemma 3.5, first claim;
GSW13, Section 3.3, `Add`; BV14, Claim 3.4.1].

**Proof sketch.** Witness `e₁ + e₂`. `Matrix.vecMul_add` splits `tᵗ(C₁+C₂)`; `add_smul` and
`Int.cast_add` regroup; `Int.natAbs_add_le` bounds the entries. -/
theorem Encrypts.add {x₁ x₂ : ℤ} {β₁ β₂ : ℕ} {C₁ C₂ : Ciphertext P}
    (h₁ : Encrypts P t x₁ β₁ C₁) (h₂ : Encrypts P t x₂ β₂ C₂) :
    Encrypts P t (x₁ + x₂) (β₁ + β₂) (C₁ + C₂) := by
  sorry

/-- Negation negates the message and keeps the noise bound.

**Proof sketch.** Witness `-e`; `Matrix.vecMul_neg`, `neg_smul`, `Int.natAbs_neg`. -/
theorem Encrypts.neg {x : ℤ} {β : ℕ} {C : Ciphertext P} (h : Encrypts P t x β C) :
    Encrypts P t (-x) β (-C) := by
  sorry

/-- Subtraction subtracts messages and adds noise bounds.

**Proof sketch.** `sub_eq_add_neg`, then `Encrypts.add` and `Encrypts.neg`. -/
theorem Encrypts.sub {x₁ x₂ : ℤ} {β₁ β₂ : ℕ} {C₁ C₂ : Ciphertext P}
    (h₁ : Encrypts P t x₁ β₁ C₁) (h₂ : Encrypts P t x₂ β₂ C₂) :
    Encrypts P t (x₁ - x₂) (β₁ + β₂) (C₁ - C₂) := by
  sorry

/-- A finite sum of encryptions encrypts the sum of the messages with the sum of the noise
bounds [AP14, Section 4.1, Equation (4.1), the outer homomorphic sum].

**Proof sketch.** `Finset.induction_on`; the empty sum is `encrypts_zero`, and each insertion
is `Encrypts.add`. -/
theorem Encrypts.sum {ι : Type*} (s : Finset ι) (x : ι → ℤ) (β : ι → ℕ)
    (C : ι → Ciphertext P) (h : ∀ i ∈ s, Encrypts P t (x i) (β i) (C i)) :
    Encrypts P t (∑ i ∈ s, x i) (∑ i ∈ s, β i) (∑ i ∈ s, C i) := by
  sorry

/-- **Asymmetric homomorphic multiplication** [AP14, Lemma 3.5; Pei16, Equation (6.1.6);
BV14, Claim 3.4.2, mirrored]. If `C₁` encrypts `x₁` with noise `β₁` and `C₂` encrypts `x₂`
with noise `β₂`, then `C₁ ⊡ C₂` encrypts `x₁x₂` with noise at most `N·β₁ + |x₁|·β₂`. The left
operand's noise is multiplied by `N`, the number of `{0,1}` entries in a column of `G⁻¹(C₂)`;
the right operand's is multiplied only by the left message.

**Proof sketch.** `Matrix.vecMul_vecMul` rewrites `tᵗ (C₁ X)` as `(tᵗ C₁) X` with
`X = lift (G⁻¹ C₂)`. Substitute `h₁`: `(x₁ tᵗG + e₁ᵗ) X = x₁ tᵗ(G X) + e₁ᵗ X`. By
`gadget_mul_decompose`, `G X = C₂`, so the first term is `x₁ tᵗ C₂ = x₁x₂ tᵗG + x₁ e₂ᵗ` by `h₂`.
The witness is `j ↦ (∑ᵢ e₁ i · X i j) + x₁ · e₂ j`. The first summand is a binary subset sum of
`N` entries bounded by `β₁`, bounded by `N·β₁` via `LWE.binaryErrorSum_bound`; the second has
magnitude `|x₁|·|e₂ j| ≤ |x₁|·β₂` (`Int.natAbs_mul`). -/
theorem Encrypts.mul {x₁ x₂ : ℤ} {β₁ β₂ : ℕ} {C₁ C₂ : Ciphertext P}
    (h₁ : Encrypts P t x₁ β₁ C₁) (h₂ : Encrypts P t x₂ β₂ C₂) :
    Encrypts P t (x₁ * x₂) (P.columns * β₁ + x₁.natAbs * β₂) (mul P C₁ C₂) := by
  sorry

/-- For a bit message on the left, multiplication has noise `N·β₁ + β₂` [GSW13, Section 3.3,
`Mult`; Pei16, Section 6.1.3].

**Proof sketch.** `Encrypts.mul` and `Encrypts.mono`, since `(b.toNat : ℤ).natAbs ≤ 1`. -/
theorem Encrypts.mul_bit {b : Bool} {x₂ : ℤ} {β₁ β₂ : ℕ} {C₁ C₂ : Ciphertext P}
    (h₁ : Encrypts P t (b.toNat : ℤ) β₁ C₁) (h₂ : Encrypts P t x₂ β₂ C₂) :
    Encrypts P t ((b.toNat : ℤ) * x₂) (P.columns * β₁ + β₂) (GSW.mul P C₁ C₂) := by
  sorry

/-- Symmetric corollary: two bit-message operands with noise at most `β` give a product with
noise at most `(N+1)·β` [GSW13, Section 3.4; Pei16, Section 6.1.3].

**Proof sketch.** `Encrypts.mul_bit` and `N·β + β = (N+1)·β`. -/
theorem Encrypts.mul_le {b₁ b₂ : Bool} {β : ℕ} {C₁ C₂ : Ciphertext P}
    (h₁ : Encrypts P t (b₁.toNat : ℤ) β C₁) (h₂ : Encrypts P t (b₂.toNat : ℤ) β C₂) :
    Encrypts P t ((b₁ && b₂).toNat : ℤ) ((P.columns + 1) * β) (GSW.mul P C₁ C₂) := by
  sorry

/-- **Homomorphic NAND** [GSW13, Sections 3.3–3.4, `NAND`, "the error is increased by a
factor of at most `N + 1`"; Pei16, Section 6.1.3]. Bit encryptions with noise `β₁`, `β₂` give
an encryption of `NAND(b₁,b₂)` with noise at most `N·β₁ + β₂`.

**Proof sketch.** `encrypts_gadget`, `Encrypts.mul_bit`, `Encrypts.sub`; the message
`1 − b₁b₂` equals `(!(b₁ && b₂)).toNat` by cases on the bits. -/
theorem Encrypts.nand {b₁ b₂ : Bool} {β₁ β₂ : ℕ} {C₁ C₂ : Ciphertext P}
    (h₁ : Encrypts P t (b₁.toNat : ℤ) β₁ C₁) (h₂ : Encrypts P t (b₂.toNat : ℤ) β₂ C₂) :
    Encrypts P t ((!(b₁ && b₂)).toNat : ℤ) (P.columns * β₁ + β₂) (nand P C₁ C₂) := by
  sorry

/-- **Product chains grow additively** [AP14, Corollary 3.6, worst-case form; Pei16,
Section 6.1.3, "any polynomial-length chain of homomorphic bit-multiplications on fresh
ciphertexts, if done in a right-associative manner, incurs only polynomial error growth";
BV14, Claim 3.4.2 and the proof of Lemma 3.6, mirrored]. If every `Cᵢ` encrypts the bit `bᵢ`
with noise at most `β` and `acc` encrypts `x` with noise `β₀`, then
`C₁ ⊡ (⋯ ⊡ (Cₖ ⊡ acc))` encrypts `(∏ bᵢ)·x` with noise at most `β₀ + k·N·β`.

**Proof sketch.** Induction on the list. The step is `Encrypts.mul_bit` with the head on the
left: noise `N·β + (previous)`, message `b · (∏ rest · x)`; reassociate the product and the
sum `β₀ + (k+1)·N·β`. -/
theorem encrypts_chain {bs : List Bool} {Cs : List (Ciphertext P)} {β β₀ : ℕ} {x : ℤ}
    {acc : Ciphertext P}
    (hs : List.Forall₂ (fun b C => Encrypts P t (b.toNat : ℤ) β C) bs Cs)
    (hacc : Encrypts P t x β₀ acc) :
    Encrypts P t (((bs.all id).toNat : ℤ) * x) (β₀ + Cs.length * (P.columns * β))
      (chain P Cs acc) := by
  sorry

end Closure

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
```

## ===== TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Scheme.lean (Lean, at 48d796a8a68cd50897047f01825a8132dd19e8d8) =====

```lean
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Noise
import TCSlib.Cryptography.Encryption.PublicKey.Regev.Basic
import TCSlib.Cryptography.Encryption.PublicKey.Regev.Experiments
import Mathlib.Data.Fin.Tuple.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Public-key GSW: key generation, encryption, decryption and fresh-noise correctness

## Main definitions

* Key generation is the existing Regev key generation `Regev.keygen P.lwe χ`; GSW adds no
  key material.
* `secretVector`: the key vector `t = (−s, 1)`, with `tᵗ Ā = eᵗ` for the augmented public key.
* `encrypt`: `C = Ā R + μ G`, with `Ā` the existing `Regev.augmented` public key and
  `R ∈ {0,1}^{m×N}`.
* `halfVector`, `decryptColumn`, `decrypt`: decrypt by the existing Regev decryptor applied
  to the column `C · G⁻¹(⌊q/2⌋ e_{n+1})`.

## Main results

* `vecMul_secretVector_augmented`: `tᵗ Ā = eᵗ` [Pei16, Equation (6.1.7)].
* `encrypts_encrypt`: a fresh encryption has noise at most `m·B`.
* `decrypt_of_encrypts`: noise `β` with `2·(ℓ·β) < ⌊q/2⌋` decrypts correctly.
* `decrypt_of_encrypts_dyadic`: at `q = 2^ℓ` the factor `ℓ` disappears.
* `decrypt_keygen_encrypt`: every-coin correctness of the basic scheme.

## References

* [GSW13] C. Gentry, A. Sahai, B. Waters, CRYPTO 2013; author version dated 8 June 2013,
  Section 3.1 (`SecretKeyGen`, `PublicKeyGen`, `Enc`, `Dec`).
* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated
  17 February 2016, Section 6.1.3 (Equation (6.1.7), "Fully homomorphic encryption").
* [AP14] J. Alperin-Sheriff, C. Peikert, ePrint 2014/094 version dated 13 June 2014,
  Section 3.2 (`GSW.Dec`) and Claim 3.4.
* [BV14] Z. Brakerski, V. Vaikuntanathan, ePrint 2013/541, Section 3.1 (`NCCrypt.PubEnc`,
  `NCCrypt.Dec`) and Lemma 3.2.

**Deviations.** (1) Gadget form: `C = ĀR + μG` [Pei16, Section 6.1.3, with the sign of `R`
flipped] instead of [GSW13]'s `Flatten(μ·I_N + BitDecomp(R·A))`; [GSW13, Section 3.2] notes
`BitDecomp⁻¹(C) = μG + RA`, so the two carry the same information. (2) Rows are samples in the
LWE layer, so `Ā` is the transpose-plus-value-row `Regev.augmented`, and `t = (−s, 1)` puts
the `1` last (GSW13 puts it first). (3) Decryption: [GSW13] reads the row with `vᵢ = 2^i ∈
(q/4, q/2]`, [AP14] the penultimate column (`2^{ℓ−2} ∈ [q/4, q/2)`), both with error `< q/8`
and a custom rounding. Here the column `C · G⁻¹(⌊q/2⌋ e_{n+1})` is a Regev ciphertext of the
message, so the audited `Regev.decrypt` and its strict nearest-codepoint rule are reused for
every `q ≥ 2`; the price is a factor `≤ ℓ` in the decryption noise, which disappears for
`q = 2^ℓ`. (4) Noise is a finite-seed bounded law, so correctness holds for every coin, not
with overwhelming probability [BV14, Lemma 3.3]. The secret is uniform, as in the LWE layer.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

open Encryption.PublicKey

/-- The GSW key vector `t = (−s, 1) ∈ Z_q^{n+1}` [GSW13, Section 3.1, `SecretKeyGen`, with the
`1` moved last; Pei16, Section 6.1.3, `s = (−s̄, 1)`]. -/
def secretVector (P : Parameters) (s : Fin P.lwe.dimension → ZMod P.lwe.modulus) :
    Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus :=
  Fin.snoc (α := fun _ => ZMod P.lwe.modulus) (-s) 1

/-- `secretVector P s` is `−s` followed by `1`. -/
theorem secretVector_eq (P : Parameters) (s : Fin P.lwe.dimension → ZMod P.lwe.modulus) :
    secretVector P s = Fin.snoc (α := fun _ => ZMod P.lwe.modulus) (-s) 1 := rfl

/-- `tᵗ Ā = eᵗ`: the key vector annihilates the augmented LWE public key up to the row errors
[Pei16, Equation (6.1.7); GSW13, Section 3.1, "Observe that `A · s = e`"].

**Proof sketch.** Column `i` of `Regev.augmented` is the `i`-th sample's row followed by its
value (`Regev.augmented_eq`, `Fin.sum_univ_castSucc`, `Fin.snoc_castSucc`, `Fin.snoc_last`). The
inner product is `−⟨s, aᵢ⟩ + (⟨aᵢ, s⟩ + eᵢ)` by `LWE.noisyValues_apply`, which is `eᵢ`. -/
theorem vecMul_secretVector_augmented (P : Parameters)
    (A : Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus))
    (s : Fin P.lwe.dimension → ZMod P.lwe.modulus) (e : Fin P.lwe.samples → ℤ) :
    Matrix.vecMul (secretVector P s) (Regev.augmented P.lwe (A, LWE.noisyValues P.lwe A s e)) =
      fun i => (e i : ZMod P.lwe.modulus) := by
  sorry

/-- Public-key GSW encryption `C = Ā R + μ G` with `R ∈ {0,1}^{m×N}` [Pei16, Section 6.1.3,
"An encryption of an integer `x` is a matrix `A = xG − ĀR`", sign of `R` flipped; GSW13,
Section 3.1, `Enc`, gadget form]. The public key is a Regev/LWE public key `(A, b)`. -/
def encrypt (P : Parameters)
    (pk : Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus))
    (μ : Bool) (R : Matrix (Fin P.lwe.samples) (Fin P.columns) Bool) : Ciphertext P :=
  Regev.augmented P.lwe pk * lift P R + (μ.toNat : ZMod P.lwe.modulus) • gadget P

/-- `encrypt P pk μ R` is the augmented public key times the lifted `R`, plus `μ` times `G`. -/
theorem encrypt_eq (P : Parameters)
    (pk : Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus))
    (μ : Bool) (R : Matrix (Fin P.lwe.samples) (Fin P.columns) Bool) :
    encrypt P pk μ R =
      Regev.augmented P.lwe pk * lift P R + (μ.toNat : ZMod P.lwe.modulus) • gadget P := rfl

/-- The target `w = ⌊q/2⌋ · e_{n+1}`: zero in the first `n` coordinates and the Regev bit
codepoint for `true` in the last. Technical decryption glue. -/
def halfVector (P : Parameters) : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus :=
  Fin.snoc (α := fun _ => ZMod P.lwe.modulus) 0 (LWE.BitEncoding.codepoint P.lwe true)

/-- `halfVector P` is `0` followed by `codepoint true = ⌊q/2⌋`. -/
theorem halfVector_eq (P : Parameters) :
    halfVector P =
      Fin.snoc (α := fun _ => ZMod P.lwe.modulus) 0 (LWE.BitEncoding.codepoint P.lwe true) := rfl

/-- The decryption column `C · G⁻¹(w)`. For a valid encryption of `μ` it is a Regev
ciphertext of `μ` in augmented form [GSW13, Section 3.1, "Dec is a BitDecomp'd version of
Regev's decryption procedure"; AP14, Section 3.2, `GSW.Dec`, generalized column]. -/
def decryptColumn (P : Parameters) (C : Ciphertext P) :
    Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus :=
  C.mulVec (fun i => ((decomposeVec P (halfVector P) i).toNat : ZMod P.lwe.modulus))

/-- `decryptColumn P C` is `C` applied to the lifted decomposition of `halfVector P`. -/
theorem decryptColumn_eq (P : Parameters) (C : Ciphertext P) :
    decryptColumn P C =
      C.mulVec (fun i => ((decomposeVec P (halfVector P) i).toNat : ZMod P.lwe.modulus)) := rfl

/-- GSW decryption: split the decryption column into its first `n` coordinates and its last
coordinate, and apply the existing Regev decryptor [GSW13, Section 3.1, `Dec`; BV14,
Section 3.1, `NCCrypt.Dec`, "standard Regev decryption"]. -/
def decrypt (P : Parameters) (s : Fin P.lwe.dimension → ZMod P.lwe.modulus)
    (C : Ciphertext P) : Bool :=
  Regev.decrypt P.lwe s (Fin.init (decryptColumn P C), decryptColumn P C (Fin.last _))

/-- `decrypt P s C` is Regev decryption of the split decryption column. -/
theorem decrypt_eq (P : Parameters) (s : Fin P.lwe.dimension → ZMod P.lwe.modulus)
    (C : Ciphertext P) :
    decrypt P s C =
      Regev.decrypt P.lwe s (Fin.init (decryptColumn P C), decryptColumn P C (Fin.last _)) :=
  rfl

/-- **Fresh-encryption noise.** With row errors bounded by `B`, a public-key encryption of `μ`
encrypts `μ` under `t = (−s,1)` with noise at most `m·B` [GSW13, Section 3.1, "The error
`⟨Rᵢ, e⟩` has magnitude at most `‖e‖₁`"; Pei16, Section 6.1.3].

**Proof sketch.** `Matrix.vecMul_add`, `Matrix.vecMul_smul` and `Matrix.vecMul_vecMul` give
`tᵗ C = (tᵗ Ā) R + μ tᵗ G`; `vecMul_secretVector_augmented` replaces `tᵗ Ā` by `eᵗ`. The
witness is `j ↦ ∑ᵢ eᵢ · R i j`, bounded by `m·B` through `LWE.binaryErrorSum_bound`. -/
theorem encrypts_encrypt (P : Parameters)
    (A : Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus))
    (s : Fin P.lwe.dimension → ZMod P.lwe.modulus) (e : Fin P.lwe.samples → ℤ) (B : ℕ)
    (he : ∀ i, (e i).natAbs ≤ B) (μ : Bool)
    (R : Matrix (Fin P.lwe.samples) (Fin P.columns) Bool) :
    Encrypts P (secretVector P s) (μ.toNat : ℤ) (P.lwe.samples * B)
      (encrypt P (A, LWE.noisyValues P.lwe A s e) μ R) := by
  sorry

/-- Fresh-encryption noise for the actual key generator and a `B`-bounded noise law.

**Proof sketch.** Read `Regev.keygen_fst`, `Regev.keygen_snd`, `LWE.sample_fst`,
`LWE.sample_snd` and `Noise.bounded_iff`, then apply `encrypts_encrypt`. -/
theorem encrypts_keygen_encrypt (P : Parameters) (χ : LWE.Noise)
    (rg : Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      ((Fin P.lwe.dimension → ZMod P.lwe.modulus) × (Fin P.lwe.samples → χ.Coins)))
    (B : ℕ) (hχ : χ.Bounded B) (μ : Bool)
    (R : Matrix (Fin P.lwe.samples) (Fin P.columns) Bool) :
    Encrypts P (secretVector P (Regev.keygen P.lwe χ rg).2) (μ.toNat : ℤ) (P.lwe.samples * B)
      (encrypt P (Regev.keygen P.lwe χ rg).1 μ R) := by
  sorry

/-- **Decryption from the invariant.** If `C` encrypts the bit `b` under `t = (−s,1)` with
noise `β` and `2·(ℓ·β) < ⌊q/2⌋`, then `decrypt P s C = b` [GSW13, Section 3.1, "if
`xᵢ = μ·vᵢ + e'` for some error `e'` of magnitude at most `q/8` … Dec … output[s] the correct
value"; AP14, Claim 3.4; BV14, Lemma 3.2].

**Proof sketch.** `Regev.decrypt_eq` reads `c.2 − ⟨s, c.1⟩`, which for the split column `v` is
`⟨t, v⟩` (`Fin.sum_univ_castSucc`, `secretVector_eq`). `Matrix.dotProduct_mulVec` turns
`⟨t, C x⟩` into `⟨tᵗC, x⟩` with `x = G⁻¹(w)` lifted; substituting the invariant gives
`b·⟨t, G x⟩ + ⟨e, x⟩ = b·⟨t, w⟩ + ⟨e, x⟩` by `gadget_mulVec_decomposeVec`, and `⟨t, w⟩ = ⌊q/2⌋`
because `w` vanishes off the last coordinate where `t` is `1`. So the residual is
`codepoint b + ⟨e, x⟩`. `errorSum_decomposeVec_le` (with `j₀ = last`) bounds `|⟨e, x⟩| ≤ ℓ·β`,
and `LWE.BitEncoding.decode_codepoint_add` with `B := ℓ·β` finishes. -/
theorem decrypt_of_encrypts (P : Parameters) (s : Fin P.lwe.dimension → ZMod P.lwe.modulus)
    (b : Bool) (β : ℕ) (C : Ciphertext P) (h : Encrypts P (secretVector P s) (b.toNat : ℤ) β C)
    (hsep : 2 * (P.width * β) < P.lwe.modulus / 2) :
    decrypt P s C = b := by
  sorry

/-- At a power-of-two modulus `q = 2^ℓ` with `ℓ ≥ 1`, noise `β` with `2β < q/2` decrypts
correctly: `⌊q/2⌋ = 2^{ℓ−1}` has a single binary digit, so the decryption column is the last
gadget column [AP14, Claim 3.4, dyadic case; GSW13, Section 3.1, `MPDec` remark].

**Proof sketch.** As `decrypt_of_encrypts`, but the decomposition of `w` has exactly one `1`,
at block `n+1` position `ℓ−1`; the error sum is a single entry of `e`, bounded by `β`. -/
theorem decrypt_of_encrypts_dyadic (P : Parameters)
    (hq : P.lwe.modulus = 2 ^ P.width) (hℓ : 0 < P.width)
    (s : Fin P.lwe.dimension → ZMod P.lwe.modulus) (b : Bool) (β : ℕ) (C : Ciphertext P)
    (h : Encrypts P (secretVector P s) (b.toNat : ℤ) β C)
    (hsep : 2 * β < P.lwe.modulus / 2) :
    decrypt P s C = b := by
  sorry

/-- **Basic correctness.** Every key-generation seed, message and encryption coin matrix
decrypts correctly when the noise law is `B`-bounded and `2·(ℓ·(m·B)) < ⌊q/2⌋` [GSW13,
Section 3.1; BV14, Lemmas 3.2–3.3, worst-case form].

**Proof sketch.** `encrypts_keygen_encrypt`, then `decrypt_of_encrypts`. -/
theorem decrypt_keygen_encrypt (P : Parameters) (χ : LWE.Noise)
    (rg : Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      ((Fin P.lwe.dimension → ZMod P.lwe.modulus) × (Fin P.lwe.samples → χ.Coins)))
    (B : ℕ) (hχ : χ.Bounded B) (μ : Bool)
    (R : Matrix (Fin P.lwe.samples) (Fin P.columns) Bool)
    (hsep : 2 * (P.width * (P.lwe.samples * B)) < P.lwe.modulus / 2) :
    decrypt P (Regev.keygen P.lwe χ rg).2 (encrypt P (Regev.keygen P.lwe χ rg).1 μ R) = μ := by
  sorry

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
```

## ===== TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Eval.lean (Lean, at 48d796a8a68cd50897047f01825a8132dd19e8d8) =====

```lean
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Scheme
import TCSlib.Complexity.CircuitComplexity.DAGCircuit

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Homomorphic evaluation of the library's Boolean circuits, and leveled correctness

## Main definitions

* `homAnd`: `[] ↦ G`, `[C] ↦ C`, `C :: Cs ↦ C ⊡ homAnd Cs` (a product chain).
* `homNot`: `G − homAnd`; `homOr`: `G − homAnd (map (G − ·))` (De Morgan).
* `homGate`: the homomorphic counterpart of `BoolCircuit.DAGGate.eval`, gate kind by gate kind.
* `evalValues`, `eval`: run `homGate` over a `BoolCircuit.DAGCircuit` with the existing
  `BoolCircuit.runWith` host, and read the output vertex.

## Main results

* `homAnd_encrypts`, `homGate_encrypts`: per-gate noise `(N+1)·β` for fan-in at most two.
* `eval_encrypts`: a fan-in-two circuit of depth `d` maps `β`-noisy bit encryptions to a
  `(N+1)^d·β`-noisy encryption of its output [GSW13, Section 3.3, "Circuits"].
* `decrypt_keygen_eval`: **leveled correctness** for depth `≤ L` whenever
  `2·(ℓ·((N+1)^L·(m·B))) < ⌊q/2⌋`, for every key, input and coin.

## References

* [GSW13] C. Gentry, A. Sahai, B. Waters, CRYPTO 2013; author version dated 8 June 2013,
  Section 3.3 ("Circuits": error `(N+1)^L · B` for NAND-depth `L`) and Section 3.4 (condition
  `q/B > 8(N+1)^L`).
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009, Definition 6.1 (the circuit model of `DAGCircuit`).
* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated
  17 February 2016, Section 6.1.3 (NAND as `1 − x₁x₂`).

**Deviations.** The circuit model is the library's `DAGCircuit` (`∧`, `∨`, `¬` gates of
fan-in at most two), not a NAND-only circuit: `∧` is one GSW product, `¬` is `G − ·`, `∨` is
De Morgan through two negations, so every gate costs at most one product and the bound
`(N+1)^depth · β` of [GSW13, Section 3.3] holds with the library's own `depth`. [GSW13]'s
"NAND-depth" and the library's depth differ by at most a constant factor for a translated
circuit. Correctness is every-coin under a worst-case bound, not with overwhelming
probability. The relation to [GSW13, Section 3.4]'s `q/B > 8(N+1)^L`: here the decryption
condition carries an extra factor `ℓ` (one for `q = 2^ℓ`) and the fresh noise is `m·B`.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

open BoolCircuit
open Encryption.PublicKey

/-- Homomorphic conjunction of a list of ciphertexts: the gadget for the empty list, the
ciphertext itself for a singleton, and a left-to-right product chain otherwise [Pei16,
Section 6.1.3; AP14, Corollary 3.6]. The singleton case avoids a needless product. -/
def homAnd (P : Parameters) : List (Ciphertext P) → Ciphertext P
  | [] => gadget P
  | [C] => C
  | C :: C' :: Cs => mul P C (homAnd P (C' :: Cs))

/-- The empty conjunction is the noiseless encryption `G` of `1`. -/
theorem homAnd_nil (P : Parameters) : homAnd P [] = gadget P := rfl

/-- A one-element conjunction is that ciphertext. -/
theorem homAnd_singleton (P : Parameters) (C : Ciphertext P) : homAnd P [C] = C := rfl

/-- A conjunction of at least two ciphertexts multiplies the head on the left. -/
theorem homAnd_cons_cons (P : Parameters) (C C' : Ciphertext P) (Cs : List (Ciphertext P)) :
    homAnd P (C :: C' :: Cs) = mul P C (homAnd P (C' :: Cs)) := rfl

/-- Homomorphic negated conjunction `G − homAnd Cs`, matching the library's `¬` gate, which
negates the conjunction of its inputs [Pei16, Section 6.1.3, NAND as `1 − x₁x₂`]. -/
def homNot (P : Parameters) (Cs : List (Ciphertext P)) : Ciphertext P :=
  gadget P - homAnd P Cs

/-- `homNot P Cs` is the gadget minus the homomorphic conjunction. -/
theorem homNot_eq (P : Parameters) (Cs : List (Ciphertext P)) :
    homNot P Cs = gadget P - homAnd P Cs := rfl

/-- Homomorphic disjunction by De Morgan: `G − homAnd (G − C₁, …, G − Cₖ)`. -/
def homOr (P : Parameters) (Cs : List (Ciphertext P)) : Ciphertext P :=
  gadget P - homAnd P (Cs.map fun C => gadget P - C)

/-- `homOr P Cs` is the gadget minus the conjunction of the complements. -/
theorem homOr_eq (P : Parameters) (Cs : List (Ciphertext P)) :
    homOr P Cs = gadget P - homAnd P (Cs.map fun C => gadget P - C) := rfl

/-- The homomorphic counterpart of `DAGGate.eval`: read each argument vertex's ciphertext
(the noiseless `0` encryption of `false` out of range, matching `getD … false`) and apply
`homAnd`, `homOr` or `homNot` by gate kind. -/
def homGate (P : Parameters) (g : DAGGate) (cts : List (Ciphertext P)) : Ciphertext P :=
  match g.kind with
  | .and => homAnd P (g.args.map fun a => cts.getD a 0)
  | .or => homOr P (g.args.map fun a => cts.getD a 0)
  | .not => homNot P (g.args.map fun a => cts.getD a 0)

/-- The homomorphic gate dispatches on the gate kind exactly as `DAGGate.eval_eq`. -/
theorem homGate_eq (P : Parameters) (g : DAGGate) (cts : List (Ciphertext P)) :
    homGate P g cts = match g.kind with
      | .and => homAnd P (g.args.map fun a => cts.getD a 0)
      | .or => homOr P (g.args.map fun a => cts.getD a 0)
      | .not => homNot P (g.args.map fun a => cts.getD a 0) := rfl

/-- The ciphertexts of all vertices: the input ciphertexts, then one per gate, computed by
the existing `runWith` host with the homomorphic gate. -/
def evalValues (P : Parameters) {k : ℕ} (Cc : DAGCircuit k) (cts : Fin k → Ciphertext P) :
    List (Ciphertext P) :=
  runWith (homGate P) Cc.gates (List.ofFn cts)

/-- `evalValues P Cc cts` runs `homGate P` over the gates from the input ciphertexts. -/
theorem evalValues_eq (P : Parameters) {k : ℕ} (Cc : DAGCircuit k)
    (cts : Fin k → Ciphertext P) :
    evalValues P Cc cts = runWith (homGate P) Cc.gates (List.ofFn cts) := rfl

/-- **Homomorphic circuit evaluation** [GSW13, Section 3.3, "Circuits"; BV14, Definition 2.12
(leveled evaluation)]: the ciphertext at the circuit's output vertex. -/
def eval (P : Parameters) {k : ℕ} (Cc : DAGCircuit k) (cts : Fin k → Ciphertext P) :
    Ciphertext P :=
  (evalValues P Cc cts).getD Cc.output 0

/-- `eval P Cc cts` reads the output vertex of `evalValues`. -/
theorem eval_eq (P : Parameters) {k : ℕ} (Cc : DAGCircuit k) (cts : Fin k → Ciphertext P) :
    eval P Cc cts = (evalValues P Cc cts).getD Cc.output 0 := rfl

section Correctness

variable (P : Parameters) {t : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus}

/-- A homomorphic conjunction of `k` bit encryptions, each with noise at most `β`, encrypts
the conjunction of the bits with noise at most `((k−1)·N + 1)·β` (natural subtraction, so
the empty and one-element cases give `β`) [Pei16, Section 6.1.3; AP14, Corollary 3.6].

**Proof sketch.** Induction following `homAnd`'s three equations: `encrypts_gadget` with
`Encrypts.mono` for `[]`, the hypothesis for `[C]`, and `Encrypts.mul_bit` for `C :: C' :: Cs`,
whose bound `N·β + ((k−2)·N+1)·β` equals `((k−1)·N+1)·β`. The message is `List.all` by
`List.all_cons` and `Bool.toNat` of `&&` as a product. -/
theorem homAnd_encrypts {bs : List Bool} {Cs : List (Ciphertext P)} {β : ℕ}
    (hs : List.Forall₂ (fun b C => Encrypts P t (b.toNat : ℤ) β C) bs Cs) :
    Encrypts P t ((bs.all id).toNat : ℤ) (((Cs.length - 1) * P.columns + 1) * β)
      (homAnd P Cs) := by
  sorry

/-- **Per-gate noise.** A gate of fan-in at most two, whose argument vertices hold `β`-noisy
encryptions of their values, produces a `(N+1)·β`-noisy encryption of its value [GSW13,
Section 3.3, `NAND`: "the error is increased by a factor of at most `N + 1`"].

**Proof sketch.** Case on `g.kind` through `homGate_eq` and `DAGGate.eval_eq`. With
`bs = g.args.map (vals.getD · false)` and `Cs = g.args.map (cts.getD · 0)`,
`List.forall₂_map_left_iff` and `List.forall₂_map_right_iff` give the hypothesis of
`homAnd_encrypts`; `List.all_map` matches the messages; `length ≤ 2`
bounds `((k−1)·N+1)·β ≤ (N+1)·β`. For `¬`, subtract from `encrypts_gadget` (`Encrypts.sub`,
noise `0 + ·`). For `∨`, the complements `G − C` keep noise `β`, then one more subtraction;
`Bool` De Morgan identifies the message. -/
theorem homGate_encrypts (g : DAGGate) (hfan : g.args.length ≤ 2) (vals : List Bool)
    (cts : List (Ciphertext P)) (β : ℕ)
    (hargs : ∀ a ∈ g.args, Encrypts P t ((vals.getD a false).toNat : ℤ) β (cts.getD a 0)) :
    Encrypts P t ((g.eval vals).toNat : ℤ) ((P.columns + 1) * β) (homGate P g cts) := by
  sorry

/-- **Depth-indexed noise growth.** For a circuit of fan-in at most two, if every input
ciphertext encrypts its input bit with noise at most `β`, then every vertex `v` holds an
encryption of its value with noise at most `(N+1)^{depthAt v}·β`; in particular the output
ciphertext has noise at most `(N+1)^{depth}·β` [GSW13, Section 3.3, "the final ciphertext's
error will be bounded by `(N + 1)^L · B`"].

**Proof sketch.** Apply the shared `runWith_rel` to `DAGGate.eval` from `List.ofFn x` and
`homGate P` from `List.ofFn cts`, with
`R v b C := Encrypts P t b.toNat ((N+1)^{Cc.depthAt v}·β) C`. Inputs: `depthAt_input` gives
depth `0`. Gate `i`: `DAGCircuit.depthAt_gate` writes the gate's depth as
`gs[i].depth Cc.depths`; `DAGGate.getD_lt_depth` puts each argument at depth at most one less,
so the arguments are `(N+1)^{d−1}·β`-noisy (`Encrypts.mono`, `Nat.pow_le_pow_right`), and
`homGate_encrypts` multiplies by `N+1`. The output vertex is in range by `Cc.output_lt`;
`DAGCircuit.eval_eq`, `values_eq` and `depth_eq` identify the two sides. -/
theorem eval_encrypts {k : ℕ} (Cc : DAGCircuit k) (hfan : ∀ g ∈ Cc.gates, g.args.length ≤ 2)
    (x : Fin k → Bool) (cts : Fin k → Ciphertext P) (β : ℕ)
    (hin : ∀ i, Encrypts P t ((x i).toNat : ℤ) β (cts i)) :
    Encrypts P t ((Cc.eval x).toNat : ℤ) ((P.columns + 1) ^ Cc.depth * β) (eval P Cc cts) := by
  sorry

/-- **Leveled correctness of public-key GSW** [GSW13, Sections 3.3–3.4; Pei16, Section 6.1.3].
For every key-generation seed, every fan-in-two circuit of depth at most `L`, every input and
every encryption coin, decrypting the homomorphic evaluation of the input encryptions gives
the circuit's output, provided the noise law is `B`-bounded and
`2·(ℓ·((N+1)^L·(m·B))) < ⌊q/2⌋`.

**Proof sketch.** `encrypts_keygen_encrypt` gives input noise `m·B`; `eval_encrypts` gives
output noise `(N+1)^{depth}·(m·B) ≤ (N+1)^L·(m·B)` (`Encrypts.mono`); `decrypt_of_encrypts`. -/
theorem decrypt_keygen_eval (χ : LWE.Noise)
    (rg : Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      ((Fin P.lwe.dimension → ZMod P.lwe.modulus) × (Fin P.lwe.samples → χ.Coins)))
    {k : ℕ} (Cc : DAGCircuit k) (hfan : ∀ g ∈ Cc.gates, g.args.length ≤ 2)
    (x : Fin k → Bool) (R : Fin k → Matrix (Fin P.lwe.samples) (Fin P.columns) Bool)
    (B L : ℕ) (hχ : χ.Bounded B) (hdepth : Cc.depth ≤ L)
    (hsep : 2 * (P.width * ((P.columns + 1) ^ L * (P.lwe.samples * B))) <
      P.lwe.modulus / 2) :
    decrypt P (Regev.keygen P.lwe χ rg).2
        (eval P Cc fun i => encrypt P (Regev.keygen P.lwe χ rg).1 (x i) (R i)) =
      Cc.eval x := by
  sorry

end Correctness

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
```

## ===== TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Security.lean (Lean, at 48d796a8a68cd50897047f01825a8132dd19e8d8) =====

```lean
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Scheme
import TCSlib.Cryptography.Hashing.SIS.Columns
import TCSlib.Cryptography.LWE.Experiments
import Mathlib.Tactic.Simps.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Public-key GSW: IND-CPA security from decisional LWE (concrete hybrids)

## Main definitions

* `view`, `realView`, `uniformKeyView`: publish the key and one GSW encryption of a fixed bit.
* `reduction`: the DLWE test that encrypts under its challenge key with its own coins.
* `columnHashParameters`: the SIS-hash shape `(n+1) × m` of the augmented public key.

## Main results

* `real_uniformKey_advantage`: real-to-uniform-key advantage equals one DLWE advantage.
* `uniformKey_uniform_advantage_le`: under a uniform key the view is within
  `N · ε_LHL` of uniform, with `ε_LHL = Regev.extractionError`.
* `distAdv_encrypt_le`: two fixed bits' views differ by at most two DLWE advantages plus
  `2·N·ε_LHL` [GSW13, Section 3.2].
* `distAdv_encrypt_le_of_width`: with `(n+1)·w + 2κ ≤ m` the statistical term is at most
  `N · 2^{−κ}`.

## References

* [GSW13] C. Gentry, A. Sahai, B. Waters, CRYPTO 2013; author version dated 8 June 2013,
  Section 3.2 and Lemma 1 ("the joint distribution `(A, R·A)` is computationally
  indistinguishable from uniform"; "it suffices to take `m > 2n log q`").
* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated
  17 February 2016, Section 6.1.3 ("semantic security follows by a lossiness argument") and
  Section 5.2.1 (Regev's hybrids).
* [BV14] Z. Brakerski, V. Vaikuntanathan, ePrint 2013/541, Section 3.1, "Security".

**Scope.** Concrete, fixed-bit, single-ciphertext statements with function-level
distinguishers, exactly as the audited Regev PKE hybrids. The LWE instance has the GSW
key's `m` rows and one common uniform secret. The asymptotic primitive bridge (`NUPPT`
reductions, `BitPublicKeyScheme.SingleBitSecure`) is a separate unit after the Regev PKE
bridge; multi-ciphertext security then follows from the existing shared-key hybrid
`distAdv_multi_le_sum` (Encryption/PublicKey/EnsembleSecurity.lean:134).
-/

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

open Encryption.PublicKey

/-- The view `(pk, Enc_pk(μ; R))` [GSW13, Section 3.2, passive-view formulation]. -/
@[simps! (config := { isSimp := false }) fst snd]
def view (P : Parameters) (μ : Bool)
    (pk : Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus))
    (R : Matrix (Fin P.lwe.samples) (Fin P.columns) Bool) :
    (Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus)) × Ciphertext P :=
  (pk, encrypt P pk μ R)

/-- The view is the key paired with its GSW encryption. -/
theorem view_eq (P : Parameters) (μ : Bool)
    (pk : Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus))
    (R : Matrix (Fin P.lwe.samples) (Fin P.columns) Bool) :
    view P μ pk R = (pk, encrypt P pk μ R) := rfl

/-- The real view: an actual LWE public key and independent uniform binary `R` [GSW13,
Section 3.1]. -/
@[simps! (config := { isSimp := false }) fst snd]
def realView (P : Parameters) (χ : LWE.Noise) (μ : Bool)
    (r : (Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      ((Fin P.lwe.dimension → ZMod P.lwe.modulus) × (Fin P.lwe.samples → χ.Coins))) ×
        Matrix (Fin P.lwe.samples) (Fin P.columns) Bool) :
    (Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus)) × Ciphertext P :=
  view P μ (LWE.sample P.lwe χ r.1) r.2

/-- The real sampler applies `view` to the existing common-secret LWE sample. -/
theorem realView_eq (P : Parameters) (χ : LWE.Noise) (μ : Bool)
    (r : (Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      ((Fin P.lwe.dimension → ZMod P.lwe.modulus) × (Fin P.lwe.samples → χ.Coins))) ×
        Matrix (Fin P.lwe.samples) (Fin P.columns) Bool) :
    realView P χ μ r = view P μ (LWE.sample P.lwe χ r.1) r.2 := rfl

/-- The first hybrid encrypts under an independent uniform key [GSW13, Section 3.2;
Pei16, Section 6.1.3, "a uniformly random (malformed) public key"]. -/
@[simps! (config := { isSimp := false }) fst snd]
def uniformKeyView (P : Parameters) (μ : Bool)
    (r : (Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus)) ×
        Matrix (Fin P.lwe.samples) (Fin P.columns) Bool) :
    (Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus)) × Ciphertext P :=
  view P μ r.1 r.2

/-- The uniform-key hybrid applies `view` to its uniform key seed. -/
theorem uniformKeyView_eq (P : Parameters) (μ : Bool)
    (r : (Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus)) ×
        Matrix (Fin P.lwe.samples) (Fin P.columns) Bool) :
    uniformKeyView P μ r = view P μ r.1 r.2 := rfl

/-- The DLWE reduction: encrypt the fixed bit under the challenge key with independent
binary coins, then run the view distinguisher with its own coins [GSW13, Section 3.2,
Lemma 1, computational half]. -/
def reduction {ρ : Type*} (P : Parameters) (μ : Bool)
    (D : ((Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus)) × Ciphertext P) → ρ → Bool)
    (pk : Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus))
    (r : Matrix (Fin P.lwe.samples) (Fin P.columns) Bool × ρ) : Bool :=
  D (view P μ pk r.1) r.2

/-- The reduction calls the distinguisher on exactly one simulated view. -/
theorem reduction_eq {ρ : Type*} (P : Parameters) (μ : Bool)
    (D : ((Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus)) × Ciphertext P) → ρ → Bool)
    (pk : Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus))
    (r : Matrix (Fin P.lwe.samples) (Fin P.columns) Bool × ρ) :
    reduction P μ D pk r = D (view P μ pk r.1) r.2 := rfl

/-- The SIS-hash shape of the augmented public key: `n+1` rows, `m` binary columns, modulus
`q`. The norm budget is unused by the unconditional extraction argument. Technical glue.

**Disclosure.** Field-for-field equal to `Regev.hashParameters`; a GSW-local copy because
GSW's types index matrices by `Fin (n+1)`, and reading `Regev.hashParameters` at the type level
would unfold another file's definition (Rule 10). Alternative: Regev publishes a domain
equivalence. Either needs a maintainer decision. -/
def columnHashParameters (P : Parameters) : TCSlib.Cryptography.SIS.Parameters where
  dimension := P.lwe.dimension + 1
  columns := P.lwe.samples
  modulus := P.lwe.modulus
  sqNormBound := P.lwe.samples
  modulus_ge_two := P.lwe.modulus_ge_two

attribute [simps (config := { isSimp := false }) dimension columns modulus sqNormBound]
  columnHashParameters

/-- **Computational hybrid.** The real view and the uniform-key view are distinguished with
exactly the DLWE advantage of the encryption reduction [GSW13, Section 3.2, Lemma 1; Pei16,
Section 6.1.3].

**Proof sketch.** As `Regev.real_uniformKey_advantage`: reassociate the independent key,
coin-matrix and distinguisher seeds (`uprob_comp_equiv` with `Equiv.prodAssoc`) on both
sides, then read `LWE.decisionAdvantage_eq` and `distAdv_def`. -/
theorem real_uniformKey_advantage {ρ : Type*} [Fintype ρ] [Nonempty ρ]
    (P : Parameters) (χ : LWE.Noise) (μ : Bool)
    (D : ((Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus)) × Ciphertext P) → ρ → Bool) :
    distAdv (realView P χ μ) (uniformKeyView P μ) D =
      LWE.decisionAdvantage P.lwe χ (reduction P μ D) := by
  sorry

/-- **Statistical hybrid.** Under a uniform key the view is within `N · ε_LHL` of a fully
uniform key-and-ciphertext pair, where `ε_LHL = ½·√(q^{n+1}/2^m)` is the existing
`Regev.extractionError` [GSW13, Section 3.2, "`R · A` is statistically uniform by the
leftover hash lemma"; Pei16, Section 6.1.3].

**Proof sketch.** Relabel the key by the bijection `Regev.augmented_bijective`. The ciphertext
is `hashColumns (columnHashParameters P) N Ā R + μG` (`encrypt_eq`, `hashColumns_eq_mul`);
translation by `μG` is a bijection of the ciphertext space, so after relabelling both samplers
(`acceptProb_comp_equiv`) the gap is that of `(Ā, ĀR)` versus `(Ā, U)`. Apply
`distAdv_hashColumns_uniform_le` and rewrite its bound with the `columnHashParameters` readers
and `Regev.extractionError_eq`. -/
theorem uniformKey_uniform_advantage_le {ρ : Type*} [Fintype ρ] [Nonempty ρ]
    (P : Parameters) (μ : Bool)
    (D : ((Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus)) × Ciphertext P) → ρ → Bool) :
    distAdv (uniformKeyView P μ)
      (id : ((Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
        (Fin P.lwe.samples → ZMod P.lwe.modulus)) × Ciphertext P) → _) D ≤
      P.columns * Regev.extractionError P.lwe := by
  sorry

/-- **Concrete IND-CPA bound for public-key GSW** [GSW13, Section 3.2 and Lemma 1; Pei16,
Section 6.1.3]. The views of two fixed bits differ by at most two DLWE advantages plus
`2·N·ε_LHL`.

**Proof sketch.** Insert both uniform-key views and the common uniform view; the triangle
inequality gives the two exact DLWE terms (`real_uniformKey_advantage`) and two statistical
terms (`uniformKey_uniform_advantage_le`), as in `Regev.distAdv_encrypt_le`. -/
theorem distAdv_encrypt_le {ρ : Type*} [Fintype ρ] [Nonempty ρ]
    (P : Parameters) (χ : LWE.Noise) (μ₀ μ₁ : Bool)
    (D : ((Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus)) × Ciphertext P) → ρ → Bool) :
    distAdv (realView P χ μ₀) (realView P χ μ₁) D ≤
      LWE.decisionAdvantage P.lwe χ (reduction P μ₀ D) +
      LWE.decisionAdvantage P.lwe χ (reduction P μ₁ D) +
      2 * (P.columns * Regev.extractionError P.lwe) := by
  sorry

/-- With residue width `w` (`q ≤ 2^w`) and `m ≥ (n+1)·w + 2κ` rows, the statistical term is at
most `N · 2^{−κ}` [GSW13, Section 3.2, "it suffices to take `m > 2n log q`", explicit
repository budget].

**Proof sketch.** `distAdv_encrypt_le` and `Regev.two_extractionError_le`, multiplying the
latter by `N ≥ 0`. -/
theorem distAdv_encrypt_le_of_width {ρ : Type*} [Fintype ρ] [Nonempty ρ]
    (P : Parameters) (χ : LWE.Noise) (μ₀ μ₁ : Bool) (w κ : ℕ)
    (hq : P.lwe.modulus ≤ 2 ^ w)
    (hm : (P.lwe.dimension + 1) * w + 2 * κ ≤ P.lwe.samples)
    (D : ((Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus)) × Ciphertext P) → ρ → Bool) :
    distAdv (realView P χ μ₀) (realView P χ μ₁) D ≤
      LWE.decisionAdvantage P.lwe χ (reduction P μ₀ D) +
      LWE.decisionAdvantage P.lwe χ (reduction P μ₁ D) +
      P.columns * ((2 : ℝ)⁻¹) ^ κ := by
  sorry

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
```

## ===== TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Symmetric.lean (Lean, at 48d796a8a68cd50897047f01825a8132dd19e8d8) =====

```lean
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Scheme
import TCSlib.Cryptography.LWE.Experiments

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Secret-key GSW: batched encryption under one secret, and its DLWE security

## Main definitions

* `rowEquiv`: split `m = k·N` LWE rows into `k` blocks of `N`.
* `symEncrypt`: `k` ciphertexts `Cᵢ = Āᵢ + μᵢ G` from one LWE challenge, block `i` of the
  augmented sample matrix supplying `Āᵢ`; one common secret for all of them.

## Main results

* `encrypts_symEncrypt`: every secret-key ciphertext has noise at most `B` (not `m·B`).
* `distAdv_symEncrypt_le`: two message vectors' batches differ by at most two DLWE
  advantages with `k·N` rows; no leftover hashing.

## References

* [AP14] J. Alperin-Sheriff, C. Peikert, ePrint 2014/094 version dated 13 June 2014,
  Section 3.2 (`GSW.Enc`: "a fresh ciphertext is just `μG` plus a matrix of `nℓ` independent
  LWE samples").
* [BV14] Z. Brakerski, V. Vaikuntanathan, ePrint 2013/541, Section 3.1 (`NCCrypt.SecEnc`:
  "a secret-key encryption of `μ` is somewhat less noisy than a public-key encryption").
* [Wu24] D. Wu, CS395T lecture notes, Spring 2024, Definition 20.5 (the batched direct
  pattern of the existing symmetric Regev scheme).

**Deviations.** The secret is uniform ([AP14] draws it from the error law, which needs a
separate normal-form assumption excluded by plan decision D1). The batch of `k` ciphertexts
uses one DLWE instance with exactly `k·N` rows, so multi-message security is part of the
statement rather than a further hybrid. Row reindexing goes through the published equivalence
`rowEquiv`, the domain-equivalence pattern used elsewhere for type-valued parameters.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

open Encryption.PublicKey

/-- Split `m = k·N` LWE rows into `k` blocks of `N` consecutive rows. Technical glue. -/
def rowEquiv (P : Parameters) {k : ℕ} (hN : P.lwe.samples = k * P.columns) :
    Fin k × Fin P.columns ≃ Fin P.lwe.samples :=
  finProdFinEquiv.trans (finCongr hN.symm)

/-- `rowEquiv P hN` is `finProdFinEquiv` followed by the cast along `hN`. -/
theorem rowEquiv_eq (P : Parameters) {k : ℕ} (hN : P.lwe.samples = k * P.columns) :
    rowEquiv P hN = finProdFinEquiv.trans (finCongr hN.symm) := rfl

/-- Batched secret-key GSW encryption [AP14, Section 3.2, `GSW.Enc`; BV14, Section 3.1,
`NCCrypt.SecEnc`, gadget form]: from an LWE challenge `(A, b)` with `k·N` rows, ciphertext `i`
is the block-`i` columns of the augmented matrix plus `μᵢ G`. -/
def symEncrypt (P : Parameters) {k : ℕ} (hN : P.lwe.samples = k * P.columns)
    (c : Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus))
    (μ : Fin k → Bool) : Fin k → Ciphertext P :=
  fun i => (Regev.augmented P.lwe c).submatrix id (fun j => rowEquiv P hN (i, j)) +
    ((μ i).toNat : ZMod P.lwe.modulus) • gadget P

/-- Ciphertext `i` is the reindexed block of the augmented challenge plus `μᵢ G`. -/
theorem symEncrypt_apply (P : Parameters) {k : ℕ} (hN : P.lwe.samples = k * P.columns)
    (c : Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus))
    (μ : Fin k → Bool) (i : Fin k) :
    symEncrypt P hN c μ i = (Regev.augmented P.lwe c).submatrix id (fun j => rowEquiv P hN (i, j)) +
      ((μ i).toNat : ZMod P.lwe.modulus) • gadget P := rfl

/-- **Secret-key noise.** On a real LWE challenge with row errors bounded by `B`, every
secret-key ciphertext encrypts its bit under `t = (−s,1)` with noise at most `B` [AP14,
Section 3.2, "Notice that `sᵗC = eᵗ + μ·sᵗG`"; BV14, Section 3.1].

**Proof sketch.** `Matrix.vecMul_add`, `Matrix.vecMul_smul`; the block of `tᵗ Ā` is
`tᵗ Ā` read at the reindexed columns (`Matrix.vecMul` of a `submatrix`), equal to
`e ∘ rowEquiv` by `vecMul_secretVector_augmented`. -/
theorem encrypts_symEncrypt (P : Parameters) {k : ℕ} (hN : P.lwe.samples = k * P.columns)
    (A : Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus))
    (s : Fin P.lwe.dimension → ZMod P.lwe.modulus) (e : Fin P.lwe.samples → ℤ) (B : ℕ)
    (he : ∀ i, (e i).natAbs ≤ B) (μ : Fin k → Bool) (i : Fin k) :
    Encrypts P (secretVector P s) ((μ i).toNat : ℤ) B
      (symEncrypt P hN (A, LWE.noisyValues P.lwe A s e) μ i) := by
  sorry

/-- **Concrete IND-CPA bound for batched secret-key GSW** [AP14, Section 3.2, "The IND-CPA
security of the scheme follows immediately from the assumed hardness of LWE"; Wu24,
Lecture 21, the two-hybrid pattern]. For two message vectors, the distributions of the `k`
ciphertexts under one uniform secret differ by at most two DLWE advantages with `k·N` rows.

**Proof sketch.** As `Encryption.Symmetric.Regev.distAdv_encrypt_le`: each real batch is
`symEncrypt` of the actual LWE sample; on the uniform side, `(A,b) ↦ symEncrypt P hN (A,b) μ`
is a bijection onto `Fin k → Ciphertext P` (`Regev.augmented_bijective`, the column
reindexing by `rowEquiv`, and translation by `μG`; both sides have `q^{(n+1)·k·N}` elements),
so both ideal acceptance probabilities equal that of a uniform batch.
Insert it between the two real experiments and use the triangle inequality. -/
theorem distAdv_symEncrypt_le {ρ : Type*} [Fintype ρ] [Nonempty ρ]
    (P : Parameters) {k : ℕ} (hN : P.lwe.samples = k * P.columns) (χ : LWE.Noise)
    (μ₀ μ₁ : Fin k → Bool) (D : (Fin k → Ciphertext P) → ρ → Bool) :
    distAdv (fun r => symEncrypt P hN (LWE.sample P.lwe χ r) μ₀)
        (fun r => symEncrypt P hN (LWE.sample P.lwe χ r) μ₁) D ≤
      LWE.decisionAdvantage P.lwe χ (fun c r => D (symEncrypt P hN c μ₀) r) +
      LWE.decisionAdvantage P.lwe χ (fun c r => D (symEncrypt P hN c μ₁) r) := by
  sorry

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
```

## ===== TCSlib/Cryptography/Hashing/SIS/Columns.lean (Lean, at 48d796a8a68cd50897047f01825a8132dd19e8d8) =====

```lean
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Hashing.SIS.Universality
import TCSlib.Cryptography.Foundations.Probability

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Leftover hashing of many independent columns under one public matrix

## Main definitions

* `hashColumns`: hash `N` independent binary columns with the same matrix, `A ↦ A R`.

## Main results

* `distAdv_hashColumns_uniform_le`: `(A, A R)` is within `N` times the single-column
  leftover-hash error of `(A, U)` with `U` uniform.

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated
  17 February 2016, Section 5.2.1 (leftover hashing in Regev encryption) and Section 6.1.3
  ("`[Ā | ĀR]` is very close to uniformly distributed").
* [GSW13] C. Gentry, A. Sahai, B. Waters, CRYPTO 2013; author version dated 8 June 2013,
  Section 3.2, Lemma 1 (`(A, R·A)` close to uniform).
* [Vad12] S. Vadhan, *Pseudorandomness*, 2012, Theorem 6.18.

The bound is a column-by-column hybrid over the existing single-column
`distAdv_hash_uniform_le`. It is not a matrix leftover-hash lemma: the family `R ↦ A R` is not
universal on whole matrices, and no such claim is made. No SIS hardness is used.
-/

namespace TCSlib.Cryptography.Hashing.SIS

open TCSlib.Cryptography.SIS (Parameters)

/-- Hash `N` binary columns with one matrix: column `j` of `hashColumns P N A R` is
`hash P A (R · j)`, so `hashColumns P N A R = A R` modulo `q` [Pei16, Section 6.1.3, `ĀR`]. -/
def hashColumns (P : Parameters) (N : ℕ)
    (A : Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus))
    (R : Matrix (Fin P.columns) (Fin N) Bool) :
    Matrix (Fin P.dimension) (Fin N) (ZMod P.modulus) :=
  fun i j => hash P A (fun c => R c j) i

/-- Entry `(i,j)` of `hashColumns P N A R` is coordinate `i` of the hash of column `j`. -/
theorem hashColumns_apply (P : Parameters) (N : ℕ)
    (A : Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus))
    (R : Matrix (Fin P.columns) (Fin N) Bool) (i : Fin P.dimension) (j : Fin N) :
    hashColumns P N A R i j = hash P A (fun c => R c j) i := rfl

/-- `hashColumns` is matrix multiplication by the `{0,1}` lift of `R`.

**Proof sketch.** Entrywise: `hash_eq` and the `mulVec`/`mul` entry formulas are the same sum. -/
theorem hashColumns_eq_mul (P : Parameters) (N : ℕ)
    (A : Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus))
    (R : Matrix (Fin P.columns) (Fin N) Bool) :
    hashColumns P N A R = A * Matrix.of fun c j => ((R c j).toNat : ZMod P.modulus) := by
  sorry

/-- **Column hybrid for leftover hashing** [GSW13, Section 3.2, Lemma 1, statistical half;
Pei16, Section 6.1.3]: any independently randomized test distinguishes `(A, A R)` from a
uniform `(A, U)`, for uniform `A` and uniform binary `R` with `N` columns, with advantage at
most `N` times the single-column error `½·√(q^{dimension}/2^{columns})`.

**Proof sketch.** Hybrid `H_j`: the first `j` columns of the second component are uniform and
the rest are hashes of independent binary columns; `H_0` is the real sampler and `H_N` the
ideal one (after relabelling seeds by `uprob_comp_equiv`). `abs_sub_le_sum_hybrids` bounds the
end-to-end gap by the sum of neighbouring gaps. The `j`-th gap equals the advantage, between
`(A, hash A r)` and `(A, u)`, of the test that plants its challenge column at `j`, samples the
other columns itself with coins carried in its own randomness, and runs `D`; this is
`distAdv_hash_uniform_le`. The reduction's coins are a product of finite nonempty types. -/
theorem distAdv_hashColumns_uniform_le {ρ : Type*} [Fintype ρ] [Nonempty ρ]
    (P : Parameters) (N : ℕ)
    (D : (Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus) ×
      Matrix (Fin P.dimension) (Fin N) (ZMod P.modulus)) → ρ → Bool) :
    distAdv (fun r : Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus) ×
        Matrix (Fin P.columns) (Fin N) Bool => (r.1, hashColumns P N r.1 r.2))
      (id : (Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus) ×
        Matrix (Fin P.dimension) (Fin N) (ZMod P.modulus)) → _) D ≤
      N * ((1 / 2) * Real.sqrt ((P.modulus : ℝ) ^ P.dimension / (2 : ℝ) ^ P.columns)) := by
  sorry

end TCSlib.Cryptography.Hashing.SIS
```

## ===== TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW.lean (Lean, at 48d796a8a68cd50897047f01825a8132dd19e8d8) =====

```lean
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Gadget
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Noise
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Scheme
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Eval
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Security
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Symmetric

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Leveled GSW homomorphic encryption from LWE

## Contents

* `Gadget`: parameters, the gadget `G = I ⊗ gᵗ` and deterministic binary decomposition `G⁻¹`.
* `Noise`: the key-agnostic invariant `tᵗC = x·tᵗG + e`, asymmetric multiplication, NAND,
  sums and right-associative product chains.
* `Scheme`: public-key GSW on the existing Regev/LWE key, fresh noise and decryption.
* `Eval`: homomorphic evaluation of `BoolCircuit.DAGCircuit` and leveled correctness.
* `Security`: concrete IND-CPA hybrids from DLWE and column leftover hashing.
* `Symmetric`: batched secret-key GSW and its direct DLWE bound (optional unit).

## References

* [GSW13] C. Gentry, A. Sahai, B. Waters, CRYPTO 2013; author version dated 8 June 2013.
* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, 17 February 2016, Section 6.1.3.
* [AP14] J. Alperin-Sheriff, C. Peikert, ePrint 2014/094, version dated 13 June 2014, Section 3.
-/
```

## ===== TCSlib/Cryptography/AdvancedEncryption/Homomorphic.lean (Lean, at 48d796a8a68cd50897047f01825a8132dd19e8d8) =====

```lean
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Homomorphic encryption

## Contents

* `GSW`: leveled Gentry–Sahai–Waters encryption from LWE.

## References

* [GSW13] C. Gentry, A. Sahai, B. Waters, CRYPTO 2013; author version dated 8 June 2013.
-/
```

## ===== TCSlib/Cryptography/AdvancedEncryption.lean (Lean, at 48d796a8a68cd50897047f01825a8132dd19e8d8) =====

```lean
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Advanced encryption primitives

Encryption primitives beyond private-key and public-key encryption.

## Contents

* `Homomorphic`: homomorphic encryption; leveled Gentry–Sahai–Waters encryption from LWE.

## References

* [GSW13] C. Gentry, A. Sahai, B. Waters, *Homomorphic Encryption from Learning with Errors:
  Conceptually-Simpler, Asymptotically-Faster, Attribute-Based*, CRYPTO 2013; author version
  dated 8 June 2013.
-/
```
