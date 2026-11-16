# Gate 43 · GSW fills: gsw-core (#339) and gsw-security (#338), proof audit (lattice campaign, phase 5)

Round 1. The auditor is Codex, under the standing ruling of 2026-11-11 (Codex for audits and reviews). Both PRs are
audited together: they are the two fill units of one fill wave, issued on one base, and they close phase 5.

**Gate number.** Gate 42 is reserved for sc-yao (Pass–shelat). The phase-6 plan
(`briefs/lattice-gsw/phase6/plan-section.md`) names its two statement gates 42 and 43 provisionally; they will be
renumbered later. This gate, 43, is the phase-5 fill gate.

| PR | Unit | Head (branch) | Head tree | Base (merge base with the tip) | Files | Targets |
|---|---|---|---|---|---|---|
| [#339](https://github.com/Shilun-Allan-Li/tcslib/pull/339) | `gsw-core` (F1 Gadget, F2 Noise, F3 Scheme, F7 Symmetric, F4 Eval) | `839f36cca9b4af0570c014f03f19858d0a03cbfb` (`land/lattice-gsw-core`) | `2a209146` | `347665bd741d367c4d2057f7d61866ff1d91c356` | 5, +542/−89 | 29 |
| [#338](https://github.com/Shilun-Allan-Li/tcslib/pull/338) | `gsw-security` (F5 Columns, F6 Security) | `d45d3682089cb6fd04f4d075f48a464fefaa143c` (`land/lattice-gsw-security`) | `696be51f` | `15d8f01a42f23aa17d8fd305c7e5edde9b602da4` | 2, +219/−26 | 6 |

- **Target and bases.** Both PRs target the records branch `cryptography/pass-shelat-ch2-4`, whose tip is now
  `c999a83c0ee57290d6a5c4bdcc7b17404dff81db`. Each was landed on the tip of its day; the tip has since changed only
  in records (0 Lean or lake paths, `pack-checks/series.txt`). The REST base SHAs equal the merge bases.
- **Issue base.** Both fills were issued on `486f44f8414c20a2d21e452c44de8b8c8d8513a0`, the Gate 41-closed head of
  #333, which contains #332. Both have merged; the issue base is an ancestor of both PR bases, and the 7 owned files
  are byte-identical at the issue base and at the PR bases.
- **Diffs.** `pr-339.diff.txt` is `git diff 347665bd..839f36cc` (55218 bytes, SHA-256 `e201ea97…`). `pr-338.diff.txt`
  is `git diff 15d8f01a..d45d3682` (21633 bytes, `79603393…`). Each equals byte for byte both the three-dot diff from
  the tip (GitHub's view) and the delivered series' diff from the issue base (`486f44f8..d4ebb0be`,
  `486f44f8..a9f97edd`).
- **Commits: the workers' commits, cherry-picked and signed.** `git range-diff` is `=` for every pair, and the
  patch-ids, authors, author dates and subjects are equal (`series.txt`):

  | PR | Landed | Delivered | Content |
  |---|---|---|---|
  | #339 | `51a415db` | `243a44cd` | F1, F2 |
  | #339 | `fe1b1f77` | `a1bc6aac` | F4 (at that point `decrypt_keygen_eval` cited the then-sorried F3) |
  | #339 | `839f36cc` | `d4ebb0be` | F3, F7 |
  | #338 | `420cbf72` | `58a97f52` | F5 |
  | #338 | `d45d3682` | `a9f97edd` | F6 |

  - Each landed commit carries one SSH signature. The pack verified it (ed25519, namespace `git`) with the key
    embedded in the signature; it is the key that signs the records tip, `SHA256:32dP45eS…`. The control, one byte
    added to the signed payload, fails to verify.
  - The delivered commits are unsigned (`COMMITS.tsv`: `none`). `git am` at the issue base reproduces their hashes
    (both reviews).
- **Deliveries** (exchange `exchange/pass-shelat-ch5-8`). The worker was Claude for both.
  - `gsw-core`: a lead with two sub-agents. A proved F1 and F2, B proved F3 and F7 with the three private helpers,
    and the lead proved F4 and integrated. Final `9e52a5019258c51d67b1f28d3675c66cf787209b`, checkpoint
    `5b72e346bd5484fb059cbaadd836de88f4adf0a2`.
  - `gsw-security`: a single agent. Final `5857e850e7f7daf264d2860caf27341e3052f8c5`, checkpoint
    `b08456186ebfa194f8445f1f78ba7c0743e4991b`.
  - Every delivery commit touches only `inbox/fills/<unit>/`, and none follows the finals there.
  - Each PR head's files equal the delivery's `src/` and the delivered head.
  - Each delivered patch has the patch-id of its landed commit (`delivery.txt`).
- **Scope:** a **proof audit** of the 35 admitted targets of phase 5 (plan §G7: F1 5, F2 12, F3 6, F7 2, F4 4, F5 2,
  F6 4). Gate 41 accepted every one as true with the hypotheses it displays (closed by disposition; G41-01 became
  DW-7). Their statements and statement prose are frozen.
- **Briefs:** `fills/gsw-core/issued-r1/brief.md` (SHA-256 `c1a603cc…`) and `fills/gsw-security/issued-r1/brief.md`
  (`5ce6f12e…`), both in the bundle and in `verification.zip`. They set out:
  - the routes Gate 41 validated;
  - the frozen-statement rule, scope (owned files only; imports: Mathlib and `Pseudorandom/Indistinguishability`) and
    the helper-module rule;
  - Rule 10 with the type-level list of plan §G8, and the notation exemptions;
  - duplication: "undisclosed copies of public lemmas are majors", with an `## Overlap and reuse` disclosure;
  - the docstring and sketch rules, the sources rule (DW-6, DW-7), the checkpoints, and evidence completeness.

Lean paths below are under `TCSlib/Cryptography/`. `GSW/` stands for `AdvancedEncryption/Homomorphic/GSW/`.

## What changed

| File | PR | Lines (base → head) | Targets | Sketches rewritten / kept | New |
|---|---|---|---|---|---|
| `GSW/Gadget.lean` | #339 | 204 → 236 | 5 | 4 / 1 | — |
| `GSW/Noise.lean` | #339 | 235 → 321 | 12 | 9 / 3 | — |
| `GSW/Scheme.lean` | #339 | 215 → 364 | 6 | 5 / 1 | private `halfVector_eq_zero_of_ne_last` (:201), `decrypt_eq_decode_errorSum` (:213) |
| `GSW/Symmetric.lean` | #339 | 111 → 185 | 2 | 2 / 0 | private `exists_equiv_symEncrypt` (:110) |
| `GSW/Eval.lean` | #339 | 209 → 321 | 4 | 1 / 3 | — |
| `Hashing/SIS/Columns.lean` | #338 | 89 → 194 | 2 | 2 / 0 | `import TCSlib.Cryptography.Pseudorandom.Indistinguishability` |
| `GSW/Security.lean` | #338 | 217 → 305 | 4 | 4 / 0 | the same import |

- Every line is at most 100 characters. There is no micro sign, tab, trailing space, `@[simp]` or new attribute
  (`docs.txt`).
- There is no new public declaration and no helper module. The facades, `DAGCircuit.lean`, and the LWE, Regev, Lossy
  and SIS files are untouched. Neither fill made a scope request.
- **Statements** (`frozen.txt`, an independent re-check from git objects at the PR bases and heads):
  - every base item of the 7 files reappears in order: 0 DIFF, 0 REMOVED, 0 ORDER. That covers the 35 target headers,
    their prose up to `**Proof sketch.**`, every definition, reader, structure, abbrev and `attribute`, and every
    `variable`, `open`, `set_option` and module docstring;
  - the only additions are the 3 private theorems and the 2 imports;
  - the controls give the expected counts: one header character 1, one prose character 1, one definition character 1,
    a deleted reader 1 removal, a sketch-only edit 0, and identity 0;
  - the reviews' own tools (`frozen.py`, `frozen_check.py`), re-run unmodified on the same blobs, agree.
- **Admissions** (`sorries.txt`): each target's base body is exactly `sorry`, and each head body is sorry-free. The
  `sorry` tokens in the 7 files go from 35 to 0.

**The proofs.** The routes as delivered, in brief (the REPORTs' `## Routes` / `## The delivered proofs`):
- **F1.** `digits_decomposeVec` and the two `G·G⁻¹` identities go through `Lossy.gadget_mulVec`, `digits_val` and
  `digit_val`. The zero-block lemma uses termwise vanishing of a nonnegative positional sum. `errorSum_decomposeVec_le`
  splits through `finProdFinEquiv` and bounds the surviving block by `LWE.binaryErrorSum_bound` with `m := ℓ`.
- **F2.**
  - `Encrypts.mul` takes the exact witness `j ↦ ∑ᵢ e₁ i·X i j + x₁·e₂ j` with `X = lift (G⁻¹ C₂)`, and bounds it by
    `Int.natAbs_add_le`, `LWE.binaryErrorSum_bound` (`N·β₁`) and `Int.natAbs_mul` (`|x₁|·β₂`).
  - `mul_bit` weakens `|b|` to 1. `mul_le` and `nand` follow, and `encrypts_chain` is `Forall₂` induction with
    `mul_bit`, the fresh bit on the left.
- **F3.**
  - The private glue `decrypt_eq_decode_errorSum` puts the residual in the form `codepoint b + ⟨e, x⟩`.
  - `decrypt_of_encrypts` combines it with `errorSum_decomposeVec_le` (`j₀ = last`) and
    `decode_codepoint_add (B := ℓ·β)`.
  - `decrypt_of_encrypts_dyadic` shows that `G⁻¹(w)` is the indicator of `(last, ℓ−1)`, by `digits_injective`, so the
    error is the single entry `e i₀`.
- **F7.**
  - The private `exists_equiv_symEncrypt` composes three maps: augmentation (`Equiv.ofBijective`,
    `Regev.augmented_bijective`), a hand-built column reindexing through `rowEquiv`, and `Equiv.addRight` by the
    message gadgets.
  - `distAdv_symEncrypt_le` inserts the uniform batch through `acceptProb_comp_equiv` and applies `abs_sub_le`.
- **F4.**
  - `homAnd_encrypts` follows `homAnd`'s three equations, and `homGate_encrypts` cases on the kind (De Morgan for `∨`).
  - `eval_encrypts` is one application of `runWith_rel` with the vertex-indexed relation
    `R v b C := Encrypts P t b.toNat ((N+1)^{depthAt v}·β) C`.
  - `decrypt_keygen_eval` chains `encrypts_keygen_encrypt` (`m·B`), `eval_encrypts`, `Encrypts.mono` with
    `Nat.pow_le_pow_right` and `decrypt_of_encrypts`.
- **F5.**
  - `hashColumns_eq_mul` is entrywise.
  - `distAdv_hashColumns_uniform_le` (98 lines) uses hybrids `H_k`, whose first `k` columns are uniform and whose
    others are hashes under the same `A`.
  - The `k`-th test plants its challenge at column `k` and carries the other columns' coins beside `D`'s.
  - `hleft` and `hright` show by `acceptProb_bind`, `acceptProb_comp_equiv` and `acceptProb_update` that the test
    accepts `(A, hash A r)` as `D` accepts `H_k`, and a uniform `(A, y)` as `D` accepts `H_{k+1}`.
  - `hzero` and `hfull` identify the end hybrids (`acceptProb_fst`). `abs_sub_le_sum_hybrids` and the strong
    single-column LHL `distAdv_hash_uniform_le` finish.
- **F6.**
  - `real_uniformKey_advantage` is an exact equality by `acceptProb_bind` and the `view` readers.
  - `uniformKey_uniform_advantage_le` relabels the key by `keyEquiv` (the augmentation bijection) and the ciphertext by
    `Equiv.addRight (μG)`. It then applies F5 to the test that undoes both, and reads the bound through the
    `columnHashParameters` readers and `Regev.extractionError_eq`.
  - `distAdv_encrypt_le` is the four-hybrid chain (real μ₀ → uniform-key μ₀ → uniform → uniform-key μ₁ → real μ₁):
    three `abs_sub_le` and `linarith`.
  - `distAdv_encrypt_le_of_width` multiplies `Regev.two_extractionError_le` by `N`.

## Rulings and records in force

1. **Phase 5 and its rulings:** Q1–Q16 (A), with Q9 changed (the paths above), and QS1–QS2. The ones relevant here:
   - Q3 regime-agnostic concrete statements; Q5 worst-case, every-coin correctness;
   - Q6 decryption through the `C·G⁻¹(⌊q/2⌋·e_{n+1})` column with `Regev.decrypt` (the factor `ℓ` is disclosed);
   - Q8 concrete hybrids now, the `NUPPT` bridge later;
   - Q10 `Lossy.gadget` reused in place;
   - Q11 the GSW-local `columnHashParameters`, disclosed.
2. **Gate 41 (closed by disposition):** all 35 statements accepted, with the noise and security calculations in its
   findings, which are in the bundle. G41-02 and G41-03 were fixed in LE-gate41, a docstring-only edit at the issue
   base. **DW-7** (the GSW13, AP14 and BV14 transcriptions and the Pei16 extension) is **done**, at records `6078f369`.
3. **Workers (Seyoon, 2026-11-16):** Claude for both fills; `gsw-core` with up to two sub-agents on disjoint files.
4. **Rule 10** (policy §1, R-04-5):
   - Seals are collected from the elaborated terms plus matchers, with paired controls, and **coe-A is canonical**.
   - Notation is never sealed: reducible abbreviations (here `Parameters.columns`, `Ciphertext`, `Noise.Coins`),
     `PolyExpr.eval` and projection coercions (Seyoon, 2026-11-14).
   - Core and Mathlib definitions may reduce in `rfl`, `decide`, `show` or `change` steps, but are never `simp`/`rw`
     selectors.
   - Each owned file may read its own definitions. The owned files are foreign to each other.
5. **Duplication:** recent gates graded undisclosed duplicates of public lemmas as majors (G23-01, G24-01, G32-01,
   G39-01). Policy §1 requires duplicated proved material to be human-approved.
6. **Proof sketches:** a fill rewrites each target's `**Proof sketch.**` paragraph to describe the delivered proof.
   The statement prose stays byte-identical.

## Questions for the audit

**1. Soundness of the 35 proofs, against the routes Gate 41 validated.** Mark each finding by PR. In particular:
- **`Encrypts.mul` (#339, `GSW/Noise.lean:216`).**
  - Does the proof establish the frozen bound `N·β₁ + |x₁|·β₂` with the exact `|x₁|·β₂` term, by the exact witness?
  - Does any consumer route a step through `mul_bit` where the exact term is needed?
  - In phase 5 every `mul_bit` use has a fresh **bit** on the left: `mul_le`, `nand`, `encrypts_chain`
    (`Noise.lean:265, 280, 317`) and `homAnd_encrypts` (`Eval.lean:164`). Weakening `|b|` to 1 there costs nothing
    in the worst case `b = 1`. The BV14 selector step `(G−C)⊡V₀ + C⊡V₁`, which needs the exact `|1−b|` and `|b|`,
    is phase 6's.
- **`encrypts_chain` (`Noise.lean:296`).** Is the induction right? Check the right-associative order, the head on the
  left, the empty chain as the accumulator with message `1·x`, the noise `β₀ + (k+1)·N·β = N·β + (β₀ + k·N·β)`, and
  the message `(bs.all id).toNat · x`.
- **`decrypt_of_encrypts` (`Scheme.lean:272`), through the private `decrypt_eq_decode_errorSum` (`:213`).**
  - Is the residual exactly `codepoint b + ⟨e, G⁻¹(w)⟩`?
  - Is `|⟨e, G⁻¹(w)⟩| ≤ ℓ·β` correctly obtained from `errorSum_decomposeVec_le`, with `halfVector` vanishing off the
    last block?
  - Is `decode_codepoint_add (B := ℓ·β)` applied under exactly its premise `2·(ℓ·β) < ⌊q/2⌋`? Check this including
    **odd `q`** and **`q` = 2, 3**, where the premise forces `ℓ·β = 0`.
- **`decrypt_of_encrypts_dyadic` (`:293`).**
  - Are `⌊2^ℓ/2⌋ = 2^{ℓ−1} < q` and the indicator `G⁻¹(w) = 1_{(last, ℓ−1)}` (by `digits_injective`) proved for
    every `ℓ ≥ 1`?
  - The proof uses `hℓ`, which Gate 41 called redundant but harmless.
- **`eval_encrypts` (`Eval.lean:250`), via `runWith_rel`.**
  - The relation is vertex-indexed. Inputs have depth 0, through the `getD`/`List.ofFn` reads (GC-01).
  - The gate step uses `DAGGate.getD_lt_depth`, `depthAt_gate`/`depthAt_eq`, `Encrypts.mono` with
    `Nat.pow_le_pow_right`, `homGate_encrypts`, and `(N+1)·(N+1)^{d−1} = (N+1)^d` with `d ≥ 1`.
  - The output is read in range (`Cc.output_lt`). Acyclicity comes from `Cc.args_lt`; `IsFaninTwo` is not used.
- **`homAnd_encrypts` and `homGate_encrypts` (`Eval.lean:142`, `:181`).**
  - `homAnd_encrypts`: the bound `((k−1)·N+1)·β` with natural subtraction at `k` = 0, 1 and ≥ 2.
  - `homGate_encrypts`: `length ≤ 2` gives `(N+1)·β`, for `∧`, `¬` (as `G − ·`) and `∨` (De Morgan through
    `List.any_eq_not_all_not`), at arities 0, 1 and 2, with repeated arguments.
- **`decrypt_keygen_eval` (`Eval.lean:300`).** Does the proof use exactly the frozen condition
  `2·(ℓ·((N+1)^L·(m·B))) < ⌊q/2⌋`, with no extra factor and no `L+1`, for every seed and coin matrix?
- **F7's bijection** (`Symmetric.lean:110`, `:154`).
  - Is `exists_equiv_symEncrypt` a genuine equivalence onto `Fin k → Ciphertext P` that agrees with
    `symEncrypt P hN · μ` pointwise?
  - The equivalence is augmentation, then the hand-built `rowEquiv` column reindexing with its two inverse laws, then
    translation by `μG`.
  - Does `distAdv_symEncrypt_le` keep one common secret and all `k·N` rows on the real side, and is the empty batch
    handled?
- **F5's column hybrid** (`Columns.lean:86`).
  - Are `hleft` and `hright` correct for every `k < N`? Check the planting, the seed equivalences `e` and `e'`, and
    `Function.update` at `⟨k, hk⟩`.
  - Are the end hybrids `hzero` and `hfull` right?
  - Does the strong LHL apply to a test whose coins `Cols × ρ` are a product of finite nonempty types, under the
    shared matrix? Is `N = 0` covered?
  - No universality is claimed for the whole-matrix family.
- **F6's four hybrids and `2Nε`** (`Security.lean:156`, `:189`, `:248`, `:287`).
  - Is `real_uniformKey_advantage` an exact equality, with the reduction's coins exactly the binary matrix coins
    paired with `D`'s?
  - In `uniformKey_uniform_advantage_le`, are `keyEquiv` (keeping the whole public key), `unpack` and `keySeeds`
    bijections, and is `hsampler` correct?
  - Is F5 applied at `columnHashParameters P`, and does its bound read back as `N·Regev.extractionError P.lwe`?
  - `distAdv_encrypt_le`: does the chain give exactly two DLWE terms plus `2·(N·ε)`?
  - `_of_width`: is `2Nε ≤ N·2^{−κ}` correctly derived?
- **Sketches.** 27 target sketches were rewritten and 8 kept (`docs.txt`). Does each describe the delivered proof? A
  misstated sketch is a minor.

**2. Frozen statements.**
- Are the 35 headers, their prose and every pre-existing item of the 7 files unchanged (0/0/0 with controls,
  `frozen.txt`)?
- Are the only additions the 3 private theorems in #339 and the authorized import in both #338 files?
- Does any proof change what a statement means (none can, the headers being byte-identical)? Or does any proof rely
  on a statement of the other PR? #338 cites only gsw-core's `rfl` readers `encrypt_eq` and `lift_apply`, which are
  not targets (the gsw-security review's dependency trace).

**3. Duplication: the reviewers' findings, and anything undisclosed.** Grade each item below. **An undisclosed
duplicate of a public lemma is a major.** `dupscan.txt` lists the pattern sites in the added lines and the named
relatives at the tip, and `names.txt` shows that the 3 new names exist nowhere else in `TCSlib/` or `audits/`.
- **GC-01** (info, disclosed): `eval_encrypts`' inline getD/`List.ofFn` chain (`Eval.lean:262–264`) is the DL-47
  class.
  - The brief prescribed `List.getD_eq_getElem` and `List.getElem_ofFn`.
  - `GI.getD_ofFn_lt'` (`ZeroKnowledge/GraphIsomorphism/SoundnessRep.lean:61`) cannot be imported there.
  - **This pin adds the site to ledger row DL-47** (`ledger.txt`: a pure insertion, and the only ledger change).
- **GC-02** (info, disclosed): Bool `toNat` identities proved inline by `cases … <;> rfl`.
  - The review lists six sites (`homGate_encrypts` twice), plus the codepoint analogue `hb` in `Scheme`.
  - The pack's aid finds 8 case-split sites: `Noise.lean:263, 278, 304`; `Eval.lean:162, 214, 222, 231`; and
    `Scheme.lean:241`. `homGate_encrypts` has three: the two negations (`:214`, `:231`) and, at `:219–222`, the De
    Morgan form `(any).toNat = 1 − (all ¬).toNat`.
  - The review found no core, Batteries, Mathlib or TCSlib lemma stating them. Confirm.
- **GC-03** (info): `exists_equiv_symEncrypt` builds its column reindexing by hand.
  - A composition of Mathlib equivalences (`Equiv.arrowCongr`, `Equiv.curry`, `Equiv.piComm`, as
    `Randomized.blocksEquiv` does) would give it. The REPORT's "`Matrix.reindex` and `Equiv.curry` do not give the
    block shape" overstates this.
  - Its augmentation step repeats the inline `keyEquiv` of `Regev/Experiments.lean:260`, which is disclosed.
  - Is the hand-built equivalence a duplicate of a public result, or construction glue?
- **GC-04** (info): two public sketches (`decrypt_of_encrypts`, `distAdv_symEncrypt_le`) name private glue lemmas.
- **GC-05** (Rule 10 tooling): see question 4.
- **GC-06** (info): evidence and report nits. `width/final.txt` repeats two rows. Two relative citations are off by
  1–2 lines (`Regev/Basic.lean:119` → 121, `Lossy/Matrix.lean:128` → 127). Sub-agent B's line counts are off by one,
  and sub-agent A has no `final/` copies.
- **GS-01** (info, disclosed; **pending Seyoon's ruling**): F5's 98-line inline column hybrid re-derives a
  shared-parameter planting hybrid from public lemmas.
  - F6's `distAdv_encrypt_le` and `uniformKey_uniform_advantage_le` mirror `Regev/Experiments.lean:254–292` and
    `309–327` almost line for line.
  - Gate 41 and the briefs sanctioned both routes.
  - The recommendation awaiting the ruling: accept as disclosed ledger debt (`Columns.lean:95–192`;
    `Security.lean:197–238` and `256–279`), with payback through promotion **P-1**, as restated in GS-02. No ledger
    row is added until the ruling.
  - Does any **public** lemma already state the shared-parameter hybrid that F5 needs?
- **GS-02** (minor, erratum of missed relatives): the gsw-security REPORT's overlap table omits three relatives:
  - (a) `pairTuple`/`pairHybrid`/`pairRed` and their lemmas (`ZeroKnowledge/Commitment.lean:143–239`), whose seed
    types differ and which have no shared parameter;
  - (b) `distAdv_multi_le_sum` (`Encryption/PublicKey/EnsembleSecurity.lean:134`);
  - (c) `distAdv_comp` (`Pseudorandom/Indistinguishability.lean:141`), which **is in the authorized import**. It states
    `distAdv X Y (D ∘ P) = distAdv (P ∘ X) (P ∘ Y) D`.

  The review graded GS-02 minor, on the ground that (a) and (b) needed an import outside the brief's list. Please
  grade (c) on its own. The `hreal`/`hideal` steps of `uniformKey_uniform_advantage_le` (`Security.lean:225–232`)
  relabel through `acceptProb_comp_equiv`, closed by `simpa only [acceptProb_def]`. Is that an undisclosed re-proof
  of `distAdv_comp`, or an inline step that the lemma does not cover? It is over `acceptProb`, with an equivalence of
  seeds.
- **GS-03** (minor): `evidence/probes/CacheProbe.lean` is listed in both manifests but was never delivered. The
  review reconstructed it: the one line `import Mathlib.Algebra.BigOperators.Field` has the manifest's SHA-256
  `f8388ee6…`. See question 6.
- **GS-04** (info): a delivered `.pyc`.
- **GS-05** (info): the delivered "base" seals of `Security` ran against the final `Columns`. Their closure is 7
  constants larger, and there were 0 failures either way.
- **GS-06** (info): the key equivalence `Equiv.ofBijective _ (Regev.augmented_bijective _)` and the translation
  `Equiv.addRight` are inline at three sites (`Regev/Experiments.lean:260`, `GSW/Security.lean:202–206`,
  `GSW/Symmetric.lean:116, 136`). The candidate fix is a published `Regev.augmentedEquiv` (DW-4 queue).
- **And beyond these:** does any new declaration, or any part of a proof, duplicate a public TCSlib or Mathlib lemma,
  or copy a private one, that is not disclosed in the REPORTs' `## Overlap and reuse`?
  - Search the binary subset sums: `LWE.binaryErrorSum_bound`, `Regev.subsetError_bound`, `Lossy.error_sum_bound`.
  - Search the decryption residual: `Regev.encrypt_residual`, `Regev.decrypt_encrypt`.
  - Search the gadget lemmas, `runWith_sim`/`runWith_rel`, the hybrid lemmas (`abs_sub_le_sum_hybrids`,
    `exists_hybrid_gap`, the multicopy and `pair*` families, `distAdv_tuple_le_sum`), and the symmetric Regev
    experiments for F7.

**4. Rule 10.**
- **The seal evidence** is in the two review evidence ZIPs (`review-extracts/`).
  - `gsw-core`: own seals 20/20, five files × strict/coe × A/B, with 0 errors in both forms. Requests strict/coe:
    Gadget 51/51, Noise 59/59, Scheme 102/101, Symmetric 107/106, Eval 154/153. Canonical coe-A has 0 failing
    declarations. Controls ALL_OK, plus the strict `ctlCoeReader` artifact.
  - `gsw-security`: own seals 8/8; requests (Columns/Security) strict 32/115 and coe 31/114; coe-A 0 failing.
    Controls: 11 + 3 paired rows plus the coercion row; coe ALL_OK with 14 sealed failures per variant.
  - Both reviews' explicit-unfold scans find 0 foreign definitions as selectors.
  - The plan §G8 type-level list is covered: `Regev.augmented`, `LWE.sample`, `Lossy.gadget`,
    `Randomized.blocksEquiv` and `BitEncoding.codepoint`.
- **GC-05, the matcher note** (`p2/probe-sources/GcMatcher*.lean`, `p2/probe-runs/mods/GcProbe_GcMatcher*.log`).
  - `homGate_encrypts` cases on the gate kind and reduces the `match g.kind` that appears in the published readers
    `homGate_eq` and `DAGGate.eval_eq`.
  - `DAGGate.eval` and `eval_eq`'s statement share the deduplicated matcher `BoolCircuit.instReprGateKind.repr.match_1`
    (from the derived `Repr GateKind`).
  - Sealing that matcher does not block reducing it on constructors: GC05-A1..A3 pass. With `DAGGate.eval` itself
    sealed, the direct `rfl` read fails exactly once (GC05-NEG), and the reader route passes (GC05-POS).
  - So the "plus matchers" seal layer does not see matcher iota. Here the reduction goes through a reader's published
    statement.
  - Is that an acceptable reading of Rule 10, or a forbidden read? The review recommends a tooling note in
    `maintainer/tooling-followups.md`; it is **not yet filed** at this pin.
- **Spots for close reading:**
  - the `change` steps that unfold the Mathlib `vecMul`/`dotProduct` (`Noise.lean`, `Scheme.lean`,
    `Symmetric.lean`);
  - `dsimp only` after `Regev.decrypt_eq` in `decrypt_eq_decode_errorSum`;
  - the closing `rfl`s of `hashColumns_eq_mul`, `exists_equiv_symEncrypt` and `hhash` in
    `uniformKey_uniform_advantage_le`, which reach `columnHashParameters` (own file) and the `Equiv.ofBijective`
    coercion;
  - `Regev.augmented` used only as a term inside `Equiv.ofBijective`.
- Does any proof read another file's definition other than through a published reader?

**5. Docstrings, sketches and sources.**
- Every proof of 15 lines or more carries a sketch (`docs.txt`: 12 such proofs in all, none without one), and the
  long ones have step comments.
- The three private helpers have docstrings ("Technical glue", no tag). There is no new public declaration, so no
  formula docstring or `_eq` reader is owed.
- **Sources rule.** The citation groups of all 7 files are identical, as multisets, at base and head: no tag was
  added, removed or moved, and no sketch carries a tag (`sources.txt`).
  - DW-7 transcriptions now exist in `blueprint/src/references/` for [GSW13] (`gentry-sahai-waters-2013-fhe`), [AP14]
    (`alperin-sheriff-peikert-2014-bootstrapping`), [BV14] (`brakerski-vaikuntanathan-2014-fhe`) and [Pei16]
    (`peikert2016-lattice-survey`, extended with §5.4.3 and §6.1.2–6.1.3). All four are registered in `sources.json`,
    are in the bundle (`.md`), and are in `verification.zip` (`.md`, `.raw.md`).
  - A locator lookup (an aid) finds all 32 distinct (key, kind, number) locators cited at the heads in the
    transcriptions.
  - Use them to check the citations the targets carry, now against the transcriptions rather than the Gate 41
    excerpts. Is any tag fabricated or misplaced?
- `[Vad12]` (`Columns.lean:32`, the module's reference list) is not registered in `sources.json`. It is unchanged
  since the base; is that a pre-existing note?

**6. Evidence completeness and the multi-agent record.**
- Deliveries (`manifests.txt`, from git objects):
  - `gsw-core`: 544/544 top-level and 533/533 `evidence/`, with exact path sets.
  - `gsw-security`: 778 of 779 top-level and 771 of 772 `evidence/`; the one missing file is GS-03's. It also
    delivers one `.pyc` (GS-04).
- Review ZIPs: inner manifests 1095/1095 (`gsw-core-r1`) and 1022/1022 (`gsw-security-r1`).
  - **The records copy `fills/gsw-core/final-r1/evidence-SHA256SUMS` is empty (0 bytes)**, a filing defect. The
    inner manifest is in `verification.zip` as `review-evidence/gsw-core-r1-evidence-SHA256SUMS`.
  - gsw-security's records copy equals its inner manifest.
- `gsw-core`'s REPORT records who proved what. Sub-agent evidence is under `evidence/subagents/{A,B}/` (45 and 47
  files). The lead integrated the sub-agents' files unchanged, by hash against B's `final/` and A's reported hashes
  (GC-06). Is the record adequate?
- Is any evidence a claim rests on missing or unverifiable?

**7. Merge interaction** (facts for the audit; the conditions are the maintainer's, below).
- #338 and #339 change disjoint files, and their merge-tree is clean in either order. Each merge-tree with the tip
  (and with #331, #327, #324) is clean with no shared path (`mergetrees.txt`).
- **Each was built on the tip separately.** The review builds' sources equal the current tip with that PR merged:
  - `gsw-core` Phase 2 tree `76fae5c8` (tip `4941b511` + `d4ebb0be`): its `TCSlib/`, `TCSlib.lean`, `audits/`,
    `scripts/` and lake files equal those of `git merge-tree c999a83c 839f36cc`, 1440 paths.
  - `gsw-security` Phase 2 tree `ac512a9b` (scratch merge `a51294c5`): the same against `git merge-tree c999a83c
    d45d3682`.
  - Each build gave 650/650 rc 0, through root `TCSlib` and both `audits/*/Checks`.
- **The combined state is not built.** Five modules are downstream of both PRs (`downstream.txt`):
  `GSW/Security.lean`, which imports #339's `Scheme`, `Noise` and `Gadget`, plus the `GSW`, `Homomorphic` and
  `AdvancedEncryption` facades and root `TCSlib`.
  - #338's build had gsw-core's 29 targets still sorried, and #339's build had gsw-security's 6.
  - The headers being byte-identical, nothing in either PR's Lean depends on the other's proofs. Is there any reason
    the combined state could fail where each half passed?

## Known dispositions (not findings)

- **Review verdicts.**
  - `gsw-core`: **ACCEPT** (0/0/0, six info: GC-01..06), no landing edit.
  - `gsw-security`: **ACCEPT** (0/0, two minors GS-02 and GS-03, four info), no landing edit. GS-01 awaits Seyoon.
  - The PR descriptions (`pr/` in `verification.zip`) summarize the same.
- **Builds** (the reviews):
  - `gsw-core`: 650/650 rc 0, 0 `error:`/`error(`, 5863 s; admissions 237 → 208, exactly the 29 targets. The 29
    targets and all 114 stored constants use the standard three axioms, and the trace of 32 constants reaches no
    sorried constant.
  - `gsw-security`: 650/650, 5856 s; admissions 237 → 231. The 6 targets and 32 stored constants are standard, and no
    sorried constant is reached.
  - State and whole-tree checks are OK in both, and both olean trees were restored to `457ba704…` (SNAPSHOT EQUAL).
- **Lint:** 92 FAIL / 101 WARN at base and head for both, with identical line sets.
- **Worst-case bounds, the factor `ℓ`, deterministic `G⁻¹`, uniform secrets and the deferred `NUPPT` bridge** are
  ruled (Q3, Q5, Q6, Q8; plan §G8 risks 3, 4, 8). Small-secret LWE (A3) is not used in phase 5.
- **`columnHashParameters`** is the Q11 copy of `Regev.hashParameters`, disclosed at the statement phase.
- **The GC-05 tooling note** is not yet filed, and **GS-01's ledger row** waits for the ruling. The records'
  empty `gsw-core` `evidence-SHA256SUMS` is a filing defect (question 6). The maintainer handles all three; none
  is an audit item.

## Merge conditions (the maintainer's; not audit items)

1. **A combined build of both PRs is a merge condition.** At least the five modules downstream of both
   (`GSW/Security`, the `GSW`, `Homomorphic` and `AdvancedEncryption` facades, root `TCSlib`) must be built on the
   state with both merged: a scratch merge before the second PR merges, or the tip right after it.
   - Expected admissions on the combined tree: 237 − 35 = 202.
   - Expected axioms: the 35 targets standard.
2. **Merge order: either.** The two PRs are disjoint.
3. With **#331** (pairings), the facade `AdvancedEncryption.lean` and root `TCSlib` are downstream of both. Whichever
   lands second rebuilds them. With #327 and #324 only root `TCSlib` is shared.
4. **Clearance:** #338 also needs Seyoon's GS-01 ruling.

## Evidence

- **`verification.zip`** (138 entries, SHA-256 `a67700ec523fe4abd0258752c092a8775e1102a0a3950e79d0387ccc25ac2a01`). Its
  `SHA256SUMS` lists every other entry, and `PROVENANCE.txt` maps each to its source. It was built at records
  `c999a83c`, the tip; the duplication ledger is the pin's version, checked at staging. It holds:
  - `review-evidence/`: `gsw-core-r1-evidence.zip` (`4c481a79…`, 1096 entries) and `gsw-security-r1-evidence.zip`
    (`447f651d…`, 1023 entries), with their manifests;
  - `review-extracts/`: byte copies of the review entries cited above: PROVENANCE, frozen checks and controls, merge
    trees, build summaries, admissions diffs, axioms and traces, seal and control summaries, error counts, GC-05's
    probe sources and logs, unfold scans, clash, sketch and width checks, source tags, lint, the patch reproduction,
    the delivered-evidence re-checks, and GS-03's reconstruction;
  - `worker/<unit>/`: `REPORT.md`, the top-level `SHA256SUMS`, `patches/COMMITS.tsv` and the patches, from the final
    exchange commits;
  - `records/`: the issue packages (README, brief, SHA256SUMS, base-sorries, dispatch), both reviews, the rulings,
    questions and plan section, Gate 41's resolutions and findings, the decision log, policy, the deferred-work
    register, the tooling follow-ups and the duplication ledger;
  - `source-references/`: the DW-7 transcriptions (`.md`, `.raw.md`) and `sources.json`;
  - `context/`: library files at the tip for question 3 that are not in `sources.zip`: `ZeroKnowledge/Commitment`,
    `PublicKey/EnsembleSecurity`, `PublicKey/Hybrid`, `GraphIsomorphism/SoundnessRep`, `SecureComputation/Garbling`,
    `Symmetric/Regev/Experiments`, `Lossy/Experiments`, `Lossy/Matrix`, `Foundations/BitLists`;
  - `pr/`: the two PR descriptions as fetched from the GitHub REST API on 2026-11-16;
  - `pack-checks/`: `series`, `delivery`, `manifests`, `frozen`, `sorries`, `docs`, `sources`, `names`, `mergetrees`,
    `downstream`, `dupscan` and `ledger`, with their scripts (`tools/`). They use git objects and `python3 -I` only;
    nothing was built.
- **`pr-339.diff.txt`, `pr-338.diff.txt`:** each PR's diff from its base to its head.
- **`source-head.json`:** the heads, bases, and the hashes, line counts and over-width counts of the 7 files.
- **`sources.zip`** (`c99418c9…`): each PR's import closure at its head, under `pr-339-gsw-core/` and
  `pr-338-gsw-security/`, 25 files each.
- **The workers' own evidence** is on the exchange under `inbox/fills/gsw-core/` (`9e52a501`) and
  `inbox/fills/gsw-security/` (`5857e850`).

## Findings delivery

Return `gate43-gsw-fills-findings.md` as a Markdown file in this chat, with findings marked by PR (#339, #338, or
both). If you have several evidence files, return a ZIP.

| # | Severity | PR · file · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

**Severities**
- **blocker:** a proof that does not establish its frozen statement, or a scope violation (a frozen or non-owned file
  changed, or an unauthorized import).
- **major:** a changed frozen statement or prose; a forbidden read in a proved declaration not covered by the rulings;
  an undisclosed copy of a private lemma or undisclosed re-proof of a public one; or necessary evidence that cannot be
  verified.
- **minor:** documentation or API defects, including an inaccurate proof sketch or disclosure.
- **note:** anything else.

Report the audited heads and the counts by severity, per PR. The gate closes at zero blockers and zero majors.
