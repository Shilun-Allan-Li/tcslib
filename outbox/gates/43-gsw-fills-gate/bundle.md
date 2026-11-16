## ===== briefs/lattice-gsw/gates/43-gsw-fills/pack.md =====

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

## ===== briefs/lattice-gsw/fills/gsw-core/final-r1/review.md =====

# gsw-core · maintainer delivery review (r1)

**Verdict: ACCEPT.** All 29 targets are proved with the standard three axioms only. The review finds 0 blockers,
0 majors, 0 minors and six info findings. No landing edit is proposed: the delivered head lands as is.

## Delivery and landing
- **Delivery:** Claude, a lead with two sub-agents:
  - A: F1 and F2, in `Gadget` and `Noise`;
  - B: F3 and F7, in `Scheme` and `Symmetric`;
  - the lead: F4 in `Eval`, plus integration, every commit and the final checks.
- **Exchange commits:** the final is `9e52a5019258c51d67b1f28d3675c66cf787209b` and the checkpoint is
  `5b72e346bd5484fb059cbaadd836de88f4adf0a2`. Both touch only `inbox/fills/gsw-core/`.
- **Issue base:** `486f44f8414c20a2d21e452c44de8b8c8d8513a0`, #333's head, with #332 as an ancestor.
- **Head:** `d4ebb0be088e5985337ccb4e0a61cb3a662e8b73`, three commits:
  - `243a44cd`: F1 and F2;
  - `a1bc6aac`: F4, with `decrypt_keygen_eval` proved modulo F3 at that point;
  - `d4ebb0be`: F3 and F7.

  The checkpoint carried the first two commits, with the same hashes.
- **Files:** the five owned files only, +542/−89:

  | File | Lines (base → final) |
  |---|---|
  | `Gadget` | 204 → 236 |
  | `Noise` | 235 → 321 |
  | `Scheme` | 215 → 364 |
  | `Symmetric` | 111 → 185 |
  | `Eval` | 209 → 321 |

  No import was added. No frozen file, helper module or facade was touched, and there was no scope request.
- **Landing:**
  - The base is an ancestor of the records tip `4941b5119c82431452face78071bd4376ee3e427`; #332 and #333 are merged.
    Since the tip used in Phase 1 (`d0007941`), the tip has changed only in records.
  - `git merge-tree` of the tip and `d4ebb0be` is clean and gives tree `76fae5c89bce2097cf32b536edfdec6544a49bcb`. It
    differs from the tip only in the five files, each blob-equal to the delivered one. This is the tree that was built.
  - Between the base and the tip, two modules in the build order changed, both by additions only: `DAGCircuit` gained
    `isFaninTwo_iff` and `Randomized/Classes` gained `inBPP_iff`. Neither name clashes with the fill.
- **Evidence:** `gsw-core-r1-evidence.zip`, SHA-256 `4c481a79b6995ffb7fc3135a83683ec790a210018e2f5f77cd5392d74029a61c`, 1096 entries. It does not include the delivery,
  which is on the exchange.

## Checks
- **Integrity.**
  - The top-level manifest verifies 544/544, and its path set equals the delivered files exactly, with no `./`.
  - `evidence/SHA256SUMS` verifies 533/533 with an exact path set (534 files including the manifest).
  - `git am` at the base, with the recorded identities and dates, reproduces all three hashes, unsigned. The five
    files equal `src/`.
- **Build, on the merged tree with `dl-oleans`.**
  - 650 modules were rebuilt and 638 reused. All 650 give rc 0, with 0 errors in both forms and no `error`
    substring. That covers root `TCSlib` and both `audits/*/Checks`, in 5863 s.
  - The pinned Mathlib `NthRootLemmas` was built separately (rc 0).
  - The whole-tree check covers 1288 modules: OK. The state check is OK.
  - The five owned modules have 0 warnings. `Security`, the GSW, Homomorphic and AdvancedEncryption facades, root
    `TCSlib` and both `Checks` give rc 0.
- **Statements.** I checked them with my own script, independently of the delivery's.
  - Every base item of the five files reappears in order.
  - The 29 targets keep their headers byte-identical, and their docstrings byte-identical up to `**Proof sketch.**`.
  - Everything else is byte-identical: every definition, reader, structure and abbrev, every `variable`, `section`,
    `open` and `set_option`, every import, and the module docstrings.
  - Result: 0 differences, 0 removals and 0 order violations. The only additions are the three private helpers.
  - All nine controls pass:
    - a one-character change to a header, and to prose, each give exactly 1 difference;
    - a deleted reader gives exactly 1 removal;
    - a changed definition body gives 1 difference;
    - swapping two blocks gives order violations;
    - an edited `variable` line and a deleted import each give 1 removal;
    - an added public theorem is reported as `PUBLIC`;
    - a sketch-only edit gives 0.
  - `decls2.py` reports 0 public changes. `touched.py` reports 29 CHANGED (the targets), 3 ADDED and 52 UNCHANGED.
- **Style.**
  - Line widths are ≤ 100 (the maximum, 100, is in `Symmetric` and was there at the base). Files are ≤ 364 lines.
  - There is no `µ`, tab, trailing space, `@[simp]` or `attribute` command.
  - Every proof of 15 lines or more has a sketch and step comments, and every rewritten sketch describes the delivered
    proof.
  - The three private helpers have docstrings ("Technical glue", no tag).
- **Sources.** The source tags are identical at base and final: none was added, and no sketch carries a tag.
- **New declarations and clashes.** There are three, all `private`:
  - `halfVector_eq_zero_of_ne_last` (`Scheme:201`);
  - `decrypt_eq_decode_errorSum` (`Scheme:213`);
  - `exists_equiv_symEncrypt` (`Symmetric:110`).

  None of these names exists in `TCSlib/` or `audits/` at the base or the tip, nor in the Mathlib, Batteries or core
  sources at the pin.
- **Duplication.**
  - I searched the tip and the Mathlib/Batteries/core sources for each new declaration and each disclosed inline
    re-proof. I also looked for undisclosed ones: getD of `List.ofFn`, Bool `toNat` of `&&` and `!`, LWE sample
    equality, `Fin.snoc` away from the last index, casts of binary sums, block and column equivalences, and the
    triangle and equivalence lemmas for `acceptProb`.
  - I found **no undisclosed duplicate of a public lemma**. The disclosures are accurate (GC-01 to GC-03).
- **Axioms (my census probe).**
  - `#print axioms` gives exactly `propext`, `Classical.choice` and `Quot.sound` for all 29 targets.
  - The five modules store 114 constants. Their axiom union is the standard three, and none uses `sorryAx`.
  - A dependency trace of the 29 targets and the 3 helpers reaches no sorried constant.
  - The closure sizes equal the delivered ones; for example, `decrypt_keygen_eval` has 7627.
- **Admissions.** The census goes from 237 at the tip to 208 on the merged tree, over 1288 modules. The difference is
  exactly the 29 targets: Gadget 5, Noise 12, Scheme 6, Symmetric 2 and Eval 4. Six admissions remain, in `Columns` (2)
  and `Security` (4); these are gsw-security's.
- **Rule 10.**
  - **Seals.** I built my own seals over each file's full TCSlib import closure, from the elaborated terms plus matchers
    (`mkseals_ab`/`mkseals_coe`), and ran them with `-DmaxErrors=0`. All 20 probes pass with 0 errors in both forms,
    each with install and EOF records. They cover strict A and B and coe A and B for each of the five files.
  - **Canonical coe-A:** 0 failing declarations.
  - **Request counts (strict/coe):** Gadget 51/51, Noise 59/59, Scheme 102/101, Symmetric 107/106, Eval 154/153.
    A = B, since `PolyExpr.eval` is outside every closure.
  - **Paired controls** (my `mkctl_gsw.py`), covering the type-level definitions of plan §G8 and the definitions of
    the other owned files:
    - Coe controls, A and B: ALL_OK. Every negative fails exactly once when sealed, every positive passes, and the
      unsealed probes have rc 0.
    - Strict controls: the only difference is the expected `ctlCoeReader` failure, because strict seals the FinDist
      coercion.
    - The control runs give 180 errors in total, all inside controls.
  - **Explicit-unfold scan (Phase 1).** 0 foreign TCSlib definitions and 0 core/Mathlib definitions appear as selectors.
- **Delivered evidence.** I re-parsed it from the raw logs and it agrees with the above:
  - 20/20 final and 20/20 base seal probes have 0 errors; the probes equal the source plus the install block.
  - The controls have exactly one error per negative.
  - The delivered axiom log lists 114 constants, all standard.
  - The delivered sweep shows 35 → 6 sorries.
- **Lint.** My rerun gives 92 FAIL / 101 WARN at both base and final, with identical line sets.
- **Overlap with gsw-security.** Its checkpoint touches only `Hashing/SIS/Columns.lean`, so the files are disjoint.
- **Restore.** `dl-oleans` is back to `457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f`:
  - the snapshot is equal, and `restoreplan` reports 0 extra, 0 changed and 0 missing;
  - a second, independent snapshot agrees;
  - the 561 backups were restored, and the 89 new oleans and the Mathlib overlay were deleted.

## Findings

| # | Severity | Finding | Disposition |
|---|---|---|---|
| GC-01 | info, disclosed | `eval_encrypts` reads the input vertices with an inline chain for getD of `List.ofFn` (`Eval.lean:262–264`: `List.getD_eq_getElem`, `List.getElem_ofFn`). This is the DL-47 class (cf. SG-F04). The brief's F4 route prescribes exactly these two Mathlib lemmas. The nearest public generic lemma, `GI.getD_ofFn_lt'` (`ZeroKnowledge/GraphIsomorphism/SoundnessRep.lean:61`), cannot be imported here. REPORT §Overlap item 9 lists the chain as reuse. | No LE. Add this site to the DL-47 ledger row, so the planned generic getD reader re-points it. |
| GC-02 | info, disclosed | Six proofs prove these Bool identities inline by `cases … <;> rfl`: `((a && c).toNat : ℤ) = a.toNat * c.toNat` and `((!c).toNat : ℤ) = 1 − c.toNat`. The proofs are `mul_le`, `nand` and `encrypts_chain` in `Noise`, and `homAnd_encrypts` and `homGate_encrypts` (twice) in `Eval`; `hb` in `Scheme` is the codepoint analogue. I confirm that no core, Batteries, Mathlib or TCSlib lemma states them. | None. A small shared lemma could be added in the cleanup; the worker offers one but does not request a promotion. |
| GC-03 | info, disclosed | `exists_equiv_symEncrypt` (private) builds the column-reindexing equivalence by hand. The REPORT says "`Matrix.reindex` and `Equiv.curry` do not give the block shape"; that slightly overstates it. A composition of Mathlib equivalences would give it: `Equiv.arrowCongr` with `rowEquiv`, `Equiv.curry` and `Equiv.piComm`. This is the pattern of `Randomized.blocksEquiv`. Its augmentation step repeats the inline `keyEquiv` of `Regev/Experiments.lean:260`, which is disclosed. | None. |
| GC-04 | info | The public sketches of `decrypt_of_encrypts` and `distAdv_symEncrypt_le` name the private glue lemmas `decrypt_eq_decode_errorSum` and `exists_equiv_symEncrypt`. The sketches are accurate, but API readers cannot see those names. | None. Rewording in an LE-doc is optional. |
| GC-05 | info (tooling), settled | `homGate_encrypts` case-splits `g : DAGGate` and `GateKind`, then reduces the `match g.kind` that appears in the published readers `homGate_eq` and `DAGGate.eval_eq`, on constructors. My probe settles how the seals treat this:<br>• `DAGGate.eval` and the statement of `eval_eq` share Lean's deduplicated matcher `BoolCircuit.instReprGateKind.repr.match_1`, which comes from the derived `Repr GateKind`.<br>• With that matcher sealed irreducible, the three reader-route reductions (`.and`, `.not`, and `.or` after `subst`) still pass.<br>• With `DAGGate.eval` also sealed, the direct `rfl` read fails exactly once and the reader route passes. Unsealed, everything passes.<br>So sealing a matcher does not block reducing a `match` on constructors, and the seals cannot see such reductions. Here the reduction goes through the reader's published statement, which is the brief's route and not a read of a definition body. The definition itself is sealed and was not read: `ctlDagEval` fails when sealed. | None on the delivery. Add a note to `maintainer/tooling-followups.md`: the "plus matchers" layer of the seals does not block matcher iota. |
| GC-06 | info | Nits in the evidence and the report:<br>• `width/final.txt` repeats the `Eval` and `Symmetric` rows.<br>• Two relative citations are off by 1–2 lines: `Regev/Basic.lean:119` should be `herr` at 121, and `Lossy/Matrix.lean:128` should be `residual_conceal` at 127.<br>• Sub-agent B's report gives 365 and 186 lines; the delivered files have 364 and 185 (B's hashes match).<br>• Sub-agent A has no `final/` copies; the hashes in its report match the delivered files. | None. |

## Proposed landing edits
None. The landing is `d4ebb0be` merged (or rebased) onto the tip. The merge is clean and touches only the five files.

## Evidence (`gsw-core-r1-evidence.zip`, under `gsw-core-r1/`)
- `PROVENANCE.txt`, `PHASE2-PLAN.txt`, `SHA256SUMS`.
- Phase 1:
  - `integrity/`, `statements/` (with `frozen-final.txt` and `frozen-controls.txt`), `style/`, `sources/`, `clash/`;
  - `rule10/` (the unfold scan and its dispositions), `lint/`;
  - `delivered-evidence-check/`, `landing/`, `tools/` (`frozen.py`, `frozen_controls.py`, `unfold_scan.py`,
    `mkctl_gsw.py`).
- Phase 2 (`p2/`):
  - Setup: `merge-tree-current-tip.txt`, `export-check.txt`, `order/`, `plan/`, `tree/` (snapshot-pre and -post,
    backup lists), `ref/`.
  - Build: `build-mathlib-extra/`, `build/` (`results.jsonl`, `per-module.tsv`, every module log), `state.json`,
    `state-out/`, `records/`, `tree-final/`.
  - Results: `admissions/`, `probe-sources/`, `probe-runs/` (census, GC-05 sealed and unsealed, collector),
    `seals/`, `seals-coe/`, `seal-runs/`, `controls/`, `controls-strict/`, `control-runs/`, `summary/`
    (`sealsum-*.tsv`, `ctlcheck*.json`/`.log`, `error-counts.tsv`, `axioms-summary.txt`).
  - Restore and scripts: `restore/`, the run scripts, and `statements/touched.json`.
- `p2-tools/`: the maintainer tools reused unmodified.

**Clear to merge**: the fill's head `d4ebb0be`, by the maintainer's landing PR.

## ===== briefs/lattice-gsw/fills/gsw-security/final-r1/review.md =====

# gsw-security · maintainer delivery review (r1)

**Verdict: ACCEPT, no landing edit.** All six targets (F5 `hashColumns_eq_mul`, `distAdv_hashColumns_uniform_le`; F6
`real_uniformKey_advantage`, `uniformKey_uniform_advantage_le`, `distAdv_encrypt_le`, `distAdv_encrypt_le_of_width`) are
proved exactly as frozen.
- On the merge of the current records tip with the delivered head, all 650 rebuilt modules pass, through root `TCSlib` and
  both `audits/*/Checks`.
- The targets use only the standard three axioms, and no target reaches a sorried constant.
- Rule 10 holds: the canonical coe seal A finds 0 failing declarations.

There are 0 blockers and 0 majors. There are two minors: GS-02, a disclosure erratum, and GS-03, an evidence file that was not
delivered and that I reconstructed. There are four info findings. **GS-01, the disclosed duplication of the hybrid pattern,
awaits Seyoon's ruling** on the debt and its payback (promotion request P-1).

## Delivery and landing
- **Delivery:** a single-agent Claude fill.
  - The final is exchange `5857e850e7f7daf264d2860caf27341e3052f8c5`; the checkpoint is
    `b08456186ebfa194f8445f1f78ba7c0743e4991b` (F5).
  - Both commits touch only `inbox/fills/gsw-security/`, and the history is linear.
  - The issue base is `486f44f8414c20a2d21e452c44de8b8c8d8513a0`, #333's head, with #332 as an ancestor. Both have since
    merged, so the base is an ancestor of the tip.
- **Head:** `a9f97eddb42c7dfc0422fa8c9ce998c658bfa4f8`. It has two commits: `58a97f52` (F5, the checkpoint's) and `a9f97edd`
  (F6). Neither is signed; `COMMITS.tsv` reads `none`.
- **Files:** only the two owned files, +219/−26:
  - `Hashing/SIS/Columns.lean`: 89 → 194 lines;
  - `AdvancedEncryption/Homomorphic/GSW/Security.lean`: 217 → 305 lines.

  Nothing else changed: there is no new declaration (public or private), no helper module, no facade, no frozen-file edit and
  no scope request. The one new import, in both files, is `TCSlib.Cryptography.Pseudorandom.Indistinguishability`, which the
  brief authorizes; its closure is 4 modules. `Columns` imports nothing under `AdvancedEncryption/`.
- **Landing:**
  - `git merge-tree` of the records tip `e2f5850fcd1b38738f7ad2f2cd413c840803ef90` and `a9f97edd` is clean, giving tree
    `ac512a9b`. I recorded it as the scratch commit `a51294c5`, which is unsigned and never pushed.
  - The merge differs from the tip only in the two files, and each equals the delivered file. The tip's code paths are equal to
    those of `4b46c488`, which Phase 1 merged (tree `710f1fcd`).
  - The three-way merge with gsw-core's head `d4ebb0be` is also clean. The two fills own disjoint files, and gsw-core changes
    no import and keeps `encrypt_eq`, `lift_apply` and `gadget`.
  - Between the base and the tip, one module in the owned closure changed: `Randomized/Classes` gained `inBPP_iff`, an addition.
- **Evidence:** `$SP/dl-review/gsw-security-r1/`. The ZIP `gsw-security-r1-evidence.zip` has SHA-256
  `447f651d4f5e5aed92642d31e3529475d1455a489a620a7d46b9f631d210d7fb`. It has 1023 entries: the 1022 manifest paths plus
  `SHA256SUMS` (SHA-256 `d2482963…`).

## Checks (Phase 1, static)
- **Integrity.**
  - **Manifests.** The top-level `SHA256SUMS` lists 779 files, of which 778 are present: `evidence/probes/CacheProbe.lean` is
    missing (GS-03). `evidence/SHA256SUMS` lists 772, of which 771 are present (the same file). There are 0 hash mismatches,
    no extra file and no `./`.
  - **Patches.** `git am` at the base, with the recorded identities and dates and `commit.gpgsign=false`, reproduces both
    hashes unsigned (`%G?` N), giving tree `6dd1a771`. `src/` equals the two changed paths byte for byte.
  - **Pack and sources.** The issue pack verifies 7/7, and its exchange copy is blob-identical. `SOURCE-SHA256SUMS` verifies
    147/147 at the base.
- **Statements, by my own script** (independent of the delivery's):
  - `Columns` 4/4 and `Security` 13/13 base declarations reappear in order, with 0 differences.
  - The six target headers are byte-identical, and so is their prose up to `**Proof sketch.**`.
  - Every non-target is byte-identical, body included: `hashColumns`, `view`, `realView`, `uniformKeyView`, `reduction`,
    `columnHashParameters`, the five readers and the `attribute [simps …]` line. So is every `open`, `set_option` and module
    docstring.
  - The only addition is the import.
  - Ten controls per file each give the expected count: one-character header 1, deleted reader 1 removal, definition body 1,
    target prose 1, sketch-only edit 0, removed option 1, added option 1, order swap 1, one-character command 2, identity 0.
  - `decls2.py`: 0 ADDED, 0 CHANGED, 0 REMOVED. The delivered header check and its two controls agree.
- **Style.**
  - Widths are at most 100 (`Columns` 100, `Security` 99), and the files have 194 and 305 lines.
  - There is no `µ`, tab, trailing space, `@[simp]` or new attribute.
  - Every target has a sketch that describes the delivered proof. The two long proofs (`distAdv_hashColumns_uniform_le`, 98
    lines; `uniformKey_uniform_advantage_le`, 42) and `distAdv_encrypt_le` carry step comments.
- **Sources.** The source-tag multisets of both files are identical at base and final, and the sketches carry no tag. No
  excerpt or location is fabricated. The Gate 41 excerpts were not needed.
- **Names.** There are no new names, so there is nothing that could clash with the base or the tip.
- **Lint.** My rerun at base and final gives 92 FAIL / 101 WARN over 364 files at both. The FAIL and WARN line sets are
  identical; only the two owned files' INFO size lines change. The results equal the delivered logs. At the merge it is
  92/101 over 385 files, with FAIL/WARN line sets identical to final's.
- **Rule 10, by reading the source.**
  - My explicit-unfold scan covers 90 rule heads (65 lemmas, 25 local `let`/`have` names) and finds 0 foreign definitions.
  - `Security` reads `hashColumns` only through `hashColumns_eq_mul`, `encrypt` through `encrypt_eq`, `lift` through
    `lift_apply`, `LWE.decisionAdvantage`, `Regev.extractionError` and `distAdv`/`acceptProb` through their readers, and its
    own `columnHashParameters` through its `simps` readers.
  - `Regev.augmented` appears only as a term inside `Equiv.ofBijective … (Regev.augmented_bijective …)`. Its declared codomain
    is `Fin (n+1)`-indexed, so the `AugKey` type is reached without a type-level unfold. `Regev.hashParameters` is not used.
  - Mathlib definitions (`Matrix.mulVec`, `Matrix.of`, `Equiv` coercions) reduce only in `rfl` or term steps.
- **Delivered seal, control, axiom and admission evidence** (re-parsed from the raw logs):
  - **Seals.** Each of the 24 seal probes reproduces its source exactly (contiguous line map, hoisted imports), with one install
    and one EOF record and 0 errors in both forms.
  - **Controls.** There are 35 at the checkpoint and 55 at final. Every sealed negative fails exactly once; the coercion fails
    only under strict.
  - **Errors.** Across 454 logs there are 38 `error:` and 5 `error(`. All are expected control negatives or the disclosed
    development iterations.
  - **Admissions,** recounted from the raw sweeps: 51 in 14 modules at checkpoint 1, and 47 in 13 at final.

## Checks (Phase 2, Lean, on `$SP/dl-oleans-2`)
- **Build.** The source is an export of the merge `a51294c5`: only `TCSlib/`, `audits/`, `scripts/` and the lake files, with
  the shared `.lake/packages` linked.
  - The tree starts at snapshot `457ba704…` (1230 files), which is the oleans at `eff2dcd0`.
  - The incremental plan by import-closure keys gives 650 builds and 638 reuses. Those 650 are exactly the downstream of the
    changes since `eff2dcd0`, including root `TCSlib` and both `audits/*/Checks`.
  - The 561 snapshot oleans to be overwritten were backed up and hash-verified. The Mathlib overlay and `NthRootLemmas`
    (built through `lean_check_tree.sh`, olean `c0a9cff0…` as before) were added.
- **Results.** 650/650 modules give rc 0, with 0 `error:`, 0 `error(` and 0 occurrences of the substring "error". The build
  took 5856 s of module time (10:50–12:28 UTC), with a maximum RSS of 4.51 GB.
  - `Columns` (2.8 s) and `Security` (3.0 s) show 0 sorry and 0 warnings. So do the `Hashing/SIS`, `Hashing`, `GSW`,
    `Homomorphic` and `AdvancedEncryption` facades, root `TCSlib` and both `Checks`.
  - **References.** 648 of the 650 modules are byte-identical, in both olean and log, to a same-source reference record from
    earlier builds of the tip's code. The other two, `Columns` and `Security`, have new sources.
  - **State check:** 1288 modules OK. **Whole-tree check:** every module is rc 0 at the merge's source and every olean equals
    its record; no olean is missing, stray or zero-byte, and no directory is empty.
- **Admissions.** The tip has 237; the merge has 231. The difference is exactly `Columns` 2 → 0 and `Security` 4 → 0, and no
  other module changes. The gsw-core files keep their 29 tip admissions.
- **Axioms**, from my own probe: all six targets and all 32 stored constants of the two modules use only `propext`,
  `Classical.choice` and `Quot.sound`.
  - My dependency trace walks types and values, theorem bodies included, and reaches no sorried constant from any target. The
    closure sizes are 2444, 19103, 9349, 19199, 19214 and 19231, the same as the delivery's.
  - The only gsw-core theorems reached are the `rfl` readers `encrypt_eq` and `lift_apply`. The tip still admits every
    gsw-core target, so this confirms that no gsw-core target is cited.
- **Rule 10, my own canonical seals.**
  - Method: the collector reads the elaborated terms and the closures, and the archived Gate 06/10 instrumenter seals every
    ordinary TCSlib definition of each file's import closure. Each probe runs with `lean -DmaxErrors=0` and without `-o`.
  - **Seals:** 8/8 probes (`Columns` and `Security` × A/B × strict/coe) give rc 0, with 0 `error:` and 0 `error(`. Each
    has its install and EOF records, with every request verified.
    - Requests: strict 32 and 115; coe 31 and 114. Strict differs from coe only by the projection coercion
      `FinDist.instCoeFunForallReal`.
    - A = B, because `PolyExpr.eval` is in neither closure.
    - The **canonical coe seal A** fails on 0 declarations in either file. The request counts equal the delivery's.
    - Coverage includes the SIS `hash`, `hashColumns`, `Regev.augmented`, `Regev.hashParameters`,
      `Regev.extractionError`, `LWE.sample`, `LWE.decisionAdvantage`, `BitEncoding.codepoint`, both `gadget`s, `encrypt`,
      `lift`, `acceptProb` and `distAdv`, which covers plan §G8's type-level list.
    - Every foreign definition that the stored constants reference is either sealed or an abbreviation, which is notation:
      `Ciphertext`, `Parameters.columns`/`lwe`, `Noise.Coins` and the `Parameters` fields.
  - **Controls, written by me:** 11 paired rows for `Security` and 3 for `Columns`, plus the coercion row under strict.
    - Each negative is the bare `rfl` unfolding, and each positive is the published reader: `hash_eq`,
      `hashColumns_apply`, `augmented_eq`, `hashParameters_dimension`, `extractionError_eq`, `sample_fst`,
      `decisionAdvantage_eq`, `encrypt_eq`, `lift_apply`, `acceptProb_def`, `distAdv_def`, `FinDist.coe_mk`.
    - In the coe variants (A and B), 8 probes are **ALL_OK**: unsealed, all pass; sealed, each negative fails exactly once
      (14 failures), the positives pass, there is no stray error, and the install and EOF records are present.
    - In the strict variants, the only deviation is `ctlCoeReader` (`FinDist.coe_mk` at an anonymous-constructor
      `FinDist`), which also fails once in each sealed probe. This is the known strict artifact from the seq-zk review;
      the coe seal is canonical.
    - Error counts in both forms: probes 0/0, seals 0/0, coe controls 14/0 per variant, strict controls 18/0 per variant.
      All are expected.
- **Restore.** All 561 backups were restored, each hash-checked, with 0 failures. The 89 new oleans and the Mathlib overlay
  (3346 symlinks plus `NthRootLemmas`) were deleted, and 18 emptied directories were removed.
  - `restoreplan` reports extra 0, changed 0 and missing 0.
  - `snapshot-post` has 1230 files and SHA-256 `457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f`, and is
    byte-equal to `snapshot-pre` (**SNAPSHOT EQUAL**). A fresh recheck snapshot is also equal.
  - The probes wrote nothing to the tree. The backup, the export and the delivery extract have been removed.

## Findings

| # | Severity | Finding | Disposition |
|---|---|---|---|
| GS-01 | info, disclosed | **Duplicated proof pattern, disclosed and within the brief.** (1) F5's 98-line inline column hybrid re-derives the shared-parameter planting hybrid. Its `hleft`/`hright` steps re-derive the planting identity from public lemmas (`acceptProb_bind`, `acceptProb_comp_equiv`, `acceptProb_update`); `hzero`/`hfull` are the end hybrids. (2) F6's proofs mirror `Regev/Experiments.lean` almost line for line: the 3×`abs_sub_le` triangle chain of `distAdv_encrypt_le` and the `hreal`/`hideal` relabel-into-test steps of `uniformKey_uniform_advantage_le`. Gate 41 and the brief sanction both routes (the generic column hybrid belongs in `Columns`; F6 restates the Regev hybrids for GSW's ciphertext space), and no generic `distAdv` triangle lemma exists. The REPORT discloses each step and proposes P-1, a generic shared-parameter hybrid in the probability layer. Policy §1 requires every duplicated proved material to be human-approved. | **Awaiting Seyoon's ruling.** Recommended: accept as disclosed debt. Add a duplication-ledger row naming the copies (`Columns.lean:95–192`; `Security.lean:197–238` and `256–279` against `Regev/Experiments.lean:254–292` and `309–327`). Payback is P-1 as restated in GS-02, in the cleanup queue. No landing edit. |
| GS-02 | minor | **Overlap disclosure is incomplete, and P-1 misstates the gap.** The `## Overlap and reuse` table omits three public relatives: (a) the generic coordinatewise hybrid with **different seed types** in `ZeroKnowledge/Commitment.lean:148–239` (`pairTuple`, `pairHybrid`, `pairRed`, `acceptProb_pairHybrid_zero/_self`, `acceptProb_pairRed_left/_right`, `exists_pairRed_ge`), which is the nearest relative of `hleft`/`hright`/`hzero`/`hfull` and appears in the worker's own `evidence/overlap/searches-tcslib.txt`; (b) `distAdv_multi_le_sum` (`Encryption/PublicKey/EnsembleSecurity.lean:134`), the public form of the disclosed `distAdv_tuple_le_sum`, which `Security`'s own module docstring cites; (c) `distAdv_comp` (`Pseudorandom/Indistinguishability.lean:141`, in the authorized import), which states the `hreal`/`hideal` relabel-into-test step. P-1 asks for a hybrid "for two samplers with *different* seed types"; `pairHybrid` already provides that. What is missing is only the **shared public parameter**, which `pairHybrid`'s independent coordinates cannot express. Neither reuse was available without an import outside the brief's list or a new shared lemma, so no code change follows. | **Erratum, recorded here.** P-1 is restated: generalize `pairHybrid`/`pairRed` with a shared parameter `κ`, then re-derive `distAdv_tuple_le_sum` and `Columns`' hybrid from it. Ledger row with GS-01. No landing edit. |
| GS-03 | minor | **Evidence completeness: one delivered-manifest file is missing.** `evidence/probes/CacheProbe.lean` is listed in both manifests at the checkpoint and at final but was never committed, so the REPORT's "listed paths equal the delivered files exactly" is false, as is its mention of `evidence/probes/`. The file is the environment's cache probe; its log `evidence/logs/cache-probe.log` is delivered, and no proof claim depends on it. **Reconstructed:** the one line `import Mathlib.Algebra.BigOperators.Field` plus a newline has exactly the manifest's SHA-256 `f8388ee61e1b1b5ba7d6786f99b895008e3278cb1f06a0063fe1434571d444a1` (evidence `out/reconstructed/`). | **Accepted with the reconstruction.** No re-delivery needed. Recorded for the intake: the exchange path set is 778 files against a 779-path manifest. |
| GS-04 | info | `evidence/headers/__pycache__/frozen_headers.cpython-313.pyc`, a compiled tool artifact, is delivered and listed in the manifests. It is harmless. | None. |
| GS-05 | info | The delivered "base" seals of `Security` ran after the final sweep, against the final `Columns` olean. Their closure therefore includes `Pseudorandom/Indistinguishability` (115/114 requests, the same as final; the true base would have 7 fewer: `copies`, `mixDist`, `multicopyAvgRed`, `multicopyHybrid`, `multicopyRed`, `pushSampler`, `sunglassRed`). The REPORT's "at base" label is imprecise. There are 0 failures either way, so no attribution depends on it. | None. |
| GS-06 | info | **Cross-fill note.** The same two inline relabellings appear at three sites: the key equivalence `Equiv.ofBijective _ (Regev.augmented_bijective _)` and the translation by `μG`/the codepoint (`Equiv.addRight`). The sites are `Regev/Experiments.lean:260`, `GSW/Security.lean:202–206` and gsw-core's `GSW/Symmetric.lean:116,136`. | None now. A published `Regev.augmentedEquiv` (with its `_apply` reader) is a candidate for the DW-4 deduplication queue. |

## Proposed landing edits
None. The delivery lands as is, after #332 and #333, which have merged; it rebases onto the tip with no conflict. The
REPORT errata (GS-02, GS-03) are recorded here and need no change to the delivery.

## Evidence (`$SP/dl-review/gsw-security-r1/`, ZIP `gsw-security-r1-evidence.zip`)
- `PROVENANCE.txt` (method, hashes, every step), `PHASE2-PLAN.txt`, `SHA256SUMS`.
- **Phase 1:**
  - `out/`: manifests, patch reproduction, package and source verification, frozen check and controls (`out/headers/`),
    `decls2`, widths, source tags, lint (`out/lint/`, base, final, merge), unfold scan, duplication searches at the tip,
    merge-tree, the delivered-evidence re-checks (seal probes against source, error counts, sweep admissions), the
    reconstructed `CacheProbe.lean`, and copies of the delivered `REPORT.md` and `COMMITS.tsv`. The delivery extract itself
    was removed; it is reproducible from exchange `5857e850e`.
  - `tools/`: `manifest_check.py`, `frozen_check.py`, `frozen_controls.py`, `widths.py`, `closure.py`, `downstream.py`,
    `unfold_scan.py`, `sealprobe_check.py`, `logcount.py`, and the maintainer's `decls2.py`.
- **Phase 2:**
  - `order/`, `plan/`, `state/` (keys at `eff2dcd0` and after the build).
  - `tree/`: `snapshot-pre.txt`, `backed-up.txt`, `new-oleans.txt`, `snapshot-post.txt`.
  - `build/`: `results.jsonl`, 650 logs, `per-module.tsv`, `buildsum.txt`, `statecheck.txt`, `refunion*`, `logcheck.txt`.
  - `build-mathlib-extra/`, `records/`, `tree-final/`, `admissions/`, `refs/` (the reference records).
  - Probes: `probe-runs-1/` (axioms and trace, collector), `p2/probes/`.
  - Seals: `seals{,-coe}/{A,B}/` (records and probe sources) and `seal-runs/`.
  - Controls: `controls-{coe,strict}-{A,B}/` and `control-runs-*/`, with `probes/` holding orders, error counts and probe
    sources.
  - Restore: `restore/`.
  - `tools-used/` (unmodified copies of the int-x tools, plus `fullorder.py` and `restore_gsws.sh`) and `rule10-tools/` (the
    seal and control harness, plus `mkctl_gsws.py`, `mkseals_*_gsws.py`, `sealtab.py`).
  - The finish scripts: `run-build.sh`, `finish-post-build.sh`, `finish-probes.sh`, `finish-restore.sh`.

**Not yet clear to merge — GS-01 awaits Seyoon's ruling; then a landing branch and PR for his approval.**

## ===== inbox/fills/gsw-core/REPORT.md =====

# Fill `gsw-core` — final (F1 Gadget, F2 Noise, F3 Scheme, F7 Symmetric, F4 Eval)

**Result: all 29 targets proved**, standard axioms only (`propext`, `Classical.choice`,
`Quot.sound`); no target reaches `sorryAx`. No statement weakened, no hypothesis or definition
changed, no frozen file touched, no scope request.

**Worker** Claude, a lead with two sub-agents (A, B). **Issue base**
`486f44f8414c20a2d21e452c44de8b8c8d8513a0` (head of draft PR #333, `stmt/gsw`), verified to contain
#332's `94eae71b779c4ca0f76c138d699f4d737dbd6cee` (`git merge-base --is-ancestor`). The pack was read
at exchange commit `523d4e97302606b0301ecbcff13882abb917ec1f`; `shasum -a 256 -c SHA256SUMS` in
`outbox/fills/gsw-core/` reported all 7 files OK. Local branch `fill/gsw-core` (never pushed), final
head `d4ebb0be088e5985337ccb4e0a61cb3a662e8b73`. Lean 4.25.0; Mathlib and packages at the base's
`lake-manifest.json`. Checkpoint 1 was delivered as exchange commit `5b72e346b`.

## Status of the 29 targets

| Unit | File | Targets | Status | Prover |
|---|---|---|---|---|
| F1 | `Gadget.lean` | `digits_decomposeVec`, `gadget_mulVec_decomposeVec`, `gadget_mul_decompose`, `decomposeVec_block_eq_false`, `errorSum_decomposeVec_le` | proved | sub-agent A |
| F2 | `Noise.lean` | `encrypts_gadget`, `encrypts_zero`, `Encrypts.mono`, `.add`, `.neg`, `.sub`, `.sum`, `.mul`, `.mul_bit`, `.mul_le`, `.nand`, `encrypts_chain` | proved | sub-agent A |
| F3 | `Scheme.lean` | `vecMul_secretVector_augmented`, `encrypts_encrypt`, `encrypts_keygen_encrypt`, `decrypt_of_encrypts`, `decrypt_of_encrypts_dyadic`, `decrypt_keygen_encrypt` | proved | sub-agent B |
| F7 | `Symmetric.lean` | `encrypts_symEncrypt`, `distAdv_symEncrypt_le` | proved | sub-agent B |
| F4 | `Eval.lean` | `homAnd_encrypts`, `homGate_encrypts`, `eval_encrypts`, `decrypt_keygen_eval` | proved | lead |

Admissions: 35 at the base → **6**, exactly the `gsw-security` ones (`Hashing/SIS/Columns`:
`hashColumns_eq_mul`, `distAdv_hashColumns_uniform_le`; `GSW/Security`: `real_uniformKey_advantage`,
`uniformKey_uniform_advantage_le`, `distAdv_encrypt_le`, `distAdv_encrypt_le_of_width`). Removed: the
29 targets; added: none (`evidence/sorries/final.txt`).

## Commits (`patches/`, `patches/COMMITS.tsv`)

1. `243a44cdb` — F1, F2 (Gadget.lean, Noise.lean; sub-agent A's files, integrated by the lead).
2. `a1bc6aacd` — F4 (Eval.lean; lead). At this commit `decrypt_keygen_eval` was proved modulo F3.
3. `d4ebb0be0` — F3, F7 (Scheme.lean, Symmetric.lean; sub-agent B's files, integrated by the lead).

Every commit was made with `git -c commit.gpgsign=false` and none is signed (`signing` = `none`).
**Reproduction checked before the push:** a scratch clone at the base applies the series with
`git am` under the recorded committer identity and date, reproduces all three hashes, and its files
equal `src/` (`evidence/logs/patch-reproduction.log`).

## Changed files

| File | Lines base → final | Edits |
|---|---|---|
| `TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Gadget.lean` | 204 → 236 | 5 bodies; sketches rewritten for `gadget_mulVec_decomposeVec`, `gadget_mul_decompose`, `decomposeVec_block_eq_false` (last sentence), `errorSum_decomposeVec_le` |
| `…/GSW/Noise.lean` | 235 → 321 | 12 bodies; sketches rewritten for `encrypts_gadget`, `encrypts_zero`, `.add`, `.neg`, `.mul`, `.mul_bit`, `.mul_le`, `.nand`, `encrypts_chain` |
| `…/GSW/Scheme.lean` | 215 → 364 | 6 bodies; 2 private helpers; sketches rewritten for the first five targets (`decrypt_keygen_encrypt`'s already matched) |
| `…/GSW/Symmetric.lean` | 111 → 185 | 2 bodies; 1 private helper; both sketches rewritten |
| `…/GSW/Eval.lean` | 209 → 321 | 4 bodies; `homGate_encrypts` sketch rewritten (the other three already described the delivered proofs) |

Statement prose before every sketch, every header, definition, reader, `variable`, `section`, `open`,
`set_option` line, import and module docstring is byte-identical (`evidence/headers/final/`). No
import was added, so no new Mathlib root and no extra cache fetch. Every proof of 15 lines or more
has a sketch and step comments.

## New declarations

All three are `private` glue with a docstring and no source tag. None is public, so `## Main
results` is unchanged and lint check 8 is not engaged.

- `Scheme.lean:201` `halfVector_eq_zero_of_ne_last (P) (j) (hj : j ≠ Fin.last _) : halfVector P j = 0`.
- `Scheme.lean:213` `decrypt_eq_decode_errorSum`: from `Encrypts P (secretVector P s) b.toNat β C`,
  there is a `β`-bounded `e` with `decrypt P s C = decode (codepoint b + ↑(∑ i, e i *
  (decomposeVec P (halfVector P) i).toNat))`. It is shared by `decrypt_of_encrypts` and `_dyadic`.
- `Symmetric.lean:110` `exists_equiv_symEncrypt (P hN μ)`: there is
  `E : (A, b) ≃ (Fin k → Ciphertext P)` with `E c = symEncrypt P hN c μ`.

Name-clash scan: none of these names is declared anywhere in `TCSlib/` at the base
(`evidence/clash/final.txt`).

## Routes (as delivered; Gate 41's routes worked as written)

- **F1.** `digits_eq`, `decomposeVec_eq`, `Equiv.apply_symm_apply`. `gadget_mulVec_decomposeVec`
  casts `Lossy.gadget_mulVec` through `Int.cast_sum`/`Int.cast_mul`. `errorSum_decomposeVec_le`
  reindexes through `finProdFinEquiv`, zeroes blocks `j ≠ j₀` with `decomposeVec_block_eq_false`,
  and applies `LWE.binaryErrorSum_bound` with `m := ℓ`.
- **F2.** `Encrypts.mul` keeps the exact `x₁.natAbs * β₂` term, with witness
  `j ↦ (∑ᵢ e₁ i · X i j) + x₁ · e₂ j`, using `Matrix.vecMul_vecMul`, `Matrix.add_vecMul`,
  `Matrix.smul_vecMul`, `gadget_mul_decompose`, `LWE.binaryErrorSum_bound` and `Int.natAbs_mul`.
  `encrypts_chain` inducts on the `Forall₂` with the head on the left.
- **F3.**
  - `vecMul_secretVector_augmented`: `Fin.sum_univ_castSucc`, `Fin.snoc_*`, `augmented_eq`,
    `noisyValues_apply`.
  - `encrypts_encrypt`: witness `j ↦ ∑ᵢ eᵢ·R i j` with bound `m·B`.
  - `decrypt_of_encrypts`: through `decrypt_eq_decode_errorSum`, then `errorSum_decomposeVec_le`
    at `j₀ = Fin.last _` and `decode_codepoint_add` with `B := ℓ·β`.
  - `_dyadic`: the decomposition of `⌊q/2⌋ e_last` is the indicator of `(last, ℓ−1)`
    (`Lossy.digits_injective`, `digits_decomposeVec`, `Lossy.digits_val`), so the error sum is
    `e i₀`.
- **F7.**
  - `encrypts_symEncrypt`: `Matrix.submatrix_apply` and `vecMul_secretVector_augmented`.
  - `distAdv_symEncrypt_le`: `acceptProb_def` on the real side. On the ideal side,
    `acceptProb_comp_equiv` with `exists_equiv_symEncrypt` (`Equiv.ofBijective` of
    `Regev.augmented_bijective`, column reindexing by `rowEquiv`, then `Equiv.addRight` by
    `μG`). The bound follows from `LWE.decisionAdvantage_eq`, `distAdv_def` and `abs_sub_le`.
- **F4.**
  - `homAnd_encrypts`: induction on the `Forall₂`, following `homAnd`'s three equations.
  - `homGate_encrypts`: `List.forall₂_map_*_iff`, `List.forall₂_same`, `List.all_map` and the
    `length ≤ 2` bound. `¬` is `G − ·`; `∨` is De Morgan via `List.any_eq_not_all_not`.
  - `eval_encrypts`: `runWith_rel` with
    `R v b C := Encrypts P t b.toNat ((N+1)^{Cc.depthAt v}·β) C`, using `depthAt_input`,
    `depthAt_gate`, `depthAt_eq`, `DAGGate.depth_eq`, `DAGGate.getD_lt_depth`, `.mono` and
    `homGate_encrypts`. The output is read with `Cc.eval_eq`, `values_eq`, `depth_eq`,
    `eval_eq` and `evalValues_eq`. `IsFaninTwo` is not used and no reader was added.
  - `decrypt_keygen_eval`: `encrypts_keygen_encrypt`, `eval_encrypts`, then `.mono` with
    `Nat.pow_le_pow_right`, then `decrypt_of_encrypts` with `hsep` verbatim. No extra factor,
    no `L+1`.

## Overlap and reuse

The new declarations and the inline `have`s that restate, specialize or re-prove existing material:

1. **`decrypt_eq_decode_errorSum`** (private, Scheme).
   - Nearest relative: `Regev.encrypt_residual`
     (`TCSlib/Cryptography/Encryption/PublicKey/Regev/Basic.lean:105`), which has the same
     shape, "residual = codepoint + integer error sum".
   - Not reusable: the GSW decryption column is not a `Regev.encrypt` output. Its residual
     comes from the GSW invariant and `G·G⁻¹(w) = w`.
   - `decode_codepoint_add`, `errorSum_decomposeVec_le` and `gadget_mulVec_decomposeVec` are
     reused.
2. **`exists_equiv_symEncrypt`** (private, Symmetric). Its relatives are inline `let`s inside
   other proofs, so they cannot be reused:
   - the translation equivalence in `Symmetric.Regev.acceptProb_uniform_shift`
     (`TCSlib/Cryptography/Encryption/Symmetric/Regev/Experiments.lean:77`);
   - `keyEquiv := Equiv.ofBijective (augmented P) …`
     (`TCSlib/Cryptography/Encryption/PublicKey/Regev/Experiments.lean:260`).

   It composes the published `Regev.augmented_bijective`, a block reindexing through `rowEquiv`
   (no relative found; Mathlib's `Matrix.reindex` and `Equiv.curry` do not give the `Fin k`-block
   shape) and Mathlib's `Equiv.addRight`.
3. **`halfVector_eq_zero_of_ne_last`** (private, Scheme): no relative (searched `halfVector`).
4. **Inline `hX`** in `Encrypts.mul` states that `e₁ᵗ · lift X` is the residue of the integer
   binary sum. The inline **`herr`** in `decrypt_eq_decode_errorSum` and the last step of
   `encrypts_encrypt` repeat the same cast pattern.
   - Relatives: the inline `herr` of `Regev.encrypt_residual` (`Regev/Basic.lean:119`) and the last
     step of `Lossy.residual_conceal` (`TCSlib/Cryptography/TrapdoorFunctions/Lossy/Matrix.lean:128`).
   - These are 2–3 lines of `Int.cast_sum`/`Int.cast_mul`/`Int.cast_natCast` glue. No stated
     lemma exists to reuse.
5. **Bool-message identities.** `((a && c).toNat : ℤ) = a.toNat * c.toNat` and
   `((!c).toNat : ℤ) = 1 − c.toNat` are proved inline by `cases … <;> rfl`:
   - in Noise: `Encrypts.mul_le`, `.nand`, `encrypts_chain`;
   - in Eval: `homAnd_encrypts`, `homGate_encrypts`;
   - in Scheme: `hb` in `decrypt_eq_decode_errorSum` is the codepoint analogue.

   No core, Mathlib or batteries lemma states them over `ℤ`. A shared public lemma would change
   Noise's interface, so they are kept inline (disclosed).
6. **Inline `hs`** in `encrypts_keygen_encrypt` (`Prod.ext (sample_fst) (sample_snd)`) repeats the
   inline `hsample` of `Regev.decrypt_keygen_encrypt` (`Regev/Basic.lean:168`). It is two lines,
   and that relative is not exported.
7. **Inline `hz`/`hsum`** in `decrypt_of_encrypts_dyadic` (the indicator decomposition): no
   existing statement. It is proved from `Lossy.digits_injective`, `Lossy.digits_val`,
   `digits_decomposeVec`, `digit_val` and Mathlib's `Fintype.sum_eq_single`.
8. **Inline `hlen`** in `homGate_encrypts`: arithmetic glue, no relative.
9. **Reused, not re-proved:**
   - `LWE.binaryErrorSum_bound` (`TCSlib/Cryptography/LWE/Basic.lean:79`; its specializations
     `Regev.subsetError_bound` and `Lossy.error_sum_bound` are not used);
   - `Lossy.gadget_mulVec`, `digits_val`, `digits_eq`, `digits_injective`;
   - `Regev.augmented_eq`, `augmented_bijective`, `decrypt_eq`, `keygen_fst`/`_snd`;
   - `LWE.sample_fst`/`_snd`, `noisyValues_apply`, `Noise.bounded_iff`, `decisionAdvantage_eq`;
   - `BitEncoding.codepoint_eq`, `decode_codepoint_add`;
   - `acceptProb_def`, `distAdv_def`, `acceptProb_comp_equiv`;
   - `runWith_rel`, `DAGGate.getD_lt_depth`, `depthAt_input`, `depthAt_gate`, `depthAt_eq`;
   - Mathlib's `List.getD_eq_getElem`/`List.getElem_ofFn` for `getD` of `List.ofFn` (no new
     copy of the DL-47 family).

Searches (details in `evidence/subagents/{A,B}/REPORT.md`):
- `grep -rn` over `TCSlib/` for `Int.cast_sum`, `error_sum_bound|subsetError_bound`, `toNat`,
  `halfVector`, `exists_equiv`, `decode_errorSum`, `sample_eq`, `ofBijective`, `encrypt_residual`,
  `digits_injective`, `blocksEquiv`, `runWith_rel|runWith_sim|runWith_remap_rel` and
  `getD_eq_getElem|getElem_ofFn`;
- core, Mathlib and batteries for `toNat_and|toNat_not|toNat_mul`;
- `#check` probes for every Mathlib name used (`evidence/lead/probes/LeadNames.lean`,
  `evidence/subagents/A/probes/NamesA.lean`, `evidence/subagents/B/probes/B_names1.lean`).

## Scope requests and promotion requests

None. The two inline Bool identities (item 5) could become a small public helper if the maintainer
wants one; no promotion is requested.

## Who proved what

- **Sub-agent A** (worktree `/home/user/gsw-A`, own TCSlib olean tree) proved F1 and F2, 17
  targets. Its evidence is in `evidence/subagents/A/`. The harness refused a sub-agent-written
  `.md` report there, so the lead saved A's returned report as `REPORT.md`.
- **Sub-agent B** (worktree `/home/user/gsw-B`, own TCSlib olean tree) proved F3 and F7, 8 targets,
  with the three private helpers. Its evidence is in `evidence/subagents/B/`. B's `scheme-004.log`
  is a stale run: a patch command of B's hung on stdin for about 30 minutes before writing, which
  B disclosed in its WORKLOG. `scheme-005` had 2 errors, fixed in `scheme-006`.
- **The lead** proved F4 (4 targets). It also integrated each sub-agent's files unchanged (SHA-256
  checked against their `final/` copies and reports), made every commit, ran all final checks and
  delivered.
- All Lean runs, by the lead and both sub-agents, went one at a time through one `flock` on
  `/home/user/gsw/.lean.lock` (`evidence/tools/runlean.py`, `chk.sh`, `seal.py`). Only the lead ran
  `lake`. There was no `lake build` and no unfiltered cache fetch. The sub-agent rules are in
  `evidence/tools/SUBAGENT-RULES.md`.

## Environment (addendum Part 1)

- **Preflight** (`evidence/logs/preflight.log`):
  - `nproc` 4;
  - cgroup v1, limit 14,338,772,992 B;
  - memory in use (usage − total_cache + total_shmem) 470,822,912 B, so the **headroom is
    12.92 GiB**;
  - the clone is on ext4 (`/dev/vda`) with **15.65 GiB free**; no tmpfs is used.
  - Re-check before the cache fetch (after the elan toolchain install): 13.2 GiB free.
- **Cache store** (`evidence/logs/cache-store.log`): `/root/.cache/mathlib` was absent before the
  fetch, so 0 archives were pre-existing.
- **Narrowed fetch** for the **38** roots. These were recomputed from `order.txt` and are identical
  to `roots.txt` (`evidence/logs/mathlib-roots.txt`). The log shows "Attempting to download 2060",
  "Decompressing 2060" and "Completed successfully" (`evidence/logs/cache-get.log`).
- **Packages** (`evidence/logs/packages-check.log`), last line: "RESULT: PASS: present packages
  match the manifest; absent: «doc-gen4», UnicodeBasic, BibtexQuery, MD4Lean".
  - Zero-size oleans: 0.
  - The root probe elaborated (`evidence/logs/cache-probe.log`).
- **Bootstrap**: the whole `order.txt` (31 modules), in order, with 0 errors, before any check
  (`evidence/logs/bootstrap.log`, `evidence/logs/bootstrap/`).
  - `/usr/bin/time` is absent on this host, so peak RSS comes from `getrusage` in `runlean.py`.
  - The highest recorded was 3,141,504 KiB (about 3.0 GiB, the lead's Mathlib name probe); the
    library modules stayed at or below about 2.6 GiB. No shortage and no OOM occurred.
- **Base runs**: a detached worktree `/home/user/gsw-base` (own TCSlib olean tree, with Eval and
  the facades re-checked at the base) ran the base seals and the base lint.

## Final checks (`evidence/`)

| Check | Result | Evidence |
|---|---|---|
| Owned modules | 5/5 exit 0, 0 errors (both forms), 0 sorry warnings | `logs/final/modules/`, `logs/final/modules.txt` |
| Sweep of `order.txt` | 31/31 exit 0, 0 errors | `logs/final/sweep/`, `logs/final/sweep.txt` |
| Admissions | 35 → 6; removed exactly the 29 targets; added 0 | `sorries/final.txt` |
| Axioms + dependency trace | 114 stored constants of the five modules (targets, helpers, readers, definitions, auxiliary); every one uses only `propext`, `Classical.choice`, `Quot.sound`; **0 reach `sorryAx`**; the trace lists no sorried constant | `axioms/final/` |
| Frozen statements | 0 unexpected differences; controls PASS in all 5 files (one-character header change → exactly 1 difference; deleted reader → exactly 1 removal) | `headers/final/` |
| Width / size | max width ≤ 100 (Python `len`), all files ≤ 364 lines, no `µ` | `width/final.txt` |
| Name clash | 0 clashes (3 new private names) | `clash/final.txt` |
| Explicit-unfold scan | Every `simp`/`rw`/`dsimp`/`unfold` selector token resolved by Lean. 0 foreign TCSlib definitions, **and 0 core/Mathlib definitions** | `unfold/final/` |
| Seals at base | 5 files × A/B × strict/coe, `-DmaxErrors=0`: 20/20 exit 0, 0 errors, harness valid | `seals/base/` |
| Seals at final | the same 20: 20/20 exit 0, 0 errors, harness valid. **Canonical coe-A: 0 failing declarations.** Strict differs from coe only by one extra sealed instance (FinDist's projection coercion), with no error difference; B = A | `seals/final/` |
| Paired controls | unsealed 0 errors; 6 POS pass in all four seals; 8 NEG (`gadget`, `mul`, `Encrypts`, `Regev.augmented`, `LWE.sample`, `Lossy.gadget`, `Randomized.blocksEquiv`, `BitEncoding.codepoint`) fail **exactly once** in each variant; COE passes coe, fails once strict. **ALL_OK** | `seals/controls-final/` |
| Lint `--check8b` | base 92 FAIL / 101 WARN / 364 files; final identical line sets (0 new, 0 removed) | `lint/lint-base.log`, `lint/lint-final.log`, `lint/diff-final.txt` |

**Seal notes.**
- Seals A and B install the same set: `Complexity.PolyExpr` is outside the import closure of every
  owned file and of the control probe, so there is no `PolyExpr.eval` control.
- Errors are counted with `^\S+\.lean:\d+:\d+: error[:(]` (both forms) in every seal, control,
  sweep and probe log.
- The harness (`evidence/tools/seal.py`, `seal_install.lean.txt`) copies verbatim the install block
  of the derand fill's harness (exchange `inbox/fills/derand/evidence/verification/tools/
  make_seals.py`, after Gate 10's), changing only its log prefix.
- The type-level Rule 10 seal covers `Regev.augmented`, `LWE.sample`, `Lossy.gadget`,
  `Randomized.blocksEquiv` and `BitEncoding.codepoint`; each is sealed and has a NEG control.

**Rule 10 reading.**
- Each file reads its own definitions directly and other files' definitions only through their
  readers.
- Mathlib definitions (`vecMul`, `mulVec`, `dotProduct`, `submatrix`, `Fin.init`, `Bool.toNat`)
  are reached only by `change` or `cases … <;> rfl`, or through their lemmas. They are never named
  in a selector.

**Tool corrections at checkpoint 1** (disclosed then, kept here). The first `ctlcheck.py` keyed
controls by name only, and the first `axioms_report.py` missed the summary line. Both were fixed and
re-run on the same raw logs; the first outputs are in `logs/cp1/evidence-run.out`. The final run
used the fixed tools throughout (`logs/final/evidence-run.out`).

## Evidence manifest

- `evidence/SHA256SUMS` lists every file under `evidence/` except itself.
- The top-level `SHA256SUMS` lists every delivered file under `inbox/fills/gsw-core/` except itself.
- The delivered paths equal the manifest's exactly: nothing missing, nothing extra, no leading `./`.
- The lead's development logs are in `evidence/lead/`, the checkpoint-1 checks in `*/cp1/`, the
  sub-agents' material in `evidence/subagents/`, and every tool used in `evidence/tools/`.

## ===== inbox/fills/gsw-security/REPORT.md =====

# Fill `gsw-security` — final (F5 column leftover hashing, F6 IND-CPA of public-key GSW)

**Worker:** Claude (single agent; external Claude route: deliveries pushed to `exchange/pass-shelat-ch5-8`,
path `inbox/fills/gsw-security/` only). **Issue base:** `486f44f8414c20a2d21e452c44de8b8c8d8513a0` (head of
draft PR #333, `stmt/gsw`; contains #332's `94eae71b779c4ca0f76c138d699f4d737dbd6cee` as `486f44f8~3`).
Local proof branch `fill/gsw-security`, never pushed; its head is `a9f97eddb42c7dfc0422fa8c9ce998c658bfa4f8`.
**Lean** 4.25.0; Mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e` (the base's `lake-manifest.json`).
**Inputs read:** exchange `README.md`, `outbox/fills/gsw-security/{README.md, brief.md,
fill-environment-addendum.md}` at exchange commit `523d4e97302606b0301ecbcff13882abb917ec1f`, the pack
verified with `shasum -a 256 -c SHA256SUMS` (7 × OK); `policy.md` at the base; the Gate 41 excerpts were not
needed (no new citation tag was written).

**Deliveries.** Checkpoint 1 (F5) was pushed as exchange commit `b08456186` (`fill gsw-security: checkpoint 1`);
its report is kept verbatim as `evidence/checkpoint1/REPORT-checkpoint1.md` with its evidence under
`evidence/checkpoint1/`, `evidence/seals/cp1*`, `evidence/controls/cp1`, `evidence/axioms/cp1`. This is the final
delivery; it supersedes the checkpoint's `REPORT.md`, `patches/`, `src/` and manifests.

## Status of the targets

All six targets are proved; no statement was weakened, no hypothesis added, no definition changed.

| Unit | Target | Status | Proof |
|---|---|---|---|
| F5 | `Hashing.SIS.hashColumns_eq_mul` | **proved** (checkpoint 1) | entrywise `hashColumns_apply`, `hash_eq`, `Matrix.mul_apply'`, `rfl` |
| F5 | `Hashing.SIS.distAdv_hashColumns_uniform_le` | **proved** (checkpoint 1) | column hybrid over `distAdv_hash_uniform_le` (below) |
| F6 | `GSW.real_uniformKey_advantage` | **proved** | exact equality via `acceptProb_bind` |
| F6 | `GSW.uniformKey_uniform_advantage_le` | **proved** | relabellings + `distAdv_hashColumns_uniform_le` |
| F6 | `GSW.distAdv_encrypt_le` | **proved** | triangle inequality over the four hybrids |
| F6 | `GSW.distAdv_encrypt_le_of_width` | **proved** | `distAdv_encrypt_le` + `Regev.two_extractionError_le` |

Admissions: base 53 declarations in 15 modules → **47 in 13** (`evidence/final/admissions.txt`, PASS: removed
exactly the 6 targets, nothing added). Checkpoint 1 removed the 2 F5 targets (53 → 51 in 14).

**`gsw-core` targets:** none cited. The dependency trace of every target reaches no sorried constant, so no
`gsw-core` target (`encrypts_*`, `vecMul_secretVector_augmented`, …) is in any proof's closure. Only `gsw-core`'s
`rfl` readers `encrypt_eq`, `lift_apply` (and the definitions `gadget`, `Parameters.columns`, `Ciphertext` as
terms/notation) are used.

## Changed files

| File | Lines at base | Lines at final | Change |
|---|---|---|---|
| `TCSlib/Cryptography/Hashing/SIS/Columns.lean` | 89 | 194 | 2 `sorry` bodies replaced; both `**Proof sketch.**` paragraphs rewritten; import `Pseudorandom.Indistinguishability` added |
| `TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Security.lean` | 217 | 305 | 4 `sorry` bodies replaced; the 4 `**Proof sketch.**` paragraphs rewritten; import `Pseudorandom.Indistinguishability` added |

- **Imports:** only `TCSlib.Cryptography.Pseudorandom.Indistinguishability` (authorized, in `order.txt`), in
  both files (`acceptProb_bind`, `acceptProb_update`, `acceptProb_fst`). No Mathlib import, so no new cache root.
  `Columns.lean` imports nothing under `AdvancedEncryption/`. No helper module.
- **Sketch edits** (statement prose before each `**Proof sketch.**` byte-identical, checked):
  `hashColumns_eq_mul` (names its three equations); `distAdv_hashColumns_uniform_le` (hybrids `H_k`, the planting
  test, the end hybrids, telescoping); `real_uniformKey_advantage` (the reassociation is now `acceptProb_bind`, with
  `reduction_eq`, `realView_eq`, `uniformKeyView_eq`); `uniformKey_uniform_advantage_le` (adds `lift_apply`,
  `Equiv.addRight` and "the test that undoes both relabellings"); `distAdv_encrypt_le` (names `abs_sub_le` ×3 and
  `linarith`); `distAdv_encrypt_le_of_width` (names `mul_le_mul_of_nonneg_left`).
- **New declarations:** none, public or private. All auxiliary objects are local `let`s/`have`s, as the brief
  prefers; `## Main results` is unchanged.

## The delivered proofs

**F5 `distAdv_hashColumns_uniform_le`.** Seeds of hybrid `H_k`: `(A, (x, u))`, `x : Fin N → {0,1}^columns`,
`u : Fin N → Z_q^dimension`; column `j` is `u j` for `j < k`, else `hash A (x j)`, all under the same `A`. The
`k`-th test plants its challenge at column `k`, simulates the other columns from coins `(x, u)` carried beside
`D`'s coins (type `((Fin N → In) × (Fin N → Out)) × ρ`, finite, nonempty), and runs `D`.
1. `hleft`: on `(A, hash A r)` the test accepts as `D` on `H_k` — `acceptProb_bind`, a seed relabelling
   (`acceptProb_comp_equiv`), `acceptProb_update` on `x` at `k`; cases `j = k` / `j ≠ k`.
2. `hright`: on uniform `(A, y)` it accepts as `D` on `H_{k+1}` — the same with the update on `u`; cases
   `j < k`, `j = k`, `j > k`.
3. `hzero`/`hfull`: `H_0` is the real sampler, `H_N` the ideal one, after transposing seeds and dropping the
   unused half (`acceptProb_comp_equiv`, `acceptProb_fst`, `hashColumns_apply`).
4. `abs_sub_le_sum_hybrids` over `range N`; each gap is `distAdv (A, hash A r) (A, y) (test k)` ≤ the
   single-column error by `distAdv_hash_uniform_le` (Gate 41: valid because the test receives `A`); `N` equal
   terms give `N · ε`. `N = 0` is the empty sum. No universality claim for `R ↦ A R`; no SIS hardness.

**F6.** Write `ε = Regev.extractionError P.lwe = ½·√(q^{n+1}/2^m)`.
- `real_uniformKey_advantage`: `reduction P μ D = fun pk c => D (view P μ pk c.1) c.2` (`reduction_eq`), so
  `acceptProb_bind` turns its acceptance on `LWE.sample P.lwe χ` (resp. the identity on keys) into `D`'s
  acceptance on `fun s => view P μ (LWE.sample … s.1) s.2` = `realView P χ μ` (resp. `uniformKeyView P μ`), read
  by `realView_eq`/`uniformKeyView_eq`; then `LWE.decisionAdvantage_eq`, `distAdv_def`. Exact equality; the
  reduction's coins are `R` paired with `D`'s coins.
- `uniformKey_uniform_advantage_le`: `keyEquiv := Equiv.ofBijective (Regev.augmented P.lwe)
  (Regev.augmented_bijective P.lwe)` (keeps the whole key), `unpack := keyEquiv.symm × (· + μG)`. The ciphertext
  `Ā·lift R + μG` equals `hashColumns (columnHashParameters P) N Ā R + μG` (`encrypt_eq`, `hashColumns_eq_mul`,
  `lift_apply`; `columnHashParameters` read directly, its own file). Relabelling both samplers
  (`acceptProb_comp_equiv`) makes the gap that of `(Ā, ĀR)` vs `(Ā, U)` for `test := D ∘ unpack`;
  `distAdv_hashColumns_uniform_le (columnHashParameters P) N test` and the `columnHashParameters_{modulus,
  dimension, columns}` readers with `Regev.extractionError_eq` give `N · ε`. `Regev.hashParameters` is never
  unfolded or used.
- `distAdv_encrypt_le`: the chain real `μ₀` → uniform-key `μ₀` → uniform → uniform-key `μ₁` → real `μ₁`;
  `abs_sub_le` three times, the two exact DLWE terms and two `N · ε` terms, `linarith`.
- `distAdv_encrypt_le_of_width`: `2·(N·ε) = N·(2ε) ≤ N·2^{−κ}` by `Regev.two_extractionError_le P.lwe w κ hq hm`
  and `mul_le_mul_of_nonneg_left` (`N ≥ 0`), then `linarith`. Only the concrete fixed-bit function-level
  statements (ruling Q8): nothing about efficiency, `NUPPT` or SIS hardness; no small-secret/normal-form
  assumption (one common uniform secret, `m` rows, as `LWE.sample`).

## Overlap and reuse

No new declaration (public or private). The inline `have`s re-prove instances of existing material; each is
disclosed with its nearest relative at the base `486f44f8`.

### F5 (`Hashing/SIS/Columns.lean`)

| Inline step | Nearest relative | Relation | Why not reused |
|---|---|---|---|
| the whole column hybrid of `distAdv_hashColumns_uniform_le` (steps 1–4) | `TCSlib/Cryptography/Encryption/PublicKey/Hybrid.lean:88` `distAdv_tuple_le_sum` | **same argument**: a hybrid over `q+1` positions sharing one public parameter, a planting distinguisher per position, `abs_sub_le_sum_hybrids` | not importable under the brief: the module is not in `order.txt`, so an import needs a scope request; it imports `Asymptotic.BlockEncryptor` (NUPPT/Turing-machine layer) into the SIS hash layer, against policy §1 layering; its interface needs one seed type for both sides and `N = q+1`, so the adaptation (sum-type seeds, `N = 0`, matrix ↔ tuple relabellings) would be as long as the hybrid. Promotion P-1 below. |
| `hleft`, `hright` (planting one column) | `…/Encryption/PublicKey/Hybrid.lean:52` **private** `acceptProb_plant`; `TCSlib/Cryptography/Pseudorandom/Indistinguishability.lean:247,266` `acceptProb_multicopyRed_left`/`_right`; `TCSlib/Cryptography/TrapdoorFunctions/Lossy/Experiments.lean:138` `column_gap` | specialization of the planting identity to a shared public matrix | `acceptProb_plant` is private: not copied, re-derived from the public `acceptProb_bind`, `acceptProb_comp_equiv`, `acceptProb_update`; the multicopy lemmas have no shared key; `column_gap` is LWE-specific (pattern only, per the brief) |
| `hzero`, `hfull` (end hybrids) | `Indistinguishability.lean:225,234` `acceptProb_multicopyHybrid_zero`/`_self` | same shape (an end hybrid ignores half the seed) | stated for `multicopyHybrid`; here by the public `acceptProb_fst`, `acceptProb_comp_equiv` |
| telescoping + per-gap bound | `TCSlib/Cryptography/Foundations/Probability.lean:218` `abs_sub_le_sum_hybrids`; `TCSlib/Cryptography/Hashing/SIS/Universality.lean:166` `distAdv_hash_uniform_le` | **reused** | — |
| `hashColumns_eq_mul` | Mathlib `Matrix.mul_apply'` (`Mathlib/Data/Matrix/Mul.lean:299`) | **reused** with `hash_eq` | — |

`TCSlib/Cryptography/OneWayFunctions/Basic.lean:131` `OneWay.uprob_update` (used by `column_gap` and
`acceptProb_plant`) was not used: not an authorized import; the authorized `acceptProb_update` covers the need.

### F6 (`GSW/Security.lean`)

Gate 41 accepted the four F6 statements as GSW restatements of the Regev PKE hybrids (not duplicates); the
proofs follow those hybrids, as the brief asks.

| Inline step | Nearest relative | Relation | Why not reused |
|---|---|---|---|
| `real_uniformKey_advantage` (whole proof) | `TCSlib/Cryptography/Encryption/PublicKey/Regev/Experiments.lean:128` `Regev.real_uniformKey_advantage`; `Indistinguishability.lean:131` `distAdv_sunglassRed` | same argument for GSW's ciphertext space; `reduction P μ D` is definitionally `sunglassRed (view P μ) D` | Regev's lemma is about Regev's `view`/ciphertext type; `distAdv_sunglassRed` would require reading the foreign `sunglassRed`/`pushSampler`, which have no published readers (Rule 10). Instead the public `acceptProb_bind` (the lemma underneath `distAdv_sunglassRed`) is **reused** with the own readers. |
| `uniformKey_uniform_advantage_le` (relabellings) | `Regev/Experiments.lean:244` `Regev.uniformKey_uniform_advantage_le` | same relabelling (augmented key, ciphertext translation) | Regev's ciphertext is a vector with Regev's codepoint and single-column hash; GSW's is an `(n+1) × N` matrix bounded by the column hybrid. Reused from Regev: `augmented_bijective`, `extractionError_eq` (and `encrypt_eq`, `lift_apply` from `gsw-core`). |
| `distAdv_encrypt_le` (triangle) | `Regev/Experiments.lean:301` `Regev.distAdv_encrypt_le` | same three `abs_sub_le` steps | different view types; a 4-step chain is shorter inline than through `abs_sub_le_sum_hybrids` with a `Fin 5`-indexed function. No generic `distAdv` triangle lemma exists at the base (searched `distAdv_triangle`, `abs_chain_le`, `distAdv_le_add`, `distAdv_trans`: 0 hits). |
| `distAdv_encrypt_le_of_width` | `Regev/Experiments.lean:334` `Regev.two_extractionError_le` | **reused** | — |
| `columnHashParameters` | `Regev/Experiments.lean:154` `Regev.hashParameters` | the disclosed Q11 twin (frozen definition, not introduced here) | used only through its own `simps` readers; `Regev.hashParameters` never unfolded |

**Searches run** (raw output in `evidence/overlap/`): `searches-tcslib.txt` (F5: `hashColumns`, `columnHybrid`,
`columnTest`, `column_gap`, `multicopy`, `abs_sub_le_sum_hybrids`, `exists_hybrid_gap`, `acceptProb_update`,
`uprob_update`, `acceptProb_bind`, `acceptProb_comp_equiv`, `acceptProb_fst`, `acceptProb_snd`,
`distAdv_hash_uniform_le`, `theorem distAdv_*_le`, `theorem uprob_*`, `theorem acceptProb_*`, `theorem uexp_*`,
`Function.update`, `hybrid`, `transpose…Equiv|piComm`, `mul_apply'`); `searches-tcslib-f6.txt` (F6:
`real_uniformKey_advantage`, `uniformKey_uniform_advantage_le`, `distAdv_encrypt_le`, `two_extractionError_le`,
`extractionError`, `augmented_bijective`, `hashParameters`, `columnHashParameters`, `acceptProb_bind`,
`sunglassRed|distAdv_comp`, `abs_sub_le`, `reduction_eq`, `Equiv.addRight`, `Equiv.ofBijective`,
`mul_le_mul_of_nonneg_left`, `distAdv_triangle|abs_chain_le|distAdv_le_add|distAdv_trans`);
`searches-mathlib.txt` (Mathlib at the pin: `mul_apply'`, `mulVec_eq_sum`, `of_apply`, `piComm`,
`ofBijective_apply`, `symm_apply_apply`, `addRight`, `prodCongr`).

## Scope requests

**None.** No frozen file was edited and no import beyond the brief's list was added. Reusing
`distAdv_tuple_le_sum` would have needed one (an import outside `order.txt`); it was not requested (see above).

## Promotion requests

- **P-1 (dedup queue).** A generic shared-parameter hybrid in the probability layer (`Foundations/` or
  `Pseudorandom/Indistinguishability.lean`), for two samplers with *different* seed types
  (`X : κ × σ → γ`, `Y : κ × τ → γ`) over `N` positions including `N = 0`, would serve `distAdv_tuple_le_sum`,
  `Lossy.column_gap`/`concealed_advantage_le` and `distAdv_hashColumns_uniform_le` alike, and make
  `acceptProb_plant` public.
- **P-2 (readers).** `_eq` readers for `pushSampler` and `sunglassRed` (`Indistinguishability.lean:119,125`)
  would let consumers cite `distAdv_sunglassRed` under Rule 10 (here it would give
  `real_uniformKey_advantage` directly from `realView_eq`/`uniformKeyView_eq`).

## Rule 10

- **Reads.** `Columns.lean`: `hash` only through `hash_eq`; `distAdv`/`acceptProb` through `distAdv_def` and the
  published `acceptProb_*` lemmas; its own `hashColumns` through `hashColumns_apply`. `Security.lean`:
  `hashColumns` only through `hashColumns_eq_mul` (Columns is foreign to it); `encrypt` through `encrypt_eq`,
  `lift` through `lift_apply` (`gsw-core`'s readers); `Regev.augmented` only as a function inside
  `Equiv.ofBijective … (Regev.augmented_bijective …)`, never unfolded; `LWE.decisionAdvantage` through
  `decisionAdvantage_eq`; `Regev.extractionError` through `extractionError_eq`; `Regev.hashParameters` not
  used; its own `columnHashParameters` through its `simps` readers and, at the type level, directly (own file).
  Mathlib definitions reduce only in `rfl`/`exact`/`congrArg`/`Prod.ext` definitional steps (`Matrix.mulVec`,
  `Matrix.of`, `Equiv` coercions); none is passed to `simp`, `rw` or `unfold`.
- **Seals** (`evidence/seals/{final-base,final}/`, summary `evidence/final/rule10-summary.txt`): whole-file seals
  of both changed files over their full TCSlib import closures, at the base and at the final, A/B × strict/coe,
  each with `lean -DmaxErrors=0`; every probe harness-valid (one `GSWSEC-INSTALL`, one `GSWSEC-EOF`, all errors
  mapped). Harness adapted from the derand fill's `make_seals.py` (Gate 10 lineage).

  | File (sealed definitions strict / coe) | A strict | **A coe (canonical)** | B strict | B coe |
  |---|---|---|---|---|
  | `Columns.lean` at base (25 / 24) | 0 errors | **0** | 0 | 0 |
  | `Columns.lean` at final (32 / 31) | 0 | **0** | 0 | 0 |
  | `Security.lean` at base (115 / 114) | 0 | **0** | 0 | 0 |
  | `Security.lean` at final (115 / 114) | 0 | **0** | 0 | 0 |

  No failing declaration in any variant, so no difference to attribute. Strict seals exactly one more definition
  than coe: the projection coercion `FinDist.instCoeFunForallReal`. A and B coincide because
  `Complexity.PolyExpr.eval` is in neither file's closure. **Coverage** (`evidence/final/seal-coverage.txt`,
  PASS): in all four `Security` variants `Regev.augmented`, `LWE.sample`, the SIS `hash`, `hashColumns`,
  `encrypt`, `lift`, `gadget`, `Regev.hashParameters`, `Regev.extractionError`, `LWE.decisionAdvantage`,
  `distAdv` and `acceptProb` are sealed; `hash`, `distAdv`, `acceptProb` in all `Columns` variants.
  `Parameters.columns` and `Ciphertext` are reducible abbreviations (notation, never sealed).
- **Controls** (paired; positive = published reader, negative = `rfl` through the body; each negative alone in
  its file): checkpoint 1 with `Columns`' imports (`evidence/controls/cp1/`, 35 probes: `hash`, `distAdv`,
  `acceptProb`, `FinDist` coercion) and final with `Security`' imports (`evidence/controls/final/`, 55 probes:
  `hashColumns` (`hashColumns_apply`), `Regev.augmented` (`augmented_eq`), `LWE.sample` (`sample_fst`),
  `encrypt` (`encrypt_eq`), `distAdv` (`distAdv_def`), `FinDist` coercion). Both `ctlcheck` **ALL_OK**: positives
  pass unsealed and in every variant; every negative passes unsealed and fails **exactly once** in every variant
  that seals its definition (the coercion only in strict). A `PolyExpr.eval` control was prepared and dropped:
  its unsealed pre-check failed with `Unknown identifier` because `PolyExpr` is outside the closure
  (`evidence/logs/dev/precheck-Ctl_polyEval_neg.log`; `make_controls.py` records why).
- **Explicit-unfold scan** (`evidence/final/unfold/`, catalog from the final seal logs, 115 definitions): 90
  selector items in the owned files (base 0): 29 local or own, 61 lemmas, **0 foreign**. PASS.
- **Error counts, both forms (G26-N1)** (`evidence/final/error-counts.txt`, `evidence/checkpoint1/error-counts.txt`;
  regex `^\S+\.lean:\d+:\d+: error([:(])`): final sweep 147 logs, owned checks, all 16 final seals, the axioms
  probe: **0 `error:`, 0 `error(`**. Final controls: 22 `error:`, 0 `error(`, exactly the 22 expected sealed
  negatives (5 × 4 + 2); checkpoint controls 14, likewise expected. Development logs (`evidence/logs/dev/`):
  `columns-01` 1 `error:` (`No goals`), `security-02` 1 `error:` + **4 `error(`** (`lean.unknownIdentifier`:
  unqualified `hashColumns` names, fixed in `security-03`), the dropped pre-check 1 `error(`.

## Checks (final)

| Check | Result | Evidence |
|---|---|---|
| Owned modules, native check (after the last change) | `Columns` and `Security`: 0 errors, 0 `sorry`, no warning | `evidence/final/owned/` |
| Sweep of `order.txt` (147), one Lean process at a time | **ALL 147 OK**, 0 errors in both forms | `evidence/final/sweep.log`, `sweep/` |
| Admissions vs `base-sorries.txt` | 53 in 15 → **47 in 13**; removed exactly the 6 targets; added 0 → PASS | `evidence/final/admissions.txt` |
| Axioms: 6 targets (`#print axioms`) and all 32 stored constants of the two files | only `propext`, `Classical.choice`, `Quot.sound` → PASS | `evidence/final/axioms.log`, `axioms-check.txt`, probe `evidence/axioms/final/Axioms.lean` |
| Dependency trace (constant closure incl. theorem bodies; `sorryAx`) | **no sorried constant reached** from any target (2444–19231 constants visited); no `gsw-core` target reached | same |
| Frozen-statement check + controls | both files 0 differences, order ok (only the import additions, listed ADDED); controls: 1-character header change → exactly 1 difference, deleted reader → exactly 1 removal, in both files | `evidence/headers/` (`frozen_headers.py`, `run_headers.py`, `final/`, `checkpoint1/`) |
| Rule 10 | see above | `evidence/seals/`, `evidence/controls/`, `evidence/final/unfold/` |
| Lint `campaign_style_lint.py TCSlib/Cryptography --check8b` | base **92 FAIL / 101 WARN over 364 files** (= the maintainer's baseline); final identical; line-set diff: only the two owned files' INFO lines (sizes); no FAIL/WARN line for either owned file → PASS | `evidence/lint/` |
| Name-clash scan (namespaces resolved, public + private) | 0 new names → PASS | `evidence/clash/` |
| Widths / sizes (`python3 -I`) | max 100 / 99 characters; 194 and 305 lines → PASS | `evidence/final/widths.txt` |
| Patch reproduction (`git am` at the base, scratch clone, committer identity/date from `COMMITS.tsv`) | both hashes and the final tree reproduced → PASS | `evidence/final/patch-reproduction.txt` |
| Manifests | `SHA256SUMS` and `evidence/SHA256SUMS`: listed paths equal the delivered files exactly; `shasum -a 256 -c` all OK | — |

## Environment

- **Preflight** (`evidence/logs/preflight.log`): `nproc` 4; cgroup v1 memory limit 14,338,772,992 B;
  in use (`usage − total_cache + total_shmem`) 386,310,144 B; **headroom 12.99 GiB** (floor 4); disk free on
  the clone's ext4 filesystem **18.22 GiB** (floor 12). No E-RES. The checkout, `.lake` and the olean tree
  are on ext4 (`/dev/vda`), not tmpfs.
- **Toolchain:** elan installed after the preflight with `leanprover/lean4:v4.25.0`
  (`evidence/logs/toolchain.log`); disk re-check before the cache: 15.8 GiB free (floor 8).
- **Cache** (`evidence/logs/cache-store.log`, `mathlib-roots.txt`, `cache-get.log`): the archive store
  `/root/.cache/mathlib` was **absent** before the fetch (0 archives, so none pre-existing). Narrowed fetch
  for the **84 roots** (identical to the pack's `roots.txt`): "Attempting to download 2338", "Decompressing
  2338", "Completed successfully", exit 0, no failed download. No zero-size olean. Cache probe
  (`import Mathlib.Algebra.BigOperators.Field`) elaborated, exit 0.
- **Packages** (`evidence/logs/packages-check.log`): last line
  `RESULT: PASS: 11 present packages match the manifest; absent: «doc-gen4», UnicodeBasic, BibtexQuery, MD4Lean`
  (no module of the order imports an absent package).
- **Bootstrap** (`evidence/logs/bootstrap.log`): phase 1 = the 23 modules of the order that the owned files
  and `Pseudorandom/Indistinguishability` import (`bootstrap-phase1.txt`), ALL OK; then the owned files at
  the base (`evidence/logs/base-checks/`: Columns 2 `sorry`, Security 4 `sorry`, 0 errors); the remaining
  modules were built by the checkpoint-1 sweep of all 147, in order; the final sweep re-checked all 147.
- **Lean processes:** one at a time throughout (every check serial through `check_module.py`). Peak RSS per
  check ≤ 2.9 GB (`MAXRSS_KIB` in each log; `/usr/bin/time` is absent on this host, so the peak is
  `getrusage(RUSAGE_CHILDREN)`). No `lake build`, no unfiltered `lake exe cache get`; Python always
  `python3 -I`.
- **Check scripts:** module checks and sweeps use `scripts/lean_check_tree.sh` unchanged. Seals, controls
  and probes use `evidence/tools/lean_check_tree_maxerrors0.sh`, a copy differing only in `-DmaxErrors=0`,
  failing on `error[:(]`, and taking the checkout root from the working directory.

## Evidence

All under `inbox/fills/gsw-security/`; `SHA256SUMS` lists every delivered file except itself and
`evidence/SHA256SUMS` every file under `evidence/` except itself (paths equal to the delivered files, no `./`).
- `patches/0001-*.patch`, `patches/0002-*.patch`: the whole `git format-patch 486f44f8..fill/gsw-security`
  series; `patches/COMMITS.tsv`: hash, author and committer name/email/date (raw and ISO), **signing `none`**
  for both (committed with `git -c commit.gpgsign=false`; `%G?` = N, no `gpgsig` header).
- `src/`: the final `Columns.lean` and `Security.lean` under their repository paths (byte-equal to the branch).
- `evidence/logs/`: preflight, toolchain, cache store/roots/fetch, packages check, bootstrap, base checks, the
  development iterations (`dev/`), cache probe.
- `evidence/checkpoint1/` and `evidence/final/`: sweeps (all 147 raw logs each), admissions, axioms (+ check),
  unfold scans, Rule 10 summaries, seal coverage, error counts, widths, patch reproduction, queue outputs; the
  checkpoint REPORT.
- `evidence/seals/{cp1-base,cp1,final-base,final}/`, `evidence/controls/{cp1,final}/`,
  `evidence/axioms/{cp1,final}/`: every probe source, line map, manifest, raw log and `results.jsonl`.
- `evidence/headers/`, `evidence/lint/`, `evidence/clash/`, `evidence/overlap/` (search logs), `evidence/probes/`.
- `evidence/tools/`: every script used (all run as `python3 -I` from the fill checkout's root):
  `check_module.py`, `run_list.py`, `closure.py`, `lean_check_tree_maxerrors0.sh`, `make_seals.py`,
  `run_seals.py`, `make_controls.py`, `check_controls.py`, `seal_coverage.py`, `rule10_summary.py`,
  `explicit_unfold_scan.py`, `make_axioms.py`, `check_sorries.py`, `error_counts.py`, `widths.py`,
  `make_patches.py`, `manifests.py`, and the two queue scripts.

## ===== briefs/lattice-gsw/fills/gsw-core/issued-r1/brief.md =====

# Claude fill · GSW gadget, noise algebra, public- and secret-key scheme, circuit evaluation (`gsw-core`)

**Issue base** `486f44f8414c20a2d21e452c44de8b8c8d8513a0`, the head of draft PR #333 (branch `stmt/gsw`; Gate 41
CLOSED by disposition). It contains #332's commit `94eae71b779c4ca0f76c138d699f4d737dbd6cee` as an ancestor
(`486f44f8~3`), so the F0 readers are present and **proved** in it (*Base and parallel work*). **Unit** `gsw-core`:
fill units F1, F2, F3, F7 and F4 of `briefs/lattice-gsw/plan-section.md` §G7 (lattice campaign, phase 5).
**Worker** Claude, a lead with **up to 2 sub-agents** (Seyoon's ruling, 2026-11-16). **Lean** 4.25.0 and the
Mathlib revision in that commit's `lake-manifest.json`.

Prove the 29 admitted, frozen statements of five modules under
`TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/`. They passed the phase-5 statement phase and Gate 41,
which accepted every target as true with the hypotheses it displays. Each docstring holds the maintainer's proof
sketch.

## Feasibility and size (maintainer's assessment)

Feasible. Gate 41 re-derived every noise bound by hand and found no false target, no missing hypothesis and no
off-by-one (*Gate 41 remarks*). The proofs are finite-sum algebra over `ZMod q` and `ℤ`, list induction and one
application of the proved host `runWith_rel`.

**Estimated size: about 760 lines** of proof (plan §G6): Gadget about 110, Noise about 190, Scheme about 175,
Symmetric about 110, Eval about 175. Each file is now 111–235 lines and stays well under 1000.

## Checkout and delivery

- Fetch `stmt/gsw` (or the commit itself). Start a local branch `fill/gsw-core` at the exact issue base, and
  record the base in `REPORT.md`. Keep the proof branch local.
- Read `policy.md`, the attached environment addendum and `README.md`.
- Deliver every checkpoint and the final payload under `inbox/fills/gsw-core/` on `exchange/pass-shelat-ch5-8`:
  - `REPORT.md`;
  - `patches/`: the whole `git format-patch` series from the issue base;
  - `patches/COMMITS.tsv`: one row per commit, giving its hash, the author's name, email and date, the
    committer's name, email and date, and its **signing** (`none`, or the signature format), so that `git am` at
    the base reproduces every hash. Commit with `git -c commit.gpgsign=false`; if a commit is signed anyway, say
    so in its row and in `REPORT.md`. Before you push, check the reproduction in a scratch clone and say so in
    `REPORT.md`;
  - `src/`: the changed and new files under their repository paths;
  - `evidence/`, with an `evidence/SHA256SUMS` manifest (see *Evidence completeness*);
  - a top-level `SHA256SUMS` listing every delivered file under `inbox/fills/gsw-core/` except itself. The
    delivered paths must **equal** the manifest's paths exactly: nothing missing, nothing extra, and no leading
    `./`. Check this before each push.
- Commit on the exchange as `fill gsw-core: checkpoint N` and `fill gsw-core: final`.
- Pull with rebase before pushing. Push only your delivery path, never force-push, and never touch another path
  (other fills, gates, the `arora-barak-ch3-4/` and `lwe-sis-constructions/` folders). If a push is refused,
  keep the commit and say so. Campaign changes land by a maintainer PR for Seyoon's approval.

## Base and parallel work

- **F0 is already done, by #332** (`stmt/dagcircuit-readers`, head `94eae71b`, Gate 41 CLEAR, not yet merged).
  #333 is stacked on it, and #333's diff of `DAGCircuit.lean` is exactly #332's. So your base already contains,
  proved and standard-axiom only, the readers `DAGGate.depth_eq`, `DAGCircuit.depths_eq`, `depthAt_eq`,
  `depth_eq`, the lemma `DAGGate.getD_lt_depth` and the host `runWith_rel`
  (`Complexity/CircuitComplexity/DAGCircuit.lean`, lines 562–647). F4 **uses them as published lemmas of a frozen
  file**; nothing about them is proved-modulo. No combined base is needed.
- **Merge order.** #332 merges first, then #333, then the fills, rebased by the maintainer onto the then records
  tip. If #332 or #333 changes or merges during the fill, **stay on the issue base**.
- **`gsw-security` runs in parallel** from the same base. It owns `Hashing/SIS/Columns.lean` and
  `GSW/Security.lean`, which are in your order (Security imports Scheme) but which you never edit. It may cite
  your targets as frozen statements, and you may not change any of them.
- **Proved-modulo.** Inside this job the dependency order is F1, then F2, then F3 and F7, then F4. Each unit may
  cite the frozen (sorried) statements of the units before it, so sub-agents can work in parallel. At the final
  every target is proved and no target may reach `sorryAx`.

## Targets (frozen; quoted from the issue base)

29 declarations, each a `theorem` whose body is `sorry` (`base-sorries.txt`). Lines are at the issue base. Paths
are under `TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/`.

| Unit | File (lines at base) | Targets (declaration line) |
|---|---|---|
| F1 | `Gadget.lean` (204) | `digits_decomposeVec` (150), `gadget_mulVec_decomposeVec` (163), `gadget_mul_decompose` (174), `decomposeVec_block_eq_false` (184), `errorSum_decomposeVec_le` (197) |
| F2 | `Noise.lean` (235) | `encrypts_gadget` (118), `encrypts_zero` (124), `Encrypts.mono` (130), `Encrypts.add` (139), `Encrypts.neg` (147), `Encrypts.sub` (154), `Encrypts.sum` (164), `Encrypts.mul` (181), `Encrypts.mul_bit` (190), `Encrypts.mul_le` (199), `Encrypts.nand` (210), `encrypts_chain` (225) |
| F3 | `Scheme.lean` (215) | `vecMul_secretVector_augmented` (80), `encrypts_encrypt` (147), `encrypts_keygen_encrypt` (160), `decrypt_of_encrypts` (181), `decrypt_of_encrypts_dyadic` (193), `decrypt_keygen_encrypt` (206) |
| F7 | `Symmetric.lean` (111) | `encrypts_symEncrypt` (83), `distAdv_symEncrypt_le` (102) |
| F4 | `Eval.lean` (209) | `homAnd_encrypts` (142), `homGate_encrypts` (159), `eval_encrypts` (180), `decrypt_keygen_eval` (194) |

Counts: F1 5, F2 12, F3 6, F7 2, F4 4; they equal plan §G7. The statements, with their docstrings and sketches,
are in the files; read them there. The two headline statements, for orientation:

```lean
theorem Encrypts.mul {x₁ x₂ : ℤ} {β₁ β₂ : ℕ} {C₁ C₂ : Ciphertext P}
    (h₁ : Encrypts P t x₁ β₁ C₁) (h₂ : Encrypts P t x₂ β₂ C₂) :
    Encrypts P t (x₁ * x₂) (P.columns * β₁ + x₁.natAbs * β₂) (mul P C₁ C₂) := by
  sorry
```

```lean
theorem eval_encrypts {k : ℕ} (Cc : DAGCircuit k) (hfan : ∀ g ∈ Cc.gates, g.args.length ≤ 2)
    (x : Fin k → Bool) (cts : Fin k → Ciphertext P) (β : ℕ)
    (hin : ∀ i, Encrypts P t ((x i).toNat : ℤ) β (cts i)) :
    Encrypts P t ((Cc.eval x).toNat : ℤ) ((P.columns + 1) ^ Cc.depth * β) (eval P Cc cts) := by
  sorry
```

## Multi-agent work (ruling: up to 2 sub-agents)

- **The lead owns the job.** It owns the brief, the branch `fill/gsw-core`, every commit, the final sweep and
  checks, the delivery and `REPORT.md`. Sub-agents return their work to the lead; only the lead commits on
  `fill/gsw-core` and pushes. The lead is the one integrator.
- **At most 2 sub-agents.** Each owns a **disjoint set of target files**; no two agents edit the same file. A
  suggested split: sub-agent A owns `Gadget.lean` and `Noise.lean` (F1, F2); sub-agent B owns `Scheme.lean` and
  `Symmetric.lean` (F3, F7); the lead owns `Eval.lean` (F4) and integrates. Another split is fine if it is
  disjoint and recorded. A file is reassigned only through the lead, and only after its owner has stopped.
- **Worktrees and olean trees.** Each sub-agent has its own git worktree of the lead's clone (on a sub-branch from
  the lead's current commit) and its own TCSlib olean tree (`TCSLIB_OLEANS`); never let two Lean processes write
  one olean tree. A sub-agent's `.lake/packages` is a symlink to the lead's (read-only Mathlib, the same pins);
  only the lead runs `lake`, and only the lead fetches the cache. The lead may seed a sub-agent's olean tree by
  copying its own bootstrapped **TCSlib** olean tree; copying Mathlib or other package trees stays forbidden
  (addendum, Part 1, item 2).
- **One Lean process at a time on the host** (addendum), shared by the lead and both sub-agents. Serialize every
  `lean`, `lake` and `scripts/lean_check_tree.sh` call through one lock (for example
  `flock <clone>/.lean.lock …`). Sub-agents keep writing while they wait. Do not hold the lock across modules.
- **Proved-modulo between agents.** A downstream file is checked against the upstream files' base statements
  (sorried bodies give the same interface), so B and the lead need not wait for A. The lead re-checks everything
  on the merged branch.
- **The record.** `REPORT.md` records who proved what. Sub-agent logs go under `evidence/subagents/<name>/` and are
  covered by the evidence-completeness rule.

## Published interfaces (reuse first)

Read other files' definitions **only** through these readers (Rule 10). The list is a start, not a limit: search
for more before writing any lemma.

| Interface | Provider (path under `TCSlib/`, line at base) |
|---|---|
| `Parameters.columns_eq`, `Ciphertext_eq` (abbrevs, notation), `gadget_apply`, `digit_val`, `decomposeVec_eq`, `decompose_apply`, `lift_apply` | `…/GSW/Gadget.lean` |
| `mul_eq`, `nand_eq`, `chain_nil`, `chain_cons`, `encrypts_iff` | `…/GSW/Noise.lean` |
| `secretVector_eq`, `encrypt_eq`, `halfVector_eq`, `decryptColumn_eq`, `decrypt_eq` | `…/GSW/Scheme.lean` |
| `rowEquiv_eq`, `symEncrypt_apply` | `…/GSW/Symmetric.lean` |
| `homAnd_nil`, `homAnd_singleton`, `homAnd_cons_cons`, `homNot_eq`, `homOr_eq`, `homGate_eq`, `evalValues_eq`, `eval_eq` | `…/GSW/Eval.lean` |
| `TrapdoorFunctions.Lossy.gadget_eq` (163), `digits_eq` (174), `digits_val` (183), `gadget_mulVec` (214), `digits_injective` (230) | `Cryptography/TrapdoorFunctions/Lossy/Gadget.lean` |
| `Randomized.blocksEquiv_apply` (267), and Mathlib's `Equiv.apply_symm_apply` | `Complexity/Randomized/RandomBits.lean` |
| `LWE.noisyValues_apply` (67), **`LWE.binaryErrorSum_bound`** (79), `sample_fst` (109), `sample_snd` (116) | `Cryptography/LWE/Basic.lean` |
| `LWE.Noise.bounded_iff` (61) | `Cryptography/LWE/Noise.lean` |
| `LWE.BitEncoding.codepoint_eq` (46), `decode_eq` (112), **`decode_codepoint_add`** (123) | `Cryptography/LWE/BitEncoding.lean` |
| `LWE.decisionAdvantage_eq` (53) | `Cryptography/LWE/Experiments.lean` |
| `Regev.keygen_fst` (53), `keygen_snd` (59), `decrypt_eq` (94); relatives `encrypt_residual` (105), `subsetError_bound` (136), `decrypt_encrypt` (146) | `Cryptography/Encryption/PublicKey/Regev/Basic.lean` |
| `Regev.augmented_eq` (173), `augmented_bijective` (182); relative `encrypt_augmented` (199) | `Cryptography/Encryption/PublicKey/Regev/Experiments.lean` |
| `Symmetric.Regev.encryptDist_eq_shift_sample` (61), `acceptProb_uniform_shift` (77), `distAdv_encrypt_le` (116): the F7 pattern | `Cryptography/Encryption/Symmetric/Regev/Experiments.lean` |
| `acceptProb_def` (98), `distAdv_def` (102), `acceptProb_comp_equiv` (107) | `Cryptography/Foundations/Experiments.lean` |
| `uprob_comp_equiv` (165), `abs_sub_le_sum_hybrids` (218) | `Cryptography/Foundations/Probability.lean` |
| `acceptProb_fst`/`_snd` (73, 83), `acceptProb_bind` (91), `acceptProb_update` (103), `distAdv_comp` (141) | `Cryptography/Pseudorandom/Indistinguishability.lean` (an allowed extra import) |
| `DAGGate.eval_eq` (131), `values_eq` (478), `DAGCircuit.eval_eq` (486), `values_getD_input` (527), `depthAt_input` (533), `depthAt_gate` (548), `DAGGate.depth_eq` (562), **`DAGGate.getD_lt_depth`** (571), `depths_eq` (592), `depthAt_eq` (596), `depth_eq` (600), **`runWith_rel`** (616); `runWith_getD_of_lt` (192), `runWith_getD_gate` (207), `runWith_getD_take` (221); the structure fields `Cc.args_lt`, `Cc.output_lt` | `Complexity/CircuitComplexity/DAGCircuit.lean` (F0 readers from #332) |
| `List.getD_eq_getElem`, `List.getElem_ofFn`, `List.forall₂_map_left_iff`, `List.forall₂_map_right_iff`, `List.all_map`, `Matrix.vecMul_vecMul`, `Matrix.vecMul_add`, `Matrix.vecMul_smul`, `Matrix.dotProduct_mulVec`, `Fin.sum_univ_castSucc`, `Fin.snoc_castSucc`, `Fin.snoc_last`, `ZMod.natCast_zmod_val`, `Int.natAbs_add_le`, `Int.natAbs_mul`, `Finset.induction_on` | Mathlib (search for the exact names at the pin) |

## Proof routes and checkpoints

The docstrings' sketches are the route; Gate 41 validated them. What follows fixes the obligations and the
checkpoints. Write `N = P.columns = (n+1)·ℓ`, `X = lift (decompose C₂)`, `w = halfVector P` and
`z` the lifted decomposition of `w`.

**F1 · Gadget** (5 targets).
- `digits_decomposeVec`: `digits_eq`, `decomposeVec_eq`, `Equiv.apply_symm_apply`.
- `gadget_mulVec_decomposeVec`: coordinate `j` is the cast of `(Lossy.gadget ℓ (n+1))ᵗ · x` at `j`
  (`gadget_apply`; `Int.cast_sum`, `Int.cast_mul`); `Lossy.gadget_mulVec` gives the digit, then
  `digits_decomposeVec`, `digit_val`, `ZMod.natCast_zmod_val`.
- `gadget_mul_decompose`: column by column from the previous target (`decompose_apply`, `lift_apply`); no
  finiteness hypothesis on the column index is needed.
- `decomposeVec_block_eq_false`: `digits_val` writes the block as `∑ₖ bitₖ·2^k = (u j).val = 0`; a sum of
  nonnegative terms vanishes termwise and `2^k > 0`.
- `errorSum_decomposeVec_le`: split the sum through `finProdFinEquiv` into blocks
  (`Fintype.sum_prod_type`, `Equiv.sum_comp`); blocks `j ≠ j₀` vanish; the surviving block is a binary subset sum
  of `ℓ` entries, so `LWE.binaryErrorSum_bound` with `m := ℓ` gives `ℓ·β`.

**F2 · Noise** (12 targets). The witness algebra is over `ℤ`, cast into `ZMod q`.
- `encrypts_gadget`, `encrypts_zero`, `.mono`, `.add`, `.neg`, `.sub`, `.sum`: as the sketches (`e = 0`; reuse;
  `e₁ + e₂`; `-e`; `sub_eq_add_neg`; `Finset.induction_on` under `classical`).
- **`Encrypts.mul`, the asymmetric bound.** The exact witness is `j ↦ (∑ᵢ e₁ i · X i j) + x₁ · e₂ j`:
  `tᵗ(C₁X) = (x₁tᵗG + e₁ᵗ)X = x₁tᵗC₂ + e₁ᵗX = x₁x₂tᵗG + x₁e₂ᵗ + e₁ᵗX`, using `gadget_mul_decompose` for `GX = C₂`.
  The first summand is a binary subset sum of `N` entries (`LWE.binaryErrorSum_bound`, `N·β₁`), the second has
  magnitude `|x₁|·|e₂ j| ≤ |x₁|·β₂`. Negative integer messages are covered; no independence or freshness
  hypothesis is needed.
- `mul_bit`, `mul_le`, `nand`: `(b.toNat : ℤ).natAbs ≤ 1`; `N·β + β = (N+1)·β`; `1 − b₁b₂ = (!(b₁ && b₂)).toNat`
  by cases.
- **`encrypts_chain`**: list induction on `Forall₂`, the head on the **left**. Step: `N·β + (β₀ + k·N·β) =
  β₀ + (k+1)·N·β`. The empty chain is the accumulator and the empty product is `1`, so the message is
  `(bs.all id).toNat * x`.
- **Caution (Gate 41, phase-6/7 hook).** Keep the exact `|x₁|·β₂` term in `Encrypts.mul`. A later BV14 selector
  step `(G−C)⊡V₀ + C⊡V₁` costs only an additive `2Nβ` because of it; do not route chain or selector arguments
  through `mul_bit` where the exact term is needed.

**F3 · Scheme** (6 targets).
- `vecMul_secretVector_augmented`: column `i` of `Regev.augmented` is the sample row followed by its value
  (`augmented_eq`, `Fin.sum_univ_castSucc`, `Fin.snoc_castSucc`, `Fin.snoc_last`, `secretVector_eq`); the inner
  product is `−⟨s,aᵢ⟩ + (⟨aᵢ,s⟩ + eᵢ) = eᵢ` by `noisyValues_apply`.
- `encrypts_encrypt`: `tᵗC = (tᵗĀ)·lift R + μ·tᵗG`; the witness is `j ↦ ∑ᵢ eᵢ·R i j`, bounded by `m·B`
  (`LWE.binaryErrorSum_bound`). `encrypts_keygen_encrypt`: the keygen and sample readers and `bounded_iff`.
- **`decrypt_of_encrypts`.** `Regev.decrypt_eq` reads `c.2 − ⟨s, c.1⟩`, which for the split column is `⟨t, Cz⟩`
  (`Fin.sum_univ_castSucc`, `secretVector_eq`; the column split uses `Fin.init` and `Fin.last`).
  `Matrix.dotProduct_mulVec` and the invariant give `b·⟨t, Gz⟩ + ⟨e, z⟩`; `Gz = w`
  (`gadget_mulVec_decomposeVec`) and `⟨t, w⟩ = ⌊q/2⌋` (`halfVector_eq`, `codepoint_eq`), so the residual is
  `codepoint b + ⟨e, z⟩`. Every block of `z` but the last vanishes; `errorSum_decomposeVec_le` with
  `j₀ = Fin.last n` gives `|⟨e, z⟩| ≤ ℓ·β`; `decode_codepoint_add` with `B := ℓ·β` finishes. Gate 41: this is
  exactly that lemma's premise, **including odd `q` and signed errors**; there is no rounding or tie gap; at
  `q = 2` or `3` the separation forces `β = 0` and decoding is still correct.
- `decrypt_of_encrypts_dyadic`: for `q = 2^ℓ`, `⌊q/2⌋ = 2^{ℓ−1}` and `z` has its single `1` at block `n` (the
  last), position `ℓ−1` (zero-based). The error sum is one entry of `e`, so the bound is `β` and the condition
  `2β < q/2`. `hℓ` is redundant given `q ≥ 2`; keep it (the statement is frozen).
- `decrypt_keygen_encrypt`: the two previous targets.

**F7 · Symmetric** (2 targets).
- `encrypts_symEncrypt`: `Matrix.vecMul` of the `submatrix` reads `tᵗĀ` at the reindexed columns, which is
  `e ∘ rowEquiv` by `vecMul_secretVector_augmented`; noise `B`, not `m·B`.
- `distAdv_symEncrypt_le`: follow `Encryption.Symmetric.Regev.distAdv_encrypt_le`. On the uniform side,
  `(A, b) ↦ symEncrypt P hN (A, b) μ` is a bijection onto `Fin k → Ciphertext P` (`augmented_bijective`, the
  column reindexing by `rowEquiv`, translation by `μG`; both sides have `q^{(n+1)·k·N}` elements). Its inverse
  subtracts the message gadgets, assembles all columns through `rowEquiv` and inverts augmentation. So both ideal
  acceptance probabilities equal that of a uniform batch; insert it and use the triangle inequality. One common
  secret and all `kN` row errors stay in the real experiment; the empty batch also satisfies the statement.

**F4 · Eval** (4 targets).
- `homAnd_encrypts`: induction along `homAnd`'s three equations. The declared bound is
  `((k−1)·N + 1)·β` with natural subtraction: at `k = 0` the actual noise is `0` (`encrypts_gadget`, `.mono`);
  at `k = 1` it is `β`; for `k ≥ 2`, `N·β + ((k−2)·N + 1)·β = ((k−1)·N + 1)·β` (`Encrypts.mul_bit`, head on the
  left). Messages: `List.all_cons` and `Bool.toNat` of `&&` as a product.
- `homGate_encrypts`: case on `g.kind` (`homGate_eq`, `DAGGate.eval_eq`); `List.forall₂_map_left_iff`/
  `_right_iff` give `homAnd_encrypts`'s hypothesis; `length ≤ 2` gives `≤ (N+1)·β`. `¬` is `G − ·`
  (`Encrypts.sub` with `encrypts_gadget`, noise `0 + ·`); `∨` is De Morgan, where `G − C` keeps noise `β`.
  Arities 0, 1 and 2 of every kind, including the library's `.not` gate, and repeated arguments are covered.
  The default `0` for an out-of-range vertex is consistent because `0` encrypts `false` noiselessly.
- **`eval_encrypts`.** Apply `runWith_rel` to `DAGGate.eval` from `List.ofFn x` and `homGate P` from
  `List.ofFn cts`, with the vertex-indexed relation
  `R v b C := Encrypts P t b.toNat ((N+1)^{Cc.depthAt v}·β) C`. Inputs have depth 0 (`depthAt_input`;
  `getD` of `List.ofFn` by `List.getD_eq_getElem` and `List.getElem_ofFn`). Acyclicity is `Cc.args_lt`; full
  `IsFaninTwo` is not needed (it has no reader at this base; do not add one). At gate `i`, `depthAt_gate` and
  `depthAt_eq` write the depth as `gs[i].depth Cc.depths`, and `DAGGate.getD_lt_depth` puts each argument at depth
  at most `d−1` with `d ≥ 1`; then `Encrypts.mono` (`Nat.pow_le_pow_right`, `N+1 ≥ 1`) and `homGate_encrypts`
  give `(N+1)·((N+1)^{d−1}·β) = (N+1)^d·β`. Read the in-range output (`Cc.output_lt`) with
  `DAGCircuit.eval_eq`, `values_eq`, `depth_eq`, `evalValues_eq` and `eval_eq`. Counting `¬` gates in the depth
  only enlarges the bound, and dead gates are harmless because the invariant is per vertex.
- `decrypt_keygen_eval`: `encrypts_keygen_encrypt` (input noise `m·B`), `eval_encrypts`, `.mono` with
  `Cc.depth ≤ L` (`Nat.pow_le_pow_right`), then `decrypt_of_encrypts`. Gate 41: the declared
  `2·(ℓ·((N+1)^L·mB)) < ⌊q/2⌋` suffices for every seed and coin matrix; **no extra factor and no `L+1`**.

**Checkpoints** (each delivers whole proved declarations; at least one mid-way checkpoint is required):
1. **Checkpoint 1 · F1 and F2** (or, under a different split, the first two units to finish): Gadget and Noise
   proved, with the per-module checks, axiom prints and seals of the changed files. Send it.
2. **Checkpoint 2 (optional) · F3 and F7**, proved modulo nothing in this job once checkpoint 1 is merged.
3. **Final · F4** and every target proved; the full checks below.

If a sketch is wrong, or a target is false as stated, stop that line of work and escalate with the exact
obligation: a checkpoint with the counterexample or the missing fact. **Do not weaken any statement**, add a
hypothesis or change a definition. A partial final is allowed only with each unproved target named and its exact
remaining obligation stated.

## Scope

**Owned files.** `Gadget.lean`, `Noise.lean`, `Scheme.lean`, `Symmetric.lean`, `Eval.lean` (the paths above). In
them you may:
1. replace each target's `sorry` body;
2. rewrite each target's `**Proof sketch.**` paragraph to describe the delivered proof (the statement prose before
   it stays byte-identical);
3. add auxiliary declarations (lemmas, `private` or public) before their first use, each public one with a
   formula docstring; and list new public results under the module docstring's `## Main results`;
4. add precise `import` lines for Mathlib modules and for `TCSlib.Cryptography.Pseudorandom.Indistinguishability`
   (in `order.txt`). Fetch the cache for any new Mathlib root as the addendum says. Any other import needs a scope
   request. Do not import a module downstream of the importing file.

**The frozen-statement rule (binding; checked).** Every declaration present at the issue base in an owned file
stays in the same file and order, with its header byte-identical: attributes and modifiers, keyword, name,
binders and type, up to the `:=`, `by`, `where` or first `|` that begins the proof (`open … in`, `include … in`,
`omit … in` prefixes included). Every `def`, `abbrev`, `structure`, `instance` stays byte-identical, body included,
and so do the readers (`_eq`, `_apply`, `_iff`, `chain_nil`, …). Delete nothing. Keep every `variable`,
`section`, `open`, `set_option` and the module title. Write a `python3 -I` script that extracts every declaration of
the owned files at base and at final, compares headers (and whole definitions) byte for byte, checks the order,
and prints the full diff; deliver it and its output under `evidence/headers/`, with zero unexpected differences.
Add two controls: one header altered by one character must report exactly one difference, and a deleted reader
must report exactly one removal.

**Helper modules.** Not expected: every owned file stays far below 1000 lines with its proofs. If one is needed, it
goes under `GSW/<Owned>/` (for example `GSW/Eval/Depth.lean`), is imported by that owned file only, states its
lemmas generically (it cannot see the owned file's definitions), and gets a module docstring. The facades
`GSW.lean`, `Homomorphic.lean`, `AdvancedEncryption.lean` and `TCSlib.lean` are frozen; nothing goes directly under
`GSW/`.

**Frozen files.** Everything else, including `Security.lean` and `Hashing/SIS/Columns.lean` (owned by
`gsw-security`), `DAGCircuit.lean`, the LWE, Regev, Lossy, SIS and Foundations files and all facades.
- **Scope requests.** If the route needs a change to a frozen file (a reader beside a foreign definition, an
  import, a promotion), stop that line of work. Ask Seyoon in your session, giving the exact file, the diff and
  the reason, and go ahead only on his approval. Record the request and his answer verbatim under
  `evidence/scope-request/` and in `REPORT.md` § *Scope requests*. Seyoon prefers a route with no frozen-file edit.
- A lemma that belongs in an existing file goes in your owned file, with a promotion request.

## Sources and citations (DW-6, DW-7)

- The sources are [GSW13] (author version of 8 June 2013), [AP14] (ePrint 2014/094 of 13 June 2014), [BV14]
  (ePrint 2013/541) and [Pei16] (author version of 17 February 2016). **GSW13, BV14 and AP14 are not ingested**
  (DW-7, Seyoon 2026-11-16: Markdown transcriptions of the passages used are added later by the maintainer), and the
  scoped Pei16 Markdown does not yet cover §5.4.3 and §6.1.2–6.1.3 (DW-7 also extends it later).
- You may rely on: the frozen docstrings' tags; the Gate 41 excerpts on the exchange,
  `outbox/gates/41-gsw-statements-gate/source-excerpts/{GSW13,AP14,BV14,Pei16}-excerpts.md` (SHA-256
  `b1241a90e4068e3f95a0bd80a2b4b497753d644e12c03fcd859be27cb70a4311`,
  `7e6cc3b800833cf2b3bea3446b2ddfac5c3f6d8e487aad5e325c7996dea88a34`,
  `d83ffb1914e2e88956ce03d62e5a7f6a87b4c14af1ce25221da43c94ae139166`,
  `2b86ff971644029c715d748ac9425bcbed4c7a5ac3c2f4418a610d3c0ff11199`); and the committed raw extraction
  `blueprint/src/references/peikert2016-lattice-survey.raw.md`.
- **Never fabricate a source excerpt, quotation or location.** A new declaration either is glue (no tag) or carries
  a tag whose passage is in those materials. Do not add reference files, edit `blueprint/` or run
  `scripts/sources.py`.
- **Small-secret LWE (A3, DW-6) is not used in phase 5.** The secret is uniform, as in the LWE layer. Introduce no
  normal-form assumption.
- **Conventions to keep straight in sketches (Gate 41).** The code uses `I_{n+1} ⊗ gᵗ`, matching AP14's
  block-diagonal description and Pei16; AP14's printed `gᵀ ⊗ I_n` differs from it by a column permutation, so do not
  call the two entrywise identical. AP14 and the code expand the **left** operand's error; GSW13 and BV14 expand the
  right operand's (mirror images under transposition). Fresh ciphertexts go on the left in additive chains here.

## Proof discipline

- **Size and width.** Every line has at most 100 characters (Python `len`), every file at most 1000 lines (policy
  target 150–600 per math file). Check both with a short `python3 -I` script before each push and put its output in
  `evidence/`.
- **Duplication (binding).**
  - **Search first.** Before writing any lemma, search `TCSlib/` and Mathlib for its statement shape and key names.
    Reuse published lemmas by importing them. The table above is a start; search further.
  - **Undisclosed copies of public lemmas are majors.** The majors that held Gates 23, 24, 29, 32 and 34 were
    undisclosed duplicates (for example G23-01, a private copy of `length_le_length_encodeLog`; G24-01,
    `inputWord_take`, which re-proves the public `take_ofFn_castLE`; G32-01, `getD`/`headD`-of-`List.ofFn` copies).
  - **Nearest relatives here:** `LWE.binaryErrorSum_bound`, `Regev.subsetError_bound` and
    `Lossy.error_sum_bound` (`TrapdoorFunctions/Lossy/Matrix.lean:175`) for binary subset sums;
    `Regev.encrypt_residual` and `Regev.decrypt_encrypt` for the decryption residual; `Lossy.gadget_mulVec` and
    `digits_val` for the gadget; `SecureComputation.runWith_sim` (`SecureComputation/Garbling.lean:94`, its
    functional special case) and `runWith_remap_rel` for `runWith_rel`; `values_getD_input` and Mathlib's
    `List.getD_eq_getElem`/`List.getElem_ofFn` for `getD` of `List.ofFn` (the DL-47 family: add no further copy;
    `TCSlib.Cryptography.headD_drop_ofFn` in `Foundations/BitLists.lean:61` is the `headD` form); the symmetric
    Regev experiments for F7.
  - **Private lemmas.** Never copy a private lemma silently. If you need one, re-derive it from published readers,
    keep its statement general, and disclose it.
  - **Disclose every overlap.** `REPORT.md` has a section **`## Overlap and reuse`**. For every new declaration
    (and every inline `have` re-proof) that restates, specializes or re-proves existing material (public or
    private, TCSlib or Mathlib), give its nearest relative (`path:line`), the relation, and why it is not reused.
    List the searches you ran.
- **Docstrings and sketches.** The last batches' landing edits were mostly LE-doc and LE-width. Do these yourself:
  - every new public declaration has a docstring that states its formula, with its arguments in the Lean order, and
    a source tag only as *Sources and citations* allows;
  - every proof of 15 lines or more carries a `**Proof sketch.**` paragraph, and long proofs get step comments
    (policy §3); each target's sketch describes the delivered proof;
  - a new public `def` lands with its `_eq`, `_iff` or `simps` readers (lint check 8); a new public `abbrev` with an
    `_eq` or `_iff` lemma. New definitions are not expected;
  - add no `@[simp]`, and no global attribute.
- **Rule 10.**
  - Use only published readers for other files' definitions, including generated matchers and projections (the
    table above). Core and Mathlib definitions may reduce in a `rfl`, `decide` or `show` step but are never passed to
    `simp`, `rw` or `unfold`; use their equation lemmas (`Bool.toNat_true`, not `simp [Bool.toNat]`).
  - Each owned file may read **its own** definitions directly. The owned files are foreign to each other: Scheme
    reads `Encrypts` only through `encrypts_iff`, Eval reads `mul` through `mul_eq`, and so on. Helper modules count
    as foreign too.
  - **Notation, never sealed:** reducible abbreviations (here `Parameters.columns` and `Ciphertext`; also
    `QueryImpl`-style abbrevs), `PolyExpr.eval`, and projection coercions (a `CoeFun`/`Coe` whose body is a
    structure projection; Seyoon, 2026-11-14).
  - **Type-level Rule 10 (plan §G8).** Matrix index types must never be reached by unfolding another file's
    definition. The seal must cover `Regev.augmented`, `LWE.sample`, `Lossy.gadget`, `Randomized.blocksEquiv` and
    `BitEncoding.codepoint`.
  - Identifiers use the Greek `μ` (U+03BC); never the micro sign `µ` (U+00B5).

## Checks and report

- **Bootstrap.** From `order.txt` (31 modules) and the narrow `roots.txt` (38), following the addendum. Check one
  module per `scripts/lean_check_tree.sh` call, one Lean process at a time on the host. **Never run `lake build`**
  or an unfiltered `lake exe cache get`. Run Python as `python3 -I`. Insert any helper module before its consumer.
- **Per-module native check and sweep.** Check each owned module after each change. Before each delivery,
  recheck the five owned modules and sweep the whole order with 0 errors.
- **Admissions.** Compare the `sorry` warnings with `base-sorries.txt` (35 declarations in 7 modules). At the
  final the only change is the removal of your 29 targets: 6 remain, in `Hashing/SIS/Columns` (2) and
  `GSW/Security` (4), which are `gsw-security`'s. A checkpoint lists exactly which targets it removed.
- **Axioms.** Print the axioms of every target and of every stored constant of the changed files. At the final
  expect only `propext`, `Classical.choice` and `Quot.sound`. At a checkpoint, a target that cites a later-unit
  target may still reach `sorryAx`; name the cited target. Run a **dependency trace** (a probe that walks the
  constant closure and lists every sorried constant reached).
- **Headers.** The frozen-statement check with its controls.
- **Rule 10 evidence.**
  - Whole-file seals A and B of every changed or new file over its full TCSlib import closure, at base and final,
    with **`-DmaxErrors=0`**.
  - Both the **strict** and the **coe** variant; **the coe-variant seal A is canonical**. Report every failing
    declaration in each and attribute every difference by reading its raw log.
  - Paired controls that pass unsealed and fail sealed, each sealed negative failing exactly once.
  - The explicit-unfold scan.
  - **Error counts (G26-N1), both forms.** Count both `error:` and `error(…)`, for example with
    `^\S+\.lean:\d+:\d+: error[:(]`, in every seal, control, sweep and probe log. Keep every raw log.
- **Lint.** Run `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography --check8b` at base and at final.
  The maintainer's baseline at the issue base is **92 FAIL / 101 WARN over 364 files**; the GSW files have no
  FAIL or WARN line. Diff the line sets, not only the counts: no new FAIL line, and no new WARN line except one you
  disclose and justify.
- **Name-clash scan.** No new name (public or private, namespaces resolved) may already be declared in `TCSlib/`
  at the issue base. Deliver the script and its output under `evidence/clash/`.
- **Report.** `REPORT.md` gives the base and the status of each target; who proved what; the changed files with
  lines at base and final, and the sketch edits; the new declarations; **Overlap and reuse**; **Scope requests**
  (none, or each with Seyoon's answer); promotion requests; the evidence, with its manifest.

### Evidence completeness

Gate 20 held a delivery for omitted raw evidence (G20-01).
- Every file that `evidence/SHA256SUMS` names must be delivered: seal and control sources, manifests and request
  records; the header check, its output and controls; the clash scan; the dependency trace; every raw log and
  `results.jsonl`; sub-agent logs; the probe sources and the tools used.
- If the evidence is too large for one commit, deliver it in several commits, or as numbered ZIP parts, each part
  with an entry list. Do not leave anything out for size.
- Check before delivery that the delivered paths are exactly the manifest's (top level and `evidence/`), with no
  leading `./`.

The maintainer checks `TCSlib` and `audits/pass-shelat/Checks` on the full-library tree at landing, after #332
and #333 merge.

**Ready to dispatch**

## ===== briefs/lattice-gsw/fills/gsw-security/issued-r1/brief.md =====

# Claude fill · column leftover hashing and IND-CPA of public-key GSW (`gsw-security`)

**Issue base** `486f44f8414c20a2d21e452c44de8b8c8d8513a0`, the head of draft PR #333 (branch `stmt/gsw`; Gate 41
CLOSED by disposition). It contains #332's commit `94eae71b779c4ca0f76c138d699f4d737dbd6cee` as an ancestor
(`486f44f8~3`). **Unit** `gsw-security`: fill units F5 and F6 of `briefs/lattice-gsw/plan-section.md` §G7 (lattice
campaign, phase 5). **Worker** Claude, a **single agent** (Seyoon's ruling, 2026-11-16). **Lean** 4.25.0 and the
Mathlib revision in that commit's `lake-manifest.json`.

Prove the 6 admitted, frozen statements of `TCSlib/Cryptography/Hashing/SIS/Columns.lean` and
`TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Security.lean`. They passed the phase-5 statement phase
and Gate 41, which accepted every target as true with the hypotheses it displays. Each docstring holds the
maintainer's proof sketch.

## Feasibility and size (maintainer's assessment)

Feasible. The six statements mirror the audited Regev PKE hybrids
(`Encryption/PublicKey/Regev/Experiments.lean`), with one new ingredient: a column-by-column hybrid over the
existing single-column leftover-hash bound. Gate 41 checked the hybrid and the final bound (two DLWE advantages
plus `2Nε`) by hand.

**Estimated size: about 270 lines** of proof (plan §G6): Columns about 130, Security about 140. The files are 89
and 217 lines now.

## Checkout and delivery

- Fetch `stmt/gsw` (or the commit itself). Start a local branch `fill/gsw-security` at the exact issue base, and
  record the base in `REPORT.md`. Keep the proof branch local.
- Read `policy.md`, the attached environment addendum and `README.md`.
- Deliver every checkpoint and the final payload under `inbox/fills/gsw-security/` on
  `exchange/pass-shelat-ch5-8`:
  - `REPORT.md`;
  - `patches/`: the whole `git format-patch` series from the issue base;
  - `patches/COMMITS.tsv`: one row per commit, giving its hash, the author's name, email and date, the
    committer's name, email and date, and its **signing** (`none`, or the signature format), so that `git am` at
    the base reproduces every hash. Commit with `git -c commit.gpgsign=false`; if a commit is signed anyway, say
    so in its row and in `REPORT.md`. Before you push, check the reproduction in a scratch clone and say so in
    `REPORT.md`;
  - `src/`: the changed and new files under their repository paths;
  - `evidence/`, with an `evidence/SHA256SUMS` manifest (see *Evidence completeness*);
  - a top-level `SHA256SUMS` listing every delivered file under `inbox/fills/gsw-security/` except itself. The
    delivered paths must **equal** the manifest's paths exactly: nothing missing, nothing extra, and no leading
    `./`. Check this before each push.
- Commit on the exchange as `fill gsw-security: checkpoint N` and `fill gsw-security: final`.
- Pull with rebase before pushing. Push only your delivery path, never force-push, and never touch another path
  (other fills, gates, the `arora-barak-ch3-4/` and `lwe-sis-constructions/` folders). If a push is refused,
  keep the commit and say so. Campaign changes land by a maintainer PR for Seyoon's approval.

## Base and parallel work

- **#332 (F0) and #333 are not merged.** #333 is stacked on #332; your base contains both. Neither F0 reader is
  needed here. #332 merges first, then #333, then the fills, rebased by the maintainer. If either changes or
  merges during the fill, **stay on the issue base**.
- **`gsw-core` runs in parallel** from the same base. It owns `GSW/{Gadget,Noise,Scheme,Symmetric,Eval}.lean`,
  which are in your order and which you never edit. **Proved-modulo:** you may cite their targets as frozen
  statements, exactly as stated. The expected route needs none of them (it uses only the `rfl` readers
  `encrypt_eq`, `view_eq`, … and the Regev, SIS and Foundations layers); if your proof does cite a `gsw-core`
  target, name it in the dependency trace.
- **F6 depends on F5 inside this job.** Prove F5 first (checkpoint 1); F6 may cite F5's statements meanwhile.

## Targets (frozen; quoted from the issue base)

6 declarations, each a `theorem` whose body is `sorry` (`base-sorries.txt`). Lines are at the issue base.

| Unit | File (lines at base) | Targets (declaration line) |
|---|---|---|
| F5 | `Hashing/SIS/Columns.lean` (89) | `hashColumns_eq_mul` (60), `distAdv_hashColumns_uniform_le` (78) |
| F6 | `AdvancedEncryption/Homomorphic/GSW/Security.lean` (217) | `real_uniformKey_advantage` (153), `uniformKey_uniform_advantage_le` (172), `distAdv_encrypt_le` (189), `distAdv_encrypt_le_of_width` (205) |

Counts: F5 2, F6 4; they equal plan §G7. The statements, with their docstrings and sketches, are in the files.
The column hybrid, for orientation:

```lean
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
```

`P` here is `TCSlib.Cryptography.SIS.Parameters` (note `P.columns` is the SIS column count, not GSW's `N`).

## Published interfaces (reuse first)

Read other files' definitions **only** through these readers (Rule 10). The list is a start, not a limit: search
for more before writing any lemma.

| Interface | Provider (path under `TCSlib/`, line at base) |
|---|---|
| `hashColumns_apply` (own file, F5) | `Cryptography/Hashing/SIS/Columns.lean` |
| `view_eq`, `realView_eq`, `uniformKeyView_eq`, `reduction_eq`, the `simps` readers of `view`, `realView`, `uniformKeyView` and `columnHashParameters` (own file, F6) | `…/GSW/Security.lean` |
| `Hashing.SIS.hash_eq` (49) | `Cryptography/Hashing/SIS/Basic.lean` |
| **`Hashing.SIS.distAdv_hash_uniform_le`** (166): the strong single-column LHL, valid for a test with independent coins | `Cryptography/Hashing/SIS/Universality.lean` |
| `encrypt_eq`, `gadget_apply`, `lift_apply`, `Parameters.columns_eq` | `…/GSW/Scheme.lean`, `…/GSW/Gadget.lean` (frozen, `gsw-core`'s) |
| `LWE.decisionAdvantage_eq` (53); `LWE.sample_fst`/`_snd` (`LWE/Basic.lean` 109, 116) | `Cryptography/LWE/Experiments.lean` |
| **`Regev.real_uniformKey_advantage`** (128), **`uniformKey_uniform_advantage_le`** (244), **`distAdv_encrypt_le`** (301): the pattern; `augmented_eq` (173), `augmented_bijective` (182), `encrypt_augmented` (199), `extractionError_eq` (232), `two_extractionError_le` (334); `hashParameters` (154, the Q11 twin) | `Cryptography/Encryption/PublicKey/Regev/Experiments.lean` |
| `acceptProb_def` (98), `distAdv_def` (102), `acceptProb_comp_equiv` (107), `distAdv_le_statDist` (173) | `Cryptography/Foundations/Experiments.lean` |
| `uprob_comp_equiv` (165), `uprob_prod` (153), `uprob_fst` (175), `abs_sub_le_sum_hybrids` (218), `exists_hybrid_gap` (230) | `Cryptography/Foundations/Probability.lean` |
| `acceptProb_fst`/`_snd` (73, 83), `acceptProb_bind` (91), `acceptProb_update` (103), `distAdv_comp` (141); `multicopyHybrid`, `multicopyRed` and `acceptProb_multicopyRed_left`/`_right` (the independent-copies relative of the column hybrid) | `Cryptography/Pseudorandom/Indistinguishability.lean` (an allowed extra import) |
| `columnHybrid`, `columnTest`, `column_gap` (82, 106, 138): a column hybrid under one public matrix, with DLWE gaps | `Cryptography/TrapdoorFunctions/Lossy/Experiments.lean` (pattern only) |
| `Matrix.mul_apply`, `Matrix.mulVec`, `dotProduct`, `Equiv.prodAssoc`, `Equiv.prodCongr`, `Equiv.addRight`, `Equiv.ofBijective`, `Real.sqrt_le_sqrt`, `Real.sqrt_mul_self` | Mathlib (search for the exact names at the pin) |

## Proof routes and checkpoints

The docstrings' sketches are the route; Gate 41 validated them.

**F5 · Columns** (2 targets).
- `hashColumns_eq_mul`: entrywise, `hashColumns_apply`, `hash_eq`, `Matrix.mul_apply` and `Matrix.of_apply`; both
  sides are the same binary-weighted sum. (Statement ruling QS1: the right side is `A * Matrix.of …`.)
- **`distAdv_hashColumns_uniform_le`.** Hybrid `H_j`: the first `j` columns of the second component are
  independent uniform columns and the rest are hashes of independent binary columns under the **same** public
  matrix; `H_0` is the real sampler and `H_N` the ideal one after relabelling seeds (`uprob_comp_equiv`,
  `acceptProb_comp_equiv`). `abs_sub_le_sum_hybrids` bounds the end-to-end gap by the sum of the `N` neighbouring
  gaps. Each gap is the advantage, between `(A, hash A r)` and `(A, u)`, of the test that plants its challenge
  column at `j`, samples the other columns itself with coins carried in its own randomness (a product of finite
  nonempty types), and runs `D`; `distAdv_hash_uniform_le` bounds it. Gate 41: the existing **strong** LHL applies
  despite the shared matrix, because the test receives `A`. At `N = 0` both samplers give the same distribution
  and the gap is 0. This is **not** a matrix leftover-hash lemma: make no universality claim for the whole-matrix
  family `R ↦ AR`.

**F6 · Security** (4 targets). Write `ε = Regev.extractionError P.lwe = ½·√(q^{n+1}/2^m)`.
- `real_uniformKey_advantage`: exact equality, as `Regev.real_uniformKey_advantage`. Reassociate the independent
  key, coin-matrix and distinguisher seeds (`uprob_comp_equiv` with `Equiv.prodAssoc`) on both sides, then
  `LWE.decisionAdvantage_eq` and `distAdv_def`. The reduction's coins are exactly the binary matrix coins paired with
  `D`'s coins.
- `uniformKey_uniform_advantage_le`: as `Regev.uniformKey_uniform_advantage_le`. Relabel the key by
  `Equiv.ofBijective _ (Regev.augmented_bijective _)`; the augmentation bijection retains the **entire** public key.
  The ciphertext is `hashColumns (columnHashParameters P) N Ā R + μG` (`encrypt_eq`, `hashColumns_eq_mul`,
  `lift_apply`); translation by `μG` is a bijection of the ciphertext space, so after relabelling both samplers the
  gap is that of `(Ā, ĀR)` versus `(Ā, U)`. Apply `distAdv_hashColumns_uniform_le` and rewrite its bound with the
  `columnHashParameters` readers and `extractionError_eq`. `columnHashParameters` is this file's own definition and
  may be read directly here; it is the disclosed Q11 twin of `Regev.hashParameters`, which you must not unfold.
- `distAdv_encrypt_le`: insert both uniform-key views and the common uniform view; the triangle inequality gives
  `|a_{μ₀} − a_{μ₁}| ≤ Adv(red_{μ₀}) + Adv(red_{μ₁}) + 2Nε` (two exact DLWE terms, two statistical terms), as
  `Regev.distAdv_encrypt_le`.
- `distAdv_encrypt_le_of_width`: `distAdv_encrypt_le` and `Regev.two_extractionError_le`, multiplied by `N ≥ 0`:
  `2Nε = N·√(q^{n+1}/2^m) ≤ N·2^{−κ}` when `q ≤ 2^w` and `(n+1)·w + 2κ ≤ m`.
- These are the concrete, fixed-bit, function-level statements of ruling Q8. Prove nothing about efficiency or the
  asymptotic `NUPPT` bridge, and assume no SIS hardness.

**Checkpoints** (each delivers whole proved declarations; at least one mid-way checkpoint is required):
1. **Checkpoint 1 · F5**: both Columns targets proved, with the module's checks, axiom prints and seals. Send it.
2. **Final · F6** and every target proved; the full checks below.

If a sketch is wrong, or a target is false as stated, stop that line of work and escalate with the exact
obligation: a checkpoint with the counterexample or the missing fact. **Do not weaken any statement**, add a
hypothesis or change a definition. A partial final is allowed only with each unproved target named and its exact
remaining obligation stated.

## Scope

**Owned files.** `Hashing/SIS/Columns.lean` and `AdvancedEncryption/Homomorphic/GSW/Security.lean`. In them you
may:
1. replace each target's `sorry` body;
2. rewrite each target's `**Proof sketch.**` paragraph to describe the delivered proof (the statement prose before
   it stays byte-identical);
3. add auxiliary declarations (lemmas, `private` or public) before their first use, each public one with a
   formula docstring, and list new public results under `## Main results`. Hybrid samplers or column tests, if you
   make them public definitions, land with `_eq` readers; prefer local `let`s or `private` definitions;
4. add precise `import` lines for Mathlib modules and for `TCSlib.Cryptography.Pseudorandom.Indistinguishability`
   (in `order.txt`). Fetch the cache for any new Mathlib root as the addendum says. Any other import needs a scope
   request. `Columns.lean` must not import anything under `AdvancedEncryption/`.

**The frozen-statement rule (binding; checked).** Every declaration present at the issue base in an owned file
stays in the same file and order, with its header byte-identical: attributes and modifiers (the `simps`
attributes included), keyword, name, binders and type, up to the `:=`, `by`, `where` or first `|` that begins the
proof. Every `def` (`hashColumns`, `view`, `realView`, `uniformKeyView`, `reduction`, `columnHashParameters`)
stays byte-identical, body included, and so do the readers and the `attribute [simps …]` line. Delete nothing. Keep
every `open`, `set_option` and the module title. Write a `python3 -I` script that extracts every declaration of the
owned files at base and at final, compares headers (and whole definitions) byte for byte, checks the order, and
prints the full diff; deliver it and its output under `evidence/headers/`, with zero unexpected differences. Add
two controls: one header altered by one character must report exactly one difference, and a deleted reader must
report exactly one removal.

**Helper modules.** Not expected. If one is needed, it goes under `Hashing/SIS/Columns/` or `GSW/Security/`, is
imported by that owned file only, and states its lemmas generically. The facades `Hashing/SIS.lean`,
`Hashing.lean`, `GSW.lean`, `Homomorphic.lean`, `AdvancedEncryption.lean` and `TCSlib.lean` are frozen.

**Frozen files.** Everything else, including `gsw-core`'s five GSW files, the SIS, LWE, Regev and Foundations files
and all facades.
- **Scope requests.** If the route needs a change to a frozen file (a reader beside a foreign definition, an
  import, a promotion), stop that line of work. Ask Seyoon in your session, giving the exact file, the diff and
  the reason, and go ahead only on his approval. Record the request and his answer verbatim under
  `evidence/scope-request/` and in `REPORT.md` § *Scope requests*. Seyoon prefers a route with no frozen-file edit.
- A lemma that belongs in an existing file goes in your owned file, with a promotion request. The generic column
  hybrid is meant for the shared hash layer, which is why it lives in `Columns.lean`; state any helper there
  generically.

## Sources and citations (DW-6, DW-7)

- The sources are [GSW13] (author version of 8 June 2013), [Pei16] (author version of 17 February 2016), [BV14]
  (ePrint 2013/541) and [Vad12, Theorem 6.18]. **GSW13 and BV14 are not ingested** (DW-7, Seyoon 2026-11-16:
  Markdown transcriptions of the passages used are added later by the maintainer), and the scoped Pei16 Markdown
  does not yet cover §6.1.3 (DW-7 also extends it later).
- You may rely on: the frozen docstrings' tags; the Gate 41 excerpts on the exchange,
  `outbox/gates/41-gsw-statements-gate/source-excerpts/{GSW13,BV14,Pei16}-excerpts.md` (SHA-256
  `b1241a90e4068e3f95a0bd80a2b4b497753d644e12c03fcd859be27cb70a4311`,
  `d83ffb1914e2e88956ce03d62e5a7f6a87b4c14af1ce25221da43c94ae139166`,
  `2b86ff971644029c715d748ac9425bcbed4c7a5ac3c2f4418a610d3c0ff11199`); and the committed raw extraction
  `blueprint/src/references/peikert2016-lattice-survey.raw.md` (§5.2.1 is also in the scoped `.md`).
- **Never fabricate a source excerpt, quotation or location.** A new declaration either is glue (no tag) or carries
  a tag whose passage is in those materials. Do not add reference files, edit `blueprint/` or run
  `scripts/sources.py`.
- **Small-secret LWE (A3, DW-6) is not used.** The DLWE instance has the GSW key's `m` rows and one common uniform
  secret. Introduce no normal-form assumption.

## Proof discipline

- **Size and width.** Every line has at most 100 characters (Python `len`), every file at most 1000 lines (policy
  target 150–600 per math file). Check both with a short `python3 -I` script before each push and put its output in
  `evidence/`.
- **Duplication (binding).**
  - **Search first.** Before writing any lemma, search `TCSlib/` and Mathlib for its statement shape and key names.
    Reuse published lemmas by importing them. The table above is a start; search further.
  - **Probability, advantage and hybrid lemmas first.** The undisclosed re-proofs that recent reviews and gates
    found were mostly of this kind (prf-mac F-01 `prfAdv_eq_expect`; learning `OneWay.uprob_eq_one_div_card`;
    G29-01 `OneWay.uexp_const`; G32-01 the `getD`/`headD`-of-`List.ofFn` family). Before writing any advantage,
    triangle, hybrid-sum, relabelling, push-forward, coin-planting or uniform-coordinate lemma, search for
    `uprob_*`, `uexp_*`, `acceptProb_*`, `distAdv_*`, `abs_sub_le_sum_hybrids`, `exists_hybrid_gap` and the
    multicopy family.
  - **Undisclosed copies of public lemmas are majors** (Gates 23, 24, 29, 32, 34).
  - **Nearest relatives here:** the Regev PKE hybrids (F6 restates them for GSW's ciphertext space, which Gate 41
    accepted as not duplicate); `Lossy.column_gap` and the multicopy hybrid (F5's hybrid); and
    `Regev.hashParameters`, of which `columnHashParameters` is the disclosed Q11 copy.
  - **Private lemmas.** Never copy a private lemma silently. If you need one, re-derive it from published readers,
    keep its statement general, and disclose it.
  - **Disclose every overlap.** `REPORT.md` has a section **`## Overlap and reuse`**. For every new declaration
    (and every inline `have` re-proof) that restates, specializes or re-proves existing material (public or
    private, TCSlib or Mathlib), give its nearest relative (`path:line`), the relation, and why it is not reused.
    List the searches you ran.
- **Docstrings and sketches.** Do these yourself:
  - every new public declaration has a docstring that states its formula, with its arguments in the Lean order, and
    a source tag only as *Sources and citations* allows;
  - every proof of 15 lines or more carries a `**Proof sketch.**` paragraph, and long proofs get step comments
    (policy §3); each target's sketch describes the delivered proof;
  - a new public `def` lands with its `_eq`, `_iff` or `simps` readers (lint check 8);
  - add no `@[simp]`, and no global attribute.
- **Rule 10.**
  - Use only published readers for other files' definitions, including generated matchers and projections (the
    table above). Core and Mathlib definitions may reduce in a `rfl`, `decide` or `show` step but are never passed to
    `simp`, `rw` or `unfold`; use their equation lemmas.
  - Each owned file may read **its own** definitions directly. `Columns.lean` and `Security.lean` are foreign to each
    other (Security reads `hashColumns` only through `hashColumns_apply`/`hashColumns_eq_mul`), and both are
    foreign to `gsw-core`'s files (`encrypt` through `encrypt_eq`, `gadget` through `gadget_apply`).
  - **Type-level Rule 10 (plan §G8).** Matrix index types must never be reached by unfolding another file's
    definition: never unfold `Regev.hashParameters`, `Regev.augmented`, `LWE.sample` or `distAdv`/`acceptProb` at
    the type level. The seal must cover `Regev.augmented`, `LWE.sample` and the SIS `hash`.
  - **Notation, never sealed:** reducible abbreviations (here GSW's `Parameters.columns` and `Ciphertext`),
    `PolyExpr.eval`, and projection coercions (a `CoeFun`/`Coe` whose body is a structure projection; Seyoon,
    2026-11-14).
  - Identifiers use the Greek `μ` (U+03BC); never the micro sign `µ` (U+00B5).

## Checks and report

- **Bootstrap.** From `order.txt` (147 modules) and the narrow `roots.txt` (84), following the addendum. The order
  is the upstream closure of the modules downstream of your two owned files (they include the `Hashing` and
  `AdvancedEncryption` facades; root `TCSlib` excluded) and of `Pseudorandom/Indistinguishability`. Check one
  module per `scripts/lean_check_tree.sh` call, one Lean process at a time on the host. **Never run `lake build`**
  or an unfiltered `lake exe cache get`. Run Python as `python3 -I`. Insert any helper module before its consumer.
- **Per-module native check and sweep.** Check each owned module after each change. Before each delivery,
  recheck both owned modules and sweep the whole order with 0 errors.
- **Admissions.** Compare the `sorry` warnings with `base-sorries.txt` (53 declarations in 15 modules: the 35 GSW
  targets and 18 complexity-layer admissions). At the final the only change is the removal of your 6 targets (47
  in 13 modules). A checkpoint lists exactly which targets it removed.
- **Axioms.** Print the axioms of every target and of every stored constant of the changed files. At the final
  expect only `propext`, `Classical.choice` and `Quot.sound`. Run a **dependency trace** (a probe that walks the
  constant closure and lists every sorried constant reached); it should reach none, and any `gsw-core` target it
  reaches must be named.
- **Headers.** The frozen-statement check with its controls.
- **Rule 10 evidence.**
  - Whole-file seals A and B of every changed or new file over its full TCSlib import closure, at base and final,
    with **`-DmaxErrors=0`**.
  - Both the **strict** and the **coe** variant; **the coe-variant seal A is canonical**. Report every failing
    declaration in each and attribute every difference by reading its raw log.
  - Paired controls that pass unsealed and fail sealed, each sealed negative failing exactly once.
  - The explicit-unfold scan.
  - **Error counts (G26-N1), both forms.** Count both `error:` and `error(…)`, for example with
    `^\S+\.lean:\d+:\d+: error[:(]`, in every seal, control, sweep and probe log. Keep every raw log.
- **Lint.** Run `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography --check8b` at base and at final.
  The maintainer's baseline at the issue base is **92 FAIL / 101 WARN over 364 files**; the two owned files have no
  FAIL or WARN line. Diff the line sets, not only the counts: no new FAIL line, and no new WARN line except one you
  disclose and justify.
- **Name-clash scan.** No new name (public or private, namespaces resolved) may already be declared in `TCSlib/`
  at the issue base. Deliver the script and its output under `evidence/clash/`.
- **Report.** `REPORT.md` gives the base and the status of each target; the changed files with lines at base and
  final, and the sketch edits; the new declarations; **Overlap and reuse**; **Scope requests** (none, or each with
  Seyoon's answer); promotion requests; the evidence, with its manifest.

### Evidence completeness

Gate 20 held a delivery for omitted raw evidence (G20-01).
- Every file that `evidence/SHA256SUMS` names must be delivered: seal and control sources, manifests and request
  records; the header check, its output and controls; the clash scan; the dependency trace; every raw log and
  `results.jsonl`; the probe sources and the tools used.
- If the evidence is too large for one commit, deliver it in several commits, or as numbered ZIP parts, each part
  with an entry list. Do not leave anything out for size.
- Check before delivery that the delivered paths are exactly the manifest's (top level and `evidence/`), with no
  leading `./`.

The maintainer checks `TCSlib` and `audits/pass-shelat/Checks` on the full-library tree at landing, after #332
and #333 merge.

**Ready to dispatch**

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

## ===== briefs/lattice-gsw/gates/41-gsw-statements/resolutions-r1.md =====

# Gate 41 · resolutions, round 1 · CLOSED by disposition

Codex:
- **#332, the DAGCircuit readers:** CLEAR, 0/0/0/0.
- **#333, GSW:** HOLD, 0/1/3/2.
- **Findings:** `findings/gate41-gsw-statements-findings.md`, SHA-256 `f9d90b3545a63ce438dab5e9889d39639cf775443304fc12c3c0d10727497bf6`. The evidence ZIP was not supplied.
- **Audited heads:** #332 `94eae71b` and #333 `48d796a8`; records `86d19094`; exchange `c72de14a`.

**Mathematics.** All 35 GSW targets are accepted as true with the hypotheses they display. That covers:
- the asymmetric `Nβ₁+|x₁|β₂` bound and the chain bound `β₀+kNβ`;
- `homAnd` and `homGate`, at arities 0, 1 and 2;
- the depth bound `(N+1)^depth·β`;
- the decryption separation, including odd `q` and `q` = 2 or 3;
- the leveled condition, which needs no extra factor and no `L+1`;
- the column-LHL hybrid, and IND-CPA as two DLWE advantages plus `2Nε`.

The two #332 proofs (`getD_lt_depth`, `runWith_rel`) are sound. `runWith_sim` can be derived from `runWith_rel`. The phase-6/7 hooks fit BV14: a selector step costs an additive `2Nβ`.

| # | Severity | Disposition |
|---|---|---|
| G41-01 | major | **Closed by Seyoon's explicit superseding disposition.** Ruling of 2026-11-16, made after this gate's pin and recorded as **DW-7** in `briefs/pass-shelat-ch5-8/deferred-work.md`: the GSW13 ingest from Q14 is deferred in the same way as pairings Q12, to Markdown transcriptions of only the passages used, added later. Seyoon also ruled to close this gate by disposition. |
| G41-02 | minor | **Fixed.** `homAnd` is described as a right-associative product chain, with each head multiplied on the left. Fixed in commit `486f44f8` (LE-gate41, docstring only). |
| G41-03 | minor | **Fixed** in the same commit. `eval_encrypts` now states output correctness, with the every-vertex invariant described as an intermediate step. The code is identical once doc comments are stripped, and the widest line is 95 characters. |
| G41-04 | minor | **Fixed (records).** `plan-section.md` now uses the `AdvancedEncryption/Homomorphic/GSW/` paths, with a status note. |
| G41-N1 | note | Extending the scoped Pei16 Markdown is part of DW-7. |
| G41-N2 | note | The #333 PR description's Gadget summary is corrected. |

Codex also noted that AP14's printed `gᵀ⊗I_n` differs from the code's `I_n⊗gᵀ` by a column permutation. The code matches AP14's block-diagonal description and Pei16. This is not an undisclosed change.

**Gate 41 is CLOSED** (Seyoon's ruling: close by disposition, no round 2).

**Merge conditions:**
- Merge #332 before #333.
- After the merges, rebuild the downstream of `DAGCircuit`: 281 modules for #332 and 291 for #333.
- Whichever of #331 and #333 merges second takes the union of the `AdvancedEncryption.lean` and `TCSlib.lean` facades.
- Rebuild the modules shared with #324 and #327 (16 and 41 modules).

## ===== briefs/lattice-gsw/gates/41-gsw-statements/findings/gate41-gsw-statements-findings.md =====

# Gate 41 — GSW statement audit

**Disposition: PR #332 CLEAR; PR #333 HOLD.** The hold is the unfulfilled Q14 source-ingestion requirement. I found no false target, missing mathematical hypothesis, or off-by-one in the 35 GSW statements. The two new #332 proofs are sound on inspection and have the standard-axiom dependencies recorded below.

| Scope | Blocker | Major | Minor | Note |
|---|---:|---:|---:|---:|
| PR #332 | 0 | 0 | 0 | 0 |
| PR #333, including its campaign records | 0 | 1 | 3 | 2 |
| Total | **0** | **1** | **3** | **2** |

This is a statement audit of #333, not a proof-completion claim: its 35 targets still contain `sorry`. I reviewed #332's two completed proofs as proofs. I authenticated and inspected the supplied build, axiom, and seal evidence; I did **not** run a new Lean elaboration. No repository files, PRs, or merge state were changed. The specified facade conflict and merged-tree rebuilds are excluded from the audit, as dispatched.

## Audited material and integrity

| Item | Pinned revision |
|---|---|
| Exchange | `c72de14a98d2ad107600323b171985017465e33a` |
| Campaign records | `86d19094aafecc1e19d208c6629b179cfdd14009` |
| [PR #332](https://github.com/Shilun-Allan-Li/tcslib/pull/332) | `94eae71b779c4ca0f76c138d699f4d737dbd6cee` |
| [PR #333](https://github.com/Shilun-Allan-Li/tcslib/pull/333) | `48d796a8a68cd50897047f01825a8132dd19e8d8` |
| Common base | `523d80d2d4dd8e4ed6799358831e5b3806c6187b` |

I read `README.md`, `pack.md`, every section of `bundle.md`, the rulings and statement-text decisions, the 118-file source closure as needed for dependencies, and the four supplied source excerpts. Independent checks passed:

- Outer `SHA256SUMS`: **15/15**; verification archive: **73/73** hashes, with exactly the listed files plus its manifest.
- Inner statement archive: **545/545** hashes; **546 files including the manifest**. All 32 furnished evidence extracts match the inner archive byte for byte. Directory entries are not counted as files.
- All **118 source files** match Git blob IDs in #333's pinned tree; all **21 bundle sections** match the Git objects named by `BUNDLE-FILES.txt`.
- The 7 verification-record copies match their disclosed pre-pin revision `aacfa40b…`; only the plan and `EVIDENCE.md` have append-only additions at the pinned records revision. The bundle supplies the pinned versions. The 8 context files match their disclosed context tip. The three filed statement-evidence objects match the pinned records.
- `48d796a8~2 = 94eae71b`; the DAGCircuit blob is identical at both heads. The supplied 84,963-byte diff matches the pinned base-to-head diff with `--abbrev=9`; SHA-256 `f577be74b52ea7607d9bdfbb87033402cc5dce6460ccf651418dee52fdf3de53`.
- Source inventory: 13 changed files, 35 target admissions, maximum line width 100, maximum file length 721.

The source comparison uses the excerpts requested in the dispatch. The cited PDF hashes are provenance claims in the pack; the PDFs are absent, so I did not independently rehash or inspect those PDFs. The committed Pei16 raw text and the supplied scoped excerpts suffice for the mathematical comparison here.

## Findings, marked by PR

Paths abbreviated as `GSW/…` below are under `TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/`.

| ID | Severity | PR · file · declaration | Claim and evidence | Proposed fix |
|---|---|---|---|---|
| **G41-01** | **major** | **#333** · source ingestion; `briefs/lattice-gsw/rulings.md`, Q14; `questions.md:147` | Q14-A expressly requires GSW13 ingestion into `blueprint/src/references/` **in the phase-5 statement PR**. The pinned diff adds no reference-ingestion files. The statement evidence and pack explicitly acknowledge that ingestion is unfinished. Excerpts make this audit possible but do not satisfy the accepted ingestion requirement or policy §2. No later waiver appears in the supplied rulings. | Complete the approved GSW13 ingestion/reference registration and provide its evidence, or obtain an explicit superseding disposition from the user. This is an unmet gate obligation, not a mathematical defect. |
| **G41-02** | **minor** | **#333** · [Eval.lean:57–63][eval] · `homAnd` | Its declaration docstring says “left-to-right product chain.” The recursion is **right-associative**, with the head on the left: `mul C₁ (mul C₂ C₃)`. Associativity/order matters for the additive noise analysis; the module docstring and recursion otherwise describe the intended operation correctly. | Say “right-associative product chain, with each head multiplied on the left.” |
| **G41-03** | **minor** | **#333** · [Eval.lean:164–184][eval] · `eval_encrypts` | The docstring says the theorem establishes the depth-indexed invariant at **every vertex**. Its exported conclusion establishes it only at the circuit output. The stronger assertion is a valid intermediate invariant in the sketch, but is not the statement being published. | State output correctness in the opening prose; describe the every-vertex invariant as an intermediate step in the proof sketch. Alternatively, publish the stronger auxiliary result deliberately. |
| **G41-04** | **minor** | **#333 / records** · `briefs/lattice-gsw/plan-section.md`, especially §G8 and §G10 | The accepted Q9 location is implemented correctly in Lean, but the proposed organization row still says `Encryption/Homomorphic/GSW/`; related facade/import prose retains the old location. The proposed organization and phase rows have not been incorporated into the main plan. The main decision log does record the correct ruling, so this is documentation drift. | Replace the obsolete paths with `AdvancedEncryption/Homomorphic/GSW/` and synchronize the pending plan tables with the actual phase-5 state. |
| **G41-N1** | **note** | **#333 / records** · Pei16 source coverage | The scoped `peikert2016-lattice-survey.md` lacks the newly cited §5.4.3/§6.1.3 passages; the committed raw extraction and gate excerpts contain them. Thus the citations can be checked here, and this is not a second source-fidelity hold. | Extend the scoped reference/anchors when integrating source matching for these declarations. |
| **G41-N2** | **note** | **#333** · PR description, Gadget summary | “The digit bounds” is an imprecise summary of the five target statements. They are digit recovery, two reconstruction identities, zero-block decomposition, and the single-block error-sum bound. The digit range itself is enforced by `digit`'s type and `Parameters.modulus_le`. | Use those five descriptions in the PR body. No signature change is needed. |

## PR #332: completed proofs and shared API

The diff adds the approved four readers, `DAGGate.getD_lt_depth`, `runWith_rel`, and their module documentation. It changes no existing definition or theorem statement. The readers are the expected `rfl` equations.

For `DAGGate.getD_lt_depth`, membership in the argument list gives

\[
\mathrm{ds.getD}(a,0)
\le \operatorname{foldr}\max\,0\,[\mathrm{ds.getD}(v,0):v\in g.\mathrm{args}]
<1+\operatorname{foldr}\max\,0\,[\mathrm{ds.getD}(v,0):v\in g.\mathrm{args}]
=g.\mathrm{depth}(\mathrm{ds}).
\]

The first inequality is exactly the list induction in the submitted proof: membership in the head uses `le_max_left`; membership in the tail uses the induction hypothesis and `le_max_right`. The strict inequality is natural-number successor arithmetic. Out-of-range reads are also covered because the formula uses `getD` throughout.

For `runWith_rel`, strong induction on the vertex is valid:

1. Below `initA.length`, both runs retain their input entries by `runWith_getD_of_lt`; `hlen` aligns the second run, and `hinit` supplies the relation.
2. Otherwise write the vertex as `initA.length + i`. Its range hypothesis implies `i < gs.length`. Both `runWith_getD_gate` equations read the prefix of exactly `i` gates; both prefixes have length `initA.length + i`.
3. Every argument is strictly earlier by `hacyc`. The induction hypothesis relates its entries in the full runs; `runWith_getD_take` transports those entries to the two prefixes. These are precisely the premises of `hgate`.

There is no requirement that the evaluators depend only on their argument entries: `hgate` already quantifies over arbitrary prefix lists with the required lengths. There is also no assumption about related out-of-range defaults; acyclicity keeps all queried arguments in range.

The relation may depend on the vertex, so it supports the depth-dependent invariant in GSW. Garbling's `runWith_sim` follows by taking `R v a b := (b = W v a)` and taking the second evaluator to be `fun g vs => fB vs.length g vs`. Its prefix-length premise turns `vs.length` into the gate's vertex number. The disclosed later deduplication is therefore viable.

The supplied axiom dump gives:

| Declaration | Dependencies |
|---|---|
| `DAGGate.getD_lt_depth` | `Quot.sound`, `propext` |
| `runWith_rel` | `Classical.choice`, `Quot.sound`, `propext` |

Neither proof reads another TCSlib definition by unfolding it. **No #332 finding.**

## PR #333: all 35 targets

Each row below is accepted as mathematically true with its displayed hypotheses. “Accepted” does not mean its Lean `sorry` has been discharged. The row numbers are the plan's target numbers.

| # | File · target | Reason |
|---:|---|---|
| 1 | Gadget · `digits_decomposeVec` | `blocksEquiv` composed with its inverse recovers the digit vector. |
| 2 | Gadget · `gadget_mulVec_decomposeVec` | Each gadget block evaluates the positional digits of the canonical residue; casting back recovers it. |
| 3 | Gadget · `gadget_mul_decompose` | Target 2 column by column; no finiteness hypothesis on the column index type is needed. |
| 4 | Gadget · `decomposeVec_block_eq_false` | A nonnegative positional sum equal to zero has every bit zero. |
| 5 | Gadget · `errorSum_decomposeVec_le` | Only one block survives; its ℓ binary-selected terms each have magnitude at most β. |
| 6 | Noise · `encrypts_gadget` | Error witness zero, message 1. |
| 7 | Noise · `encrypts_zero` | Error witness zero, message 0. |
| 8 | Noise · `Encrypts.mono` | Reuse the same error witness. |
| 9 | Noise · `Encrypts.add` | Add error witnesses; triangle inequality. |
| 10 | Noise · `Encrypts.neg` | Negate the error witness; absolute value unchanged. |
| 11 | Noise · `Encrypts.sub` | Subtract error witnesses; triangle inequality. |
| 12 | Noise · `Encrypts.sum` | Finite induction using targets 7 and 9. |
| 13 | Noise · `Encrypts.mul` | Exact witness `e₁ᵀX + x₁e₂ᵀ`, bounded by `Nβ₁ + |x₁|β₂`; see below. |
| 14 | Noise · `Encrypts.mul_bit` | A bit on the left has integer absolute value at most 1. |
| 15 | Noise · `Encrypts.mul_le` | Bit multiplication is conjunction; `Nβ + β = (N+1)β`. |
| 16 | Noise · `Encrypts.nand` | Subtract the product from noiseless G; `1 − b₁b₂` is the NAND bit. |
| 17 | Noise · `encrypts_chain` | List induction adds `Nβ` per fresh left factor; `Forall₂` supplies equal lengths. |
| 18 | Scheme · `vecMul_secretVector_augmented` | `−⟨s,aᵢ⟩ + (⟨aᵢ,s⟩ + eᵢ) = eᵢ`. |
| 19 | Scheme · `encrypts_encrypt` | Fresh error is `eᵀR`; every column is a binary subset sum of m errors. |
| 20 | Scheme · `encrypts_keygen_encrypt` | Read existing keygen/sample projections; `χ.Bounded B` bounds each realized row error. |
| 21 | Scheme · `decrypt_of_encrypts` | Regev residual is the bit codepoint plus a single-block error of magnitude at most ℓβ. |
| 22 | Scheme · `decrypt_of_encrypts_dyadic` | For `q = 2^ℓ`, the half-codepoint decomposition has one nonzero bit, so the error bound is β. |
| 23 | Scheme · `decrypt_keygen_encrypt` | Targets 20 and 21. |
| 24 | Eval · `homAnd_encrypts` | Empty/singleton bases and the right-associative product recurrence; natural subtraction is correct. |
| 25 | Eval · `homGate_encrypts` | Conjunction, negated conjunction, and De Morgan; fan-in at most two costs `(N+1)β`. |
| 26 | Eval · `eval_encrypts` | The vertex-indexed relation and strictly smaller argument depths give the depth induction below. |
| 27 | Eval · `decrypt_keygen_eval` | Fresh bound `mB`, target 26, depth monotonicity, then target 21. |
| 28 | Columns · `hashColumns_eq_mul` | Both entries are the same binary-weighted sum; the QS1 `Matrix.of` is correct. |
| 29 | Columns · `distAdv_hashColumns_uniform_le` | A hybrid replaces one independent column at a time; each neighboring gap is bounded by the existing strong single-column LHL. |
| 30 | Security · `real_uniformKey_advantage` | Reassociate the independent key, encryption, and test coins; equality with the stated DLWE advantage is exact. |
| 31 | Security · `uniformKey_uniform_advantage_le` | Augmentation is a bijection; use target 29 and the ciphertext translation by μG. |
| 32 | Security · `distAdv_encrypt_le` | Triangle inequality through both uniform-key views and a common uniform view. |
| 33 | Security · `distAdv_encrypt_le_of_width` | `Regev.two_extractionError_le` multiplied by N. |
| 34 | Symmetric · `encrypts_symEncrypt` | Reindex the augmented sample's error coordinates; each keeps bound B. |
| 35 | Symmetric · `distAdv_symEncrypt_le` | Each uniform DLWE sample maps bijectively onto the whole ciphertext batch; insert that common uniform distribution. |

### Noise calculations and boundary cases

All residue equalities below are modulo q. The error witnesses and their bounds are over the integers. Put `X = lift (decompose C₂)`, so its entries are 0 or 1 and `GX = C₂`. From the two `Encrypts` witnesses,

\[
\begin{aligned}
t^{\mathsf T}(C_1X)
&=(x_1t^{\mathsf T}G+e_1^{\mathsf T})X\\
&=x_1t^{\mathsf T}C_2+e_1^{\mathsf T}X\\
&=x_1x_2t^{\mathsf T}G+x_1e_2^{\mathsf T}+e_1^{\mathsf T}X,\\
\left|\sum_i e_{1,i}X_{ij}+x_1e_{2,j}\right|
&\le\sum_i |e_{1,i}|X_{ij}+|x_1|\,|e_{2,j}|\\
&\le N\beta_1+|x_1|\beta_2.
\end{aligned}
\]

This also covers negative integer messages. No noise independence or fresh-encryption hypothesis is needed. For a bit on the left, weaken `|x₁|` to 1. Subtraction from G negates the resulting error without increasing its bound.

For the right-associative chain of k fresh bit factors and an accumulator of bound β₀, the induction step is

\[
N\beta+\bigl(\beta_0+kN\beta\bigr)=\beta_0+(k+1)N\beta.
\]

The empty chain is exactly the accumulator and the empty Boolean product is 1. The message is consequently `(bs.all id).toNat * x`. No restriction on the integer accumulator message is missing.

For `homAnd` on k entries, the declared bound is

\[
\bigl(\max(k-1,0)N+1\bigr)\beta.
\]

At k = 0 the actual noise is zero and the displayed bound is β; at k = 1 it is β. At k ≥ 2 the recurrence is

\[
N\beta+\bigl((k-2)N+1\bigr)\beta=((k-1)N+1)\beta.
\]

Thus k ≤ 2 gives at most `(N+1)β`. Complementing a bit ciphertext as `G − C` preserves its noise bound. This proves the disjunction and negated-conjunction cases too, including arities zero and two for the library's `.not` gate. Repeated arguments are harmless. `homGate_encrypts` explicitly assumes its argument relations; mismatched list lengths need no extra hypothesis. Its default false/zero pair is consistent because zero encrypts zero noiselessly.

For a gate of depth d, each argument has depth at most d−1 and d ≥ 1. Since N+1 ≥ 1,

\[
(N+1)^{\operatorname{depthAt}(a)}\beta
\le (N+1)^{d-1}\beta,
\qquad
(N+1)\bigl((N+1)^{d-1}\beta\bigr)=(N+1)^d\beta.
\]

Inputs have depth zero. Apply `runWith_rel` with the depth-indexed `Encrypts` relation and read the in-range output. Acyclicity comes from `Cc.args_lt`; full `IsFaninTwo` is unnecessary. Counting negation gates in `depth` only makes the sufficient bound larger. Dead gates do not invalidate an output-depth bound because the invariant is proved separately at each vertex.

For decryption let `w = halfVector P` and let z be its lifted binary decomposition. Then

\[
Gz=w,\qquad t^{\mathsf T}w=\lfloor q/2\rfloor,
\]

\[
\begin{aligned}
\text{Regev residual}
&=t^{\mathsf T}Cz\\
&=b\lfloor q/2\rfloor+\sum_i e_i z_i,\\
\left|\sum_i e_i z_i\right|&\le\ell\beta.
\end{aligned}
\]

All blocks of z except the last vanish. The two codepoints have circular distance `floor(q/2)`. Under `2ℓβ < floor(q/2)`, the received residue is at distance at most ℓβ from its intended codepoint and at distance at least `floor(q/2) − ℓβ > ℓβ` from the other. This is exactly the existing `decode_codepoint_add` premise, including odd q and signed errors. There is no rounding or tie-rule gap.

For `q = 2^ℓ`, z has its sole 1 at block n, position ℓ−1 with zero-based indices. The noise bound is β and the condition becomes `2β < q/2`. `hℓ : 0 < ℓ` is redundant because `q ≥ 2` and `q = 2^ℓ` imply it; retaining it is harmless. More generally `q ≥ 2` and `q ≤ 2^ℓ` already exclude ℓ = 0. At q = 2 or 3 the general separation premise forces β = 0, and decoding is correct. B = 0, m = 0, and depth zero cause no exception.

Fresh encryption has error `eᵀR`, bounded by mB. Therefore `Cc.depth ≤ L` gives

\[
\beta_{\rm out}\le (N+1)^{\mathrm{Cc.depth}}mB
\le (N+1)^L mB,
\]

and the declared condition

\[
2\bigl(\ell((N+1)^L mB)\bigr)<\lfloor q/2\rfloor
\]

is sufficient for every key-generation seed and encryption coin matrix. No extra factor or `L+1` is required.

### Security calculations

For target 29, use hybrids whose first j ciphertext columns are independent uniform columns and whose remaining columns are independent binary hashes under the same public matrix. In each neighboring pair, the test receives the public matrix and one challenge column, samples every other column itself, and runs D. The existing **strong** LHL applies despite the shared matrix. The triangle inequality yields N times the single-column error. At N = 0 both samplers give the same public-matrix distribution and the gap is zero. This does not assert universality of the whole-matrix hash family.

With `ε = Regev.extractionError P.lwe`,

\[
\varepsilon=\tfrac12\sqrt{q^{n+1}/2^m}.
\]

Let `a_μ`, `u_μ`, and `p_unif` be D's acceptance probabilities on the real view of μ, the uniform-key view of μ, and the fully uniform key/ciphertext pair. Reassociating product seeds gives

\[
|a_\mu-u_\mu|=\operatorname{DLWEAdv}(\operatorname{reduction}_\mu D),
\qquad |u_\mu-p_{\rm unif}|\le N\varepsilon.
\]

The reduction's coins are exactly the independent binary matrix coins paired with D's coins. The augmentation bijection retains the **entire public key**; translation by μG is a ciphertext-space bijection. Hence

\[
\begin{aligned}
|a_{\mu_0}-a_{\mu_1}|
&\le |a_{\mu_0}-u_{\mu_0}|+|u_{\mu_0}-p_{\rm unif}|
  +|p_{\rm unif}-u_{\mu_1}|+|u_{\mu_1}-a_{\mu_1}|\\
&\le\operatorname{DLWEAdv}(\operatorname{reduction}_{\mu_0}D)
 +\operatorname{DLWEAdv}(\operatorname{reduction}_{\mu_1}D)+2N\varepsilon.
\end{aligned}
\]

If `q ≤ 2^w` and `m ≥ (n+1)w + 2κ`, then

\[
2N\varepsilon
=N\sqrt{q^{n+1}/2^m}
\le N\sqrt{2^{-2\kappa}}=N2^{-\kappa}.
\]

The statements are exactly the concrete, fixed-bit function-level claims approved by Q8. They do not establish the deferred efficient asymptotic primitive bridge. The statistical claims require no SIS hardness assumption.

For symmetric encryption, `m = kN` and `rowEquiv` partition all challenge rows into exactly k blocks. Augmentation, column reindexing, and translation by the chosen message vector form a bijection from a uniform challenge `(A,b)` to a uniform batch of k ciphertexts. Its inverse subtracts the message gadgets, assembles all columns through `rowEquiv`, and inverts augmentation. Thus both ideal message experiments have the same distribution, giving exactly the two displayed DLWE advantages. One common secret and all kN row errors are retained in the real experiment; no hidden independent-key assumption occurs. The empty batch also satisfies the statement.

## Fidelity, reuse, Rule 10, and roadmap

The construction is faithful to the disclosed gadget presentation. GSW13's square, flattened ciphertexts become rectangular gadget ciphertexts after the disclosed decompression/transposition and coordinate reordering. AP14 and Pei16 support the displayed left-vector invariant and multiplication algebra. The following differences are expressly disclosed: deterministic binary decomposition instead of AP14's randomized subgaussian decomposition; worst-case bounded integer errors; arbitrary sufficient gadget width; uniform secrets; the optional symmetric unit; and the Regev-based half-codepoint decryptor with its factor ℓ. The results do not claim the sources' Gaussian bounds or lattice approximation-factor theorems.

There is one source-notation point to resolve explicitly in reading the excerpts: under the standard Kronecker convention, AP14's printed `gᵀ ⊗ I_n` is **not literally** the displayed `diag(gᵀ,…,gᵀ)`. It differs by a column permutation. The code uses `I_n ⊗ gᵀ`, matching AP14's accompanying block-diagonal description and Pei16's formula exactly. I do not treat the reversed Kronecker expression as an undisclosed construction change. It is not correct to call the two Kronecker products entrywise identical without mentioning the permutation.

The operand mirroring is correct **with product order reversed under transposition**. GSW13/BV14 expand the right operand's error; AP14/the code expand the left operand's error. Accordingly, fresh ciphertexts belong on the left in the code's additive chains. The code does not assert that the two conventions produce identical ciphertexts in the same operand order.

Reuse is appropriate: the code consumes `LWE.Parameters`, noise/sample readers, binary subset-sum bounds, the existing bit decoder, Regev keygen/augmentation/decryption/extraction error, `Lossy.gadget` and its digit lemmas, `Randomized.blocksEquiv`, and the SIS single-column LHL. The `columnHashParameters` definition is the disclosed field-for-field Q11 copy; Q11 already authorizes it. The GSW security statements concern a different ciphertext space and are not duplicate public results merely because they mirror Regev's hybrid pattern. No further undisclosed duplicate was found. The generic column hybrid is placed in the shared hash layer, and the relational evaluator is placed in the circuit layer.

The Q9 namespace and file location are correct. The new facades import and list their children; the hash facade and `TCSlib.lean` export the additions. Imports are precise. The Q10 cross-topic gadget import is intentional. QS1's `Matrix.of` and QS2's qualified `GSW.mul` preserve the drafted meanings. The 23 `UNCHECKED` uses and F1–F4 resolutions are supported by the statement/API evidence; F3 and F4 are sketch-name corrections.

Every target has a sketch and the source anchors match the supplied passages: AP14 Definitions 3.2–3.3, Claim 3.4, Lemma 3.5, Corollary 3.6; GSW13 §3.3 and Lemma 1; BV14 Claims 3.4.1–3.4.2 and Lemma 3.6; Pei16 (6.1.4)–(6.1.7). The key-agnostic `Encrypts` predicate is broader than AP14's provenance-based “designed to encrypt” relation, as its documentation explains; the algebra and conditional correctness remain valid for that broader relation.

The authenticated supplied evidence records 12/12 final module checks and 278/278 root-closure checks with zero errors. Its axiom inventory has 285 declarations and 56 auxiliary constants, with `sorryAx` in exactly the 35 target rows. Its four seal variants total 48/48 successes. The sealed negative-control file fails at each of the five intended reads; the unsealed and positive controls pass. These establish the recorded behavior of the current statement surface and #332 proofs, not Rule 10 compliance of future target fills. Inspection of the new completed proofs and readers finds no forbidden read.

The phase-6/7 hooks fit the ruled BV14 roadmap. In particular, let C encrypt the selector bit b with noise β, and let `V₀,V₁` be the accumulated branch ciphertexts with noise at most β₀. The mirrored update is

\[
(G-C)\mathbin{\mathrm{mul}}V_0+C\mathbin{\mathrm{mul}}V_1.
\]

Targets 9 and 13 give its bound

\[
N\beta+(1-b)\beta_0+N\beta+b\beta_0
=\beta_0+2N\beta\qquad(b\in\{0,1\}).
\]

Thus k steps cost at most an additive `2kNβ`. The exact `|x₁|β₂` term is essential: replacing both products prematurely by `mul_bit` would unnecessarily double the accumulated bound. Worst-case analysis needs neither fresh noise independence nor BV14's probabilistic rerandomization guarantee. It incurs larger polynomial factors, which are disclosed and do not obstruct a polynomial ratio.

The decryptor's public column preprocessing leaves a modular inner product and rounding as the secret-dependent circuit, so the chosen circuit model and uniform-secret convention introduce no evident phase-6 obstruction. Barrington/PBP machinery, a decryption circuit with its depth bound, compactness/efficiency, weak circular security, and the asymptotic security bridge remain later obligations already identified by the roadmap. Phase 5 does not silently prove them or assume circular security from LWE. The accepted later small-secret-LWE assumption is unnecessary for this phase or the selected BV14 route.

## Evidence archive and notation

`gate41-gsw-statements-evidence.zip` contains this report, the independent read-only checker `verify_gate41.py`, its `gate41-integrity.json` output, and a short usage file. The checker verifies pack/Git correspondence and authenticates the furnished evidence; it does not run the audited scripts or Lean. Its 12,828 finite decryption-boundary checks for q = 2,…,127 are supplemental only; the general arguments above establish the audited bounds.

| Notation | Meaning |
|---|---|
| n, m, q, ℓ, N | LWE dimension, sample count, modulus, gadget width, and `(n+1)ℓ`. |
| G, `G⁻¹`, X, z | Gadget; deterministic binary decomposition; lifted decomposition of C₂; lifted decomposition of the half-codepoint vector. `G⁻¹` denotes a function, not an inverse matrix. |
| s, t, w | LWE secret, `secretVector = (−s,1)`, and the half-codepoint vector. In the sample-budget formula only, w is the residue-width parameter of that theorem. |
| C, Cᵢ, x, xᵢ, b, μ | Ciphertexts, integer messages, and Boolean messages interpreted as 0 or 1 where used in arithmetic. |
| e, eᵢ, β, βᵢ, β₀, B, β_out | Integer error witnesses; ciphertext/accumulator error bounds; row-error bound; output-error bound. |
| k, d, L | List/batch/program length as indicated, gate/circuit depth, and allowed depth bound. |
| R, D, χ | Binary encryption coins (or the explicitly local relation in the host proof), distinguisher, and finite-seed noise law. |
| ε, κ | Single-column extraction error and sample-budget slack. |
| a_μ, u_μ, p_unif | D's acceptance probabilities in the real, uniform-key, and fully uniform experiments. |
| V₀,V₁ | Accumulated branch ciphertexts in the roadmap calculation. |
| `ds`, g, a, v, j | Depth list, gate, argument/vertex indices, and column/hybrid index, as in the local formulas. |

[eval]: https://github.com/Shilun-Allan-Li/tcslib/blob/48d796a8a68cd50897047f01825a8132dd19e8d8/TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Eval.lean

## ===== briefs/pass-shelat-ch5-8/duplication-ledger.md =====

# Duplication ledger: Pass–shelat ch. 5–8

Accepted debt, each entry acknowledged by the user, with its scheduled resolution.

| ID | New declaration (where) | Existing copy (where) | Status | Resolution |
|---|---|---|---|---|
| DL-1 | `TCSlib.InformationTheory.abs_probTrue_sub_le_statDist` (#183, `InformationTheory/Extractors.lean`, for `main`) | `TCSlib.Cryptography.abs_sum_sub_le_statDist` (`Foundations/Experiments.lean`, Garg's concrete layer, on `cryptography/pass-shelat-ch2-4` and `cryptography/garg-ch1-3`; not on `main`) | accepted 2026-11-04 (user) | No copy on `main` today. When the concrete layer lands on `main`, its lemma becomes a one-line corollary of #183's (a `Finset` test is the `Bool` test `(· ∈ T)`) or is removed. Gate 01 pack erratum E1. |

## Inherited with ch. 2–4 (found 2026-11-05; acknowledged 2026-11-05 by the user: clean up now)

This campaign owns ch. 2–4 since 2026-11-05 (plan, decision log). These duplicates predate it.

| ID | Copies (where) | Status | Proposed resolution |
|---|---|---|---|
| DL-2 | XOR of encodings is the encoding of the Boolean sum, `zipWith xor (ofFn a) (ofFn b) = ofFn (a + b)`, stated three times: `TCSlib.Cryptography.zipWith_xor_ofFn_add` (`Asymptotic/HardCoreLoops.lean`; it was `zipWith_xor_ofFn`, renamed by the base repair to end the name clash with `Encryption.lean`'s different lemma); `TCSlib.Cryptography.zipWith_xor_ofFn_eq_add` (`Asymptotic/MultiMessage.lean`); `TCSlib.Cryptography.MultiMsg.zipWith_xor_ofFn_eq_add` (`Asymptotic/MultiMessageLemmas.lean`) | accepted; scheduled now | Keep the most upstream copy (`HardCoreLoops`) and point the other two at it, in a ch. 2–4 cleanup PR. |
| DL-3 | `pairEncode a b ≠ []`, stated four times: `GGMRed.pairEncode_ne_nil` (`Asymptotic/GGMReduction.lean`), `GI.pairEncode_ne_nil` (`ZeroKnowledge/GraphIsomorphism/Proofs.lean`), `ColMachines.pairEncode_ne_nil` (`ZeroKnowledge/ThreeColoring/Machines.lean`); and, on `main`, `Complexity.pairEncode_ne_nil` (`Complexity/SpaceComplexity/Logspace/InputAccess.lean`), the copy that made the merge's ambiguity | accepted; scheduled now | `main` is merged (#186). Remove the three local copies in favour of `Complexity.pairEncode_ne_nil`, in the same cleanup PR. |
| DL-4 | Not a copy (different carriers): the sampler-based `StatClose` (`Asymptotic/Sampling.lean`) and `main`'s `EpsClose` on `FinDist` (`InformationTheory/Extractors.lean`, #183) | accepted; scheduled now | A bridge lemma, in the same cleanup PR (user, 2026-11-05). |
| DL-5 | Not a copy (different carriers; found by the gate 02 round 2 review): `Games.guessAdv_eq_half_advantage` and `Games.accept_guessGame` (games) and the concrete layer's `predict_eq` (`Asymptotic/Ensembles.lean`, on `uprob` over seed spaces), both the identity behind [PS10, Lemma 73.8] | disclosed in the docstring (gate 02 closing commit) | Derive one from the other through bridge B2 when ch. 2–4 lands on `main`. |

## Found in the ch. 5–8 statement phase (2026-11-05)

| # | Statement | Copies | Status | Resolution |
|---|---|---|---|---|
| DL-6 | Coin-tape slices `(r.drop (j * c)).take c` in global/GI-shadow graph isomorphism, Lamport and sequential ZK, alongside the former BlockEncryptor home | historical duplicates found by the Lamport worker/maintainer | **Implemented at `e9d64158461bfe24ddc88ab885bc4017899b4c16`; final source `3f6db40e1688c4a0bb922c9575dd3bd2157a650b` is checked in draft PR #232. Native and layered Rule10 reconciliation identify zero new/touched reads; all older failures remain recorded. External gates and landing pending.** | One `TCSlib.Cryptography.coinBlock`, `coinBlock_eq` and `length_coinBlock` live in `Asymptotic/Adversary.lean`. The BlockEncryptor definition moved upstream; global/shadow `coinSlice` and sequential ZK's `phaseSlice`/unused length lemma are retired. Lamport already used the public BlockEncryptor `coinBlock`; its length lemma moved upstream. Consumers use the shared name and published reader. |
| DL-7 | Equal-length padding: Lamport's `ofFn_padFin_of_length`, and the inline step in `Composability.length_eval_of_length` (`CCA2Scheme.lean`) | General equation `Collection.ofFn_padFin_of_le` in **`Asymptotic/CollectionsHelpers.lean`**, not `Collections.lean` | **Implemented at `e9d64158461bfe24ddc88ab885bc4017899b4c16`; final source `3f6db40e1688c4a0bb922c9575dd3bd2157a650b` is checked in draft PR #232. Native and layered Rule10 reconciliation identify zero new/touched reads; all older failures remain recorded. External gates and landing pending.** | Lamport's duplicate theorem is deleted. Its uses and CCA2's two padding steps use the general equation, whose conclusion is `List.ofFn (padFin ℓ w) = w ++ List.replicate (ℓ - w.length) false`; at `w.length = ℓ`, simplify `Nat.sub_self`, `List.replicate_zero` and `List.append_nil`. |
| DL-8 | `SecureComputation.PRFOut ℓ₂` (prong B, `SpecialEncryptionSecurity.lean`): ch. 2–4's `PRF` with `ℓ₂(n)`-bit outputs; `PRF` is its case `ℓ₂ = n` | resolved 2026-11-05 | `prfOut_var_iff : PRFOut .var F ↔ PRF F` proved beside `PRFOut` (prong B). The ch. 2–4 layer is unchanged. |


## Found by gate 03 (2026-11-05; rulings G3-5 and R-03l-1: clean up in the gate 03 clean-up PR, after #195)

Most copies trace to helpers that are `private` in pack 03a's and 03l's files. The clean-up makes
one copy public in the most upstream file and re-points the rest.

| Id | Copies | Status | Payback |
|---|---|---|---|
| DL-9 | The coin-block bijection `blocks` (`Fin (m · c) → Bool ≃ Fin m → Fin c → Bool`) and its lemmas, copies and an inverse: `FunFamily.blocks`, `OneWayYao.blocksE`, `blocksEquiv`, `blocksEquivX`, `EnsembleLemmas.blocks`, `SoundnessRep.blocksEquiv`, and `Ensemble.blocks` (private, `Asymptotic/Ensembles.lean`, which calls itself a copy of `FunFamily.blocks`; added on gate 03a round 2, R2-4); with S2b's public duplicate `take_drop_ofFn_blocks` of `EnsembleLemmas.take_drop_ofFn_blocks` (gate 04 N4) | accepted; scheduled (G3-5) | One `FunFamily.blocks` in a low file; re-point 03h, 03i, 03k's statements, `Ensembles.lean` (03a) and S2b's copy. |
| DL-10 | `ptc_comp` (composition of polynomial-time functions in a convenient form), six private or public copies (`Closure`/`Repetition` helpers, `Universal*`, `ThreeColoring/Machines`, …) | accepted; scheduled (G3-5) | Public once in 03a's `Closure.lean`; delete the copies. |
| DL-11 | The state loop `stateFind` (private in `Repetition.lean`) and its copies `GI.stateFind`, `EncodingMachines.polyTimeComputable_stateFind`, `GGMRed.stateLoopFun`, and the variant `stateIterate` | accepted; **half done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)** (`polyTimeComputable_stateFind` public, prose fixed); the copies are re-pointed in clean-up part 2 | `polyTimeComputable_stateFind` public in `Repetition.lean`; re-point; update the prose that calls it private (`StringLoops.lean:36–38`, `HardCoreLoops.lean:68`). |
| DL-12 | `abs_uexp_sub_le`, two copies (`PublicKeyLemmas` and a private one) | accepted; scheduled (G3-5) | One public copy. |
| DL-13 | `negligible_zero` (`Foundations/Negligible.lean` since G3-7a) and `negligible_const_zero` (`ZeroKnowledge/Defs.lean`) | accepted; scheduled (G3-5) | Delete `negligible_const_zero` (2 uses). |
| DL-14 | `forall_of_uprob_eq_one`, two copies | accepted; scheduled (G3-5) | One public copy. |
| DL-15 | `decodeFin_eq_some_iff`, a private copy in `Collections.lean` and a public one in `GGMReductionEval.lean` (`GGMRed.decodeFin_eq_some_iff`; making the `Collections.lean` copy public must avoid the namespace clash, gate 03b review #12c), and the new forward lemma `ofFn_of_decodeFin_eq_some` (`CollectionsHelpers.lean`, #198); S2b's private `eq_ofFn_of_decodeFin` | accepted; scheduled (G3-5) | One public `decodeFin_eq_some_iff` in `Asymptotic/Adversary.lean`; the forward lemma derived from it. |
| DL-16 | `IterateFindHost` (03l) copies 26 declarations of `main`'s private module layer in `Complexity/ClassNP/SAT.lean` (ten now public); the new host is missing from the policy's host registry (§14) | **done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)**: one public host `Turing.ModuleHost` (`TuringMachine/Build/ModuleHost.lean`), consumed by `SAT.lean` and `IterateFindHost.lean`; registry row H14 | Make `SAT.lean`'s layer public on the ch. 2–4 branch and re-point `IterateFindHost`; register the host. |
| DL-17 | `StateLoop` (03l) restates five `main` lemmas, plus `tail_poly` and `xor_poly` (arrived with the `main` merge, #186) | accepted; scheduled (R-03l-1) | Use `main`'s lemmas. |
| DL-18 | `UnaryMul` (03l) privately copies `PairSplit`'s parser | **done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)** (`Turing.PairParse` in `PairSplit.lean`) | Use `PairSplit`'s. |
| DL-19 | Not a copy yet: a latent name clash between `StateLoop.BlockLoop` and `main`'s `Complexity.BlockLoop` (nothing uses it) | **done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)** (renamed `StateLoop.BlockMapLoop`) | Rename or merge in the same PR. |
| DL-20 | `main`'s `TuringMachine/Build/Loop.lean` keeps a private `loop_first_halt`, the same lemma as the new public `Turing.ModuleHost.first_halt` (found by #203's worker). `Loop.lean` is upstream of the host, so it cannot consume it | noted | Move `first_halt` and `live_prefix` down into `Loop.lean` (or the machine core) at the `main` landing, and have `Loop.lean` use them. |
| DL-21 | Elementary number theory that Mathlib already has (audit `mathlib-overlap-nt.md`, 2026-11-06, Mathlib pin `029db123`): 6 DUP (`QR` = `(powMonoidHom 2).range`, `crtUnits` (keep as alias, `rfl`), `coprime_of_ne` = `(Nat.coprime_primes hp hq).2`, `powOneSubgroup` = `(powMonoidHom m).ker`, `rsaPerm` ≈ `powCoprime` (optional), `IsGenerator` ≈ `∀ x, x ∈ zpowers g`) and 9 WRAP (shorter proofs from Mathlib: `units_val_mem`, `pow_mod_totient_modEq`, `units_pow_eq_one_iff`, `two_mul_card_le_of_ne_top`, `card_units_eq_mul_card_QR`, `card_QR_prime`, `sq_pow_div_four_succ`, `fmultNat_eq_mul_prime`; and the core of the sorried `elGamal_correct`) | accepted; scheduled (user direction 2026-11-06: Mathlib first) | Replace by Mathlib's (alias where a name is load-bearing), clean-up part 2 item M; rows in fill-owned files (`Candidates/*`) after those fills land, as landing edits. The fill briefs cite the report's Mathlib names. |
| DL-22 | TCSlib's Chebyshev lower bound (`NumberTheory/Chebyshev.lean`) and Korselt-type facts are in newer Mathlib (`Chebyshev.pi_ge`, `theta_ge`, `psi_ge`; `Nat.isCarmichael_iff_korselt`; master `94f43000`, Lean v4.36.0-rc2), not at our pin | noted | Replace at the next Mathlib bump (repository-wide, `main`'s pin). At the same bump, the hypothesis `BlumDensity` (`Rabin.lean`) can be discharged in its eventual form (`n ≥ n₀`): apply `WienerIkehara.tendsto_sum_range_div` (master only) to `vonMangoldt.residueClass 3` mod 4, with the continuation `vonMangoldt.continuousOn_LFunctionResidueClassAux` (already at our pin) and Chebyshev's `ψ(x) ≪ x` (master), to get `ψ(x; 4, 3) ~ x/2`; then `θ ≥ ψ − (ψ − θ)` (`Chebyshev.psi_sub_theta_le_mul_sqrt`) and `π(x; 4, 3) ≥ θ(x; 4, 3)/log x`. This changes the Rabin statements that take `BlumDensity` (they would take nothing, or `n ≥ n₀`); a statement gate then. |
| DL-23 | fac fill (`Candidates/Factoring.lean`, delivery review 2026-11-07): private near-copies of public lemmas: `fac_chunkEquiv` = `FunFamily.blocks`; `fac_arrowCongr` = `finCastEquiv`; `fac_ofFn_halves` repeats a private `OneWay` lemma (half is `ofFn_block_eq_take_drop`); `fac_listToNat_inj` repeats a private `Sampling` lemma; plus the REPORT's three near-duplicates and small numeral facts re-proved across the fac, rsa and dl-a fills | noted | Clean-up part 2: re-point to the public lemmas; publish the two private ones beside their files and share the numeral facts. |
| DL-24 | col-b fill (delivery review 2026-11-07): `ColZK.acceptProb_seed_to_coins` = `acceptProb_bind` reversed and `ColZK.findSome?_map_option` = core `List.map_findSome?` (removed by landing edits E3–E4); a third copy of `pushesUniform_restrict` across fill units (dl-a has one); `table_index_*` vs `finProdFinEquiv`; `polyTimeComputable_next` repeats `reply_poly`'s proof (review finding 6 has the full list) | E3–E4 at landing; rest noted | Clean-up part 2: publish one `pushesUniform_restrict`, re-point the rest. |
| DL-25 | dl-b fill (`DiscreteLogHardcore.lean`, delivery review 2026-11-07): `dlb_statClose_pi` copies the public `OneWay.statClose_pi` (removed by landing edit E1); `dlb_stateIterate_poly` (from `HardCoreLoops`), `dlb_count_ofFn` (from `HardCoreGL`; relative of `List.count_ofFn`), the `listToNat` fold lemmas, `two_pow_size_le` (dl-a and 3-col have inline `2^size m ≤ 2m` bounds), `pushesUniform_castLE` copies (review D1) | E1 at landing; rest noted | Clean-up part 2: publish one copy of each beside its source; missing equations `HardcoreBit.majority_eq` (`PairwiseIndependence.lean`) and `expSampler_coins` (`DiscreteLog.lean`) at the next shared-file window. |
| DL-26 | col-a fill (delivery review 2026-11-07): `colRep_xor_poly` = `StateLoop.xor_poly`, `eq_of_xor_eq_false` = core `bne_eq_false_iff_eq`, `pushesUniform_blockRead` rebuilds `FunFamily.blocks` (removed by landing edits E2–E4); `ColRep.exec_four_mul`'s step repeats `GI.exec_repViews`'s proof (promote `exec_four_mul`, request R-3); cross-unit near-copies with col-b's `ColZK.pushesUniform_offsetTable`, `ColZK.ofFn_drop_take` | E2–E4 at landing; rest noted | Clean-up part 2: promote `exec_four_mul`, share the col-a/col-b helpers; requests R-2 (`(decGraph x).1` equation), R-5 endorsed. Base reading for #210's next round: `R3COL_witnessRelation`'s `bounded` clause destructures `R3COL` instead of using `R3COL_iff`. |
| DL-27 | rsa fill (delivery review 2026-11-07): 151 lines copied verbatim from dl-a's private helpers (`dla_findSome?_ite`, `dla_find?_range_lt`, `dla_listToNat_append`, `dla_drop_natToList_zero_append`, `dla_ss*`); `rsa_appendEquiv` = Mathlib `Fin.appendEquiv` (landing edit E1); `rsa_comp`/`ptc_congr` copies of the private `ptc_comp` family; loop lemmas descend from Primality's private `spStep`; near-copies of `findSome?_eq_bind_find?`, `find?_range_eq_map_find?_finRange`; parallels with fac (`fac_natToList_mod`, `fac_pairDec`) | E1 at landing; shared-lemma PR planned | **Landing order:** (1) dl-a lands; (2) a shared-lemma PR publishes `PolyTimeComputable.comp'`/`.congr` (`PolyTime.lean`), `IterateFind.find?_range_and_lt` (`IterateFind.lean`), nine `listToNat`/`natToList` lemmas (`Arithmetic.lean`), `rejectBlocksL_eq_find?` (`Concrete.lean`), removing dl-a's copies; (3) rsa lands with E1–E3 and E4 (cites them; checked against stubs); (4) a statement-gated `polyTimeComputable_rejectBlocksL` retires the copied loops in dl-a, rsa, rabin (and dl-c, pending its review). |
| DL-28 | dl-c fill (delivery review 2026-11-07): near-verbatim copies of the trial loop and numeral helpers shared with dl-a and rsa (and dl-b's own modular-numeral layer); `dlc_abs_uexp_sub_le` duplicates `Sampling.lean`'s private lemma and its public copy in `PublicKeyLemmas.lean` (review D1) | noted | Folds into DL-27's shared-lemma PR. The review's D2 homes: generic `polyTimeComputable_rejectBlocksL` (`Concrete.lean`), `listToNat` lemmas, width lemmas (`Arithmetic.lean`), `find?_range` (`Repetition.lean`), `PolyTimeComputable.congr` (`PolyTime.lean`), `abs_uexp_sub_le` public in `Sampling.lean`, `finCastEquiv` to `CollectionsHelpers.lean`. Reconcile with DL-27's homes when that PR is drafted. |
| DL-29 | rabin fill (delivery review 2026-11-07): `rabin_appendEquiv` = Mathlib `Fin.appendEquiv` and `rabin_pushesUniform_prod` (re-proved from `PushesUniform.prodMap`) handled by landing edits E1–E2; undisclosed copies: `rabin_statClose_one` = dl-a's `dla_statClose_one`; `rabin_listToNat_mulStr`, `rabin_prime_poly` copy rsa helpers; `rabin_rS`/`_rQ`/`_rTest` ≈ rsa's `rsa_fS`/`_fQ`/`_fTest`; the block loop is a fourth copy (with dl-a, rsa, dl-c `dlc_ss*`); `rabin_drop_zeros_append`'s step = fac's `fac_natToList_mod` | E1–E2 at landing; rest noted | Folds into DL-27/DL-28's shared-lemma PR and the `polyTimeComputable_rejectBlocksL` host PR. Base reads `rabinCollection_index`, `rabinBlumTrapdoor_index` (through `show`; re-point via `Collection.index_eq`) go to clean-up part 2's (b) list. |
| DL-30 | padded-cpa fill (delivery review 2026-11-11): generic `ProbComp` facts published in a public-key helper as `Composability.ChallengeSim.expect_sample_equiv`, `expect_sample_comm`, `expect_sample_unique`, `expect_sub` (`PublicKey/OracleSecurity/ChallengeSim.lean`); `expect_sample_prod` repeated `Bridge.expect_sample_pair`'s proof. | `ChallengeSim.lean` only | **Paid** ([#298](https://github.com/Shilun-Allan-Li/tcslib/pull/298), merge `d3f2290a`, 2026-11-13; Gate 20) | Landing edit re-proved `expect_sample_prod` from `Bridge.expect_sample_pair`. Promote the four lemmas to `ProbComp` in `Games/Probability.lean` and re-point their uses. |
| DL-31 | `ofFn_padFin_of_length` (`List.ofFn (padFin d w) = w` when `w.length = d`): `GGMRed.ofFn_padFin_of_length` (`GGM/Run.lean`), copy in `Asymptotic/HardCoreGLColl.lean`, private copy in `ElGamal.lean`; padded-cpa's `RecordHandler.lean` uses the GGM one through a transitive import. | 3 | **Paid** ([#298](https://github.com/Shilun-Allan-Li/tcslib/pull/298), merge `d3f2290a`, 2026-11-13; Gate 20) | Promote one public lemma beside `padFin` in `Asymptotic/Adversary.lean`; re-point all uses and delete the copies. |
| DL-32 | `List.ofFn (cast h f) = List.ofFn f` for a width equality: public `Composability.AdaptiveCPA.ofFn_cast` (`PublicKey/AdaptiveCPA/Games.lean`) and private `cca2OfFn_cast` (`PrivateKey/OracleFromPRF.lean`, #289). adaptive-cpa review also lists for promotion: `expect_sample_update` (→ `Games/Probability.lean`, with DL-30), `simulate_eq_of_abs` and the `castImpl` family (→ `Games/Simulate.lean`), `padFin_ofFn_zeroBits`, `headD_ofFn_one`, `ofFn_splitHalf_fst/_snd`; reader request `indCodec_eq_bitCodec`; new uses of `GGMRed.ofFn_padFin_of_length` join DL-31. | 2 (+ candidates) | **Paid** ([#298](https://github.com/Shilun-Allan-Li/tcslib/pull/298), merge `d3f2290a`, 2026-11-13; Gate 20) | Promote one generic `ofFn_cast` beside `padFin`/`BitCodec`; re-point both; promote the listed generic lemmas. |
| DL-33 | bitwise-cpa fill (delivery review 2026-11-11): `BitwiseSim.expect_sample_update` vs `AdaptiveCPA.expect_sample_update` (two forms, same name); generic `BitwiseSim.expect_simulate_eager` and public near-copy `BitwiseSim.expect_simulate_indImpl_cpa` of the private lemma in `PublicKey/OracleSecurity.lean`; `chRun_toCompOn_transport_list` generalizes `ChallengeSim.chRun_toCompOn_transport`; `BitwiseSim.headD_drop` = public `CommitmentLemmas.headD_drop` (and private `headD_drop_ofFn` in `Pseudorandom/NextBit.lean`); `flatten_ofFn_singleton` = private `flatten_ofFn_one` (`Yao.lean`); `decodeFin_nil_getD` (→ `Games/BitCodec`); `padded_enc_runAt/_coins` (→ beside the padded readers); `qDin/qDout` third copy of the two-oracle length vector (`recDin/recDout`, `acDin/acDout`); private `ofFn_half`, `bitwise_runAtL` re-prove published facts; reader request `HybridMachine.hybridPre_eq`. | several | **Paid** ([#298](https://github.com/Shilun-Allan-Li/tcslib/pull/298), merge `d3f2290a`, 2026-11-13; Gate 20) | One consolidation PR with DL-30–DL-32: promote to `Games/Probability`, `Games/Simulate`, `ChallengeSim`, `BitCodec`, a shared list module; re-point and delete copies. |
| DL-34 | pk-cpa-cca1 fill (delivery review 2026-11-12): `OracleFromPRF/Handler.lean` copies private AdaptiveCPA handler pieces (`ofFn_padFin_eq_padL`, round-input readers `rU`…`rCnt`, `impl_of_ret`, `replicate_one`); public `ofFn_pkTapes` re-proves `AdaptiveCPA.ofFn_acTapes` (a generic `⟦blocks q ℓ ω j⟧ = (⟦ω⟧.drop (j·ℓ)).take ℓ` belongs beside `FunFamily.blocks`, input-layout readers beside `InteractiveHandler.input`); private-key `indCodec_eq_bitCodec` (DL-32 reader request); `mem_keys_of_lookup_isSome` (core `List.lookup_isSome_iff`); promotion candidates `simulate_eq_of_abs_bounded` (generalizes `AdaptiveCPA.simulate_eq_of_abs`), `expect_simulate_congr` (→ `Games/Simulate`), `abs_expect_sub_le` (→ `Games/Probability`), `prob_bad_le`, `expect_sample_mem_le` (→ `Games/Hopping`), `padFin_nil`, `padFin_replicate_false`, `ofFn_arrowCongr_finCongr` (→ beside `padFin`), `zipWith_xor_cancel_left`, `xorPerm` (shared list/vector module); owned-file private overlaps with the `cca2*` helpers. | several | **Paid** ([#298](https://github.com/Shilun-Allan-Li/tcslib/pull/298), merge `d3f2290a`, 2026-11-13; Gate 20) | Fold into the DL-30–DL-34 consolidation PR. |
| DL-35 | Found while staging the consolidation (2026-11-12): public `blocks` in `Asymptotic/EnsemblesLemmas.lean` and private `blocks` in `Asymptotic/Ensembles.lean`, both the equivalence `(Fin (q * ℓ) → Bool) ≃ (Fin q → Fin ℓ → Bool)` of `FunFamily.blocks` (`Asymptotic/Adversary.lean`). | 2 | Open (ch. 2–4 inherited) | Re-point to `FunFamily.blocks` in a later ch. 2–4 cleanup; out of scope for `dl-consolidation`. |
| DL-36 | nm-cca2 fill (delivery review 2026-11-12): `NMCCA2.logEmit` (`PublicKey/NonMalleability/Indistinguishability/Forward.lean`) generalizes `Games.EffFill.relabelN`/`relabel` (`Games/Efficiency/OracleBridge.lean`), and its log facts `logEmit_encodeLog`, `iterate_pairSndD_encodeLog`, `flatMap_range_drop`, `length_le_length_encodeLog`, `length_iterate_pairSndD_le`, `polyTimeComputable_logEmit` mirror `relabelN_encodeHist`, `length_le_length_encodeHist` and the orbit bound of `bridgePre_poly` (undisclosed); public `finU`, `finZ`, `finW`, `finA`, `finL`, `fields_finInput` are the DL-34 round-input readers (`rU`…`rL`) again; `ofFn_nthCt` (owned file) is DL-34's generic block fact (`ofFn_acTapes`, `ofFn_pkTapes`); the private readers `rState`…`rAns` (disclosed). Promotion requests: `fwdHandler`/`fwdHandler_impl`, `exists_withAdviceOn` (→ `Games/Efficiency`), `cntRead`/`ansRead` (→ `BitCodec`), `indImpl_eq_of_msgLen_eq_zero` (→ `PublicKey/OracleSecurity`, after that file is split: it is at 999 lines). | several | **Paid** ([#299](https://github.com/Shilun-Allan-Li/tcslib/pull/299), merge `eff2dcd0`, 2026-11-14; Gate 21) | After the DL-30–DL-34 consolidation lands: put `logEmit` beside `relabelN` with `relabel x = logEmit relabelEmit x`; re-point `dCnt`/`dCt`/`dIn`/`dFin`/`eBit`/`eMsg`/`eTape`/`eCt` to R6's readers and delete `finU`…`fields_finInput`; derive `ofFn_nthCt` from the generic block lemma; promote the accepted requests. |
| DL-37 | nm-sim fill (delivery review 2026-11-13; **undisclosed**, accepted as debt by Seyoon 2026-11-13): `NMSim.chunkAt`/`chunkAt_eq`/`length_chunkAt` (`PublicKey/NonMalleability/Simulation/Hybrid.lean`) and the block lemmas `ofFn_block`, `chunkAt_flatten_append`, `map_chunkAt_flatten`; private `padFin_replicate_false` (`Simulation/Challenge.lean`); `Rounds.impl_of_ret`, `rdU`…`rdLog`/`rdState`, `rdAns`, `Simulator.finSt` (`Simulation/Rounds.lean`, `Simulator.lean`); also generic neighbours `expect_eq_until_bad`, `NMSim.expect_simulate_eager`, `expect_congr_of_allOutputs`, `chunkMap`; disclosed: `flatMap_range_drop`, `ofFn_padFin_eq_padL`, `polyTimeComputable_guessBit`, `ofFn_eq_map_range` | `coinBlock`/`coinBlock_eq`/`length_coinBlock` (`Asymptotic/Adversary.lean`), `OneWayLemmas.ofFn_block_eq_take_drop`, `NMCCA2.ofFn_nthCt`, Lamport `coinBlock_flatten`; `PRFGame.padFin_replicate_false` (`OracleFromPRF/Transfer.lean`; → `Games.padFin_replicate_false` in the consolidation); DL-34 private `impl_of_ret` (`AdaptiveCPA/Handler.lean`, `PRFGame`) and readers `rU`…`rL`/`rS`; `Games.prob_eq_until_bad`, `BitwiseSim.expect_simulate_eager`, `ProbComp.expect_mono_of_allOutputs`, `relabelN`/`logEmit` (DL-36); ZK `ofFn_eq_map_range` ×2; A4 `EnsembleLemmas.ofFn_padFin_eq_padL`; `rFwd`/`rY`/Forward `rAns` | **Paid** ([#299](https://github.com/Shilun-Allan-Li/tcslib/pull/299), merge `eff2dcd0`, 2026-11-14; Gate 21) | Landing of the consolidation (after nm-sim): delete the private `padFin_replicate_false` and use `Games.padFin_replicate_false`; re-point the nm-sim files to the moved names. Post-consolidation fold window, with DL-36: fold `chunkAt` onto `coinBlock` (58 uses) and place the block lemmas beside it; re-point `rdU`…`rdLog`, `rdState`, `finSt` to `InteractiveHandler.rU`…`rS` and `impl_of_ret` to `InteractiveHandler.impl_of_ret`; derive `prob_eq_until_bad` and `ChallengeSim.expect_simulate_eager` from the general nm-sim forms; one iterate-and-emit definition for `relabelN`/`logEmit`/`chunkMap`; merge the three `ofFn_eq_map_range` into `Foundations/BitLists`; make `NMSim.ofFn_padFin_eq_padL` the A4 lemma; fold `rdAns` with the `rFwd`/`rY`/`rAns` readers; promote the accepted requests (review r1 table). |
| DL-38 | dl-folds fill (worker REPORT §0.6, disclosed; delivery review 2026-11-14): inline re-proofs of `impl_of_query` (`acHandler_impl_forward`) and of a returning finalization (`pkHandler_finish`, `acHandler_finish`); a local `have` equal to `polyTimeComputable_ansRead` (`OracleFromPRF.lean`); further block-window restatements (`Primality.ofFn_chunk`, `ColRep.drop_take_ofFn_blockRead`, `Factoring.fac_ofFn_halves`, already corollaries); other iterate-and-emit loops (`BlockEncryptor`, `EnsembleLemmas.CopiesLoop`, `StretchMachine`, `CommitmentLemmas.ComLoop`, ZK `EncodingMachines`); the ZK pair `GI.iterate_pairSndD_encodeMsgs` / `ColMachines.iterate_pairSndD_encodeMsgs`; and the B3 `blocks` aliases (`EnsembleLemmas.blocks` and its lemmas, private `Ensembles.blocks`), escalated. | `InteractiveHandler.impl_of_query`, `finish_of_ret`; `Games.polyTimeComputable_ansRead`; `FunFamily.ofFn_blocks`; `Games.iterEmit`; `FunFamily.blocks` | Open (deferred) | Opportunistic: fold each when its file is next touched. The B3 aliases need a gate-approved restatement of `exists_copiesRed`, `ofFn_blocks_symm`, `take_drop_ofFn_blocks`, `ComLoop.emit_init_of_lt` and of the bodies of `PRFGame.pkTapes`, `Ensemble.copies` (all definitionally equal). Complexity copies of `ofFn_eq_map_range` and `flatMap_range_drop` are another campaign's. |
| DL-39 | ext-nosrc fill (worker request and delivery review 2026-11-14, disclosed): `Randomness.Rejection.tupleEquiv` restates Mathlib's `(Fin.consEquiv _).symm`; generic `FinDist` facts local to `Randomness/Extraction/Rejection.lean` (`sum_map`, `expect_map`, `probTrue_map`, `probTrue_le_one`, `probTrue_nonneg`, `map_map`, `map_prod_snd`, `uniform_prod`, `map_uniform_equiv`, `mixture`, `mixture_isSource`, `uniform_probTrue`); no exact duplicate in TCSlib (nearest: `SamplingFinDist.uprob_comp_eq_probTrue_map`, `Experiments.uprob_comp_eq_sum_map`, `ProbComp.expect_map`). | Mathlib `Fin.consEquiv`; `InformationTheory/FinDist` (to be added) | Open (deferred) | Promote the `FinDist` facts to `InformationTheory/FinDist` and use `Fin.consEquiv` in a later job (`FinDist` was frozen for the fill). The authoritative full promotion list (also `map_apply_expect`, `branch_apply`, the uniform-machine family, `take_poly`) is the delivery's `evidence/promotion-requests.md`, `rejection-review.md`, `sampler-review.md` (exchange `a5da5cc3`, `inbox/fills/ext-nosrc/`; Gate 22 observation). |
| DL-40 | cca2-ett fill (delivery review 2026-11-14): undisclosed `ETTGame.eval_toOracleAdversary_len` (`EncryptThenTag/Machines.lean`) generalizes public `PRFGame.eval_toOracleAdversary_width` (`OracleFromPRF/Reduction.lean`, its `ℓ = n` case); disclosed `ETTGame.zipWith_xor_cancel` = four private `zipWith_xor_xor_self` copies (`FromPRF`, `FromPRG`, `SpecialEncryption`, owned `zipWith_xor_xor_self'`; public relative `zipWith_xor_cancel_left`, other orientation); Gate 23 (G23-01, Seyoon 2026-11-14: debt now, fold in cleanup): private `length_le_length_encodeLog` (`EncryptThenTag/Machines.lean`) = the private copy in `NonMalleability/Indistinguishability/Forward.lean:108`; `ETTGame.prfAdv_eq_expect` re-derives private `prfAdv_prfReduction` (public relative `prfAdv_eq`, uprob form); generic forms `ETTGame.tapeImpl`/`simulate_tapeImpl_congr`/`expect_simulate_tapeImpl` (AdaptiveCPA), `recBits` family and `ovr` (PRFGame), `expect_simulate_abs` (`Games.simulate_eq_of_abs_bounded`), private `abs_expect_sub_le_expect` (`ProbComp.abs_expect_sub_le`). | `Foundations/BitLists`, `Pseudorandom/Functions`, `Games/*`, the general ETT forms | Open (deferred) | Promote the general forms (worker requested most) and re-derive the specialised copies from them; fold the private XOR copies; publish `length_le_length_encodeLog` in `Games/Efficiency/Strings.lean` beside `length_encodeLog_le` and delete both private copies (cleanup job). |
| DL-41 | dl-crh fill (delivery review 2026-11-14): **undisclosed** `FromDiscreteLog.inputWord_split` restates `ofFn_eq_init_append` (`Asymptotic/ReductionSupport.lean`, up to `Fin.init`); `ofFn_splitBits_fst/_snd` restate `ofFn_splitCoins_fst/_snd` (`CollectionsHelpers.lean`; `Authentication.splitBits` = `splitCoins`); disclosed re-derivations from public readers of private `dlb_expo_val`, `fac_listToNat_inj`, `ofFn_splitCoins_symm_cast`, `dla_statClose_expDec`; near relatives `residueFinEquiv` (Mathlib `ZMod.finEquiv`), `boundedInputEquiv` (`Fin.snocEquiv`), `expect_sample_eq_uexp` (`Games.Bridge.prob_sample_eq_uprob`). | `ofFn_eq_init_append`, `ofFn_splitCoins_*`, a `splitBits = splitCoins` bridge; worker promotion list `evidence/PROMOTION.md` (exchange `9ad236d1`) | Open (deferred) | `inputWord_take` (Gate 24 G24-01) and `inputWord_split` re-pointed to `take_ofFn_castLE` / `ofFn_eq_init_append` by LE-reuse `d356381a` (#307); the rest: re-point and promote in a later job. |
| DL-42 | hash-sign fill (delivery review 2026-11-14): `HashSignForward.roundWord`/`handler` repeats the `Games/Forwarding` `fwdRun`/`fwdHandler` pattern with a hashed query and different widths (disclosed); `splitBits_pad_concat` is a corollary of `Games.padFin_append_split`; `expect_simulate_sample_once` near `Games.expect_simulate_eager`; `MachineCodec.ext_of_fields`, `forgerCodec_eq_bitCodec`, `eq_pure_of_cost_zero` overlap the parallel lamport delivery's `lamport_codec_ext`, `lamport_forgerCodec`, `exists_pure_of_cost_zero`. | `Games/Forwarding` (a query-map `fwdHandler`), `Games/BitCodec`, `Games/Hopping`, `Games/Machines` | Open (deferred) | Generalize `fwdHandler`; promote the codec/cost facts to `Games/Machines` (no attribute) and fold the lamport copies once both units have landed. |
| DL-43 | lamport fill (delivery review 2026-11-14): **undisclosed** `LamportFill.signatureBlock σ i` = `FunFamily.blocks n n σ i` (via `blocks_apply`; DL-9 class); near relatives `Blocks.flatten_ofFn_update` (`CommitmentLemmas.ofFn_update_eq`), `Averaging.expect_favourable_of_success` (`ProbComp` counterpart of `HardcoreBit.uprob_mul_le_uexp`). Overlaps with hash-sign are DL-42. Also the follow-up (Seyoon, 2026-11-14): restate the frozen `lamport_oneTimeSecure` hypothesis `f` over `Fin (var.eval n)` with a published reader, clearing its 16 seal-B failures. | `FunFamily.blocks`; `CommitmentLemmas`; `HardcoreBit` | Open (deferred) | Re-point `signatureBlock`; promote the averaging lemma; the frozen-statement restatement needs its own gate. |
| DL-44 | prf-mac fill (delivery review 2026-11-15): F-01 local `hadv` in `MAC/FromPRF/Bound.lean` re-proves public `ETTGame.prfAdv_eq_expect` (**ruling Seyoon 2026-11-15: promote now** to the PRF layer beside `prfAdv`, re-derive the ETT copy proof-only, re-point prf-mac); F-02 `decide_fnForge`'s `hw`/`htake`/`hdrop` restate list readings of `splitBits` (`take_ofFn_castLE`, `CollectionsHelpers.ofFn_drop_take`, `FromDiscreteLog.ofFn_splitBits_fst/_snd`); F-03 `PRFMAC.blocks`/`macState`/`hits_nil_iff` near `GGMRed.tblEnc`/`lookup` (cca2-ett `tblW`). The private `prfAdv_prfReduction` (`OracleFromPRF.lean`) is the same identity specialised (DL-40). | `TCSlib.Cryptography.prfAdv_eq_expect` (published in #314, merge `59c2c1fb`); the list readers above; `GGMRed.tblEnc` | Open (F-01 paid) | F-01 **paid**: promoted in #314 (ETT re-derived, LE-gate30), prf-mac re-pointed by LE-reuse `590d1a56` (#317, Gate 33). F-02/F-03 and the private `prfAdv_prfReduction` in the deferred cleanup. |
| DL-45 | learning fill (delivery review 2026-11-15): undisclosed `LearnPRF.uprob_eq_point` = `OneWay.uprob_eq_one_div_card` (reversed); inline re-proof of `MultiMsg.abs_uexp_sub_le_uprob` in `abs_gameProb_random_sub_half_le` (both re-pointed by maintainer LE-reuse `8befc589`, #313); private `length_blk` re-proves `MultiMsg.length_histBlock` for the disclosed private copy `blk` of `histBlock`; `flip0`/`flip0_flip0` = `flipBit`/`flipBit_flipBit` (BooleanAnalysis) and `flipAt` (DeterministicCC); `foldr_pairEncode_nil` reads `Strategy.encodeMsgs`; short-name clashes `relabel`/`relabel_eq` (DL-36 family) and `flipAt`. | `OneWay.uprob_eq_one_div_card`; `MultiMsg.abs_uexp_sub_le_uprob`, `length_histBlock`; `BooleanAnalysis.flipBit` | Open | Items 1–2 by LE-reuse at landing; the rest in the deferred cleanup. |
| DL-46 | prf-long fill (delivery review 2026-11-15, disclosed): `MultiMsg.encodeList_eq_flatMap` (`FromPRF/MultiMsgOut.lean`) is a third copy of public `encodeList_eq_flatMap` (`Asymptotic/BlockEncryptor.lean`) beside the frozen private copy in `FromPRF.lean` (now unused); reuse blocked by a private/public name clash. `histBlockLen` kept beside `histBlockLenOut` (different `PolyExpr` terms); `adviceBound` now unused. Near relatives: GGM `encodeHist_eq_histEnc`/`histEnc_append_single`/`length_histEnc`, `UniformTableauEmitter.encodeList_eq_flatMap`. | `encodeList_eq_flatMap` (to move to `EnsembleSecurity`, worker's promotion request) | Open (deferred) | Promote and delete the copies; remove the unused frozen items under a frozen-file exception in the cleanup. |
| DL-47 | Gate 32 staging (2026-11-15), pre-existing: copies of `((List.ofFn f).drop i).headD d = f i` and of its getD form `(List.ofFn f).getD i d = f i`, at the tip `e9998722`. Inline chain: `Pseudorandom/NextBit.lean:454` (`headD_drop, List.getD_eq_getElem?_getD, List.getElem?_ofFn`, the remnant of NextBit's private `headD_drop_ofFn` that dl-consolidation L1 deleted). Index-0 cases: `headD_ofFn_one` (`Foundations/BitLists.lean:75`), `GIZK.headD_ofFn_block` (`ZeroKnowledge/GraphIsomorphismZK/Closeness.lean:280`), private `eq_const_headD` (`Encryption/PublicKey/NonMalleability/Simulation/SimIND.lean:88`). getD forms: `GI.getD_ofFn_lt'` (`ZeroKnowledge/GraphIsomorphism/SoundnessRep.lean:61`), `GI.getD_ofFn_lt` (`ZeroKnowledge/GraphIsomorphism/Proofs.lean:818`), `GIZK.getD_ofFn_lt` (`ZeroKnowledge/GraphIsomorphismZK/Closeness.lean:110`), `ColProofs.ofFn_getD_lt` (`ZeroKnowledge/ThreeColoring/ProtocolProofs.lean:391`), Yao's private `getD_ofFn'` (`SecureComputation/Yao.lean:611`). Inline getD chains (`List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos …`): `ZeroKnowledge/ThreeColoring/Simulator.lean:861`, `ZeroKnowledge/ThreeColoring/Language.lean:429` (in private `ofFn_getD_tape`), `ZeroKnowledge/Encoding.lean:359`; the same getD chain also inline outside the cryptography files, in `TCSlib/Complexity/ClassNP/SAT.lean:149`, `TCSlib/Complexity/ClassNP/Tautology.lean:142` and `TCSlib/Complexity/SpaceComplexity/Codec/Word.lean:135` (`getD_encChunk`). **Extended by Gate 32 G32-01 (ruling Seyoon 2026-11-15: extend DL-47 and close), at the #316 head `c18afbe6`:** exact copy of the promoted statement: GGM `Pseudorandom/Functions/Asymptotic/GGM/Run.lean:449–450` (`step_eq`, local `hbit`, replacement `TCSlib.Cryptography.headD_drop_ofFn x ⟨d.i, hi⟩ false`); headD chain `Asymptotic/HardCoreLoops.lean:278–280` (`orbit_eq`); getD/ofFn computations: `SecureComputation/Garbling.lean:193–198` (private `map_range_getD_ofFn`) and `:375–380` (`garbledValues_getD`), `SecureComputation/Yao.lean:626–627` (`yaoBobTables_yaoMsg`), `Encryption/PublicKey/BitwiseCPA.lean:107–113` (private `ofFn_half`), `Encryption/PublicKey/OracleSecurity/PaddedCPA.lean:72–78` (private `ofFn_splitHalf_bit`), `Complexity/CircuitComplexity/CircuitEvalNP.lean:68–69` (`dagCktSatLang_mem_NP`), `PSubsetPPolyGadget.lean:188–190` (`runWith_embedGates_getD`), `PSubsetPPolyProgram.lean:383–387` (`progGates_values`), `PSubsetPPolyTableau.lean:127–132` (`snapEncode_injective`), `UniformTableauCircuit.lean:427–431` (private `tabSrc_eval`), `Complexity/Randomized/RandomWalk.lean:256–259` (`decodeIdx_succ_append`), `Complexity/ClassPSPACE/TQBF.lean:857–859` (private `codecRow_realize`), optional-access form `Cryptography/Encoding/BooleanVector.lean:168–171` (`expandPoly_encode`) and `Hashing/SIS/CollisionOutput.lean:237–243` (`collisionOutputPoly_pairEncode`). **sc-garble SG-F04 (ruling Seyoon 2026-11-15, ledger):** new inline getD/`List.ofFn` chain in `SecureComputation/Garbling/CoinBlocks.lean:73–74` (`getD_eq_getElem`, `getElem_ofFn`), same as Yao's private `getD_ofFn'`. **gsw-core GC-01 (review r1, 2026-11-16; info, disclosed; ledger):** new inline getD/`List.ofFn` chain in `AdvancedEncryption/Homomorphic/GSW/Eval.lean:262–264` (`eval_encrypts`, the input vertices; `List.getD_eq_getElem`, `List.getElem_ofFn`), at the #339 head `839f36cc` (the same lines in the delivered `d4ebb0be`). The brief's F4 route prescribed these two Mathlib lemmas; the nearest public getD form, `GI.getD_ofFn_lt'`, cannot be imported there. | `TCSlib.Cryptography.headD_drop_ofFn` (#316) | Open (deferred) | Ruling Seyoon 2026-11-15: pre-existing (merged before the promotion), recorded as debt and not re-pointed in #316. Re-point NextBit:454 and the index-0 cases onto `headD_drop_ofFn`, and the getD forms onto one shared getD reader, in the deferred cleanup. Yao's `getD_ofFn'` waits for sc-garble and sc-yao to land (`Yao.lean` is shared). **Cleanup plan (G32-01):** add one generic reader `(List.ofFn f).getD i d = f ⟨i, h⟩` (any type) derived from `headD_drop_ofFn` and `List.headD_drop`, then re-point every DL-47 copy onto it or onto `headD_drop_ofFn`, proof only, headers preserved, starting with the exact GGM copy; the `Garbling.lean`/`Yao.lean` copies wait for sc-garble and sc-yao to land. |
| DL-48 | sc-ot fill (delivery review 2026-11-15): F-02 `OT.splitLen` / `splitLen_symm_ofFn` (`SecureComputation/ObliviousTransfer/Simulators.lean`) restate public `coinsEquiv` (inverted) and `ofFn_coinsEquiv` (`Asymptotic/EnsemblesLemmas.lean:141,145`), body as private ElGamal `dlc_splitEquiv`; F-04 `OT.uprob_signedPredictor_false/_true` adapt `exists_pkPredictor` (`pkPredictor` has no public reader); F-07 near-relatives `GI.pairSndD_encodeMsgs` (for `getD_one_eq`), `predict_eq`, and promotion requests `negligible_finset_sum`, `statClose_prod_of_forall`, `exec_five`, `length_runAtL_le`. **Gate 34 G34-02 (ruling Seyoon 2026-11-15, ledger):** `OT.length_ofFn_coins` (`ObliviousTransfer/Simulators.lean:210–212`) is a verbatim copy of public `Composability.NMSim.length_ofFn_coins` (`Encryption/PublicKey/NonMalleability/Simulation/Rounds.lean:41–43`); direct reuse would add 69 NM modules to the OT closure. (G34-01, `OT.getD_zero_eq`/`OT.getD_one_eq'` re-proving `headD_drop`, is fixed by LE-gate34, not debt.) | `coinsEquiv`, `ofFn_coinsEquiv`; `exists_pkPredictor` | Open (deferred) | Ruling Seyoon 2026-11-15: ledger debt, disclosed (not fixed in the landing: reuse needs a new import and a definition change). Cleanup: replace `splitLen` by `(coinsEquiv h).symm`; publish `pkPredictor_apply` and re-derive the signed predictor from `exists_pkPredictor`; decide the promotion requests. G34-02 cleanup: promote `length_ofFn_coins` to the `NUPPT` layer (`Asymptotic/Adversary` or `Randomized/NonUniform`) and re-point both copies. |
| DL-49 | sc-compose fill (delivery review 2026-11-15, SC-F01; disclosed in the checkpoint REPORTs): helpers under `SecureComputation/ComposeSecurity/` restate public lemmas because the brief's two extra imports were read as exhaustive: a third `negligible_polyExpr_mul`; `appendCoins` (= `coinsEquiv`); `ofFn_blocks_symm` (= `FunFamily.ofFn_blocks_symm`); `polyTimeComputable_flatMap_range`, `flatMap_range_ite`, `iterSnd_poly`, `encodeMsgs_eq_flatMap`, `msgAt_encodeMsgs` and the `padTo` family (from `Composability/ZeroKnowledge/ThreeColoring/Machines.lean`). | `EnsembleLemmas.negligible_polyExpr_mul` (`Asymptotic/EnsemblesLemmas.lean:377`), `coinsEquiv`, `FunFamily.ofFn_blocks_symm`, the `ThreeColoring/Machines` helpers | Open (deferred) | Ruling Seyoon 2026-11-15: ledger debt. Cleanup: import the public lemmas (or promote the ThreeColoring helpers to a shared machine layer) and re-point the sc-compose copies proof-only. |

## ===== blueprint/src/references/gentry-sahai-waters-2013-fhe.md =====

<!-- generated-by: maintainer transcription of the passages used (DW-7) -->
<!-- source-pdf-sha256: 8edb94cfd852a88a8684adbf81b73e78bd21466514b7bb7000d7df1e4431bf00 -->
<!-- validation-status: scoped transcription for DW-7; awaiting Codex source review -->

# Homomorphic Encryption from Learning with Errors: Conceptually-Simpler, Asymptotically-Faster, Attribute-Based

Craig Gentry, Amit Sahai and Brent Waters. *CRYPTO 2013*, LNCS 8042, pp. 75–92; full version
IACR ePrint 2013/340, version dated 8 June 2013 (25 pages; tag `GSW13`).

**Scope.** Only the passages that the GSW Lean (phase 5) and the phase-6 plan cite are
transcribed (DW-7; GSW ruling Q14): the bootstrapping remark of §1.2, §1.3.1–§1.3.4, §2.3, and
§3.1–§3.4. The PDF is not committed. Physical and printed pages coincide. The scoped raw
extraction is `gentry-sahai-waters-2013-fhe.raw.md`. Mathematics is set in LaTeX (the paper's
arrows over vectors are kept as $\vec v$); the wording is the paper's. Notes marked
*Transcription note* are not part of the source.

<a id="pdf-8edb94cfd852-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.95 -->

**Section 1.2, bootstrapping and circular security (p. 4).** As with all current FHE schemes
without bootstrapping, the parameters and per-gate complexity of evaluation depend on the
multiplicative depth $L$ of the circuit. "Bootstrapping" [Gen09], together with an assumption
of circular security, remains the only known way of making these performance metrics
independent of $L$, and while the overhead of bootstrapping is high, it becomes an attractive
option once $L$ passes some threshold. However, our scheme loses some of its advantages once
bootstrapping is used. First, to apply bootstrapping, the evaluator needs to obtain the user's
secret key encrypted under its public key – in effect, an evaluation key – and therefore we no
longer achieve identity-based/attribute-based FHE in this context. Second, this encrypted
secret key has quasi-cubic size in our scheme, and while this can be mitigated by public key
compression techniques [CNT12], it eliminates the space complexity advantages of our scheme.
Essentially, bootstrapping returns us to the realm of "unnatural" operations, with all of its
disadvantages. It remains a fascinating open problem to find some "natural" alternative to
bootstrapping, and (relatedly) to achieve "pure" FHE without an assumption of circular
security.

<a id="pdf-8edb94cfd852-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=0.95 -->

## 1.3 An Overview of Our FHE Scheme

**Section 1.3 and Section 1.3.1, homomorphic operations (pp. 4–5).** Our main insight is that we
can achieve LWE-based homomorphic encryption where homomorphic addition and multiplication
correspond directly to matrix addition and multiplication.

Let us skip key generation and encryption for the moment, and jump directly to the homomorphic
operations (and decryption).

In our scheme, for some modulus $q$ and dimension parameter $N$ to be specified later, a
ciphertext $C$ is a $N\times N$ matrix over $\mathbb Z_q$, with "small" entries (much smaller
than $q$) and the secret key $\vec v$ is a $N$-dimensional vector over $\mathbb Z_q$ with at
least one "big" coefficient $v_i$. We restrict the message $\mu$ to be a "small" integer. We
say $C$ encrypts $\mu$ when $C\cdot\vec v=\mu\cdot\vec v+\vec e$, where $\vec e$ is a "small"
error vector. To decrypt, we extract the $i$-th row $C_i$ from $C$, compute
$x\leftarrow\langle C_i,\vec v\rangle=\mu\cdot v_i+e_i$, and output $\mu=\lfloor x/v_i\rceil$.
In a nutshell, the essence of our scheme is that the secret key $\vec v$ is an approximate
eigenvector of the ciphertext matrix $C$, and the message $\mu$ is the eigenvalue.

Now, let us see why matrix addition and multiplication are correct homomorphic operations.
Suppose $C_1$ and $C_2$ encrypt $\mu_1$ and $\mu_2$ in that
$C_i\cdot\vec v=\mu_i\cdot\vec v+\vec e_i$ for small $\vec e_i$. Let $C^+=C_1+C_2$ and
$C^\times=C_1\cdot C_2$. For addition, we have
$C^+\cdot\vec v=(\mu_1+\mu_2)\cdot\vec v+(\vec e_1+\vec e_2)$, where the error likely has grown
a little, as usual in FHE schemes. But assuming the error is still "small", the sum of the
ciphertext matrices encrypts the sum of the messages. For multiplication, we have

$$
\begin{aligned}
C^\times\cdot\vec v&=C_1\cdot(\mu_2\cdot\vec v+\vec e_2)
=\mu_2\cdot(\mu_1\cdot\vec v+\vec e_1)+C_1\cdot\vec e_2
=\mu_1\cdot\mu_2\cdot\vec v+\mu_2\cdot\vec e_1+C_1\cdot\vec e_2\\
&=\mu_1\cdot\mu_2\cdot\vec v+\text{small}
\end{aligned}
$$

where the final error vector is hopefully "small", since $\mu_2$, $C_1$, $\vec e_1$, and
$\vec e_2$ are all small. If so, the product of the ciphertext matrices encrypts the product of
the messages. Interestingly, $C_2\cdot C_1$ is also an encryption of $\mu_1\cdot\mu_2$, even
though matrix multiplication is not commutative.

To simplify further, it might be helpful to imagine an error-free version of the scheme, where
$C_i\cdot\vec v=\mu_i\cdot\vec v$ exactly. In this case, the key $\vec v$ is an (exact)
eigenvector of ciphertext matrices, and the message $\mu_i$ is the eigenvalue. In general, if
matrices $C_1$ and $C_2$ have a common eigenvector $\vec v$ with eigenvalues $\mu_1$ and
$\mu_2$, then $C_1\cdot C_2$ and $C_2\cdot C_1$ have eigenvector $\vec v$ with eigenvalue
$\mu_1\cdot\mu_2$.

<a id="pdf-8edb94cfd852-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.95 -->

**Section 1.3.1, end (p. 5).** Of course, in our scheme, the secret key $\vec v$ is only an
approximate eigenvector, not an exact one. Introducing error is necessary to base the security
of our scheme on LWE. The cost of making $\vec v$ only an approximate eigenvector is that
certain terms in our scheme must be "small" to ensure that homomorphic operations do not
disrupt the essential form of the ciphertexts. We call our new approach to LWE-based
(homomorphic) encryption the approximate eigenvector method.

<a id="pdf-8edb94cfd852-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=0.95 -->

**Section 1.3.2, bounding the error and somewhat homomorphic encryption (p. 5).** Although we
have not fully specified the scheme, let us go ahead and estimate how homomorphic it is. The
scheme above works correctly until the coefficients of the error vector begin to approach $q$
in magnitude. How many homomorphic operations can we perform before that happens?

Suppose $C_1$ and $C_2$ are $B$-bounded ciphertexts, in the sense that $\mu_i$ and the
coefficients of $C_i$ and $\vec e_i$ all have magnitude at most some bound $B$. Then, $C^+$ is
$2B$-bounded, and $C^\times$ is $(N+1)B^2$-bounded. In short, the error level grows worse than
$B^{2^L}$, doubly exponentially with the multiplicative depth $L$ of the circuit being
evaluated. Alternatively, if one wants to consider the degree (rather than depth) of functions
that can be evaluated, if we evaluate a multivariate polynomial $P(x_1,\dots,x_t)$ of total
degree $d$, on $B$-bounded ciphertexts as input, the final ciphertext is
$|P|(N+1)^{d-1}B^{d}$-bounded, where $|P|$ is the $\ell_1$-norm of $P$'s coefficient vector.
Taking $q$ to comfortably exceed this bound, we (roughly) can evaluate polynomials of degree
$\log_{NB}q$. Since $q/B$ must be subexponential (at most) in $N$ for security reasons, our
scheme-so-far can only evaluate polynomials of (sublinear) polynomial degree in $N$ (only
logarithmic depth). In short, our scheme-so-far is a somewhat homomorphic encryption (SWHE)
scheme [Gen09] that can evaluate log-depth or polynomial degree. Though not yet fully
homomorphic, it is by far the most homomorphic LWE-based encryption scheme that uses only
"natural" homomorphic operations.

*Transcription note.* The superscripts $(N+1)B^2$ and $B^{2^L}$ are flattened in the
extraction and were checked against the page image (140 dpi); $\log_{NB}q$ is read from the
layout.

<a id="pdf-8edb94cfd852-p005-b003"></a>
<!-- pdf-source: page=5; block=3; confidence=0.95 -->

**Section 1.3.3, flattening ciphertexts and fully homomorphic encryption (pp. 5–6).** To obtain
a leveled FHE scheme that can evaluate circuits of polynomial depth without bootstrapping or
techniques like relinearization, we need to ensure better bounds on the growth of the error. Let
us say that a ciphertext $C$ is $B$-strongly-bounded if its associated $\mu$ and the
coefficients of $C$ all have magnitude at most $1$, while the coefficients of its $\vec e$ all
have magnitude at most $B$. If we evaluate a NAND gate on $B$-strongly-bounded ciphertexts
$C_1,C_2$ to obtain a new ciphertext $C_3\leftarrow I_N-C_1\cdot C_2$ (where $I_N$ is the
$N$-dimensional identity matrix), then the message remains in $\{0,1\}$, and the coefficients of
$C_3$'s error vector have magnitude at most $(N+1)B$. If we could somehow additionally ensure
that $C_3$'s coefficients have magnitude at most $1$ so that strong-boundedness is preserved,
then we could evaluate a circuit of depth $L$ while keeping the error magnitude at most
$(N+1)^{L}B$. Setting $q/B$ to be subexponential in $N$, we could evaluate a circuit of
polynomial depth rather than merely polynomial degree. In short, we would have a leveled FHE
scheme.

Here we describe a operation called ciphertext flattening that keeps ciphertexts strongly
bounded, so that we obtain leveled FHE.

Flattening uses some simple transformations from [BV11b, BGV12, Bra12] that modify vectors
without affecting dot products. Let $\vec a,\vec b$ be vectors of some dimension $k$ over
$\mathbb Z_q$. Let $\ell=\lfloor\log_2 q\rfloor+1$ and $N=k\cdot\ell$. Let
$\mathrm{BitDecomp}(\vec a)$ be the $N$-dimensional vector
$(a_{1,0},\dots,a_{1,\ell-1},\dots,a_{k,0},\dots,a_{k,\ell-1})$, where $a_{i,j}$ is the $j$-th bit
in $a_i$'s binary representation, bits ordered least significant to most significant. For
$\vec a'=(a_{1,0},\dots,a_{1,\ell-1},\dots,a_{k,0},\dots,a_{k,\ell-1})$, let
$\mathrm{BitDecomp}^{-1}(\vec a')=(\sum 2^j\cdot a_{1,j},\dots,\sum 2^j\cdot a_{k,j})$ be the
inverse of BitDecomp, but well-defined even when the input is not a $0/1$ vector. For
$N$-dimensional $\vec a'$, let
$\mathrm{Flatten}(\vec a')=\mathrm{BitDecomp}(\mathrm{BitDecomp}^{-1}(\vec a'))$, a
$N$-dimensional vector with $0/1$ coefficients. When $A$ is a matrix, let
$\mathrm{BitDecomp}(A)$, $\mathrm{BitDecomp}^{-1}$, or $\mathrm{Flatten}(A)$ be the matrix
formed by applying the operation to each row of $A$ separately. Finally, let
$\mathrm{Powersof2}(\vec b)=(b_1,2b_1,\dots,2^{\ell-1}b_1,\dots,b_k,2b_k,\dots,2^{\ell-1}b_k)$, a
$N$-dimensional vector. Here are some obvious facts:

- $\langle\mathrm{BitDecomp}(\vec a),\mathrm{Powersof2}(\vec b)\rangle=\langle\vec a,\vec b\rangle$.
- For any $N$-dimensional $\vec a'$,
  $\langle\vec a',\mathrm{Powersof2}(\vec b)\rangle
  =\langle\mathrm{BitDecomp}^{-1}(\vec a'),\vec b\rangle
  =\langle\mathrm{Flatten}(\vec a'),\mathrm{Powersof2}(\vec b)\rangle$.

An interesting feature of Flatten is that it makes the coefficients of a vector or matrix
small, without affecting its product with $\mathrm{Powersof2}(\vec b)$, and without knowing
$\vec b$.

To facilitate ciphertext flattening, we give a special form to our secret key $\vec v$.
Specifically, we set $\vec v=\mathrm{Powersof2}(\vec s)$ for some secret vector $\vec s$ (to be
specified later). This form is consistent with our earlier requirement that $\vec v$ have some
big coefficient $v_i$ for decryption; indeed, since $\vec v$'s coefficients go up by
$\lfloor\log_2 q\rfloor$ powers of 2, it must have a big coefficient suitable to recover
$\mu\in\{0,1\}$.

Now, for any $N\times N$ matrix $C$, we have $\mathrm{Flatten}(C)\cdot\vec v=C\cdot\vec v$. So,
after we compute an initial ciphertext $C_3\leftarrow I_N-C_1\cdot C_2$ for the NAND gate, we
set $C^{\mathrm{NAND}}=\mathrm{Flatten}(C_3)$ to obtain a ciphertext that has $0/1$
coefficients and is strongly bounded. Thus, we obtain leveled FHE without relinearization, under
a fixed approximate eigenvector secret key.

*Transcription note.* The page break (p. 5 to p. 6) falls inside the definition of
$\mathrm{Flatten}$; the subsection is kept as one block. The sums in
$\mathrm{BitDecomp}^{-1}$ run over $j$ (the extraction prints the $\sum$ signs on a separate
line).

<a id="pdf-8edb94cfd852-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.95 -->

**Section 1.3.4, key generation, encryption, and reduction to LWE (p. 6).** Let us finally
circle back to key generation and encryption. We want to base security on LWE. So, for key
generation, we generate an LWE instance. For suitable parameters $q$, $n$,
$m=O(n\log q)$, an LWE instance over $\mathbb Z_q$ consists of a $m\times(n+1)$ matrix $A$ such
that there exists a $(n+1)$-dimensional vector $\vec s$ whose first coefficient is $1$ where
$\vec e=A\cdot\vec s$ is a "small" error vector. (See Section 2 for a formal definition of LWE.)
In our scheme, $A$ is public and $\vec s$ is secret. We set our approximate eigenvector to be
$\vec v=\mathrm{Powersof2}(\vec s)$, a vector of dimension $N=(n+1)\cdot\ell$ for
$\ell=\lfloor\log_2 q\rfloor+1$.

To encrypt $\mu\in\mathbb Z_q$, the encrypter generates a random $N\times m$ matrix $R$ with
$0/1$ entries, and sets $C=\mathrm{Flatten}(\mu\cdot I_N+\mathrm{BitDecomp}(R\cdot A))$, where
$I_N$ is the $N$-dimensional identity matrix. Since Flatten does not affect the product with
$\vec v$, we have:

$$
C\cdot\vec v=\mu\cdot\vec v+\mathrm{BitDecomp}(R\cdot A)\cdot\vec v
=\mu\cdot\vec v+R\cdot A\cdot\vec s=\mu\cdot\vec v+\text{small}
$$

Flatten ensures that the coefficients of $C$ are small, and therefore that $C$ has the proper
form of a ciphertext that permits our homomorphic operations. Decryption works as mentioned
previously.

To show that security is based on LWE, it is now enough to show that $C$ is statistically
independent of $\mu$ when $A$ is a uniformly random $m\times(n+1)$ matrix over $\mathbb Z_q$.
Let $C'=\mathrm{BitDecomp}^{-1}(C)$. Recall that $C$ is Flatten'd, and so
$C=\mathrm{Flatten}(C)=\mathrm{BitDecomp}(C')$. Therefore, $C$ reveals nothing more than $C'$.
But $C'=\mathrm{BitDecomp}^{-1}(\mu\cdot I_N)+R\cdot A$, and $R\cdot A$ is statistically uniform
by the leftover hash lemma when $m=O(n\log q)$ is chosen appropriately.

<a id="pdf-8edb94cfd852-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.95 -->

**Section 2.3, other preliminaries (p. 8).** For $n$, $q$, and
$\ell=\lfloor\log q\rfloor+1$, we define the procedures BitDecomp, $\mathrm{BitDecomp}^{-1}$,
Flatten and Powersof2 as described in the Introduction. $I_N$ denotes the $N$-dimensional
identity matrix.

<a id="pdf-8edb94cfd852-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=0.95 -->

## 3 Our LWE-Based FHE Scheme

**Section 3.1, basic encryption scheme: opening and Setup (p. 8).** Here, we formally describe
our basic encryption scheme (without homomorphic operations). This description matches the
description outlined in the Introduction. In our description, we split up KeyGen into three
parts Setup, SecretKeyGen and PublicKeyGen. We provide two decryption algorithms Dec and MPDec.
Dec is sufficient to recover the message $\mu$ when it is in a small space (e.g., $\{0,1\}$).
MPDec is an algorithm by Micciancio and Peikert [MP12] that can recover any
$\mu\in\mathbb Z_q$.

- $\mathrm{Setup}(1^\lambda,1^L)$: Choose a modulus $q$ of $\kappa=\kappa(\lambda,L)$ bits,
  lattice dimension parameter $n=n(\lambda,L)$, and error distribution
  $\chi=\chi(\lambda,L)$ appropriately for LWE that achieves at least $2^\lambda$ security
  against known attacks. Also, choose parameter $m=m(\lambda,L)=O(n\log q)$. Let
  $\textit{params}=(n,q,\chi,m)$. Let $\ell=\lfloor\log q\rfloor+1$ and $N=(n+1)\cdot\ell$.

<a id="pdf-8edb94cfd852-p009-b001"></a>
<!-- pdf-source: page=9; block=1; confidence=0.95 -->

**Section 3.1, SecretKeyGen, PublicKeyGen, Enc, Dec, MPDec (p. 9).**

- $\mathrm{SecretKeyGen}(\textit{params})$: Sample $\vec t\leftarrow\mathbb Z_q^{n}$. Output
  $sk=\vec s\leftarrow(1,-t_1,\dots,-t_n)\in\mathbb Z_q^{n+1}$. Let
  $\vec v=\mathrm{Powersof2}(\vec s)$.
- $\mathrm{PublicKeyGen}(\textit{params},sk)$: Generate a matrix
  $B\leftarrow\mathbb Z_q^{m\times n}$ uniformly and a vector $\vec e\leftarrow\chi^m$. Set
  $\vec b=B\cdot\vec t+\vec e$. Set $A$ to be the $(n+1)$-column matrix consisting of $\vec b$
  followed by the $n$ columns of $B$. Set the public key $pk=A$. (Remark: Observe that
  $A\cdot\vec s=\vec e$.)
- $\mathrm{Enc}(\textit{params},pk,\mu)$: To encrypt a message $\mu\in\mathbb Z_q$, sample a
  uniform matrix $R\in\{0,1\}^{N\times m}$ and output the ciphertext $C$ given below.

  $$
  C=\mathrm{Flatten}\bigl(\mu\cdot I_N+\mathrm{BitDecomp}(R\cdot A)\bigr)\in\mathbb Z_q^{N\times N}.
  $$
- $\mathrm{Dec}(\textit{params},sk,C)$: Observe that the first $\ell$ coefficients of
  $\vec v$ are $1,2,\dots,2^{\ell-1}$. Among these coefficients, let $v_i=2^i$ be in
  $(q/4,q/2]$. Let $C_i$ be the $i$-th row of $C$. Compute
  $x_i\leftarrow\langle C_i,\vec v\rangle$. Output $\mu'=\lfloor x_i/v_i\rceil$.
- $\mathrm{MPDec}(\textit{params},sk,C)$ (for $q$ a power of 2): Observe that $q=2^{\ell-1}$
  and the first $\ell-1$ coefficients of $\vec v$ are $1,2,\dots,2^{\ell-2}$, and therefore if
  $C\cdot\vec v=\mu\cdot\vec v+\text{small}$, then the first $\ell-1$ coefficients of
  $C\cdot\vec v$ are $\mu\cdot\vec g+\text{small}$, where $\vec g=(1,2,\dots,2^{\ell-2})$.
  Recover $\mathrm{LSB}(\mu)$ from $\mu\cdot 2^{\ell-2}+\text{small}$, then recover the
  next-least-significant-bit from $(\mu-\mathrm{LSB}(\mu))\cdot 2^{\ell-3}+\text{small}$, etc.
  (See [MP12] for the general $q$ case.)

Dec is a BitDecomp'd version of Regev's decryption procedure, applied to one row of the
ciphertext, which is a BitDecomp'd Regev ciphertext. (The extra rows will come into play in the
homomorphic operations). If $C$ is properly generated, then by the elementary properties of
BitDecomp and Powersof2, we have

$$
C\cdot\vec v=\mu\cdot\vec v+R\cdot A\cdot\vec s=\mu\cdot\vec v+R\cdot\vec e.
$$

Dec only uses the $i$-th coefficient of the above expression, which is
$x_i=\mu\cdot v_i+\langle R_i,\vec e\rangle$. The error $\langle R_i,\vec e\rangle$ has
magnitude at most $\|\vec e\|_1$. In general, if $x_i=\mu\cdot v_i+e'$ for some error $e'$ of
magnitude at most $q/8$, and if $v_i\in(q/4,q/2]$, then $x_i/v_i$ differs from $\mu$ by at most
$(q/8)/v_i<1/2$, and Dec uses rounding to output the correct value of $\mu$. (In the basic
scheme, we set $\chi$ to ensure that the error is so bounded with overwhelming probability.)

For the basic scheme (without homomorphic operations), one can take $n$ to be quasi-linear in
the security parameter $\lambda$ and $\kappa=O(\log n)$. When allowing homomorphic operations,
$L$ represents the circuit complexity of the functions that the scheme correctly evaluates
(roughly, $L$ is the multiplicative depth); we provide a detailed analysis later of how $L$
affects the other parameters.

<a id="pdf-8edb94cfd852-p009-b002"></a>
<!-- pdf-source: page=9; block=2; confidence=0.95 -->

**Section 3.2, security (pp. 9–10).** Observe that
$\mathrm{BitDecomp}^{-1}(C)=\mu\cdot G+R\cdot A$, where
$G=\mathrm{BitDecomp}^{-1}(I_N)$ is (the transpose of) the "primitive matrix" used by Micciancio
and Peikert [MP12] in their construction of lattice trapdoors, and the rows of $R\cdot A$ are
simply Regev [Reg05] encryptions of $0$ for dimension $n$. Assuming
$\mathrm{BitDecomp}^{-1}(C)$ hides $\mu$, $C$ does as well, since $C$ can be derived by applying
BitDecomp. Thus, the security of our basic encryption scheme follows directly from the following
lemma, used to prove the security of Regev's encryption scheme [Reg05].

<a id="pdf-8edb94cfd852-p010-b001"></a>
<!-- pdf-source: page=10; block=1; confidence=0.95 -->

**Lemma 1 (Implicit in [Reg05]).** Let $\textit{params}=(n,q,\chi,m)$ be such that the
$\mathrm{LWE}_{n,q,\chi}$ assumption holds. Then, for $m=O(n\log q)$ and $A$, $R$ as generated
above, the joint distribution $(A,R\cdot A)$ is computationally indistinguishable from uniform
over $\mathbb Z_q^{m\times(n+1)}\times\mathbb Z_q^{N\times(n+1)}$.

Concretely, it suffices to take $m>2n\log q$ [Reg05].

Like Brakerski [Bra12], we can also base security on GapSVP via a classical reduction from LWE
[Pei09, BLP+13]. Specifically, Peikert [Pei09] gives a classical reduction of GapSVP to LWE,
with the caveat that $q$ must be exponential in $n$. Brakerski notes that exponential $q$ was
unusable in previous FHE schemes, since the ratio of $q$ to the error level $B$ of "fresh"
ciphertexts cannot be exponential in $n$ for security reasons (since LLL [LLL82] could be used to
break such a scheme), and since $B$ must be very small to permit many homomorphic operations. As
in Brakerski's scheme, we do not have that problem. The error bound $B$ of fresh ciphertexts in
our scheme does not need to be small to permit many homomorphic operations; we only require
$q/B$ to be sub-exponential, and we can therefore permit $q$ to be exponential. Alternatively, we
can use a sub-exponential $q$ and base security on GapSVP via Brakerski et al.'s [BLP+13] recent
classical reduction to LWE that works even for polynomial-size moduli, with the caveat that, in
their reduction, the dimension of the GapSVP instances may be much smaller than the dimension of
the LWE instances.

<a id="pdf-8edb94cfd852-p010-b002"></a>
<!-- pdf-source: page=10; block=2; confidence=0.95 -->

**Section 3.3, homomorphic operations: MultConst, Add, Mult (pp. 10–11).** Recall that we
already described some basic "homomorphic" operations BitDecomp, $\mathrm{BitDecomp}^{-1}$,
Flatten, and Powersof2. These will play an important role in analyzing the homomorphic
operations supported by our scheme. We remark that BitDecomp could alternatively decompose with
respect to bases other than 2, or according to the Chinese Remainder Theorem.

We provide additional homomorphic operations MultConst, Add, Mult, NAND as follows.

- $\mathrm{MultConst}(C,\alpha)$: To multiply a ciphertext $C\in\mathbb Z_q^{N\times N}$ by known
  constant $\alpha\in\mathbb Z_q$, set $M_\alpha\leftarrow\mathrm{Flatten}(\alpha\cdot I_N)$ and
  output $\mathrm{Flatten}(M_\alpha\cdot C)$. Observe that:

  $$
  \begin{aligned}
  \mathrm{MultConst}(C,\alpha)\cdot\vec v&=M_\alpha\cdot C\cdot\vec v
  =M_\alpha\cdot(\mu\cdot\vec v+\vec e)=\mu\cdot(M_\alpha\cdot\vec v)+M_\alpha\cdot\vec e\\
  &=\alpha\cdot\mu\cdot\vec v+M_\alpha\cdot\vec e
  \end{aligned}
  $$

  Thus, the error increases by a factor of at most $N$, regardless of what element
  $\alpha\in\mathbb Z_q$ is used for multiplication. As in "classical" additively homomorphic
  encryption schemes, we could alternatively perform multiplication-by-constant $\alpha$ by
  recursively applying Add. But this multiplies the error size by at least $\alpha$, whereas
  MultConst increases the error by at most a factor of $N$, regardless of $\alpha$. An example
  application of MultConst is that we can perform homomorphic fast Fourier transformations
  (FFTs) natively over $\mathbb Z_q$ without error growth dependent on $q$. Previously, the
  error growth depended on the size of the field underlying the FFT [GHS12a, GHS12b],
  restricting the choice of field.
- $\mathrm{Add}(C_1,C_2)$: To add ciphertexts $C_1,C_2\in\mathbb Z_q^{N\times N}$, output
  $\mathrm{Flatten}(C_1+C_2)$. The correctness of this operation is immediate. Note that the
  addition of messages is over the full base ring $\mathbb Z_q$.
- $\mathrm{Mult}(C_1,C_2)$: To multiply ciphertexts $C_1,C_2\in\mathbb Z_q^{N\times N}$, output
  $\mathrm{Flatten}(C_1\cdot C_2)$. Observe that:

  $$
  \begin{aligned}
  \mathrm{Mult}(C_1,C_2)\cdot\vec v&=C_1\cdot C_2\cdot\vec v
  =C_1\cdot(\mu_2\cdot\vec v+\vec e_2)+\mu_2\cdot(\mu_1\vec v+\vec e_1)+C_1\cdot\vec e_2\\
  &=\mu_1\cdot\mu_2\cdot\vec v+\mu_2\cdot\vec e_1+C_1\cdot\vec e_2
  \end{aligned}
  $$

  As in Add, the multiplication operator is over the full base field $\mathbb Z_q$. In Mult, the
  new error depends on the old errors, the ciphertext $C_1$, and the message $\mu_2$. The
  dependence on the old errors seems unavoidable (and normal for LWE-based HE schemes), and
  observe that $C_1$ contributes at most a factor $N$ blowup of error, since all components of
  $C_1$ are restricted to $\{0,1\}$. The error growth based on the message $\mu_2$, however,
  presents a concern. In general, we must address this concern by using homomorphic operations
  in a way that restricts the message space to small messages. One way to do this is to
  consider Boolean circuits using only NAND operations: this would restrict the message space to
  $\{0,1\}$. We elaborate below.

*Transcription note.* The first line of the Mult display is transcribed as printed (checked
against the page image, 140 dpi): a "$+$" stands where an "$=$" is meant, i.e. the intended
expansion is
$C_1\cdot(\mu_2\cdot\vec v+\vec e_2)=\mu_2\cdot(\mu_1\vec v+\vec e_1)+C_1\cdot\vec e_2$. The
second line is the correct result.

<a id="pdf-8edb94cfd852-p011-b001"></a>
<!-- pdf-source: page=11; block=1; confidence=0.95 -->

**Section 3.3, NAND (p. 11).**

- $\mathrm{NAND}(C_1,C_2)$: To NAND ciphertexts $C_1,C_2\in\mathbb Z_q^{N\times N}$ that are
  known to encrypt messages $\mu_1,\mu_2\in\{0,1\}$, output $\mathrm{Flatten}(I_N-C_1\cdot C_2)$.
  Observe that:

  $$
  \mathrm{NAND}(C_1,C_2)\cdot\vec v=(I_N-C_1\cdot C_2)\cdot\vec v
  =(1-\mu_1\cdot\mu_2)\cdot\vec v-\mu_2\cdot\vec e_1-C_1\cdot\vec e_2
  $$

  Note here that the NAND homomorphic operation maintains the invariant that if the input
  messages are in $\{0,1\}$, then the output ciphertext will also encryption of $\{0,1\}$, thus
  guaranteeing small messages. Note that since $\mu_2\in\{0,1\}$, the error is increased by a
  factor of at most $N+1$.

<a id="pdf-8edb94cfd852-p011-b002"></a>
<!-- pdf-source: page=11; block=2; confidence=0.95 -->

**Section 3.3, "Circuits" (p. 11).** By iteratively applying the homomorphic operations above,
different types of (bounded-depth) circuits may be homomorphically computed while maintaining
correctness of decryption.

The simplest case to analyze is the case of Boolean circuits computed over encryptions of
$\{0,1\}$ values. In this case, the circuit can be converted to use only NAND gates, and through
appropriate leveled application of the NAND homomorphic operation, the final ciphertext's error
will be bounded by $(N+1)^{L}\cdot B$, where $L$ is the NAND-depth of the circuit, and $B$ is the
original bound on the error of a fresh encryption of $\{0,1\}$.

More generally, with more care, we may consider arithmetic circuits over $\mathbb Z_q$ that make
use of gates that perform addition, multiplication, or multiplication by a known constant.
However, as we have seen in the case of multiplication gates, the error growth may depend on the
values being encrypted in intermediate computations. One way to deal with this is to focus on
situations where (1) all input values are known to encrypt values bounded by some value $T$, and
(2) the arithmetic circuit is chosen to guarantee that all intermediate values are also bounded
by $T'$ whenever the circuit inputs are constrained to values bounded by $T$. In such a
situation, the final ciphertext's error will be bounded by $(N+T')^{L}\cdot B$, where $L$ is the
depth of the arithmetic circuit, and $B$ is the original bound on the error of fresh encryptions
of values smaller than $T$. For example, in this way, we can homomorphically evaluate
polynomials of degree $d$ in this large-message-space variant when the initial messages are
bounded by roughly $q^{1/d}$, achieving a scheme that is "somewhat homomorphic" [Gen09]. Another
example application would be to convert encryptions of a polynomially bounded set of small values
to encryptions of binary values, by using an appropriate arithmetic circuit for the conversion.
Once converted to encryptions of binary values, a NAND-based Boolean circuit could be used for
further computations.

<a id="pdf-8edb94cfd852-p011-b003"></a>
<!-- pdf-source: page=11; block=3; confidence=0.95 -->

**Section 3.4, parameters, performance and optimizations (pp. 11–12).** Suppose that
Flatten'd ciphertexts $C_1,C_2$ encrypt $\mu_1,\mu_2\in\{0,1\}$ under approximate eigenvector
$\vec v$ with $B$-bounded error – that is, $C_i\cdot\vec v=\mu_i\cdot\vec v+\vec e_i$ where
$|\vec e_i|_\infty\le B$. Then $C^{\mathrm{NAND}}\leftarrow\mathrm{NAND}(C_1,C_2)$ encrypts
$\mathrm{NAND}(\mu_1,\mu_2)\in\{0,1\}$ under $\vec v$ with $(N+1)B$-bounded error. As long as
$q/B>8(N+1)^{L}$, we can evaluate a depth-$L$ circuit of NANDs over $B$-bounded ciphertexts to
obtain a $q/8$-bounded ciphertext, which Dec will decrypt correctly.

As in previous LWE-based FHE schemes, $n$ (hence $N$) must increase linearly with $\log(q/B)$ to
maintain fixed $2^\lambda$ security against known attacks, so $q/B$ grows more like
$\exp(L\log L)$. We will brush such issues under the rug and view $n$ as a fixed parameter.
Choosing $\chi$ so that $B$ is not too large, and since in practice there is no reason to have
$\kappa=\log q$ grow super-linearly with $n$, we have
$\kappa=O(L\log N)=O(L(\log n+\log\kappa))=O(L\log n)$, similar to [BGV12, Bra12]. Given that the
NAND procedure is dominated by multiplication of two $N\times N$ matrices for
$N=O(n\kappa)=\tilde O(nL)$, we have the following theorem to characterize the performance of
our FHE scheme.

<a id="pdf-8edb94cfd852-p012-b001"></a>
<!-- pdf-source: page=12; block=1; confidence=0.95 -->

**Theorem 3.** For dimension parameter $n$ and depth parameter $L$, our FHE scheme evaluates
depth-$L$ circuits of NAND gates with $\tilde O((nL)^{\omega})$ field operations per gate, where
$\omega<2.3727$ is the matrix multiplication exponent.

This compares favorably with previous LWE-based FHE schemes, which all have at least
$\tilde O(n^3L)$ field operations per gate [BV11b, BGV12, Bra12].

Theorem 3 hides some factors, both good and bad. On the good size, it hides the fact that
ciphertext matrices in our scheme have $0/1$ entries, and therefore can be multiplied faster than
if they were general matrices over $\mathbb Z_q$. In previous LWE-based FHE schemes, the field
operations involve multiplying a small number with a general number of $\mathbb Z_q$, which has
complexity $\tilde O(\kappa)=\tilde O(L)$. So, previous LWE-based FHE schemes have real
complexity $\tilde O(n^3L^2)$ whereas ours remains $\tilde O((nL)^{\omega})$. On the bad side,
Theorem 3 hides logarithmic factors in the dimension of the ciphertext matrices, since
$N=O(n\kappa)=O(nL\log n)$. We note that typically $n$ will dominate $L$, since for very deep
circuits, one would want to use Gentry's bootstrapping technique [Gen09] to make the per-gate
computation independent of $L$.

<a id="pdf-8edb94cfd852-p012-b002"></a>
<!-- pdf-source: page=12; block=2; confidence=0.95 -->

**Section 3.4, bootstrapping (p. 12).** Since bootstrapping involves homomorphically evaluating
the decryption function, and since Dec is essentially Regev decryption [Reg05], bootstrapping
works as in previous LWE-based FHE schemes. In particular, we can use techniques from [BV11b] to
reduce the dimension and modulus-size of the ciphertext before bootstrapping, so that the
complexity of decryption (and hence bootstrapping) is completely independent of the depth $L$ of
the circuit that was evaluated to arrive at that ciphertext. Regev decryption can be evaluated in
$O(\log n)$ depth. Due to the logarithmic depth, one can take $q/B$ to be quasi-polynomial in
$n$, and base security on LWE for quasi-polynomial factors.

## ===== blueprint/src/references/alperin-sheriff-peikert-2014-bootstrapping.md =====

<!-- generated-by: maintainer transcription of the passages used (DW-7) -->
<!-- source-pdf-sha256: cecd346d2e879ff865c23fe977e172e1068f20b01c7f555a419d2f3d5ec2c0da -->
<!-- validation-status: scoped transcription for DW-7; awaiting Codex source review -->

# Faster Bootstrapping with Polynomial Error

Jacob Alperin-Sheriff and Chris Peikert. *CRYPTO 2014*, LNCS 8616, pp. 297–314; IACR ePrint
2014/094, version dated June 13, 2014 (18 pages; tag `AP14`).

**Scope.** Only the passages that the GSW Lean (phase 5) and the phase-6 plan use are
transcribed (DW-7; GSW ruling Q14): §2.2 (symmetric groups and permutation matrices), §3
(the GSW variant: Claim 3.1, Equation (3.1), the scheme, Definitions 3.2–3.3, Claim 3.4,
Lemma 3.5, Corollary 3.6), §4.1–§4.2 (HEPerm, Equation (4.1), Lemma 4.1, Corollary 4.2), and
from §5 the specification, the procedures, Theorem 5.1, the security paragraph and Lemma 5.2
(the phase-6 cross-check). The PDF is not committed. Anchors use the physical PDF page; the
printed page is one less (`p008` is printed page 7). The scoped raw extraction is
`alperin-sheriff-peikert-2014-bootstrapping.raw.md`. Mathematics is set in LaTeX; the
paper's operators are written $\boxplus$ (homomorphic addition), $\boxdot$ (homomorphic
multiplication) and ⧇ (homomorphic composition, printed as a boxed small circle). The wording
is the paper's. Notes marked *Transcription note* are not part of the source.

<a id="pdf-cecd346d2e87-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.95 -->

**Section 2.2, symmetric groups and $\mathbb Z_q$-embeddings (printed p. 6).** Here we recall
some basic facts about symmetric groups, which can be found in most abstract algebra textbooks,
e.g., [Jac12]. Let $S_r$ denote the symmetric group of order $r$, i.e., the group of
permutations (bijections) $\pi:\{1,\dots,r\}\to\{1,\dots,r\}$ with function composition as the
group operation. The group $S_r$ is isomorphic to the multiplicative group of $r$-by-$r$
permutation matrices (i.e., 0-1 matrices with exactly one nonzero element in each row and each
column), via the map that associates $\pi\in S_r$ with the permutation matrix
$\mathbf P_\pi=[\mathbf e_{\pi(1)}\ \mathbf e_{\pi(2)}\ \cdots\ \mathbf e_{\pi(r)}]$, where
$\mathbf e_i\in\{0,1\}^r$ is the $i$th standard basis vector. For the remainder of this work we
identify permutations with their associated permutation matrices.

The additive cyclic group $(\mathbb Z_r,+)$ embeds into the symmetric group $S_r$ via the
injective homomorphism that sends the generator $1\in\mathbb Z_r$ to the "cyclic shift"
permutation $\pi\in S_r$, defined as $\pi(i)=i+1$ for $1\le i<r$ and $\pi(r)=1$.³ Clearly, this
embedding and its inverse can be computed efficiently. Notice also that the permutation matrices
in the image of this embedding can be represented more compactly by just their first column,
because the remaining columns are just the successive cyclic shifts of this column. Similarly,
such permutation matrices can be multiplied in only $O(r^2)$ operations, since we only need to
multiply one matrix by the first column of the other.

For our efficient bootstrapping algorithm, we need to efficiently embed a group
$(\mathbb Z_q,+)$, for some sufficiently large $q$ of our choice, into a symmetric group of order
much smaller than $q$ (e.g., polylogarithmic in $q$). This can be done as follows: suppose that
$q=r_1r_2\cdots r_t$, where the $r_i$ are pairwise coprime. Then by the Chinese Remainder
Theorem, the ring $\mathbb Z_q$ is isomorphic to the direct product of rings
$\mathbb Z_{r_1}\times\mathbb Z_{r_2}\times\cdots\times\mathbb Z_{r_t}$, and hence their additive
groups are isomorphic as well. Combining this with the group embeddings of $(\mathbb Z_{r_i},+)$
into $S_{r_i}$, we have an (efficient) group embedding from $(\mathbb Z_q,+)$ into
$S_{r_1}\times S_{r_2}\times\cdots\times S_{r_t}$.⁴

Importantly for our purposes, $q$ can be exponentially large in terms of $\max_i r_i$ above.
This can be shown using lower bounds on the second Chebyshev function

$$
\psi(x):=\sum_{p^k\le x}\log p=\log\Bigl(\prod_{p\le x}p^{\lfloor\log_p x\rfloor}\Bigr),
$$

where the first summation is over all prime powers $p^k\le x$, and the second is over all
primes $p\le x$; note that $p^{\lfloor\log_p x\rfloor}$ is the largest power of $p$ not exceeding
$x$. Therefore, the product $q$ of all maximal prime powers $r_i=p^{\lfloor\log_p x\rfloor}\le x$
is $\exp(\psi(x))$. Asymptotically, it is known that $\psi(x)=x\pm O(x/\log x)$, and we also have
the nonasymptotic bound $\psi(x)\ge 3x/4$ for all $x\ge 7$ [Sch76, Theorem 11]. In summary:

**Lemma 2.2.** For all $x\ge 7$, the product of all maximal prime powers $r_i\le x$ is at least
$\exp(3x/4)$.

For any given lower bound $q_0\ge 191>\exp(21/4)$, we can therefore efficiently find a
$q\ge q_0$ whose maximal prime-power divisors are all at most $x=\frac43\log q_0\ge 7$.

Footnote 3: This is just a special case of Cayley's theorem, which says that any group $G$
embeds into the symmetric group $S_{|G|}$. Footnote 4: The latter group can be seen as a
subgroup of $S_r$ for $r=\sum_i r_i$, but it will be more efficient to retain the product
structure.

<a id="pdf-cecd346d2e87-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.95 -->

## 3 GSW Cryptosystem

**Section 3, opening (printed p. 6).** Here we present a variant of the Gentry-Sahai-Waters
homomorphic encryption scheme [GSW13] (hereafter called GSW), which we believe is simpler to
understand at a technical level. We also give a tighter analysis of its error growth under
homomorphic operations.

<a id="pdf-cecd346d2e87-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.95 -->

**Section 3.1, background; Claim 3.1 and Equation (3.1) (printed p. 7).** We first recall some
standard background (see, e.g., [MP12] for further details). For a modulus $q$, let
$\ell=\lceil\log_2 q\rceil$ and define the "gadget" (column) vector
$\mathbf g=(1,2,4,\dots,2^{\ell-1})\in\mathbb Z_q^{\ell}$. Note that the penultimate entry
$2^{\ell-2}$ of $\mathbf g$ is in the interval $[q/4,q/2)$ mod $q$. It will be convenient to use
the following randomized "decomposition" function.

**Claim 3.1 (Adapted from [MP12]).** There is a randomized, efficiently computable function
$\mathbf g^{-1}:\mathbb Z_q\to\mathbb Z^{\ell}$ such that $\mathbf x\leftarrow\mathbf g^{-1}(a)$
is subgaussian with parameter $O(1)$, and always satisfies $\langle\mathbf g,\mathbf x\rangle=a$.

Briefly, the algorithm described in the claim works as follows (though for our application it is
not necessary to understand its internals): let $\mathbf S\in\mathbb Z^{\ell\times\ell}$ be the
basis of the lattice
$\Lambda^\perp(\mathbf g^t)=\{\mathbf z\in\mathbb Z^\ell:\langle\mathbf g,\mathbf z\rangle=0\in\mathbb Z_q\}$
as constructed in [MP12], whose Gram-Schmidt vectors all have Euclidean norm $O(1)$. Given
$a\in\mathbb Z_q$, run a randomized version of the nearest-plane algorithm [Bab85] with basis
$\mathbf S$ to sample from the coset
$\Lambda^\perp_a(\mathbf g^t)=\{\mathbf x:\langle\mathbf g,\mathbf x\rangle=a\}$, where in each
iteration of the algorithm we choose the coefficient of the $i$th basis vector to have
expectation zero over $\{c_i-1,c_i\}$ for an appropriate $c_i\in\frac1q\mathbb Z\cap[0,1)$. In
particular, the coefficient is subgaussian with parameter $\sqrt{2\pi}$ given any fixed values
of the previous coefficients. The final output $\mathbf x$ is the linear combination of the
(orthogonal) Gram-Schmidt vectors of $\mathbf S$ with these coefficients, and is therefore
subgaussian with parameter $O(1)$.

For vectors and matrices over $\mathbb Z_q$, define the randomized function
$\mathbf G^{-1}:\mathbb Z_q^{n\times m}\to\mathbb Z^{n\ell\times m}$ by applying
$\mathbf g^{-1}$ independently to each entry. Notice that for any
$\mathbf A\in\mathbb Z_q^{n\times m}$, if $\mathbf X\leftarrow\mathbf G^{-1}(\mathbf A)$ then
$\mathbf X$ has subgaussian parameter $O(1)$ and

$$
\mathbf G\cdot\mathbf X=\mathbf A,\qquad\text{where }\mathbf G=\mathbf g^t\otimes\mathbf I_n
=\mathrm{diag}(\mathbf g^t,\dots,\mathbf g^t)\in\mathbb Z_q^{n\times n\ell}\tag{3.1}
$$

is the block matrix with $n$ copies of $\mathbf g^t$ as diagonal blocks, and zeros elsewhere.

*Transcription note.* Under the standard Kronecker convention $\mathbf g^t\otimes\mathbf I_n$
and $\mathrm{diag}(\mathbf g^t,\dots,\mathbf g^t)=\mathbf I_n\otimes\mathbf g^t$ differ by a
column permutation; the printed text gives both (Gate 41 audit, roadmap section). The Lean
follows the block-diagonal description.

<a id="pdf-cecd346d2e87-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=0.95 -->

**Section 3.2, cryptosystem and homomorphic operations: parameters and the two differences
(printed pp. 7–8).** The GSW scheme is parameterized by a dimension $n$, a modulus $q$ with
$\ell=\lceil\log_2 q\rceil$, and some error distribution $\chi$ over $\mathbb Z$ which we assume
to be subgaussian. Formally, the message space is the ring of integers $\mathbb Z$, though for
bootstrapping we only work with ciphertexts encrypting messages in
$\{0,1\}\subset\mathbb Z$. The ciphertext space is
$\mathcal C=\mathbb Z_q^{n\times n\ell}$. For simplicity we present just a symmetric-key scheme,
which is sufficient for our purposes (it can be converted to a public-key or even
attribute-based scheme, as described in [GSW13]).

Our GSW variant differs from the original scheme described in [GSW13] in two main ways:

1. In [GSW13], a ciphertext is a square binary matrix $\mathbf C\in\{0,1\}^{n\ell}$, a secret key
   is a "structured" mod-$q$ vector $\mathbf s\in\mathbb Z_q^{n\ell}$ (having large entries), and
   $\mathbf s$ is an "approximate mod-$q$ eigenvector" of $\mathbf C$, in the sense that
   $\mathbf s^t\mathbf C\approx\mu\mathbf s^t\pmod q$, where $\mu\in\mathbb Z$ is the message.

   In our variant, a ciphertext is a rectangular mod-$q$ matrix
   $\mathbf C\in\mathbb Z_q^{n\times n\ell}$, a secret key is some (unstructured, short) integer
   vector $\mathbf s\in\mathbb Z^n$, and
   $\mathbf s^t\mathbf C\approx\mu\cdot\mathbf s^t\mathbf G\pmod q$, i.e., $\mathbf s$ and
   $\mathbf G^t\mathbf s$ are corresponding left- and right- "approximate singular vectors" of
   $\mathbf C$.

   The difference between these two variants turns out to be purely syntactic, in that we can
   efficiently and "losslessly" switch between them (without needing the secret key). However,
   we believe that our variant leads to simpler notation and easier-to-understand operations and
   analysis.
2. The second difference is more substantial: our homomorphic multiplication procedure uses the
   *randomized* $\mathbf G^{-1}(\cdot)$ operation from Claim 3.1. This yields a few important
   advantages, such as a very tight and simple error analysis using subgaussianity (see
   Lemma 3.5), and the ability to *completely re-randomize* the error in a ciphertext (see
   Corollary 3.6).

*Transcription note.* "$\{0,1\}^{n\ell}$" for the square matrix is as printed (an
$n\ell\times n\ell$ matrix is meant).

<a id="pdf-cecd346d2e87-p009-b001"></a>
<!-- pdf-source: page=9; block=1; confidence=0.95 -->

**Section 3.2, the scheme (printed p. 8).** We now describe the scheme formally.

- $\mathsf{GSW.Gen}()$: choose $\bar{\mathbf s}\leftarrow\chi^{n-1}$ and output secret key
  $\mathbf s=(\bar{\mathbf s},1)\in\mathbb Z^n$.
- $\mathsf{GSW.Enc}((\bar{\mathbf s},1),\mu\in\mathbb Z)$: choose
  $\bar{\mathbf C}\leftarrow\mathbb Z_q^{(n-1)\times n\ell}$ and $\mathbf e\leftarrow\chi^m$, let
  $\mathbf b^t=\mathbf e^t-\bar{\mathbf s}^t\bar{\mathbf C}\pmod q$, and output the ciphertext

  $$
  \mathbf C=\begin{pmatrix}\bar{\mathbf C}\\ \mathbf b^t\end{pmatrix}+\mu\mathbf G\in\mathcal C,
  $$

  where $\mathbf G$ is as defined in Equation (3.1). Notice that
  $\mathbf s^t\mathbf C=\mathbf e^t+\mu\cdot\mathbf s^t\mathbf G\pmod q$.
- $\mathsf{GSW.Dec}(\mathbf s,\mathbf C\in\mathcal C)$: let $\mathbf c$ be the penultimate
  column of $\mathbf C$, and output $\mu=\lfloor\langle\mathbf s,\mathbf c\rangle\rceil_2$, where
  $\lfloor\cdot\rceil_2:\mathbb Z_q\to\{0,1\}$ indicates whether its argument is closer modulo $q$
  to $0$ or to $2^{\ell-2}$ (the penultimate entry of $\mathbf g$).⁵
- **Homomorphic addition** is defined as $\mathbf C_1\boxplus\mathbf C_2=\mathbf C_1+\mathbf C_2$.
- **Homomorphic multiplication** is defined as
  $\mathbf C_1\boxdot\mathbf C_2\leftarrow\mathbf C_1\cdot\mathbf G^{-1}(\mathbf C_2)$, and is
  *right associative*. Notice that this is a randomized procedure, because $\mathbf G^{-1}$ is
  randomized.

The IND-CPA security of the scheme follows immediately from the assumed hardness of
$\mathsf{LWE}_{n-1,q,\chi}$, where the entries of the secret are drawn from the error
distribution $\chi$ (which is no easier than for a uniformly random secret; see [ACPS09,
Lemma 2]). This is because a fresh ciphertext is just $\mu\mathbf G$ plus a matrix of $n\ell$
independent LWE samples under secret $\bar{\mathbf s}$, which are pseudorandom by assumption and
hence hide $\mu\mathbf G$.

Footnote 5: Note that we can decrypt messages in $\mathbb Z\cap[-\frac q2,\frac q2)$, or any
other canonical set of representatives of $\mathbb Z_q$, by "decoding" $\mathbf s^t\mathbf C$ to
the nearest multiple of $\mathbf s^t\mathbf G$. The above decryption algorithm will be
sufficient for our purposes.

*Transcription note.* "$\mathbf e\leftarrow\chi^m$" is as printed; with $n\ell$ columns,
$m=n\ell$ is meant.

<a id="pdf-cecd346d2e87-p009-b002"></a>
<!-- pdf-source: page=9; block=2; confidence=0.95 -->

**Definition 3.2.** We say that a ciphertext $\mathbf C$ is *designed* to encrypt message
$\mu\in\mathbb Z$ (under a secret key $\mathbf s$) if it is a fresh encryption of $\mu$, or if
$\mathbf C=\mathbf C_1\boxplus\mathbf C_2$ where $\mathbf C_1,\mathbf C_2$ are respectively
designed to encrypt $\mu_1,\mu_2\in\mathbb Z$ and $\mu=\mu_1+\mu_2$, or similarly for homomorphic
multiplication.

<a id="pdf-cecd346d2e87-p009-b003"></a>
<!-- pdf-source: page=9; block=3; confidence=0.95 -->

**Definition 3.3.** We say that a ciphertext $\mathbf C$ that is designed to encrypt
$\mu\in\mathbb Z$ (under $\mathbf s$) has *error* vector $\mathbf e^t\in\mathbb Z^{n\ell}$ if
$\mathbf s^t\mathbf C-\mu\cdot\mathbf s^t\mathbf G=\mathbf e^t\pmod q$.

For convenience later on, we also say the matrix $\mu\mathbf G$ is designed to encrypt $\mu$, and
has error $\mathbf 0$. (This is essentially implied by the above definitions, since $\mu\mathbf G$
is indeed a fresh encryption of $\mu$, assuming that zero is in the support of $\chi$.) The next
claim on the correctness of decryption follows immediately from the fact that
$\mathbf s=(\bar{\mathbf s},1)$ and the penultimate column of $\mathbf G$ is
$(0,\dots,0,2^{\ell-2})$, where $2^{\ell-2}\in[q/4,q/2)\bmod q$.

<a id="pdf-cecd346d2e87-p009-b004"></a>
<!-- pdf-source: page=9; block=4; confidence=0.95 -->

**Claim 3.4.** If $\mathbf C$ is designed to encrypt some $\mu\in\{0,1\}\subset\mathbb Z$, and has
error vector $\mathbf e^t$ whose penultimate coordinate has magnitude less than $q/8$, then
$\mathsf{GSW.Dec}(\mathbf s,\mathbf C)$ correctly outputs $\mu$.

We now analyze the behavior of the error terms under homomorphic operations.

<a id="pdf-cecd346d2e87-p010-b001"></a>
<!-- pdf-source: page=10; block=1; confidence=0.95 -->

**Lemma 3.5.** Suppose $\mathbf C_1,\mathbf C_2$ are respectively designed to encrypt
$\mu_1,\mu_2\in\mathbb Z$ and have error vectors $\mathbf e_1^t,\mathbf e_2^t$. Then
$\mathbf C_1\boxplus\mathbf C_2$ has error vector $\mathbf e_1^t+\mathbf e_2^t$, and
$\mathbf C_1\boxdot\mathbf C_2$ has error vector $\mathbf e_1^t\mathbf X+\mu_1\mathbf e_2^t$,
where $\mathbf X\leftarrow\mathbf G^{-1}(\mathbf C_2)$ is the matrix used in the evaluation of
$\boxdot$. In particular, for any values of $\mathbf C_i,\mathbf e_i,\mu_i$, the latter error
vector is of the form $\mathbf e^t+\mu_1\mathbf e_2^t$, where the entries of $\mathbf e$ are
independent and subgaussian with parameter $O(\|\mathbf e_1\|)$.

Importantly, the error in $\mathbf C_1\boxdot\mathbf C_2$ is quasi-additive and asymmetric with
respect to the errors in $\mathbf C_1,\mathbf C_2$: while the first error vector
$\mathbf e_1^t$ is multiplied by a short (subgaussian) matrix $\mathbf X$, the second error
vector $\mathbf e_2^t$ is only multiplied by the (scalar) message $\mu_1$, which we will ensure
remains in $\{0,1\}$.

<a id="pdf-cecd346d2e87-p010-b002"></a>
<!-- pdf-source: page=10; block=2; confidence=0.95 -->

**Proof of Lemma 3.5.** The first claim is immediate, by linearity. For the second claim, because
$\mathbf G\cdot\mathbf X=\mathbf C_2$ we have

$$
\begin{aligned}
\mathbf s^t(\mathbf C_1\boxdot\mathbf C_2)&=\mathbf s^t\mathbf C_1\cdot\mathbf X\\
&=(\mathbf e_1^t+\mu_1\cdot\mathbf s^t\mathbf G)\mathbf X\\
&=\mathbf e_1^t\mathbf X+\mu_1(\mathbf e_2^t+\mu_2\cdot\mathbf s^t\mathbf G)\\
&=(\mathbf e_1^t\mathbf X+\mu_1\mathbf e_2^t)+\mu_1\mu_2\cdot\mathbf s^t\mathbf G.
\end{aligned}
$$

<a id="pdf-cecd346d2e87-p010-b003"></a>
<!-- pdf-source: page=10; block=3; confidence=0.95 -->

**Section 3.3, chains (printed p. 9).** As observed in [BV14], the asymmetric noise growth
allows for performing a long chain of homomorphic multiplications while only incurring a
polynomial-factor error growth, because $\boxdot$ is defined to be right associative. For
convenience of analysis, in such a chain we always include the fixed ciphertext $\mathbf G$,
which is designed to encrypt $\mu=1$ and has zero error, as the rightmost ciphertext in the
chain. This ensures that the error vector of the output ciphertext is subgaussian and essentially
independent of the errors in the input ciphertexts (apart from their lengths), which leads to a
simpler and tighter analysis. (In [BV14] a weaker independence guarantee was achieved by a
separate "partial re-randomization" procedure, which requires additional public key material.)

**Corollary 3.6.** Suppose that $\mathbf C_i$ for $i\in[k]$ are respectively designed to
encrypt $\mu_i\in\{0,\pm1\}$ and have error vectors $\mathbf e_i^t$. Then for any fixed values of
these variables,

$$
\mathbf C\leftarrow\mathop{\boxdot}_{i\in[k]}\mathbf C_i\boxdot\mathbf G
=\mathbf C_1\boxdot(\mathbf C_2\boxdot(\cdots(\mathbf C_k\boxdot\mathbf G)\cdots))
$$

has an error vector whose entries are mutually independent and subgaussian with parameter
$O(\|\mathbf e\|)$, where $\mathbf e^t=(\mathbf e_1^t,\dots,\mathbf e_k^t)\in\mathbb Z^{kn\ell}$
is the concatenation of the individual error vectors.

**Proof.** By Lemma 3.5, the error vector in $\mathbf C$ is $\sum_i\mathbf e_i^t\mathbf X_i$,
where each $\mathbf e_i^t\mathbf X_i$ is a fresh independent vector that has mutually
independent coordinates and is subgaussian with parameter $O(\|\mathbf e_i\|)$. The claim then
follows by Pythagorean additivity.

<a id="pdf-cecd346d2e87-p010-b004"></a>
<!-- pdf-source: page=10; block=4; confidence=0.95 -->

## 4 Homomomorphic Encryption for Symmetric Groups

**Section 4, opening (printed p. 9).** Brakerski and Vaikuntanathan [BV14] showed how to use the
GSW encryption scheme to homomorphically compose permutations of five elements (i.e., to
homomorphically compute the group operation in the symmetric group $S_5$) with small additive
noise growth; the use of $S_5$ comes from its essential role in Barrington's theorem [Bar86]. In
[BV14], the homomorphic composition of permutations is intertwined with the evaluation of a
branching program given by Barrington's theorem. Here we give, as a "first-class object," a
homomorphic cryptosystem for any symmetric group $S_r$. The ability to use several different
small values of $r$, along with a homomorphic equality test that we design, will be central to
our bootstrapping algorithm.

*Transcription note.* The section title is printed "Homomomorphic" (sic).

<a id="pdf-cecd346d2e87-p011-b001"></a>
<!-- pdf-source: page=11; block=1; confidence=0.95 -->

**Section 4.1, HEPerm: encryption, composition (Equation (4.1)) and equality test (printed
p. 10).** We now describe our (symmetric-key) homomorphic encryption scheme for symmetric groups,
called HEPerm. Let $\mathcal C$ denote the ciphertext space for an appropriate instantiation of
the GSW scheme, which we treat as a "black box." A secret key $sk$ for HEPerm is simply a secret
key for the GSW scheme.

- $\mathsf{HEPerm.Enc}(sk,\pi\in S_r)$: let
  $\mathbf P=(p_{i,j})\in\{0,1\}^{r\times r}$ be the permutation matrix associated with $\pi$.
  Output an entry-wise encryption of $\mathbf P$, i.e., the ciphertext

  $$
  \mathbf C=(c_{i,j})\in\mathcal C^{r\times r},\quad\text{where }c_{i,j}\leftarrow\mathsf{Enc}(sk,p_{i,j}).
  $$

(Decryption follows in the obvious manner.) As with the GSW system, we say that a ciphertext
$\mathbf C\in\mathcal C^{r\times r}$ is *designed* to encrypt a permutation $\pi\in S_r$ (or its
permutation matrix $\mathbf P_\pi$) if its $\mathcal C$-entries are designed to encrypt the
corresponding entries of $\mathbf P_\pi$. For convenience, we let
$\mathbf J\in\mathcal C^{r\times r}$ denote the ciphertext that encrypts the identity permutation
with zero noise, which is built in the expected way from the fixed zero-error GSW ciphertexts
that encrypt $0$ and $1$.

We now show how to homomorphically compute two operations: the standard composition operation
for permutations, and an equality test.

**Homomorphic composition $\mathbf C^\pi$ ⧇ $\mathbf C^\sigma$:** on ciphertexts
$\mathbf C^\pi=(c^\pi_{i,j}),\mathbf C^\sigma=(c^\sigma_{i,j})\in\mathcal C^{r\times r}$
encrypting permutations $\pi,\sigma\in S_r$ respectively, we compute one encrypting the
permutation $\pi\circ\sigma$ by homomorphically evaluating the naïve matrix-multiplication
algorithm.⁶ That is, output $\mathbf C=(c_{i,j})\in\mathcal C^{r\times r}$ where

$$
c_{i,j}\leftarrow\mathop{\boxplus}_{\ell\in[r]}\bigl(c^\pi_{i,\ell}\boxdot c^\sigma_{\ell,j}\bigr)\in\mathcal C.\tag{4.1}
$$

Just like $\boxdot$, we define ⧇ to be right associative.

**Homomorphic equality test $\mathsf{Eq?}(\mathbf C^\pi=(c^\pi_{i,j}),\sigma\in S_r)$:** given a
ciphertext encrypting some permutation $\pi\in S_r$ and a permutation $\sigma\in S_r$ (in the
clear), output a ciphertext $c\in\mathcal C$ encrypting $1$ if $\pi=\sigma$ and $0$ otherwise, as

$$
c\leftarrow\mathop{\boxdot}_{i\in[r]}c^\pi_{\sigma(i),i}\boxdot g,
$$

where $g\in\mathcal C$ denotes the fixed zero-error encryption of $1$. (Recall that $\boxdot$ is
right associative.)

Observe that for the above two operations, the GSW ciphertext(s) in the output are designed to
encrypt the appropriate $\{0,1\}$-message. For Compose this is simply by correctness of the
matrix-multiplication algorithm. For Eq? this is because the output ciphertext is designed to
encrypt $1$ if and only if every $c_{\sigma(i),i}$ is designed to encrypt $1$, which is the case
if and only if $\mathbf C^\pi$ is in fact designed to encrypt $\sigma$. All that remains is to
analyze the behavior of the error terms, which we do next.

Footnote 6: Note that asymptotically faster algorithms (e.g., Strassen's) do not appear suitable
here, because the intermediate steps of these algorithms can result in values having magnitude
greater than one, which can cause the error in the ciphertexts to grow much faster. In any case,
this will not matter much in our application, since $r$ will be small.

<a id="pdf-cecd346d2e87-p012-b001"></a>
<!-- pdf-source: page=12; block=1; confidence=0.95 -->

**Section 4.2, analysis; Lemma 4.1 (printed p. 11).** Recalling that the GSW scheme is
parameterized by $n$ and $q$, denote its space of error vectors by $\mathcal E=\mathbb Z^m$ where
$m=n\lceil\log_2 q\rceil$. The Euclidean norm on $\mathcal E^r=\mathbb Z^{mr}$ is defined in the
expected way. In what follows it is often convenient to consider vectors and matrices over
$\mathcal E$, i.e., each entry is itself a (row) vector in $\mathcal E=\mathbb Z^m$, and we
switch between $\mathcal E^{h\times w}$ and $\mathbb Z^{h\times wm}$ as is convenient.

The following lemma describes the behavior of errors under the homomorphic composition
operation ⧇. Note that working with vectors and matrices over $\mathcal E$ lets us write a
statement that is syntactically very similar to the one from Lemma 3.5, with a very similar
proof.

**Lemma 4.1.** Let $\mathbf C^\pi,\mathbf C^\sigma\in\mathcal C^{r\times r}$ respectively be
designed to encrypt permutation matrices $\mathbf P_\pi,\mathbf P_\sigma\in\{0,1\}^{r\times r}$
with error matrices $\mathbf E_\pi,\mathbf E_\sigma\in\mathcal E^{r\times r}$. Then for any fixed
values of these variables, $\mathbf C^\pi$ ⧇ $\mathbf C^\sigma$ has error matrix
$\mathbf E+\mathbf P_\pi\cdot\mathbf E_\sigma\in\mathcal E^{r\times r}$, where the
$\mathbb Z$-entries of $\mathbf E$ are mutually independent, and those in its $i$th row are
subgaussian with parameter $O(\|\mathbf e^\pi_i\|)$, where $\mathbf e^\pi_i$ is the $i$th row of
$\mathbf E_\pi$.

**Proof.** Let $\mathbf C\leftarrow\mathbf C^\pi$ ⧇ $\mathbf C^\sigma$. It suffices to show that
for all $i,j$, its $(i,j)$th entry $c_{i,j}\in\mathcal C$ has error

$$
\mathbf e_{i,j}+\mathbf e^\sigma_{\pi^{-1}(i),j}\in\mathcal E=\mathbb Z^m,
$$

where all the $\mathbb Z$-entries of all the $\mathbf e_{i,j}\in\mathbb Z^m$ are mutually
independent and subgaussian with parameter $O(\|\mathbf e^\pi_i\|)$, and $\mathbf e^\sigma_{\ell,j}$
is the $(\ell,j)$th entry of $\mathbf E_\sigma$. This follows directly from Equation (4.1) and
Lemma 3.5: the error in each ciphertext $c^\pi_{i,\ell}\boxdot c^\sigma_{\ell,j}$ is
$p^\pi_{i,\ell}\cdot\mathbf e^\sigma_{\ell,j}$ plus a fresh vector whose entries are independent and
subgaussian with parameter $O(\|\mathbf e^\pi_{i,\ell}\|)$. Since $p^\pi_{i,\ell}=1$ for
$\ell=\pi^{-1}(i)$ and $0$ otherwise, the claim follows by Pythagorean additivity of independent
subgaussians.

<a id="pdf-cecd346d2e87-p012-b002"></a>
<!-- pdf-source: page=12; block=2; confidence=0.95 -->

**Section 4.2, chains of compositions; Corollary 4.2 (printed p. 11).** Similarly to a
multiplication chain of GSW ciphertexts, we can perform a
(right-associative) chain of compositions while incurring only small error growth. For
convenience of analysis, we always include the fixed zero-error ciphertext
$\mathbf J\in\mathcal C^{r\times r}$ (which encrypts the identity permutation) as the rightmost
ciphertext in the chain. The following corollary follows directly from Lemma 4.1 in the same way
that Corollary 3.6 follows from Lemma 3.5.

**Corollary 4.2.** Suppose that $\mathbf C_i\in\mathcal C^{r\times r}$ for $i\in[k]$ are
respectively designed to encrypt permutation matrices $\mathbf P_i\in\{0,1\}^{r\times r}$ and
have error matrices $\mathbf E_i\in\mathcal E^{r\times r}$. Then for any fixed values of these
variables,

$$
\mathbf C\leftarrow\mathop{\text{⧇}}_{i\in[k]}\mathbf C_i\ \text{⧇}\ \mathbf J
=\mathbf C_1\ \text{⧇}\ (\mathbf C_2\ \text{⧇}\ (\cdots(\mathbf C_k\ \text{⧇}\ \mathbf J)\cdots))
$$

has an error matrix whose $\mathbb Z$-entries are mutually independent, and those in its $i$th
row are subgaussian with parameter $O(\|\mathbf e_i\|)$, where
$\mathbf e_i^t\in\mathcal E^{kr}$ is the $i$th row of the concatenated error matrices
$[\mathbf E_1\mid\cdots\mid\mathbf E_k]$.

Finally, since the $\mathsf{Eq?}$ procedure simply performs a chain of (right-associative)
multiplications of GSW ciphertexts, Corollary 3.6 applies.

<a id="pdf-cecd346d2e87-p013-b001"></a>
<!-- pdf-source: page=13; block=1; confidence=0.95 -->

## 5 Bootstrapping

**Section 5 and Section 5.1, specification and usage (printed p. 12).** We now describe our
bootstrapping procedure.

We start by specifying the abstract preconditions and output guarantees of our bootstrapping
algorithm, and describe how to use it (with some additional pre- and post-processing) to
bootstrap known LWE-based encryption schemes.

The scheme to be bootstrapped must have binary ciphertexts in $\{0,1\}^d$ and secret keys in
$\mathbb Z_q^d$ for some dimension $d$ and modulus $q$ that should be made as small as possible
($q,d=\tilde O(\lambda)$ are possible), and a decryption function of the form
$\mathrm{Dec}_{\mathbf s}(\mathbf c)=f(\langle\mathbf s,\mathbf c\rangle)\in\{0,1\}$ for some
arbitrary function $f:\mathbb Z_q\to\{0,1\}$. We rely on an appropriate instantiation of the GSW
cryptosystem, as described in further detail in Section 5.2 below.

- $\mathsf{BootGen}(\mathbf s\in\mathbb Z_q^d,sk)$ takes as input a secret key vector
  $\mathbf s\in\mathbb Z_q^d$ from the scheme to be bootstrapped, and a secret key $sk$ for GSW. It
  outputs a bootstrapping key $bk$, which appropriately encrypts $\mathbf s$ under $sk$.
- $\mathsf{Bootstrap}(bk,\mathbf c\in\{0,1\}^d)$ takes as input the bootstrapping key $bk$ and a
  ciphertext vector $\mathbf c\in\{0,1\}^d$ (which decrypts under the secret key $\mathbf s$). It
  outputs a GSW ciphertext which decrypts (under $sk$) to the same bit as $\mathbf c$ does (under
  $\mathbf s$), but with less error.

<a id="pdf-cecd346d2e87-p014-b001"></a>
<!-- pdf-source: page=14; block=1; confidence=0.95 -->

**Section 5.1, pre- and post-processing (printed p. 13).** We can bootstrap all known LWE-based
bit-encryption schemes using the above algorithms as follows. In all LWE-based encryption
schemes, decryption can be expressed as a "rounded inner product"
$\lfloor\langle\mathbf s,\mathbf c\rangle\rceil_2$ for some appropriate rounding function
$\lfloor\cdot\rceil_2:\mathbb Z_q\to\{0,1\}$, as required. Note that a GSW ciphertext can
trivially be put in this form by just taking its penultimate column (see $\mathsf{GSW.Dec}$ in
Section 3.2). As for the other conditions we need (binary ciphertexts and small $d,q$), LWE
encryption schemes are not always presented in a way that fulfills them, but fortunately there
are standard transformations that do so, as we now describe. (See [BV11, BLP+13] for further
details.)

First, since we do not need to perform any further homomorphic operations on the ciphertext, we
can use dimension- and modulus-reduction [BV11] to get a ciphertext $\bar{\mathbf c}$ (over
$\mathbb Z_q$) of dimension $\tilde O(\lambda)$ and modulus $q=\tilde O(\lambda)$, while
preserving correct decryption. These steps can be implemented with $2^\lambda$ security under
conventional lattice assumptions.⁷ Then, we can obtain a binary ciphertext $\mathbf c$ using
"bit decomposition:" let $\mathbf G$ be as defined in Section 3.1, and for the ciphertext
$\bar{\mathbf c}$ over $\mathbb Z_q$ under secret key $\bar{\mathbf s}$, let $\mathbf c$ be a
$\{0,1\}$-vector such that $\mathbf G\mathbf c=\bar{\mathbf c}$, and let
$\mathbf s=\mathbf G^t\bar{\mathbf s}$ so that
$\langle\mathbf s,\mathbf c\rangle=\langle\bar{\mathbf s},\bar{\mathbf c}\rangle\in\mathbb Z_q$.
(The secret key $\mathbf s$ is therefore the one we need to provide to $\mathsf{BootGen}$.)

After bootstrapping, the output is a GSW ciphertext $\mathbf C$ encrypted under $sk$ (which is
just an integer vector). If desired, we can convert this ciphertext back to one for the original
LWE cryptosystem, simply by taking the penultimate column of $\mathbf C$. We can also key-switch
from $sk$ back to the original secret key $\mathbf s$. (As usual in bootstrapping, going "full
circle" in this way requires an appropriate circular security assumption.)

Footnote 7: To make the modulus quasi-linear, we need to use randomized (subgaussian) rounding in
the modulus-reduction step.

<a id="pdf-cecd346d2e87-p014-b002"></a>
<!-- pdf-source: page=14; block=2; confidence=0.95 -->

**Section 5.2, procedures: parameters and $\mathsf{BootGen}$ (printed p. 13).** Our algorithms
rely on instantiations of GSW and HEPerm with parameters $n,Q,\chi$. Importantly, the ciphertext
modulus $Q$ is not the modulus $q$ of the scheme we are bootstrapping, but rather some $Q\gg q$
that is sufficiently larger than the error in Bootstrap's output ciphertext. Let $\mathcal C$
denote the GSW ciphertext space.

Our procedures need $q$ to be of the form $q=\prod_{i\in[t]}r_i$ where the $r_i$ are small and
powers of distinct primes (and hence pairwise coprime). Specifically, using Lemma 2.2 we can
choose $q=\tilde O(\lambda)$ to be large enough by letting it be the product of all maximal
prime-powers $r_i$ that are bounded by $O(\log\lambda)$, of which there are
$t=O(\log\lambda/\log\log\lambda)$. Let $\phi$ be the group embedding of
$(\mathbb Z_q,+)\cong(\mathbb Z_{r_1}\times\cdots\times\mathbb Z_{r_t},+)$ into
$S=S_{r_1}\times\cdots\times S_{r_t}$ described in Section 2.2, and let $\phi_i$ denote the $i$th
component of this embedding, i.e., the one from $\mathbb Z_q$ into $S_{r_i}$.

- $\mathsf{BootGen}(\mathbf s\in\mathbb Z_q^d,sk)$: given secret key $\mathbf s\in\mathbb Z_q^d$
  for the scheme to be bootstrapped and a secret key $sk$ for HEPerm, embed each coordinate
  $s_j\in\mathbb Z_q$ of $\mathbf s$ as $\phi(s_j)\in S$ and encrypt the components under HEPerm.
  That is, generate and output the bootstrapping key

  $$
  bk=\{\mathbf C_{i,j}\leftarrow\mathsf{HEPerm.Enc}(sk,\phi_i(s_j)):i\in[t],j\in[d]\}.
  $$

  Recalling that we are working with embeddings of $\mathbb Z_{r_i}$, each
  $\mathbf C_{i,j}\in\mathcal C^{r_i}$ can be represented as a tuple of $r_i$ GSW ciphertexts
  encrypting an indicator vector (see Section 4.3). Because $t,r_i=O(\log\lambda)$ and
  $d=\tilde O(\lambda)$, the bootstrapping key consists of $\tilde O(\lambda)$ GSW ciphertexts.

<a id="pdf-cecd346d2e87-p014-b003"></a>
<!-- pdf-source: page=14; block=3; confidence=0.95 -->

**Section 5.2, $\mathsf{Bootstrap}$: Inner Product and Round, Equations (5.1)–(5.2) (printed
pp. 13–14).** $\mathsf{Bootstrap}(bk,\mathbf c\in\{0,1\}^d)$: given a binary ciphertext
$\mathbf c\in\{0,1\}^d$, do the following:

**Inner Product:** Homomorphically compute an encryption of

$$
v=\langle\mathbf s,\mathbf c\rangle=\sum_{j\,:\,c_j=1}s_j\in\mathbb Z_q
$$

using the encryptions of the $s_j\in\mathbb Z_q$ as embedded into the permutation group $S$, via
a chain of compositions. Formally, for each $i\in[t]$ compute (recalling that ⧇ is right
associative, and $\mathbf J$ is the fixed HEPerm encryption of the identity permutation)

$$
\mathbf C_i\leftarrow\mathop{\text{⧇}}_{j\text{ s.t. }c_j=1}\mathbf C_{i,j}\ \text{⧇}\ \mathbf J.\tag{5.1}
$$

Again, because we are working with embeddings of $\mathbb Z_{r_i}$, each
$\mathbf C_i\in\mathcal C^{r_i}$.

**Round:** Homomorphically map $v\in\mathbb Z_q$ to $f(v)\in\mathbb Z_2=\{0,1\}$: for each
$x\in\mathbb Z_q$ such that $f(x)=1$, homomorphically test whether $v\stackrel?=x$ by
homomorphically multiplying the GSW ciphertexts resulting from all the equality tests
$v\stackrel?=x\pmod{r_i}$. Then homomorphically sum the results of all the $v\stackrel?=x$ tests.

Formally, compute and output the GSW ciphertext (recalling that $\boxdot$ is right associative,
and $\mathbf G$ is the fixed GSW encryption of $1$)

$$
\mathbf C\leftarrow\mathop{\boxplus}_{x\in\mathbb Z_q\text{ s.t. }f(x)=1}
\Bigl(\mathop{\boxdot}_{i\in[t]}\mathsf{Eq?}(\mathbf C_i,\phi_i(x))\boxdot\mathbf G\Bigr).\tag{5.2}
$$

Note that since we are working with embeddings of $\mathbb Z_{r_i}$, each
$\mathsf{Eq?}(\mathbf C_i,\phi_i(x))$ is just some GSW ciphertext component of
$\mathbf C_i\in\mathcal C^{r_i}$ (see Section 4.3).

Because $t,r_i=O(\log\lambda)$ and $d=\tilde O(\lambda)$ and by Equations (5.1) and (5.2),
Bootstrap performs $\tilde O(\lambda)$ homomorphic multiplications and additions on GSW
ciphertexts.

<a id="pdf-cecd346d2e87-p015-b001"></a>
<!-- pdf-source: page=15; block=1; confidence=0.95 -->

**Theorem 5.1.** The above bootstrapping scheme can be instantiated to be correct (with
overwhelming probability) and secure assuming that the decisional Shortest Vector Problem
(GapSVP) and Shortest Independent Vectors Problem (SIVP) are (quantumly) hard to approximate in
the worst case to within $\tilde O(n^2\lambda)$ factors on $n$-dimensional lattices.

Because all known (quantum) algorithms for $\mathrm{poly}(n)$-factor approximations to GapSVP
and SIVP on $n$-dimensional lattices take $2^{\Omega(n)}$ time, for $2^\lambda$ hardness we can
take $n=\Theta(\lambda)$, yielding a final approximation factor of $\tilde O(n^3)$. This comes
quite close to the $O(n^{3/2+\epsilon})$ factors obtained in [BV14], but without any expensive
"dimension leveraging:" we use GSW ciphertexts of dimension only $n=O(\lambda)$, rather than
some large polynomial in $\lambda$. Alternatively, at the cost of a larger dimension
$n=\lambda^{1/\epsilon}$, but without using the successive dimension-reduction procedure from
[BV14], we can obtain factors as small as $\tilde O(n^{2+\epsilon})$ for any constant
$\epsilon>0$.

The remainder of this subsection is devoted to proving the above theorem.

<a id="pdf-cecd346d2e87-p015-b002"></a>
<!-- pdf-source: page=15; block=2; confidence=0.95 -->

**Section 5.3, security (printed p. 14).** If the HEPerm key $sk$ is generated independently of
$\mathbf s$, then IND-CPA security of the bootstrapping key follows immediately from the security
of HEPerm, hence from LWE with parameters $n-1,Q,\chi$, and finally from worst-case lattice
problems. (We instantiate these parameters below to obtain the claimed approximation factors.) As
usual, if the keys are not independent, then we need to make an appropriate circular security
assumption. (To date, such an assumption is the only known way to obtain unbounded FHE.)

<a id="pdf-cecd346d2e87-p016-b001"></a>
<!-- pdf-source: page=16; block=1; confidence=0.95 -->

**Lemma 5.2 (Correctness).** For $bk\leftarrow\mathsf{BootGen}(\mathbf s,sk)$, the GSW ciphertext
$\mathbf C\leftarrow\mathsf{Bootstrap}(bk,\mathbf c)$ is designed to encrypt
$\mathrm{Dec}_{\mathbf s}(\mathbf c)=f(\langle\mathbf s,\mathbf c\rangle)\in\{0,1\}$.

**Proof.** First, by construction the HEPerm ciphertext $\mathbf C_{i,j}$ is designed to encrypt
$\phi_i(s_j)$. Therefore, because $\phi_i:\mathbb Z_q\to S_{r_i}$ is a group homomorphism, the
ciphertext $\mathbf C_i$ as defined in Equation (5.1) is designed to encrypt
$\phi_i(\sum_{j:c_j=1}s_j)=\phi_i(\langle\mathbf s,\mathbf c\rangle)=\phi_i(v)$. By correctness
of Eq? and the isomorphism $\mathbb Z_q\cong\mathbb Z_{r_1}\times\cdots\times\mathbb Z_{r_t}$
given by Chinese Remainder Theorem, the homomorphic product
$\mathop{\boxdot}_{i\in[t]}\mathsf{Eq?}(\mathbf C_i,\phi_i(x))\boxdot\mathbf G$ is designed to
encrypt $1$ if and only if $v=x$. Finally, because the homomorphic sum is taken over every
$x\in\mathbb Z_q$ such that $f(x)=1$, it is designed to encrypt $1$ if and only if $f(v)=1$.

## ===== blueprint/src/references/brakerski-vaikuntanathan-2014-fhe.md =====

<!-- generated-by: maintainer transcription of the passages used (DW-7) -->
<!-- source-pdf-sha256: eab2d1667a8e8a07155968141c72d0ff0be15b1185dd0fd34f291fb41fb812ca -->
<!-- validation-status: scoped transcription for DW-7; awaiting Codex source review -->

# Lattice-Based FHE as Secure as PKE

Zvika Brakerski and Vinod Vaikuntanathan. *ITCS 2014*, pp. 1–12; IACR ePrint 2013/541, PDF
created 28 August 2013 (21 pages; tag `BV14`).

**Scope.** Only the passages that the GSW Lean (phase 5) and the phase-6 plan use are
transcribed (DW-7; GSW ruling Q14): the leveled-FHE footnote and Theorem 1.1 of §1, the
decomposition routines of §2.3, §2.5 (homomorphic encryption, Definitions 2.12–2.13,
Theorem 2.14), all of §3 (the scheme `NCCrypt`, Definition 3.1, Lemmas 3.2–3.3, Proposition 3.4,
Claims 3.4.1–3.4.2, width-5 permutation branching programs, Equations (4)–(6), Theorem 3.5,
Lemma 3.6, Theorem 3.7), the statement of Lemma 4.4, and Corollary 4.5 with the key-size remark
of §4.2. §2.1, §2.2, §2.4 (the randomization lemmas 2.9–2.11) and §4.1 are not transcribed; the
phase-5 Lean replaces their probabilistic bounds by worst-case ones. The PDF is not committed.
Physical and printed pages coincide. The scoped raw extraction is
`brakerski-vaikuntanathan-2014-fhe.raw.md`. Mathematics is set in LaTeX; the paper's
sans-serif procedure names are written $\mathsf{NCCrypt.Keygen}$ etc. The wording is the
paper's. Notes marked *Transcription note* are not part of the source.

<a id="pdf-eab2d1667a8e-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.95 -->

**Section 1, footnote 1: leveled FHE and circular security (p. 1).** Here, and in the rest of the
introduction, when we say FHE, we mean a leveled FHE scheme that can evaluate circuits of any
a-priori bounded polynomial depth. The only known way to achieve non-leveled FHE schemes is to
make a circular security assumption, in addition.

<a id="pdf-eab2d1667a8e-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.90 -->

**Theorem 1.1.** For every $\epsilon>0$, there exists a leveled fully homomorphic encryption
scheme based on the $\mathsf{DLWE}_{n,q,\alpha}$ assumption ($n$-dimensional decisional LWE
modulo $q$, with discrete Gaussian noise with parameter $\alpha$), where
$\alpha=1/\tilde O(n^{\epsilon}\cdot\sqrt{n\log(q)})$.

Thus, the scheme is secure based on either the quantum worst-case hardness of
$\mathsf{GapSVP}_{\tilde O(n^{1.5+\epsilon})}$, or the classical worst-case hardness of
$\mathsf{GapSVP}_{\tilde O(n^{2+\epsilon})}$.

*Transcription note.* The extraction drops the $\epsilon$ glyphs and scatters the tildes; the
statement is read from the layout. It is context only (the phase-6 plan does not formalize
worst-case lattice factors).

<a id="pdf-eab2d1667a8e-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.90 -->

**Section 2.3, vector decomposition (pp. 5–6).** We show how to decompose vectors in a way that
makes their norm smaller, and yet preserves certain inner products. Our notation is generally
adopted from [BGV12].

*Vector Decomposition.* We often break vectors into their bit representations as defined below:

- $\mathsf{BitDecomp}_q(\mathbf x)$: For $\mathbf x\in\mathbb Z^n$, let $w_{i,j}\in\{0,1\}$ be
  such that $\mathbf x[i]=\sum_{j=0}^{\lceil\log q\rceil-1}2^j\cdot w_{i,j}\pmod q$. Output the
  vector
  $(w_{1,\lceil\log q\rceil-1},\dots,w_{1,0},\dots,w_{n,\lceil\log q\rceil-1},\dots,w_{n,0})\in\{0,1\}^{n\cdot\lceil\log q\rceil}$.
- $\mathsf{PowersOfTwo}_q(\mathbf y)$: For $\mathbf y\in\mathbb Z^n$, output
  $\bigl[(2^{\lceil\log q\rceil-1}\mathbf y[1],\dots,2\mathbf y[1],\mathbf y[1],\dots,2^{\lceil\log q\rceil-1}\cdot\mathbf y[n],\dots,2\mathbf y[n],\mathbf y[n])\bigr]_q\in\mathbb Z_q^{n\cdot\lceil\log q\rceil}$.

We will usually omit the subscript $q$ when it is clear from the context.

**Claim 2.7.** For all $q\in\mathbb N$ and $\mathbf x,\mathbf y\in\mathbb Z^n$, it holds that

$$
\langle\mathbf x,\mathbf y\rangle=\langle\mathsf{BitDecomp}_q(\mathbf x),\mathsf{PowersOfTwo}_q(\mathbf y)\rangle\pmod q.
$$

Additionally, we define the procedure Flatten following [GSW13], along with the procedure
Combine. Let
$\mathbf g=(2^{\lceil\log(q)\rceil-1},2^{\lceil\log(q)\rceil-2},\dots,4,2,1)\in\mathbb Z^{\lceil\log q\rceil}$
and let $\mathbf G:=\mathbf g\otimes\mathbf I_n\in\mathbb Z^{n\times(n\cdot\lceil\log q\rceil)}$
denote the tensor product of $\mathbf g$ with the $n$-by-$n$ identity matrix $\mathbf I_n$.

- $\mathsf{Combine}_q(\mathbf z)$: For $\mathbf z\in\mathbb Z^{n\cdot\lceil\log q\rceil}$, output
  $[\mathbf G\cdot\mathbf z]_q\in\mathbb Z_q^n$.
- $\mathsf{Flatten}_q(\mathbf z)$: For $\mathbf z\in\mathbb Z^{n\cdot\lceil\log q\rceil}$, output
  $\mathsf{BitDecomp}_q(\mathsf{Combine}(\mathbf z))\in\{0,1\}^{n\cdot\lceil\log q\rceil}$.

**Claim 2.8.** For all $q\in\mathbb N$, and $\mathbf x,\mathbf z\in\mathbb Z^{n\cdot\lceil\log q\rceil}$,
it holds that

$$
\langle\mathsf{PowersOfTwo}(\mathbf x),\mathbf z\rangle=\langle\mathsf{PowersOfTwo}(\mathbf x),\mathsf{Flatten}(\mathbf z)\rangle\pmod q.
$$

*Transcription note.* BV14 orders bits most significant first, unlike GSW13. In Claim 2.8 the
printed domain of $\mathbf x$ is as transcribed (the claim is used with
$\mathbf x\in\mathbb Z^{n}$). Confidence is lowered because sub- and superscripts are flattened
in the extraction.

<a id="pdf-eab2d1667a8e-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.95 -->

**Section 2.5, homomorphic encryption and bootstrapping (pp. 7–8).** We now define homomorphic
encryption and introduce Gentry's bootstrapping theorem. Our definitions are mostly taken from
[BV11, BGV12].

A homomorphic (public-key) encryption scheme
$\mathsf{HE}=(\mathsf{HE.Keygen},\mathsf{HE.Enc},\mathsf{HE.Dec},\mathsf{HE.Eval})$ is a
quadruple of ppt algorithms as follows ($\kappa$ is the security parameter):

- **Key generation** $(pk,evk,sk)\leftarrow\mathsf{HE.Keygen}(1^\kappa)$: Outputs a public
  encryption key $pk$, a public evaluation key $evk$ and a secret decryption key $sk$.²
- **Encryption** $c\leftarrow\mathsf{HE.Enc}_{pk}(\mu)$: Using the public key $pk$, encrypts a
  single bit message $\mu\in\{0,1\}$ into a ciphertext $c$.
- **Decryption** $\mu\leftarrow\mathsf{HE.Dec}_{sk}(c)$: Using the secret key $sk$, decrypts a
  ciphertext $c$ to recover the message $\mu\in\{0,1\}$.
- **Homomorphic evaluation** $c_f\leftarrow\mathsf{HE.Eval}_{evk}(f,c_1,\dots,c_\ell)$: Using the
  evaluation key $evk$, applies a function $f:\{0,1\}^\ell\to\{0,1\}$ to $c_1,\dots,c_\ell$, and
  outputs a ciphertext $c_f$.

Footnote 2: We adopt the terminology of [BV11] that treats the evaluation key as a separate
entity from the public key.

A homomorphic encryption scheme is said to be secure if it is semantically secure (note that the
adversary is given both $pk$ and $evk$).

Homomorphism w.r.t depth-bounded circuits and full homomorphism are defined next:

<a id="pdf-eab2d1667a8e-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.95 -->

**Definition 2.12 (compactness and full homomorphism).** A homomorphic encryption scheme is
*compact* if its decryption circuit is independent of the evaluated function. A compact scheme is
(pure) *fully homomorphic* if it can evaluate any efficiently computable function. The scheme is
*leveled fully homomorphic* if it takes $1^L$ as additional input in key generation, and can only
evaluate depth $L$ Boolean circuits.

Gentry's bootstrapping theorem shows how to go from limited amount of homomorphism to full
homomorphism. This method has to do with the augmented decryption circuit.

<a id="pdf-eab2d1667a8e-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=0.95 -->

**Definition 2.13.** Consider a homomorphic encryption scheme $\mathsf{HE}$. Let $(sk,pk,evk)$ be
properly generated keys and let $\mathcal C$ be the set of properly decryptable ciphertexts. Then
the set of *augmented decryption functions*, $\{f_{c_1,c_2}\}_{c_1,c_2\in\mathcal C}$ is defined
by $f_{c_1,c_2}(x)=\overline{\mathsf{HE.Dec}_x(c_1)\wedge\mathsf{HE.Dec}_x(c_2)}$. Namely, the function
that uses its input as secret key, decrypts $c_1,c_2$ and returns the NAND of the results.

*Transcription note.* The bar over the conjunction (NAND) is visible in the page image
(150 dpi), not in the extraction, which shows a plain $\wedge$.

<a id="pdf-eab2d1667a8e-p008-b003"></a>
<!-- pdf-source: page=8; block=3; confidence=0.95 -->

**Theorem 2.14 (bootstrapping [Gen09b, Gen09a]).** The bootstrapping theorem is thus as
follows. A scheme that can homomorphically evaluate its family of augmented decryption circuits
can be transformed into a leveled fully homomorphic encryption scheme with the same decryption
circuit, ciphertext space and public key.

Furthermore, if the aforementioned scheme is also weak circular secure (remains secure even
against an adversary who gets encryptions of the bits of the secret key), then it can be made into
a pure fully homomorphic encryption scheme.

<a id="pdf-eab2d1667a8e-p008-b004"></a>
<!-- pdf-source: page=8; block=4; confidence=0.95 -->

## 3 Our FHE Scheme

**Section 3, opening, and Section 3.1, opening (p. 8).** In this section, we describe an FHE
scheme secure under a polynomial LWE assumption which, using known reductions [Reg05, Pei09],
translates to the worst-case hardness of solving various lattice problems to within polynomial
approximation factors. We start with the basic encryption scheme in Section 3.1, and describe
"proto-homomorphic" addition and multiplication subroutines in Section 3.2. Departing from the
"conventional wisdom" in FHE, our circuit evaluation procedure in Section 3.3 will not be a naive
combination of these proto-homomorphic operations, but rather a carefully designed procedure that
manages the noise growth effectively.

Finally, in Section 3.4, we put this all together to get our FHE scheme under the decisional LWE
assumption $\mathsf{DLWE}_{n,q,\alpha}$ with $\alpha=n^{-c}$ for some constant $c>0$. This
polynomial factor is rather large: thus, in Section 4, we apply a carefully designed variant of
the dimension-modulus reduction procedure of [BV11] to obtain our final FHE scheme that is secure
under the hardness of $\mathsf{DLWE}_{n,q,\alpha}$ with
$\alpha\le1/\tilde O_\kappa(n\cdot\sqrt{n\log(q)})$ which is weakest LWE hardness assumption that
underlies the (non-homomorphic) lattice-based PKE schemes [AD97, Reg04, Reg05, Pei09, BLP+13].

Our basic encryption scheme closely follows the Gentry-Sahai-Waters FHE scheme [GSW13]. We refer
the reader to Section 2.3 for the description of the vector decomposition routines PowersOfTwo,
BitDecomp and Flatten used in the scheme below.

<a id="pdf-eab2d1667a8e-p009-b001"></a>
<!-- pdf-source: page=9; block=1; confidence=0.95 -->

**Section 3.1, the scheme $\mathsf{NCCrypt}$ (p. 9).**

*System Parameters.* Let $n$ be the LWE dimension and $q$ be an LWE modulus. Define
$N:=(n+1)\cdot\lceil\log q\rceil$. Let $d$ denote the maximal homomorphism depth that is allowed
by the scheme. Let $\chi$ be an error distribution over $\mathbb Z$. Typically $\chi$ will be a
discrete Gaussian $D_{\mathbb Z,\alpha q}$ for
$\alpha=1/\tilde O_\kappa(\sqrt{n\log(q)}\cdot4^d)$. Recall that we identify $\mathbb Z_q$ with
the set $(-q/2,q/2]\cap\mathbb Z$.

- $\mathsf{NCCrypt.Keygen}(1^n,q,4^d)$: Sample a vector $\mathbf s\xleftarrow{\$}\mathbb Z_q^n$.
  Let $m\triangleq(n+1)\cdot(\log q+O(1))$. Sample $\mathbf A\xleftarrow{\$}\mathbb Z_q^{m\times n}$
  and $\mathbf e\xleftarrow{\$}\chi^m$. Compute $\mathbf b:=[\mathbf A\cdot\mathbf s+\mathbf e]_q$,
  and define

  $$
  \mathbf P:=[\mathbf b\,\|-\mathbf A]\in\mathbb Z_q^{m\times(n+1)}.
  $$

  Output $sk=\mathbf s$ and $pk=evk=\mathbf P$.

  We describe public-key as well as secret-key encryption algorithms. Looking ahead, we remark
  that a secret-key encryption of $\mu$ is somewhat less "noisy" than a public-key encryption of
  $\mu$.
- $\mathsf{NCCrypt.PubEnc}(pk,\mu)$: To encrypt a bit $\mu\in\{0,1\}$, using the public key
  $pk=\mathbf P$, we let $\mathbf R\xleftarrow{\$}\{0,1\}^{N\times m}$, and output the ciphertext

  $$
  \mathbf C=\mathsf{Flatten}\left(\mathsf{BitDecomp}(\mathbf R\cdot\mathbf P)+\mu\cdot\mathbf I\right)\in\{0,1\}^{N\times N}.
  $$
- $\mathsf{NCCrypt.SecEnc}(sk,\mu)$: A symmetric encryption of a bit $\mu\in\{0,1\}$, using the
  secret key $sk=\mathbf s$, is performed by sampling
  $\mathbf A\xleftarrow{\$}\mathbb Z_q^{N\times n}$ and $\mathbf e\xleftarrow{\$}\chi^N$,
  computing $\mathbf b:=[\mathbf A\cdot\mathbf s+\mathbf e]_q$, and defining

  $$
  \mathbf C=\mathsf{Flatten}\left(\mathsf{BitDecomp}\left([\mathbf b\,\|-\mathbf A]\right)+\mu\cdot\mathbf I\right)\in\{0,1\}^{N\times N}.
  $$
- $\mathsf{NCCrypt.Dec}(sk,\mathbf C)$: Let $\mathbf c$ be the second row of $\mathbf C$. We use
  standard Regev decryption on $\mathbf c$. Namely, we output $\mu^*=0$ if
  $\bigl|[\langle\mathbf c,\mathsf{PowersOfTwo}(1,\mathbf s)\rangle]_q\bigr|<q/8$, and $\mu^*=1$
  otherwise.

*Transcription note.* The absolute value in $\mathsf{NCCrypt.Dec}$ is visible in the page image
(115 dpi), not in the extraction.

<a id="pdf-eab2d1667a8e-p009-b002"></a>
<!-- pdf-source: page=9; block=2; confidence=0.95 -->

**Section 3.1, correctness; Definition 3.1 and Lemma 3.2 (p. 9).** In order to show correctness
of this scheme, we analyze the noise magnitude of ciphertexts produced by both the public-key and
secret-key encryption algorithms. As we will show shortly, for ciphertexts $\mathbf C$ produced by
either encryption algorithm, we have

$$
\mathbf C\cdot\mathsf{PowersOfTwo}(1,\mathbf s)=\mu\cdot\mathsf{PowersOfTwo}(1,\mathbf s)+\mathbf e\pmod q
$$

for a noise vector $\mathbf e$ of "small magnitude". This motivates our definition of the noise in
the ciphertext $\mathbf C$ with respect to a secret key vector $\mathbf s$ and a message $\mu$ as
follows.

**Definition 3.1.** For every $\mathbf C\in\{0,1\}^{N\times N}$, $\mathbf s\in\mathbb Z_q^n$ and
$\mu\in\mathbb Z$, we define

$$
\mathsf{noise}_{\mathbf s,\mu}(\mathbf C)\triangleq\bigl\|(\mathbf C-\mu\mathbf I)\cdot\mathsf{PowersOfTwo}(1,\mathbf s)\pmod q\bigr\|_\infty
$$

The significance of this definition is captured by the following claims. The first claim shows
that any ciphertext with small noise is decrypted correctly.

**Lemma 3.2.** For every $\mathbf C\in\{0,1\}^{N\times N}$, $\mathbf s\in\mathbb Z_q^n$ and
$\mu\in\mathbb Z$ such that $\mathsf{noise}_{\mathbf s,\mu}(\mathbf C)<q/8$,

$$
\mathsf{NCCrypt.Dec}(\mathbf s,\mathbf C)=\mu
$$

<a id="pdf-eab2d1667a8e-p010-b001"></a>
<!-- pdf-source: page=10; block=1; confidence=0.95 -->

**Proof of Lemma 3.2 (p. 10).** Since $\mathsf{noise}_{\mathbf s,\mu}(\mathbf C)<q/8$, we have

$$
\mathbf C\cdot\mathsf{PowersOfTwo}(1,\mathbf s)=\eta+\mu\cdot\mathsf{PowersOfTwo}(1,\mathbf s)\pmod q
$$

where $\|\eta\|_\infty<q/8$. Thus, for the second row of $\mathbf C$ it holds that

$$
\langle\mathbf c,\mathsf{PowersOfTwo}(1,\mathbf s)\rangle=\eta+2^{\lceil\log(q)\rceil-2}\cdot\mu\pmod q
$$

where $|\eta|<q/8$. Thus, when $\mu=0$,

$$
\bigl|[\langle\mathbf c,\mathsf{PowersOfTwo}(1,\mathbf s)\rangle]_q\bigr|=|\eta|<q/8
$$

When $\mu=1$,

$$
\bigl|[\langle\mathbf c,\mathsf{PowersOfTwo}(1,\mathbf s)\rangle]_q\bigr|\ge q/4-|\eta|\ge q/8
$$

since $q/4\le2^{\lceil\log(q)\rceil-2}<q/2$. This shows correctness of decryption for ciphertexts
with small noise.

*Transcription note.* The vertical bars around $[\cdot]_q$ in the two displays are visible in the
page image (130 dpi), not in the extraction.

<a id="pdf-eab2d1667a8e-p010-b002"></a>
<!-- pdf-source: page=10; block=2; confidence=0.90 -->

**Section 3.1, fresh noise; Lemma 3.3 and its proof (p. 10).** The next claim demonstrates
parameter settings for which the (public key and secret key) encryption algorithms produce
ciphertexts with small noise.

**Lemma 3.3.** Let $n$ be the LWE dimension, $q$ be the LWE modulus and $\chi=D_{\mathbb Z,\alpha q}$ be the discrete Gaussian
distribution. Then, for every $\mathbf s\in\mathbb Z_q^n$ and $\mu\in\{0,1\}$,

- for $\mathbf C_{pub}\leftarrow\mathsf{NCCrypt.PubEnc}(pk,\mu)$, we have
  $\mathsf{noise}_{\mathbf s,\mu}(\mathbf C_{pub})=\tilde O_\kappa(\alpha q\cdot\sqrt m)$.
- for $\mathbf C_{sec}\leftarrow\mathsf{NCCrypt.SecEnc}(sk,\mu)$, we have
  $\mathsf{noise}_{\mathbf s,\mu}(\mathbf C_{sec})=\tilde O_\kappa(\alpha q)$.

with all but negligible (in $\kappa$) probability over the coins of $\mathsf{NCCrypt.Keygen}$.

In particular, we have correctness of decryption for the public key encryption for
$\alpha<1/\tilde\Omega_\kappa(\sqrt m)$, and for the secret key encryption for
$\alpha<1/\tilde\Omega_\kappa(1)$.

**Proof of Lemma 3.3.** We first show the analysis for the public-key encryption.

$$
\begin{aligned}
\mathbf C_{pub}\cdot\mathsf{PowersOfTwo}(1,\mathbf s)
&=\mathsf{Flatten}\bigl(\mathsf{BitDecomp}(\mathbf R\cdot\mathbf P)+\mu\cdot\mathbf I\bigr)\cdot\mathsf{PowersOfTwo}(1,\mathbf s)\\
&=\bigl(\mathsf{BitDecomp}(\mathbf R\cdot\mathbf P)+\mu\cdot\mathbf I\bigr)\cdot\mathsf{PowersOfTwo}(1,\mathbf s)\\
&=\mathbf R\cdot\mathbf P\cdot(1,\mathbf s)^T+\mu\cdot\mathsf{PowersOfTwo}(1,\mathbf s)\\
&=\mathbf R\cdot\mathbf e+\mu\cdot\mathsf{PowersOfTwo}(1,\mathbf s)
\end{aligned}
$$

Thus, by Proposition 2.3,

$$
\mathsf{noise}(\mathbf C_{pub})=\|\mathbf R\cdot\mathbf e\|_\infty=\tilde O_\kappa(\sqrt m\cdot\alpha q)
$$

This is less than $q/8$ by the choice of $\alpha<1/\tilde\Omega_\kappa(\sqrt m)$.

The analysis for the secret key encryption follows analogously, except that

$$
\mathbf C_{sec}\cdot\mathsf{PowersOfTwo}(1,\mathbf s)=\mathbf e+\mu\cdot\mathsf{PowersOfTwo}(1,\mathbf s)
$$

Thus,

$$
\mathsf{noise}(\mathbf C_{sec})=\|\mathbf e\|_\infty=\tilde O_\kappa(\alpha q)
$$

which is less than $q/8$ by the choice of $\alpha<1/\tilde\Omega_\kappa(1)$.

*Transcription note.* The tildes and radicals are flattened in the extraction; confidence is
lowered for that reason.

<a id="pdf-eab2d1667a8e-p011-b001"></a>
<!-- pdf-source: page=11; block=1; confidence=0.95 -->

**Section 3.1, security and complexity of decryption; Proposition 3.4 (p. 11).**

*Security.* Semantic security of the scheme follows from the decisional LWE assumption
$\mathsf{DLWE}_{n,q,\alpha}$, similarly to Regev's encryption scheme (see [Reg05, BV11, GSW13]
for similar arguments).

*Complexity of Decryption.* Our decryption algorithm is essentially the same as the decryption
algorithm in Regev's encryption scheme, the complexity of which has been thoroughly studied in the
context of FHE. The following is an immediate corollary from [BV11, Lemma 4.1].

**Proposition 3.4.** There exists a constant $c_{\mathsf{dec}}$ such that the decryption circuit
of the scheme $\mathsf{NCCrypt}$, with parameters $n,q$, has depth at most
$c_{\mathsf{dec}}\cdot\log(n\log q)$.

*Transcription note.* In the 39-page full version of [BV11] used for this campaign
(`brakerski-vaikuntanathan-2011-fhe.md`) the decryption-depth lemma is numbered Lemma 4.5;
"[BV11, Lemma 4.1]" is BV14's reference.

<a id="pdf-eab2d1667a8e-p011-b002"></a>
<!-- pdf-source: page=11; block=2; confidence=0.95 -->

**Section 3.2, proto-homomorphic operations; addition and Claim 3.4.1 (p. 11).** We now describe
proto-homomorphic addition and multiplication algorithms which will be used in Section 3.3 for
homomorphic circuit evaluation. Departing from the "conventional wisdom" in FHE, our circuit
evaluation procedure will not be a naive combination of homomorphic addition and multiplication,
but a carefully designed procedure that manages the noise growth effectively. To further stress
the fact that we do not intend for these procedures to be used independently, we call them
proto-homomorphic operations.

*Proto-Homomorphic Addition.* This is a simple addition of the ciphertext matrices.

- $\mathsf{NCCrypt.ProtoAdd}(\mathbf C_1,\mathbf C_2)$: Output
  $\mathbf C_+:=\mathsf{Flatten}(\mathbf C_1+\mathbf C_2)$.

Jumping ahead, we note that in our use of $\mathsf{NCCrypt.ProtoAdd}$ in Section 3.3, both
$\mathbf C_1$ and $\mathbf C_2$ will be encryptions of bits, and at most one of them will be an
encryption of $1$. The following claim analyzes the noise growth in homomorphic addition.

**Claim 3.4.1 (Noise Growth in $\mathsf{NCCrypt.ProtoAdd}$.).** For every
$\mathbf s\in\mathbb Z_q^n$, $\mu_1,\mu_2\in\mathbb Z$ and
$\mathbf C_1,\mathbf C_2\in\{0,1\}^{N\times N}$, we have

$$
\mathsf{noise}_{\mathbf s,\mu_1+\mu_2}(\mathsf{NCCrypt.ProtoAdd}(\mathbf C_1,\mathbf C_2))
\le\mathsf{noise}_{\mathbf s,\mu_1}(\mathbf C_1)+\mathsf{noise}_{\mathbf s,\mu_2}(\mathbf C_2)
$$

**Proof.** Let $\mathbf C_+\leftarrow\mathsf{NCCrypt.ProtoAdd}(\mathbf C_1,\mathbf C_2)$. We note
that

$$
\begin{aligned}
\mathbf C_+\cdot\mathsf{PowersOfTwo}(1,\mathbf s)&=\mathsf{Flatten}(\mathbf C_1+\mathbf C_2)\cdot\mathsf{PowersOfTwo}(1,\mathbf s)\\
&=(\mathbf C_1+\mathbf C_2)\cdot\mathsf{PowersOfTwo}(1,\mathbf s)\\
&=\mathbf C_1\cdot\mathsf{PowersOfTwo}(1,\mathbf s)+\mathbf C_2\cdot\mathsf{PowersOfTwo}(1,\mathbf s)\\
&=(\mathbf e_1+\mathbf e_2)+(\mu_1+\mu_2)\cdot\mathbf I
\end{aligned}
$$

Thus, by the definition of $\mathsf{noise}_{\mathbf s,\mu_1+\mu_2}$, we have

$$
\mathsf{noise}_{\mathbf s,\mu_1+\mu_2}(\mathbf C_+)\le\mathsf{noise}_{\mathbf s,\mu_1}(\mathbf C_1)+\mathsf{noise}_{\mathbf s,\mu_2}(\mathbf C_2)
$$

*Transcription note.* The last line of the display ends in "$\cdot\,\mathbf I$" as printed (the
intended term is $(\mu_1+\mu_2)\cdot\mathsf{PowersOfTwo}(1,\mathbf s)$).

<a id="pdf-eab2d1667a8e-p012-b001"></a>
<!-- pdf-source: page=12; block=1; confidence=0.95 -->

**Section 3.2, multiplication; Claim 3.4.2 (p. 12).** *Homomorphic Multiplication.* This is
essentially a multiplication of the ciphertext matrices, except that we randomize the first
ciphertext.

- $\mathsf{NCCrypt.ProtoMult}(evk,\mathbf C_1,\mathbf C_2)$:
  - Randomize $\mathbf C_1\in\{0,1\}^{N\times N}$ into a matrix
    $\widetilde{\mathbf C}_1\in\{0,1\}^{N\times N}$ by replacing each row $\mathbf c$ in
    $\mathbf C_1$ by the row
    $\widetilde{\mathbf c}\leftarrow\mathsf{BitDecomp}(\mathsf{Rand}(pk,\mathsf{Combine}(\mathbf c)))$
    where $\mathsf{Rand}$ is the LWE randomization procedure from Section 2.4.
  - Output $\mathbf C_\times\leftarrow\mathsf{Flatten}\bigl(\widetilde{\mathbf C}_1\cdot\mathbf C_2\bigr)$.

Jumping ahead, we remark that when we use $\mathsf{NCCrypt.ProtoMult}$ in our homomorphic circuit
evaluation in Section 3.3, the first ciphertext will be an "evaluated ciphertext" (namely, a
result of previous homomorphic evaluations), whereas the second ciphertext will be a "fresh
ciphertext" (namely an output of the *secret key* encryption algorithm).

The first new idea in this work is that while the order of the arguments does not matter in
homomorphic addition, the homomorphic multiplication algorithm $\mathsf{NCCrypt.ProtoMult}$ is
inherently asymmetric, since it is essentially the (non-commutative) matrix multiplication
operation. This asymmetry turns out to be the key to achieving improved noise growth, as
Claim 3.4.2 below will demonstrate.

**Claim 3.4.2 (Noise Growth in $\mathsf{NCCrypt.ProtoMult}$.).** For every
$\mathbf s\in\mathbb Z_q^n$, $\mu_1,\mu_2\in\{0,1\}$ and $\mathbf C_1\in\{0,1\}^{N\times N}$ and
$\mathbf C_2\leftarrow\mathsf{NCCrypt.SecEnc}(sk,\mu_2)$, we have

$$
\mathsf{noise}_{\mathbf s,\mu_1\mu_2}(\mathsf{NCCrypt.ProtoMult}(\mathbf C_1,\mathbf C_2))
\le|\mu_2|\cdot\mathsf{noise}_{\mathbf s,\mu_1}(\mathbf C_1)+\tilde O_\kappa(\alpha q\cdot\sqrt{n\log q})
$$

with all but negligible probability over the randomness of $\mathsf{NCCrypt.Keygen}$,
$\mathsf{NCCrypt.SecEnc}$ and $\mathsf{NCCrypt.ProtoMult}$.

**Remark.** In words, Claim 3.4.2 says that if $\mu_2\in\{0,1\}$ (as will be the case in our
homomorphic circuit evaluation in Section 3.3), the noise in $\mathbf C_\times$ is at most the
noise in $\mathbf C_1$, plus a fixed additive term. What's more, if $\mu_2=0$, then the noise in
$\mathbf C_\times$ is independent of that in $\mathbf C_1$! *These two facts are the key new ideas
that enable our main result.*

<a id="pdf-eab2d1667a8e-p012-b002"></a>
<!-- pdf-source: page=12; block=2; confidence=0.95 -->

**Proof of Claim 3.4.2 (pp. 12–13).** Let
$\mathbf C_\times\leftarrow\mathsf{NCCrypt.ProtoMult}(evk,\mathbf C_1,\mathbf C_2)$. Note that

$$
\begin{aligned}
\mathbf C_\times\cdot\mathsf{PowersOfTwo}(1,\mathbf s)
&=\mathsf{Flatten}(\widetilde{\mathbf C}_1\cdot\mathbf C_2)\cdot\mathsf{PowersOfTwo}(1,\mathbf s)\\
&=\widetilde{\mathbf C}_1\cdot(\mathbf C_2\cdot\mathsf{PowersOfTwo}(1,\mathbf s))\\
&=\widetilde{\mathbf C}_1\cdot(\mathbf e_2+\mu_2\cdot\mathsf{PowersOfTwo}(1,\mathbf s))\\
&=\widetilde{\mathbf C}_1\cdot\mathbf e_2+\mu_2\cdot\widetilde{\mathbf C}_1\cdot\mathsf{PowersOfTwo}(1,\mathbf s)\\
&=\widetilde{\mathbf C}_1\cdot\mathbf e_2+\mu_2\cdot(\widetilde{\mathbf e}_1+\mu_1\cdot\mathsf{PowersOfTwo}(1,\mathbf s))\\
&=(\widetilde{\mathbf C}_1\cdot\mathbf e_2+\mu_2\cdot\widetilde{\mathbf e}_1)+\mu_1\mu_2\cdot\mathsf{PowersOfTwo}(1,\mathbf s)
\end{aligned}\tag{1}
$$

Since $\mathbf e_2\leftarrow D^N_{\mathbb Z,\alpha q}$ and each row of
$\widetilde{\mathbf C}_1\in\{0,1\}^{N\times N}$ is the result of $\mathsf{Rand}$, by Lemma 2.11,
we have

$$
\bigl\|\widetilde{\mathbf C}_1\cdot\mathbf e_2\bigr\|_\infty\le\tilde O_\kappa(\alpha q\cdot\sqrt{n\log q})\tag{2}
$$

with all but negligible probability. Also, by lemma 2.10, we have

$$
\|\widetilde{\mathbf e}_1\|_\infty\le\|\mathbf e_1\|_\infty+\tilde O_\kappa(\alpha q\cdot\sqrt{n\log q})\tag{3}
$$

with all but negligible probability.

Putting together Eq. (1),(2) and (3), we have

$$
\mathsf{noise}_{\mathbf s,\mu_1\mu_2}(\mathbf C_\times)
\le\bigl\|\widetilde{\mathbf C}_1\cdot\mathbf e_2\bigr\|_\infty+|\mu_2|\cdot\|\widetilde{\mathbf e}_1\|_\infty
\le|\mu_2|\cdot\mathsf{noise}_{\mathbf s,\mu_1}(\mathbf C_1)+\tilde O_\kappa(\alpha q\cdot\sqrt{n\log q})
$$

which finishes the proof.

<a id="pdf-eab2d1667a8e-p013-b001"></a>
<!-- pdf-source: page=13; block=1; confidence=0.95 -->

**Section 3.3, homomorphic evaluation of circuits: opening (p. 13).** We now describe how to
homomorphically evaluate a Boolean circuit $\Psi$ with two-input NAND gates that takes $\ell$
inputs, and has depth $d$. In particular, our scheme will be able to evaluate circuits of depth
$c\cdot\log n$ (for any constant $c$) under a polynomial LWE assumption, namely
$\mathsf{DLWE}_{n,q,\chi}$ where $\chi=D_{\mathbb Z,\alpha}$ and $\alpha=1/n^{\Theta(c)}$. Since
the depth of the decryption circuit is
$c_{\mathsf{dec}}\cdot\log(n\log(q))\le2c_{\mathsf{dec}}\cdot\log(n)$ (for some constant
$c_{\mathsf{dec}}>0$), the scheme is bootstrappable, and by the bootstrapping theorem
(Theorem 2.14), we get a leveled FHE scheme under the same assumption.

To evaluate a circuit, our scheme first turns it into a width-5 permutation branching program
[BDFP86, Bar89], a model of computation that we describe below.

<a id="pdf-eab2d1667a8e-p013-b002"></a>
<!-- pdf-source: page=13; block=2; confidence=0.95 -->

**Section 3.3, width-5 permutation branching programs (pp. 13–14).** A permutation branching
program $\Pi$ of length $L$ with input space $\{0,1\}^\ell$ is a sequence of $L$ tuples of the form
$\bigl(\mathsf{var}(t),\sigma_{t,0},\sigma_{t,1}\bigr)$ where

- $\mathsf{var}:[L]\to[\ell]$ is a function that associates the $t$-th tuple with an input bit
  $x_{\mathsf{var}(t)}$.
- $\sigma_{j,0}$ and $\sigma_{j,1}$ are permutations on 5 elements. We will think of $\sigma_{j,0}$
  and $\sigma_{j,1}$ as bijective functions from the set $\{1,2,3,4,5\}$ to itself.

The computation of the program $\Pi$ on input $\mathbf x=(x_1,\dots,x_\ell)$ proceeds as follows.
The state of the computation at any point in time $t$ is a number $\zeta_t\in\{1,2,3,4,5\}$.
Computation starts with the initial state $\zeta_0=1$. The state $\zeta_t$ is computed
recursively as

$$
\zeta_t=\sigma_{t,\mathsf{var}(t)}(\zeta_{t-1})
$$

Finally, after $L$ steps, our state is $\zeta_L$. The output of the computation is $1$ if
$\zeta_L=1$, and $0$ otherwise.

To manage the growth of noise in homomorphic evaluation, we need to work with bits rather than
numbers. Thus, we prefer to represent the state $\zeta_t\in\{1,2,3,4,5\}$ by a 0-1 vector
$\mathbf v_t$ which is the unit vector $\mathbf u_{\zeta_t}$ in 5 dimensions.

The computation then proceeds as follows. The idea is that $\mathbf v_t[i]=1$ if and only if
$\sigma_{t,\mathsf{var}(t)}(\zeta_{t-1})=i$. Turning this around, $\mathbf v_t[i]=1$ if and only
if either:

- $\mathbf v_{t-1}[\sigma_{t,0}^{-1}(i)]=1$ and $x_{\mathsf{var}(t)}=0$; or
- $\mathbf v_{t-1}[\sigma_{t,1}^{-1}(i)]=1$ and $x_{\mathsf{var}(t)}=1$.

The following formula captures this condition. For $t=1,\dots,L$, and $i\in\{1,2,3,4,5\}$, we
have:

$$
\begin{aligned}
\mathbf v_t[i]&:=\mathbf v_{t-1}[\sigma_{t,0}^{-1}(i)]\cdot(1-x_{\mathsf{var}(t)})+\mathbf v_{t-1}[\sigma_{t,1}^{-1}(i)]\cdot x_{\mathsf{var}(t)}\\
&=\mathbf v_{t-1}[\gamma_{t,i,0}]\cdot(1-x_{\mathsf{var}(t)})+\mathbf v_{t-1}[\gamma_{t,i,1}]\cdot x_{\mathsf{var}(t)}
\end{aligned}\tag{4}
$$

where $\gamma_{t,i,0}\triangleq\sigma_{t,0}^{-1}(i)$ and $\gamma_{t,i,1}\triangleq\sigma_{t,1}^{-1}(i)$
are constants that are publicly computable given the description of the branching program. It is
this form that we will work with in our homomorphic evaluation.

The important property that we will use is that circuits of depth $d$ can be simulated by
branching programs of depth $L=4^d$.

*Transcription note.* "$\zeta_t=\sigma_{t,\mathsf{var}(t)}(\zeta_{t-1})$" is as printed (checked
against the page image); the intended permutation is $\sigma_{t,x_{\mathsf{var}(t)}}$, selected by
the value of the input bit, as Equation (4) shows.

<a id="pdf-eab2d1667a8e-p014-b001"></a>
<!-- pdf-source: page=14; block=1; confidence=0.95 -->

**Theorem 3.5 (Barrington's Theorem [Bar89]).** Every Boolean NAND circuit $\Psi$ that acts on
$\ell$ inputs and has depth $d$ can be computed by a width-5 permutation branching program $\Pi$ of
length $4^d$. Given the description of the circuit $\Psi$, the description of the branching
program $\Pi$ can be computed in $\mathrm{poly}(\ell,4^d)$ time.

<a id="pdf-eab2d1667a8e-p014-b002"></a>
<!-- pdf-source: page=14; block=2; confidence=0.95 -->

**Section 3.3, homomorphic evaluation $\mathsf{NCCrypt.Eval}(\Psi,\mathbf C_1,\dots,\mathbf C_\ell)$,
Equations (5)–(6) (p. 14).** The homomorphic evaluation procedure will first convert the depth-$d$
circuit $\Psi$ into a width-5 permutation branching program $\Pi$ of length $L=4^d$.

- **[Initialization]** We will maintain the encrypted state of the computation of the branching
  program for every step $t$. We denote this by
  $\mathbf V_t=(\mathbf V_{t,1},\mathbf V_{t,2},\mathbf V_{t,3},\mathbf V_{t,4},\mathbf V_{t,5})$,
  where each $\mathbf V_t[i]\in\{0,1\}^{N\times N}$ will be an encryption of $\mathbf v_t[i]$.
  - We initialize the state as follows. Compute $\mathbf V_{0,i}:=\mathbf v_0[i]\cdot\mathbf I$.
    Note that $\mathbf V_{0,i}$ is in fact a valid encryption of the bit $\mathbf v_0[i]$ with zero
    noise.
  - We also compute encryptions of the complements of the input bits, for convenience. That is,
    set $\bar{\mathbf C}_k:=\mathbf I-\mathbf C_k$. Note that $\bar{\mathbf C}_k$ is an encryption
    of $\bar x_k=1-x_k$ with the same noise as $\mathbf C_k$.
- **[Evaluation]** The evaluation proceeds iteratively for $t=1,\dots,L$, where $L$ is the length
  of the branching program $\Pi$. Assuming that we have
  $\mathbf V_{t-1}:=(\mathbf V_{t-1,1},\mathbf V_{t-1,2},\dots,\mathbf V_{t-1,5})$, the encryption
  of the state of the branching program computation at time $t-1$, we compute
  $\mathbf V_t:=(\mathbf V_{t,1},\mathbf V_{t,2},\dots,\mathbf V_{t,5})$ by homomorphically
  evaluating Eq. (4) above.

  That is, for $i\in\{1,2,3,4,5\}$, we compute

  $$
  \begin{aligned}
  \mathbf V_{t,i}:=\mathsf{NCCrypt.ProtoAdd}\Bigl(&\mathsf{NCCrypt.ProtoMult}\bigl(\mathbf V_{t-1,\gamma_0},\bar{\mathbf C}_{\mathsf{var}(t)}\bigr),&&(5)\\
  &\mathsf{NCCrypt.ProtoMult}\bigl(\mathbf V_{t-1,\gamma_1},\mathbf C_{\mathsf{var}(t)}\bigr)\Bigr)&&(6)
  \end{aligned}
  $$
- **[Output]** Upon finishing the evaluation stage, we have
  $\mathbf V_L:=(\mathbf V_{L,1},\mathbf V_{L,2},\dots,\mathbf V_{L,5})$. Output $\mathbf V_{L,1}$
  as the result of the homomorphic evaluation.

We now show that the scheme correctly evaluates circuits.

*Transcription note.* In Equations (5)–(6) $\gamma_0,\gamma_1$ abbreviate
$\gamma_{t,i,0},\gamma_{t,i,1}$ of Equation (4).

<a id="pdf-eab2d1667a8e-p015-b001"></a>
<!-- pdf-source: page=15; block=1; confidence=0.95 -->

**Lemma 3.6 (Correctness of Homomorphic Evaluation).** Let $n$ be the LWE dimension, $q$ the LWE
modulus, $\Psi$ be any Boolean circuit of depth $d$, and

$$
\alpha\le1/\tilde\Theta_\kappa(4^d\cdot\sqrt{n\log q})
$$

For every $x_1,\dots,x_\ell\in\{0,1\}$, every Boolean circuit $\Psi$ of depth at most $d$, and
every secret key $sk$, letting $\mathbf C_k\leftarrow\mathsf{NCCrypt.SecEnc}(sk,x_k)$ be the
*secret key* encryptions of the inputs, and
$\mathbf C_\Psi\leftarrow\mathsf{NCCrypt.Eval}(evk,\Psi,\mathbf C_1,\dots,\mathbf C_k)$ be the
evaluated ciphertext, we have:

$$
\mathsf{NCCrypt.Dec}(sk,\mathbf C_\Psi)=\Psi(x_1,\dots,x_\ell)
$$

with overwhelming probability over the coin tosses of all the algorithms. $\mathsf{NCCrypt.Eval}$
runs in time $\mathrm{poly}(4^d,\ell,n,\log q)$.

Note that we stated the correctness of homomorphic evaluation on ciphertexts produced by the
secret-key encryption algorithm $\mathsf{NCCrypt.SecEnc}$. A similar lemma can be shown in the case
of public-key encryption, if $\alpha$ is smaller by a factor of $\sqrt{n\log q}$. However, in our
"optimal FHE" scheme in Section 4, we will only need to invoke this lemma with secret-key
encryption.

*Transcription note.* "$\mathbf C_1,\dots,\mathbf C_k$" in the evaluated ciphertext is as printed
($\mathbf C_1,\dots,\mathbf C_\ell$ is meant).

<a id="pdf-eab2d1667a8e-p015-b002"></a>
<!-- pdf-source: page=15; block=2; confidence=0.95 -->

**Proof of Lemma 3.6 (p. 15).** It is easy to see that each step of the homomorphic evaluation
algorithm, given by Eq. (5), simulates the execution of the branching program, given by Eq. (4).
It remains to bound the noise growth during $\mathsf{NCCrypt.Eval}$. We show this by induction.

In the sequel, we will abbreviate the noise function $\mathsf{noise}_{\mathbf s,\mu}(\mathbf C)$ to
$\mathsf{noise}(\mathbf C)$ since the secret key is fixed throughout the evaluation, and the message
$\mu$ is clear from the context.

Clearly, $\mathsf{noise}(\mathbf V_{0,i})=0$, since they $\mathbf V_{0,i}$ are just the messages,
with no noise. Assume, as the inductive hypothesis, that for all $i\in\{1,2,3,4,5\}$,

$$
\mathsf{noise}(\mathbf V_{t-1,i})=(t-1)\cdot\tilde O_\kappa(\alpha q\cdot\sqrt{n\log q})
$$

We will now bound $\mathsf{noise}(\mathbf V_{t,i})$ for all $i\in\{1,2,3,4,5\}$. Note that

$$
\begin{aligned}
\mathsf{noise}\bigl(\mathbf V_{t,i}\bigr)&\le\mathsf{noise}\Bigl(\mathsf{NCCrypt.ProtoMult}\bigl(\mathbf V_{t-1,\gamma_0},\bar{\mathbf C}_{\mathsf{var}(t)}\bigr)\Bigr)
+\mathsf{noise}\Bigl(\mathsf{NCCrypt.ProtoMult}\bigl(\mathbf V_{t-1,\gamma_1},\mathbf C_{\mathsf{var}(t)}\bigr)\Bigr)\\
&\le|1-x_{\mathsf{var}(t)}|\cdot\mathsf{noise}(\mathbf V_{t-1,\gamma_0})+|x_{\mathsf{var}(t)}|\cdot\mathsf{noise}(\mathbf V_{t-1,\gamma_1})+\tilde O_\kappa(\alpha q\cdot\sqrt{n\log q})
\end{aligned}
$$

where the second inequality holds by Claim 3.4.2 since all the ciphertexts encrypt bits,
$\mathbf C_{\mathsf{var}(t)}$ is a fresh secret-key encryption, and $\bar{\mathbf C}_{\mathsf{var}(t)}$
contains exactly the same noise as $\mathbf C_{\mathsf{var}(t)}$.

Since exactly one of $x_{\mathsf{var}(t)}$ and $1-x_{\mathsf{var}(t)}$ is non-zero, we have

$$
\begin{aligned}
\mathsf{noise}\bigl(\mathbf V_{t,i}\bigr)&\le\max(\mathsf{noise}(\mathbf V_{t-1,\gamma_0}),\mathsf{noise}(\mathbf V_{t-1,\gamma_1}))+\tilde O_\kappa(\alpha q\cdot\sqrt{n\log q})\\
&\le t\cdot\tilde O_\kappa(\alpha q\cdot\sqrt{n\log q})
\end{aligned}
$$

by the inductive hypothesis.

Thus, in particular,

$$
\mathsf{noise}(\mathbf V_\Psi)=\mathsf{noise}\bigl(\mathbf V_{L,1}\bigr)\le4^d\cdot\tilde O_\kappa(\alpha q\cdot\sqrt{n\log q})<q/8
$$

by our setting of the parameter $\alpha$.

*Transcription note.* The second inequality applies Claim 3.4.2 to the two ProtoMult calls, but
the claim has one additive term per call, so the two calls give two such terms; the printed bound
keeps one $\tilde O$ term, which absorbs the factor 2. In the phase-5 Lean's worst-case form
(fresh ciphertext on the left) the step costs an additive $2N\beta$.

<a id="pdf-eab2d1667a8e-p016-b001"></a>
<!-- pdf-source: page=16; block=1; confidence=0.90 -->

**Section 3.4, achieving fully homomorphic encryption; Theorem 3.7 (p. 16).** We know by
Lemma 3.4 that the depth of the decryption circuit of $\mathsf{NCCrypt}$ is
$c_{\mathsf{dec}}\cdot\log(n\log q)=c_{\mathsf{dec}}\log N$ for some constant
$c_{\mathsf{dec}}>0$. Setting the depth $d=c\log N$ for some constant $c>c_{\mathsf{dec}}$ in
Lemma 3.6 and $\alpha\le1/\tilde\Theta_\kappa(4^d\cdot\sqrt{n\log q})$ gives us a bootstrappable
encryption scheme. By the bootstrapping theorem (Theorem 2.14), this can be turned into a leveled
FHE scheme, without additional assumptions. We state this theorem below:

**Theorem 3.7.** Let $n$ be the LWE dimension, $q$ be the LWE modulus,
$N:=(n+1)\cdot\lceil\log q\rceil$, and let $c>c_{\mathsf{dec}}$ be a large enough constant (where
$c_{\mathsf{dec}}$ is the decryption depth constant from Proposition 3.4), and

$$
\alpha\le1/\tilde\Theta_\kappa\bigl((n\log q)^{2c+1/2}\bigr)
$$

Then, there is a leveled FHE scheme that is secure under the decisional LWE assumption
$\mathsf{DLWE}_{n,q,\alpha}$.

In the next section, we will use a variant of the dimension-modulus reduction of [BV11], the
effect of which will be to reduce the constant $c$ above to a very small $\epsilon\to0$, thus
achieving a value of $\alpha$ that matches the best known lattice-based PKE schemes.

*Transcription note.* "Lemma 3.4" in the first sentence is as printed (Proposition 3.4 is meant).
Confidence is lowered because the radicals and tildes are flattened in the extraction.

<a id="pdf-eab2d1667a8e-p019-b001"></a>
<!-- pdf-source: page=19; block=1; confidence=0.95 -->

**Lemma 4.4.** Let $\alpha(n)=1/\tilde O_\kappa(\sqrt{n\log(q)}\cdot n^{\epsilon})$, and let
$q(n)\ge\tilde O(\sqrt n/\alpha(n))$. Consider a set of keys generated by
$(sk,pk,evk)\leftarrow\mathsf{DimReduced.Keygen}(1^k)$, and recall that $sk=(\mathbf s_0,\mathbf s_L)$.
Let $K_i\leftarrow\mathsf{DimReduced.SecEnc}_{sk}(\mathsf{BitDecomp}(\mathbf s_0)[i])$. Namely,
$K_i$ is the symmetric encryption of the $i$th bit of $\mathbf s_0$.

Let $f$ be an augmented decryption circuit as per Definition 2.13. Namely, let
$\mathbf c,\mathbf c'\in\mathbb Z_p^k$ and $\mu,\mu'\in\{0,1\}$ be such that

$$
[\langle\mathbf c,\mathbf s_0\rangle]_p=\mu\cdot\tau p+e,
$$

where $|e|<p/8$, and similarly for $\mathbf c'$. The function $f$ is the function that on input
$x$, treats $x$ as a secret key and decrypts $\mathbf c,\mathbf c'$, and outputs the NAND of their
decryptions.

Let

$$
\mathbf c_0\leftarrow\mathsf{DimReduced.Eval}_{evk}(f,K_1,K_2,\dots),
$$

and note that this is syntactically well defined since $f$ can be represented as a Boolean circuit
of depth $c_{\mathsf{dec}}\cdot\log(k\log(q(k)))+1$.

Then with all but $\mathrm{negl}(\kappa)$ probability,

$$
[\langle\mathbf c_0,\mathbf s_0\rangle]_p=\mu^*\cdot\tau p+e_f,
$$

where $\mu^*=\overline{(\mu\wedge\mu')}$, $|e_f|<p/8$ are as above.

*Transcription note.* The statement is given for the shape of the bootstrapping step (the
evaluation key holds secret-key encryptions $K_i$ of the bits of the secret key; the augmented
decryption circuit has depth $c_{\mathsf{dec}}\cdot\log(\cdot)+1$). $\tau=2^{\lceil\log(q_L)\rceil-2}/q_L$
is defined just before the lemma (p. 18). The radicals and the bar over $(\mu\wedge\mu')$ were
checked against the page image (130 dpi).

<a id="pdf-eab2d1667a8e-p020-b001"></a>
<!-- pdf-source: page=20; block=1; confidence=0.90 -->

**Section 4.2, Corollary 4.5 and the key-size remark (p. 20).** Finally, we derive the worst-case
lattice approximation factor based on Corollary 2.6. We recall that a bootstrappable homomorphic
encryption scheme implies a leveled FHE scheme under the same assumptions, and a pure FHE scheme
with an additional circular security assumption.

**Corollary 4.5.** For all $\epsilon>0$, there exist:

- A bootstrappable homomorphic encryption scheme based on the worst-case quantum hardness of
  solving $\mathsf{GapSVP}_{\tilde O(n^{1.5+\epsilon})}$ and $\mathsf{SIVP}_{\tilde O(n^{1.5+\epsilon})}$.
- A bootstrappable homomorphic encryption scheme based on the worst-case classical hardness of
  solving $\mathsf{GapSVP}_{\tilde O(n^{2+\epsilon})}$.

The first (quantum) case is derived from Lemma 4.4 by setting $q(n)=\sqrt n/\alpha(n)=\mathrm{poly}(n)$,
and the second (classical) case is derived by setting $q(n)=2^{n/2}$.

*Improving Key and Ciphertext sizes.* The scheme $\mathsf{DimReduced}$ uses a ladder of LWE
instances, ranging from short $(k,p)$ to polynomially larger $(n,q)$. In the description above, the
public key of the scheme is derived from that of $\mathsf{NCCrypt}$, and therefore depends on $n$
and not on $k$. Likewise, the "input ciphertexts" (the ones before homomorphic evaluation) also
depend on $n$.

We note here that this can be fixed in such a way that only the $evk$ depends on $n$, and the rest
of the parameters are exactly the same as Regev's scheme with parameters $(k,p)$. This is done in a
standard way (used e.g. in [BV11]) as follows.

We will generate the public key as a standard Regev public key with parameters $(k,p)$, and in the
evaluation key we will encrypt the bits of the respective secret key using $\mathsf{NCCrypt}$. This
will allow to perform homomorphic operations by evaluating the augmented decryption circuit.
Namely, the ciphertexts visible to the user of the scheme will always be short, but in the process
of homomorphic evaluation, larger ciphertexts are used to accommodate the homomorphic operation,
and once it is done dimension-modulus reduction will be used to shrink the output ciphertext back
to the original size. Since this is standard practice, we omit the technical description.

## ===== blueprint/src/references/peikert2016-lattice-survey.md =====

<!-- generated-by: Codex source review of approved excerpts -->
<!-- source-pdf-sha256: 1a9802b66031a2b863fd498a5de4a71cdb1bd46ac1d47dc1f4a67ae341357488 -->
<!-- validation-status: scoped excerpts for PRs #236 and #237; DW-7 extension (Sections 5.4.3, 6.1.2-6.1.3) awaiting Codex source review -->

# A Decade of Lattice Cryptography

Chris Peikert, author version dated 17 February 2016.

The approved coverage is Definitions 4.1.1, 4.2.1 and 4.2.3, with the
introductory sentence specifying the LWE error law. The anchors refer to
pages 20, 21 and 24 of the original PDF. The added SIS passages cover
the exclusion of trivial modulus multiples and the binary collision argument. The raw extraction retains the
complete document. Footnotes and intervening material are omitted here.

**DW-7 extension (2026-11-16).** The blocks on PDF pages 52–53 and 68–70 were added by the
maintainer for the GSW campaign (GSW ruling Q14; deferred item DW-7). They transcribe, from the
committed raw extraction, the passages the GSW Lean and the phase-6 plan cite: the "Gadgets"
part of §5.4.3 (the vector $\mathbf g$, $\mathbf G=\mathbf I_n\otimes\mathbf g^t$,
Equation (5.4.1) and $\mathbf G\cdot\mathbf G^{-1}(\mathbf u)=\mathbf u$), §6.1.2
(bootstrapping and circular security) and §6.1.3 (Equations (6.1.4)–(6.1.7), decryption, NAND,
bootstrapping by right-associative chains and Barrington's theorem). Unlike the summaries above,
these blocks are transcriptions in the paper's wording, with mathematics in LaTeX; printed page
numbers are two less than the PDF page. The rest of §5.4.3 (trapdoors, Definition 5.4.4 onward)
and of §6.1.3 (fully homomorphic signatures) is not used and is not transcribed. Notes marked
*Transcription note* are not part of the source.

<a id="pdf-1a9802b66031-p020-b001"></a>
<!-- pdf-source: page=20; block=1; confidence=0.98 -->

**Definition 4.1.1 (Short Integer Solution ($\mathrm{SIS}_{n,q,\beta,m}$)).** Given $m$ uniformly random vectors $\mathbf a_i\in\mathbb Z_q^n$, forming
the columns of a matrix $\mathbf A\in\mathbb Z_q^{n\times m}$, find a nonzero integer vector $\mathbf z\in\mathbb Z^m$ of norm $\|\mathbf z\|\le\beta$ such
that

$$
f_{\mathbf A}(\mathbf z):=\mathbf A\mathbf z=\sum_i\mathbf a_i\cdot z_i=\mathbf0\in\mathbb Z_q^n.\tag{4.1.1}
$$

<a id="pdf-1a9802b66031-p020-b002"></a>
<!-- pdf-source: page=20; block=2; confidence=0.98 -->

**Observation after Equation (4.1.1).**

Similarly, we
  must take $\beta<q$ because otherwise $\mathbf z=(q,0,\ldots,0)\in\mathbb Z^m$ would always be a legitimate (but trivial)
  solution.

<a id="pdf-1a9802b66031-p021-b001"></a>
<!-- pdf-source: page=21; block=1; confidence=0.98 -->

* Any solution for a matrix $\mathbf A$ can trivially be converted to one for any extension $[\mathbf A\mid\mathbf A']$, simply by
  appending the solution vector with zeros (which leaves the norm of the solution unchanged). In other
  words, we can ignore columns $\mathbf a_i$ as desired, so the SIS problem can only become easier as $m$ increases.
  Similarly, it can only become harder as $n$ increases.

* The norm bound $\beta$ and the number $m$ of vectors $\mathbf a_i$ must be large enough that a solution is guaranteed
  to exist. This is the case whenever $\beta\ge\sqrt{\bar m}$ and $m\ge\bar m$, where $\bar m$ is the smallest integer greater than
  $n\log q$, by a pigeonhole argument: first, by the previous observation we can assume without loss of
  generality that $m=\bar m$. Then because there are more than $q^n$ vectors $\mathbf x\in\{0,1\}^m$, there must be two
  distinct $\mathbf x,\mathbf x'$ such that $\mathbf A\mathbf x=\mathbf A\mathbf x'\in\mathbb Z_q^n$, so their difference $\mathbf z=\mathbf x-\mathbf x'\in\{0,\pm1\}^m$ is a solution of
  norm at most $\beta$.

* The above pigeonhole argument in fact shows more: the induced function family $\{f_{\mathbf A}:\{0,1\}^m\to\mathbb Z_q^n\}$
  defined in Equation (4.1.1) is *collision resistant*, assuming the hardness of the corresponding SIS
  problem. This is because a collision $\mathbf x,\mathbf x'\in\{0,1\}^m$ for $f_{\mathbf A}$ immediately yields an SIS solution for $\mathbf A$.
  (Of course the domain $\{0,1\}^m$ is somewhat arbitrary here, and can be replaced by essentially any other
  large enough set of sufficiently short integer vectors.)

<a id="pdf-1a9802b66031-p024-b001"></a>
<!-- pdf-source: page=24; block=1; confidence=0.98 -->

LWE is parameterized by positive integers $n$ and $q$, and an error distribution $\chi$ over $\mathbb Z$.

**Definition 4.2.1 (LWE distribution).** For a vector $\mathbf s\in\mathbb Z_q^n$ called the *secret*, the LWE distribution $A_{\mathbf s,\chi}$
over $\mathbb Z_q^n\times\mathbb Z_q$ is sampled by choosing $\mathbf a\in\mathbb Z_q^n$ uniformly at random, choosing $e\leftarrow\chi$, and outputting
$(\mathbf a,b=\langle\mathbf s,\mathbf a\rangle+e\bmod q)$.

*Definition 4.2.2 omitted.*

**Definition 4.2.3 (Decision-$\mathrm{LWE}_{n,q,\chi,m}$).** Given $m$ independent samples $(\mathbf a_i,b_i)\in\mathbb Z_q^n\times\mathbb Z_q$ where every
sample is distributed according to either: (1) $A_{\mathbf s,\chi}$ for a uniformly random $\mathbf s\in\mathbb Z_q^n$ (fixed for all samples), or
(2) the uniform distribution, distinguish which is the case (with non-negligible advantage).

<a id="pdf-1a9802b66031-p036-b001"></a>
<!-- pdf-source: page=36; block=1; confidence=1.00 -->

**Section 5.1, SIS hashing.** The opening paragraph recalls that the
binary matrix map of Equation (4.1.1) is collision resistant under the
hardness of the corresponding SIS problem. A collision yields the short
nonzero difference described in the earlier section.

<a id="pdf-1a9802b66031-p037-b001"></a>
<!-- pdf-source: page=37; block=1; confidence=1.00 -->

**Section 5.2.1, Regev public-key encryption.** The public key collects
LWE samples under a uniform common secret as columns of an augmented
matrix. Equation (5.2.1) gives the augmented matrix and Equation (5.2.2)
cancels the secret product to expose the errors. Equation (5.2.3) forms
a binary subset sum and adds the message's half-modulus codepoint to its
last coordinate. Decryption cancels the secret contribution and compares
the residual with the two codepoints modulo the modulus.

<a id="pdf-1a9802b66031-p038-b001"></a>
<!-- pdf-source: page=38; block=1; confidence=1.00 -->

**Section 5.2.1, correctness.** The accumulated integer error is the
inner product of the key error vector and the binary subset. The source
uses a quarter-modulus separation and discusses choosing the noise law
and modulus to make decryption correct with overwhelming probability.

<a id="pdf-1a9802b66031-p038-b002"></a>
<!-- pdf-source: page=38; block=2; confidence=1.00 -->

**Section 5.2.1, first security hybrid.** Compare the fixed-bit view
of the public key and ciphertext with the experiment that uses a uniform
public key. A decision-LWE test forms its challenge matrix, encrypts the
fixed bit, and runs the view distinguisher. The simulation is exact for
both challenge laws.

<a id="pdf-1a9802b66031-p038-b003"></a>
<!-- pdf-source: page=38; block=3; confidence=1.00 -->

**Section 5.2.1, second security hybrid.** For a uniform augmented
key matrix and an independent uniform binary subset, the leftover hash
lemma makes the seed-published matrix product close to a uniform independent
ciphertext. Adding a fixed message vector preserves that ideal uniform law.
This hybrid and the first hybrid compare the two fixed-bit views.

<a id="pdf-1a9802b66031-p052-b001"></a>
<!-- pdf-source: page=52; block=1; confidence=0.95 -->

**Section 5.4.3, gadget trapdoors: gadgets (printed p. 50).** We now turn from short bases as
generic lattice trapdoors, to the "gadget"-based trapdoors for $q$-ary SIS/LWE lattices as
developed in [MP12], building on techniques from several related works [Ajt99, AP09, PW08,
ABB10].

*Gadgets.* The first main idea is that there are special, structured matrices $\mathbf G$, called
"gadgets," for which solving SIS and LWE is easy. The simplest gadget is as follows: for a given a
modulus $q$, define the vector

$$
\mathbf g=(1,2,4,\dots,2^{\ell-1})\in\mathbb Z_q^{\ell},
$$

where $\ell=\lceil\log_2 q\rceil$.⁸ Now observe that given any $u\in\mathbb Z_q$, we can find a
short solution $\mathbf x\in\mathbb Z^m$ to

$$
\langle\mathbf g,\mathbf x\rangle=\mathbf g^t\cdot\mathbf x=u\pmod q;
$$

for example, let $\mathbf x$ correspond to the base-two representation of $u$'s canonical
representative in $\{0,\dots,q-1\}$. In other words, it is easy to solve the SIS problem with
respect to the one-row parity-check "matrix" $\mathbf g^t$. Moreover, it is easy to randomly
sample from a discrete Gaussian over the lattice coset $\mathcal L^\perp_u(\mathbf g^t)$ of
solutions.

A bit more thought reveals that solving LWE with respect to $\mathbf g^t$ is also easy. For
simplicity, suppose that $q=2^\ell$; then given any $\mathbf b^t\approx s\cdot\mathbf g^t\pmod q$
with errors in the interval $[-\frac q4,\frac q4)$, we can recover the most-significant bit of
$s\in\mathbb Z_q$ from

$$
b_\ell\approx s\cdot2^{\ell-1}=\mathrm{msb}(s)\cdot\tfrac q2\pmod q.
$$

We can then recover the next-most-significant bit of $s$ from $b_{\ell-1}\approx s\cdot2^{\ell-2}\pmod q$,
etc. (This all generalizes to non-power-of-two moduli as well, but is a bit more technically
involved.)

We extend all of the above to $n$-dimensional SIS and LWE with respect to the block-diagonal
gadget matrix

$$
\mathbf G:=\mathbf I_n\otimes\mathbf g^t=\mathrm{diag}(\mathbf g^t,\dots,\mathbf g^t)\in\mathbb Z_q^{n\times n\ell},
$$

just by working blockwise: for LWE, given $\mathbf b^t\approx\mathbf s^t\mathbf G=(s_1\mathbf g,\dots,s_n\mathbf g)^t$,
just recover each $s_i$ from the corresponding block of $\mathbf b$. For SIS, to find a short
solution to $\mathbf G\mathbf x=\mathbf u$ for a given $\mathbf u\in\mathbb Z_q^n$, just find short
solutions to $\mathbf g^t\cdot\mathbf x_i=u_i$ for each entry $u_i$ and concatenate the results. It
is convenient to express this operation in terms of the "decomposition" function

$$
\begin{aligned}
\mathbf G^{-1}:\ &\mathbb Z_q^n\to\mathbb Z^{n\ell}\\
&\mathbf u\mapsto\text{a short solution }\mathbf x\text{ to }\mathbf G\mathbf x=\mathbf u\pmod q,
\end{aligned}\tag{5.4.1}
$$

Footnote 8: This $\mathbf g$ can be generalized in a variety of ways, e.g., by using a base other
than two, mixed bases, the Chinese Remainder Theorem, etc.

<a id="pdf-1a9802b66031-p053-b001"></a>
<!-- pdf-source: page=53; block=1; confidence=0.95 -->

**Section 5.4.3, the relation $\mathbf G\cdot\mathbf G^{-1}(\mathbf u)=\mathbf u$ (printed p. 51).**
where the choice of notation is explained by the relation

$$
\mathbf G\cdot\mathbf G^{-1}(\mathbf u)=\mathbf u\pmod q.
$$

We stress that $\mathbf G^{-1}$ is not a matrix, but rather a function that maps a mod-$q$ input to
a short integer vector. Depending on the context, the $\mathbf G^{-1}$ operation may even be
randomized, e.g., it could sample a Gaussian-distribution solution.

Finally, observe that given any invertible matrix $\mathbf H\in\mathbb Z_q^{n\times n}$, SIS and LWE
remain easy with respect to the matrix $\mathbf H\mathbf G\in\mathbb Z_q^{n\times n\ell}$.
Specifically, to solve $(\mathbf H\mathbf G)\mathbf x=\mathbf u$, simply output
$\mathbf x=\mathbf G^{-1}(\mathbf H^{-1}\cdot\mathbf u)$, and given
$\mathbf b^t\approx\mathbf s^t\mathbf H\mathbf G$, first recover $\mathbf s^t\mathbf H$ by solving
with respect to $\mathbf G$, then multiply the solution by $\mathbf H^{-1}$.

*Transcription note.* The sentence continues the display (5.4.1) from the previous page.

<a id="pdf-1a9802b66031-p068-b001"></a>
<!-- pdf-source: page=68; block=1; confidence=0.95 -->

**Section 6.1.2, bootstrapping (printed p. 66).** Even with all of the above techniques,
homomorphic operations still always increase the error rate of a ciphertext, by as much as a
polynomial factor per operation. Therefore, the schemes described so far can only homomorphically
evaluate circuits of an a-priori bounded depth; such systems are frequently called "somewhat
homomorphic" or "leveled" (we ignore the precise technical distinction between these terms).

A beautiful idea from Gentry's original work [Gen09b, Gen09a], called *bootstrapping* or sometimes
*refreshing*, makes it possible to reduce the error rate of a ciphertext, thus enabling unbounded
homomorphic computation. Suppose we have a ciphertext $c$ that encrypts some (unknown) message
$\mu$ under a secret key $s$, where the error rate of $c$ is too large to perform further
homomorphic operations on it. The idea behind bootstrapping is to homomorphically evaluate the
*decryption function* on a low-error encryption $c_s=\mathrm{Enc}(s)$ of the secret key $s$, which
is included as part of the public key. More specifically, we homomorphically evaluate the function
$f_c(\cdot)=\mathrm{Dec}(\cdot,c)$ on the ciphertext $c_s$. (Note that the ciphertext $c$ to be
refreshed is "hard-coded" into the function $f_c(\cdot)$, whereas the secret key is treated as the
function argument.) Because $f_c(s)=\mathrm{Dec}(s,c)=\mu$, it follows that homomorphic evaluation
of $f_c$ on an encryption of $s$ (namely, $c_s$) produces an encryption of $\mu$. Moreover, as long
as the circuit depth of $f_c$ and the error rate of $c_s$ are small enough, the error rate of the
output ciphertext will be substantially smaller than that of the input ciphertext $c$, as desired.
In particular, decryption can be performed in $O(\log\lambda)$ depth, so it suffices for $c_s$ to
have some $\lambda^{-O(\log\lambda)}$ error rate.

Because bootstrapping involves the homomorphic evaluation of a somewhat complex function, it is not
very efficient (see, e.g., [GH11b]). However, bootstrapping has been intensively studied and
improved in various ways [GH11a, BGV12], culminating in ring-LWE-based methods that run in only
polylogarithmic $\tilde O(1)$ time per encrypted bit [GHS12a, AP13], where the hidden
$\log^{O(1)}(\lambda)$ factors are not exceedingly large.

We conclude this discussion by noting that, in order to yield unbounded homomorphic operations,
bootstrapping requires a "circular" encryption of the secret key under itself. It is unknown
whether it is provably secure (under a standard assumption) to reveal such an encryption, but nor
are any attacks known. So to date, all unbounded FHE schemes require an additional assumption of
circular security for the secret key.

<a id="pdf-1a9802b66031-p069-b001"></a>
<!-- pdf-source: page=69; block=1; confidence=0.95 -->

**Section 6.1.3, third-generation FHE; homomorphic trapdoors, Equations (6.1.4)–(6.1.6) (printed
p. 67).** In 2013, Gentry, Sahai, and Waters (hereafter GSW) [GSW13] proposed an interesting
LWE-based FHE scheme that has some unique and advantageous properties. For example, homomorphic
multiplication does not require any key-switching step, and the scheme can be made identity-based.
Moreover, as shown in [BV14, AP14], the GSW scheme can be used to bootstrap with only a small
polynomial-factor growth in the error rate, as opposed to quasi-polynomial $\lambda^{\Theta(\log\lambda)}$
growth for the system described above. This yields unbounded FHE based on LWE with just an
inverse-polynomial $n^{-O(1)}$ error rate (plus a circular-security assumption). We describe these
results in some detail next.

*Homomorphic trapdoors.* The GSW scheme is presented most simply in terms of the gadget-based
trapdoors described in Section 5.4.3. (The presentation here has evolved through [BGG+14, AP14,
GVW15b].) At the heart of GSW are the following additive and multiplicative homomorphisms for tags
and trapdoors. Let $\bar{\mathbf A}\in\mathbb Z_q^{n\times\bar m}$ be arbitrary, and for $i=1,2$ let

$$
\mathbf A_i=x_i\mathbf G-\bar{\mathbf A}\mathbf R_i\tag{6.1.4}
$$

for some integer $x_i$ and short integer matrix $\mathbf R_i$. In other words,
$\begin{bmatrix}\mathbf R_i\\ \mathbf I\end{bmatrix}$ is a trapdoor with tag $x_i$ (or more
accurately, tag $x_i\mathbf I$) for the matrix $[\bar{\mathbf A}\mid\mathbf A_i]$.

Applying Equation (6.1.4), it is easy to verify that

$$
\mathbf A_1+\mathbf A_2=(x_1+x_2)\mathbf G-\bar{\mathbf A}(\mathbf R_1+\mathbf R_2),\tag{6.1.5}
$$

and

$$
\begin{aligned}
\mathbf A_1\cdot\mathbf G^{-1}(\mathbf A_2)&=(x_1\mathbf G-\bar{\mathbf A}\mathbf R_1)\cdot\mathbf G^{-1}(\mathbf A_2)\\
&=x_1\mathbf A_2-\bar{\mathbf A}\cdot\mathbf R_1\mathbf G^{-1}(\mathbf A_2)\\
&=x_1x_2\mathbf G-\bar{\mathbf A}\underbrace{\bigl(\mathbf R_1\mathbf G^{-1}(\mathbf A_2)+x_1\mathbf R_2\bigr)}_{\mathbf R}.
\end{aligned}\tag{6.1.6}
$$

In other words, $\begin{bmatrix}\mathbf R_1+\mathbf R_2\\ \mathbf I\end{bmatrix}$ is a trapdoor with
tag $x_1+x_2$ for the matrix $[\bar{\mathbf A}\mid\mathbf A_1+\mathbf A_2]$, and
$\begin{bmatrix}\mathbf R\\ \mathbf I\end{bmatrix}$ is a trapdoor with tag $x_1x_2$ for the matrix
$[\bar{\mathbf A}\mid\mathbf A_1\cdot\mathbf G^{-1}(\mathbf A_2)]$. Note that in the latter case,
we need $x_1$ to be a small integer in order to get a good-quality trapdoor.

One very important property of homomorphic multiplication is that the growth of the resulting
trapdoor matrix $\mathbf R$ is *asymmetric* and *quasi-additive*: while $\mathbf R_1$ is expanded by
some polynomial factor due to the multiplication by $\mathbf G^{-1}(\mathbf A_2)$, the $\mathbf R_2$
term is only multiplied by $x_1$. We discuss the implications of this below.

<a id="pdf-1a9802b66031-p069-b002"></a>
<!-- pdf-source: page=69; block=2; confidence=0.95 -->

**Section 6.1.3, fully homomorphic encryption: the GSW scheme, Equation (6.1.7) (printed
pp. 67–68).** The GSW FHE scheme works as follows. As in prior systems, the public key is a matrix
$\bar{\mathbf A}\in\mathbb Z_q^{n\times\bar m}$ whose columns are LWE samples with some secret
$\bar{\mathbf s}\in\mathbb Z^{n-1}$, i.e.,

$$
\mathbf s^t\bar{\mathbf A}\approx\mathbf 0\tag{6.1.7}
$$

where $\mathbf s=(-\bar{\mathbf s},1)$ is the secret key. An encryption of an integer $x$ is a matrix

$$
\mathbf A=x\mathbf G-\bar{\mathbf A}\mathbf R
$$

for some sufficiently short random $\mathbf R$. As usual, semantic security follows by a lossiness
argument: encrypting under a uniformly random ("malformed") public key $\bar{\mathbf A}$
statistically hides the message, because $[\bar{\mathbf A}\mid\bar{\mathbf A}\mathbf R]$ is very
close to uniformly distributed.

To decrypt a ciphertext $\mathbf A$ using the secret key $\mathbf s$, one just computes

$$
\mathbf s^t\mathbf A\approx x\cdot\mathbf s^t\mathbf G,
$$

where the approximation holds by Equation (6.1.7), and because $\mathbf R$ is short. Since it is
easy to solve LWE with respect to $\mathbf G$, we can recover $x\cdot\mathbf s^t$ and hence $x$
(modulo $q$). In fact, if $x$ is known to be just a bit, then because one of the rightmost entries
of $\mathbf s^t\mathbf G$ is far from zero modulo $q$, we can recover $x$ simply by testing whether
$\mathbf s^t\cdot\mathbf a\approx0$ for an appropriate column $\mathbf a$ of $\mathbf A$.

To homomorphically add or multiply ciphertexts $\mathbf A_1,\mathbf A_2$ that encrypt small
messages, one just computes $\mathbf A_1+\mathbf A_2$ or $\mathbf A_1\cdot\mathbf G^{-1}(\mathbf A_2)$,
respectively. As shown above in Equations (6.1.5) and (6.1.6), the resulting ciphertext is a valid
encryption for the sum or product of the messages, respectively. Because it is important for noise
growth that messages remain small integers, we typically only use operations that maintain the
messages as $\{0,1\}$-values. For example, the binary NAND operation, which is sufficient for
expressing arbitrary computations, can be written as $(x_1\text{ NAND }x_2)=1-x_1x_2$.

*Transcription note.* The block runs onto PDF page 70 (printed 68) from "for some sufficiently
short random $\mathbf R$". "$\bar{\mathbf s}\in\mathbb Z^{n-1}$" is as printed.

<a id="pdf-1a9802b66031-p070-b001"></a>
<!-- pdf-source: page=70; block=1; confidence=0.95 -->

**Section 6.1.3, bootstrapping (printed p. 68).** As first shown by Brakerski and Vaikuntanathan
[BV14], the asymmetric and quasi-additive growth of the trapdoor matrices under homomorphic
multiplication allows certain computations—in particular, decryption for the purpose of
bootstrapping—to be performed with rather small error growth. The first main observation is that
by Equation (6.1.6), any polynomial-length chain of homomorphic bit-multiplications on fresh
ciphertexts, if done in a right-associative manner, incurs only polynomial error growth. The same
also holds when multiplying a sequence of permutation matrices (or more generally, orthonormal
integer matrices), where each matrix is encrypted entry-wise.

The second main idea is that by using Barrington's Theorem [Bar86], any depth-$d$ circuit can be
converted into a length-$4^d$ branching program of permutation matrices. In particular, the
$O(\log\lambda)$-depth decryption circuit can be computed homomorphically in polynomial time and
with polynomial error growth, albeit for rather large polynomials. The subsequent work of
Alperin-Sheriff and Peikert [AP14] significantly improved the runtime and growth to small
polynomials, by avoiding Barrington's Theorem and instead expressing decryption as an arithmetic
function that can be embedded directly into permutation matrices. Ducas and Micciancio [DM15]
devised and implemented a version of this method incorporating additional ideas, yielding a system
that evaluates a complete "bootstrapped NAND gate" in less than a second on standard desktop
hardware.

## ===== TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Gadget.lean =====

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
  rw [TrapdoorFunctions.Lossy.digits_eq, decomposeVec_eq, Equiv.apply_symm_apply]

/-- `G · G⁻¹(u) = u` [Pei16, Section 5.4.3, relation `G · G⁻¹(u) = u (mod q)`].

**Proof sketch.** Fix a coordinate `j`. Over the integers, `Lossy.gadget_mulVec` evaluates
`(Lossy.gadget ℓ (n+1))ᵗ · x` at `j`, where `x` is the decomposition read as integers, to the
block-`j` digit, which `digits_decomposeVec` and `digit_val` identify with `(u j).val`. Write
`u j` as the residue of `(u j).val` (`ZMod.natCast_zmod_val`), hence as the residue of that
integer sum; the cast commutes with the finite sum (`Int.cast_sum`), and each term is the
matching entry of `G` times the lifted bit by `gadget_apply` and `Int.cast_mul`. -/
theorem gadget_mulVec_decomposeVec (P : Parameters)
    (u : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus) :
    (gadget P).mulVec (fun i => ((decomposeVec P u i).toNat : ZMod P.lwe.modulus)) = u := by
  funext j
  have h := TrapdoorFunctions.Lossy.gadget_mulVec P.width (P.lwe.dimension + 1)
    (decomposeVec P u) j
  simp only [digits_decomposeVec, digit_val] at h
  change (∑ i, TrapdoorFunctions.Lossy.gadget P.width (P.lwe.dimension + 1) i j *
    ((decomposeVec P u i).toNat : ℤ)) = ((u j).val : ℤ) at h
  change ∑ i, gadget P j i * ((decomposeVec P u i).toNat : ZMod P.lwe.modulus) = u j
  rw [← ZMod.natCast_zmod_val (u j), ← Int.cast_natCast (R := ZMod P.lwe.modulus) (u j).val,
    ← h, Int.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gadget_apply, Int.cast_mul, Int.cast_natCast]

/-- `G · G⁻¹(M) = M` for every matrix with `n+1` rows [Pei16, Section 5.4.3; AP14,
Equation (3.1)].

**Proof sketch.** Compare entry `(i, c)`: by `Matrix.mul_apply`, `decompose_apply` and
`lift_apply` it is coordinate `i` of `G` times the lifted decomposition of column `c` of `M`,
which is `M i c` by `gadget_mulVec_decomposeVec`. -/
theorem gadget_mul_decompose (P : Parameters) {ι : Type*}
    (M : Matrix (Fin (P.lwe.dimension + 1)) ι (ZMod P.lwe.modulus)) :
    gadget P * lift P (decompose P M) = M := by
  ext i c
  have h := congrFun (gadget_mulVec_decomposeVec P (fun j => M j c)) i
  rw [Matrix.mul_apply]
  simp only [lift_apply, decompose_apply]
  exact h

/-- A coordinate equal to zero decomposes to an all-false block.

**Proof sketch.** `Lossy.digits_val` writes the block-`j` digit of `decomposeVec P u` as
`∑ₖ bitₖ · 2^k`; by `digits_decomposeVec` and `digit_val` it equals `(u j).val = 0`. A sum of
natural numbers is zero only if every term is (`Finset.sum_eq_zero_iff`), so
`bitₖ · 2^k = 0`; since `2^k ≠ 0`, the bit has value `0`, i.e. it is `false`. -/
theorem decomposeVec_block_eq_false (P : Parameters)
    (u : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus) (j : Fin (P.lwe.dimension + 1))
    (hj : u j = 0) (k : Fin P.width) :
    decomposeVec P u (finProdFinEquiv (j, k)) = false := by
  have h := TrapdoorFunctions.Lossy.digits_val P.width (P.lwe.dimension + 1) (decomposeVec P u) j
  simp only [digits_decomposeVec, digit_val, hj, ZMod.val_zero] at h
  have hk := (Finset.sum_eq_zero_iff.mp h.symm) k (Finset.mem_univ k)
  rcases Nat.mul_eq_zero.mp hk with hb | hpow
  · exact Bool.toNat_eq_zero.mp hb
  · exact absurd hpow (pow_ne_zero _ two_ne_zero)

/-- If `u` vanishes outside coordinate `j₀`, any error vector with entries bounded by `β`
has inner product with the decomposition of `u` at most `ℓ·β` in absolute value. This is
the decryption-noise bound used for the `G⁻¹`-column decryptor.

**Proof sketch.** Split the sum over `Fin ((n+1)ℓ)` through `finProdFinEquiv` into blocks
(`Equiv.sum_comp`, `Fintype.sum_prod_type`). Every block `j ≠ j₀` vanishes termwise by
`decomposeVec_block_eq_false`, so `Finset.sum_eq_single` leaves block `j₀`. It is a binary
subset sum of `ℓ` errors, each of magnitude at most `β`; apply `LWE.binaryErrorSum_bound`
with `m := ℓ`. -/
theorem errorSum_decomposeVec_le (P : Parameters)
    (u : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus) (j₀ : Fin (P.lwe.dimension + 1))
    (hu : ∀ j, j ≠ j₀ → u j = 0) (e : Fin P.columns → ℤ) (β : ℕ)
    (he : ∀ i, (e i).natAbs ≤ β) :
    (∑ i, e i * ((decomposeVec P u i).toNat : ℤ)).natAbs ≤ P.width * β := by
  -- Step 1: split the index `Fin ((n+1)ℓ)` into blocks `(j, k)`.
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  -- Step 2: every block other than `j₀` vanishes.
  rw [Finset.sum_eq_single j₀ (fun j _ hj => Finset.sum_eq_zero fun k _ => by
      rw [decomposeVec_block_eq_false P u j (hu j hj) k, Bool.toNat_false, Nat.cast_zero,
        mul_zero])
    (fun h => absurd (Finset.mem_univ j₀) h)]
  -- Step 3: the surviving block is a binary subset sum of `ℓ` bounded errors.
  exact LWE.binaryErrorSum_bound (fun k => e (finProdFinEquiv (j₀, k)))
    (fun k => decomposeVec P u (finProdFinEquiv (j₀, k))) β fun k => he _

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

## ===== TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Noise.lean =====

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

**Proof sketch.** Through `encrypts_iff`, take `e = 0`; coordinatewise `1 • v + 0 = v`. -/
theorem encrypts_gadget : Encrypts P t 1 0 (gadget P) := by
  rw [encrypts_iff]
  refine ⟨0, fun j => (Int.natAbs_zero).le, ?_⟩
  ext j
  simp only [Pi.add_apply, Pi.zero_apply, Int.cast_one, one_smul, Int.cast_zero, add_zero]

/-- The zero matrix encrypts `0` with zero noise [AP14, Section 3.3].

**Proof sketch.** Through `encrypts_iff`, take `e = 0`; coordinatewise
`Matrix.vecMul_zero` and `zero_smul`. -/
theorem encrypts_zero : Encrypts P t 0 0 0 := by
  rw [encrypts_iff]
  refine ⟨0, fun j => (Int.natAbs_zero).le, ?_⟩
  ext j
  simp only [Matrix.vecMul_zero, Pi.add_apply, Pi.zero_apply, Int.cast_zero, zero_smul,
    add_zero]

/-- Weakening the noise bound preserves the invariant.

**Proof sketch.** Reuse the witness; `le_trans` on each entry. -/
theorem Encrypts.mono {x : ℤ} {β β' : ℕ} {C : Ciphertext P} (h : Encrypts P t x β C)
    (hβ : β ≤ β') : Encrypts P t x β' C := by
  obtain ⟨e, he, hC⟩ := (encrypts_iff P t x β C).mp h
  exact (encrypts_iff P t x β' C).mpr ⟨e, fun j => (he j).trans hβ, hC⟩

/-- Homomorphic addition adds messages and noise bounds [AP14, Lemma 3.5, first claim;
GSW13, Section 3.3, `Add`; BV14, Claim 3.4.1].

**Proof sketch.** Witness `e₁ + e₂`; `Int.natAbs_add_le` bounds the entries.
`Matrix.vecMul_add` splits `tᵗ(C₁+C₂)`, the two invariants are substituted, and coordinatewise
`Int.cast_add` and ring arithmetic regroup `x₁ v + e₁ + x₂ v + e₂ = (x₁+x₂) v + (e₁+e₂)`. -/
theorem Encrypts.add {x₁ x₂ : ℤ} {β₁ β₂ : ℕ} {C₁ C₂ : Ciphertext P}
    (h₁ : Encrypts P t x₁ β₁ C₁) (h₂ : Encrypts P t x₂ β₂ C₂) :
    Encrypts P t (x₁ + x₂) (β₁ + β₂) (C₁ + C₂) := by
  obtain ⟨e₁, he₁, hC₁⟩ := (encrypts_iff P t x₁ β₁ C₁).mp h₁
  obtain ⟨e₂, he₂, hC₂⟩ := (encrypts_iff P t x₂ β₂ C₂).mp h₂
  refine (encrypts_iff P t _ _ _).mpr ⟨e₁ + e₂, fun j =>
    (Int.natAbs_add_le (e₁ j) (e₂ j)).trans (Nat.add_le_add (he₁ j) (he₂ j)), ?_⟩
  rw [Matrix.vecMul_add, hC₁, hC₂]
  ext j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Int.cast_add]
  ring

/-- Negation negates the message and keeps the noise bound.

**Proof sketch.** Witness `-e`, bounded by `Int.natAbs_neg`. `Matrix.vecMul_neg` and the
invariant give `-(x v + e)`, which is `(-x) v + (-e)` coordinatewise (`Int.cast_neg`, ring). -/
theorem Encrypts.neg {x : ℤ} {β : ℕ} {C : Ciphertext P} (h : Encrypts P t x β C) :
    Encrypts P t (-x) β (-C) := by
  obtain ⟨e, he, hC⟩ := (encrypts_iff P t x β C).mp h
  refine (encrypts_iff P t _ _ _).mpr ⟨-e, fun j => (Int.natAbs_neg (e j)).le.trans (he j), ?_⟩
  rw [Matrix.vecMul_neg, hC]
  ext j
  simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, Int.cast_neg]
  ring

/-- Subtraction subtracts messages and adds noise bounds.

**Proof sketch.** `sub_eq_add_neg`, then `Encrypts.add` and `Encrypts.neg`. -/
theorem Encrypts.sub {x₁ x₂ : ℤ} {β₁ β₂ : ℕ} {C₁ C₂ : Ciphertext P}
    (h₁ : Encrypts P t x₁ β₁ C₁) (h₂ : Encrypts P t x₂ β₂ C₂) :
    Encrypts P t (x₁ - x₂) (β₁ + β₂) (C₁ - C₂) := by
  rw [sub_eq_add_neg x₁, sub_eq_add_neg C₁]
  exact Encrypts.add P h₁ (Encrypts.neg P h₂)

/-- A finite sum of encryptions encrypts the sum of the messages with the sum of the noise
bounds [AP14, Section 4.1, Equation (4.1), the outer homomorphic sum].

**Proof sketch.** `Finset.induction_on`; the empty sum is `encrypts_zero`, and each insertion
is `Encrypts.add`. -/
theorem Encrypts.sum {ι : Type*} (s : Finset ι) (x : ι → ℤ) (β : ι → ℕ)
    (C : ι → Ciphertext P) (h : ∀ i ∈ s, Encrypts P t (x i) (β i) (C i)) :
    Encrypts P t (∑ i ∈ s, x i) (∑ i ∈ s, β i) (∑ i ∈ s, C i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, Finset.sum_empty]
    exact encrypts_zero P
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
    exact Encrypts.add P (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- **Asymmetric homomorphic multiplication** [AP14, Lemma 3.5; Pei16, Equation (6.1.6);
BV14, Claim 3.4.2, mirrored]. If `C₁` encrypts `x₁` with noise `β₁` and `C₂` encrypts `x₂`
with noise `β₂`, then `C₁ ⊡ C₂` encrypts `x₁x₂` with noise at most `N·β₁ + |x₁|·β₂`. The left
operand's noise is multiplied by `N`, the number of `{0,1}` entries in a column of `G⁻¹(C₂)`;
the right operand's is multiplied only by the left message.

**Proof sketch.** The witness is `j ↦ (∑ᵢ e₁ i · X i j) + x₁ · e₂ j` with
`X = lift (G⁻¹ C₂)`. Bound: by `Int.natAbs_add_le`, the first summand is a binary subset sum
of `N` entries bounded by `β₁`, bounded by `N·β₁` via `LWE.binaryErrorSum_bound`; the second
has magnitude `|x₁|·|e₂ j| ≤ |x₁|·β₂` (`Int.natAbs_mul`). Invariant: `Matrix.vecMul_vecMul`
rewrites `tᵗ (C₁ X)` as `(tᵗ C₁) X`; substituting `h₁` and distributing
(`Matrix.add_vecMul`, `Matrix.smul_vecMul`) gives `x₁ tᵗ(G X) + e₁ᵗ X`. By
`gadget_mul_decompose`, `G X = C₂`, so the first term is `x₁ (x₂ tᵗG + e₂ᵗ)` by `h₂`. Finally
`e₁ᵗ X` is, coordinatewise, the residue of the integer sum `∑ᵢ e₁ i · X i j` (`lift_apply`,
`Int.cast_sum`), and ring arithmetic in each coordinate closes the identity. -/
theorem Encrypts.mul {x₁ x₂ : ℤ} {β₁ β₂ : ℕ} {C₁ C₂ : Ciphertext P}
    (h₁ : Encrypts P t x₁ β₁ C₁) (h₂ : Encrypts P t x₂ β₂ C₂) :
    Encrypts P t (x₁ * x₂) (P.columns * β₁ + x₁.natAbs * β₂) (mul P C₁ C₂) := by
  obtain ⟨e₁, he₁, hC₁⟩ := (encrypts_iff P t x₁ β₁ C₁).mp h₁
  obtain ⟨e₂, he₂, hC₂⟩ := (encrypts_iff P t x₂ β₂ C₂).mp h₂
  refine (encrypts_iff P t _ _ _).mpr
    ⟨fun j => (∑ i, e₁ i * ((decompose P C₂ i j).toNat : ℤ)) + x₁ * e₂ j, fun j => ?_, ?_⟩
  · -- Step 1: the binary subset sum and the scaled right error.
    refine (Int.natAbs_add_le _ _).trans (Nat.add_le_add ?_ ?_)
    · exact LWE.binaryErrorSum_bound e₁ (fun i => decompose P C₂ i j) β₁ he₁
    · rw [Int.natAbs_mul]
      exact Nat.mul_le_mul_left _ (he₂ j)
  · -- Step 2: `tᵗ (C₁ X) = (x₁ tᵗG + e₁ᵗ) X = x₁ tᵗ (G X) + e₁ᵗ X` and `G X = C₂`.
    rw [mul_eq, ← Matrix.vecMul_vecMul, hC₁, Matrix.add_vecMul, Matrix.smul_vecMul,
      Matrix.vecMul_vecMul, gadget_mul_decompose, hC₂]
    -- Step 3: read `e₁ᵗ X` coordinatewise as the residue of an integer sum.
    have hX : Matrix.vecMul (fun i => (e₁ i : ZMod P.lwe.modulus)) (lift P (decompose P C₂)) =
        fun j => ((∑ i, e₁ i * ((decompose P C₂ i j).toNat : ℤ) : ℤ) : ZMod P.lwe.modulus) := by
      ext j
      change ∑ i, (e₁ i : ZMod P.lwe.modulus) * lift P (decompose P C₂) i j = _
      simp only [lift_apply, Int.cast_sum, Int.cast_mul, Int.cast_natCast]
    rw [hX]
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Int.cast_add, Int.cast_mul]
    ring

/-- For a bit message on the left, multiplication has noise `N·β₁ + β₂` [GSW13, Section 3.3,
`Mult`; Pei16, Section 6.1.3].

**Proof sketch.** `Encrypts.mul` and `Encrypts.mono`, since `(b.toNat : ℤ).natAbs = b.toNat ≤ 1`
(`Int.natAbs_natCast`, `Bool.toNat_le`). -/
theorem Encrypts.mul_bit {b : Bool} {x₂ : ℤ} {β₁ β₂ : ℕ} {C₁ C₂ : Ciphertext P}
    (h₁ : Encrypts P t (b.toNat : ℤ) β₁ C₁) (h₂ : Encrypts P t x₂ β₂ C₂) :
    Encrypts P t ((b.toNat : ℤ) * x₂) (P.columns * β₁ + β₂) (GSW.mul P C₁ C₂) := by
  refine Encrypts.mono P (Encrypts.mul P h₁ h₂) (Nat.add_le_add_left ?_ _)
  rw [Int.natAbs_natCast]
  exact (Nat.mul_le_mul_right β₂ (Bool.toNat_le b)).trans (Nat.one_mul β₂).le

/-- Symmetric corollary: two bit-message operands with noise at most `β` give a product with
noise at most `(N+1)·β` [GSW13, Section 3.4; Pei16, Section 6.1.3].

**Proof sketch.** `Encrypts.mul_bit` and `N·β + β = (N+1)·β`; the message
`(b₁ && b₂).toNat = b₁.toNat · b₂.toNat` by cases on the bits. -/
theorem Encrypts.mul_le {b₁ b₂ : Bool} {β : ℕ} {C₁ C₂ : Ciphertext P}
    (h₁ : Encrypts P t (b₁.toNat : ℤ) β C₁) (h₂ : Encrypts P t (b₂.toNat : ℤ) β C₂) :
    Encrypts P t ((b₁ && b₂).toNat : ℤ) ((P.columns + 1) * β) (GSW.mul P C₁ C₂) := by
  have hm : ((b₁ && b₂).toNat : ℤ) = (b₁.toNat : ℤ) * (b₂.toNat : ℤ) := by
    cases b₁ <;> cases b₂ <;> rfl
  rw [hm, Nat.succ_mul]
  exact Encrypts.mul_bit P h₁ h₂

/-- **Homomorphic NAND** [GSW13, Sections 3.3–3.4, `NAND`, "the error is increased by a
factor of at most `N + 1`"; Pei16, Section 6.1.3]. Bit encryptions with noise `β₁`, `β₂` give
an encryption of `NAND(b₁,b₂)` with noise at most `N·β₁ + β₂`.

**Proof sketch.** `encrypts_gadget`, `Encrypts.mul_bit`, `Encrypts.sub` give noise
`0 + (N·β₁ + β₂)`, which `Encrypts.mono` drops to `N·β₁ + β₂`; the message `1 − b₁b₂` equals
`(!(b₁ && b₂)).toNat` by cases on the bits. -/
theorem Encrypts.nand {b₁ b₂ : Bool} {β₁ β₂ : ℕ} {C₁ C₂ : Ciphertext P}
    (h₁ : Encrypts P t (b₁.toNat : ℤ) β₁ C₁) (h₂ : Encrypts P t (b₂.toNat : ℤ) β₂ C₂) :
    Encrypts P t ((!(b₁ && b₂)).toNat : ℤ) (P.columns * β₁ + β₂) (nand P C₁ C₂) := by
  have hm : ((!(b₁ && b₂)).toNat : ℤ) = 1 - (b₁.toNat : ℤ) * (b₂.toNat : ℤ) := by
    cases b₁ <;> cases b₂ <;> rfl
  rw [hm, nand_eq]
  exact Encrypts.mono P (Encrypts.sub P (encrypts_gadget P) (Encrypts.mul_bit P h₁ h₂))
    (Nat.zero_add _).le

/-- **Product chains grow additively** [AP14, Corollary 3.6, worst-case form; Pei16,
Section 6.1.3, "any polynomial-length chain of homomorphic bit-multiplications on fresh
ciphertexts, if done in a right-associative manner, incurs only polynomial error growth";
BV14, Claim 3.4.2 and the proof of Lemma 3.6, mirrored]. If every `Cᵢ` encrypts the bit `bᵢ`
with noise at most `β` and `acc` encrypts `x` with noise `β₀`, then
`C₁ ⊡ (⋯ ⊡ (Cₖ ⊡ acc))` encrypts `(∏ bᵢ)·x` with noise at most `β₀ + k·N·β`.

**Proof sketch.** Induction on the `List.Forall₂` hypothesis. The empty chain is the
accumulator, and the empty conjunction is `true`, whose `toNat` is `1`. The step is
`Encrypts.mul_bit` with the head on the left: noise `N·β + (previous)`, message
`b · ((∏ rest) · x)`; the message of the cons is `(b && ∏ rest) · x`, which is that product
because `Bool.toNat` turns `&&` into multiplication (cases on the bits), and the noise
`β₀ + (k+1)·N·β` equals `N·β + (β₀ + k·N·β)` by ring arithmetic. -/
theorem encrypts_chain {bs : List Bool} {Cs : List (Ciphertext P)} {β β₀ : ℕ} {x : ℤ}
    {acc : Ciphertext P}
    (hs : List.Forall₂ (fun b C => Encrypts P t (b.toNat : ℤ) β C) bs Cs)
    (hacc : Encrypts P t x β₀ acc) :
    Encrypts P t (((bs.all id).toNat : ℤ) * x) (β₀ + Cs.length * (P.columns * β))
      (chain P Cs acc) := by
  have hand : ∀ a c : Bool, ((a && c).toNat : ℤ) = (a.toNat : ℤ) * (c.toNat : ℤ) := by
    intro a c
    cases a <;> cases c <;> rfl
  induction hs with
  | nil =>
    -- Step 1: the empty chain is the accumulator, with message `1 · x`.
    rw [chain_nil, List.all_nil, Bool.toNat_true, Nat.cast_one, one_mul, List.length_nil,
      zero_mul, add_zero]
    exact hacc
  | @cons b C bs Cs hbC _ ih =>
    -- Step 2: multiply the head on the left of the shorter chain (`Encrypts.mul_bit`).
    rw [chain_cons, List.all_cons, hand, id_eq, mul_assoc, List.length_cons]
    have hn : β₀ + (Cs.length + 1) * (P.columns * β) =
        P.columns * β + (β₀ + Cs.length * (P.columns * β)) := by ring
    rw [hn]
    exact Encrypts.mul_bit P hbC ih

end Closure

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

## ===== TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Scheme.lean =====

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

**Proof sketch.** Write coordinate `i` of `tᵗ Ā` as a sum over the `n+1` rows and split off the
last row (`Fin.sum_univ_castSucc`). Column `i` of `Regev.augmented` is the `i`-th sample's row
followed by its value (`Regev.augmented_eq`, `Fin.snoc_castSucc`, `Fin.snoc_last`), and `t` is
`−s` followed by `1`. The inner product is `−⟨s, aᵢ⟩ + (⟨aᵢ, s⟩ + eᵢ)` by
`LWE.noisyValues_apply`; commuting the factors of `⟨s, aᵢ⟩` cancels it, leaving `eᵢ`. -/
theorem vecMul_secretVector_augmented (P : Parameters)
    (A : Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus))
    (s : Fin P.lwe.dimension → ZMod P.lwe.modulus) (e : Fin P.lwe.samples → ℤ) :
    Matrix.vecMul (secretVector P s) (Regev.augmented P.lwe (A, LWE.noisyValues P.lwe A s e)) =
      fun i => (e i : ZMod P.lwe.modulus) := by
  funext i
  -- Step 1: the product at column `i` as a sum, with the last row split off.
  change ∑ j, secretVector P s j *
      Regev.augmented P.lwe (A, LWE.noisyValues P.lwe A s e) j i = _
  rw [Fin.sum_univ_castSucc, secretVector_eq, Regev.augmented_eq]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Matrix.transpose_apply, Pi.neg_apply,
    LWE.noisyValues_apply, one_mul, neg_mul, Finset.sum_neg_distrib]
  -- Step 2: `−⟨s, aᵢ⟩ + (⟨aᵢ, s⟩ + eᵢ) = eᵢ`.
  have hc : ∑ j, s j * A i j = ∑ j, A i j * s j :=
    Finset.sum_congr rfl fun j _ => mul_comm (s j) (A i j)
  rw [hc, neg_add_cancel_left]

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

**Proof sketch.** The witness is `j ↦ ∑ᵢ eᵢ · R i j`, bounded by `m·B` through
`LWE.binaryErrorSum_bound` applied to column `j` of `R`. `Matrix.vecMul_add`,
`Matrix.vecMul_smul` and `Matrix.vecMul_vecMul` give `tᵗ C = (tᵗ Ā) R + μ tᵗ G`, and
`vecMul_secretVector_augmented` replaces `tᵗ Ā` by `eᵗ`. Coordinate `j` of `eᵗ R` is
`∑ᵢ eᵢ · R i j` read modulo `q` (`lift_apply`, `Int.cast_sum`, `Int.cast_mul`). -/
theorem encrypts_encrypt (P : Parameters)
    (A : Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus))
    (s : Fin P.lwe.dimension → ZMod P.lwe.modulus) (e : Fin P.lwe.samples → ℤ) (B : ℕ)
    (he : ∀ i, (e i).natAbs ≤ B) (μ : Bool)
    (R : Matrix (Fin P.lwe.samples) (Fin P.columns) Bool) :
    Encrypts P (secretVector P s) (μ.toNat : ℤ) (P.lwe.samples * B)
      (encrypt P (A, LWE.noisyValues P.lwe A s e) μ R) := by
  rw [encrypts_iff]
  refine ⟨fun j => ∑ i, e i * ((R i j).toNat : ℤ),
    fun j => LWE.binaryErrorSum_bound e (fun i => R i j) B he, ?_⟩
  -- Step 1: `tᵗ C = (tᵗ Ā) R + μ tᵗ G`, and `tᵗ Ā = eᵗ`.
  rw [encrypt_eq, Matrix.vecMul_add, Matrix.vecMul_smul, ← Matrix.vecMul_vecMul,
    vecMul_secretVector_augmented, Int.cast_natCast, add_comm]
  -- Step 2: `eᵗ R` is the cast of the integer subset sums.
  congr 1
  funext j
  change ∑ i, (e i : ZMod P.lwe.modulus) * lift P R i j = _
  simp only [lift_apply, Int.cast_sum, Int.cast_mul, Int.cast_natCast]

/-- Fresh-encryption noise for the actual key generator and a `B`-bounded noise law.

**Proof sketch.** `Regev.keygen_fst` and `Regev.keygen_snd` expose the sample and the secret;
`LWE.sample_fst` and `LWE.sample_snd` write the sample as `(A, A s + e)` with
`eᵢ = χ.sample(seedᵢ)`, and `Noise.bounded_iff` bounds each `eᵢ` by `B`. Then apply
`encrypts_encrypt`. -/
theorem encrypts_keygen_encrypt (P : Parameters) (χ : LWE.Noise)
    (rg : Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      ((Fin P.lwe.dimension → ZMod P.lwe.modulus) × (Fin P.lwe.samples → χ.Coins)))
    (B : ℕ) (hχ : χ.Bounded B) (μ : Bool)
    (R : Matrix (Fin P.lwe.samples) (Fin P.columns) Bool) :
    Encrypts P (secretVector P (Regev.keygen P.lwe χ rg).2) (μ.toNat : ℤ) (P.lwe.samples * B)
      (encrypt P (Regev.keygen P.lwe χ rg).1 μ R) := by
  have hs : LWE.sample P.lwe χ rg =
      (rg.1, LWE.noisyValues P.lwe rg.1 rg.2.1 (fun i => χ.sample (rg.2.2 i))) :=
    Prod.ext (LWE.sample_fst P.lwe χ rg) (LWE.sample_snd P.lwe χ rg)
  rw [Regev.keygen_fst, Regev.keygen_snd, hs]
  exact encrypts_encrypt P rg.1 rg.2.1 _ B
    (fun i => (LWE.Noise.bounded_iff χ B).1 hχ (rg.2.2 i)) μ R

/-- `halfVector P` vanishes at every coordinate except the last. Technical glue. -/
private theorem halfVector_eq_zero_of_ne_last (P : Parameters) (j : Fin (P.lwe.dimension + 1))
    (hj : j ≠ Fin.last P.lwe.dimension) : halfVector P j = 0 := by
  obtain ⟨j', rfl⟩ := Fin.exists_castSucc_eq.2 hj
  rw [halfVector_eq, Fin.snoc_castSucc, Pi.zero_apply]

/-- If `C` encrypts the bit `b` under `t = (−s,1)` with the error vector `e`, decryption decodes
`codepoint b` plus the integer error sum of `e` against the decomposition of `halfVector P`.
Technical glue shared by the two decryption theorems.

**Proof sketch.** The Regev residual of the split column `v = C x` is `⟨t, v⟩`, by splitting
off the last coordinate. Then `⟨t, C x⟩ = ⟨tᵗ C, x⟩`, the invariant gives
`b·⟨tᵗ G, x⟩ + ⟨e, x⟩ = b·⟨t, G x⟩ + ⟨e, x⟩`, `G x = w` and `⟨t, w⟩ = codepoint true`. -/
private theorem decrypt_eq_decode_errorSum (P : Parameters)
    (s : Fin P.lwe.dimension → ZMod P.lwe.modulus) (b : Bool) (β : ℕ) (C : Ciphertext P)
    (h : Encrypts P (secretVector P s) (b.toNat : ℤ) β C) :
    ∃ e : Fin P.columns → ℤ, (∀ j, (e j).natAbs ≤ β) ∧
      decrypt P s C = LWE.BitEncoding.decode P.lwe (LWE.BitEncoding.codepoint P.lwe b +
        ((∑ i, e i * ((decomposeVec P (halfVector P) i).toNat : ℤ) : ℤ) :
          ZMod P.lwe.modulus)) := by
  obtain ⟨e, he, hC⟩ := (encrypts_iff P _ _ β C).1 h
  refine ⟨e, he, ?_⟩
  -- Step 1: the Regev residual of the split column `v = C x` is `⟨t, v⟩`.
  have hsplit : decryptColumn P C (Fin.last _) - ∑ j, s j * Fin.init (decryptColumn P C) j =
      dotProduct (secretVector P s) (C.mulVec
        (fun i => ((decomposeVec P (halfVector P) i).toNat : ZMod P.lwe.modulus))) := by
    rw [← decryptColumn_eq]
    change _ = ∑ i, secretVector P s i * decryptColumn P C i
    rw [Fin.sum_univ_castSucc, secretVector_eq]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Pi.neg_apply, neg_mul, one_mul,
      Finset.sum_neg_distrib, Fin.init_def]
    abel
  -- Step 2: `⟨t, w⟩ = codepoint true`, and `b · codepoint true = codepoint b`.
  have hw : dotProduct (secretVector P s) (halfVector P) =
      LWE.BitEncoding.codepoint P.lwe true := by
    change ∑ i, secretVector P s i * halfVector P i = _
    rw [Fin.sum_univ_castSucc, secretVector_eq, halfVector_eq]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Pi.zero_apply, mul_zero,
      Finset.sum_const_zero, zero_add, one_mul]
  have hb : ((b.toNat : ℤ) : ZMod P.lwe.modulus) * LWE.BitEncoding.codepoint P.lwe true =
      LWE.BitEncoding.codepoint P.lwe b := by
    cases b <;> simp only [LWE.BitEncoding.codepoint_eq, Bool.toNat_false, Bool.toNat_true,
      Nat.cast_zero, Nat.cast_one, Int.cast_zero, Int.cast_one, zero_mul, one_mul,
      Bool.false_eq_true, if_false, if_true]
  -- Step 3: the error term is the cast of the integer error sum.
  have herr : dotProduct (fun j => (e j : ZMod P.lwe.modulus))
      (fun i => ((decomposeVec P (halfVector P) i).toNat : ZMod P.lwe.modulus)) =
      ((∑ i, e i * ((decomposeVec P (halfVector P) i).toNat : ℤ) : ℤ) :
        ZMod P.lwe.modulus) := by
    change ∑ i, (e i : ZMod P.lwe.modulus) *
      ((decomposeVec P (halfVector P) i).toNat : ZMod P.lwe.modulus) = _
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast]
  -- Step 4: assemble `⟨t, C x⟩ = b·⟨t, G x⟩ + ⟨e, x⟩`.
  rw [decrypt_eq, Regev.decrypt_eq]
  dsimp only
  rw [hsplit, Matrix.dotProduct_mulVec, hC, add_dotProduct, smul_dotProduct,
    ← Matrix.dotProduct_mulVec, gadget_mulVec_decomposeVec, hw, herr, smul_eq_mul, hb]

/-- **Decryption from the invariant.** If `C` encrypts the bit `b` under `t = (−s,1)` with
noise `β` and `2·(ℓ·β) < ⌊q/2⌋`, then `decrypt P s C = b` [GSW13, Section 3.1, "if
`xᵢ = μ·vᵢ + e'` for some error `e'` of magnitude at most `q/8` … Dec … output[s] the correct
value"; AP14, Claim 3.4; BV14, Lemma 3.2].

**Proof sketch.** The private glue lemma `decrypt_eq_decode_errorSum` does the algebra:
`Regev.decrypt_eq` reads `c.2 − ⟨s, c.1⟩`, which for the split column `v` is `⟨t, v⟩`
(`Fin.sum_univ_castSucc`, `secretVector_eq`). `Matrix.dotProduct_mulVec` turns `⟨t, C x⟩` into
`⟨tᵗC, x⟩` with `x = G⁻¹(w)` lifted; substituting the invariant gives
`b·⟨t, G x⟩ + ⟨e, x⟩ = b·⟨t, w⟩ + ⟨e, x⟩` by `gadget_mulVec_decomposeVec`, and `⟨t, w⟩ = ⌊q/2⌋`
because `w` vanishes off the last coordinate where `t` is `1`. So the residual is
`codepoint b + ⟨e, x⟩`. Since `w` vanishes off the last coordinate,
`errorSum_decomposeVec_le` (with `j₀ = last`) bounds `|⟨e, x⟩| ≤ ℓ·β`, and
`LWE.BitEncoding.decode_codepoint_add` with `B := ℓ·β` finishes. -/
theorem decrypt_of_encrypts (P : Parameters) (s : Fin P.lwe.dimension → ZMod P.lwe.modulus)
    (b : Bool) (β : ℕ) (C : Ciphertext P) (h : Encrypts P (secretVector P s) (b.toNat : ℤ) β C)
    (hsep : 2 * (P.width * β) < P.lwe.modulus / 2) :
    decrypt P s C = b := by
  obtain ⟨e, he, hdec⟩ := decrypt_eq_decode_errorSum P s b β C h
  rw [hdec]
  exact LWE.BitEncoding.decode_codepoint_add P.lwe (P.width * β) b _
    (errorSum_decomposeVec_le P (halfVector P) (Fin.last _)
      (halfVector_eq_zero_of_ne_last P) e β he) hsep

/-- At a power-of-two modulus `q = 2^ℓ` with `ℓ ≥ 1`, noise `β` with `2β < q/2` decrypts
correctly: `⌊q/2⌋ = 2^{ℓ−1}` has a single binary digit, so the decryption column is the last
gadget column [AP14, Claim 3.4, dyadic case; GSW13, Section 3.1, `MPDec` remark].

**Proof sketch.** As `decrypt_of_encrypts`, the residual is `codepoint b + ⟨e, x⟩` with `x` the
decomposition of `w` (`decrypt_eq_decode_errorSum`). Here `⌊q/2⌋ = 2^{ℓ−1} < q`, and `x` is the
indicator of the single position `i₀ = (n, ℓ−1)` (last block and top position, zero-based):
both have the same block digits (`Lossy.digits_val`, `digits_decomposeVec`, `digit_val`; the
last block's positional sum is `2^{ℓ−1}`, every other block's is `0 = w_j`), and the digit map
is injective (`Lossy.digits_injective`). So the error sum is the single entry `e i₀`, bounded by
`β`, and `LWE.BitEncoding.decode_codepoint_add` with `B := β` finishes. -/
theorem decrypt_of_encrypts_dyadic (P : Parameters)
    (hq : P.lwe.modulus = 2 ^ P.width) (hℓ : 0 < P.width)
    (s : Fin P.lwe.dimension → ZMod P.lwe.modulus) (b : Bool) (β : ℕ) (C : Ciphertext P)
    (h : Encrypts P (secretVector P s) (b.toNat : ℤ) β C)
    (hsep : 2 * β < P.lwe.modulus / 2) :
    decrypt P s C = b := by
  obtain ⟨e, he, hdec⟩ := decrypt_eq_decode_errorSum P s b β C h
  rw [hdec]
  have hl : P.width - 1 < P.width := Nat.sub_lt hℓ Nat.one_pos
  obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin P.columns,
      i₀ = finProdFinEquiv (Fin.last P.lwe.dimension, ⟨P.width - 1, hl⟩) := ⟨_, rfl⟩
  -- Step 1: `⌊q/2⌋ = 2^{ℓ-1}`, a residue below `q`.
  have hhalf : P.lwe.modulus / 2 = 2 ^ (P.width - 1) := by
    have h2 : 2 ^ P.width = 2 ^ (P.width - 1) * 2 := by
      rw [← pow_succ, Nat.sub_add_cancel hℓ]
    rw [hq, h2, Nat.mul_div_cancel _ two_pos]
  have hlt : P.lwe.modulus / 2 < P.lwe.modulus :=
    Nat.div_lt_self (by have := P.lwe.modulus_ge_two; omega) one_lt_two
  -- Step 2: the decomposition of `w` is the indicator of `i₀ = (last, ℓ-1)`, since its digit
  -- vector is that of `w` (`digits_val`) and the digit map is injective.
  have hz : decomposeVec P (halfVector P) = fun i => decide (i = i₀) := by
    apply TrapdoorFunctions.Lossy.digits_injective P.width (P.lwe.dimension + 1)
    rw [digits_decomposeVec]
    funext j
    apply Fin.ext
    simp only [digit_val, TrapdoorFunctions.Lossy.digits_val]
    refine Fin.lastCases ?_ (fun j' => ?_) j
    · rw [halfVector_eq, Fin.snoc_last, LWE.BitEncoding.codepoint_eq, if_pos rfl,
        ZMod.val_natCast, Nat.mod_eq_of_lt hlt, hhalf,
        Fintype.sum_eq_single (⟨P.width - 1, hl⟩ : Fin P.width)]
      · rw [← hi₀, decide_eq_true rfl, Bool.toNat_true, one_mul]
      · intro k hk
        have hne : finProdFinEquiv (Fin.last P.lwe.dimension, k) ≠ i₀ := by
          rw [hi₀]
          intro hk'
          exact hk (Prod.ext_iff.1 (finProdFinEquiv.injective hk')).2
        rw [decide_eq_false hne, Bool.toNat_false, zero_mul]
    · rw [halfVector_eq, Fin.snoc_castSucc, Pi.zero_apply, ZMod.val_zero]
      symm
      refine Finset.sum_eq_zero fun k _ => ?_
      have hne : finProdFinEquiv (j'.castSucc, k) ≠ i₀ := by
        rw [hi₀]
        intro hk'
        exact Fin.castSucc_ne_last j' (Prod.ext_iff.1 (finProdFinEquiv.injective hk')).1
      rw [decide_eq_false hne, Bool.toNat_false, zero_mul]
  -- Step 3: the error sum is the single entry `e i₀`, bounded by `β`.
  have hsum : (∑ i, e i * ((decomposeVec P (halfVector P) i).toNat : ℤ)) = e i₀ := by
    rw [hz, Fintype.sum_eq_single i₀]
    · dsimp only
      rw [decide_eq_true rfl, Bool.toNat_true, Nat.cast_one, mul_one]
    · intro i hi
      dsimp only
      rw [decide_eq_false hi, Bool.toNat_false, Nat.cast_zero, mul_zero]
  rw [hsum]
  exact LWE.BitEncoding.decode_codepoint_add P.lwe β b (e i₀) (he i₀) hsep

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
  exact decrypt_of_encrypts P _ μ (P.lwe.samples * B) _
    (encrypts_keygen_encrypt P χ rg B hχ μ R) hsep

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

## ===== TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Symmetric.lean =====

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

**Proof sketch.** The witness is `j ↦ e (rowEquiv (i, j))`, bounded by `B`.
`Matrix.vecMul_add`, `Matrix.vecMul_smul` split `tᵗ Cᵢ`; the block of `tᵗ Ā` is `tᵗ Ā` read at
the reindexed columns (`Matrix.submatrix_apply`), equal to `e ∘ rowEquiv` by
`vecMul_secretVector_augmented`. -/
theorem encrypts_symEncrypt (P : Parameters) {k : ℕ} (hN : P.lwe.samples = k * P.columns)
    (A : Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus))
    (s : Fin P.lwe.dimension → ZMod P.lwe.modulus) (e : Fin P.lwe.samples → ℤ) (B : ℕ)
    (he : ∀ i, (e i).natAbs ≤ B) (μ : Fin k → Bool) (i : Fin k) :
    Encrypts P (secretVector P s) ((μ i).toNat : ℤ) B
      (symEncrypt P hN (A, LWE.noisyValues P.lwe A s e) μ i) := by
  rw [encrypts_iff]
  refine ⟨fun j => e (rowEquiv P hN (i, j)), fun j => he _, ?_⟩
  -- Step 1: `tᵗ Cᵢ = (tᵗ Ā) ∘ rowEquiv(i, ·) + μᵢ tᵗ G`.
  rw [symEncrypt_apply, Matrix.vecMul_add, Matrix.vecMul_smul, Int.cast_natCast, add_comm]
  congr 1
  funext j
  -- Step 2: column `j` of the block is column `rowEquiv (i, j)` of `Ā`, read by
  -- `vecMul_secretVector_augmented`.
  change ∑ a, secretVector P s a *
    (Regev.augmented P.lwe (A, LWE.noisyValues P.lwe A s e)).submatrix
      id (fun j => rowEquiv P hN (i, j)) a j = _
  simp only [Matrix.submatrix_apply, id_eq]
  exact congrFun (vecMul_secretVector_augmented P A s e) (rowEquiv P hN (i, j))

/-- For every message vector `μ`, the batch map `c ↦ symEncrypt P hN c μ` on challenges is a
bijection onto `Fin k → Ciphertext P`, given as an equivalence. Technical glue.

**Proof sketch.** Compose the augmentation bijection (`Regev.augmented_bijective`), the
column reindexing `M ↦ (i ↦ M · rowEquiv(i, ·))` (inverse: read column `c` of block
`rowEquiv⁻¹ c`), and the translation by `i ↦ μᵢ G`. -/
private theorem exists_equiv_symEncrypt (P : Parameters) {k : ℕ}
    (hN : P.lwe.samples = k * P.columns) (μ : Fin k → Bool) :
    ∃ E : (Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
        (Fin P.lwe.samples → ZMod P.lwe.modulus)) ≃ (Fin k → Ciphertext P),
      ∀ c, E c = symEncrypt P hN c μ := by
  -- Step 1: augmentation.
  let E₁ := Equiv.ofBijective _ (Regev.augmented_bijective P.lwe)
  -- Step 2: column reindexing through `rowEquiv`.
  let E₂ : Matrix (Fin (P.lwe.dimension + 1)) (Fin P.lwe.samples) (ZMod P.lwe.modulus) ≃
      (Fin k → Ciphertext P) :=
    { toFun := fun M i => M.submatrix id (fun j => rowEquiv P hN (i, j))
      invFun := fun F a c => F ((rowEquiv P hN).symm c).1 a ((rowEquiv P hN).symm c).2
      left_inv := by
        intro M
        funext a c
        change M a (rowEquiv P hN (((rowEquiv P hN).symm c).1, ((rowEquiv P hN).symm c).2)) =
          M a c
        rw [Prod.mk.eta, Equiv.apply_symm_apply]
      right_inv := by
        intro F
        funext i a j
        change F ((rowEquiv P hN).symm (rowEquiv P hN (i, j))).1 a
          ((rowEquiv P hN).symm (rowEquiv P hN (i, j))).2 = F i a j
        rw [Equiv.symm_apply_apply] }
  -- Step 3: translation by the message gadgets.
  refine ⟨E₁.trans (E₂.trans
    (Equiv.addRight fun i => ((μ i).toNat : ZMod P.lwe.modulus) • gadget P)), fun c => ?_⟩
  funext i
  rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.coe_addRight, Equiv.ofBijective_apply,
    symEncrypt_apply]
  rfl

/-- **Concrete IND-CPA bound for batched secret-key GSW** [AP14, Section 3.2, "The IND-CPA
security of the scheme follows immediately from the assumed hardness of LWE"; Wu24,
Lecture 21, the two-hybrid pattern]. For two message vectors, the distributions of the `k`
ciphertexts under one uniform secret differ by at most two DLWE advantages with `k·N` rows.

**Proof sketch.** As `Encryption.Symmetric.Regev.distAdv_encrypt_le`: each real batch is
`symEncrypt` of the actual LWE sample (`acceptProb_def`); on the uniform side,
`(A,b) ↦ symEncrypt P hN (A,b) μ` is an equivalence onto `Fin k → Ciphertext P` (the private
glue `exists_equiv_symEncrypt`: `Regev.augmented_bijective`, the column reindexing by
`rowEquiv`, and translation by `μG`), so by `acceptProb_comp_equiv` both ideal acceptance
probabilities equal that of a uniform batch. Insert it between the two real experiments
(`LWE.decisionAdvantage_eq`, `distAdv_def`) and use the triangle inequality. -/
theorem distAdv_symEncrypt_le {ρ : Type*} [Fintype ρ] [Nonempty ρ]
    (P : Parameters) {k : ℕ} (hN : P.lwe.samples = k * P.columns) (χ : LWE.Noise)
    (μ₀ μ₁ : Fin k → Bool) (D : (Fin k → Ciphertext P) → ρ → Bool) :
    distAdv (fun r => symEncrypt P hN (LWE.sample P.lwe χ r) μ₀)
        (fun r => symEncrypt P hN (LWE.sample P.lwe χ r) μ₁) D ≤
      LWE.decisionAdvantage P.lwe χ (fun c r => D (symEncrypt P hN c μ₀) r) +
      LWE.decisionAdvantage P.lwe χ (fun c r => D (symEncrypt P hN c μ₁) r) := by
  -- Step 1: each real batch is `symEncrypt` of the actual LWE sample.
  have hreal (μ : Fin k → Bool) :
      acceptProb (fun r => symEncrypt P hN (LWE.sample P.lwe χ r) μ) D =
        acceptProb (LWE.sample P.lwe χ) (fun c r => D (symEncrypt P hN c μ) r) := by
    rw [acceptProb_def, acceptProb_def]
  -- Step 2: on a uniform challenge, every batch is a uniform batch of ciphertexts.
  have hideal (μ : Fin k → Bool) :
      acceptProb (id : (Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
        (Fin P.lwe.samples → ZMod P.lwe.modulus)) → _) (fun c r => D (symEncrypt P hN c μ) r) =
        acceptProb (id : (Fin k → Ciphertext P) → _) D := by
    obtain ⟨E, hE⟩ := exists_equiv_symEncrypt P hN μ
    rw [← acceptProb_comp_equiv E id D, acceptProb_def, acceptProb_def]
    simp only [id_eq, hE]
  -- Step 3: insert the uniform batch and use the triangle inequality.
  rw [LWE.decisionAdvantage_eq, LWE.decisionAdvantage_eq, distAdv_def, distAdv_def,
    distAdv_def, hideal μ₀, hideal μ₁, ← hreal μ₀, ← hreal μ₁]
  calc
    _ ≤ |acceptProb (fun r => symEncrypt P hN (LWE.sample P.lwe χ r) μ₀) D -
          acceptProb (id : (Fin k → Ciphertext P) → _) D| +
        |acceptProb (id : (Fin k → Ciphertext P) → _) D -
          acceptProb (fun r => symEncrypt P hN (LWE.sample P.lwe χ r) μ₁) D| :=
      abs_sub_le _ _ _
    _ = _ := by rw [abs_sub_comm (acceptProb (id : (Fin k → Ciphertext P) → _) D)]

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

## ===== TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Eval.lean =====

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
ciphertext itself for a singleton, and otherwise a right-associative product chain, each head
multiplied on the left [Pei16, Section 6.1.3; AP14, Corollary 3.6]. The singleton case avoids a
needless product. -/
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
  induction hs with
  | nil =>
    -- `[]`: the gadget encrypts `1 = ([].all id).toNat` with noise `0 ≤ β`.
    rw [homAnd_nil, List.all_nil]
    exact Encrypts.mono P (encrypts_gadget P) (Nat.zero_le _)
  | @cons b C bs Cs hb hrest ih =>
    cases hrest with
    | nil =>
      -- `[C]`: the ciphertext itself, with noise `((1 - 1)·N + 1)·β = β`.
      rw [homAnd_singleton, List.all_cons, List.all_nil, Bool.and_true]
      simpa only [List.length_singleton, Nat.sub_self, zero_mul, zero_add, one_mul] using hb
    | @cons b' C' bs' Cs' hb' hrest' =>
      -- `C :: C' :: Cs'`: one product with the head on the left (`Encrypts.mul_bit`).
      rw [homAnd_cons_cons, List.all_cons]
      have hmsg : (((id b && (b' :: bs').all id)).toNat : ℤ) =
          (b.toNat : ℤ) * ((b' :: bs').all id).toNat := by
        cases b <;> cases ((b' :: bs').all id) <;> rfl
      rw [hmsg]
      refine Encrypts.mono P (Encrypts.mul_bit P hb ih) (le_of_eq ?_)
      simp only [List.length_cons, Nat.add_sub_cancel]
      ring

/-- **Per-gate noise.** A gate of fan-in at most two, whose argument vertices hold `β`-noisy
encryptions of their values, produces a `(N+1)·β`-noisy encryption of its value [GSW13,
Section 3.3, `NAND`: "the error is increased by a factor of at most `N + 1`"].

**Proof sketch.** With `bs = g.args.map (vals.getD · false)` and
`Cs = g.args.map (cts.getD · 0)`, `List.forall₂_map_left_iff`, `List.forall₂_map_right_iff` and
`List.forall₂_same` turn `hargs` into the hypothesis of `homAnd_encrypts`; `List.all_map` matches
the messages, and `length ≤ 2` bounds `((k−1)·N+1)·β ≤ (N+1)·β`. Then case on `g.kind` through
`homGate_eq` and `DAGGate.eval_eq`. For `∧` this is the bound. For `¬`, subtract from
`encrypts_gadget` (`Encrypts.sub`, noise `0 + ·`), the message being `1 − c.toNat = (!c).toNat`
by cases on `c`. For `∨`, the complements `G − C` encrypt `!b` with noise `0 + β`, their
conjunction is complemented once more, and `List.any_eq_not_all_not` (De Morgan) identifies the
message. -/
theorem homGate_encrypts (g : DAGGate) (hfan : g.args.length ≤ 2) (vals : List Bool)
    (cts : List (Ciphertext P)) (β : ℕ)
    (hargs : ∀ a ∈ g.args, Encrypts P t ((vals.getD a false).toNat : ℤ) β (cts.getD a 0)) :
    Encrypts P t ((g.eval vals).toNat : ℤ) ((P.columns + 1) * β) (homGate P g cts) := by
  -- The argument encryptions, as the hypothesis of `homAnd_encrypts`.
  have hall : List.Forall₂ (fun b C => Encrypts P t (b.toNat : ℤ) β C)
      (g.args.map fun a => vals.getD a false) (g.args.map fun a => cts.getD a 0) := by
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
    exact hargs
  -- A conjunction of at most two arguments has noise at most `(N+1)·β`.
  have hlen : ((g.args.length - 1) * P.columns + 1) * β ≤ (P.columns + 1) * β := by
    refine Nat.mul_le_mul_right β ?_
    have h1 : (g.args.length - 1) * P.columns ≤ 1 * P.columns :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have hand := homAnd_encrypts P hall
  rw [List.all_map, Function.id_comp, List.length_map] at hand
  rw [homGate_eq, DAGGate.eval_eq]
  rcases g with ⟨kind, args⟩
  cases kind with
  | and =>
    exact Encrypts.mono P hand hlen
  | or =>
    -- De Morgan: complement each argument (`G − C`, noise `0 + β`), conjoin, complement.
    have hneg : List.Forall₂ (fun b C => Encrypts P t (b.toNat : ℤ) β C)
        (args.map fun a => !vals.getD a false)
        ((args.map fun a => cts.getD a 0).map fun C => gadget P - C) := by
      rw [List.map_map, List.forall₂_map_left_iff, List.forall₂_map_right_iff,
        List.forall₂_same]
      intro a ha
      have h := Encrypts.sub P (encrypts_gadget P) (hargs a ha)
      rw [zero_add] at h
      have hm : ((!vals.getD a false).toNat : ℤ) = 1 - ((vals.getD a false).toNat : ℤ) := by
        cases vals.getD a false <;> rfl
      rw [hm]
      exact h
    have hor := Encrypts.sub P (encrypts_gadget P) (homAnd_encrypts P hneg)
    rw [List.all_map, Function.id_comp, zero_add, List.length_map, List.length_map] at hor
    have hm : ((args.any fun a => vals.getD a false).toNat : ℤ) =
        1 - ((args.all fun a => !vals.getD a false).toNat : ℤ) := by
      rw [List.any_eq_not_all_not]
      cases args.all (fun a => !vals.getD a false) <;> rfl
    rw [homOr_eq, hm]
    exact Encrypts.mono P hor hlen
  | not =>
    -- `¬`: subtract the conjunction from the gadget (noise `0 + ·`).
    have hnot := Encrypts.sub P (encrypts_gadget P) hand
    rw [zero_add] at hnot
    have hm : ((!(args.all fun a => vals.getD a false)).toNat : ℤ) =
        1 - ((args.all fun a => vals.getD a false).toNat : ℤ) := by
      cases args.all (fun a => vals.getD a false) <;> rfl
    rw [homNot_eq, hm]
    exact Encrypts.mono P hnot hlen

/-- **Depth-indexed noise growth.** For a circuit of fan-in at most two, if every input
ciphertext encrypts its input bit with noise at most `β`, then the output ciphertext
`eval P Cc cts` encrypts the circuit's output with noise at most `(N+1)^{depth}·β` [GSW13,
Section 3.3, "the final ciphertext's error will be bounded by `(N + 1)^L · B`"]. The proof
establishes the stronger invariant `(N+1)^{depthAt v}·β` at every vertex `v` as an intermediate
step.

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
  -- Step 1: the per-vertex invariant `(N+1)^{depthAt v}·β`, by `runWith_rel`.
  have key := runWith_rel DAGGate.eval (homGate P)
    (fun v b C => Encrypts P t (b.toNat : ℤ) ((P.columns + 1) ^ Cc.depthAt v * β) C)
    false 0 Cc.gates (List.ofFn x) (List.ofFn cts) (by rw [List.length_ofFn, List.length_ofFn])
    (by
      -- Input vertices have depth `0` and hold the input encryptions.
      intro v hv
      rw [List.length_ofFn] at hv
      rw [List.getD_eq_getElem _ _ (by rwa [List.length_ofFn]),
        List.getD_eq_getElem _ _ (by rwa [List.length_ofFn]), List.getElem_ofFn,
        List.getElem_ofFn, Cc.depthAt_input hv, pow_zero, one_mul]
      exact hin ⟨v, hv⟩)
    (by
      intro i hi a ha
      rw [List.length_ofFn]
      exact Cc.args_lt i hi a ha)
    (by
      -- Gate vertices: arguments are one level shallower; one gate multiplies by `N+1`.
      intro i hi vA vB _ _ hargs
      rw [List.length_ofFn, Cc.depthAt_gate hi]
      have hd : 1 ≤ Cc.gates[i].depth Cc.depths := by
        rw [DAGGate.depth_eq]
        omega
      have hargs' : ∀ a ∈ Cc.gates[i].args, Encrypts P t ((vA.getD a false).toNat : ℤ)
          ((P.columns + 1) ^ (Cc.gates[i].depth Cc.depths - 1) * β) (vB.getD a 0) := by
        intro a ha
        refine Encrypts.mono P (hargs a ha) (Nat.mul_le_mul_right β ?_)
        refine Nat.pow_le_pow_right (Nat.succ_pos _) ?_
        have := DAGGate.getD_lt_depth Cc.gates[i] Cc.depths ha
        rw [Cc.depthAt_eq a]
        omega
      have hg := homGate_encrypts P Cc.gates[i] (hfan _ (List.getElem_mem hi)) vA vB _ hargs'
      rwa [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hd] at hg)
  -- Step 2: read the in-range output vertex on both sides.
  have hout := key Cc.output (by rw [List.length_ofFn]; exact Cc.output_lt)
  rw [Cc.eval_eq, Cc.values_eq, Cc.depth_eq, eval_eq P Cc cts, evalValues_eq P Cc cts]
  exact hout

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
  have hin : ∀ i, Encrypts P (secretVector P (Regev.keygen P.lwe χ rg).2) ((x i).toNat : ℤ)
      (P.lwe.samples * B) (encrypt P (Regev.keygen P.lwe χ rg).1 (x i) (R i)) :=
    fun i => encrypts_keygen_encrypt P χ rg B hχ (x i) (R i)
  have hev := eval_encrypts P Cc hfan x _ _ hin
  refine decrypt_of_encrypts P _ _ _ _
    (Encrypts.mono P hev (Nat.mul_le_mul_right _ ?_)) hsep
  exact Nat.pow_le_pow_right (Nat.succ_pos _) hdepth

end Correctness

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

## ===== TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Security.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Scheme
import TCSlib.Cryptography.Hashing.SIS.Columns
import TCSlib.Cryptography.LWE.Experiments
import TCSlib.Cryptography.Pseudorandom.Indistinguishability
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

**Proof sketch.** As `Regev.real_uniformKey_advantage`, with the reassociation of the
independent key, coin-matrix and distinguisher seeds done by `acceptProb_bind`: the reduction
is `D` after the coin-using map `(pk, R) ↦ view P μ pk R` (`reduction_eq`), so on `LWE.sample`
and on a uniform key it accepts exactly as `D` accepts `realView` and `uniformKeyView`
(`realView_eq`, `uniformKeyView_eq`). Then read `LWE.decisionAdvantage_eq` and `distAdv_def`. -/
theorem real_uniformKey_advantage {ρ : Type*} [Fintype ρ] [Nonempty ρ]
    (P : Parameters) (χ : LWE.Noise) (μ : Bool)
    (D : ((Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus)) × Ciphertext P) → ρ → Bool) :
    distAdv (realView P χ μ) (uniformKeyView P μ) D =
      LWE.decisionAdvantage P.lwe χ (reduction P μ D) := by
  have hred : reduction P μ D = fun pk c => D (view P μ pk c.1) c.2 := by
    funext pk c
    exact reduction_eq P μ D pk c
  have hreal : acceptProb (LWE.sample P.lwe χ) (reduction P μ D) =
      acceptProb (realView P χ μ) D := by
    rw [hred, acceptProb_bind]
    exact congrArg (fun X => acceptProb X D) (funext fun r => (realView_eq P χ μ r).symm)
  have hkey : acceptProb (id : (Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension)
      (ZMod P.lwe.modulus) × (Fin P.lwe.samples → ZMod P.lwe.modulus)) → _) (reduction P μ D) =
      acceptProb (uniformKeyView P μ) D := by
    rw [hred, acceptProb_bind]
    exact congrArg (fun X => acceptProb X D) (funext fun r => (uniformKeyView_eq P μ r).symm)
  rw [LWE.decisionAdvantage_eq, distAdv_def, distAdv_def, hreal, hkey]

/-- **Statistical hybrid.** Under a uniform key the view is within `N · ε_LHL` of a fully
uniform key-and-ciphertext pair, where `ε_LHL = ½·√(q^{n+1}/2^m)` is the existing
`Regev.extractionError` [GSW13, Section 3.2, "`R · A` is statistically uniform by the
leftover hash lemma"; Pei16, Section 6.1.3].

**Proof sketch.** As `Regev.uniformKey_uniform_advantage_le`. Relabel the key by the
bijection `Regev.augmented_bijective`, which keeps the whole public key. The ciphertext is
`hashColumns (columnHashParameters P) N Ā R + μG` (`encrypt_eq`, `hashColumns_eq_mul`,
`lift_apply`); translation by `μG` (`Equiv.addRight`) is a bijection of the ciphertext space, so
after relabelling both samplers (`acceptProb_comp_equiv`) the gap is that of `(Ā, ĀR)` versus
`(Ā, U)` for the test that undoes both relabellings before running `D`. Apply
`distAdv_hashColumns_uniform_le` to that test and rewrite its bound with the
`columnHashParameters` readers and `Regev.extractionError_eq`. -/
theorem uniformKey_uniform_advantage_le {ρ : Type*} [Fintype ρ] [Nonempty ρ]
    (P : Parameters) (μ : Bool)
    (D : ((Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus)) × Ciphertext P) → ρ → Bool) :
    distAdv (uniformKeyView P μ)
      (id : ((Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
        (Fin P.lwe.samples → ZMod P.lwe.modulus)) × Ciphertext P) → _) D ≤
      P.columns * Regev.extractionError P.lwe := by
  -- Step 1: the key relabelling `pk ↦ Ā`, the ciphertext translation by `μG`, and the test.
  let Key := Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
    (Fin P.lwe.samples → ZMod P.lwe.modulus)
  let AugKey := Matrix (Fin (P.lwe.dimension + 1)) (Fin P.lwe.samples) (ZMod P.lwe.modulus)
  let Coins := Matrix (Fin P.lwe.samples) (Fin P.columns) Bool
  let keyEquiv : Key ≃ AugKey :=
    Equiv.ofBijective (Regev.augmented P.lwe) (Regev.augmented_bijective P.lwe)
  let shift : Ciphertext P := (μ.toNat : ZMod P.lwe.modulus) • gadget P
  let unpack : AugKey × Ciphertext P ≃ Key × Ciphertext P :=
    keyEquiv.symm.prodCongr (Equiv.addRight shift)
  let keySeeds : Key × Coins ≃ AugKey × Coins := keyEquiv.prodCongr (Equiv.refl Coins)
  let sampleHash (r : AugKey × Coins) : AugKey × Ciphertext P :=
    (r.1, Hashing.SIS.hashColumns (columnHashParameters P) P.columns r.1 r.2)
  let test (v : AugKey × Ciphertext P) (coins : ρ) : Bool := D (unpack v) coins
  -- Step 2: the ciphertext is the column hash of the augmented key, translated by `μG`.
  have hsampler : uniformKeyView P μ = fun r => unpack (sampleHash (keySeeds r)) := by
    funext r
    have hlift : (Matrix.of fun c j => ((r.2 c j).toNat : ZMod P.lwe.modulus)) = lift P r.2 := by
      ext c j
      rw [Matrix.of_apply, lift_apply]
    have hhash : Hashing.SIS.hashColumns (columnHashParameters P) P.columns (keyEquiv r.1) r.2 =
        Regev.augmented P.lwe r.1 * lift P r.2 := by
      rw [Hashing.SIS.hashColumns_eq_mul, ← hlift]
      rfl
    rw [uniformKeyView_eq, view_eq, encrypt_eq]
    refine Prod.ext (keyEquiv.symm_apply_apply r.1).symm ?_
    exact (congrArg (· + shift) hhash).symm
  -- Step 3: relabel both samplers; the gap becomes that of `(Ā, ĀR)` versus `(Ā, U)`.
  have hreal : acceptProb (uniformKeyView P μ) D = acceptProb sampleHash test := by
    rw [hsampler]
    simpa only [acceptProb_def] using
      acceptProb_comp_equiv keySeeds (fun r => unpack (sampleHash r)) D
  have hideal : acceptProb (id : Key × Ciphertext P → Key × Ciphertext P) D =
      acceptProb (id : AugKey × Ciphertext P → AugKey × Ciphertext P) test := by
    simpa only [acceptProb_def, id_eq] using
      (acceptProb_comp_equiv unpack (id : Key × Ciphertext P → Key × Ciphertext P) D).symm
  -- Step 4: the column hybrid, its bound read through the `columnHashParameters` readers.
  have hbound := Hashing.SIS.distAdv_hashColumns_uniform_le (columnHashParameters P) P.columns test
  rw [distAdv_def] at hbound ⊢
  rw [hreal, hideal, Regev.extractionError_eq]
  simpa only [columnHashParameters_modulus, columnHashParameters_dimension,
    columnHashParameters_columns] using hbound

/-- **Concrete IND-CPA bound for public-key GSW** [GSW13, Section 3.2 and Lemma 1; Pei16,
Section 6.1.3]. The views of two fixed bits differ by at most two DLWE advantages plus
`2·N·ε_LHL`.

**Proof sketch.** Insert both uniform-key views and the common uniform view; the triangle
inequality (`abs_sub_le`, three times) gives the two exact DLWE terms
(`real_uniformKey_advantage`) and two statistical terms (`uniformKey_uniform_advantage_le`), as
in `Regev.distAdv_encrypt_le`; `linarith` adds them up. -/
theorem distAdv_encrypt_le {ρ : Type*} [Fintype ρ] [Nonempty ρ]
    (P : Parameters) (χ : LWE.Noise) (μ₀ μ₁ : Bool)
    (D : ((Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus)) × Ciphertext P) → ρ → Bool) :
    distAdv (realView P χ μ₀) (realView P χ μ₁) D ≤
      LWE.decisionAdvantage P.lwe χ (reduction P μ₀ D) +
      LWE.decisionAdvantage P.lwe χ (reduction P μ₁ D) +
      2 * (P.columns * Regev.extractionError P.lwe) := by
  let View := (Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
    (Fin P.lwe.samples → ZMod P.lwe.modulus)) × Ciphertext P
  let ideal : View → View := id
  -- The two exact DLWE terms and the two statistical terms.
  have hkey₀ := real_uniformKey_advantage P χ μ₀ D
  have hkey₁ := real_uniformKey_advantage P χ μ₁ D
  have hstat₀ : distAdv (uniformKeyView P μ₀) ideal D ≤
      P.columns * Regev.extractionError P.lwe :=
    uniformKey_uniform_advantage_le P μ₀ D
  have hstat₁ : distAdv (uniformKeyView P μ₁) ideal D ≤
      P.columns * Regev.extractionError P.lwe :=
    uniformKey_uniform_advantage_le P μ₁ D
  -- The chain `real μ₀ → uniform-key μ₀ → uniform → uniform-key μ₁ → real μ₁`.
  have htriangle₀ := abs_sub_le (acceptProb (realView P χ μ₀) D)
    (acceptProb (uniformKeyView P μ₀) D) (acceptProb (realView P χ μ₁) D)
  have htriangle₁ := abs_sub_le (acceptProb (uniformKeyView P μ₀) D)
    (acceptProb ideal D) (acceptProb (realView P χ μ₁) D)
  have htriangle₂ := abs_sub_le (acceptProb ideal D)
    (acceptProb (uniformKeyView P μ₁) D) (acceptProb (realView P χ μ₁) D)
  rw [abs_sub_comm (acceptProb ideal D) (acceptProb (uniformKeyView P μ₁) D),
    abs_sub_comm (acceptProb (uniformKeyView P μ₁) D) (acceptProb (realView P χ μ₁) D)]
    at htriangle₂
  rw [distAdv_def] at hkey₀ hkey₁ hstat₀ hstat₁ ⊢
  linarith only [hkey₀, hkey₁, hstat₀, hstat₁, htriangle₀, htriangle₁, htriangle₂]

/-- With residue width `w` (`q ≤ 2^w`) and `m ≥ (n+1)·w + 2κ` rows, the statistical term is at
most `N · 2^{−κ}` [GSW13, Section 3.2, "it suffices to take `m > 2n log q`", explicit
repository budget].

**Proof sketch.** `distAdv_encrypt_le` and `Regev.two_extractionError_le`, multiplying the
latter by `N ≥ 0` (`mul_le_mul_of_nonneg_left`). -/
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
  have h := distAdv_encrypt_le P χ μ₀ μ₁ D
  have hw := Regev.two_extractionError_le P.lwe w κ hq hm
  have hN : 2 * ((P.columns : ℝ) * Regev.extractionError P.lwe) ≤
      P.columns * ((2 : ℝ)⁻¹) ^ κ := by
    rw [mul_left_comm]
    exact mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg _)
  linarith only [h, hN]

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

## ===== TCSlib/Cryptography/Hashing/SIS/Columns.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Hashing.SIS.Universality
import TCSlib.Cryptography.Foundations.Probability
import TCSlib.Cryptography.Pseudorandom.Indistinguishability

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

**Proof sketch.** Entrywise: by `hashColumns_apply`, `hash_eq` and `Matrix.mul_apply'` both
sides are the same dot product of row `i` of `A` with the lifted column `j` of `R`. -/
theorem hashColumns_eq_mul (P : Parameters) (N : ℕ)
    (A : Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus))
    (R : Matrix (Fin P.columns) (Fin N) Bool) :
    hashColumns P N A R = A * Matrix.of fun c j => ((R c j).toNat : ZMod P.modulus) := by
  ext i j
  rw [hashColumns_apply, hash_eq, Matrix.mul_apply']
  rfl

/-- **Column hybrid for leftover hashing** [GSW13, Section 3.2, Lemma 1, statistical half;
Pei16, Section 6.1.3]: any independently randomized test distinguishes `(A, A R)` from a
uniform `(A, U)`, for uniform `A` and uniform binary `R` with `N` columns, with advantage at
most `N` times the single-column error `½·√(q^{dimension}/2^{columns})`.

**Proof sketch.** Hybrid `H_k`, on seeds `(A, (x, u))` with binary columns `x j` and uniform
columns `u j`: column `j` of the second component is `u j` for `j < k` and `hash A (x j)`
otherwise, all under the same `A`. The `k`-th test plants its challenge column at `k`,
simulates the other columns from coins `(x, u)` carried beside `D`'s own coins (a product of
finite nonempty types), and runs `D`. By `acceptProb_bind`, a seed relabelling
(`acceptProb_comp_equiv`) and `acceptProb_update`, it accepts `(A, hash A r)` exactly as `D`
accepts `H_k`, and a uniform `(A, y)` exactly as `D` accepts `H_{k+1}`. `H_0` is the real
sampler and `H_N` the ideal one after transposing the seeds and dropping the unused columns
(`acceptProb_comp_equiv`, `acceptProb_fst`). `abs_sub_le_sum_hybrids` bounds the end-to-end
gap by the `N` neighbouring gaps, each at most the single-column error by
`distAdv_hash_uniform_le`. At `N = 0` the sum is empty. -/
theorem distAdv_hashColumns_uniform_le {ρ : Type*} [Fintype ρ] [Nonempty ρ]
    (P : Parameters) (N : ℕ)
    (D : (Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus) ×
      Matrix (Fin P.dimension) (Fin N) (ZMod P.modulus)) → ρ → Bool) :
    distAdv (fun r : Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus) ×
        Matrix (Fin P.columns) (Fin N) Bool => (r.1, hashColumns P N r.1 r.2))
      (id : (Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus) ×
        Matrix (Fin P.dimension) (Fin N) (ZMod P.modulus)) → _) D ≤
      N * ((1 / 2) * Real.sqrt ((P.modulus : ℝ) ^ P.dimension / (2 : ℝ) ^ P.columns)) := by
  classical
  let Key := Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus)
  let In := Fin P.columns → Bool
  let Out := Fin P.dimension → ZMod P.modulus
  let Mat := Matrix (Fin P.dimension) (Fin N) (ZMod P.modulus)
  let Cols := (Fin N → In) × (Fin N → Out)
  -- Hybrid `k`: columns `j < k` are uniform, the others hash binary columns under `A`.
  let hyb (k : ℕ) (s : Key × Cols) : Key × Mat :=
    (s.1, Matrix.of fun i j => if (j : ℕ) < k then s.2.2 j i else hash P s.1 (s.2.1 j) i)
  -- The `k`-th test plants its challenge at column `k` and simulates the other columns.
  let plant (k : ℕ) (z : Key × Out) (c : Cols) : Key × Mat :=
    (z.1, Matrix.of fun i j => if (j : ℕ) < k then c.2 j i else if (j : ℕ) = k then z.2 i
      else hash P z.1 (c.1 j) i)
  let test (k : ℕ) (z : Key × Out) (c : Cols × ρ) : Bool := D (plant k z c.1) c.2
  -- Step 1: on a real challenge, the `k`-th test runs `D` on hybrid `k`.
  have hleft (k : ℕ) (hk : k < N) :
      acceptProb (fun r : Key × In => (r.1, hash P r.1 r.2)) (test k) =
        acceptProb (hyb k) D := by
    let e : (Key × In) × Cols ≃ In × ((Fin N → In) × (Key × (Fin N → Out))) :=
      ⟨fun w => (w.1.2, (w.2.1, (w.1.1, w.2.2))), fun v => ((v.2.2.1, v.1), (v.2.1, v.2.2.2)),
        fun _ => rfl, fun _ => rfl⟩
    let e' : (Fin N → In) × (Key × (Fin N → Out)) ≃ Key × Cols :=
      ⟨fun v => (v.2.1, (v.1, v.2.2)), fun s => (s.2.1, (s.1, s.2.2)), fun _ => rfl, fun _ => rfl⟩
    refine (acceptProb_bind _ (plant k) D).trans (Eq.trans ?_
      ((acceptProb_comp_equiv e
        (fun w => hyb k (e' (Function.update w.2.1 ⟨k, hk⟩ w.1, w.2.2))) D).trans
      ((acceptProb_update (ρ := ρ) (⟨k, hk⟩ : Fin N) (fun c v => hyb k (e' (c, v))) D).trans
        (acceptProb_comp_equiv e' (hyb k) D))))
    refine congrArg (fun X => acceptProb X D) ?_
    funext w
    refine Prod.ext rfl ?_
    ext i j
    simp only [plant, hyb, e, e', Equiv.coe_fn_mk, Matrix.of_apply]
    by_cases hj : (j : ℕ) = k
    · obtain rfl : j = ⟨k, hk⟩ := Fin.ext hj
      simp only [lt_irrefl, if_false, if_true, Function.update_self]
    · have hne : j ≠ ⟨k, hk⟩ := fun h => hj (congrArg Fin.val h)
      simp only [hj, if_false, Function.update_of_ne hne]
  -- Step 2: on a uniform challenge, the `k`-th test runs `D` on hybrid `k + 1`.
  have hright (k : ℕ) (hk : k < N) :
      acceptProb (id : Key × Out → Key × Out) (test k) = acceptProb (hyb (k + 1)) D := by
    let e : (Key × Out) × Cols ≃ Out × ((Fin N → Out) × (Key × (Fin N → In))) :=
      ⟨fun w => (w.1.2, (w.2.2, (w.1.1, w.2.1))), fun v => ((v.2.2.1, v.1), (v.2.2.2, v.2.1)),
        fun _ => rfl, fun _ => rfl⟩
    let e' : (Fin N → Out) × (Key × (Fin N → In)) ≃ Key × Cols :=
      ⟨fun v => (v.2.1, (v.2.2, v.1)), fun s => (s.2.2, (s.1, s.2.1)), fun _ => rfl, fun _ => rfl⟩
    refine (acceptProb_bind _ (plant k) D).trans (Eq.trans ?_
      ((acceptProb_comp_equiv e
        (fun w => hyb (k + 1) (e' (Function.update w.2.1 ⟨k, hk⟩ w.1, w.2.2))) D).trans
      ((acceptProb_update (ρ := ρ) (⟨k, hk⟩ : Fin N) (fun c v => hyb (k + 1) (e' (c, v))) D).trans
        (acceptProb_comp_equiv e' (hyb (k + 1)) D))))
    refine congrArg (fun X => acceptProb X D) ?_
    funext w
    refine Prod.ext rfl ?_
    ext i j
    simp only [plant, hyb, e, e', Equiv.coe_fn_mk, Matrix.of_apply, id_eq]
    rcases lt_trichotomy (j : ℕ) k with h | h | h
    · have hne : j ≠ ⟨k, hk⟩ := fun h' => h.ne (congrArg Fin.val h')
      simp only [h, Nat.lt_succ_of_lt h, if_true, Function.update_of_ne hne]
    · obtain rfl : j = ⟨k, hk⟩ := Fin.ext h
      simp only [lt_irrefl, Nat.lt_succ_self, if_false, if_true, Function.update_self]
    · have hne : j ≠ ⟨k, hk⟩ := fun h' => h.ne' (congrArg Fin.val h')
      simp only [not_lt.mpr h.le, not_lt.mpr (Nat.succ_le_of_lt h), h.ne', if_false]
  -- Step 3: hybrid `0` is the real sampler and hybrid `N` the ideal one, after relabelling.
  have hzero : acceptProb (fun r : Key × Matrix (Fin P.columns) (Fin N) Bool =>
      (r.1, hashColumns P N r.1 r.2)) D = acceptProb (hyb 0) D := by
    let e : Key × Cols ≃ (Key × Matrix (Fin P.columns) (Fin N) Bool) × (Fin N → Out) :=
      ⟨fun s => ((s.1, fun c j => s.2.1 j c), s.2.2), fun t => (t.1.1, (fun j c => t.1.2 c j, t.2)),
        fun _ => rfl, fun _ => rfl⟩
    refine (acceptProb_fst (τ := Fin N → Out) _ D).symm.trans (Eq.trans
      (acceptProb_comp_equiv e (fun t => (t.1.1, hashColumns P N t.1.1 t.1.2)) D).symm ?_)
    refine congrArg (fun X => acceptProb X D) ?_
    funext s
    refine Prod.ext rfl ?_
    ext i j
    simp only [hyb, e, Equiv.coe_fn_mk, Matrix.of_apply, hashColumns_apply, Nat.not_lt_zero,
      if_false]
  have hfull : acceptProb (id : Key × Mat → Key × Mat) D = acceptProb (hyb N) D := by
    let e : Key × Cols ≃ (Key × Mat) × (Fin N → In) :=
      ⟨fun s => ((s.1, Matrix.of fun i j => s.2.2 j i), s.2.1),
        fun t => (t.1.1, (t.2, fun j i => t.1.2 i j)), fun _ => rfl, fun _ => rfl⟩
    refine (acceptProb_fst (τ := Fin N → In) _ D).symm.trans (Eq.trans
      (acceptProb_comp_equiv e (fun t => id t.1) D).symm ?_)
    refine congrArg (fun X => acceptProb X D) ?_
    funext s
    refine Prod.ext rfl ?_
    ext i j
    simp only [hyb, e, Equiv.coe_fn_mk, Matrix.of_apply, id_eq, j.isLt, if_true]
  -- Step 4: telescope the neighbouring gaps and bound each by the single-column lemma.
  have hgap (k : ℕ) (hk : k ∈ Finset.range N) :
      |acceptProb (hyb k) D - acceptProb (hyb (k + 1)) D| ≤
        (1 / 2) * Real.sqrt ((P.modulus : ℝ) ^ P.dimension / (2 : ℝ) ^ P.columns) := by
    have h := distAdv_hash_uniform_le P (test k)
    rwa [distAdv_def, hleft k (Finset.mem_range.1 hk), hright k (Finset.mem_range.1 hk)] at h
  rw [distAdv_def, hzero, hfull]
  refine (abs_sub_le_sum_hybrids (fun k => acceptProb (hyb k) D) N).trans
    ((Finset.sum_le_sum hgap).trans_eq ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end TCSlib.Cryptography.Hashing.SIS
