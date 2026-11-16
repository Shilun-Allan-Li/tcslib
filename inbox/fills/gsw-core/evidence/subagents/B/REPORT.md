# Sub-agent B report (gsw-core, units F3 and F7)

Worktree `/home/user/gsw-B`. Owned files edited only:
`TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Scheme.lean` (215 → 365 lines) and
`.../GSW/Symmetric.lean` (111 → 186 lines). Final copies and SHA-256 under `final/`:
Scheme `d824b5a0…c433`, Symmetric `9a975a82…7006`. No git operation, no other file touched.

## Target status (all 8 proved)

| Target | Status | Axioms (with F1/F2 still sorried in this worktree) |
|---|---|---|
| `vecMul_secretVector_augmented` | proved | standard only |
| `encrypts_encrypt` | proved | standard only |
| `encrypts_keygen_encrypt` | proved | standard only |
| `decrypt_of_encrypts` | proved | sorryAx only via F1 `errorSum_decomposeVec_le`, `gadget_mulVec_decomposeVec` |
| `decrypt_of_encrypts_dyadic` | proved | sorryAx only via F1 `digits_decomposeVec`, `gadget_mulVec_decomposeVec` |
| `decrypt_keygen_encrypt` | proved | sorryAx only via F1 `errorSum_decomposeVec_le`, `gadget_mulVec_decomposeVec` |
| `encrypts_symEncrypt` | proved | standard only |
| `distAdv_symEncrypt_le` | proved | standard only |

Standard = `propext`, `Classical.choice`, `Quot.sound`. Evidence: `logs/axioms-010.log`
(`#print axioms` plus a dependency trace listing every sorried constant in the closure;
probe source `probes/B_axioms.lean`). No F2 (Noise) target is used; `Encrypts` is read only via
`encrypts_iff`.

Last checks: `logs/scheme-008.log` and `logs/symmetric-009.log`: exit 0, 0 errors (both forms),
0 sorry warnings. Note: `logs/scheme-004.log` is a stale run (my patch command hung on a stray
`cat` before writing, see WORKLOG); `scheme-005.log` has the 2 errors fixed in `scheme-006`.

## Seals (Rule 10)

`seal-Scheme/` and `seal-Symmetric/` (sources, linemaps, raw logs, `manifest.json`,
`results.jsonl`, `run.log`): all four variants (A/B × strict/coe) exit 0, errors 0, for both
files (canonical coe-A: 0). Explicit-unfold scan of every `simp`/`rw`/`dsimp` selector: no
foreign TCSlib definition and no core/Mathlib definition named; no `unfold`/`delta`. Mathlib
definitions (`vecMul`, `dotProduct`, `submatrix`, `Fin.init`) are reached only via `change`
or by their lemmas (`Fin.init_def`, `Matrix.submatrix_apply`, `Matrix.dotProduct_mulVec`, …).

## Sketch edits

Each target's `**Proof sketch.**` paragraph was rewritten to the delivered proof (statement
prose unchanged; checked by diff against `/home/user/gsw-base`: only sketch lines and `sorry`
lines removed). Headers byte-identical; nothing deleted; no import added.

## New auxiliary declarations (all `private`, glue, no source tag)

- `Scheme.lean`: `halfVector_eq_zero_of_ne_last (P) (j) (hj : j ≠ Fin.last _) :
  halfVector P j = 0`.
- `Scheme.lean`: `decrypt_eq_decode_errorSum (P s b β C) (h : Encrypts P (secretVector P s)
  b.toNat β C) : ∃ e, (∀ j, |e j| ≤ β) ∧ decrypt P s C = decode (codepoint b +
  ↑(∑ i, e i * (decomposeVec P (halfVector P) i).toNat))` (has its own sketch).
- `Symmetric.lean`: `exists_equiv_symEncrypt (P hN μ) : ∃ E : PK ≃ (Fin k → Ciphertext P),
  ∀ c, E c = symEncrypt P hN c μ` (has its own sketch).

No public declaration, so no `## Main results` change. Name-clash grep: none of the three names
occurs anywhere else in `TCSlib/`.

## Overlap and reuse

- `decrypt_eq_decode_errorSum` — nearest relative `Regev.encrypt_residual`
  (`Cryptography/Encryption/PublicKey/Regev/Basic.lean:105`): same "residual = codepoint +
  integer error sum" shape for Regev ciphertexts. Not reusable: the GSW decryption column is not
  a `Regev.encrypt` output (its residual comes from the GSW invariant and `G·G⁻¹(w) = w`).
  `LWE.BitEncoding.decode_codepoint_add`, `errorSum_decomposeVec_le`,
  `gadget_mulVec_decomposeVec` are reused, not re-proved.
- `exists_equiv_symEncrypt` — relatives: the inline translation equivalence in
  `Symmetric.Regev.acceptProb_uniform_shift` (`Encryption/Symmetric/Regev/Experiments.lean:77`)
  and the inline `keyEquiv := Equiv.ofBijective (augmented P) (augmented_bijective P)`
  (`Encryption/PublicKey/Regev/Experiments.lean:260`). Both are inline `let`s inside proofs, so
  not reusable; mine composes `Equiv.ofBijective _ Regev.augmented_bijective` (reused), a column
  reindexing through `rowEquiv` (new, no relative found: Mathlib `Matrix.reindex` /
  `Equiv.curry` do not give the `Fin k`-block shape directly), and Mathlib `Equiv.addRight`.
- `halfVector_eq_zero_of_ne_last` — no relative (searched `halfVector` in `TCSlib/`).
- Inline `hs` in `encrypts_keygen_encrypt` — same `Prod.ext (sample_fst) (sample_snd)` as the
  inline `hsample` in `Regev.decrypt_keygen_encrypt` (`Regev/Basic.lean:168`); inline, not
  exported, two lines.
- Inline `hz` in `decrypt_of_encrypts_dyadic` (decomposition of `⌊q/2⌋ e_last` at `q = 2^ℓ`
  is an indicator): proved by reusing `Lossy.digits_injective`, `Lossy.digits_val`,
  `digits_decomposeVec`, `digit_val`; no existing statement of it. Inline `hsum` uses Mathlib
  `Fintype.sum_eq_single`.
- Reused, not restated: `LWE.binaryErrorSum_bound` (fresh noise `m·B`), `Regev.augmented_eq`,
  `Regev.augmented_bijective`, `LWE.noisyValues_apply`, `Regev.decrypt_eq`,
  `codepoint_eq`, `acceptProb_def`, `distAdv_def`, `acceptProb_comp_equiv`,
  `LWE.decisionAdvantage_eq`, `Noise.bounded_iff`, `keygen_fst/snd`, `sample_fst/snd`.

Searches run: `grep -rn` in `TCSlib/` for `halfVector`, `exists_equiv`, `decode_errorSum`,
`sample_eq`, `ofBijective`, `symm_apply` (Encryption), `encrypt_residual`, `digits_injective`,
`blocksEquiv`; Mathlib `#check` probe `probes/B_names1.lean` (`logs/probe-001.log`) for
`vecMul_add/smul/vecMul`, `dotProduct_mulVec`, `add_dotProduct`, `smul_dotProduct`,
`submatrix_apply`, `Fin.init_def`, `Fin.sum_univ_castSucc`, `Fin.snoc_*`, `ZMod.val_natCast`,
`Fintype.sum_eq_single`, `Equiv.ofBijective_apply`, `Equiv.coe_addRight` (no
`Matrix.vecMul_apply`/`Matrix.vecMul_submatrix` at this pin; `change` used instead).

## Scope requests / failed routes / false targets

None. Every route of the brief worked as written.
