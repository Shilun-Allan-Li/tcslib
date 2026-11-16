# Sub-agent B WORKLOG (gsw-core, units F3 Scheme and F7 Symmetric)

- 2026-11-16T08:08Z Read SUBAGENT-RULES.md, brief.md, policy.md, Scheme.lean, Symmetric.lean,
  Gadget/Noise statements, foreign readers (LWE Basic/Noise/BitEncoding/Experiments, Regev
  Basic/Experiments, Symmetric Regev Experiments, Foundations Experiments/Probability, Lossy Gadget).
- 08:09Z probe-001 (probes/B_names1): Mathlib names. No `Matrix.vecMul_apply`/`vecMul_submatrix`;
  use `change` to the sum form (Mathlib defs may reduce in change/show). `add_dotProduct`,
  `smul_dotProduct`, `Matrix.dotProduct_mulVec`, `Fin.init_def`, `Matrix.submatrix_apply` exist.
- 08:09-08:10Z scheme-002/003: `vecMul_secretVector_augmented`, `encrypts_encrypt`,
  `encrypts_keygen_encrypt` proved (0 errors).
- 08:11Z written (in Scheme.lean): private helpers `halfVector_eq_zero_of_ne_last`,
  `decrypt_eq_decode_errorSum` and the proof of `decrypt_of_encrypts`. Its check (scheme-004)
  has been waiting on the host-wide Lean lock since ~08:12Z (lead's seal runs hold it); no
  result yet. Drafts for `decrypt_of_encrypts_dyadic` (indicator vector via
  `Lossy.digits_injective` + `digits_decomposeVec` + `digits_val`), `decrypt_keygen_encrypt`,
  `encrypts_symEncrypt` and `distAdv_symEncrypt_le` (Equiv = ofBijective augmented ∘ rowEquiv
  reindexing ∘ addRight μG, then `acceptProb_comp_equiv`) are prepared in scratch and will be
  applied/checked as soon as the lock frees. No blocker known yet; no route has failed.
- 08:42Z Found the cause of the stall: the 08:11 patch command began with a stray `cat > fix.py`
  that waited on stdin, so the Python patch never ran and scheme-004.log is a stale run of the
  3-target file (its content predates the patch). Re-applied the decryption patch from a script
  file. scheme-005: 2 errors in the dyadic `hsum` step (beta-redex `(fun i => decide ..) i₀`);
  fixed with `dsimp only`. scheme-006: 0 errors, 0 sorry warnings: all 6 Scheme targets.
- 08:42Z symmetric-007: both Symmetric targets (helper `exists_equiv_symEncrypt`) 0 errors first try.
- 08:43Z Rewrote the `**Proof sketch.**` paragraphs of all 8 targets to the delivered proofs;
  widths ≤ 100; scheme-008, symmetric-009: 0 errors, 0 sorry warnings.
- 08:43Z axioms-010 (probes/B_axioms.lean): 5 targets standard axioms only; decrypt_of_encrypts,
  decrypt_keygen_encrypt reach sorryAx only via F1 `errorSum_decomposeVec_le`,
  `gadget_mulVec_decomposeVec`; decrypt_of_encrypts_dyadic only via F1 `digits_decomposeVec`,
  `gadget_mulVec_decomposeVec` (dependency trace in the same log).
- 08:44Z Seals (4 variants) of Scheme and Symmetric: all exit=0 errors=0. Explicit-unfold scan of
  simp/rw/dsimp selectors: no foreign or Mathlib definition named; no unfold/delta.
