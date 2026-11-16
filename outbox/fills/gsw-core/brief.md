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
