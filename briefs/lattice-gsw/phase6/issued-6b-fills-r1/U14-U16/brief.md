# Claude fill · `gsw-6b-u14-u16`: GSW 6b units U14 and U16, bootstrapping and the leveled scheme (G9–G13, G18, L2, L3)

**Unit** `gsw-6b-u14-u16` · **Route** Claude fill, a lead with up to 1 sub-agent · **Base** B6
`bff0567b6c4b6b724c8fd20ff3ef92258eb3fc9d` (tree `845bdc982fd8f79aba755796bb13188922c4655d`) · **Size** 460–740 fill
lines (r3 §H7: U14 280–440, U16 180–300) plus the public helper · **Delivery** `inbox/fills/gsw-6b-u14-u16/` on
`exchange/pass-shelat-ch5-8` · **Local inputs (rule 16)** none.

Read `../COMMON.md` first; it is part of this brief. Then `../dup-sweep.md` §0 and §U14-U16 (binding must-reuse list).

**Why one unit for two plan units** (README Q-6BF-2 A). G10's gate step and L2's gate step are the same fact: a NAND
gate whose argument ciphertexts decrypt under `s` to the argument values is bootstrapped by `bootGate` to an
encryption of the gate's value. Two separate workers would each prove it privately (a cross-file private copy,
COMMON §5.2); one owner states it once, public, in `Bootstrap.lean`, and both proofs use it.

## Targets (frozen statements; prove all seven)

| Row | Declaration (`TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.`) | Line at B6 |
|---|---|---|
| G9 | `encrypts_bootNAND`: for all `C₁, C₂`, `bootNAND P evk C₁ C₂` encrypts `!(dec C₁ && dec C₂)` under `t'` with noise `bootNoise P βk` | `GSW/Bootstrap.lean:235` |
| G10 | `decrypt_fheEval`: pure FHE, every NAND-form circuit of any depth | `:264` |
| G18 | `decrypt_fheEvalCircuit`: every fan-in-2 circuit through `toNANDForm` | `:282` |
| G12 | `decrypt_keygen_fheEvalCircuit`: honest keys, every circuit | `:322` |
| G13 | `bootNoise_le`: `bootNoise P β ≤ 4^33·N^19·(ℓ + ⌈log₂ N⌉ + 3)^4·(2β)` | `:344` |
| L2 | `encrypts_leveledEval`: layered NAND-form circuits of depth `≤ L`, output under `s_{depth}` | `GSW/Leveled.lean:243` |
| L3 | `decrypt_keygen_leveledEvalCircuit`: honest keys, every fan-in-2 circuit of NAND depth `≤ L` | `:277` |

G11 (`encrypts_evalKey`) and L1 (`encrypts_levelKey`) are proved citations at B6, frozen.

## Owned files and scope

| File | Lines at B6 | Permitted (COMMON §4) |
|---|---|---|
| `TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Bootstrap.lean` | 349 | the five proofs, private helpers, sketches, the admitted-sentence of the module docstring, **and the one public helper `encrypts_bootGate`** (below), inserted after G9 and before G10, with a `## Main results` entry |
| `TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Leveled.lean` | 291 | the two proofs, private helpers, sketches, the admitted-sentence |

**The public helper `encrypts_bootGate`** (README Q-6BF-3 A; the only new public declaration). Proposed statement,
which you may refine with disclosure (*Statement changes*, the helper only):

```lean
theorem encrypts_bootGate (P : Parameters) {t' : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus}
    (s : Secret P) (βk : ℕ) (evk : Fin P.columns → Ciphertext P)
    (hk : ∀ i, Encrypts P t' ((keyBits P s i).toNat : ℤ) βk (evk i))
    {g : DAGGate} (hg : g.IsNAND) (vals : List Bool) (cts : List (Ciphertext P))
    (hargs : ∀ a ∈ g.args, decrypt P s (cts.getD a 0) = vals.getD a false) :
    Encrypts P t' ((g.eval vals).toNat : ℤ) (bootNoise P βk) (bootGate P evk g cts)
```

Docstring: words and formula, "Glue." (no source tag; it is the gate step of [BV14, Thm 2.14]'s two parts, which G10's
and L2's tags already cite), and a `**Proof sketch.**`: the three case readers `bootGate_of_args_eq_nil`/
`_singleton`/`_cons_cons` (`g.args.length ≤ 2` from `DAGGate.isNAND_iff`); G9 on `(G, G)`, `(a, a)` or `(a, b)`; the
padded `G` decrypts to `true` (`encrypts_gadget`, `decrypt_of_encrypts` needs no noise condition at noise `0`, or a
direct reading); `DAGGate.eval_of_isNAND` (N1) matches `!(d₁ && d₂)` with `!(g.args.all …)`. Seal it with its own
liveness pair (COMMON C6).

Frozen: everything else, including Branching (U12) and DecryptFormula (U13), whose targets you cite as frozen
statements, and every definition and case reader in the two owned files.

## Known context

- **G9.** `bootNAND_eq`; G3 (`encrypts_homEvalFormula`, U12) for `nandFormula P C₁ C₂` on `N ≥ 1` inputs
  (`Parameters.neZero_columns`) with fan-in `≤ 2` (G8 `maxFanin_nandFormula_le`, U13); message by G7
  (`nandFormula_eval`, U13); noise by G8 `depth_nandFormula_le`, `Nat.pow_le_pow_right`, `bootNoise_eq`,
  `Encrypts.mono`. No hypothesis on `C₁`, `C₂` (key-switching form).
- **G10.** `runWith_rel` (H19) on `DAGGate.eval` from `List.ofFn x` and `bootGate P evk` from `List.ofFn cts`, with the
  vertex relation "encrypts the value under `t` with noise `βin` (input) or `bootNoise P βk` (gate)"; the gate step is
  `encrypts_bootGate` with `t' = t`, after `decrypt_of_encrypts` with `hβin`/`hboot` on the arguments (earlier
  vertices, `Cc.args_lt`); the output via `Cc.output_lt`, `DAGCircuit.eval_eq`, `values_eq`, `fheEval_eq`. Phase 5's
  `eval_encrypts` (`GSW/Eval.lean:250`) is the pattern (disclose the analogy).
- **G18.** `fheEvalCircuit_eq`; G10 for `Cc.toNANDForm hC` (`toNANDForm_isNANDForm` N4, `toNANDForm_eval` N3).
- **G12.** `Regev.keygen_fst/_snd`, `LWE.sample_fst/_snd` give `(A, A s + e)` with `B`-bounded errors
  (`LWE.Noise.bounded_iff`); inputs by `encrypts_keygen_encrypt`, the evaluation key by G11 (`encrypts_evalKey`);
  `m·B ≤ bootNoise P (m·B)` (`bootNoise_eq`, `N ≥ 1`) so `hsep` gives both conditions; then G18.
- **G13.** `bootNoise_eq`; G8 `decDepth_le` (U13); `4^⌈log₂ y⌉ ≤ 4y²` for `y ≥ 1` from `Nat.pow_pred_clog_lt_self`
  (`y ≥ 2`) and `Nat.clog_one_right` (`y = 1`); `4^22·(4N²)^9·(4X²)^2 = 4^33·N^18·X^4`; constants `c₀ = 33`, `c₁ = 9`,
  `c₂ = 2` are settled and frozen. Search Mathlib for the `4^⌈log₂ y⌉` bound before writing it (e.g. a
  `Nat.pow_clog`-type lemma); if none, a private helper.
- **L2.** `runWith_rel` with the leveled gate function; relation "if `Cc.depthAt v ≤ L`, encrypts the value under
  `s_{depthAt v}` with noise `max βin (bootNoise P βk)`"; inputs at level `0` (`depthAt_input`); a gate at level
  `δ = depthAt v ≥ 1` (`depthAt_gate`, `DAGGate.depth_eq`, `length_runWith`) uses `levelGate_of_lt` and
  `encrypts_bootGate` with `s = s_{δ−1}`, `t' = t_δ`, `hk`; the layered property (`isLayered_iff`) puts every argument
  at level `δ − 1`; gates above `L` are unconstrained and never read. Output level `Cc.depth` (`depth_eq`).
- **L3.** `leveledEvalCircuit_eq`; L1 for `hk` with `βk = m·B`; the literal ciphertexts (`literalCts_castAdd`/
  `_natAdd` with `encrypts_keygen_encrypt`, and `homNot_eq`, `homAnd_singleton`, `encrypts_gadget`, `Encrypts.sub`)
  against `litInput_castAdd`/`_natAdd`, `Fin.addCases`; the layered circuit by `layerNAND_isNANDForm` +
  `toNANDForm_isNANDForm`, `layerNAND_isLayered`, `layerNAND_depth`, `layerNAND_eval` + `toNANDForm_eval` (6a N3–N13,
  proved); then L2 and `decrypt_of_encrypts`.
- **Sizes** (G6B-F07): `Bootstrap.lean` was projected at ≤ 791 lines filled. If it would pass 1,000, that is a scope
  request (a module split), not a reason to compress proofs.
- **Probe history** (G6B-F06): `fheEval` on the padded XOR circuit took over an hour per input; do not plan on
  numeric probes of G10 or L2.

## Axioms (C5)

Allowed `sorryAx` traces, through these frozen targets of other units only:
- U12: `encrypts_homEvalFormula` (G3), and through it `encrypts_homEvalPBP`, `Encrypts.select`;
- U13: `nandFormula_eval`, `depth_nandFormula_le`, `maxFanin_nandFormula_le`, `decDepth_le`, and through them
  `decryptFormula_eval`, `vecMul_secretVector_eq_sum`.

No trace may name a declaration of `Bootstrap.lean` or `Leveled.lean`. `encrypts_bootGate` traces only through G9's
allowed set.

## Unit checks (in addition to COMMON C1–C13)

- **C2 count.** `base-sorries.txt` minus the 7 targets: **35 declarations in 14 modules**.
- **C3.** decls2 on the two files: `Bootstrap.lean` ADDED exactly `encrypts_bootGate`, 0 CHANGED, 0 REMOVED;
  `Leveled.lean` 0/0/0. C4's frozen check allows exactly that insertion and its `## Main results` line.
- **Split.** Lead: `Bootstrap.lean` (the helper first, stated with `sorry` until proved so the sub-agent can start
  L2), the integration, every final check, the delivery. Sub-agent `lev`: `Leveled.lean`. The final has no `sorry`.

## Size

460–740 fill lines plus the helper (about 40–80). Checkpoint 1: the helper and G9, G13 proved and checked; L2 outlined.

**Ready to dispatch once the records pin is filled and Q-6BF-2/Q-6BF-3 are ruled** (README).
