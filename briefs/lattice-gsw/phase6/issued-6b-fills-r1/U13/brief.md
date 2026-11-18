# Claude fill · `gsw-6b-u13`: GSW 6b unit U13, the decryption formula (G5–G8)

**Unit** `gsw-6b-u13` · **Route** Claude fill, one worker · **Base** B6 `bff0567b6c4b6b724c8fd20ff3ef92258eb3fc9d`
(tree `845bdc982fd8f79aba755796bb13188922c4655d`) · **Size** 200–330 fill lines (r3 §H7) · **Delivery**
`inbox/fills/gsw-6b-u13/` on `exchange/pass-shelat-ch5-8` · **Local inputs (rule 16)** none.

Read `../COMMON.md` first; it is part of this brief. Then `../dup-sweep.md` §0 and §U13 (binding must-reuse list).

## Targets (frozen statements; prove all six)

| Row | Declaration (`TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.`) | Line at B6 |
|---|---|---|
| G5 | `vecMul_secretVector_eq_sum`: `t ⬝ᵥ c = ∑ i, (keyBits P s i).toNat · decConstants P C i` | `GSW/DecryptFormula.lean:143` |
| G6 | `decryptFormula_eval`: `(decryptFormula P C).eval (keyBits P s) = decrypt P s C` | `:165` |
| G7 | `nandFormula_eval`: `(nandFormula P C₁ C₂).eval (keyBits P s) = !(decrypt P s C₁ && decrypt P s C₂)` | `:176` |
| G8 | `depth_nandFormula_le`: depth `≤ decDepth P + 1` | `:188` |
| G8 | `maxFanin_nandFormula_le`: fan-in `≤ 2` | `:198` |
| G8 | `decDepth_le`: `decDepth P ≤ 9⌈log₂ N⌉ + 2⌈log₂(ℓ + ⌈log₂ N⌉ + 3)⌉ + 21` | `:211` |

## Owned file and scope

`TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/DecryptFormula.lean` (216 lines at B6), under COMMON §4. **No
public helper.** Frozen: the instance `Parameters.neZero_columns` (its proof is LE-6b3's), every definition and reader,
the 6a formula layer (`FormulaArith/*`, proved), O2 (`LWE/BitEncoding.lean`), phase 5's `Scheme.lean` and
`Gadget.lean`.

## Known context

- **G5.** `keyBits_eq` and `gadget_mulVec_decomposeVec` give `t = G·x` (lifted key bits); `Matrix.dotProduct_mulVec`
  moves `G` across, `decConstants_eq` names `cᵀG`, `dotProduct_comm` fixes the order.
- **G6.** Decryption is `decode` of `⟨t, c⟩` by the owner-side reader `decrypt_eq_decode_dotProduct`
  (`Scheme.lean:162`, ruling Q-C1): **use it, do not re-derive it**. Then G5; the representative
  `(∑ xᵢ·aᵢ.val) mod q` (`ZMod.val_natCast`, `Nat.cast_sum`, `ZMod.natCast_zmod_val`); O2's `decode_iff_mem_Ico`
  turns `decode` into the interval test and F9's `modSumInterval_eval` evaluates the formula to the same test, with
  `aᵢ.val < q` (`ZMod.val_lt`) and `decodeLo ≤ decodeHi ≤ q` (`decodeLo_eq`, `decodeHi_eq`). The frozen G6 sketch
  already names the reader (LE-6b1); refresh it only to describe the delivered proof.
- **G7.** `nandFormula_eq`, `TreeCircuit.neg_eval` (F1), `TreeCircuit.and2_eval` (F3), G6 twice.
- **G8.** `depth_neg`, `depth_and2_le`, `depth_modSumInterval_le` (F10) via `decryptFormula_eq`, `decDepth_eq`;
  `maxFanin_neg`, `maxFanin_and2_le`, `maxFanin_modSumInterval_le`. `decDepth_le` is F10's `modSumDepth_le` at
  `M = N` weakened by `⌈log₂ q⌉ ≤ ℓ` (`P.modulus_le`, `Nat.clog_le_iff_le_pow`, `Nat.clog_mono_right`): about three
  lines (G6B-F05; **disclose the specialization** in *Overlap and reuse*).
- **No term linear in `ℓ`** may enter a depth bound (r3 §H3.3, §H8 item 1); none of these proofs needs one.
- **Probe history** (G6B-F06): the statement job's kernel attempt on G6/G7 stalled; `#eval` covered them. No statement
  was found false.

## Axioms (C5)

All six targets and every helper: standard axioms only. **No `sorryAx`**: U13 depends on no other 6b target (O2 and
the 6a formula layer are proved). The trace must be empty.

## Unit checks (in addition to COMMON C1–C13)

- **C2 count.** `base-sorries.txt` minus U13's 6 targets: **36 declarations in 15 modules**.
- **C3.** decls2 on `DecryptFormula.lean`: 0 ADDED, 0 CHANGED, 0 REMOVED.
- **C12 probe U13-P1** (optional): `#eval` of `(decryptFormula P C).eval (keyBits P s)` against `decrypt P s C` for
  `q ∈ {5, 8}`, `n = 1`, a handful of `C`, `s`; evidence only.

## Size and split

200–330 lines; `DecryptFormula.lean` stays under 550. One worker; checkpoint 1 with G5, G7 and G8 proved.

**Ready to dispatch once the records pin is filled** (README *Maintainer steps*).
