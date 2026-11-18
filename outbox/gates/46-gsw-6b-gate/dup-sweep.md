# Gate 46 · pre-dispatch duplication sweep (GSW 6b: #376 O2 and #377 statements)

Run 2026-11-18 at staging, before dispatch (binding practice since Gate 50, lesson G50-05). Static only: no Lean, no
`lake`; git objects, `python3 -I` and grep. The raw output is `checks/dup-sweep.txt` in `verification.zip`
(`tools/dupsweep46.sh`); the import closures are from `tools/closure.py`.

**Result: one finding needs a ruling (S1). Everything else is a note with a disposition already on record.**

**Update at re-staging (2026-11-18): S1 is ruled and fixed.** Seyoon ruled option A (fix now). Landing edit LE-g46
(`7563734a8badba842223e0687c719b3b4692e9d2` on #377; `le-g46.md`) makes both proofs apply `length_flatten_map_const`
after `List.ofFn_eq_map` and `List.length_finRange`; DL-61 reads "Repaid by LE-g46". The sweep's greps were re-run at
the new head (`verification.zip` `checks/dup-sweep.txt`); apart from line numbers they differ only in the two proofs.
The text below is the sweep as written at staging, at `680be9fa` (line numbers there).

| Item | Kind | Disposition |
|---|---|---|
| **S1** | undisclosed inline re-derivation of a public TCSlib lemma (two proved readers in #377) | **ruling pending (Seyoon), question Q-G46-S1**; recorded today as ledger row **DL-61** (status open) |
| N1–N11 | notes: no duplicate, or a duplicate-shaped item already ruled or by design | none needed; listed for the auditor |

## Pins

- #376 `04ba2446f541c39dd02aefaa97a9eb31dbbda748` (O2); #377 `680be9fa45a9cf5deeb7a59820e8e86aaaa4f068`.
- Records tip at staging `dab31951abb5c892dc6279c229e49497ec95de10`. Its Lean equals the PR cut tip
  `38123ccbebef878cd25dd2d2761de1b40ba7e421` and snapshot #10's T `cf6a2266`.
- `main` `acea851c1dbafae140d481d91827dcf72ba31c74`.
- Mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`, Batteries `39260e31b7b3f7f05643da95242463b462dc05f1`, core
  Lean 4.25.0.

## What was swept

- **Inventory.** decls2, tip → #377 head (phase 2, `decls2/tip-vs-stmt.tsv`): **136 ADDED, 0 CHANGED, 0 REMOVED**.
  Of these, 5 are #376's (`decodeLo`, `decodeHi`, `decodeLo_eq`, `decodeHi_eq`, `decode_iff_mem_Ico`) and **131** are
  #377's. ("5 + 136" in the staging request counts O2 twice: the 136 already contain it.)
  - An independent count of added keyword lines gives the same 136: 9 `abbrev`, 41 `def`, 1 `instance`, 85 `theorem`.
  - There are **0 `private`** declarations.
  - `simps` adds 4 more names, `Parameters.ofFamily_lwe`/`_width` and `fheView_fst`/`_snd`.
- **By name.** All 135 short names were checked as declarations in `TCSlib/` and `audits/` at the records tip and at
  `main`, and in Mathlib and Batteries. The only hits are the unrelated namespaces phase 1 lists: `Coins` (PPT,
  `SecureComputation.Hybrid`, `ZeroKnowledge.Interaction`), `PublicKey` (RSA) and `select` (`Turing.Cfg.select`,
  `Randomness.Rejection.select`). Mathlib and Batteries give 0 hits.
- **By definition body.** Each new definition's body shape was grepped across TCSlib: `decomposeVec P (secretVector …)`,
  `vecMul (decryptColumn …) (gadget …)`, `mul P (gadget P - …)`, `evalWith (select …)`, `modSumInterval (fun …)`,
  `Fin.append cts …homNot`, `encodeMatrix P.width`, `encodeChallenge P.lwe P.width`, and the names `RatioBounded`,
  `ofFamily`, `ReductionEfficient`, `WeakCircular`, `hybridPlant (encrypt …)`. Nothing is found outside the new files.
  The new definitions reuse `encodeMatrix`, `encodeChallenge`, `homNot`, `hybridPlant`, phase-5 `reduction`/`encrypt`,
  6a `modSumInterval`, `evalWith`, `barrington`, `runWith`, `toNANDForm` and `layerNAND` as terms. They copy none of them.
- **By statement shape.** I read every target and reader statement against its nearest relatives: phase-5 GSW,
  `LWE/`, Regev, `EnsembleSecurity`, the 6a `Complexity/` layer and the brief's list of near-relatives.
- **Inline proofs.** I read every proof body at the head that is not `rfl`, `Iff.rfl` or `sorry` (section 3 of
  `dup-sweep.txt`): O2's `decode_iff_mem_Ico`; `neZero_columns` (after LE-6b3); the case readers of `bootGate` and
  `levelGate`; `literalCts_castAdd`/`_natAdd`; G11 and L1; and the four `_length` readers. Each one-step use of a library
  lemma is listed there.

The name scan and the body scan are kept separate from the statement-shape reading, as G50-05 asks. S1 was found by the
shape reading, not by either scan.

## S1 · ruling needed

**What.** Two readers in #377 rebuild "a flatten of constant-length blocks has length count × block" inline, and the
docstrings do not say so:
- `GSW.encodeFheView_length` (`AdvancedEncryption/Homomorphic/GSW/Asymptotic.lean:123`);
- `GSW.encodeLeveledView_length` (`:152`).

Both proofs run `List.length_flatten`, `← List.ofFn_comp'`, `List.ofFn_const` and `List.sum_replicate_nat` for each
`(List.ofFn fun i => encodeCiphertext P (…)).flatten` block (`:128–130`, `:157–160`).

**The public lemmas.**
- **`TCSlib.Cryptography.length_flatten_map_const`** (`Cryptography/Foundations/BitLists.lean:175`):
  `(l.map g).flatten.length = l.length * k` when every `g x` has length `k`.
  - It is proved by the same chain, `List.length_flatten`, `map_const'`, `sum_replicate_nat`.
  - `Foundations.BitLists` **is in the import closure** of `GSW/Asymptotic` (134 modules).
  - It applies after Mathlib's `List.ofFn_eq_map` (`Mathlib/Data/List/FinRange.lean:87`) and core's
    `List.length_finRange`.
- **`TCSlib.Cryptography.Authentication.length_flatten_ofFn`** (`Authentication/Signatures/Lamport.lean:123`): the exact
  `List.ofFn` form for `List Bool` blocks, `(List.ofFn g).flatten.length = q * B`. It is **not** in the closure.
- `TCSlib.Cryptography.length_flatten_ofFn` (`Encryption/PublicKey/HybridMachine.lean:105`, in the closure) and
  `CommitmentLemmas.length_flatten_ofFn` (`ZeroKnowledge/CommitmentLemmas.lean:211`) state only the
  `List.ofFn (f i)`-block case, so they do not apply to `encodeCiphertext` blocks.
- Core, Mathlib and Batteries have no `flatten`-of-`ofFn` length lemma (section 4a).

**Grade.** Under the dispatched standard, an inline re-derivation of a public lemma is a re-proof:
- Gate 50 regraded GF-F03 to **major** for rebuilding `Finset.sum_le_card_nsmul` from `sum_le_sum` and `sum_const`;
- see also G48-01 and GF-F01.

These two proofs rebuild a public lemma of the closure from the same core steps, and it is not disclosed. Unless
Seyoon rules it accepted, Codex would grade it like GF-F03.

Phase 1 (`final-6b-r1/review.md`, *Inline proofs*) read these proofs and wrote "The `_length` proofs use only library
lemmas". That is the G50-05 pattern: the review looked at names and bodies, not at the statement shape.

**Question Q-G46-S1 (Seyoon). Not decided here.** *(Ruled 2026-11-18: A, fix now; done by LE-g46.)*
- **A. Fix now** with a proof-only landing edit **LE-g46** on #377. This follows the Gate 50 sweep ruling (fix now,
  LE-g50) and G48-01 (repaid before round 2).
  - It touches `GSW/Asymptotic.lean` only and changes both proofs to go through `length_flatten_map_const` (with
    `List.ofFn_eq_map`, `List.length_finRange`). The docstrings name the lemma.
  - Checks: comment-strip identity outside the two proofs; a re-replay of `GSW.Asymptotic`, `GSW`, `Homomorphic`,
    `AdvancedEncryption` and `TCSlib` on R2; the coe-A seal of `GSW/Asymptotic`; decls2 0/0/0.
  - It needs one Lean slot. #377's head changes, so the pack is re-pinned to the new head before dispatch.
- **B. Accept as debt.** Ledger row DL-61 becomes Accepted, and the pack discloses it as accepted debt (G44-01: a
  recorded acceptance plus a ledger row with its repayment).
  - Repayment: the U19 fill, or Cleanup Stage 2 together with the pre-existing family in N11.
  - No Lean is needed now.

**Recorded today:** `briefs/pass-shelat-ch5-8/duplication-ledger.md` row **DL-61**, status *Open: ruling pending*
(now *Repaid by LE-g46*). The
lattice rows (DL-50, DL-54) live in that ledger, and there is no separate lattice ledger. The row is updated with the
ruling.

## Notes (no ruling needed)

- **N1 · `decDepth_le` (G8) against F10 `modSumDepth_le`** (`FormulaArith/ModSum.lean:365`). F10 bounds
  `modSumDepth M q` by `9⌈log₂ M⌉ + 2⌈log₂(⌈log₂ q⌉ + ⌈log₂ M⌉ + 3)⌉ + 21`, and G8 bounds `decDepth P` (= `modSumDepth N q`,
  `decDepth_eq`) with `ℓ` in place of `⌈log₂ q⌉`.
  - It is a weakening with a different right-hand side, not a restatement.
  - Disclosed (G6B-F05) and **ruled** Q-6B-F2 A (it stays an admitted target; the U13 fill is about 3 lines).
- **N2 · O2's `hsub`** (`LWE/BitEncoding.lean:157–166`), the two-case value of `(v − ⌊q/2⌋).val`.
  - The first case uses Mathlib's `ZMod.val_sub`.
  - The second case is the `ZMod` analogue of core's `Fin.coe_sub_iff_lt` (`Init/Data/Fin/Lemmas.lean:1089`), stated for
    `Fin`. Mathlib's `Fin.intCast_val_sub_eq_sub_add_ite` (`Mathlib/Data/Fin/Basic.lean:306`) is its ℤ-cast form.
  - There is no `ZMod` lemma for an abstract modulus (`Mathlib/Data/ZMod/`). Using the `Fin` one would need a case split
    `q = n + 1` through `ZMod`'s definition.
  - The phase-1 disposition (no lemma, info) stands. Phase 1 put `Fin.coe_sub_iff_lt` at `Mathlib/Data/Fin/Basic.lean:306`;
    it is in core, and Mathlib's line 306 is `intCast_val_sub_eq_sub_add_ite` (pack, known slips).
  - O2's other step goes through `ZMod.valMinAbs_natAbs_eq_min`, the checkpoint-1 fix of G6B-C1-F01.
- **N3 · `Parameters.neZero_columns`** (`GSW/DecryptFormula.lean:65`). The old case contradiction re-derived core
  `Nat.one_lt_two_pow_iff` (G6B-F04). **Repaid** by LE-6b3 (ruled Q-6B-F1 A), which compiles. No `NeZero P.columns` or
  `width_pos` lemma exists elsewhere (section 4c).
- **N4 · G11 `encrypts_evalKey` and L1 `encrypts_levelKey`.** These are proved citations of phase-5 `encrypts_encrypt`
  (`Scheme.lean:182`) and `encrypts_keygen_encrypt` (`:207`) through the file's own `evalKey_eq`/`levelKey_eq`. The brief
  allows this (the LE-g45 `const_eval` precedent); they are never admitted, and they are disclosed in REPORT §4.
- **N5 · G14 and A2** are reader-only: `weakCircularSecure_iff` and `weakCircularSecureFamily_iff`, ruled Q-6B-1 A.
  No `distAdv_fheView_le` or `fheView_negligible` exists.
- **N6 · G15 `distAdv_fheView_noEvk_le`** has the right-hand side of phase-5 `distAdv_encrypt_le` (`Security.lean:248`).
  - Its left-hand side is a view over `Seeds P χ`, which has an extra evaluation-key coin component, so it is the
    transport of that theorem along the coin regrouping (`acceptProb_comp_equiv`, `acceptProb_fst`/`uprob_fst`), not a
    restatement.
  - This is the brief's design: over `realView` it would restate the theorem (G45-01).
- **N7 · Compositions.**
  - G18 is G10 through N3–N4;
  - G17 (split) is G12/L3 with G16;
  - G3 is C14/C16 with G2;
  - G6 is `decrypt_eq_decode_dotProduct` (#368), F9 and O2.

  Each is a theorem to be proved from public lemmas, not a restatement of one.
- **N8 · Thin wrappers.** `encodeCiphertext` (= `encodeMatrix P.width`), `keyBits`, `decConstants`, `homEvalPBP`,
  `literalCts` and the seven type abbreviations are definitions over existing terms, each with its reader. No existing
  declaration has the same body (section 4d).
- **N9 · Case readers.** `bootGate_of_args_eq_*` and `levelGate_of_lt`/`_of_le` unfold the file's own definitions.
  `literalCts_castAdd`/`_natAdd` are readers through core `Fin.append_left`/`_right`.
- **N10 · Other relatives** from the brief's list are confirmed different: `eval_encrypts`/`decrypt_keygen_eval`
  (phase-5 leveled `eval`), `homGate`, `Encrypts.nand`, `vecMul_secretVector_augmented`, `gadget_mulVec_decomposeVec`,
  `decode_codepoint_add`. The three `negligible_polyExpr_mul` copies are cited in sketches; no fourth is added.
- **N11 · A pre-existing family of flatten-length lemmas** (not 6b's; context for S1 option B). The same fact is stated
  at least six times in TCSlib:
  - `length_flatten_ofFn` in Lamport, HybridMachine and CommitmentLemmas;
  - BitLists' `length_flatten_map_const`/`_map_range`;
  - `Programs/Util/List.lean`'s `length_flatMap_finRange`/`length_flatMap_range`;
  - `PSubsetPPolyTableau.length_flatMap_const`;
  - EnsemblesLemmas' `length_flatMap_range`.

  None is in the ledger. Whether to consolidate them is a Cleanup Stage 2 question for Seyoon, not a 6b one.

## Not swept

- 6a and #368 content: audited at Gates 45 and 50, merged.
- Proof sketches as plans: they name the lemmas a fill will use and prove nothing.
- Duplication inside the delivery's evidence tools.
