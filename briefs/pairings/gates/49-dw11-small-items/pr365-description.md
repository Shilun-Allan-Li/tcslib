## Problem
This is the DW-11 ruling (Seyoon, 2026-11-17, `PairingCryptographyPlan.md`). It concerns `TCSlib/Cryptography/Pairing/Group.lean`:
- `BilinearGroup.pow_val_bijective_of_ne_one`, added by #352, restates the frozen `pow_val_bijective` on `G` instead of `G_T`. Its 7-line proof is a copy.
- Three proofs re-derive Mathlib's `pow_mod_card` with a `← Nat.mod_add_div … pow_order` chain: `pow_val_add` (#352), and the frozen `pow_val_mul` and `pow_val_mul_GT`.
- The injectivity step of both bijectivity lemmas (`pow_eq_pow_iff_modEq` + `Nat.ModEq.eq_of_lt_of_lt`) is Mathlib's `pow_injOn_Iio_orderOf`.

## Change
Two signed commits on `5aed99076d2bd4e5d6f831aed88739fc3ce475b6`. Together they change 1 file, +28/−19.

**Commit 1: `6fc5f49456507dab5901045356ea40acf42bdd67`** (+25/−17, proof-only)
- **One new public lemma**, placed before `namespace BilinearGroup`. It has a formula docstring, a glue/source note and a proof sketch:
  ```lean
  theorem TCSlib.Cryptography.Pairing.pow_val_bijective_of_prime_card {M : Type*} [Group M] [Fintype M] {p : ℕ}
      [Fact p.Prime] (hM : Fintype.card M = p) {g : M} (hg : g ≠ 1) :
      Function.Bijective fun a : ZMod p => g ^ a.val
  ```
  It is proved from Mathlib's `orderOf_eq_prime`, `pow_card_eq_one` and `pow_injOn_Iio_orderOf`, plus a cardinality argument.
  - Mathlib at `029db123` has no statement of this form. The closest is `IsCyclic.unique_zpow_zmod`, an `∃!` over `ZMod (Fintype.card α)` for a generator.
- `pow_val_bijective` and `pow_val_bijective_of_ne_one` are now one-line `exact`s of the new lemma, with `B.card_GT` and `pair_ne_one` for the first and `B.card_G` for the second.
- `pow_val_add` and `pow_val_mul` are now `rw [ZMod.val_add/val_mul, …, ← pow_mod_card x _, B.card_G]`.

**Commit 2: `5eaddd171bceccee917929e7f319ff9202994c59`** (+3/−2, at the maintainer's request)
- `pow_val_mul_GT`: the remaining `Nat.mod_add_div` chain becomes `rw [ZMod.val_mul, ← pow_mod_card y (a.val * b.val), B.card_GT]`. Only the proof body changed.
- The module docstring's `## Main results` gains one line for `pow_val_bijective_of_prime_card`. These are 2 added lines; nothing is removed.

**What did not change:** every existing statement, declaration header and declaration docstring. In the module docstring, only those 2 lines were added.
- decls2 against the tip: 1 ADDED, 0 CHANGED, 0 REMOVED.
- touched.py: 1 ADDED and exactly the 5 intended CHANGED.

## Checks
These are for the head `5eaddd17`. Commit 1's checks were run the same way and also passed.
- **Method:** one `lean` process at a time behind a host-slot gate, no `lake build`, no cache get. Replay on `olean-replay-grpfix`, a hard-linked copy of `olean-replay-cs1-s6` (TS2 `13fc8060`, Lean-equal to the base). The records tip has since moved to `bfa1f5a4` with records only; `merge-tree` is clean, and the merged Lean equals this head.
- **Replay:** the plan rebuilt 22 modules (`Group.lean` and its whole downstream) and reused 1412. All 22 gave rc 0, with 0 `error:`/`error(`, 0 sorry and 0 warnings.
  - The state check gives 1434/1434, RESULT OK.
  - The 22 rebuilt oleans have link count 1.
  - The parent tree rehashes 0/0/0 before, after and at the end, and snapshot #6 also gives 0/0/0.
  - Output map SHA-256 `28677767…`. Only `Pairing/Group`'s olean differs from the parent.
- **Admissions:** 192 at both base and head, equal module by module. The diff adds or removes 0 `sorry`/`admit`/`native_decide` tokens.
- **Axioms:** the new lemma, the 5 touched lemmas, `bb1_sidSecure` and `jouxKeyIndist_of_dbdhAssumption` use only `[propext, Classical.choice, Quot.sound]`.
  - The `#sorry_trace` of each traced constant has no direct `sorryAx` user.
  - All 83 constants of `Pairing.Group` are standard.
  - The sorry control is reported NONSTANDARD, as it should be.
- **Rule 10, canonical coe-A seal on `Group.lean`:** base and head both give 567 requests, rc 0 and 0 errors.
  - The request rows, `requested`, `term_names`, `term_readers` and `closure_modules` are equal, and the seal logs are byte-identical.
  - The new lemma refers to no TCSlib definition.
  - Requests did not change, so no consumer seal was needed.
- **Lint:** `campaign_style_lint --check8b TCSlib/Cryptography` gives 92 FAIL / 103 WARN at both base and head, with no new or removed lines. `style_lint` on `Group.lean` gives 0 findings.
- **Consumers** rebuilt cleanly: Pairing/*, KeyExchange/Joux and AdvancedEncryption/IdentityBased/* (BonehBoyen, BonehBoyenMachine/*, BonehBoyenSecurity/*).

Records: `briefs/pairings/fixes/group-dedup/report.md` and `group-dedup-evidence.zip`, which covers both commits.

Gate 49 (DW-11) audits this with #351 and #352.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

https://claude.ai/code/session_01PqpVTiuDcjSqhyfbqnsVxA