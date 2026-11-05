# The ch. 2–4 base repair: evidence (2026-11-05)

- **The commit:** `63b93c6b224427c829994f9c5596afa7c9639bc1` on `cryptography/pass-shelat-ch2-4-base-repair`, branched from
  `5b4ade61eac25f247c21c83a3f61f21cec889e1f`. It renames `HardCoreLoops`' `zipWith_xor_ofFn` to
  `zipWith_xor_ofFn_add`, and qualifies 7 uses of `pairEncode_ne_nil` in
  `ThreeColoring/ProtocolProofs.lean`. No statement changes.
- **The replay** (`replay.log`, `replay-order.txt`): the closure of all 125 ch. 2–4 modules (the
  five asymptotic directories, the four Garg-layer directories and their facades) with its upstream,
  170 modules. Each was checked alone with `scripts/lean_check_tree.sh`, into a fresh olean tree.
  **170 of 170 pass, with 0 errors.** It is the first Lean-confirmed build of the ch. 2–4 layer: the
  run-4 record of 2026-10-28 says the build failed, and no closure census was taken.
- **The `sorry` census:** 63 `sorry` warnings, all inherited, matching the run-4 text census:
  - `Candidates`: 57 (Rabin 19, RSA 9, Factoring 8, ElGamal 7, DiscreteLogHardcore 7,
    DiscreteLog 6, Concrete 1);
  - `ThreeColoring`: 3 (Protocol 2, Simulator 1);
  - `Universal`, `UniversalPadding`: 1 each;
  - `NonUniform`: 1 (an optional bridge).
- **Headline axioms** (`checks-axioms.log`): `audits/pass-shelat/Checks.lean` prints 291 headline
  theorems. 237 depend only on `propext`, `Classical.choice` and `Quot.sound`; 54 depend on
  `sorryAx`, each through the 63 `sorry`s above. They include:
  - Thm 63.1, the universal one-way function (`theorem_63_1`, `lemma_64_3`), through the two
    `Universal` gaps;
  - Thm 124.1 and its corollaries, ZK for NP (`zk_proof_of_*`, `col_zk`, `col_hvzk`), through the
    three `ThreeColoring` gaps.
