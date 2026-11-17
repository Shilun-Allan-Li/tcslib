This PR proves **T1** `BilinearGen.bdhAssumption_of_dbdhAssumption`, the folklore implication that the DBDH assumption gives the BDH assumption under the exponential-order hypothesis. The maintainer wrote it in-house under Seyoon's overnight authorization.

**Head:** `916afc25c21f5e52b4b01958186ad55d2f615fd1`, one signed commit. **Base:** `cryptography/pass-shelat-ch2-4`. #331 has merged, so the PR is retargeted to the records branch. Against the tip, the only file changed is `Pairing/Assumptions.lean`: +227/−8.

## The proof (the Gate 40 route)
- **The distinguisher `D`** re-pairs the first five components of its input into the BDH string, runs the solver `A`, and accepts iff `A`'s answer equals the target encoding. It is `NUPPT.ofPolyTime` of a raw function, and its equality test is `polyTimeComputable_pairEq`.
- **On a real tuple,** `D` accepts exactly when `A` wins.
- **On a random tuple,** injectivity of `encT` bounds acceptance by `1/p`.
- **The order bound** is `1/p ≤ 2^{-κ} + [p < 2^κ]`. The bad generator coins cost at most `δ(κ)`, and negligibility follows.
- No group operations, no decoding and no `Ops` are used.

## Changes
- T1's header is byte-identical. Its body and `**Proof sketch.**` describe the delivered proof.
- Four imports are added: `Complexity.Randomized.Closure`, `Complexity.Randomized.Repetition`, `Games.Bridges.Experiments` and `OneWayFunctions.Basic`.
- Ten private helpers are added, each with a formula docstring. No public declaration is added, and no other file changes.

## Checks
In-house evidence is in `briefs/pairings/fills/pair-bdh/inhouse-r1/`.
- **Frozen-header check:** PASS, with all 6 mutation controls behaving as required.
- **Build:** the pairing closure at the head gives rc 0, with 0 `error:` and 0 `error(`.
- **Admissions:** T1 is removed and nothing is added.
- **Axioms:** T1 uses only `propext`, `Classical.choice` and `Quot.sound`.
- **Rule 10 on `Assumptions`:** the seals (strict and coe, × A and B) pass 4/4 with 0 errors. Paired controls are ALL_OK, and the explicit-unfold scan finds 0 foreign unfolds.
- **Overlap and reuse:** 7 disclosures, none a copy of a published lemma. For example, `decide_singleton_eq_true` exists in `PublicKey/TrapdoorPredictor.lean`, but it is not imported here, to keep the public-key layer out of the pairing closure.

**Joint check with #346 on olean snapshot #4** (Gate 44 staging; `briefs/pairings/gates/44-pairing-fills/`). The tree is tip × #340 × #346 (`33681cb8`, Lean-equal to `c7be1301`).
- **Build:** 16/16 modules rc 0. The state check is OK over 1427 modules.
- **Admissions:** −2, exactly T1 and T4.
- **Seals:** the `Assumptions` seals and paired controls pass. #346's five owners downstream of `Assumptions` are re-sealed, 20/20 with 0 errors. Each gains exactly #340's two private definitions as requests. This answers the downstream-seal item that was open in the earlier description.

**Gate 44 (Codex)** audits this PR together with #346. Seyoon merges.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

https://claude.ai/code/session_01PqpVTiuDcjSqhyfbqnsVxA