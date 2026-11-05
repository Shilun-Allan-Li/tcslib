# Merging `main` into `cryptography/pass-shelat-ch2-4`: the replay (2026-11-05)

- **The merge:** `87b5b37c6f21fcea58f9274a519b1d530d83c257` on
  `integrate/main-into-pass-shelat-ch2-4`. It merges `main` at
  `7d36bbc27dfabd4988ee1702bc342049a1f3e006` into the branch at
  `1a338385e7e1f67522987162322bee0948c96f3b`.
- **The ruling:** replay first, then the PR (user, 2026-11-05).
- **Conflicts:** two, both resolved by union (`merge.log`):
  - `TCSlib/Complexity/Randomized.lean`: main's facade, plus the branch's six imports and Contents
    entries;
  - `TCSlib/ComputationalModels.lean`: both reference lines.

## Replay (`replay.log`, `replay-order.txt`)

The replay covers the 91 modules whose import closure mixes files changed on `main` with branch
files (`mixed-modules.txt`), plus their upstream: 418 modules. Each was checked alone with
`scripts/lean_check_tree.sh`, into a fresh olean tree. **406 pass and 12 fail:**

| Modules | Cause | Caused by the merge? |
|---|---|---|
| `Asymptotic/MultiMessage`, `Asymptotic/PublicKey`, the `Asymptotic` facade | `TCSlib.Cryptography.zipWith_xor_ofFn` is declared in both `Asymptotic/Encryption` and `Asymptotic/HardCoreLoops` (S1 note, point 1) | no; already on the branch |
| `ZeroKnowledge/ThreeColoring/ProtocolProofs` | 7 × "Ambiguous term `pairEncode_ne_nil`", at lines 175, 211, 219, 222, 239, 242 and 246 | **yes** |
| `ThreeColoring/{Protocol, SimulatorLemmas, SimulatorNumeric, SimulatorMachine, Simulator}`, the `ThreeColoring` facade, `ZeroKnowledge/NP`, the `ZeroKnowledge` facade | a missing olean of a failed import | downstream |

**The cause.**
- `main` added `Complexity.pairEncode_ne_nil`
  (`Complexity/SpaceComplexity/Logspace/InputAccess.lean:83`).
- It states the same fact as the branch's `ColMachines.pairEncode_ne_nil`
  (`ZeroKnowledge/ThreeColoring/Machines.lean:969`).
- `ProtocolProofs.lean` opens both `Complexity` and `ColMachines`, so a bare `pairEncode_ne_nil`
  is ambiguous.

The full-name duplicate screen run before the merge could not see this. No two full names are
equal; the clash is between short names under `open`.

## The fix probe (`fix-probe.log`, `fix-probe.diff.txt`)

The probe ran on the merge in a scratch worktree, with the change left uncommitted and reverted
afterwards. The branch is unchanged. It qualified the 7 uses as `ColMachines.pairEncode_ne_nil`,
then checked `ProtocolProofs` and the 10 modules after it in the replay order:
- **10 of 11 pass, with 0 errors.**
- The 3 `sorry` warnings are already on the branch (`ThreeColoring/Protocol.lean:784, 853`;
  `Simulator.lean:766`).
- The `ZeroKnowledge` facade still fails, on the `zipWith_xor_ofFn` clash.

So, with that fix, the merge adds no failure to the branch. The file is Frederick Dehmel's: the
request goes to him through the user (`S1-note-frederick-addendum-2.md`, F-5).
