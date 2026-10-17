# C1's normal form in its own module (PR #120): notes

**Why:** the user's ruling of 2026-10-17 (C1's fill plan, question 3). Two workers cannot share a
file. `NTimeHierarchy` holds the universal machine's brief (UN with BF, H′ and S), so NF
(`Turing.FinNDTM.exists_codeNDTM_accepts_linear`, 2.5–5k lines of fill) moves out.

**What:** `lean/nd-normalform`, one commit (`95a3b6a0`) on #119's first commit `4abca360`. It is now
merged with #119's second and third commits (head `6d18902f`); the Lean diff from #119's head
`1e45f50a` is the same three files.
- The new `ClassNP/NDNormalForm` holds NF's declaration with its docstring, byte-identical (2,599
  characters, asserted by `move.py.txt`). It imports `ClassNP/NTIME` and `TuringMachine/NDCodes`, as
  `ExhaustiveReplay` does.
- `NTimeHierarchy` imports it, and its docstrings point there.
- The `ClassNP` facade lists it.
- The plan described a copy under a new name with a one-line citation in `NTimeHierarchy`. The PR
  moves the declaration itself under its existing name instead: one public statement, not two.
- An `NDCodes` docstring pointer ("in the consumer module") stays as is. It is still true, and editing
  it would have put `NDCodes`' whole downstream closure into the replay.

**Checks** (maintainer, against `oleans-lbapi4`; `logs/`):
- `NDNormalForm` alone has 0 errors and 1 warning (NF's `sorry`).
- `NDNormalForm` has no olean yet, so the two modules' bodies were elaborated in one check file. That
  gives 0 errors and the six `sorry` warnings of the base `NTimeHierarchy` (`base-NTimeHierarchy.out`).
- **Freeze** (`freeze/`): `NTimeHierarchy` removes only NF's public, and `NDNormalForm` adds it.
- **Lint:** 0 FAIL. `ClassNP/` stays at 15 WARN (now over 21 files), `Diagonalization/` at 1.
- **Replay closure:** 4 modules (`replay-order.txt`). `replay-lndnf.sh` chains from `oleans-lndapi`
  (#119's replay, 189 modules).

**Replay passed (user, 2026-10-17):** `replay-lndnf.sh`, 4 of 4 at `6d18902f`, 0 failed, static-equal
(6). The snapshot `oleans-lndnf` is the tip plus #119 and #120. The gate is staged in
`infra_local/gate-dispatches/38-nd-normalform-gate/`.
