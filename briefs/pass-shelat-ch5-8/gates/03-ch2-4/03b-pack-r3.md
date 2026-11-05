# Gate 03b ([PS10] ch. 2–4, one-wayness and collections), round 3: delta audit pack

**What is audited:** the repair of round 2, on `cryptography/pass-shelat-ch2-4` at
`4769fe88d6894a62c87a19bc524088c5a2c99e0b` (the merge of
[Shilun-Allan-Li/tcslib#204](https://github.com/Shilun-Allan-Li/tcslib/pull/204); its Lean files are
#204's head `08fa1185`).
- **Round 2** audited `e79397ea` and found **0 blockers, 1 major, 2 minors**
  (`gate03b-r2-findings.md`, in the bundle, verbatim). Round 1's major (canonical decoding) was
  confirmed fixed there; every other round 1 row was fixed, recorded or scheduled, except #9 and M6,
  which round 2's R2-2 and R2-3 carry.
- **The repair:** #204 changes two docstrings in `TCSlib/Cryptography/Asymptotic/OneWay.lean`; no
  statement changes. R2-3 is a records correction. The diff is `evidence-repairs/03b-r2/repair.diff.txt`;
  the resolutions are `resolutions-03b-r2.md` (both in the bundle).
- **The deliverable:** **`gate03b-r3-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10], 3rd ed., January 2010 (PDF; book page = PDF page −
12). Book pp. 26–28 (Defs 26.1, 27.3) are the relevant pages.

## Brief for the auditor

1. **Verify the three round 2 resolutions:** say for each whether it is fixed, or not resolved and
   why.
   - **R2-1 (major).** `FunFamily.ofString`'s docstring now gives the informal example with
     `p = var` and `g(x ‖ b) := h(x) ‖ 1`, and claims a typed-inversion success at most the
     inverter's success against `g` plus `O(2^{-n/2})`. Check that claim against `ofString`'s
     implementation, which pads or truncates `f`'s output to `p(n)` bits with `false`. Check that
     the special outputs cannot collide with ordinary ones, that the text's experiment is still
     inverted with probability one by `y ↦ 0^{|y|} ‖ y`, and that the stated bound holds,
     including at odd lengths and at `k = 0`. Attempt at least one counterexample.
   - **R2-2 (minor).** `WorstCaseOneWayLit`'s docstring: the two forms coincide for families with
     non-constant `outLen`; with constant `outLen` they can differ.
   - **R2-3 (minor).** `resolutions-03b-r1.md`, row M6 (records): the ledger's DL-15 already
     calls the `GGMRed` copy public.
2. **Check that nothing else changed** in `OneWay.lean`: no statement and no other docstring.
   The diff is the whole change.

Pack 03a's severity guide applies. Do not give a blanket approval.

## Scope

| Item | Where |
|---|---|
| Round 2 findings, resolutions, the diff | `findings/gate03b-r2-findings.md`, `resolutions-03b-r2.md`, `evidence-repairs/03b-r2/repair.diff.txt` |
| Under audit | `TCSlib/Cryptography/Asymptotic/OneWay.lean` (the two docstrings), at the pin |
| Context | `resolutions-03b-r1.md` (row M6), `03b-pack-r2.md` |

## Attestations (maintainer execution claims; `evidence-repairs/03b-r2/`)

- **Elaboration** (`replay.log`): `OneWay.lean` and its 42 downstream modules (facades excluded),
  then `audits/pass-shelat/Checks`, each checked alone into a copy of the tree at #203's merge:
  **44 of 44 pass, 0 errors**. The `sorry` warnings are unchanged (61 before, 61 after).
- **Lint** (`lint.log`): `scripts/style_lint.py` on `OneWay.lean`: 0 findings.
- **Axioms:** no statement changed. The round 2 print of `OneWay.lean`'s public theorems stands:
  all standard, none `sorryAx` (`evidence/b2/axioms.log`).

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Plus one line per round 2 finding: `R2-<n>: fixed / not resolved — <reason>`.

The gate closes at **0 blockers and 0 majors**.
