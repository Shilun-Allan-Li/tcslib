# RAM fill (Codex), tier 2 job A: word arithmetic (`Build/WordArith`, 9 admissions)

Read `COMMON.md` (bundled), its tier 2 addendum included; its rules bind. **Fill name:**
`fill-ram-word-arith`. **Base:** the commit given in the dispatch prompt, on
`complexity/ram-simulation`.

## What this is

`TCSlib/Complexity/TuringMachine/Build/WordArith.lean` states the arithmetic of a word RAM run on
a Turing machine. A word of `W` bits is held least significant first and delimited by blanks
(`Turing.WordAt`). Every row is a five-tape machine over `Bool`: operands on tapes `0` and `1`, the
destination on `2`, blank scratch on `3` and `4` (`Turing.ScratchBlank`). It writes only the
destination's word interval (`Turing.wordWrite`), returns every head, and is stated with
`Turing.ReachesWithin`. The definitions and their readers are proved; **this job proves the nine
admissions.** Jobs B, C and D cite these statements.

## Targets (in file order)

1. `bvBits_injective`
2. `exists_wordAddTM`: `u + v`, `O(W)` steps and radius
3. `exists_wordSubTM`: `u - v`
4. `exists_wordMulTM`: `u * v`, `O(W²)` steps, `O(W)` radius
5. `exists_wordHalfTM`: `u.sshiftRight 1`
6. `exists_wordSignExtendTM a`: `u.signExtend (W + a)`
7. `exists_wordIntTM c a`: `BitVec.ofInt (W + a) c` over a word of `W + a` cells
8. `exists_wordSignTM`: exits `yes`/`no` on `u.toInt < 0`
9. `exists_wordNonzeroTM`: exits `yes`/`no` on `u ≠ 0`

Each has a proof sketch. Gate 162's auditor checked them all achievable, `W = 0` included
(findings G162-06, G162-09 to G162-16).

## Route

- **The lockstep machine, once.** No catalog row reads two tapes with a carry. Write one private
  machine: a finite-state transducer that sweeps the heads of tapes `0`, `1` and `2` together,
  reading a cell of each, writing tape `2` and carrying a state, until the operand's delimiter;
  then sweeps back. Prove its run once, for an arbitrary transducer. Then add, sub and the
  in-place adder that the multiplier uses are instances.
- **The frame (G162-11).** State the lockstep machine's run lemma with an **arbitrary frame**: any
  cells outside the swept intervals, and the scratch tapes, may hold anything and are unchanged.
  The exported add row's `ScratchBlank` precondition does not cover the multiplier, whose scratch
  tapes are occupied mid-run.
- **The multiplier:**
  - copy `u` to scratch tape `3` (`Turing.copyTM`) and set the destination to `0`;
  - for each bit of `v`, least significant first: if it is `1`, add tape `3` into the destination
    (the in-place adder, with scratch tape `4` for the sum, copied back); then shift tape `3` up
    one place, dropping the top bit;
  - walk `v`'s head one cell per round, so the loop needs no counter and stops at `v`'s
    delimiter;
  - clear the scratch tapes and return the heads.

  Invariant after `r` rounds: the destination holds `u * (v mod 2^r)` and tape `3` holds
  `u <<< r`, both modulo `2^W`. Compose the rounds by a phase loop, or by `Contract.trans` and
  induction on `r`.
- **Sign and zero tests (G162-15, G162-16):** instances of `Turing.scanTM` (`Build/Catalog`,
  `Turing.scanTM_run_ofCfg`): forward with a flag (last bit read, or "a `1` was read"), symbols
  unchanged, then branch. They need no new machine.
- **Half, sign extension, constants:** one-word sweeps with finite state. `exists_wordIntTM`'s
  table of `c`'s low bits is finite: the bits from `c`'s bit length upward are all `c`'s sign.
- **BitVec facts:** the ripple-carry bits of `BitVec.add` (`BitVec.getLsbD_add` and the carry
  lemmas in core), `BitVec.toInt_neg_iff` or `msb`, `BitVec.getLsbD_sshiftRight`,
  `BitVec.getLsbD_signExtend`, `BitVec.getLsbD_ofInt`. Search core and Mathlib before proving one.

## Owned file

`TCSlib/Complexity/TuringMachine/Build/WordArith.lean`. Statements byte-identical. Private
helpers in sections before their first use. You may add imports of existing
`TCSlib/Complexity/TuringMachine/Build/*` modules and of Mathlib, each listed in `REPORT.md`
with its reason.

## Admitted dependencies allowed

None: this job's proofs reach no admission.

## Downstream check

Elaborate every module that imports `WordArith` at the base: `Build/KeyTable`, `Build/InputBit`,
`RAMSimulation/Sim/*`, `RAMSimulation/Simulation`, `RAMSimulation/Classes` and the facades
`TuringMachine.lean` and `RAMSimulation.lean`.

## Frontier

The order above is the order of difficulty, mul last. Deliver checkpoints as you go.
