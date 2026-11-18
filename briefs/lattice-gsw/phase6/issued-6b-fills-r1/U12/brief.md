# Claude fill · `gsw-6b-u12`: GSW 6b unit U12, homomorphic branching programs (G1–G3)

**Unit** `gsw-6b-u12` · **Route** Claude fill, one worker (no sub-agents needed) · **Base** B6
`bff0567b6c4b6b724c8fd20ff3ef92258eb3fc9d` (tree `845bdc982fd8f79aba755796bb13188922c4655d`, the #377 merge) ·
**Size** 150–250 fill lines (r3 §H7) · **Delivery** `inbox/fills/gsw-6b-u12/` on `exchange/pass-shelat-ch5-8` ·
**Local inputs (rule 16)** none.

Read `../COMMON.md` first; it is part of this brief. Then `../dup-sweep.md` §0 and §U12 (binding must-reuse list).

## Targets (frozen statements; prove all three)

| Row | Declaration (`TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.`) | Line at B6 |
|---|---|---|
| G1 | `Encrypts.select`: `select P C U V` encrypts `(1 − b)·u + b·v` with noise `βV + 2·(N·β)` | `GSW/Branching.lean:120` |
| G2 | `encrypts_homEvalPBP`: a permutation program of length `L` from `Pi.single s₀ G`, coordinate `i` encrypts `[yield x s₀ = i]` with noise `L·(2·(N·β))` | `:147` |
| G3 | `encrypts_homEvalFormula`: a fan-in-2 formula of depth `d` encrypts `c.eval x` with noise `4^d·(2·(N·β))` | `:171` |

`GSW/` is `TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/`. Each target is `theorem … := by sorry` with a
frozen header, statement prose, source tag and `**Proof sketch.**` (Gate 46: fidelity CLEAR).

## Owned file and scope

`TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Branching.lean` (179 lines at B6), under COMMON §4. **No
public helper**: every helper is `private`. Everything else is frozen, including the 6a modules this file imports
(`BranchingPrograms/{Defs,Eval,Barrington}`, proved) and phase 5's `Noise.lean`.

## Known context

- **G1.** The selector is `mul P (gadget P - C) U + mul P C V` (`select_eq`); the fresh selector is on the left of
  both products, so the step's noise is additive in the state's noise (module docstring, *Deviations*). `hb : b = 0 ∨
  b = 1` is over `ℤ`: case on it and use `Encrypts.mul_bit` (`Noise.lean:247`) with `false.toNat`/`true.toNat`, or
  `Encrypts.mul` with `Encrypts.mono`; either way do not re-derive `|1 − b| + |b| = 1` as a general lemma.
- **G2.** Through the host lemma `BranchingProgram.evalWith_rel` (C7) against the Boolean run
  `evalWith (fun b u v => if b then v else u) x (Pi.single s₀ 1)` and `evalWith_single` (C8); the step reads the pull
  form `Instr.stepWith_of_isPermutation` (C6), the program being a permutation program (`isPermutation_iff`). The
  relation at step `τ` carries noise `τ·(2·(N·β))`; initial coordinates are `G` (`encrypts_gadget`) and `0`
  (`encrypts_zero`). Worst case (BV14 Lemma 3.6 is with overwhelming probability; disclosed in the statement).
- **G3.** `homEvalFormula_eq`, G2 at `s₀ = 0`, `i = sigma1 0` for `barrington c sigma1` (`isPermutation_barrington`,
  C15); the message by `barrington_yield_zero` (C16, with `isFiveCycle_sigma1`) and `sigma1 0 ≠ 0` (`isFiveCycle_iff`
  or `decide` on `Fin 5`); noise by `barrington_length_le` (C14) and `Encrypts.mono`. The output coordinate is `σ 0`,
  not BV14's `1` (frozen deviation).
- **Probe history** (G6B-F06): the statement job's P2c (G3 numeric noise) was stopped for time; only the noise-free
  part ran. No statement was found false.

## Axioms (C5)

All three targets and every helper: `propext`, `Classical.choice`, `Quot.sound` only. **No `sorryAx`**: U12 depends
on no other 6b target (the 6a modules are proved). The trace must be empty.

## Unit checks (in addition to COMMON C1–C13)

- **C2 count.** At the head, `base-sorries.txt` minus U12's 3 targets: **39 declarations in 15 modules**.
- **C3.** decls2 on `Branching.lean`: 0 ADDED, 0 CHANGED, 0 REMOVED.
- **C12 probe U12-P1** (optional, time-boxed at 30 minutes of pool time): `#eval` of `select` on toy parameters
  (`n = 1`, `q = 8`, `ℓ = 3`) against the message `(1 − b)·u + b·v` for the four bit pairs, evidence only.

## Size and split

150–250 lines; `Branching.lean` stays under 450. One worker; checkpoint 1 with G1 proved and checked.

**Ready to dispatch once the records pin is filled** (README *Maintainer steps*).
