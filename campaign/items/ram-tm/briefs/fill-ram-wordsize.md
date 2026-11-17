# RAM fill (Codex): tier 1, the word size (`RAMSimulation/WordSize`, 3 admissions)

Read `COMMON.md` (bundled) first; its rules bind. **Fill name:** `fill-ram-wordsize`.
**Base:** the commit given in the dispatch prompt, on `complexity/ram-simulation`.

## What this is

`TCSlib/Complexity/RAMSimulation/WordSize.lean` defines the stage-2 word-size hypothesis:

```lean
def WordSizeComputable (W TW SW : ℕ → ℕ) : Prop :=
  ∃ M : Turing.FinTM Bool, ∀ x : List Bool, ∃ t ≤ TW x.length,
    M.ComputesInTime x (W x.length).bits t ∧ M.tm.spaceUsed (M.tm.initCfg x) t ≤ SW x.length
```

It also states three admitted results. Their statements were audited on 2026-10-14 and
rechecked against the base on 2026-11-17; they are frozen. **This fill proves all three.**

## Targets

1. **`WordSizeComputable.mono`**: larger bounds. This is the same machine and the same halting
   times. The definition is in the same file, so it may be unfolded.
2. **`wordSizeComputable_logSpace (c : ℕ)`**: some `a` with
   `WordSizeComputable (fun n => c * logSpace n) (fun n => a * (n + 1)) (fun n => a * logSpace n)`.
   The time is **linear** and the space is logarithmic.
3. **`wordSizeComputable_of_spaceConstructible (hS : SpaceConstructible S) (c : ℕ)`**: some `a`
   and `TW` with `WordSizeComputable (fun n => c * S n) TW (fun n => a * S n)`. The time `TW` is
   unconstrained, but it must be a function of `n` only.

## Route (the maintainer's reading; you choose the construction)

**Target 2.** One machine, in stages. Each stage after the first works on a word of length
`O(log n)`, so its time is far below linear.
- **First stage:** `Nat.bits |x|`. `Turing.FinTM.computesFunInTime_lengthBits_spaceUsed`
  (`Build/Catalog`) gives a machine that computes `x ↦ Nat.bits |x|` within `c₀·(|x| + 1)` steps
  and `c₀·(Nat.size |x| + 1)` cells. The work-tape contract `Turing.exists_inputLengthTM`
  (`Build/InputLength`) writes `Nat.bits |x|` on a work tape within `C·(|x| + 1)` steps, with
  head envelope `C·(|bits |x|| + 1)`. It is the natural first stage of a composed machine.
- **Note:** `logSpace n = |Nat.bits n|` for `n ≥ 1`, and `logSpace 0 = 1`. Read `logSpace`
  through `Complexity.logSpace_eq`.
- **Next stages:** the length of that word in binary, then multiplication by the constant `c`
  (repeated addition, or shift-and-add), then emission as `Nat.bits (c * logSpace n)` on the
  output tape. `c = 0` gives the empty word.
- **Composition:** `Build/Seam` (`seamCompTM`, `seamCompTM_run`, `seamCompTM_run_ofCfg`,
  `seamCompTM_spaceUsed_le_add`, `seamCompTM_spaceUsed_le_add_ofCfg`) and `Build/Embed`
  (`embedSilentTM`). The time bound needs `poly(log n) ≤ a·(n + 1)` for a suitable `a`. Prove
  it once, as a private arithmetic lemma.
- **Not usable:** `Complexity.spaceConstructible_logSpace` (`SpaceComplexity/Constructible`)
  computes `Nat.bits (logSpace n)` in logarithmic space but bounds no time. Its private machine
  `b3a_log_machine` cannot be cited across files.

**Target 3.** `SpaceConstructible S` gives `logSpace ≤ S` and a machine `M_S` with
`M_S.ComputesInSpace (fun x => Nat.bits (S |x|)) (c_S * S ·)`. Read both through
`Complexity.spaceConstructible_iff` and `Turing.FinTM.computesInSpace_iff`.
- Run `M_S` with its output captured on a work tape (`embedSilentTM`), multiply by `c`, and emit.
- **Space:** `c_S·S + O(log (c·S) + 1) ≤ a·S`, because `S ≥ logSpace ≥ 1`.
- **Time:** `ComputesInSpace` gives each input a halting time. Take `TW n` to be the maximum
  over the `2^n` inputs of length `n` (a `Finset.sup` over `List.Vector`, or a classical choice
  of bound), plus the multiplication's cost.

**Shared helper.** Targets 2 and 3 both need "multiply a binary word on a work tape by the
constant `c`". Write it once as a private machine with its run and space lemmas, and cite it
twice.

## Owned file (modify this and nothing else)

`TCSlib/Complexity/RAMSimulation/WordSize.lean`.
- **Imports:** you may add imports of existing `TCSlib/Complexity/TuringMachine/Build/*`
  modules, which the construction needs. List each one in `REPORT.md` with the reason. Do not
  add any other import.
- **Statements** stay byte-identical. The machines are private, in a section
  `/-! ## Machines -/` before the targets.

## Downstream check

`RAMSimulation/Simulation`, `RAMSimulation/Classes` and the facade
`TCSlib/Complexity/RAMSimulation.lean` import this file. Elaborate all three.

## Size and frontier

Target 2 is the hardest and may run to several hundred lines. Deliver in this order:
1. target 1;
2. the shared multiplication helper;
3. target 3;
4. target 2.

A frontier after any of these steps is acceptable; checkpoint zips are welcome.
