/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Finite

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Alphabet reduction

[AB09, Claim 1.5]: a machine over any finite alphabet `Γ` is simulated by a machine
over the binary alphabet with only a constant-factor slowdown (the constant depending
on `|Γ|`), and with the same number of work tapes. This is the theorem that justifies
defining `DTIME` over binary-alphabet machines (see
`TCSlib.Complexity.ClassP.DTIME`).

## Deviations from [AB09]

* [AB09] states the slowdown as `4 log |Γ| · T(n)`; we existentialize the constant and
  pad with `+ 1` (empty input), consistently with the rest of the development.
* [AB09]'s statement fixes input and output over `{0,1}` with only the *work* alphabet
  reduced. In our model a machine has one alphabet for all tapes, so "computing a
  binary function" for a `Γ`-machine is expressed via a symbol embedding `e : Bool ↪ Γ`
  (`Turing.FinTM.ComputesFunInTimeVia`): the simulator reads genuine binary input
  directly (its table composes with `e`), block-encodes work-tape symbols in
  `⌈log₂ |Γ|⌉` bits, and decodes each emitted symbol `e b` back to the bit `b`.
  Emitted symbols are always in the range of `e` because the append-only output equals
  the final output string, which is `(f x).map e` — early emissions included, since an
  irrevocable emission remains a prefix of the final output.
* [AB09]'s Claim 1.5 hypothesizes a time-constructible `T`; the simulation does not
  need it, so we drop the hypothesis. The statement also generalizes Boolean output to
  string output.

## Main results

* `Turing.FinTM.alphabet_reduction` — [AB09, Claim 1.5].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Claim 1.5, p. 16.)
-/

namespace Turing.FinTM

/-- **Alphabet reduction** [AB09, Claim 1.5]: if a machine over a finite alphabet `Γ`
computes the binary string function `f` via `e : Bool ↪ Γ` within time `T`, then a
binary-alphabet machine with the *same number of work tapes* computes `f` within
`c · (T n + 1)` for some constant `c` (depending on the original machine).

**Proof sketch.** Fix a binary block code of length `L = ⌈log₂ |Γ|⌉` for `Option Γ`'s
non-blank symbols. `M'` keeps each of `M`'s work tapes as a block-encoded tape. One
step of `M` is simulated by: reading the `L` bits under each work head into the state
(`L` steps per tape, walking right), reading the input bit directly (its `e`-image is
determined by the table), computing `M`'s transition inside the finite state, writing
back the `L`-bit codes while returning left (`L` steps per tape), moving each head `L`
cells in the simulated direction, and emitting the decoded bit whenever `M` emits.
Total: at most `c` steps of `M'` per step of `M` with `c = O(k · L)`, plus a constant
start-up. Logical blank is represented by the all-blank (`none`-cell) block — never-
visited blocks already have this shape, so no binary code needs reserving and no
initialization pass is required (phase-2 audit, finding 8). The invariant
relating block-encoded configurations to `M`'s configurations is preserved by each
simulated step, and `M`'s halting transfers. -/
theorem alphabet_reduction {Γ : Type} [Fintype Γ] [DecidableEq Γ] (e : Bool ↪ Γ)
    (M : FinTM Γ) (f : List Bool → List Bool) (T : ℕ → ℕ)
    (hM : M.ComputesFunInTimeVia e f T) :
    ∃ (c : ℕ) (M' : FinTM Bool), M'.k = M.k ∧
      M'.ComputesFunInTime f fun n => c * (T n + 1) := by
  sorry

end Turing.FinTM
