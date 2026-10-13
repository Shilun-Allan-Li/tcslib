/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.SpaceComplexity.ConfigGraph
import TCSlib.Complexity.SpaceComplexity.Constructible
import TCSlib.Complexity.TimeHierarchy.CodePrefix
import TCSlib.Complexity.TimeHierarchy.Diagonal
import TCSlib.Complexity.ClassNP.NP

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The space hierarchy theorem

[AB09, §4.1.3, Theorem 4.8] with the space-bounded universal machine of
[AB09, Exercise 4.1] (its forward clause, as the book states it), the
strictness corollary `L ⊊ PSPACE` on the p. 92 chain, and `SPACE(n+1) ≠ NP`
([AB09, Exercise 3.2], restated with the positive normalization per the P0
convention — `AroraBarakChapters3-4Plan.md` §2.4). Phase P4.3; on 2026-10-12
`space_universal` was restated forward-only and `space_hierarchy`'s sketch
moved to the window route (`machine-library-design.md` §16b item 3,
`backlog.md` RD-3), both pending their statement gate.

## Design

* **Constant-factor overhead is the point** ([AB09]: "one can have a
  universal TM using only a constant factor of space overhead, and hence we
  don't need the logarithmic term of Theorem 3.1"): the hierarchy hypothesis
  below is eventual domination of every constant multiple — no square, no
  log — in contrast to the received `f²` time hierarchy.
* **The space-universal machine** reuses the fixed code scheme
  `Complexity.TimeHierarchy.code` (one-work-tape binary codes) and the layout
  `⟨bits s, ⟨α, x⟩⟩`, and keeps only Exercise 4.1's forward clause: a run of
  the coded machine within `s` work cells is reproduced, output included,
  within constant-factor space. Overruns and divergence are unconstrained, so
  the machine tests no budget, runs no clock and replays nothing. Its space
  bound carries a `+ logSpace n` addend for its input device (the simulated
  input is a suffix of its input, read through a binary position) — a
  declared deviation from Exercise 4.1's literal `C_α · t`, which presumes the
  standing `S(n) > log n` convention.
* **The hierarchy takes the window route** (design §16b item 3): the
  diagonalizer runs one fixed self-application universal machine `U₀` in a
  window of radius `a · g(n)` on the configuration-record rows
  (`Build/CfgRecord.lean`, `Build/RecordTable.lean`), stopped by a
  configuration-count clock, and flips its verdict. The window, not `U₀`'s
  code-dependent constant, bounds the diagonalizer's space. The chapter-1
  interpreter (`Turing.universalInterpreter`) serves neither machine: it
  tracks the simulated input head in unary on its fourth tape, which uses one
  plus the largest simulated input position reached, `Θ(n + 1)` cells on a
  full scan, so it cannot guarantee `O(S(n))` space uniformly for sublinear
  `S` (Finding B, recorded in the sketches).
* **Both bounds space-constructible**, as in the book; `g`'s witness drives
  the window radius and the clock width, and of `f` the proof uses only the
  bundled floor `1 ≤ logSpace n ≤ f n` (round-1 confirmed, recorded in the
  sketch).
* Facade wiring: root-wired while the P4.1 gate was live; the
  `SpaceComplexity.lean` facade has carried this module since that gate
  closed.

## Main results (all sorried; phase-P4.3 statements)

* `Complexity.space_universal` — [AB09, Exercise 4.1], forward clause
  (restated 2026-10-12).
* `Complexity.space_hierarchy` — [AB09, Theorem 4.8].
* `Complexity.LOGSPACE_ssubset_PSPACE` — `L ⊊ PSPACE` on the p. 92 chain.
* `Complexity.SPACE_linear_ne_NP` — [AB09, Exercise 3.2], normalized.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.3, Theorem 4.8, Exercise 4.1;
  Exercise 3.2; [SHL65] through [AB09].)
-/

namespace Complexity

open Turing

/-- **The space-bounded universal machine** ([AB09, Exercise 4.1], p. 93,
forward clause; spec, fill pending — phase P4.3, restated forward-only
2026-10-12 by design §16b item 3, statement gate pending): for the fixed
scheme there is a machine `SU` such that for every code `α` there is a
constant `C > 0` with: whenever the coded machine halts on `x` with `output`,
having visited at most `s` work cells by then, `SU` on input
`⟨bits s, ⟨α, x⟩⟩` halts with the same `output`, having visited at most
`C · (s + logSpace |x| + 1)` work cells. Nothing is claimed when the coded
machine overruns `s` or does not halt. The time is existential, as
`Turing.FinTM.ComputesInTime`'s halting demands, with no stated bound.

Deviations from the book's `SU(α, t, x) = M_α(x)` within `C · t` cells:
* **`C` depends on the representation `α`**, not only on `M_α`, as in
  `Turing.universal`, whose module docstring records why an arbitrary
  effective scheme forces this.
* **The `+ logSpace |x| + 1` addend** pays for the input device: `x` is a
  suffix of `SU`'s input and the cell left of it is the pairing separator's
  `true`, so the simulated position `0` must be emulated, which the device
  does by holding the simulated head's position in binary. Under the
  book's standing convention `s ≥ logSpace |x|` (p. 79) it is absorbed:
  `s + logSpace |x| + 1 ≤ 3s`. It is a cost of this construction, with no
  lower-bound claim against other input devices.
* "Halts before using `t` cells" is read as "at most `s` visited cells"; the
  budget is an argument of `SU`, as in the book, but is never read.
* The output is the simulated output itself: with no failure clause there is
  no verdict to tag. The former `[false]` clause, and with it the
  visited-interval counters, the core-count clock and the probe/replay of the
  previous statement, went with design §16b item 3.

**Proof sketch.** A code-first interpreter in three parts. (i) **Startup.**
Skip the doubled `bits s` region and its separator by a finite-state pair
scan (the budget is not read). Then canonize `α` as the chapter-1 startup
does (`Turing.universalCanonTM`: extract the undoubled code into a buffer,
run the scheme's canonizer on it), leaving the canonical table
`serialize (decode α)` on a table tape and the initial state on a state tape.
This is a fixed computation on the fixed `α`, so its cells are a constant
depending only on `α` (`Turing.MultiTapeTM.spaceUsed_le_mul_succ` at the
canonizer's halting time), absorbed into `C`; the effective scheme supplies
no bound linear in `|α|`, and none is claimed. (ii) **Input device** (H5,
the binary-position device). The simulated input head runs over the
verbatim `x` region, the physical head in lockstep. The device keeps the
simulated position `0, …, |x| + 1` as a binary word of `posWidth |x|`
digits, moved with the head by the counter rows (`Turing.incrementTM`,
`Turing.decrementTM`); at position `0`, whose physical cell holds the
separator's `true`, it supplies a blank read and suppresses outward moves, as
`moveInputPos` clamps. Its cells are `O(logSpace |x|)`. The chapter-1
interpreter's device cannot serve: its fourth tape holds a unary boundary
marker whose head `applyRecord` moves with the input head
(`Turing.universalInterpreter`), so that tape uses one plus the largest
simulated input position reached, `Θ(|x| + 1)` cells on a full scan, which a
budget `s = o(|x|)` does not cover (Finding B). (iii) **Step block** (H2). Each round
looks up the record of the state, the input read and the work read in the
table, writes and moves on the simulated work tape — held cell for cell on
one real tape, so its visited cells are exactly the coded machine's, at most
`s` — installs the successor state, forwards the record's emission verbatim,
and halts exactly when the successor is halt. Its scratch is
`O(|table| + 1)`, a constant for fixed `α`. Hence `SU` emits the coded
machine's output and visits at most `C_α + s + O(logSpace |x|)` cells, which
is at most `C · (s + logSpace |x| + 1)`. Fill obligations, named: the H2 step
block at one coded work tape with its head envelope; the H5 binary-position
device with the boundary emulation; the startup (header skip, buffered
canonization); the per-code constant ledger. -/
theorem space_universal :
    ∃ SU : FinTM Bool, ∀ α : List Bool, ∃ C : ℕ, 0 < C ∧
      ∀ (s : ℕ) (x output : List Bool) (t : ℕ),
        ((TimeHierarchy.code).decode α).toFinTM.ComputesInTime x output t →
        ((TimeHierarchy.code).decode α).toFinTM.tm.spaceUsed
            (((TimeHierarchy.code).decode α).toFinTM.tm.initCfg x) t ≤ s →
          ∃ t' : ℕ,
            SU.ComputesInTime (pairEncode (Nat.bits s) (pairEncode α x)) output t' ∧
            SU.tm.spaceUsed
                (SU.tm.initCfg (pairEncode (Nat.bits s) (pairEncode α x))) t'
              ≤ C * (s + logSpace x.length + 1) := by
  sorry

/-- **The space hierarchy theorem** ([AB09, Theorem 4.8]; [SHL65] through
[AB09]; spec, fill pending — phase P4.3, sketch moved to the window route
2026-10-12 by design §16b item 3, statement gate pending): for
space-constructible `f` and `g`, if every constant multiple of `f` is
eventually below `g` (that is, `f = o(g)`), then `SPACE f ⊊ SPACE g`.
Constant-factor hypothesis — no square and no logarithmic term, by a
universal simulation with constant-factor space overhead (the
self-application universal `U₀` of the sketch, the sibling of
`Complexity.space_universal`); both constructibility hypotheses are the
book's, and the proof uses `g`'s witness and floor but, of `f`'s, only the
bundled floor (recorded here, seeded to the audit). Positivity of both bounds
is automatic from the bundled `logSpace` floor, so the P0 zero-bound
convention needs no side condition.

**Proof sketch.** *Inclusion.* `hfg` at `A = 1` gives `f n ≤ g n` from some
`N` on; below `N` each `f n` is at most `F := max_{n<N} f n` times
`g n ≥ 1` (`g`'s floor), so `f ≤ max F 1 · g` everywhere and
`Complexity.SPACE.mono_const` applies.

*The universal machine `U₀`.* One fixed machine for the scheme
`Complexity.TimeHierarchy.code`: on an input `x = pairEncode α w` it canonizes
`α` from the doubled prefix (the chapter-1 startup, `Turing.universalCanonTM`),
returns its input head to the origin, and simulates the coded machine on `x`
itself — self-application, so no `preTM` copy is needed — with its own input
head as the simulated one (H5's native device: the simulated input is all of
`U₀`'s input, so its left boundary is a real blank and no position is stored)
and the H2 step block on the canonical table. Its forward ledger: for each
`α` a constant `C_α` such that whenever the coded machine halts on `x` with
some output, having visited at most `s` cells, `U₀` halts on `x` with the
same output, having visited at most `C_α · (s + 1)` cells. This is
`space_universal`'s forward clause with the native device in place of the
binary-position one, hence without its logarithmic addend; only this
direction is used.

*The diagonalizer `D`.* On input `x` with `n = |x|`, over the record alphabet:
(i) validate the input (`Turing.inputFoldTM`, R8.5d; decision O6), so that
`D`'s space is bounded on foreign rich inputs, as
`Turing.FinTM.alphabet_reduction_spaceUsed` requires, and compute
`bits (g n)` by `g`'s witness, captured on a work tape, in `O(g n)` cells;
(ii) form the radius `r = a · g n` for a fixed `a ≥ 1`
(`a = 1` suffices, the code-dependent constant being paid by the hypothesis
below; a power of two costs only low zero digits) and write `U₀`'s initial
record on `x` at radius `r`, tagged with the empty-output summary
(`Turing.exists_recordInitTM`); (iii) run the H3 windowed runner: each round
tests the record for a halted state (`Turing.exists_recordTestTM`), else
applies one step of `U₀` (`Turing.exists_recordStepTM`, whose `no` verdict
is the window exit), the tag updated by the three-valued output summary
`Turing.outSummary` (append-compatible, `Turing.outSummary_append_congr`;
coded in `Fin 3` by design §12.8a decision O4), so the emitted word is
never buffered (W1). The rounds are driven by the configuration-count clock,
the rich counter loop (`Turing.counterLoopTMVia`, §12.7 and R8.0b) on an
all-`true` word of width `W = |Q₀| + posWidth n + 3 · k₀ · (2r + 1) + 1`,
where `Q₀` and `k₀` are `U₀`'s states and tape count. Its value `2^W - 1`
exceeds `Turing.FinTM.configBound U₀ n r`, which is at most
`2^(|Q₀| + posWidth n + 3 · k₀ · (2r + 1))`, each of its four factors being
at most a power of two. (iv) Answer `false` if the runner stopped at a halted
record with summary `accept` (output exactly `[true]`,
`Turing.outSummary_eq_accept_iff`), and `true` on every other exit: halted
with another output, window exit, or clock exhaustion. `D` halts on every
input. Its cells are the witness's `O(g n)`, the record's
`k₀ · (2r + 1) + posWidth n + k₀ + 4` (`Turing.recordLength`), the record
rows' `O(record length)` scratch and the clock's `W`: all `O(g n)` with
constants depending only on `U₀` and `g`'s witness, **uniformly in the code
part of `x`**, because the window, not `U₀`'s constant, bounds the
simulation (round-1 finding 5); the `posWidth n = O(logSpace n)` terms are
absorbed by `g`'s floor. After the alphabet reduction, the language `L_D`
that `D` decides lies in `SPACE g`.

*`L_D ∉ SPACE f`.* Suppose `M` decides `L_D` within `c₀ · f n` cells. Then
`M` halts within `configBound M n (c₀ · f n)` steps
(`Turing.FinTM.ComputesInTime.of_spaceUsed_le`), and its space bound holds at
every time (`Turing.MultiTapeTM.spaceUsed_mono` up to the halt, the halted
configuration frozen after it). The space-faithful normal form
`Turing.FinTM.one_work_tape_binary_spaceUsed` gives a one-work-tape binary
`M'` within `c · (c₀ · f n + 1)` cells. Relabel it to a coded machine `N`
(`Turing.exists_codeTM`, plus the space clause it does not state:
relabelling states leaves tapes and heads untouched,
`Turing.MultiTapeTM.relabelState_runFrom_init`) and set
`α_M := code.encode N`, so that `code.decode α_M = N`. Pad the **payload**,
never the code: on `x = pairEncode α_M w`, `U₀` outputs `N`'s verdict
`[x ∈ L_D]` within `C_{α_M} · (c · (c₀ · f n + 1) + 1) ≤ A · f n` cells,
where `A := C_{α_M} · (c · c₀ + c + 1)`, using `1 ≤ f n`. The hypothesis
`hfg` at this one `A` gives `N₀` with `A · f n ≤ g n ≤ r` for `n ≥ N₀`;
take `w := List.replicate N₀ true`. Then every configuration of `U₀`'s run
on `x` up to its halt is in the radius-`r` window, since each
tape's visited cells form an interval around `0` of size at most `r`
(`Turing.MultiTapeTM.abs_pos_lt_card_visited`) and every nonblank cell was
visited (`Turing.MultiTapeTM.mem_visited_of_ne_none`); and the halt comes by
step `configBound U₀ n r` (`ComputesInTime.of_spaceUsed_le` at the bound
`r`), before the clock runs out. So the runner stops at `U₀`'s halted record,
whose summary is `accept` exactly when `x ∈ L_D`, and `D` answers the
opposite: `x ∈ L_D ↔ x ∉ L_D`, a contradiction. Fill obligations, named in
the host vocabulary of design §14: `U₀` with its forward ledger (the H2 step
block at one coded work tape, H5's native input device, the chapter-1
startup), a public row as H2's named consumer, not a private host of this
proof; the H3 windowed runner at `U₀` with the output-summary tag, over the
record rows `exists_recordInitTM` (record-table row 18; row 17,
`exists_recordTemplateTM`, beneath it), `exists_recordTestTM` and
`exists_recordStepTM`, clocked by `counterLoopTMVia`; the radius and
clock-width phases (`g`'s witness captured, radius digits, width expansion);
the window-containment lemma from the visited-interval facts; the space
clause of `exists_codeTM` and the all-times space bound of a decider; the
contradiction arithmetic; `D`'s `DecidesInSpace` packaging through the
alphabet reduction. -/
theorem space_hierarchy (f g : ℕ → ℕ) (hf : SpaceConstructible f)
    (hg : SpaceConstructible g)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * f n ≤ g n) :
    SPACE f ⊂ SPACE g := by
  sorry

/-- **`L ⊊ PSPACE`** — the strict step of the p. 92 chain ([AB09, §4.3.2,
"the hierarchy theorems imply `L ⊊ PSPACE`"]; spec, fill pending).

**Proof sketch.** `Complexity.space_hierarchy` at `f := logSpace`,
`g := fun n => n + 1` (both constructible — the received
`Complexity.spaceConstructible_logSpace` and
`Complexity.spaceConstructible_linear` of phase P4.1; domination:
`A · logSpace n ≤ n + 1` eventually, a logarithm-versus-identity
inequality), then `SPACE (n + 1) ⊆ PSPACE`
(`Complexity.space_poly_subset_PSPACE` at degree one) and strictness
transports along the inclusion. -/
theorem LOGSPACE_ssubset_PSPACE : LOGSPACE ⊂ PSPACE := by
  sorry

/-- **`SPACE(n + 1) ≠ NP`** ([AB09, Exercise 3.2], stated at the positive
normalization `n + 1` per the P0 convention — the literal `SPACE(n)` is the
zero-work-tape class; spec, fill pending). Neither inclusion between the
two classes is claimed, matching the book's remark.

**Proof sketch.** Suppose `SPACE (n + 1) = NP`. `NP` is closed downward
under `≤ₚ` (the chapter-2 bounded-certificate transport — a derived
obligation from `Complexity.mem_NP_iff_exists_length_le`, Exercise 2.1's
bounded form, named for the brief). Padding transfers space bounds down:
for `L ∈ SPACE (n² + 1)`, the padded language
`L' := {y | ∃ x ∈ L, y = pairEncode x (List.replicate (|x|²) true)}` —
membership restricted to padded members of `L` (round-2 finding 5); padded
length exactly `m = n² + 2n + 2`, syntax validated — lies in `SPACE (m + 1)` in the padded
length (validate, then run the `L`-decider on the first component; the pad
supplies the room — the chapter-2 padding-cluster discipline,
`EXP_subset_NEXP`'s precedent), so `L' ∈ NP` by the assumption, and
`L ≤ₚ L'` by the padding reduction (a `polyUnary` emitter; the **unpadded**
language reduces to the **padded** one), so `L ∈ NP = SPACE (n + 1)` — the
`NP` pullback composing the reduction with the bounded-certificate verifier
at the reduction's polynomial output length. Hence
`SPACE (n² + 1) ⊆ SPACE (n + 1)`, contradicting
`Complexity.space_hierarchy` at the constructible pair
(`Complexity.spaceConstructible_linear`,
`Complexity.spaceConstructible_poly` at degree two; domination
`A · (n + 1) ≤ n² + 1` eventually). Fill obligations, named: the `NP`
`≤ₚ`-closure lemma; the padded-language space decider; the padding
reduction machine; the strictness extraction. -/
theorem SPACE_linear_ne_NP : SPACE (fun n => n + 1) ≠ NP := by
  sorry

end Complexity
