/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Simulation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: the calling convention

The vocabulary module of the machine-construction library
(`machine-library-design.md`, design frozen 2026-10-03): the single seam
notion that the library's control combinators speak, plus the pure list/
arithmetic functions that the primitive contracts in
`TCSlib.Complexity.TuringMachine.Build.Primitives` are stated against.

**Status: proved.** This module is fully proved (definitions, two glue
lemmas, and the two `incFixed` laws promoted at CH34-D4), and the sibling
`Build` modules' contracts stated against
it are now all proved as well (library fill batches and the emitter
increment; zero sorries). The `Build` surface was new Chapter-1 growth,
audited in the shared infrastructure and emitter rounds
(`audits/ch1-infra-*`, `audits/emitter-*`).

## The seam notion

The model already gives *whole* machines a clean boundary: read-only input,
blank work tapes, append-only output, start at `Turing.MultiTapeTM.initCfg`.
The library therefore needs a configuration discipline only where a
construction crosses an *internal* seam — the round boundary of the loop
combinator and the entry of a wrapped subroutine. `Turing.Cfg.ofWords` is
that discipline: control at a designated anchor, input head at its initial
position, every work tape holding one word from the origin
(`Turing.FinTM.bufferTape`) with its head at the origin, output empty. A
loop body's contract is "`ofWords` in, `ofWords` out", and — per the frozen
design decision — the body *restores its own scratch to blank* (its scratch
words are `[]` on both sides of the contract) rather than relying on a
generic clearing pass.

## Main definitions

* `Turing.Cfg.ofWords` — the canonical seam configuration: anchor state,
  input head at 1, work tape `i` holding word `w i` from the origin, heads
  at the origin, empty output.
* `Turing.Cfg.ofWords_state`, `_inputPos`, `_workTapePos`, `_output` — the seam's fields beside
  `Turing.Cfg.ofWords_workTapes` (the ND inventory API, C1's pre-ship inventory, 2026-10-17).
* `Turing.splitAtLastTrue` — strip a marker suffix: the prefix before the
  last `true`, or `none` if the word is all `false` (the audited marker
  discipline of the Chapter-2 Exercise-2.1 construction).
* `Turing.solveSplit` — least solution `i ≤ n` of the padding length
  equation `i + C·(i+1)^e = n`, or `none` (the split-search discipline of
  the padding constructions).
* `Turing.incFixed_replicate_true_append`, `Turing.incFixed_eq_none_iff_replicate` — the
  increment's carry through a `true` prefix and its overflow criterion (CH34-D4).
* `Turing.incFixed` — little-endian fixed-width binary increment with
  explicit overflow (`none`), width preserved (the enumerator's counter
  discipline; width zero overflows immediately).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2: the k-tape machine model the
  seams are stated over.)
-/

namespace Turing

variable {k : ℕ} {State : Type*}

/-- The canonical seam configuration of the machine-construction library:
control at the anchor state `q`, input head at its initial position `1`,
work tape `i` holding the word `w i` written from the origin
(`Turing.FinTM.bufferTape`), every work head at the origin, and the output
empty. Loop-round and wrapper-entry contracts are stated as equations
between `runFrom` results and `ofWords` configurations; a body that owns
scratch tapes lists them with word `[]` on both sides of its contract
(body-restores-scratch, the frozen design decision 9.2). -/
def Cfg.ofWords {input : List Bool} (q : State) (w : Fin k → List Bool) :
    Cfg k Bool State input :=
  ⟨some q, 1, fun i => FinTM.bufferTape (w i), fun _ => 0, []⟩

/-- A machine's genuine initial configuration is the seam configuration at
its start state with every tape word empty: `Cfg.init` has blank tapes and
`Turing.FinTM.bufferTape [] = fun _ => none`. This is the lemma that lets a
combinator's startup phase begin from a seam rather than from a bespoke
initialization invariant. -/
lemma initCfg_ofWords (tm : MultiTapeTM k Bool State) (x : List Bool) :
    tm.initCfg x = Cfg.ofWords tm.q₀ (fun _ => []) := by
  simp only [MultiTapeTM.initCfg, Cfg.init, Cfg.ofWords, FinTM.bufferTape_nil]

/-- The seam words of a configuration are read back literally: at a seam,
work tape `i` holds exactly `w i` on cells `0, …, |w i| − 1` and blanks
elsewhere. Unfolds `Cfg.ofWords` for consumers that reason cell-wise. -/
lemma Cfg.ofWords_workTapes {input : List Bool} (q : State)
    (w : Fin k → List Bool) (i : Fin k) :
    (Cfg.ofWords (input := input) q w).workTapes i = FinTM.bufferTape (w i) :=
  rfl

/-- The seam's other fields (the ND inventory API, 2026-10-17; C1 wave 1's route inventory): the
state is `some q`, `(Cfg.ofWords q w).state = some q`. -/
theorem Cfg.ofWords_state {input : List Bool} (q : State) (w : Fin k → List Bool) :
    (Cfg.ofWords (input := input) q w).state = some q :=
  rfl

/-- At a seam the input head is at its initial position: `(Cfg.ofWords q w).inputPos = 1`. -/
theorem Cfg.ofWords_inputPos {input : List Bool} (q : State) (w : Fin k → List Bool) :
    (Cfg.ofWords (input := input) q w).inputPos = 1 :=
  rfl

/-- At a seam every work head is at the origin: `(Cfg.ofWords q w).workTapePos i = 0`. -/
theorem Cfg.ofWords_workTapePos {input : List Bool} (q : State) (w : Fin k → List Bool)
    (i : Fin k) : (Cfg.ofWords (input := input) q w).workTapePos i = 0 :=
  rfl

/-- At a seam the output is empty: `(Cfg.ofWords q w).output = []`. -/
theorem Cfg.ofWords_output {input : List Bool} (q : State) (w : Fin k → List Bool) :
    (Cfg.ofWords (input := input) q w).output = [] :=
  rfl

/-- Strip a marker suffix: the prefix of `v` before its **last** `true`, or
`none` when `v` is all `false`. This is the Chapter-2 Exercise-2.1 marker
discipline (split at the last `true`; an all-`false` certificate region is
a rejection), stated once as a pure function so that machine contracts and
the chapter-side semantic lemmas name the same operation. -/
def splitAtLastTrue (v : List Bool) : Option (List Bool) :=
  match v.reverse.dropWhile (fun b => !b) with
  | true :: rest => some rest.reverse
  | _ => none

/-- Least index `i ≤ n` solving the padding length equation
`i + C·(i+1)^e = n`, or `none` when no solution exists. Strict monotonicity
of `i ↦ i + C·(i+1)^e` makes the solution unique; the machine contract
`Turing.FinTM.computesFunInTime_splitSolve` performs this bounded search. -/
def solveSplit (C e n : ℕ) : Option ℕ :=
  (List.range (n + 1)).find? fun i => i + C * (i + 1) ^ e == n

/-- Little-endian fixed-width binary increment with explicit overflow:
`incFixed w` is the successor word of the same length, or `none` when `w`
is all `true` (overflow) — in particular width zero overflows immediately,
matching the enumerator's audited counter discipline. -/
def incFixed : List Bool → Option (List Bool)
  | [] => none
  | false :: rest => some (true :: rest)
  | true :: rest => (incFixed rest).map (false :: ·)

/-- The empty word overflows: `incFixed [] = none`. -/
theorem incFixed_nil : incFixed [] = none :=
  rfl

/-- A low `false` absorbs the carry: `incFixed (false :: w) = some (true :: w)`. -/
theorem incFixed_false_cons (w : List Bool) : incFixed (false :: w) = some (true :: w) :=
  rfl

/-- A low `true` passes the carry on: `incFixed (true :: w) = (incFixed w).map (false :: ·)`. -/
theorem incFixed_true_cons (w : List Bool) :
    incFixed (true :: w) = (incFixed w).map (false :: ·) :=
  rfl

/-- **The increment keeps the width:** `incFixed w = some v → |v| = |w|`.

**Proof sketch.** Induct on `w` through the three case equations: the empty word overflows, a
low `false` becomes `true`, and a low `true` becomes `false` before the incremented tail. -/
theorem incFixed_length {w v : List Bool} (h : incFixed w = some v) : v.length = w.length := by
  induction w generalizing v with
  | nil =>
    rw [incFixed_nil] at h
    exact absurd h (by simp)
  | cons b w ih =>
    cases b with
    | false =>
      rw [incFixed_false_cons, Option.some.injEq] at h
      subst v
      rfl
    | true =>
      rw [incFixed_true_cons] at h
      cases he : incFixed w with
      | none =>
        rw [he] at h
        exact absurd h (by simp)
      | some z =>
        rw [he, Option.map_some, Option.some.injEq] at h
        subst v
        rw [List.length_cons, List.length_cons, ih he]

/-- `Turing.incFixed` carries through a prefix of `true` bits: the prefix
`1ⁿ` becomes `0ⁿ` and the remainder `w` is incremented, the width is kept,
and the whole word overflows exactly when `w` does. Shared by the catalog's
increment routine and the `EXPCOM` deadline guard (CH34-D4).

**Proof sketch.** Induct on `n`. Each leading `true` is one step of the carry
clause of `incFixed`, which prepends one `false` to the incremented tail. -/
theorem incFixed_replicate_true_append (n : ℕ) (w : List Bool) :
    incFixed (List.replicate n true ++ w) =
      (incFixed w).map (List.replicate n false ++ ·) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [List.replicate_succ, incFixed, ih, Option.map_map, Function.comp_def]

/-- **The overflow criterion of `Turing.incFixed`**: the increment overflows
exactly on the all-`true` word (the empty word included). The public home of
the criterion, promoted per the fills-6 request F6-1(e) (CH34-D4).

**Proof sketch.** Induct on `u`. The empty word overflows. A leading `false`
never overflows, and the word is then not all `true`. After a leading `true`,
the word overflows exactly when its tail does, and is all `true` exactly when
its tail is. -/
theorem incFixed_eq_none_iff_replicate (u : List Bool) :
    incFixed u = none ↔ u = List.replicate u.length true := by
  induction u with
  | nil => simp [incFixed]
  | cons b u ih =>
    cases b <;> simp [incFixed, ih, List.replicate_succ]

/-- **Emitter-increment vocabulary** (design §11): least
solution `i ≤ n` of the width-parametric split equation `i + f i = n`, or
`none` — the generalization of `Turing.solveSplit` from the hardwired
polynomial family to an arbitrary width function. At
`f = fun i => C * (i + 1) ^ e` this definitionally recovers
`solveSplit C e n`. Customers: the 3A-continuation's exponential padding
equation (through `computesFunInTime_splitSolveWith`) and later padding
arguments. No machine content: `List.range` search, first match. -/
def solveSplitWith (f : ℕ → ℕ) (n : ℕ) : Option ℕ :=
  (List.range (n + 1)).find? fun i => i + f i == n

/-- **Emitter-increment vocabulary** (design §11): split off
the leading unary token — the maximal `true`-prefix together with its
terminating `false` delimiter — returning the token and the remainder. A
word with no delimiter yields the whole word as an unterminated token with
empty remainder; the empty word yields two empty words; a leading `false`
is the length-zero token `[false]`. This operation consumes **unary
tokens** — the shared atom of the serialization grammars (unary indices
with terminators). It does not consume standalone single-bit markers or
polarity bits: `unaryTokenSplit [true, false, true] =
([true, false], [true])`, a terminated unary-one token, not a lone
`true` marker — scanners handle markers and polarity by their own
grammar states (emitter-infra round-1 audit, finding 4). Customers: the
3B continuation's streaming scanner, the Cook-Levin emitter's index
reads (4A), 4B's dual scanner. No machine content: structural recursion
on the word. -/
def unaryTokenSplit : List Bool → List Bool × List Bool
  | [] => ([], [])
  | false :: rest => ([false], rest)
  | true :: rest =>
    let (tok, r) := unaryTokenSplit rest
    (true :: tok, r)

end Turing
