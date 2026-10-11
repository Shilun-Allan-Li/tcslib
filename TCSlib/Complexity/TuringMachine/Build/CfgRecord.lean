/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Nat.Bits
import TCSlib.Complexity.TuringMachine.Build.Catalog
import TCSlib.Complexity.TuringMachine.SymbolLift

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: configuration records over a rich alphabet (§12.8)

The record carrier of the §12.8 rich-alphabet design
(`machine-library-design.md` §12.8a §2, decision 12.8.1): a configuration of a
`Bool` machine with work tapes inside a radius-`s` window, written as a list of
fields over the rich alphabet `Turing.RecSym`. Records are what the
configuration-graph searches of chapter 4 (the reachability simulation of
`NSPACE` in `DSPACE` by breadth-first search, Savitch's midpoint recursion)
keep on their tapes, and the record rows are the machines that read, step and
compare them.

**Status: statements.** The carrier, the record and its predicates are real
definitions, and `Turing.cfgRecord_length` is proved. Every other result is
sorried with a proof sketch, pending the §12.8 fill: the pure decoding facts
and the three record rows.

## Design

* **One cell per simulated cell.** A tape field holds the `2s + 1` window cells
  of one work tape, each a content track and a head-mark track
  (`Turing.RecSym.cell`). The input position is a fixed-width binary field of
  digits, `O(log n)` cells, and the state and the tag take one cell each. A
  record therefore has `k(2s + 1) + posWidth n + 2` cells and `k + 2`
  separators, which is `O(S n)` at radius `O(S n)` for `S ≥ log`.
* **Blank-separated fields** (`Turing.joinFields`): every field is a §12.6
  delimited word in place (`Turing.fieldsTape_field`), so the framed catalog
  rows apply field by field, and no field is empty, so two blanks end a table.
* **Digits are the lift's `e`.** `Turing.RecSym.digitEmb` is the embedding
  along which the `Bool` counter rows run on rich tapes
  (`Turing.MultiTapeTM.liftSymbols`), and the native input of a rich
  simulator is the input's image under it.
* **The window predicate** `Turing.Cfg.InWindow` lives here, relocated
  verbatim from `TCSlib.Complexity.ClassPSPACE.TQBF` (decision 12.8.2), which
  now imports it, so the record carrier and the adjacency codec share one
  definition.
* **Record rows are existential modules** in the `exists_installCallTM` style:
  a machine, entry and verdict anchors, and a linear first-return bound, with
  every head, the input position and the scratch restored.

## Main definitions

* `Turing.Cfg.InWindow` — the radius-`s` window predicate (relocated).
* `Turing.RecSym`, `Turing.RecSym.digitEmb` — the record alphabet and its
  digit embedding.
* `Turing.binDigits`, `Turing.posWidth` — fixed-width binary digits and the
  input-position width.
* `Turing.cfgRecord` — the record of a configuration.
* `Turing.RecordValid`, `Turing.RecordAt` — valid records, and a record laid
  out at a head.

## Main results

* `Turing.cfgRecord_length` — a record has `k + 3` fields.
* `Turing.cfgRecord_inj` — on windowed configurations, records agree exactly
  when configuration cores and tags do (statement).
* `Turing.recordValid_iff` — validity as a field-by-field shape condition
  (statement).
* `Turing.exists_recordStepTM`, `Turing.exists_recordEqTM`,
  `Turing.exists_recordTestTM` — the record rows R8.7: one simulated step, record
  equality, and a test of the state and tag (statements).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.1: the configuration graph and
  Claim 4.4(1), the `O(S(n))`-bit description of a configuration;
  Theorem 4.2(iii) and Theorem 4.14 (Savitch), whose simulations search the
  graph keeping configuration descriptions on work tapes. The record adds an
  `O(log n)` input-position field, as the book's description does.)
-/

namespace Turing

/-! ### The window predicate -/

/-- A configuration lies **in the radius-`s` window** when every work head
sits within `[-s, s]` and every work cell outside `[-s, s]` is blank — the
side condition under which the packaged codec of
`Complexity.exists_adjacency_codec_cnf` is faithful. (The input head needs no
clause: its type bounds it.) It is equally the side condition under which a
configuration record determines its configuration (`Turing.cfgRecord_inj`);
relocated here from `TCSlib.Complexity.ClassPSPACE.TQBF` (decision 12.8.2). -/
def Cfg.InWindow {k : ℕ} {Symbol State : Type} {x : List Symbol} (s : ℕ)
    (c : Cfg k Symbol State x) : Prop :=
  (∀ i, |c.workTapePos i| ≤ (s : ℤ)) ∧
  ∀ (i : Fin k) (z : ℤ), (s : ℤ) < |z| → c.workTapes i z = none

/-! ### The record alphabet -/

/-- **The record alphabet** (design §12.8a §2) over machine states `Q` and tags
`T`: binary digits, simulated work cells with a head-mark track, the state
cell, and the tag cell. Fields of a record are separated by blank cells. -/
inductive RecSym (Q T : Type) where
  /-- a binary digit: the input-position field, counters, and the native input -/
  | digit (b : Bool)
  /-- one simulated work cell: its content and whether the head is on it -/
  | cell (content : Option Bool) (mark : Bool)
  /-- the state cell, `none` for halted -/
  | st (q : Option Q)
  /-- the tag cell: a summary of what the run has emitted -/
  | tag (τ : T)
deriving DecidableEq

/-- The record alphabet is finite when the states and tags are; this is the
`Fintype` instance `Turing.FinTM.alphabet_reduction` needs. -/
instance recSymFintype (Q T : Type) [Fintype Q] [Fintype T] : Fintype (RecSym Q T) :=
  derive_fintype% _

/-- **The digit embedding** (design §12.8a §2): `Bool` into the record alphabet
by `Turing.RecSym.digit`. It is the `e` along which `Bool` rows and the `Bool`
input are lifted to rich tapes (`Turing.MultiTapeTM.liftSymbols`). -/
def RecSym.digitEmb (Q T : Type) : Bool ↪ RecSym Q T :=
  ⟨RecSym.digit, fun _ _ h => by cases h; rfl⟩

/-! ### The record -/

/-- **Fixed-width binary digits** (design §12.8a §2): the `w` low bits of `v`,
least significant first. -/
def binDigits (w v : ℕ) : List Bool := (List.range w).map v.testBit

/-- **The input-position width** (design §12.8a §2) at input length `n`: the
bit length of `n + 1`, so that `2 ^ posWidth n > n + 1` and every input
position `0, …, n + 1` has a distinct `Turing.binDigits` code. -/
def posWidth (n : ℕ) : ℕ := (Nat.bits (n + 1)).length

/-- **The configuration record** (design §12.8a §2) of `c` at window radius
`s` with tag `τ`: `k + 3` fields. Field `0` is the state, field `1` the input
position in `Turing.binDigits` of width `Turing.posWidth |x|`, fields `2` to
`k + 1` the window cells `-s, …, s` of each work tape with their head marks,
and field `k + 2` the tag. The output tape is not recorded; the tag summarizes
it. -/
def cfgRecord {k : ℕ} {Q T : Type} {x : List Bool} (s : ℕ) (c : Cfg k Bool Q x) (τ : T) :
    List (List (RecSym Q T)) :=
  [RecSym.st c.state] ::
    ((binDigits (posWidth x.length) c.inputPos.val).map RecSym.digit) ::
    (((List.finRange k).map fun i => (List.range (2 * s + 1)).map fun j =>
      RecSym.cell (c.workTapes i ((j : ℤ) - s)) (decide (c.workTapePos i = (j : ℤ) - s))) ++
    [[RecSym.tag τ]])

/-- **Record length** (design §12.8a §2): a record has `k + 3` fields, whatever
the configuration, radius and tag. -/
theorem cfgRecord_length {k : ℕ} {Q T : Type} {x : List Bool} (s : ℕ) (c : Cfg k Bool Q x)
    (τ : T) : (cfgRecord s c τ).length = k + 3 := by
  simp [cfgRecord]

/-- **Canonical decoding** (design §12.8a §2). On windowed configurations of
one input, records agree exactly when the configurations agree on state, input
position, work tapes and work heads, and the tags agree. The output is not
compared, so this is injectivity on the configuration core, the vertex
quotient of the configuration graph.

**Proof sketch.** Compare the fields. The state field gives the state. The
position field is `Turing.binDigits` at a width with `2 ^ posWidth |x| >
|x| + 1`, which is injective on values `≤ |x| + 1`, the range of input
positions. For tape `i`, the content track gives the cells in `[-s, s]`, and
outside it both configurations are blank by the window hypothesis. The mark
track has exactly one mark, at the head, which lies in `[-s, s]`. The tag field
gives the tag. -/
theorem cfgRecord_inj {k : ℕ} {Q T : Type} {x : List Bool} (s : ℕ) {c d : Cfg k Bool Q x}
    {τ τ' : T} (hc : c.InWindow s) (hd : d.InWindow s) :
    cfgRecord s c τ = cfgRecord s d τ' ↔
      (c.state = d.state ∧ c.inputPos = d.inputPos ∧ c.workTapes = d.workTapes ∧
        c.workTapePos = d.workTapePos) ∧ τ = τ' := by
  sorry

/-- **Valid records** (design §12.8a §2): the field list is the record, at
radius `s`, of some windowed configuration on some input of length `n`, with
some tag. -/
def RecordValid (k n s : ℕ) (Q T : Type) (fs : List (List (RecSym Q T))) : Prop :=
  ∃ (x : List Bool) (c : Cfg k Bool Q x) (τ : T), x.length = n ∧ c.InWindow s ∧
    cfgRecord s c τ = fs

/-- **Validity is a shape condition** (design §12.8a §2). A field list is a
valid record exactly when it has `k + 3` fields: a state cell; `posWidth n`
digits of a value at most `n + 1`; for each tape, `2s + 1` work cells of which
exactly one carries the head mark; and a tag cell. Each conjunct is a fold of
one field, which is how a validity machine checks it.

**Proof sketch.** Forward: read the shape off `Turing.cfgRecord`, with the mark
at index `pos + s` of each tape field, which is in range by the window
hypothesis. Backward: take the input `List.replicate n false`, the state and
the tag from their cells, the input position from the digits, and for tape `i`
the cell at `z` from index `z + s` of its field when `|z| ≤ s`, and blank
otherwise, with the head at the mark minus `s`. This configuration is windowed
and its record is the given list. -/
theorem recordValid_iff {k : ℕ} {Q T : Type} (n s : ℕ) (fs : List (List (RecSym Q T))) :
    RecordValid k n s Q T fs ↔
      fs.length = k + 3 ∧
      (∃ q : Option Q, fs[0]? = some [RecSym.st q]) ∧
      (∃ v ≤ n + 1, fs[1]? = some ((binDigits (posWidth n) v).map RecSym.digit)) ∧
      (∀ i : Fin k, ∃ (cs : ℕ → Option Bool) (m : ℕ), m < 2 * s + 1 ∧
        fs[i.val + 2]? = some ((List.range (2 * s + 1)).map fun j =>
          RecSym.cell (cs j) (decide (j = m)))) ∧
      (∃ τ : T, fs[k + 2]? = some [RecSym.tag τ]) := by
  sorry

/-- **A record at a head** (design §12.8a §2): tape `r` holds the field layout
of `fs` from its head, delimited by blanks at relative positions `-1` and
`|joinFields fs|`. The cells beyond the delimiters are arbitrary. -/
def RecordAt {K : ℕ} {Γ S : Type*} {x : List Γ} (d : Cfg K Γ S x) (r : Fin K)
    (fs : List (List Γ)) : Prop :=
  ∀ p : ℤ, -1 ≤ p → p ≤ ((joinFields fs).length : ℤ) →
    d.workTapes r (d.workTapePos r + p) = fieldsTape fs p

/-! ### R8.7 — the record rows -/

/-- **R8.7, one simulated step** (design §12.8a §3, GAP-4). For a fixed `Bool`
machine `M` and a tag update `upd` that ignores silent steps, there is a module
over the record alphabet with an entry and two distinct verdict anchors with
the following contract. Start it at its entry with the record of a windowed
configuration `c` at the head of tape `0`, its other tapes blank, and the
native input `x` as digits. It reaches a verdict within `C` times the record
length plus `|x| + 1`, and no verdict earlier. If `M.step c` is windowed, the
verdict is `yes` and the record interval holds the record of `M.step c`, with
tag `upd τ (M.outputSymbol c)`; otherwise the verdict is `no` and nothing has
changed. In both cases every head, the input position, the other tapes and the
output are restored. A halted `c` steps to itself with its tag unchanged, by
`hupd`.

**Proof sketch.** Compose by R2 seams, with no private trace. Read: `scanTM`
folds collect the state, the tag, and for each tape field the marked cell's
content and whether the mark is at an edge, moving between fields by `skipTM`.
Read the input symbol: copy the position field to a scratch digit tape
(`copyTM`), run the lifted `exists_inputSeekTM` on it, read the symbol, and
restore. Dispatch on `M.tr` over the finite data. Apply: `scanTM` maps rewrite
the marked content, the state and the tag; delay steps shift the marks; the
position field moves by the lifted increment or decrement on the scratch tape
and is copied back; a mark leaving the window selects `no` before anything is
written. Rewind by `skipBackTM`. Each phase is linear in the record length or
in `|x|`. -/
theorem exists_recordStepTM {k : ℕ} {Q T : Type} [Fintype Q] [DecidableEq Q] [Fintype T]
    [DecidableEq T] (M : MultiTapeTM k Bool Q) (upd : T → Option Bool → T)
    (hupd : ∀ τ, upd τ none = τ) :
    ∃ (K : ℕ) (P : Type) (_ : Fintype P) (_ : DecidableEq P)
      (R : MultiTapeTM (K + 1) (RecSym Q T) P) (entry yes no : P) (C : ℕ), yes ≠ no ∧
      ∀ {x : List Bool} (s : ℕ) (c : Cfg k Bool Q x) (τ : T), c.InWindow s →
      ∀ d : Cfg (K + 1) (RecSym Q T) P (x.map (RecSym.digitEmb Q T)),
        d.state = some entry → RecordAt d 0 (cfgRecord s c τ) →
        (∀ j : Fin (K + 1), j ≠ 0 → ∀ p, d.workTapes j p = none) →
        ∃ t ≤ C * ((joinFields (cfgRecord s c τ)).length + x.length + 1),
          (∀ u < t, (R.runFrom d u).state ≠ some yes ∧ (R.runFrom d u).state ≠ some no) ∧
          ((M.step c).InWindow s →
            R.runFrom d t =
              { d with
                state := some yes
                workTapes := fun j q =>
                  if j = 0 ∧ d.workTapePos j ≤ q ∧
                      q < d.workTapePos j + ((joinFields (cfgRecord s c τ)).length : ℤ)
                    then fieldsTape (cfgRecord s (M.step c) (upd τ (M.outputSymbol c)))
                      (q - d.workTapePos j)
                  else d.workTapes j q }) ∧
          (¬ (M.step c).InWindow s → R.runFrom d t = { d with state := some no }) := by
  sorry

/-- **R8.7, record equality** (design §12.8a §3). There is a two-tape module
over the record alphabet with an entry and two distinct verdict anchors with
the following contract. Start it at its entry with field lists `fs` and `gs`,
of `k + 3` fields each, laid out at the heads of tapes `0` and `1`. It reaches
`yes` if `fs = gs` and `no` otherwise, within `C` times the length of `fs`'s
layout plus one, with no verdict earlier and nothing else changed. The input is
arbitrary and not read.

**Proof sketch.** For each of the `k + 3` fields, run `compareTM` framed
(`compareTM_run_ofCfg`) on the two current fields; on `false`, return `no`, and
on `true`, `skipTM` both tapes to the next field. After the last field, return
`yes`. Before the verdict, `skipBackTM` both heads over the fields crossed,
which have the same lengths on both tapes. Every phase is linear in the cells
of `fs` crossed. -/
theorem exists_recordEqTM (k : ℕ) (Q T : Type) [Fintype Q] [DecidableEq Q] [Fintype T]
    [DecidableEq T] :
    ∃ (P : Type) (_ : Fintype P) (_ : DecidableEq P) (R : MultiTapeTM 2 (RecSym Q T) P)
      (entry yes no : P) (C : ℕ), yes ≠ no ∧
      ∀ {x : List (RecSym Q T)} (fs gs : List (List (RecSym Q T))),
        fs.length = k + 3 → gs.length = k + 3 →
      ∀ d : Cfg 2 (RecSym Q T) P x, d.state = some entry → RecordAt d 0 fs → RecordAt d 1 gs →
        ∃ t ≤ C * ((joinFields fs).length + 1),
          (∀ u < t, (R.runFrom d u).state ≠ some yes ∧ (R.runFrom d u).state ≠ some no) ∧
          R.runFrom d t = { d with state := some (if fs = gs then yes else no) } := by
  sorry

/-- **R8.7, a test of state and tag** (design §12.8a §3). For a predicate `P`
on states and tags, there is a one-tape module over the record alphabet with an
entry and two distinct verdict anchors with the following contract. Start it
at its entry with the record of `c` with tag `τ` at its head. It reaches `yes`
if `P c.state τ` and `no` otherwise, within `C` times the record length plus
one, with no verdict earlier and nothing else changed. Consumers host it on a
record tape by R1 (`embedEmitTM`); the table search of the reachability
simulation tests for a halted accepting record this way.

**Proof sketch.** A `scanTM` fold reads the state field; `skipTM` crosses the
`k + 2` fields to the tag, a second fold reads the tag, and `skipBackTM`
returns over the fields crossed. Dispatch on `P` over the finite data. -/
theorem exists_recordTestTM {k : ℕ} {Q T : Type} [Fintype Q] [DecidableEq Q] [Fintype T]
    [DecidableEq T] (P : Option Q → T → Bool) :
    ∃ (P' : Type) (_ : Fintype P') (_ : DecidableEq P') (R : MultiTapeTM 1 (RecSym Q T) P')
      (entry yes no : P') (C : ℕ), yes ≠ no ∧
      ∀ {x : List Bool} (s : ℕ) (c : Cfg k Bool Q x) (τ : T) {y : List (RecSym Q T)}
        (d : Cfg 1 (RecSym Q T) P' y), d.state = some entry →
        RecordAt d 0 (cfgRecord s c τ) →
        ∃ t ≤ C * ((joinFields (cfgRecord s c τ)).length + 1),
          (∀ u < t, (R.runFrom d u).state ≠ some yes ∧ (R.runFrom d u).state ≠ some no) ∧
          R.runFrom d t = { d with state := some (if P c.state τ then yes else no) } := by
  sorry

end Turing
