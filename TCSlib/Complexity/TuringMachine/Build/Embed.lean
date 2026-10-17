/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.List.FinRange
import TCSlib.Complexity.TuringMachine.Simulation
import TCSlib.Complexity.TuringMachine.StateRenaming
import TCSlib.Complexity.TuringMachine.Build.Convention

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: bank embedding (R1)

The general tape-embedding layer of the machine-construction library
(`machine-library-design.md` §12, R1): a verified routine on its own
`m`-tape set runs on any injectively selected subset of a `k`-tape host's
work tapes, cost unchanged, everything else framed. This is the §5
deferral promoted — the design deferred the general form "until a third
site needs it", and the third, fourth, and fifth sites have arrived (the
chapter-1/2 retrofit families, the Hennie–Stearns conversion, the
two-work-tape universal machine). **Scope, stated precisely** (round-1
note R9): `ι` selects whole distinct physical tapes with coordinates
intact — it does not multiplex several virtual tapes onto zones of one
physical tape, shrink the tape count, or alter the source input word; the
Hennie–Stearns and universal-machine consumers get their zone/virtual-input
representation layers separately, with this module supplying only the
fixed-physical-bank routine relocation. It is the generic form of the private
`emitterBank*`/`emitterP2*` relocation families of
`TCSlib.Complexity.TuringMachine.Build.Primitives`, of the 4A chain's
`clBank*`/`clSlot*` families, and of the retained-tape disciplines that
`Build/Loop.lean` and `Build/Wrappers.lean` carry internally.

**Status: proved.** The transformers and configuration transports below
are real definitions, and every contract is proved: the §12 fill epochs
(gates closed 2026-10-09) and the later additive exports, the last of them
the guarded state transport (retrofit RB5, 2026-10-10).

## Design

Per frozen decision 12.4 there are **two named transformers over one
shared private core** (`embedActionCore`), so each spec stays crisp and a
consumer cites whichever fits:

* `Turing.embedSilentTM` — the W1/capture flavor: the embedded routine's
  emissions are recorded on a designated host work tape `cap` outside the
  selected bank, and the host's physical output stays silent.
* `Turing.embedEmitTM` — the E2/forwarding flavor: emissions pass to the
  host's physical output verbatim.

The two **closed** transformers preserve the source state type and map
the source halt to the host halt; their lockstep is unguarded, holding at
every time with the step count preserved exactly. The round-1 audit
(finding R1) refuted the earlier claim that live-return dispatch could be
left to the seam combinator: a source whose final transition emits and
halts loses that emission either way — the closed embedding is halted
after it, and a seam exit at the sole live state dispatches *before* it.
The **returning** flavors below repair this with an explicit halt-to-live
adapter built into the action core: `Turing.embedSilentRetTM` and
`Turing.embedEmitRetTM` run the source on states `S ⊕ Unit`, execute every
source action **through the halting transition** — the final emission
included — and land in the live return anchor `Sum.inr ()`, which a seam
then consumes as its left exit (`Turing.captureAction`'s and
`Turing.emitterRightTM`'s halt-to-live discipline, now exported).
`Turing.captureAction`/`Turing.capture_run` and
`Turing.emitAction`/`Turing.emit_run` are the fixed-shape precursors
(last-tape capture, identity selection); their statements are untouched.

## Main definitions

* `Turing.embedSilentCfg`, `Turing.embedEmitCfg` — a source configuration
  transported along `ι : Fin m ↪ Fin k`, with the unselected host tapes
  carried as frame parameters.
* `Turing.embedSilentTM`, `Turing.embedEmitTM` — the two closed machine
  transformers.
* `Turing.Cfg.select` — the selected bank of a host configuration, with empty output
  (moved from `Build/Contract.lean` at MIG-0b's layering split).
* `Turing.embedSilentRetTM`, `Turing.embedEmitRetTM` — the two returning
  transformers (round-1 repair R1): source halts land in the live return
  anchor `Sum.inr ()`, with the halting transition executed in full.

## Main results

* `Turing.embedEmitCfg_unselected`, `Turing.embedEmitCfg_select` — the frame export and
  the selection identity (moved from `Build/Contract.lean` at MIG-0b's layering split).
* `Turing.embedEmitCfg_eq`, `Turing.embedEmitCfg_mapState_eq`,
  `Turing.embedEmitCfg_ofWords_eq` — the R1 reconstruction lemma and its corollaries
  (MIG-0b; the wave-1 fill gate's major F1). `Turing.MultiTapeTM.runFrom_mapState_of_agreeOn`
  moved to `StateRenaming` at MIG-0b.
* `Turing.embedEmitTM_tr` — the forwarding transformer's transition at the action level:
  the source action on each selected tape, `(none, 0)` on every other tape, and the input
  move, output and successor state unchanged (12.2c item 6's export).
* `Turing.embedSilentCfg_cap` — the silent transport's capture tape and head, off the
  selection (the C1-A assembly gate's export, 2026-10-14).
* `Turing.embedSilentTM_runFrom`, `Turing.embedEmitTM_runFrom` — lockstep:
  the transported run is the transport of the source run, same step count.
* `Turing.embedSilentTM_frame`, `Turing.embedEmitTM_frame` — tapes outside
  `Set.range ι` byte-identical with heads unmoved, input position tracking
  the source, output per flavor.
* `Turing.embedSilentTM_visitedByTapeHead`,
  `Turing.embedEmitTM_visitedByTapeHead` (and `_frame` companions),
  `Turing.embedSilentTM_spaceUsedByTape_cap` — per-tape space: host tape
  `ι i` visits exactly the source's tape-`i` cells, unselected tapes visit
  nothing new, and the capture tape is bounded by the recorded output.
* `Turing.embedSilentRetTM_run`, `Turing.embedEmitRetTM_run` — the
  through-halt contracts: live lockstep, then the handover at the source's
  first halt, final emission and source residue preserved, with the return
  anchor reached first exactly there.
* `Turing.embedSilentRetTM_visitedByTapeHead`,
  `Turing.embedEmitRetTM_visitedByTapeHead` — the returning flavors visit
  exactly what the closed flavors visit, at every time.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2; tape-subset simulations are the
  folklore of the §1.3/§1.7 robustness and simulation arguments.)
* [Bon26] É. Bonnet, *classical-complexity*, Lax Archive entry lax-434930,
  module `proofs/Lax434930Proofs/InclusionAux/TimeCompiler/`, commit
  `0c0840319318215fd7b36a9a822b81ce55cf6941`, Apache-2.0, examined
  2026-10-05. Design adaptation with nothing transcribed (different
  toolchain and machine model — TM2-style keyed stacks there, `FinTM`
  tapes with heads here): the bank-embedding shape is `StackRename`'s
  `rename_executes`.
-/

namespace Turing

variable {m k : ℕ} {S : Type*} {Symbol : Type*} {x : List Symbol}

/-- The partial inverse of the tape selection: the source index that `ι`
sends to host tape `j`, or `none` when `j` is unselected. Injectivity of
`ι` makes the first `List.find?` hit the unique preimage. -/
private def embedSlot (ι : Fin m ↪ Fin k) (j : Fin k) : Option (Fin m) :=
  (List.finRange m).find? fun i => decide (ι i = j)

/-- Searching at a selected tape returns its unique source index. -/
private lemma embedSlot_selected (ι : Fin m ↪ Fin k) (i : Fin m) :
    embedSlot ι (ι i) = some i := by
  unfold embedSlot
  cases hs : (List.finRange m).find? (fun j => decide (ι j = ι i)) with
  | none =>
    have hn := List.find?_eq_none.mp hs i (by simp)
    simp at hn
  | some j =>
    have hj := List.find?_some hs
    have hji : j = i := ι.injective (of_decide_eq_true hj)
    subst j
    rfl

/-- Searching outside the selected bank returns no source index. -/
private lemma embedSlot_unselected (ι : Fin m ↪ Fin k) (j : Fin k)
    (hj : j ∉ Set.range ι) : embedSlot ι j = none := by
  unfold embedSlot
  rw [List.find?_eq_none]
  intro i _
  simp only [decide_eq_true_eq]
  exact fun hij => hj ⟨i, hij⟩

/-- The shared private core of the two embedding transformers (frozen
decision 12.4): transport one source action along `ι`, keeping the input
move and the successor state, performing the source's tape-`i` action on
host tape `ι i`, and leaving every unselected tape stationary and
unwritten — except that an emission is handled per the mode `sink`:
`sink = some cap` records it on host tape `cap` with a right move (the
capture discipline of `Turing.captureAction`) and keeps the host output
silent, while `sink = none` forwards it as the host's physical emission
(the discipline of `Turing.emitAction`). -/
private def embedActionCore (ι : Fin m ↪ Fin k) (sink : Option (Fin k))
    (a : Action m Symbol S) : Action k Symbol S where
  inputTape := a.inputTape
  workTapes := fun j =>
    match embedSlot ι j with
    | some i => a.workTapes i
    | none =>
      match sink with
      | some cap =>
        if j = cap then
          match a.output with
          | some b => (some (some b), SignType.pos)
          | none => (none, 0)
        else (none, 0)
      | none => (none, 0)
  output :=
    match sink with
    | some _ => none
    | none => a.output
  state := a.state

/-- A source configuration viewed inside a `k`-tape host along the
selection `ι`, suppressing flavor: same control state and input position,
source tape `i` sitting on host tape `ι i` (content and head), the
designated capture tape `cap` holding `pre ++ c.output` — the emissions
recorded so far after a pre-existing prefix — with its head one past that
word, every other unselected tape holding the ambient frame `tapes j` with
its head at `heads j`, and the host's physical output the untouched
`out₀`. Generic form of the `emitterBank*`/`clBank*` configuration
correspondences; for a source of `m` tapes in a host of `m + 1` with the
last tape selected as capture, it degenerates to `Turing.captureCfg` up to
the state embedding (round-1 restatement note: the specialization enlarges
the tape count by one — it is not `m = k`). [Bon26] -/
def embedSilentCfg (ι : Fin m ↪ Fin k) (cap : Fin k)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) : Cfg k Symbol S x where
  state := c.state
  inputPos := c.inputPos
  workTapes := fun j =>
    match embedSlot ι j with
    | some i => c.workTapes i
    | none =>
      if j = cap then FinTM.bufferTape (pre ++ c.output) else tapes j
  workTapePos := fun j =>
    match embedSlot ι j with
    | some i => c.workTapePos i
    | none =>
      if j = cap then ((pre ++ c.output).length : ℤ) else heads j
  output := out₀

/-- A source configuration viewed inside a `k`-tape host along the
selection `ι`, forwarding flavor: same control state and input position,
source tape `i` on host tape `ι i`, every unselected tape holding the
ambient frame, and the host's physical output equal to the host's prior
output `pre` followed by everything the source has emitted. Generic form
of the `emitterP2*` relocation correspondences; at `ι = id` it is
`Turing.emitCfg` up to the state embedding. [Bon26] -/
def embedEmitCfg (ι : Fin m ↪ Fin k)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre : List Symbol) (c : Cfg m Symbol S x) : Cfg k Symbol S x where
  state := c.state
  inputPos := c.inputPos
  workTapes := fun j =>
    match embedSlot ι j with
    | some i => c.workTapes i
    | none => tapes j
  workTapePos := fun j =>
    match embedSlot ι j with
    | some i => c.workTapePos i
    | none => heads j
  output := pre ++ c.output

/-- **R1, the suppressing embedding transformer** (design §12, decision
12.4; [Bon26]). Run the `m`-tape machine `M` on the host tapes selected by
`ι`, recording every emission on the designated host work tape `cap`
(intended outside `Set.range ι`) and emitting nothing physically — the
W1/capture flavor. States are preserved and the source halt is the host
halt; live return dispatch is the seam combinator's job. -/
def embedSilentTM (ι : Fin m ↪ Fin k) (cap : Fin k)
    (M : MultiTapeTM m Symbol S) : MultiTapeTM k Symbol S where
  q₀ := M.q₀
  tr := fun q inp w =>
    embedActionCore ι (some cap) (M.tr q inp fun i => w (ι i))

/-- **R1, the forwarding embedding transformer** (design §12, decision
12.4; [Bon26]). Run the `m`-tape machine `M` on the host tapes selected by
`ι`, with every emission passed to the host's physical output verbatim —
the E2 flavor. States are preserved and the source halt is the host
halt. -/
def embedEmitTM (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Symbol S) :
    MultiTapeTM k Symbol S where
  q₀ := M.q₀
  tr := fun q inp w =>
    embedActionCore ι none (M.tr q inp fun i => w (ι i))

/-- **R1, the forwarding transformer's transition** (12.2c item 6's prerequisite export;
user, 2026-10-10, from the RB5 review). One host transition of `embedEmitTM ι M` is the
source transition, read through `ι` and transported along it. Each selected host tape
`ι i` performs the source's tape-`i` action. Every unselected tape is stationary and
unwritten, `(none, 0)`. The input move, the output and the successor state are the
source's. Consumers cite this rather than unfolding the private slot search. [Bon26]

**Proof sketch.** `embedEmitTM` is `embedActionCore ι none` of the source action. The
selected and unselected tapes are the slot inverse's two equations, `embedSlot ι (ι i) =
some i` and `embedSlot ι j = none` off `Set.range ι`. The other three fields are copied
verbatim. -/
theorem embedEmitTM_tr (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Symbol S) (q : S)
    (inp : Option Symbol) (w : Fin k → Option Symbol) :
    ((embedEmitTM ι M).tr q inp w).inputTape = (M.tr q inp fun i => w (ι i)).inputTape ∧
      (∀ i, ((embedEmitTM ι M).tr q inp w).workTapes (ι i) =
        (M.tr q inp fun i => w (ι i)).workTapes i) ∧
      (∀ j, j ∉ Set.range ι → ((embedEmitTM ι M).tr q inp w).workTapes j = (none, 0)) ∧
      ((embedEmitTM ι M).tr q inp w).output = (M.tr q inp fun i => w (ι i)).output ∧
      ((embedEmitTM ι M).tr q inp w).state = (M.tr q inp fun i => w (ι i)).state := by
  refine ⟨rfl, fun i => ?_, fun j hj => ?_, rfl, rfl⟩
  · simp [embedEmitTM, embedActionCore, embedSlot_selected]
  · simp [embedEmitTM, embedActionCore, embedSlot_unselected ι j hj]

/-- Applying the silent core commutes with configuration transport.
**Proof sketch.** Selected tapes perform the source action. Off-bank tapes
are stationary, except that capture appends the emitted symbol at the old
word length. Input movement and successor control are copied verbatim. -/
private lemma embedSilent_apply (ι : Fin m ↪ Fin k) (cap : Fin k)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) (a : Action m Symbol S) :
    (embedActionCore ι (some cap) a).apply
        (embedSilentCfg ι cap tapes heads pre out₀ c) =
      embedSilentCfg ι cap tapes heads pre out₀ (a.apply c) := by
  refine Cfg.ext rfl rfl ?_ ?_ ?_
  · funext j
    cases hs : embedSlot ι j with
    | some i => simp [embedActionCore, embedSilentCfg, Action.apply, hs]
    | none =>
      by_cases hj : j = cap
      · subst j
        cases ho : a.output <;>
          simp [embedActionCore, embedSilentCfg, Action.apply, hs, ho,
            ← List.append_assoc, FinTM.bufferTape_append]
      · simp [embedActionCore, embedSilentCfg, Action.apply, hs, hj]
  · funext j
    cases hs : embedSlot ι j with
    | some i => simp [embedActionCore, embedSilentCfg, Action.apply, hs]
    | none =>
      by_cases hj : j = cap
      · subst j
        cases ho : a.output <;>
          simp [embedActionCore, embedSilentCfg, Action.apply, hs, ho,
            Nat.cast_add, add_assoc]
      · simp [embedActionCore, embedSilentCfg, Action.apply, hs, hj]
  · simp [embedActionCore, embedSilentCfg, Action.apply]

/-- The silent host reads the source action and executes all its effects
in one step; halted configurations remain fixed on both sides. -/
private lemma embedSilent_step (ι : Fin m ↪ Fin k) (cap : Fin k)
    (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) :
    (embedSilentTM ι cap M).step (embedSilentCfg ι cap tapes heads pre out₀ c) =
      embedSilentCfg ι cap tapes heads pre out₀ (M.step c) := by
  unfold MultiTapeTM.step
  cases hs : c.state with
  | none => simp [embedSilentCfg, hs]
  | some q =>
    rw [show (embedSilentCfg ι cap tapes heads pre out₀ c).state = some q from hs]
    dsimp only
    have hr : (fun i => (embedSilentCfg ι cap tapes heads pre out₀ c).workTapeSymbols
        (ι i)) = c.workTapeSymbols := by
      funext i
      simp [Cfg.workTapeSymbols, embedSilentCfg, embedSlot_selected]
    change (embedActionCore ι (some cap) (M.tr q c.inputSymbol _)).apply _ = _
    rw [hr]
    exact embedSilent_apply ι cap tapes heads pre out₀ c _

/-- **R1 lockstep, suppressing flavor** (design §12;
[Bon26], `rename_executes`). The transported run *is* the transport of the
source run, at every time and with the step count preserved exactly: `t`
host steps simulate `t` source steps. No liveness guard is needed — the
transformer preserves states, so a halted source transports to a halted
host and both runs stall together.

**Proof sketch.** One-step commutation plus
`Turing.MultiTapeTM.runFrom_comm_of_step`. For the step: a halted source
makes both sides the identity. For a live source state, the host reads the
source symbols through `ι` (the transport puts source tape `i` at `ι i`),
so the host applies `embedActionCore` of the very action the source
applies; componentwise, selected tapes update as the source's
(`Turing.Action.apply` through the `embedSlot` inverse, whose two
equations `embedSlot ι (ι i) = some i` and `embedSlot ι j = none` off the
range are the `List.find?` glue obligations), unselected tapes receive the
stationary no-write action, the capture tape appends the optional emission
at head `|pre ++ c.output|` (`Turing.FinTM.bufferTape_append`, exactly as
in `capture_apply`), silence keeps the output at `out₀`, and the states
agree. -/
theorem embedSilentTM_runFrom (ι : Fin m ↪ Fin k) (cap : Fin k)
    (hcap : cap ∉ Set.range ι) (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) (t : ℕ) :
    (embedSilentTM ι cap M).runFrom
        (embedSilentCfg ι cap tapes heads pre out₀ c) t =
      embedSilentCfg ι cap tapes heads pre out₀ (M.runFrom c t) := by
  exact MultiTapeTM.runFrom_comm_of_step
    (embedSilentCfg ι cap tapes heads pre out₀)
    (embedSilent_step ι cap M tapes heads pre out₀) c t

/-- **R1 frame, suppressing flavor** (design §12).
Along the whole transported run, every host tape outside the selected bank
and distinct from the capture tape is byte-identical to its ambient frame
with its head unmoved; the input position tracks the source's; and the
host's physical output stays `out₀` (output silence).

**Proof sketch.** Project the lockstep equation
`embedSilentTM_runFrom` componentwise: the transport's `workTapes`/
`workTapePos` at an unselected `j ≠ cap` are the frame parameters by the
`embedSlot` off-range equation, its `inputPos` is the source's, and its
`output` is `out₀` by definition. -/
theorem embedSilentTM_frame (ι : Fin m ↪ Fin k) (cap : Fin k)
    (hcap : cap ∉ Set.range ι) (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) (t : ℕ) :
    (∀ j : Fin k, j ∉ Set.range ι → j ≠ cap →
      ((embedSilentTM ι cap M).runFrom
          (embedSilentCfg ι cap tapes heads pre out₀ c) t).workTapes j
        = tapes j ∧
      ((embedSilentTM ι cap M).runFrom
          (embedSilentCfg ι cap tapes heads pre out₀ c) t).workTapePos j
        = heads j) ∧
    ((embedSilentTM ι cap M).runFrom
        (embedSilentCfg ι cap tapes heads pre out₀ c) t).inputPos
      = (M.runFrom c t).inputPos ∧
    ((embedSilentTM ι cap M).runFrom
        (embedSilentCfg ι cap tapes heads pre out₀ c) t).output = out₀ := by
  rw [embedSilentTM_runFrom ι cap hcap]
  refine ⟨?_, rfl, rfl⟩
  intro j hj hjc
  simp [embedSilentCfg, embedSlot_unselected ι j hj, hjc]

/-- **R1 space, suppressing flavor, selected tapes**
(design §12: "cells visited on host tape `ι i` equal cells visited on
source tape `i`"). The visited set of host tape `ι i` up to time `t` is
exactly the source's visited set of tape `i`, so the per-tape space
agrees on the nose.

**Proof sketch.** Both visited sets are images of `Finset.range (t + 1)`
under the respective head trajectories
(`Turing.MultiTapeTM.visitedByTapeHead`), and the lockstep equation
`embedSilentTM_runFrom` makes the trajectories pointwise equal at `ι i`
via the transport's `workTapePos` clause and `embedSlot ι (ι i) = some i`.
The cardinality clause is `congrArg Finset.card`. -/
theorem embedSilentTM_visitedByTapeHead (ι : Fin m ↪ Fin k) (cap : Fin k)
    (hcap : cap ∉ Set.range ι) (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) (t : ℕ) (i : Fin m) :
    (embedSilentTM ι cap M).visitedByTapeHead
        (embedSilentCfg ι cap tapes heads pre out₀ c) t (ι i)
      = M.visitedByTapeHead c t i ∧
    (embedSilentTM ι cap M).spaceUsedByTape
        (embedSilentCfg ι cap tapes heads pre out₀ c) t (ι i)
      = M.spaceUsedByTape c t i := by
  have hv : (embedSilentTM ι cap M).visitedByTapeHead
      (embedSilentCfg ι cap tapes heads pre out₀ c) t (ι i) =
      M.visitedByTapeHead c t i := by
    unfold MultiTapeTM.visitedByTapeHead
    congr 1
    funext u
    rw [embedSilentTM_runFrom ι cap hcap]
    simp [embedSilentCfg, embedSlot_selected]
  exact ⟨hv, congrArg Finset.card hv⟩

/-- **R1 space, suppressing flavor, unselected tapes** (spec, fill
pending — design §12: "unselected tapes visit nothing new"). A host tape
outside the selected bank and distinct from the capture tape visits
exactly the singleton of its initial head position, so its space usage is
one cell.

**Proof sketch.** By `embedSilentTM_frame` the head of such a tape never
moves, so the trajectory image collapses to `{heads j}`; the cardinality
clause is `Finset.card_singleton`. -/
theorem embedSilentTM_visitedByTapeHead_frame (ι : Fin m ↪ Fin k)
    (cap : Fin k) (hcap : cap ∉ Set.range ι) (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) (t : ℕ)
    (j : Fin k) (hj : j ∉ Set.range ι) (hjc : j ≠ cap) :
    (embedSilentTM ι cap M).visitedByTapeHead
        (embedSilentCfg ι cap tapes heads pre out₀ c) t j = {heads j} ∧
    (embedSilentTM ι cap M).spaceUsedByTape
        (embedSilentCfg ι cap tapes heads pre out₀ c) t j = 1 := by
  have hv : (embedSilentTM ι cap M).visitedByTapeHead
      (embedSilentCfg ι cap tapes heads pre out₀ c) t j = {heads j} := by
    unfold MultiTapeTM.visitedByTapeHead
    simp_rw [embedSilentTM_runFrom ι cap hcap]
    simp [embedSilentCfg, embedSlot_unselected ι j hj, hjc]
    exact Finset.image_const ⟨0, by simp⟩ _
  refine ⟨hv, ?_⟩
  simp [MultiTapeTM.spaceUsedByTape, hv]

/-- **R1 space, suppressing flavor, the capture tape** (spec, fill
pending — design §12; every unselected tape is accounted for, the capture
tape included). The capture tape's space usage up to time `t` is bounded
by the number of emissions recorded in that window plus one: the head
starts one past `pre ++ c.output` and advances right exactly once per
recorded emission.

**Proof sketch.** By lockstep the capture head position at time `t'` is
`|pre| + |(M.runFrom c t').output|`, which is nondecreasing in `t'` with
increments bounded by one emission per step; the visited set is therefore
the integer interval from the initial head to the final one, of
cardinality the output growth plus one
(`Turing.MultiTapeTM.output_prefix` gives the monotone growth).

**Fill appendix.** For the stated upper bound, the formal proof only
needs containment in this interval, followed by its cardinality. -/
theorem embedSilentTM_spaceUsedByTape_cap (ι : Fin m ↪ Fin k) (cap : Fin k)
    (hcap : cap ∉ Set.range ι) (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) (t : ℕ) :
    (embedSilentTM ι cap M).spaceUsedByTape
        (embedSilentCfg ι cap tapes heads pre out₀ c) t cap
      ≤ (M.runFrom c t).output.length - c.output.length + 1 := by
  have hgrowth : c.output.length ≤ (M.runFrom c t).output.length := by
    simpa using (M.output_prefix c (Nat.zero_le t)).length_le
  have hsub : (embedSilentTM ι cap M).visitedByTapeHead
      (embedSilentCfg ι cap tapes heads pre out₀ c) t cap ⊆
      Finset.Icc ((pre ++ c.output).length : ℤ)
        ((pre ++ (M.runFrom c t).output).length : ℤ) := by
    intro z hz
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
    have hut : u ≤ t := Nat.le_of_lt_succ (Finset.mem_range.mp hu)
    have hlo : c.output.length ≤ (M.runFrom c u).output.length := by
      simpa using (M.output_prefix c (Nat.zero_le u)).length_le
    have hhi := (M.output_prefix c hut).length_le
    rw [embedSilentTM_runFrom ι cap hcap]
    simp only [embedSilentCfg, embedSlot_unselected ι cap hcap, ↓reduceIte,
      Finset.mem_Icc, List.length_append, Nat.cast_add]
    constructor <;> omega
  calc
    _ ≤ (Finset.Icc ((pre ++ c.output).length : ℤ)
        ((pre ++ (M.runFrom c t).output).length : ℤ)).card :=
      Finset.card_le_card hsub
    _ = (M.runFrom c t).output.length - c.output.length + 1 := by
      rw [Int.card_Icc]
      simp only [List.length_append, Nat.cast_add]
      omega

/-- Applying the forwarding core commutes with configuration transport:
selected tapes update identically, the frame stays fixed, and appending
the optional emission associates with the existing output prefix. -/
private lemma embedEmit_apply (ι : Fin m ↪ Fin k)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre : List Symbol) (c : Cfg m Symbol S x) (a : Action m Symbol S) :
    (embedActionCore ι none a).apply (embedEmitCfg ι tapes heads pre c) =
      embedEmitCfg ι tapes heads pre (a.apply c) := by
  refine Cfg.ext rfl rfl ?_ ?_ ?_
  · funext j
    cases hs : embedSlot ι j <;>
      simp [embedActionCore, embedEmitCfg, Action.apply, hs]
  · funext j
    cases hs : embedSlot ι j <;>
      simp [embedActionCore, embedEmitCfg, Action.apply, hs]
  · simp [embedActionCore, embedEmitCfg, Action.apply, List.append_assoc]

/-- The forwarding host reads the same source action and executes it
completely in one step, including an emission on a halting transition. -/
private lemma embedEmit_step (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre : List Symbol) (c : Cfg m Symbol S x) :
    (embedEmitTM ι M).step (embedEmitCfg ι tapes heads pre c) =
      embedEmitCfg ι tapes heads pre (M.step c) := by
  unfold MultiTapeTM.step
  cases hs : c.state with
  | none => simp [embedEmitCfg, hs]
  | some q =>
    rw [show (embedEmitCfg ι tapes heads pre c).state = some q from hs]
    dsimp only
    have hr : (fun i => (embedEmitCfg ι tapes heads pre c).workTapeSymbols
        (ι i)) = c.workTapeSymbols := by
      funext i
      simp [Cfg.workTapeSymbols, embedEmitCfg, embedSlot_selected]
    change (embedActionCore ι none (M.tr q c.inputSymbol _)).apply _ = _
    rw [hr]
    exact embedEmit_apply ι tapes heads pre c _

/-- **R1 lockstep, forwarding flavor** (design §12;
[Bon26], `rename_executes`). The transported run is the transport of the
source run, at every time and with the step count preserved exactly;
emissions are forwarded, so the host's output is `pre` followed by the
source's output at every instant (through the transport).

**Proof sketch.** As `embedSilentTM_runFrom`, with the capture clause
replaced by the output clause: the one-step commutation appends the
optional emission after `pre` (associativity of `++`, exactly as in
`emit_apply`), and `Turing.MultiTapeTM.runFrom_comm_of_step` iterates. -/
theorem embedEmitTM_runFrom (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre : List Symbol) (c : Cfg m Symbol S x) (t : ℕ) :
    (embedEmitTM ι M).runFrom (embedEmitCfg ι tapes heads pre c) t =
      embedEmitCfg ι tapes heads pre (M.runFrom c t) := by
  exact MultiTapeTM.runFrom_comm_of_step (embedEmitCfg ι tapes heads pre)
    (embedEmit_step ι M tapes heads pre) c t

/-- **R1 frame, forwarding flavor** (design §12).
Along the whole transported run, every host tape outside the selected
bank is byte-identical to its ambient frame with its head unmoved, the
input position tracks the source's, and the host's physical output is
`pre` followed by the source's output so far.

**Proof sketch.** Project `embedEmitTM_runFrom` componentwise, as in the
suppressing flavor; the output clause is the transport's definition. -/
theorem embedEmitTM_frame (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre : List Symbol) (c : Cfg m Symbol S x) (t : ℕ) :
    (∀ j : Fin k, j ∉ Set.range ι →
      ((embedEmitTM ι M).runFrom
          (embedEmitCfg ι tapes heads pre c) t).workTapes j = tapes j ∧
      ((embedEmitTM ι M).runFrom
          (embedEmitCfg ι tapes heads pre c) t).workTapePos j = heads j) ∧
    ((embedEmitTM ι M).runFrom
        (embedEmitCfg ι tapes heads pre c) t).inputPos
      = (M.runFrom c t).inputPos ∧
    ((embedEmitTM ι M).runFrom
        (embedEmitCfg ι tapes heads pre c) t).output
      = pre ++ (M.runFrom c t).output := by
  rw [embedEmitTM_runFrom]
  refine ⟨?_, rfl, rfl⟩
  intro j hj
  simp [embedEmitCfg, embedSlot_unselected ι j hj]

/-- **R1 space, forwarding flavor, selected tapes**
(design §12). The visited set of host tape `ι i` up to time `t` is exactly
the source's visited set of tape `i`; per-tape space agrees on the nose.

**Proof sketch.** As `embedSilentTM_visitedByTapeHead`: pointwise equal
head trajectories from `embedEmitTM_runFrom`, then image and
cardinality. -/
theorem embedEmitTM_visitedByTapeHead (ι : Fin m ↪ Fin k)
    (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre : List Symbol) (c : Cfg m Symbol S x) (t : ℕ) (i : Fin m) :
    (embedEmitTM ι M).visitedByTapeHead
        (embedEmitCfg ι tapes heads pre c) t (ι i)
      = M.visitedByTapeHead c t i ∧
    (embedEmitTM ι M).spaceUsedByTape
        (embedEmitCfg ι tapes heads pre c) t (ι i)
      = M.spaceUsedByTape c t i := by
  have hv : (embedEmitTM ι M).visitedByTapeHead
      (embedEmitCfg ι tapes heads pre c) t (ι i) =
      M.visitedByTapeHead c t i := by
    unfold MultiTapeTM.visitedByTapeHead
    congr 1
    funext u
    rw [embedEmitTM_runFrom]
    simp [embedEmitCfg, embedSlot_selected]
  exact ⟨hv, congrArg Finset.card hv⟩

/-- **R1 space, forwarding flavor, unselected tapes** (spec, fill
pending — design §12). A host tape outside the selected bank visits
exactly the singleton of its initial head position; its space usage is
one cell.

**Proof sketch.** By `embedEmitTM_frame` the head never moves; collapse
the trajectory image to `{heads j}` and take cardinalities. -/
theorem embedEmitTM_visitedByTapeHead_frame (ι : Fin m ↪ Fin k)
    (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre : List Symbol) (c : Cfg m Symbol S x) (t : ℕ)
    (j : Fin k) (hj : j ∉ Set.range ι) :
    (embedEmitTM ι M).visitedByTapeHead
        (embedEmitCfg ι tapes heads pre c) t j = {heads j} ∧
    (embedEmitTM ι M).spaceUsedByTape
        (embedEmitCfg ι tapes heads pre c) t j = 1 := by
  have hv : (embedEmitTM ι M).visitedByTapeHead
      (embedEmitCfg ι tapes heads pre c) t j = {heads j} := by
    unfold MultiTapeTM.visitedByTapeHead
    simp_rw [embedEmitTM_runFrom]
    simp only [embedEmitCfg, embedSlot_unselected ι j hj]
    exact Finset.image_const ⟨0, by simp⟩ _
  refine ⟨hv, ?_⟩
  simp [MultiTapeTM.spaceUsedByTape, hv]

/-- **R1′, the returning suppressing embedding** (round-1 repair R1). As
`Turing.embedSilentTM`, on states `S ⊕ Unit`: live source states run the
capture-flavored core, but a source action whose successor is `none` lands
in the **live return anchor** `Sum.inr ()` — the halting transition is
executed in full, its emission recorded on `cap`, before control arrives at
the anchor (the `Turing.captureAction`/`Turing.emitterRightTM` halt-to-live
discipline, exported). The anchor itself idles (stationary, silent, live),
which is exactly what a seam combinator overrides as its left exit. -/
def embedSilentRetTM (ι : Fin m ↪ Fin k) (cap : Fin k)
    (M : MultiTapeTM m Symbol S) : MultiTapeTM k Symbol (S ⊕ Unit) where
  q₀ := Sum.inl M.q₀
  tr := fun q inp w =>
    match q with
    | Sum.inl s =>
      let a := M.tr s inp fun i => w (ι i)
      let h := embedActionCore ι (some cap) a
      ⟨h.inputTape, h.workTapes, h.output,
        some (a.state.elim (Sum.inr ()) Sum.inl)⟩
    | Sum.inr _ => ⟨0, fun _ => (none, 0), none, some (Sum.inr ())⟩

/-- **R1′, the returning forwarding embedding** (round-1 repair R1). As
`Turing.embedEmitTM`, on states `S ⊕ Unit`, with source halts landing in
the live return anchor `Sum.inr ()` after the halting transition — its
forwarded emission included — has executed in full. -/
def embedEmitRetTM (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Symbol S) :
    MultiTapeTM k Symbol (S ⊕ Unit) where
  q₀ := Sum.inl M.q₀
  tr := fun q inp w =>
    match q with
    | Sum.inl s =>
      let a := M.tr s inp fun i => w (ι i)
      let h := embedActionCore ι none a
      ⟨h.inputTape, h.workTapes, h.output,
        some (a.state.elim (Sum.inr ()) Sum.inl)⟩
    | Sum.inr _ => ⟨0, fun _ => (none, 0), none, some (Sum.inr ())⟩

/-- Replace an action's optional successor by the live return encoding,
without changing any input, work-tape, or output effect. -/
private def embedReturnAction (a : Action k Symbol S) : Action k Symbol (S ⊕ Unit) :=
  ⟨a.inputTape, a.workTapes, a.output, some (a.state.elim (Sum.inr ()) Sum.inl)⟩

/-- Encode a closed host configuration with live left states and a live
right return anchor, preserving all four non-control fields. -/
private def embedReturnCfg (c : Cfg k Symbol S x) : Cfg k Symbol (S ⊕ Unit) x :=
  { c with state := some (c.state.elim (Sum.inr ()) Sum.inl) }

/-- At a live configuration, the return encoding is ordinary left state
mapping; at a halt it instead uses the live right anchor. -/
private lemma embedReturnCfg_live (c : Cfg k Symbol S x) (hc : c.state ≠ none) :
    embedReturnCfg c = c.mapState Sum.inl := by
  cases hs : c.state with
  | none => exact (hc hs).elim
  | some q => simp [embedReturnCfg, Cfg.mapState, hs]

/-- Direct comparison of a closed host step with a returning host step.
**Proof sketch.** At a live left state, both hosts execute the same action
and only the successor encoding differs. At a closed halt, the returning
anchor's idle action preserves every non-control field, just as absorption
does on the closed side. No property of a source embedding is needed. -/
private lemma embedReturn_step (N : MultiTapeTM k Symbol S)
    (R : MultiTapeTM k Symbol (S ⊕ Unit))
    (hleft : ∀ q inp work, R.tr (Sum.inl q) inp work =
      embedReturnAction (N.tr q inp work))
    (hidle : ∀ inp work, R.tr (Sum.inr ()) inp work =
      ⟨0, fun _ => (none, 0), none, some (Sum.inr ())⟩)
    (c : Cfg k Symbol S x) :
    R.step (embedReturnCfg c) = embedReturnCfg (N.step c) := by
  unfold MultiTapeTM.step
  cases hs : c.state with
  | none => simp [embedReturnCfg, hs, hidle, Action.apply]
  | some q =>
    rw [show (embedReturnCfg c).state = some (Sum.inl q) by
      simp [embedReturnCfg, hs]]
    dsimp only
    have hin : (embedReturnCfg c).inputSymbol = c.inputSymbol := rfl
    have hw : (embedReturnCfg c).workTapeSymbols = c.workTapeSymbols := rfl
    rw [hin, hw, hleft]
    rfl

/-- The silent returning step executes the entire transported source
action, then encodes its successor as a live left state or return anchor. -/
private lemma embedSilentRet_step (ι : Fin m ↪ Fin k) (cap : Fin k)
    (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) (hc : c.state ≠ none) :
    (embedSilentRetTM ι cap M).step
        ((embedSilentCfg ι cap tapes heads pre out₀ c).mapState Sum.inl) =
      embedReturnCfg (embedSilentCfg ι cap tapes heads pre out₀ (M.step c)) := by
  have h := embedReturn_step (embedSilentTM ι cap M) (embedSilentRetTM ι cap M)
    (fun _ _ _ => rfl) (fun _ _ => rfl)
    (embedSilentCfg ι cap tapes heads pre out₀ c)
  rw [embedReturnCfg_live (embedSilentCfg ι cap tapes heads pre out₀ c) hc,
    embedSilent_step] at h
  exact h

/-- A live-step transport reaches the return anchor exactly at a positive
first halt, with all transported data intact.
**Proof sketch.** The initially live state and terminal halt imply positive
time. Induct over the strict live prefix, where the successor encoding is
ordinary left mapping. Execute the step from the last live configuration
separately; its halted successor encodes the return anchor. Earlier states
are left constructors, so none is the right anchor. -/
private lemma embedThroughHalt (M : MultiTapeTM m Symbol S)
    (R : MultiTapeTM k Symbol (S ⊕ Unit))
    (E : Cfg m Symbol S x → Cfg k Symbol S x)
    (hstate : ∀ d, (E d).state = d.state)
    (hstep : ∀ d, d.state ≠ none →
      R.step ((E d).mapState Sum.inl) = embedReturnCfg (E (M.step d)))
    (c : Cfg m Symbol S x) (T : ℕ) (hc : c.state ≠ none)
    (hlive : ∀ t < T, (M.runFrom c t).state ≠ none)
    (hhalt : (M.runFrom c T).state = none) :
    (∀ t < T, R.runFrom ((E c).mapState Sum.inl) t =
      (E (M.runFrom c t)).mapState Sum.inl) ∧
    R.runFrom ((E c).mapState Sum.inl) T =
      { E (M.runFrom c T) with state := some (Sum.inr ()) } ∧
    ∀ t < T, (R.runFrom ((E c).mapState Sum.inl) t).state ≠
      some (Sum.inr ()) := by
  have hT : 0 < T := by
    by_contra hn
    have hz : T = 0 := by omega
    subst T
    exact hc (by simpa using hhalt)
  have hrun : ∀ t < T, R.runFrom ((E c).mapState Sum.inl) t =
      (E (M.runFrom c t)).mapState Sum.inl := by
    intro t
    induction t with
    | zero => intro _; rfl
    | succ t ih =>
      intro ht
      rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega),
        hstep _ (hlive t (by omega)), ← MultiTapeTM.runFrom_succ_eq_step']
      apply embedReturnCfg_live
      rw [hstate]
      exact hlive _ ht
  refine ⟨hrun, ?_, ?_⟩
  · have hlast : T - 1 + 1 = T := by omega
    calc
      R.runFrom ((E c).mapState Sum.inl) T =
          R.step (R.runFrom ((E c).mapState Sum.inl) (T - 1)) :=
        (congrArg (R.runFrom ((E c).mapState Sum.inl)) hlast).symm.trans
          MultiTapeTM.runFrom_succ_eq_step'
      _ = embedReturnCfg (E (M.runFrom c T)) := by
        rw [hrun _ (by omega), hstep _ (hlive _ (by omega)),
          ← MultiTapeTM.runFrom_succ_eq_step', hlast]
      _ = _ := by simp [embedReturnCfg, hstate, hhalt]
  · intro t ht
    rw [hrun t ht]
    simp only [Cfg.mapState, hstate]
    cases (M.runFrom c t).state <;> simp

/-- **R1′ through-halt contract, suppressing flavor**
(round-1 repair R1): if the source first halts at time `T`, the returning
embedding runs in `Sum.inl`-lockstep through every live time and, at `T`,
sits at the **live return anchor** over the completed transport — the
halting transition's emission recorded on `cap`, the source tape residue
preserved on the selected bank, the frame untouched — having visited the
anchor first exactly there. The start must be **live** (`hc` — round-2
blocker: an initially halted `c` at `T = 0` satisfies the other hypotheses
vacuously while the handover state projection would demand
`none = some (Sum.inr ())`; under `hlive` **and** `hhalt` together, `hc` is
equivalent to `0 < T` — the forward direction uses `hhalt`, the reverse
`hlive 0` (round-3 finding 1 sharpened the earlier `hhalt`-only phrasing).
The smallest case is the round-1 counterexample cured: a one-state source
that emits and halts on its first transition lands at time `1` in
`Sum.inr ()` with `pre ++ [b]` on the capture tape (the audit's S8 check).

**Proof sketch.** Live times: the `Sum.inl` branch applies the very core of
`Turing.embedSilentTM`, so `embedSilentTM_runFrom`'s one-step commutation
transports verbatim under `Cfg.mapState Sum.inl` (`Cfg.mapState_apply`).
At the halting step, the source action's tape and capture effects are those
of the closed flavor — `Turing.FinTM.bufferTape_append` records the final
emission — while the successor `Option.elim` lands in `Sum.inr ()` instead
of `none`; the anchor cannot occur earlier because live source states map
into `Sum.inl`. Fill obligations, named: the two `Option.elim` successor
equations; the through-halt step case; the first-visit projection. -/
theorem embedSilentRetTM_run (ι : Fin m ↪ Fin k) (cap : Fin k)
    (hcap : cap ∉ Set.range ι) (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) (T : ℕ)
    (hc : c.state ≠ none)
    (hlive : ∀ t < T, (M.runFrom c t).state ≠ none)
    (hhalt : (M.runFrom c T).state = none) :
    (∀ t < T,
      (embedSilentRetTM ι cap M).runFrom
          ((embedSilentCfg ι cap tapes heads pre out₀ c).mapState Sum.inl) t =
        (embedSilentCfg ι cap tapes heads pre out₀
          (M.runFrom c t)).mapState Sum.inl) ∧
    (embedSilentRetTM ι cap M).runFrom
        ((embedSilentCfg ι cap tapes heads pre out₀ c).mapState Sum.inl) T =
      { embedSilentCfg ι cap tapes heads pre out₀ (M.runFrom c T) with
          state := some (Sum.inr ()) } ∧
    ∀ t < T,
      ((embedSilentRetTM ι cap M).runFrom
          ((embedSilentCfg ι cap tapes heads pre out₀ c).mapState Sum.inl)
          t).state ≠ some (Sum.inr ()) := by
  exact embedThroughHalt M (embedSilentRetTM ι cap M)
    (embedSilentCfg ι cap tapes heads pre out₀) (fun _ => rfl)
    (embedSilentRet_step ι cap M tapes heads pre out₀) c T hc hlive hhalt

/-- The forwarding returning step preserves the complete source action,
including its final emission, and changes only the successor encoding. -/
private lemma embedEmitRet_step (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre : List Symbol) (c : Cfg m Symbol S x) (hc : c.state ≠ none) :
    (embedEmitRetTM ι M).step ((embedEmitCfg ι tapes heads pre c).mapState Sum.inl) =
      embedReturnCfg (embedEmitCfg ι tapes heads pre (M.step c)) := by
  have h := embedReturn_step (embedEmitTM ι M) (embedEmitRetTM ι M)
    (fun _ _ _ => rfl) (fun _ _ => rfl) (embedEmitCfg ι tapes heads pre c)
  rw [embedReturnCfg_live (embedEmitCfg ι tapes heads pre c) hc, embedEmit_step] at h
  exact h

/-- **R1′ through-halt contract, forwarding flavor**
(round-1 repair R1): as `Turing.embedSilentRetTM_run` with the final
emission forwarded to the physical output (`pre ++ (M.runFrom c T).output`
at the anchor).

**Proof sketch.** As `embedSilentRetTM_run`, with the forwarding core: live
times transport under `Cfg.mapState Sum.inl` by `embedEmitTM_runFrom`'s
one-step commutation, the halting step applies the closed forwarding core's
tape and output effects (the final emission appended to the physical
output) with the successor `Option.elim` landing in `Sum.inr ()`, and the
first-visit clause projects from the `Sum.inl` lockstep. Fill obligations,
named: the successor equations; the through-halt step case; the
first-visit projection. -/
theorem embedEmitRetTM_run (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre : List Symbol) (c : Cfg m Symbol S x) (T : ℕ)
    (hc : c.state ≠ none)
    (hlive : ∀ t < T, (M.runFrom c t).state ≠ none)
    (hhalt : (M.runFrom c T).state = none) :
    (∀ t < T,
      (embedEmitRetTM ι M).runFrom
          ((embedEmitCfg ι tapes heads pre c).mapState Sum.inl) t =
        (embedEmitCfg ι tapes heads pre (M.runFrom c t)).mapState Sum.inl) ∧
    (embedEmitRetTM ι M).runFrom
        ((embedEmitCfg ι tapes heads pre c).mapState Sum.inl) T =
      { embedEmitCfg ι tapes heads pre (M.runFrom c T) with
          state := some (Sum.inr ()) } ∧
    ∀ t < T,
      ((embedEmitRetTM ι M).runFrom
          ((embedEmitCfg ι tapes heads pre c).mapState Sum.inl) t).state ≠
        some (Sum.inr ()) := by
  exact embedThroughHalt M (embedEmitRetTM ι M)
    (embedEmitCfg ι tapes heads pre) (fun _ => rfl)
    (embedEmitRet_step ι M tapes heads pre) c T hc hlive hhalt

/-- Direct host comparison preserves every visited-head set, from any
initial configuration and for every finite horizon.
**Proof sketch.** Initially halted configurations stay halted on both
sides. From a live start, iterate the direct step comparison under the
return encoding, whose head positions are unchanged. Equality of the
head trajectories gives equality of their finite images. This uses no
termination hypothesis, source simulation, or capture-tape separation. -/
private lemma embedReturn_visited (N : MultiTapeTM k Symbol S)
    (R : MultiTapeTM k Symbol (S ⊕ Unit))
    (hleft : ∀ q inp work, R.tr (Sum.inl q) inp work =
      embedReturnAction (N.tr q inp work))
    (hidle : ∀ inp work, R.tr (Sum.inr ()) inp work =
      ⟨0, fun _ => (none, 0), none, some (Sum.inr ())⟩)
    (c : Cfg k Symbol S x) (t : ℕ) (j : Fin k) :
    R.visitedByTapeHead (c.mapState Sum.inl) t j = N.visitedByTapeHead c t j := by
  unfold MultiTapeTM.visitedByTapeHead
  congr 1
  funext u
  by_cases hc : c.state = none
  · rw [R.runFrom_of_halt _ (by simp [Cfg.mapState, hc]), N.runFrom_of_halt _ hc]
    rfl
  · have hrun := MultiTapeTM.runFrom_comm_of_step embedReturnCfg
      (embedReturn_step N R hleft hidle) c u
    rw [embedReturnCfg_live c hc] at hrun
    exact congrArg (fun d => d.workTapePos j) hrun

/-- **R1′ space, suppressing flavor** (round-1 repair
R1): at every time and on every tape, the returning embedding's visited set
from the `Sum.inl`-mapped seam equals the closed embedding's from the plain
seam — the trajectories coincide through the halt, and afterwards one idles
at the live anchor while the other sits halted, both stationary.

**Proof sketch.** For `t` up to the first source halt, both machines apply
identical tape actions (`embedSilentRetTM_run`'s lockstep and the halting
step's shared core); beyond it, the anchor's idle action and the halted
absorption are both stationary, freezing both visited sets.

**Fill appendix.** The direct host comparison `embedReturn_visited`
handles initially halted and live starts separately. It uses neither
through-halt contract nor a capture-separation hypothesis. -/
theorem embedSilentRetTM_visitedByTapeHead (ι : Fin m ↪ Fin k) (cap : Fin k)
    (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) (t : ℕ) (j : Fin k) :
    (embedSilentRetTM ι cap M).visitedByTapeHead
        ((embedSilentCfg ι cap tapes heads pre out₀ c).mapState Sum.inl) t j =
      (embedSilentTM ι cap M).visitedByTapeHead
        (embedSilentCfg ι cap tapes heads pre out₀ c) t j := by
  exact embedReturn_visited (embedSilentTM ι cap M) (embedSilentRetTM ι cap M)
    (fun _ _ _ => rfl) (fun _ _ => rfl)
    (embedSilentCfg ι cap tapes heads pre out₀ c) t j

/-- **R1′ space, forwarding flavor** (round-1 repair
R1): the forwarding analogue of
`Turing.embedSilentRetTM_visitedByTapeHead`.

**Proof sketch.** As the suppressing flavor: identical tape actions through
the first source halt, then the live idle and the halted absorption are
both stationary, freezing both visited sets — the trajectories coincide at
every time. -/
theorem embedEmitRetTM_visitedByTapeHead (ι : Fin m ↪ Fin k)
    (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre : List Symbol) (c : Cfg m Symbol S x) (t : ℕ) (j : Fin k) :
    (embedEmitRetTM ι M).visitedByTapeHead
        ((embedEmitCfg ι tapes heads pre c).mapState Sum.inl) t j =
      (embedEmitTM ι M).visitedByTapeHead
        (embedEmitCfg ι tapes heads pre c) t j := by
  exact embedReturn_visited (embedEmitTM ι M) (embedEmitRetTM ι M)
    (fun _ _ _ => rfl) (fun _ _ => rfl) (embedEmitCfg ι tapes heads pre c) t j


/-! ### Selected-tape exports (§13 Z1 rider, decision D-R1)

The retrofit inventories (`audits/retrofit-inventory/`) found, three times
independently, that no old-code R1 consumer can be proved from this file's
public surface: the frame lemmas cover only unselected tapes, and
`embedSlot_selected` is private. These four projections export the
selected-tape fields of the two configuration transports; `Turing.embedSilentCfg_cap`, after
them, exports the silent transport's capture field (the C1-A assembly gate, finding M1). They are
skeleton-time proofs (statement-phase additions flagged for the A-S1
audit): each is definitional at `embedSlot_selected`. -/

/-- The silent transport holds the source's tape `i` on host tape `ι i`. -/
theorem embedSilentCfg_selected_tape (ι : Fin m ↪ Fin k) (cap : Fin k)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) (i : Fin m) :
    (embedSilentCfg ι cap tapes heads pre out₀ c).workTapes (ι i) =
      c.workTapes i := by
  simp [embedSilentCfg, embedSlot_selected]

/-- The silent transport holds the source's tape-`i` head on host tape
`ι i`. -/
theorem embedSilentCfg_selected_pos (ι : Fin m ↪ Fin k) (cap : Fin k)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) (i : Fin m) :
    (embedSilentCfg ι cap tapes heads pre out₀ c).workTapePos (ι i) =
      c.workTapePos i := by
  simp [embedSilentCfg, embedSlot_selected]

/-- The forwarding transport holds the source's tape `i` on host tape
`ι i`. -/
theorem embedEmitCfg_selected_tape (ι : Fin m ↪ Fin k)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre : List Symbol) (c : Cfg m Symbol S x) (i : Fin m) :
    (embedEmitCfg ι tapes heads pre c).workTapes (ι i) = c.workTapes i := by
  simp [embedEmitCfg, embedSlot_selected]

/-- The forwarding transport holds the source's tape-`i` head on host tape
`ι i`. -/
theorem embedEmitCfg_selected_pos (ι : Fin m ↪ Fin k)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre : List Symbol) (c : Cfg m Symbol S x) (i : Fin m) :
    (embedEmitCfg ι tapes heads pre c).workTapePos (ι i) = c.workTapePos i := by
  simp [embedEmitCfg, embedSlot_selected]

/-- **The silent transport's capture tape.** If the capture tape `cap` lies outside the selection
`ι`, the transported configuration `Turing.embedSilentCfg ι cap tapes heads pre out₀ c` holds the
recorded word `pre ++ c.output` on `cap`, and that tape's head sits just after it, at
`|pre ++ c.output|`, for every frame, prefix, physical output and source configuration. It is the
capture-field companion of the selected-tape exports, so that consumers need not unfold the
transport's private slot search (the C1-A assembly gate, finding M1). (Technical glue.)

**Proof sketch.** Off the selection the slot search finds no source tape
(`embedSlot_unselected`), so both fields are the capture branch of the transport's
definition. -/
theorem embedSilentCfg_cap (ι : Fin m ↪ Fin k) (cap : Fin k)
    (hcap : cap ∉ Set.range ι)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) :
    (embedSilentCfg ι cap tapes heads pre out₀ c).workTapes cap =
        FinTM.bufferTape (pre ++ c.output) ∧
      (embedSilentCfg ι cap tapes heads pre out₀ c).workTapePos cap =
        ((pre ++ c.output).length : ℤ) := by
  simp [embedSilentCfg, embedSlot_unselected ι cap hcap]


end Turing

namespace Turing

variable {k : ℕ} {Γ : Type*}

/-! ## Reconstruction of embedded configurations (MIG-0b)

The frame export missing beside `Turing.embedEmitCfg_selected_tape` and `_pos`, the selection of
a host configuration, and the **R1 reconstruction lemma** (the wave-1 fill gate's major F1,
acknowledged by the user; backlog F6-1(i), F7-1(b)), with its relabelling and word-layout
corollaries. The first three moved here from `Build/Contract.lean` at MIG-0b's layering split.
All are stated over any universes, like the rest of `Build/Embed`: MIG-0a stated its three over
`Type`, which are instances (the generalization changes nothing else in their statements), so
that the lemma can replace every member of the family at its own signature (`RecordTable`'s
`rt_embed_matches` is stated over `Type*`). -/

/-- The forwarding embedding keeps an unselected tape and head as its frame: the export missing
from `Build/Embed.lean` beside `Turing.embedEmitCfg_selected_tape` and `_pos`. It moved to
`Build/Embed` from `Build/Contract.lean` at MIG-0b's layering split.

**Proof sketch.** At time `0`, `Turing.embedEmitTM_frame` for a one-state machine says exactly
this; the transport's tape fields do not depend on the state type. -/
theorem embedEmitCfg_unselected {m : ℕ} {S : Type*} {x : List Γ} (σ : Fin m ↪ Fin k)
    (tapes : Fin k → ℤ → Option Γ) (heads : Fin k → ℤ) (pre : List Γ) (c : Cfg m Γ S x)
    (j : Fin k) (hj : j ∉ Set.range σ) :
    (embedEmitCfg σ tapes heads pre c).workTapes j = tapes j ∧
      (embedEmitCfg σ tapes heads pre c).workTapePos j = heads j := by
  let M0 : MultiTapeTM m Γ Unit := ⟨(), fun _ _ _ => ⟨0, fun _ => (none, 0), none, none⟩⟩
  let c0 : Cfg m Γ Unit x := ⟨none, c.inputPos, c.workTapes, c.workTapePos, c.output⟩
  have h := (embedEmitTM_frame σ M0 tapes heads pre c0 0).1 j hj
  simp only [MultiTapeTM.runFrom_zero] at h
  exact h

/-- The source configuration seen through an R1 selection: selected tapes and heads, the same
state and input position, and an **empty output**. The selection empties the source output, so
a source precondition is always tested on the output `[]`: `Turing.Contract.embed` transports
output-normalized preconditions only. -/
def Cfg.select {m : ℕ} {S : Type*} {x : List Γ} (σ : Fin m ↪ Fin k)
    (d : Cfg k Γ S x) : Cfg m Γ S x :=
  ⟨d.state, d.inputPos, fun i => d.workTapes (σ i), fun i => d.workTapePos (σ i), []⟩

/-- **The R1 reconstruction lemma** (MIG-0b; backlog F6-1(i), F7-1(b)): an embedded
configuration is determined by its selected bank and its ambient frame. If `d` has the state,
input position and selected tapes and heads of `c`, its output is `pre` followed by `c`'s, and
off the selection it holds the frame `tapes`, `heads`, then `d` is the forwarding embedding of `c`
into that frame. At their migrations it replaces `OracleSim.oracleBankCfg_eq`,
`CodeSimulator.canonEmbedEq`, `Primitives.emitterP2_frame` and the local `hframe` of
`Loop.emCall_exit_fixed` (the MIG-0b fit tests derive each in one term).

**Proof sketch.** Compare field by field. A selected tape or head is the source's
(`Turing.embedEmitCfg_selected_tape`, `_pos`), which is `d`'s by hypothesis; an unselected one is
the frame (`Turing.embedEmitCfg_unselected`), which is `d`'s by hypothesis. The state, the input
position and the output are the hypotheses. -/
theorem embedEmitCfg_eq {m : ℕ} {S : Type*} {x : List Γ} (σ : Fin m ↪ Fin k)
    (tapes : Fin k → ℤ → Option Γ) (heads : Fin k → ℤ) (pre : List Γ) (c : Cfg m Γ S x)
    (d : Cfg k Γ S x) (hs : c.state = d.state) (hin : c.inputPos = d.inputPos)
    (hout : pre ++ c.output = d.output)
    (selected : ∀ i, c.workTapes i = d.workTapes (σ i) ∧ c.workTapePos i = d.workTapePos (σ i))
    (outside : ∀ j, j ∉ Set.range σ → tapes j = d.workTapes j ∧ heads j = d.workTapePos j) :
    embedEmitCfg σ tapes heads pre c = d := by
  have fields (j : Fin k) :
      (embedEmitCfg σ tapes heads pre c).workTapes j = d.workTapes j ∧
        (embedEmitCfg σ tapes heads pre c).workTapePos j = d.workTapePos j := by
    by_cases hj : j ∈ Set.range σ
    · obtain ⟨i, rfl⟩ := hj
      rw [embedEmitCfg_selected_tape, embedEmitCfg_selected_pos]
      exact selected i
    · obtain ⟨ht, hp⟩ := embedEmitCfg_unselected σ tapes heads pre c j hj
      exact ⟨ht.trans (outside j hj).1, hp.trans (outside j hj).2⟩
  exact Cfg.ext hs hin (funext fun j => (fields j).1) (funext fun j => (fields j).2) hout

/-- **R1 reconstruction with state relabelling**: as `Turing.embedEmitCfg_eq`, for a host whose
control is the source's relabelled by `f` (the phase-host and call-controller tags). This is the
shape of `Primitives.emitterP2_frame` and of `Loop.emCall_exit_fixed`'s `hframe`.

**Proof sketch.** Relabelling the embedded configuration is embedding the relabelled source, by
definition; apply `Turing.embedEmitCfg_eq` to it. -/
theorem embedEmitCfg_mapState_eq {m : ℕ} {S H : Type*} {x : List Γ} (σ : Fin m ↪ Fin k)
    (f : S → H) (tapes : Fin k → ℤ → Option Γ) (heads : Fin k → ℤ) (pre : List Γ)
    (c : Cfg m Γ S x) (d : Cfg k Γ H x) (hs : c.state.map f = d.state)
    (hin : c.inputPos = d.inputPos) (hout : pre ++ c.output = d.output)
    (selected : ∀ i, c.workTapes i = d.workTapes (σ i) ∧ c.workTapePos i = d.workTapePos (σ i))
    (outside : ∀ j, j ∉ Set.range σ → tapes j = d.workTapes j ∧ heads j = d.workTapePos j) :
    (embedEmitCfg σ tapes heads pre c).mapState f = d :=
  embedEmitCfg_eq σ tapes heads pre (c.mapState f) d hs hin hout selected outside

/-- **R1 reconstruction, word layout**: embedding a word seam into a word frame gives the word
seam of the combined layout, when the target's selected words are the source's and its other words
the frame's. This is the shape of `CodeSimulator.canonEmbedWords` and `CertShell.cert_embed_words`
(`Build/Embed` imports `Build/Convention`, where `Turing.Cfg.ofWords` lives, for it).

**Proof sketch.** `Turing.embedEmitCfg_eq`: the selected tapes are the source buffers, the other
tapes the frame buffers, and every head is at the origin. -/
theorem embedEmitCfg_ofWords_eq {m : ℕ} {S : Type*} {x : List Bool} (σ : Fin m ↪ Fin k) (q : S)
    (v : Fin m → List Bool) (frame target : Fin k → List Bool)
    (selected : ∀ i, target (σ i) = v i)
    (outside : ∀ j, j ∉ Set.range σ → frame j = target j) :
    embedEmitCfg σ (fun j => FinTM.bufferTape (frame j)) (fun _ => 0) []
        (Cfg.ofWords (input := x) q v) = Cfg.ofWords q target :=
  embedEmitCfg_eq σ _ _ [] _ _ rfl rfl rfl
    (fun i => ⟨congrArg FinTM.bufferTape (selected i).symm, rfl⟩)
    (fun j hj => ⟨congrArg FinTM.bufferTape (outside j hj), rfl⟩)

/-- Every host configuration is the forwarding embedding of its selection, framed by itself:
embedding the selection of `d` into `d`'s own tapes, heads and output gives back `d`.

**Proof sketch.** The R1 reconstruction lemma (`Turing.embedEmitCfg_eq`) at `d`'s own tapes,
heads and output: the selection keeps the state, the input position and the selected tapes and
heads, its empty output follows `d`'s, and off the selection the frame is `d`'s own. -/
theorem embedEmitCfg_select {m : ℕ} {S : Type*} {x : List Γ} (σ : Fin m ↪ Fin k)
    (d : Cfg k Γ S x) :
    embedEmitCfg σ d.workTapes d.workTapePos d.output (d.select σ) = d :=
  embedEmitCfg_eq σ _ _ _ _ d rfl rfl (List.append_nil _) (fun _ => ⟨rfl, rfl⟩)
    (fun _ _ => ⟨rfl, rfl⟩)

end Turing
