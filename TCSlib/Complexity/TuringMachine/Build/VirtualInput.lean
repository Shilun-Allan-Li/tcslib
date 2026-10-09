/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Simulation
import TCSlib.Complexity.TuringMachine.Build.Embed

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: virtual-input hosting (Z1)

The virtual-input layer of the machine-construction library
(`machine-library-design.md` §13, Z1): a verified machine whose *input* is
a designated **buffered word** on a work tape runs inside a host, one host
step per source step, with the buffer read-only, the source's work bank
intact, and the source's input movement realized as the clamped buffer
movement of `Turing.FinTM.virtualMove` under the `VirtualTag` boundary
discipline. This is the pattern the proved corpus has hand-rebuilt five
times — `Turing.FinTM.bufferedCompTM`'s second phase
(`bufferedSecondCfg_step`/`_run`, the public template for the contracts
below), the A2 forwarding controller's `a2_mapVirtual` lockstep and the
F2A `f2_splitCount*` virtual-empty-input hosting (both private in
`Build/Catalog.lean`), the universal interpreter's input discipline, and
the oblivious candidate's `obliviousVisit` transduction — promoted to one
transformer pair.

## Design (decisions 13.4 and 13a, recorded in the design document)

* **Canonical layout, relocation by composition.** The transformer is
  defined on exactly `1 + m` work tapes — the buffer first, the payload
  bank after it. A consumer needing the buffer or bank elsewhere composes
  with the R1 embeddings of `Build/Embed.lean`; relocation is never baked
  in.
* **A silent/emit pair over one core** (the 12.4 shape). The forwarding
  flavor `vhostEmitTM` passes source emissions to the host's physical
  output. The suppressing flavor `vhostSilentTM` is *defined as the layer
  composing with itself*: the R1 capture wrapper `embedSilentTM` applied
  to `vhostEmitTM` at the identity-shaped selection, with one extra
  capture tape appended — so its contracts are instances of the two
  layers' contracts, never a third lockstep.
* **The boundary tag lives in the control state** (`S × Bool`, the
  `a2_MapState.run q tag` precedent): a stationary move preserves the
  tag, so repeated outward attempts at a blank boundary stay clamped,
  with **no nonempty-input premise anywhere** — on an empty buffered word
  the two boundaries are adjacent and the clamps still hold.
* **Setup is the consumer's.** The transformer owns the hosting from a
  loaded buffer onward; parsing, loading, and rewinding the buffer, and
  choosing the seam, belong to the consumer (the A2 controller's parse
  stages are the precedent), seamed with R2.

## Status: statement skeleton (§13 statement phase, tranche A-S1)

The transformers and the configuration transport below are real
definitions; every contract is `sorry`d with a proof sketch, awaiting the
A-S1 statement gate and its fill epoch. The sketches name the proved
template each fill adapts.

## Main definitions and results

* `Turing.vhostCfg` — the configuration transport: a source configuration
  on virtual input `y`, a boundary tag, a frozen native input position,
  and a prior output prefix, viewed inside the `1 + m`-tape host.
* `Turing.vhostEmitTM` — the forwarding transformer.
* `Turing.vhostSilentTM` — the suppressing/capturing transformer, as the
  R1 capture of the forwarding flavor.
* `Turing.vhostEmitTM_runFrom` — the lockstep: one host step per source
  step, at every time, with a valid arrival tag; halted sources are
  absorbed; no halting, liveness, or nonempty-input hypotheses.
* `Turing.vhostEmitTM_visitedByTapeHead_bank` /
  `Turing.vhostEmitTM_visitedByTapeHead_buffer` — the bank tapes visit
  exactly the source's cells; the buffer head's trajectory is exactly the
  source's input trajectory shifted by one.
* `Turing.vhostEmitTM_spaceUsed_le` — the coefficient-one space ledger:
  host space is at most source space plus the buffer interval
  `y.length + 2`.
* `Turing.vhostSilentTM_runFrom` / `Turing.vhostSilentTM_spaceUsed_le` —
  the suppressing flavor's instances.
* Permanent regression lemmas (adopted from the F2 epoch audit):
  `Turing.vhostCfg_buffer_head_mem` (the clamp interval, empty word
  included) and `Turing.vhostEmitTM_emitting_halt` (a source halting
  emission is forwarded before the host control dies).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern
  Approach*, Cambridge University Press, 2009. (§1.2; running a machine
  on a stored word is the folklore of every simulation argument there.)
* In-repo precedents harvested (design §13, Evidence):
  `Turing.FinTM.bufferedCompTM` phase two (`Simulation.lean`, proved);
  `a2_mapVirtual`/`a2_mapVirtual_step`/`a2_mapVirtual_run` and
  `f2_splitCountAction`/`f2_splitCount_run` (`Build/Catalog.lean`,
  proved, private); the audited A2/F2 contracts bind the clamp and
  halt-absorption clauses below.
-/

namespace Turing

variable {m : ℕ} {S : Type*} {x y : List Bool}

/-- The buffer tape of the canonical virtual-input host: the first of its
`1 + m` work tapes. -/
def vhostBuffer (m : ℕ) : Fin (1 + m) := Fin.castAdd m (0 : Fin 1)

/-- The payload-bank tape of the canonical virtual-input host carrying the
source's work tape `i`. -/
def vhostBank (i : Fin m) : Fin (1 + m) := Fin.natAdd 1 i

/-- A source configuration on virtual input `y`, viewed inside the
`1 + m`-tape host over native input `x`: the control carries the source
state and the boundary tag; the native input head sits frozen at `p`; the
buffer holds `y` with its head at the source's input position minus one
(the `Turing.FinTM.bufferTape_inputSymbol` convention); the bank holds the
source's work tapes and heads verbatim; and the host output is the prior
prefix `pre` followed by everything the source has emitted. A halted
source maps to a halted host. -/
def vhostCfg (c : Cfg m Bool S y) (b : Bool) (p : Fin (x.length + 2))
    (pre : List Bool) : Cfg (1 + m) Bool (S × Bool) x where
  state := c.state.map (fun q => (q, b))
  inputPos := p
  workTapes := Fin.addCases (fun _ => FinTM.bufferTape y) c.workTapes
  workTapePos := Fin.addCases (fun _ => (c.inputPos.val : ℤ) - 1) c.workTapePos
  output := pre ++ c.output

/-- **Z1, the forwarding virtual-input transformer** (design §13, decision
13.4). Host the `m`-tape machine `M` on `1 + m` tapes with its input read
from the buffer: each step reads the buffer cell as the source's input
symbol, performs the source's work actions on the bank, realizes the
source's input movement as the clamped buffer movement, forwards the
source's emission physically, never moves the native input head, and
carries the arrival tag in control. The initial tag is `true` (valid at
the canonical start position `1` for every `y`, the empty word included).
Setup — loading `y` onto the buffer and arriving at a `vhostCfg` seam — is
the consumer's, by R2 composition. -/
def vhostEmitTM (M : MultiTapeTM m Bool S) :
    MultiTapeTM (1 + m) Bool (S × Bool) where
  q₀ := (M.q₀, true)
  tr := fun qb _inp w =>
    let v := w (vhostBuffer m)
    let a := M.tr qb.1 v (fun i => w (vhostBank i))
    let mv := FinTM.virtualMove qb.2 v a.inputTape
    ⟨0, Fin.addCases (fun _ => ((none : Option (Option Bool)), mv)) a.workTapes,
      a.output, a.state.map (fun q => (q, FinTM.virtualNextTag qb.2 mv))⟩

/-- The capture tape of the suppressing flavor: the extra last tape of its
`(1 + m) + 1` work tapes. -/
def vhostCap (m : ℕ) : Fin ((1 + m) + 1) := Fin.natAdd (1 + m) (0 : Fin 1)

/-- **Z1, the suppressing virtual-input transformer**: the layer composing
with itself. The R1 capture wrapper runs the forwarding host on the first
`1 + m` tapes of a `(1 + m) + 1`-tape machine, records every emission on
the appended capture tape, and emits nothing physically. Its contracts are
instances of `Turing.embedSilentTM`'s over `Turing.vhostEmitTM`'s — no
third lockstep exists. -/
def vhostSilentTM (M : MultiTapeTM m Bool S) :
    MultiTapeTM ((1 + m) + 1) Bool (S × Bool) :=
  embedSilentTM (Fin.castAddEmb 1) (vhostCap m) (vhostEmitTM M)

/-- The suppressing flavor's configuration transport: the forwarding
transport (with empty inner prefix) viewed through the R1 silent transport
— capture word `capPre` followed by the source's emissions, ambient frame
nowhere (the single unselected tape is the capture tape), physical output
the untouched `out₀`. -/
def vhostSilentCfg (c : Cfg m Bool S y) (b : Bool) (p : Fin (x.length + 2))
    (capPre out₀ : List Bool) : Cfg ((1 + m) + 1) Bool (S × Bool) x :=
  embedSilentCfg (Fin.castAddEmb 1) (vhostCap m) (fun _ _ => none) (fun _ => 0)
    capPre out₀ (vhostCfg c b p [])

/-- One forwarding host step simulates one source step, producing a valid
arrival tag; the statement includes the absorbing halted case and the
empty buffered word, with no liveness or nonemptiness premises.

**Proof sketch.** The template is the proved
`Turing.FinTM.bufferedSecondCfg_step`, with the first block removed and
the output prefix carried along. A halted source is fixed on both sides.
On a live state, buffer reads at the source input position minus one equal
source input reads (`bufferTape_inputSymbol`); `virtualMove_correct`
supplies the buffer-head equation and the new tag; the bank performs the
source's work actions; the emission appends to `pre ++ c.output` by
associativity; the native head and buffer contents are fixed; the
successor control carries the new tag, dying exactly when the source
halts. -/
theorem vhostEmitTM_step (M : MultiTapeTM m Bool S) (c : Cfg m Bool S y)
    (b : Bool) (hb : FinTM.VirtualTag c.inputPos b) (p : Fin (x.length + 2))
    (pre : List Bool) :
    ∃ b', FinTM.VirtualTag (M.step c).inputPos b' ∧
      (vhostEmitTM M).step (vhostCfg c b p pre) =
        vhostCfg (M.step c) b' p pre := by
  sorry

/-- The forwarding lockstep at every time: one host step per source step,
with a valid arrival tag at the endpoint. Completed outputs are preserved
and a halted source stays absorbed; `t = 0` and the empty buffered word
are instances, not exceptions.

**Proof sketch.** Induct on `t` and chain `vhostEmitTM_step`, exactly as
`Turing.FinTM.bufferedSecondCfg_run` chains its step lemma. -/
theorem vhostEmitTM_runFrom (M : MultiTapeTM m Bool S) (c : Cfg m Bool S y)
    (b : Bool) (hb : FinTM.VirtualTag c.inputPos b) (p : Fin (x.length + 2))
    (pre : List Bool) (t : ℕ) :
    ∃ b', FinTM.VirtualTag (M.runFrom c t).inputPos b' ∧
      (vhostEmitTM M).runFrom (vhostCfg c b p pre) t =
        vhostCfg (M.runFrom c t) b' p pre := by
  sorry

/-- Bank tape `i` of the forwarding host visits exactly the cells the
source's tape `i` visits, at every horizon.

**Proof sketch.** Project `vhostEmitTM_runFrom` at each time
`u ≤ t` onto the head of `vhostBank i`: the transported configuration
holds the source head verbatim, so the two `Finset.image`s over
`Finset.range (t + 1)` agree pointwise. -/
theorem vhostEmitTM_visitedByTapeHead_bank (M : MultiTapeTM m Bool S)
    (c : Cfg m Bool S y) (b : Bool) (hb : FinTM.VirtualTag c.inputPos b)
    (p : Fin (x.length + 2)) (pre : List Bool) (t : ℕ) (i : Fin m) :
    (vhostEmitTM M).visitedByTapeHead (vhostCfg c b p pre) t (vhostBank i) =
      M.visitedByTapeHead c t i := by
  sorry

/-- The buffer head's trajectory is exactly the source's input trajectory
shifted by one: at every horizon, the buffer tape's visited set is the
image of the source's input positions minus one.

**Proof sketch.** Project `vhostEmitTM_runFrom` at each `u ≤ t` onto the
buffer head, which the transport pins at the source input position minus
one. -/
theorem vhostEmitTM_visitedByTapeHead_buffer (M : MultiTapeTM m Bool S)
    (c : Cfg m Bool S y) (b : Bool) (hb : FinTM.VirtualTag c.inputPos b)
    (p : Fin (x.length + 2)) (pre : List Bool) (t : ℕ) :
    (vhostEmitTM M).visitedByTapeHead (vhostCfg c b p pre) t (vhostBuffer m) =
      (Finset.range (t + 1)).image
        (fun u => ((M.runFrom c u).inputPos.val : ℤ) - 1) := by
  sorry

/-- The buffer head stays inside `[-1, y.length]` at every time — the
permanent form of the two boundary clamps, the empty buffered word
included (there the interval is `[-1, 0]` and outward moves stay put).
Adopted as a permanent regression lemma from the F2 epoch audit.

**Proof sketch.** By `vhostEmitTM_runFrom` the buffer head at time `u` is
the source input position minus one, and input positions inhabit
`Fin (y.length + 2)`. -/
theorem vhostCfg_buffer_head_mem (M : MultiTapeTM m Bool S)
    (c : Cfg m Bool S y) (b : Bool) (hb : FinTM.VirtualTag c.inputPos b)
    (p : Fin (x.length + 2)) (pre : List Bool) (t : ℕ) :
    ((vhostEmitTM M).runFrom (vhostCfg c b p pre) t).workTapePos
        (vhostBuffer m) ∈ Finset.Icc (-1 : ℤ) (y.length : ℤ) := by
  sorry

/-- The coefficient-one space ledger of the forwarding host: host space is
at most source space plus the buffer interval. No term depends on the
source's output or on the host horizon beyond the source's own space.

**Proof sketch.** Sum over the `1 + m` tapes: each bank tape's visited set
equals the source's (`vhostEmitTM_visitedByTapeHead_bank`), and the
buffer's visited set lies in the `y.length + 2`-cell interval
(`vhostCfg_buffer_head_mem`), so its cardinality is at most
`y.length + 2`. -/
theorem vhostEmitTM_spaceUsed_le (M : MultiTapeTM m Bool S)
    (c : Cfg m Bool S y) (b : Bool) (hb : FinTM.VirtualTag c.inputPos b)
    (p : Fin (x.length + 2)) (pre : List Bool) (t : ℕ) :
    (vhostEmitTM M).spaceUsed (vhostCfg c b p pre) t ≤
      M.spaceUsed c t + (y.length + 2) := by
  sorry

/-- A source halting step that emits is forwarded before the host control
dies: the emitted bit lands on the host output and the host halts in the
same step. Adopted as a permanent regression lemma from the F2 epoch audit
(the "closed embeddings lose the final halting emission" lesson, checked
here in the positive).

**Proof sketch.** Instantiate `vhostEmitTM_step` at a live `c` whose
action has `state = none` and `output = some bit`: the transported
successor is the halted source step, whose output is
`pre ++ c.output ++ [bit]` by the step identity. -/
theorem vhostEmitTM_emitting_halt (M : MultiTapeTM m Bool S)
    (c : Cfg m Bool S y) (b : Bool) (hb : FinTM.VirtualTag c.inputPos b)
    (p : Fin (x.length + 2)) (pre : List Bool) (q : S) (bit : Bool)
    (hq : c.state = some q)
    (ha : (M.tr q c.inputSymbol c.workTapeSymbols).state = none)
    (ho : (M.tr q c.inputSymbol c.workTapeSymbols).output = some bit) :
    ((vhostEmitTM M).step (vhostCfg c b p pre)).state = none ∧
      ((vhostEmitTM M).step (vhostCfg c b p pre)).output =
        pre ++ c.output ++ [bit] := by
  sorry

/-- The suppressing lockstep at every time: capture records the source's
emissions after the prior capture prefix, the physical output stays
`out₀`, and the arrival tag stays valid.

**Proof sketch.** Chain the two layers: `vhostEmitTM_runFrom` transports
the source run through the forwarding host, and the R1 silent lockstep
(`embedSilentTM_runFrom`) transports the forwarding host's run through the
capture wrapper; `vhostSilentCfg` is by definition the composite
transport. No third induction is performed. -/
theorem vhostSilentTM_runFrom (M : MultiTapeTM m Bool S) (c : Cfg m Bool S y)
    (b : Bool) (hb : FinTM.VirtualTag c.inputPos b) (p : Fin (x.length + 2))
    (capPre out₀ : List Bool) (t : ℕ) :
    ∃ b', FinTM.VirtualTag (M.runFrom c t).inputPos b' ∧
      (vhostSilentTM M).runFrom (vhostSilentCfg c b p capPre out₀) t =
        vhostSilentCfg (M.runFrom c t) b' p capPre out₀ := by
  sorry

/-- The suppressing flavor's space ledger: source space, the buffer
interval, and the capture word — coefficient one on the source term.

**Proof sketch.** The R1 silent space clauses give the selected tapes' and
capture tape's contributions over the forwarding host's run; substitute
the forwarding ledger (`vhostEmitTM_spaceUsed_le` tape by tape) for the
selected bank, and bound the capture tape by its final word length plus
one via `bufferTape_append` growth. -/
theorem vhostSilentTM_spaceUsed_le (M : MultiTapeTM m Bool S)
    (c : Cfg m Bool S y) (b : Bool) (hb : FinTM.VirtualTag c.inputPos b)
    (p : Fin (x.length + 2)) (capPre out₀ : List Bool) (t : ℕ) :
    (vhostSilentTM M).spaceUsed (vhostSilentCfg c b p capPre out₀) t ≤
      M.spaceUsed c t + (y.length + 2) +
        ((capPre ++ (M.runFrom c t).output).length + 1) := by
  sorry

end Turing
