/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Complexity.CircuitComplexity.DAGCircuit
import TCSlib.Complexity.ClassP.BinaryArith.Words
import TCSlib.Complexity.Randomized.Repetition

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A polynomial-time host for data-dependent gate evaluation

A gate traversal retains its input and a state consisting of the unprocessed gate records
and the current encoded vertex data. Its leaf routine receives the retained input, one gate
record and the vertex data, and returns the vertex data extended by the gate's result.
The host is generic in the gate records, the vertex-data encoding and the leaf routine.

Unlike the CVAL decider, this host returns the entire encoded value list and permits a
polynomial-time, input-dependent gate operation. It uses the registered state-loop host;
there is no new transition table.

## Main definitions

* `RunWithHost.step`: one gate-record traversal step.
* `RunWithHost.acc`: the test that no gate records remain.

## Main results

* `RunWithHost.orbit_eq`: the traversal state after a gate prefix.
* `RunWithHost.polyTimeComputable_runWith`: polynomial time under a polynomial state envelope.
* `RunWithHost.exists_machine`: one finite machine and a uniform polynomial time envelope.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009, §6.1 (topologically ordered circuits).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Protocol 162.6 (garbled evaluation).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.RunWithHost

open Complexity Turing BoolCircuit

/-- The traversal step sends `⟨x, ⟨records, values⟩⟩` to
`⟨tail records, F ⟨x, ⟨head records, values⟩⟩⟩`.
The outer retained input is maintained by the state-loop host.
`step F w = pairEncode (pairSndD (pairFstD (pairSndD w))) (F (pairEncode (pairFstD w) (pairEncode
(pairFstD (pairFstD (pairSndD w))) (pairSndD (pairSndD w)))))`. -/
def step (F : List Bool → List Bool) (w : List Bool) : List Bool :=
  pairEncode (pairSndD (pairFstD (pairSndD w)))
    (F (pairEncode (pairFstD w)
      (pairEncode (pairFstD (pairFstD (pairSndD w))) (pairSndD (pairSndD w)))))

/-- For every word `w`, `step F w` drops its first gate record and calls `F` on
`⟨fst w, ⟨head records, values⟩⟩`.
`step F w = pairEncode (pairSndD (pairFstD (pairSndD w))) (F (pairEncode (pairFstD w) (pairEncode
(pairFstD (pairFstD (pairSndD w))) (pairSndD (pairSndD w)))))`. -/
theorem step_eq (F : List Bool → List Bool) (w : List Bool) :
    step F w = pairEncode (pairSndD (pairFstD (pairSndD w)))
      (F (pairEncode (pairFstD w)
        (pairEncode (pairFstD (pairFstD (pairSndD w))) (pairSndD (pairSndD w))))) := rfl

/-- The traversal accepts exactly when its remaining record list is empty:
`acc w = decide (fst (snd w) = [])`. -/
def acc (w : List Bool) : Bool := decide (pairFstD (pairSndD w) = [])

/-- For every word `w`, `acc w = decide (pairFstD (pairSndD w) = [])`. -/
theorem acc_eq (w : List Bool) : acc w = decide (pairFstD (pairSndD w) = []) := rfl

/-- If `F` is polynomial-time, then `step F` is polynomial-time; it consists of
pair projections, two pairings and one call to `F`.
`PolyTimeComputable (step F)`. -/
theorem step_poly {F : List Bool → List Bool} (hF : PolyTimeComputable F) :
    PolyTimeComputable (step F) :=
  ((polyTimeComputable_pairSndD.comp
      (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)).pairEncode
    (hF.comp (polyTimeComputable_pairFstD.pairEncode
      ((polyTimeComputable_pairFstD.comp
          (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)).pairEncode
        (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)))))

/-- The one-bit acceptance test `w ↦ [acc w]` is polynomial-time.
`PolyTimeComputable fun w => [acc w]`. -/
theorem acc_poly : PolyTimeComputable fun w => [acc w] :=
  polyTimeComputable_isNil.comp
    (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)

/-- After `i ≤ |gs x|` rounds, the state is the unprocessed gate suffix paired with
`valueCode x (runWith (f x) ((gs x).take i) (init x))`.

**Proof sketch.** At round zero the prefix is empty. At a successor round the head
of the remaining encoded list is the next gate record. The leaf contract appends
its computed value, and the append and singleton equations of `runWith` identify
the result with evaluation of the next prefix. -/
theorem orbit_eq {β : List Bool → Type} (gateCode : DAGGate → List Bool)
    (valueCode : ∀ x, List (β x) → List Bool) (gs : List Bool → List DAGGate)
    (init : ∀ x, List (β x)) (f : ∀ x, DAGGate → List (β x) → β x)
    (F : List Bool → List Bool)
    (hnext : ∀ x g vs,
      F (pairEncode x (pairEncode (gateCode g) (valueCode x vs))) =
        valueCode x (vs ++ [f x g vs])) (x : List Bool) :
    ∀ i, i ≤ (gs x).length →
      StateLoop.orbit
          (fun z => pairEncode (BinArith.encWords ((gs z).map gateCode)) (valueCode z (init z)))
          (step F) x i =
        pairEncode (BinArith.encWords (((gs x).drop i).map gateCode))
          (valueCode x (runWith (f x) ((gs x).take i) (init x))) := by
  intro i
  induction i with
  | zero =>
    intro _
    rw [StateLoop.orbit_zero, List.drop_zero, List.take_zero, runWith_nil]
  | succ i ih =>
    intro hi
    have hilt : i < (gs x).length := by omega
    rw [StateLoop.orbit_succ, ih (by omega), step_eq]
    simp only [pairFstD_pairEncode, pairSndD_pairEncode]
    rw [List.drop_eq_getElem_cons hilt, List.map_cons, BinArith.encWords_cons]
    simp only [pairFstD_pairEncode, pairSndD_pairEncode]
    rw [hnext, List.take_succ_eq_append_getElem hilt, runWith_append, runWith_singleton]

/-- Evaluating `gs x` from `init x` and returning its `valueCode` is polynomial-time
when the encoded input maps and leaf routine are polynomial-time, the gate count
is at most `R |x|`, and every encoded prefix state has length at most `B |x|`.
The leaf receives `⟨x, ⟨gateCode g, valueCode x vs⟩⟩` and returns
`valueCode x (vs ++ [f x g vs])`. [PS10, Protocol 162.6]
`PolyTimeComputable fun x => valueCode x (runWith (f x) (gs x) (init x))`.

**Proof sketch.** Use the public state-loop host with the unprocessed gate records
and current vertex data as state. The orbit equation gives the caller's length
bound. Before the last round the encoded suffix contains a pair, so it is nonempty;
at the gate count it is empty. Thus the loop stops at exactly the gate count and
its second projection is the encoded result of `runWith`. -/
theorem polyTimeComputable_runWith {β : List Bool → Type} (gateCode : DAGGate → List Bool)
    (valueCode : ∀ x, List (β x) → List Bool) (gs : List Bool → List DAGGate)
    (init : ∀ x, List (β x)) (f : ∀ x, DAGGate → List (β x) → β x)
    {F : List Bool → List Bool}
    (hgs : PolyTimeComputable fun x => BinArith.encWords ((gs x).map gateCode))
    (hinit : PolyTimeComputable fun x => valueCode x (init x)) (hF : PolyTimeComputable F)
    (hnext : ∀ x g vs,
      F (pairEncode x (pairEncode (gateCode g) (valueCode x vs))) =
        valueCode x (vs ++ [f x g vs])) (R B : PolyExpr)
    (hN : ∀ x, (gs x).length ≤ R.eval x.length)
    (hbound : ∀ x i, i ≤ (gs x).length →
      (pairEncode (BinArith.encWords (((gs x).drop i).map gateCode))
        (valueCode x (runWith (f x) ((gs x).take i) (init x)))).length ≤ B.eval x.length) :
    PolyTimeComputable fun x => valueCode x (runWith (f x) (gs x) (init x)) := by
  have h := polyTimeComputable_stateFind (hgs.pairEncode hinit) (step_poly hF)
    acc_poly (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
    R B (fun x => (gs x).length) hN
    (fun x i hi => by
      rw [orbit_eq gateCode valueCode gs init f F hnext x i hi]
      exact hbound x i hi)
    (fun x i hi => by
      rw [orbit_eq gateCode valueCode gs init f F hnext x i hi.le, acc_eq]
      simp only [pairFstD_pairEncode, pairSndD_pairEncode]
      rw [List.drop_eq_getElem_cons hi, List.map_cons, BinArith.encWords_cons]
      apply decide_eq_false_iff_not.mpr
      exact pairEncode_ne_nil _ _)
    (fun x => by
      rw [orbit_eq gateCode valueCode gs init f F hnext x _ le_rfl, acc_eq]
      simp only [pairSndD_pairEncode, pairFstD_pairEncode, List.drop_length,
        List.map_nil, BinArith.encWords_nil, decide_true])
  convert h using 1
  funext x
  rw [orbit_eq gateCode valueCode gs init f F hnext x _ le_rfl]
  simp only [Function.comp_apply, pairSndD_pairEncode, List.take_length]

/-- There is one clean evaluation machine `M` with a polynomial budget
`A (|arg| + 1)^d`, installing `valueCode arg (runWith (f arg) (gs arg) (init arg))`
and emitting nothing. At every time every work head of that same machine is
within the budget of the origin. The hypotheses are those of
`polyTimeComputable_runWith`. [PS10, Protocol 162.6]
`∃ (M : FinTM Bool) (A d : ℕ), ModuleHost.Clean M (fun x => valueCode x (runWith (f x) (gs x) (init
x))) (fun _ => []) (fun n => A * (n + 1) ^ d) ∧ ∀ (x arg : List Bool) (v : ℕ) (j : Fin M.k),
|(M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) v).workTapePos j| ≤ (A *
(arg.length + 1) ^ d : ℕ)`.

The machine is obtained by applying the registered H14 clean-install contract to
the traversal's polynomial-time function; its head envelope is H14's `Clean.envelope`. -/
theorem exists_machine {β : List Bool → Type} (gateCode : DAGGate → List Bool)
    (valueCode : ∀ x, List (β x) → List Bool) (gs : List Bool → List DAGGate)
    (init : ∀ x, List (β x)) (f : ∀ x, DAGGate → List (β x) → β x)
    {F : List Bool → List Bool}
    (hgs : PolyTimeComputable fun x => BinArith.encWords ((gs x).map gateCode))
    (hinit : PolyTimeComputable fun x => valueCode x (init x)) (hF : PolyTimeComputable F)
    (hnext : ∀ x g vs,
      F (pairEncode x (pairEncode (gateCode g) (valueCode x vs))) =
        valueCode x (vs ++ [f x g vs])) (R B : PolyExpr)
    (hN : ∀ x, (gs x).length ≤ R.eval x.length)
    (hbound : ∀ x i, i ≤ (gs x).length →
      (pairEncode (BinArith.encWords (((gs x).drop i).map gateCode))
        (valueCode x (runWith (f x) ((gs x).take i) (init x)))).length ≤ B.eval x.length) :
    ∃ (M : FinTM Bool) (A d : ℕ),
      ModuleHost.Clean M (fun x => valueCode x (runWith (f x) (gs x) (init x)))
          (fun _ => []) (fun n => A * (n + 1) ^ d) ∧
        ∀ (x arg : List Bool) (v : ℕ) (j : Fin M.k),
          |(M.tm.runFrom
            (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) v).workTapePos j| ≤
              (A * (arg.length + 1) ^ d : ℕ) := by
  obtain ⟨M, A, d, hM⟩ := ModuleHost.clean_install
    (polyTimeComputable_runWith gateCode valueCode gs init f hgs hinit hF hnext R B hN hbound)
  exact ⟨M, A, d, hM, fun x arg v j => hM.envelope x arg v j⟩

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.RunWithHost
