/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.ChunkScanner
import TCSlib.Complexity.CircuitComplexity.DAGCircuitSatLang
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.ReductionMachine
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut requested := 0
  let mut excluded := 0
  for (name, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let home := env.header.moduleNames[idx.toNat]!
      if home.toString.startsWith "TCSlib." then
        if let .defnInfo d := ci then
          let status ← liftCoreM <| Lean.getReducibilityStatus name
          let matcher := Lean.Meta.isMatcherCore env name
          let rec body : Nat → Expr → Expr
            | 0, e => e
            | fuel+1, .lam _ _ b _ => body fuel b
            | fuel+1, .letE _ _ v b _ => body fuel (b.instantiate1 v)
            | _, e => e
          let ty := d.type.getForallBody.getAppFn.constName?
          let val := body 64 d.value
          let coe := ty == some `CoeFun || ty == some `Coe
          let map := if val.getAppArgs.isEmpty then val else val.getAppArgs.back!
          let projection := match (body 64 map).getAppFn with
            | .proj .. => true
            | .const n _ => env.isProjectionFn n
            | _ => false
          let isNotation : Bool := (name == `Complexity.PolyExpr.eval && true) ||
            (false && coe && projection)
          if isNotation || (status == .reducible && !matcher) then
            excluded := excluded + 1
            logInfo m!"EXCLUDED\t{home}\t{name}"
          else
            let id := mkIdent name
            if status != .irreducible then
              elabCommand (← `(command| attribute [local irreducible] $id:ident))
            let installed ← liftCoreM <| Lean.getReducibilityStatus name
            unless installed == .irreducible do
              throwError "seal not installed: {name}"
            requested := requested + 1
            logInfo m!"SEALED\t{home}\t{name}"
  logInfo m!"SEAL_COUNTS requested={requested} excluded={excluded}"

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A polynomial-time host for circuit descriptions

The decoder converts the unary circuit-description grammar to the library's encoded lists
of words. It supplies the input count, gate kinds, and argument indices as independently
accessible words. A supplied output list is retained verbatim. The conversion is total on
malformed descriptions as well; its correctness contract concerns every encoded circuit.

`DAGCircuit.decode_encode` already validates and reconstructs canonical descriptions. This
host instead supplies a polynomial-time representation for subsequent traversal, without
needing to unfold that decoder or copy its validity checks.

## Main definitions

* `DescriptionDecoder.gateRecord`: a kind word paired with encoded unary argument words.
* `DescriptionDecoder.readCircuit`: a unary input count paired with encoded gate records.
* `DescriptionDecoder.decodeDescription`: parse the circuit half and retain the output half.

## Main results

* `DescriptionDecoder.readCircuit_encode`: correctness on every circuit encoding.
* `DescriptionDecoder.decodeDescription_host`: one clean machine with polynomial time and
  work-head envelopes,
  together with correctness on circuit descriptions carrying an arbitrary output word.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009, §6.2 (descriptions of uniform circuit families).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Protocol 162.6 (the canonical circuit description).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder

open Complexity Turing BoolCircuit ChunkScanner

-- Control phases: input unary, gate marker, kind bit one, kind bit two,
-- argument marker, argument unary, done. The eighth code is also absorbing.
private def next : Phase → Bool → Phase
  | (false, false, false), b => if b then (false, false, false) else (false, false, true)
  | (false, false, true), b => if b then (false, true, false) else (true, true, false)
  | (false, true, false), _ => (false, true, true)
  | (false, true, true), _ => (true, false, false)
  | (true, false, false), b => if b then (true, false, true) else (false, false, true)
  | (true, false, true), b => if b then (true, false, true) else (true, false, false)
  | (true, true, c), _ => (true, true, c)

private def output : Phase → Bool → List Bool
  | (false, false, false), b => if b then [true, true] else [false, true]
  | (false, false, true), _ => []
  | (false, true, false), b => List.replicate 4 b
  | (false, true, true), b => List.replicate 4 b ++ [false, false, true, true]
  | (true, false, false), b => if b then [] else [false, true]
  | (true, false, true), b =>
      if b then [true, true, true, true] else [false, false, true, true]
  | (true, true, _), _ => []

/-- A gate record is `⟨g.kind.encode, encWords (g.args.map (fun a => 1^a))⟩`.
[PS10, Protocol 162.6], a representation for decoding the canonical circuit. -/
def gateRecord (g : DAGGate) : List Bool :=
  pairEncode g.kind.encode (BinArith.encWords (g.args.map fun a => List.replicate a true))

/-- `gateRecord g = ⟨g.kind.encode, encWords (g.args.map (fun a => 1^a))⟩`. -/
theorem gateRecord_eq (g : DAGGate) :
    gateRecord g =
      pairEncode g.kind.encode
        (BinArith.encWords (g.args.map fun a => List.replicate a true)) := rfl

/-- Parse the circuit grammar into `⟨1^inputCount, encWords gateRecords⟩`.
[AB09, §6.2], using the seven finite control phases described above. -/
def readCircuit (w : List Bool) : List Bool :=
  ChunkScanner.scan next output (false, false, false) w

/-- `readCircuit w = ChunkScanner.scan next output (false, false, false) w`. -/
theorem readCircuit_eq (w : List Bool) :
    readCircuit w = ChunkScanner.scan next output (false, false, false) w := rfl

/-- Circuit-description parsing is polynomial-time: `PolyTimeComputable readCircuit`. -/
theorem readCircuit_poly : PolyTimeComputable readCircuit :=
  ChunkScanner.scan_poly next output (false, false, false)

/-- Parse a description pair, retaining its output word:
`decodeDescription w = ⟨readCircuit (pairFstD w), pairSndD w⟩`. -/
def decodeDescription (w : List Bool) : List Bool :=
  pairEncode (readCircuit (pairFstD w)) (pairSndD w)

/-- `decodeDescription w = ⟨readCircuit (pairFstD w), pairSndD w⟩`. -/
theorem decodeDescription_eq (w : List Bool) :
    decodeDescription w = pairEncode (readCircuit (pairFstD w)) (pairSndD w) := rfl

/-- The total description decoder is polynomial-time:
`PolyTimeComputable decodeDescription`. -/
theorem decodeDescription_poly : PolyTimeComputable decodeDescription :=
  (readCircuit_poly.comp polyTimeComputable_pairFstD).pairEncode polyTimeComputable_pairSndD

private theorem dbl_pair (a b : List Bool) :
    dbl (pairEncode a b) =
      dbl (dbl a) ++ [false, false, true, true] ++ dbl b := by
  rw [pairEncode_eq_dbl, MultiMsg.dbl_append, MultiMsg.dbl_append]
  simp only [dbl_cons, dbl_nil, List.append_assoc]

private theorem scan_done (w : List Bool) :
    ChunkScanner.scan next output (true, true, false) w = [] := by
  induction w with
  | nil => exact ChunkScanner.scan_nil _ _ _
  | cons b w ih =>
    rw [ChunkScanner.scan_cons]
    simpa only [next, output, List.nil_append] using ih

private theorem scan_input (n : ℕ) (r : List Bool) :
    ChunkScanner.scan next output (false, false, false)
        (List.replicate n true ++ false :: r) =
      dbl (List.replicate n true) ++ [false, true] ++
        ChunkScanner.scan next output (false, false, true) r := by
  induction n with
  | zero =>
    simp only [List.replicate_zero, List.nil_append, ChunkScanner.scan_cons, next,
      output, Bool.false_eq_true, if_false, dbl_nil]
  | succ n ih =>
    simp only [List.replicate_succ, List.cons_append, ChunkScanner.scan_cons, next,
      output, if_true, dbl_cons, ih, List.cons_append, List.nil_append]

private theorem scan_argument (n : ℕ) (r : List Bool) :
    ChunkScanner.scan next output (true, false, true)
        (List.replicate n true ++ false :: r) =
      dbl (dbl (List.replicate n true)) ++ [false, false, true, true] ++
        ChunkScanner.scan next output (true, false, false) r := by
  induction n with
  | zero =>
    simp only [List.replicate_zero, List.nil_append, ChunkScanner.scan_cons, next,
      output, Bool.false_eq_true, if_false, dbl_nil]
  | succ n ih =>
    simp only [List.replicate_succ, List.cons_append, ChunkScanner.scan_cons, next,
      output, if_true, dbl_cons, ih, List.cons_append, List.nil_append]

private theorem scan_arguments (args : List ℕ) (r : List Bool) :
    ChunkScanner.scan next output (true, false, false) (encodeList encodeNat args ++ r) =
      dbl (BinArith.encWords (args.map fun a => List.replicate a true)) ++ [false, true] ++
        ChunkScanner.scan next output (false, false, true) r := by
  induction args with
  | nil =>
    simp only [encodeList_nil, List.singleton_append, ChunkScanner.scan_cons, next,
      output, Bool.false_eq_true, if_false, List.map_nil, BinArith.encWords_nil,
      dbl_nil, List.nil_append]
  | cons a args ih =>
    rw [encodeList_cons, List.cons_append, ChunkScanner.scan_cons]
    simp only [next, output, if_true, List.nil_append]
    simp only [encodeNat_def, List.append_assoc, List.cons_append, List.nil_append]
    rw [scan_argument, ih, List.map_cons, BinArith.encWords_cons, dbl_pair]
    simp only [List.append_assoc, List.cons_append, List.nil_append]

private theorem scan_gate (g : DAGGate) (r : List Bool) :
    ChunkScanner.scan next output (false, true, false) (g.encode ++ r) =
      dbl (gateRecord g) ++ [false, true] ++
        ChunkScanner.scan next output (false, false, true) r := by
  cases g with
  | mk k args =>
    cases k <;>
      simp only [DAGGate.encode_eq, GateKind.encode_and, GateKind.encode_or,
        GateKind.encode_not, List.cons_append, List.nil_append, ChunkScanner.scan_cons,
        next, output, List.replicate_succ, List.replicate_zero, scan_arguments,
        gateRecord_eq, dbl_pair, dbl_cons, dbl_nil, List.append_assoc]

private theorem scan_gates (gs : List DAGGate) (r : List Bool) :
    ChunkScanner.scan next output (false, false, true) (encodeList DAGGate.encode gs ++ r) =
      BinArith.encWords (gs.map gateRecord) := by
  induction gs with
  | nil =>
    simp only [encodeList_nil, List.singleton_append, ChunkScanner.scan_cons, next,
      output, Bool.false_eq_true, if_false, scan_done, List.map_nil,
      BinArith.encWords_nil, List.nil_append]
  | cons g gs ih =>
    rw [encodeList_cons, List.cons_append, ChunkScanner.scan_cons]
    simp only [next, output, if_true, List.nil_append]
    rw [List.append_assoc, scan_gate, ih, List.map_cons, BinArith.encWords_cons,
      pairEncode_eq_dbl]

/-- On every circuit, parsing returns the unary input count and every gate record:
`readCircuit C.encode = ⟨1^n, encWords (C.gates.map gateRecord)⟩`. [AB09, §6.2]

**Proof sketch.** The input-count phase doubles the unary count and emits the pair
separator. Each gate's two kind bits become the first field of its gate record; each unary
argument becomes one encoded word. The gate-list terminator enters an absorbing phase,
so the circuit's distinguished output field does not affect the list. Induction on the
argument and gate lists proves these identities without any fan-in assumption. -/
theorem readCircuit_encode {n : ℕ} (C : DAGCircuit n) :
    readCircuit C.encode =
      pairEncode (List.replicate n true) (BinArith.encWords (C.gates.map gateRecord)) := by
  rw [readCircuit_eq, DAGCircuit.encode_parts]
  simp only [encodeNat_def, List.append_assoc, List.singleton_append]
  rw [scan_input, scan_gates, pairEncode_eq_dbl]

/-- On a circuit description paired with any output word, the host returns
`⟨⟨1^n, encWords (C.gates.map gateRecord)⟩, outs⟩`.
[PS10, Protocol 162.6], decoding the canonical description with an output list. -/
theorem decodeDescription_pair {n : ℕ} (C : DAGCircuit n) (outs : List Bool) :
    decodeDescription (pairEncode C.encode outs) =
      pairEncode
        (pairEncode (List.replicate n true) (BinArith.encWords (C.gates.map gateRecord)))
        outs := by
  rw [decodeDescription_eq, pairFstD_pairEncode, pairSndD_pairEncode, readCircuit_encode]

/-- **The circuit-description decoder host**: one clean finite machine installs
`decodeDescription arg` and emits nothing within `A · (|arg| + 1)^c` steps. Every work head
of that same machine remains within this envelope at every time. On `⟨C.encode, outs⟩` the
installed word is `⟨⟨1^n, encWords (C.gates.map gateRecord)⟩, outs⟩`.
[AB09, §6.2; PS10, Protocol 162.6]

The machine uses the registered H14 clean-install host; the work-head bound is its
`Clean.envelope` contract, so correctness, time, and work heads refer to the same machine. -/
theorem decodeDescription_host :
    ∃ (M : FinTM Bool) (A c : ℕ),
      ModuleHost.Clean M decodeDescription (fun _ => []) (fun n => A * (n + 1) ^ c) ∧
      (∀ (x arg : List Bool) (v : ℕ) (j : Fin M.k),
        |(M.tm.runFrom
          (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) v).workTapePos j| ≤
            (A * (arg.length + 1) ^ c : ℕ)) ∧
      ∀ (n : ℕ) (C : DAGCircuit n) (outs : List Bool),
        decodeDescription (pairEncode C.encode outs) =
          pairEncode
            (pairEncode (List.replicate n true) (BinArith.encWords (C.gates.map gateRecord)))
            outs := by
  obtain ⟨M, A, c, hM⟩ := ModuleHost.clean_install decodeDescription_poly
  exact ⟨M, A, c, hM, (fun x arg v j => hM.envelope x arg v j),
    fun _ C outs => decodeDescription_pair C outs⟩

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.DescriptionDecoder
