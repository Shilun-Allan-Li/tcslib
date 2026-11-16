/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.AliceProgram
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.AliceSimulator
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.AllTables
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.BobIO
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.BobInit
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.BobProgram
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.BobSimulator
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.BobTables
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.CallEquations
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.ChunkScanner
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.CoinGarbling
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.CoinRead
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.CoinRelabel
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.CoinSeedRelabel
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.Decryption
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.EvalGate
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.FakeMessage
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.FakeObjects
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.FakeProgram
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.FirstTagged
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.GarbledRun
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.Garbling
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.GarblingProgram
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.GateHybrids
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.GateOccurrences
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.Lengths
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.OTInputs
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.ProtocolEfficiency
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.RelabelGarbling
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.RowFromCoins
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.RunWithHost
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.SimulationBound
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.SliceReduction
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.StatisticalSwitch
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.Strategies
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.TablesFromCoins
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.TwoMoveViews
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.WordLists
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
            (true && coe && projection)
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
# Helpers for Yao’s protocol in the OT-hybrid model

These generic contracts provide total garbling/evaluation programs, message bounds,
simulator machines, exact seed relabelings and the probability framework for gate hybrids.
They do not import the concrete Yao protocol.

## Contents

* `AliceProgram`: polynomial-time Alice messages from generic circuit and seed readers.
* `AliceSimulator`: a copying simulator for an Alice-first two-message view.
* `AllTables`: polynomial-time assembly of all garbled tables.
* `BobIO`: reading the output of an encoded garbled evaluation.
* `BobInit`: polynomial-time initial keys for a garbled evaluation.
* `BobProgram`: the complete generic polynomial-time garbled-circuit evaluator.
* `BobSimulator`: a polynomial-time Bob simulator from generic fake-garbling interfaces.
* `BobTables`: a total row-table selector for the garbled-evaluation host.
* `CallEquations`: the bit-OT input machines and a product call index.
* `ChunkScanner`: finite scanners with word-valued emissions.
* `CoinGarbling`: polynomial-time garbling coin addresses.
* `CoinRead`: polynomial-time windows of a coin string.
* `CoinRelabel`: exact coin-block bijections for garbling.
* `CoinSeedRelabel`: the tape-to-seed coin relabeling bridge.
* `Decryption`: tagged special decryption at arbitrary message lengths.
* `DescriptionDecoder`: a polynomial-time host for circuit descriptions.
* `EvalGate`: polynomial-time garbled-gate evaluation.
* `FakeMessage`: the canonical encoded simulated garbling message.
* `FakeObjects`: active-key simulated garblings.
* `FakeProgram`: polynomial-time simulated garbling programs.
* `FirstTagged`: first successful tagged row in polynomial time.
* `GarbledRun`: the generic polynomial-time garbled-evaluation host.
* `Garbling`: polynomial-time leaves for circuit garbling.
* `GarblingProgram`: generic garbling programs from uniform circuit descriptions.
* `GateHybrids`: two-stage garbled-gate hybrids.
* `GateOccurrences`: all occurrences of a selected inactive wire label.
* `Lengths`: length bounds for garbled messages.
* `OTInputs`: polynomial-time inputs for bit oblivious transfers.
* `ProtocolEfficiency`: message bounds for an Alice-first two-move protocol.
* `RelabelGarbling`: seed-by-seed relabeling of a generic garbling.
* `RowFromCoins`: a polynomial-time row garbler from coin words.
* `RunWithHost`: a polynomial-time host for data-dependent gate evaluation.
* `SimulationBound`: combining the two simulation bounds.
* `SliceReduction`: advice and averaging for a slice-encryption reduction.
* `StatisticalSwitch`: statistical switches outside a bad event.
* `Strategies`: efficient first-message and reply strategies.
* `TablesFromCoins`: polynomial-time garbled tables from coin words.
* `TwoMoveViews`: views of an Alice-first two-message protocol.
* `WordLists`: polynomial-time encoded word vectors.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Protocol 162.6 and Theorem 163.7.
-/
