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
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.Decryption
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.EvalGate
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.FirstTagged
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.GarbledRun
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.Garbling
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.GarblingProgram
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.Lengths
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.OTInputs
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.ProtocolEfficiency
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.RowFromCoins
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.RunWithHost
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.StatisticalSwitch
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.Strategies
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.TablesFromCoins
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.TwoMoveViews
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.WordLists

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Helpers for Yao’s protocol in the OT-hybrid model

The generic contracts below support polynomial-time garbling, evaluation, message bounds
and simulation without importing the concrete Yao protocol.

## Contents

* `AliceProgram`: AliceProgram.
* `AliceSimulator`: AliceSimulator.
* `AllTables`: AllTables.
* `BobIO`: BobIO.
* `BobInit`: BobInit.
* `BobProgram`: BobProgram.
* `BobSimulator`: BobSimulator.
* `BobTables`: BobTables.
* `CallEquations`: CallEquations.
* `ChunkScanner`: ChunkScanner.
* `CoinGarbling`: CoinGarbling.
* `CoinRead`: CoinRead.
* `CoinRelabel`: CoinRelabel.
* `Decryption`: Decryption.
* `DescriptionDecoder`: DescriptionDecoder.
* `EvalGate`: EvalGate.
* `FirstTagged`: FirstTagged.
* `GarbledRun`: GarbledRun.
* `Garbling`: Garbling.
* `GarblingProgram`: GarblingProgram.
* `Lengths`: Lengths.
* `OTInputs`: OTInputs.
* `ProtocolEfficiency`: ProtocolEfficiency.
* `RowFromCoins`: RowFromCoins.
* `RunWithHost`: RunWithHost.
* `StatisticalSwitch`: StatisticalSwitch.
* `Strategies`: Strategies.
* `TablesFromCoins`: TablesFromCoins.
* `TwoMoveViews`: TwoMoveViews.
* `WordLists`: WordLists.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Protocol 162.6 and Theorem 163.7.
-/
