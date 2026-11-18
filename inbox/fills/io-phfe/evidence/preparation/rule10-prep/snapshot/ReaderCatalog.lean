import Lean
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Classes
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Defs
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Defs.Correctness
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Defs.Efficient
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Defs.Raw
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Defs.Simulator
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Defs
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Layered
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Run
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.SemiAdaptive
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.SemiAdaptive.Data
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.SemiAdaptive.FromTwoStage
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.SemiAdaptive.Games
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.SemiAdaptive.Security
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.SemiAdaptive.Simulator
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Simulation
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Simulation.Games
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Simulation.Security
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Simulation.TwoStage
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearCorrect
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearSecurity.Data
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearSecurity.Endpoint
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearSecurity.Fresh
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearSecurity.Games
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearSecurity.Keys
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearSecurity.Reductions
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearSecurity.Slack
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearSecurity.Theorems
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearSimulator
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Adapter
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.CommittedSimulator
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Core
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Correctness
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Data
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Embedding
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Encodings
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Headlines
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Raw
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Security
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Simulator
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Widths
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticCorrect
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticSecurity.Advice
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticSecurity.Compose
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticSecurity.Data
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticSecurity.Derived
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticSecurity.Fresh
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticSecurity.Games
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticSecurity.Reduction
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticSecurity.Theorems
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticSimulator
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Targets
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Targets.Assembly
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Targets.Garbling
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Targets.LinearEfficiency
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Targets.MatrixDH
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Targets.Scheme
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Targets.Sim
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.WireDraws
import TCSlib.Cryptography.Pairing.Exponents
import TCSlib.Cryptography.Pairing.Linear
import TCSlib.Cryptography.Pairing.MatrixDH
import TCSlib.Cryptography.Pairing.MatrixDH.Defs
import TCSlib.Cryptography.Pairing.MatrixDH.Parameters
import TCSlib.Cryptography.Pairing.MatrixDH.SelfReduction

set_option maxHeartbeats 0
set_option maxRecDepth 65536
open Lean Elab Command

def phfeOwners : List Name := [
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Classes,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Defs,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Defs.Correctness,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Defs.Efficient,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Defs.Raw,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Defs.Simulator,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Defs,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Layered,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Run,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.SemiAdaptive,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.SemiAdaptive.Data,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.SemiAdaptive.FromTwoStage,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.SemiAdaptive.Games,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.SemiAdaptive.Security,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.SemiAdaptive.Simulator,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Simulation,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Simulation.Games,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Simulation.Security,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Simulation.TwoStage,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearCorrect,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearSecurity.Data,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearSecurity.Endpoint,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearSecurity.Fresh,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearSecurity.Games,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearSecurity.Keys,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearSecurity.Reductions,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearSecurity.Slack,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearSecurity.Theorems,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearSimulator,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Adapter,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.CommittedSimulator,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Core,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Correctness,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Data,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Embedding,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Encodings,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Headlines,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Raw,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Security,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Simulator,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Widths,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticCorrect,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticSecurity.Advice,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticSecurity.Compose,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticSecurity.Data,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticSecurity.Derived,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticSecurity.Fresh,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticSecurity.Games,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticSecurity.Reduction,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticSecurity.Theorems,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticSimulator,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Targets,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Targets.Assembly,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Targets.Garbling,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Targets.LinearEfficiency,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Targets.MatrixDH,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Targets.Scheme,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Targets.Sim,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.WireDraws,
  `TCSlib.Cryptography.Pairing.Exponents,
  `TCSlib.Cryptography.Pairing.Linear,
  `TCSlib.Cryptography.Pairing.MatrixDH,
  `TCSlib.Cryptography.Pairing.MatrixDH.Defs,
  `TCSlib.Cryptography.Pairing.MatrixDH.Parameters,
  `TCSlib.Cryptography.Pairing.MatrixDH.SelfReduction]

def phfeReaderPairs : Array (String × String) := #[
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PolyTensor", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.polyTensor_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.xhat", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.xhat_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.polyTensorEval", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.polyTensorEval_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.tupleCoord", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.tupleCoord_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.decodeResidues", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.decodeResidues_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.encodeTensor", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.encodeTensor_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.encodeTensorBits", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.encodeTensorBits_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.decodeTensor", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.decodeTensor_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.privateTensor", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.privateTensor_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.quadEval", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.quadEval_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.phfeEval", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.phfeEval_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.tensorFnLen", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.tensorFnLen_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.encodeScalar", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.encodeScalar_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.phfeClass", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.phfeClassParamEquiv_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.phfeClassParamEquiv", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.phfeClassParamEquiv_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.phfeClassValueEquiv", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.phfeClassValueEquiv_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.quadClass", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.quadClassParamEquiv_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.quadClassParamEquiv", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.quadClassParamEquiv_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.quadClassValueEquiv", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.quadClassValueEquiv_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.duplicatePrivateBits", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.duplicatePrivateBits_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.BidegreeAtMost", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.bidegreeAtMost_iff"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.pubGen", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.pubGen_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.setup", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.setup_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.enc", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.enc_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.keyGen", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.keyGen_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.honestRun", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.honestRun_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.Correct", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.correct_iff"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.CorrectExcept", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.correctExcept_iff"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.Omega.encode", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.Omega.encode_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.Simulator.Raw.encInputWord", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.Simulator.Raw.encInputWord_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.Simulator.Raw.keyInputWord", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.Simulator.Raw.keyInputWord_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.Simulator.Raw.setup", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.Simulator.Raw.setup_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.Simulator.Raw.enc", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.Simulator.Raw.enc_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.Simulator.Raw.key", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.Simulator.Raw.key_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.publicTensor", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.publicTensor_apply"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.pgbCore", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.pgbCore_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.pgbStarCore", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.pgbStarCore_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.paramWord", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.paramWord_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Raw.pgb", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Raw.pgb_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Raw.pgbStar", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Raw.pgbStar_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Raw.rowCoord", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Raw.rowCoord_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Raw.l1ColCoord", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Raw.l1ColCoord_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Raw.outputCoord", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Raw.outputCoord_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Raw.encMIdx", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Raw.encMIdx_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Raw.encTIdx", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Raw.encTIdx_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Raw.encLgen", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Raw.encLgen_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Raw.encRec", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Raw.encRec_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Raw.lgenInput", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Raw.lgenInput_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Raw.recInput", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Raw.recInput_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Layered.MIdx", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Layered.mIdx_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Layered.TIdx", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Layered.tIdx_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Layered.root", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Layered.root_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Layered.node", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Layered.node_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Layered.parent", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Layered.parent_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Layered.lastLabel", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Layered.lastLabel_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Layered.leaf", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Layered.leaf_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Layered.nodeCount", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Layered.nodeCount_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Layered.auxCount", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Layered.auxCount_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Layered.nodeBound", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Layered.nodeBound_zero"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Layered.nodeCoord", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Layered.nodeCoord_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Layered.auxCoord", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Layered.auxCoord_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Layered.L1", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Layered.L1_inr"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Layered.L0", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Layered.L0_inr"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Layered.matrix", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Layered.matrix_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Layered.forward", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Layered.forward_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Layered.rec", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Layered.rec_inr"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Layered.extend", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Layered.extend_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Layered.backward", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Layered.backward_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Layered.shift", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Layered.shift_inr"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.layeredPG_raw", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.layeredPG_raw_mBound"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.detImpl", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.detImpl_apply"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.runDet", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.runDet_zero_of_ret"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.saIn", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.saIn_one"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.saOut", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.saOut_one"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.saSpec", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.saSpec_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.saCodec", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.saCodec_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.saChallengeQuery", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.saChallengeQuery_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.saSplitChallenge", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.saSplitChallenge_snd"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.saKeyFunction", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.saKeyFunction_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.saChallengeMove", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.saChallengeMove_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.saKeyMove", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.saKeyMove_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.saCTAnswer", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.saCTAnswer_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.saSKAnswer", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.saSKAnswer_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.saCTPayload", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.saCTPayload_one"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.saSKPayload", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.saSKPayload_zero"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.saInputWord", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.saInputWord_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.SAAdv.run", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.SAAdv.run_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.saReadMove", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.saReadMove_eq"),
    ("Complexity.NUPPT.toSAAdv", "Complexity.NUPPT.toSAAdv_coins"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.SASimulator.Raw.toSim", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.SASimulator.Raw.toSim_St"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.TwoStage.firstCoins", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.TwoStage.firstCoins_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.TwoStage.secondCoins", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.TwoStage.secondCoins_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.TwoStage.saCommitment", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.TwoStage.saCommitment_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.TwoStage.saNext", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.TwoStage.saNext_nil"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.TwoStage.toSA", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.TwoStage.toSA_coins"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.SAState", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.saState_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.SAIdealState", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.saIdealState_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.saImpl", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.saImpl_one_onSpec"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.realSAChallenge", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.realSAChallenge_some"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.realSAKey", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.realSAKey_none"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.idealSAChallenge", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.idealSAChallenge_some"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.idealSAKey", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.idealSAKey_none"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.realSAImpl", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.realSAImpl_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.idealSAImpl", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.idealSAImpl_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.saGame", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.saGame_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.saSimAdv", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.saSimAdv_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.SASimSecureWith", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.saSimSecureWith_iff"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.SASimSecure", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.saSimSecure_iff"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.SubexpSASimSecureWith", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.subexpSASimSecureWith_iff"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.SubexpSASimSecure", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.subexpSASimSecure_iff"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.SASimulator.Raw.encInputWord", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.SASimulator.Raw.encInputWord_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.SASimulator.Raw.keyInputWord", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.SASimulator.Raw.keyInputWord_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.SASimulator.Raw.setup", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.SASimulator.Raw.setup_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.SASimulator.Raw.enc", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.SASimulator.Raw.enc_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.SASimulator.Raw.key", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.SASimulator.Raw.key_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.viewWordBits", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.viewWordBits_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.viewWord", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.viewWord_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.realView", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.realView_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.idealView", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.idealView_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.simGame", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.simGame_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.simAdv", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.simAdv_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.SimSecureWith", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.simSecureWith_iff"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.SimSecure", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.simSecure_iff"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.SubexpSimSecureWith", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.subexpSimSecureWith_iff"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.SubexpSimSecure", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw.subexpSimSecure_iff"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Commitment.decode", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Commitment.decode_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Commitment.omega", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Commitment.omega_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.SetupDraw", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.setupDraw_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.EncDraw", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.encDraw_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.KeyDraw", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.keyDraw_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.setupCore", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.setupCore_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.encCore", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.encCore_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.keyCore", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.keyCore_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.decFirst", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.decFirst_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.decSecond", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.decSecond_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.dec", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.dec_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.leak", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.leak_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.setup", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.setup_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.enc", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.enc_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.keyGen", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.keyGen_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.scheme_raw", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.scheme_raw_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.Challenge", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.challenge_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.KeyPack", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.keyPack_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.saSpec", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.saSpec_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.SAAdv.run", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.SAAdv.run_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.protocolHandler", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.protocolHandler_challenge"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.securityCount", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.securityCount_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.SecurityDraw", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.securityDraw_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.securityAt", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.securityAt_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.securityOffsets", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.securityOffsets_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.setupAt", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.setupAt_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.seedAt", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.seedAt_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.globalUAt", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.globalUAt_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.paddedDrawIndex", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.paddedDrawIndex_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.keyAt", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.keyAt_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.simKeyAt", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.simKeyAt_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.freshRealHandler", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.freshRealHandler_challenge"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.freshIdealHandler", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.freshIdealHandler_challenge"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.freshSaGame", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.freshSaGame_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.freshSaSimAdv", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.freshSaSimAdv_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.gameHandler", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.gameHandler_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.game0Handler", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.game0Handler_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.game1Handler", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.game1Handler_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.game2Handler", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.game2Handler_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.game3Handler", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.game3Handler_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.game4Handler", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.game4Handler_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.game5Handler", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.game5Handler_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.runGameDet", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.runGameDet_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.game", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.game_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.saGame", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.saGame_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.saSimAdv", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.saSimAdv_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.maskedCipher", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.maskedCipher_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.decomposedKey", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.decomposedKey_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.projectedKey", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.projectedKey_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.semiKey", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.semiKey_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.Advice", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.advice_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.adviceDraw", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.adviceDraw_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.adviceMeta", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.adviceMeta_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.adviceEnc", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.adviceEnc_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.adviceLen", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.adviceLen_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.publicFromGroupA", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.publicFromGroupA_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.red0Handler", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.red0Handler_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.red0", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.red0_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.challengeR", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.challengeR_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.challengeUhat", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.challengeUhat_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.red1Handler", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.red1Handler_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.red1", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.red1_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.groupPGStar", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.groupPGStar_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.basisMatrix", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.basisMatrix_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.SimSetupDraw", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.simSetupDraw_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.simSetupCore", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.simSetupCore_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.simEncCore", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.simEncCore_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.combineRows", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.combineRows_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.SimKeyDraw", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.simKeyDraw_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.simKeyCore", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.simKeyCore_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.simSetup", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.simSetup_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.simEnc", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.simEnc_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.simKey", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.simKey_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.rankSlack", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.rankSlack_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.linearSlack", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear.linearSlack_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.decodeChallenge", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.decodeChallenge_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.wrapKey", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.wrapKey_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.replayStep", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.replayStep_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.replay", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.replay_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.quadraticNext", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.quadraticNext_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.toQuadraticNext", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.toQuadraticNext_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.toQuadratic", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.toQuadratic_coins"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.wee20Sim_raw", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.wee20Sim_raw_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.setupCore", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.setupCore_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.encCore", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.encCore_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.keyCore", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.keyCore_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.dec", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.dec_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.TensorFn", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.tensorFn_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.PGSound", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.pgSound_iff"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.classParam", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.classParam_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.valueEquiv", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.valueEquiv_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.embedValue", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.embedValue_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.decodePublic", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.decodePublic_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.decodePrivate", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.decodePrivate_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.decodeFunction", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.decodeFunction_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.keyWord", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.keyWord_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.encMPK", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.encMPK_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.encMSK", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.encMSK_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.encSK", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.encSK_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.encCT", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.encCT_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.wee20PHFE_raw", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.wee20PHFE_raw_G"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.publicParamsEquiv", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.publicParamsEquiv_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.mpkEquiv", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.mpkEquiv_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.keyEquiv", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.keyEquiv_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.ctEquiv", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.ctEquiv_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.scalarValueEquiv", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.scalarValueEquiv_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wee20RealizableSA", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.wee20RealizableSA_iff"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wee20Realizable43", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.wee20Realizable43_iff"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.wee20SASim_raw", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.wee20SASim_raw_setupCore"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.mpkLen", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.mpkLen_eval"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.mskLen", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.mskLen_eval"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.skLen", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.skLen_eval"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.ctLen", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.ctLen_eval"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.piDim", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.piDim_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.signalCoord", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.signalCoord_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.mixScalar", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.mixScalar_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.mixGroup", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.mixGroup_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.signalScalar", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.signalScalar_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.signalGroup", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.signalGroup_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.SetupDraw", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.setupDraw_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.EncDraw", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.encDraw_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.setupCore", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.setupCore_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.encCore", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.encCore_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.keyCore", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.keyCore_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.value", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.value_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.dec", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.dec_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.setup", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.setup_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.enc", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.enc_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.keyGen", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.keyGen_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.scheme_raw", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.scheme_raw_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.MaskAdvice", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.maskAdvice_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.maskAdviceDraw", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.maskAdviceDraw_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.Advice", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.advice_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.adviceDraw", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.adviceDraw_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.maskAdviceMeta", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.maskAdviceMeta_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.maskAdviceEnc", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.maskAdviceEnc_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.maskAdviceLen", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.maskAdviceLen_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.adviceEnc", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.adviceEnc_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.adviceLen", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.adviceLen_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.hopCols", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.hopCols_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.hopRows", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.hopRows_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.quadraticSlack", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.quadraticSlack_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.Challenge", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.challenge_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.KeyPack", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.keyPack_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.saSpec", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.saSpec_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.SAAdv.run", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.SAAdv.run_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.protocolHandler", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.protocolHandler_challenge"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.maskCount", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.maskCount_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.MaskDraw", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.maskDraw_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.maskAt", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.maskAt_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.masksAt", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.masksAt_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.SecurityDraw", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.securityDraw_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.wrapLinearCT", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.wrapLinearCT_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.wrapLinearKey", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.wrapLinearKey_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.replayLinear", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.replayLinear_nil"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.derivedNext", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.derivedNext_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.toLinear", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.toLinear_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.freshRealHandler", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.freshRealHandler_challenge"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.freshIdealHandler", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.freshIdealHandler_challenge"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.freshSaGame", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.freshSaGame_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.freshSaSimAdv", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.freshSaSimAdv_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.maskedVectors", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.maskedVectors_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.publicFromMasks", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.publicFromMasks_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.gameHandler", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.gameHandler_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.game0Handler", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.game0Handler_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.game1Handler", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.game1Handler_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.game2Handler", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.game2Handler_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.game3Handler", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.game3Handler_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.game4Handler", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.game4Handler_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.runGameDet", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.runGameDet_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.game", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.game_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.saGame", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.saGame_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.saSimAdv", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.saSimAdv_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.crossLeakLeft", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.crossLeakLeft_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.crossLeakRight", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.crossLeakRight_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.red2Handler", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.red2Handler_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.red3Handler", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.red3Handler_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.red2", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.red2_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.red3", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.red3_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.SimSetupDraw", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.simSetupDraw_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.SimEncDraw", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.simEncDraw_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.simSetupCore", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.simSetupCore_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.simEncCore", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.simEncCore_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.crossLeak", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.crossLeak_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.simKeyCore", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.simKeyCore_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.simSetup", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.simSetup_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.simEnc", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.simEnc_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.simKey", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic.simKey_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.layeredPG", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.layeredPG_toRaw"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.wee20PHFE", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.wee20PHFE_toRaw"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.wee20Sim", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.wee20Sim_toRaw"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.wee20SASim", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.wee20SASim_toRaw"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.linearEncInput", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.linearEncInput_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearEfficient", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.linearEfficient_iff"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.MddhPreTargets", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.mddhPreTargets_iff"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire.groupVector", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire.groupVector_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire.groupMatrix", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire.groupMatrix_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire.linearMPK", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire.linearMPK_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire.linearMSK", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire.linearMSK_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire.linearCT", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire.linearCT_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire.linearKey", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire.linearKey_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire.quadraticMPK", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire.quadraticMPK_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire.quadraticMSK", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire.quadraticMSK_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire.quadraticCT", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire.quadraticCT_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire.quadraticKey", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire.quadraticKey_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire.scalarVector", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire.scalarVector_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire.scalarMatrix", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire.scalarMatrix_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire.linearSetupDraw", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire.linearSetupDraw_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire.quadraticSetupDraw", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire.quadraticSetupDraw_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire.quadraticEncDraw", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire.quadraticEncDraw_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire.linearKeyDraw", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire.linearKeyDraw_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire.linearSimSetupDraw", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire.linearSimSetupDraw_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire.quadraticSimSetupDraw", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire.quadraticSimSetupDraw_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire.linearSimKeyDraw", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire.linearSimKeyDraw_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire.linearSimState", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire.linearSimState_eq"),
    ("TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire.quadraticSimState", "TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire.quadraticSimState_eq"),
    ("TCSlib.Cryptography.Pairing.groupDot", "TCSlib.Cryptography.Pairing.groupDot_eq"),
    ("TCSlib.Cryptography.Pairing.groupMulVec", "TCSlib.Cryptography.Pairing.groupMulVec_apply"),
    ("TCSlib.Cryptography.Pairing.groupVecMul", "TCSlib.Cryptography.Pairing.groupVecMul_apply"),
    ("TCSlib.Cryptography.Pairing.groupMatMul", "TCSlib.Cryptography.Pairing.groupMatMul_apply"),
    ("TCSlib.Cryptography.Pairing.matMulGroup", "TCSlib.Cryptography.Pairing.matMulGroup_apply"),
    ("TCSlib.Cryptography.Pairing.BilinearGroup.expVec", "TCSlib.Cryptography.Pairing.BilinearGroup.expVec_apply"),
    ("TCSlib.Cryptography.Pairing.BilinearGroup.expMat", "TCSlib.Cryptography.Pairing.BilinearGroup.expMat_apply"),
    ("TCSlib.Cryptography.Pairing.BilinearGroup.expVecT", "TCSlib.Cryptography.Pairing.BilinearGroup.expVecT_apply"),
    ("TCSlib.Cryptography.Pairing.BilinearGroup.expMatT", "TCSlib.Cryptography.Pairing.BilinearGroup.expMatT_apply"),
    ("TCSlib.Cryptography.Pairing.BilinearGroup.pairVec", "TCSlib.Cryptography.Pairing.BilinearGroup.pairVec_eq"),
    ("TCSlib.Cryptography.Pairing.BilinearGroup.pairMat", "TCSlib.Cryptography.Pairing.BilinearGroup.pairMat_apply"),
    ("TCSlib.Cryptography.Pairing.BilinearGroup.pairTensor", "TCSlib.Cryptography.Pairing.BilinearGroup.pairTensor_apply"),
    ("TCSlib.Cryptography.Pairing.dlinStr", "TCSlib.Cryptography.Pairing.dlinStr_eq"),
    ("TCSlib.Cryptography.Pairing.dlinMatrix", "TCSlib.Cryptography.Pairing.dlinMatrix_eq"),
    ("TCSlib.Cryptography.Pairing.BilinearGen.dlinChallenge", "TCSlib.Cryptography.Pairing.BilinearGen.dlinChallenge_eq"),
    ("TCSlib.Cryptography.Pairing.BilinearGen.dlinEnc", "TCSlib.Cryptography.Pairing.BilinearGen.dlinEnc_eq"),
    ("TCSlib.Cryptography.Pairing.BilinearGen.dlinSample", "TCSlib.Cryptography.Pairing.BilinearGen.dlinSample_eq"),
    ("TCSlib.Cryptography.Pairing.BilinearGen.dlinGame", "TCSlib.Cryptography.Pairing.BilinearGen.dlinGame_eq"),
    ("TCSlib.Cryptography.Pairing.BilinearGen.dlinAdv", "TCSlib.Cryptography.Pairing.BilinearGen.dlinAdv_eq"),
    ("TCSlib.Cryptography.Pairing.BilinearGen.DLINAssumption", "TCSlib.Cryptography.Pairing.BilinearGen.dlinAssumption_iff"),
    ("TCSlib.Cryptography.Pairing.BilinearGen.SubexpDLIN", "TCSlib.Cryptography.Pairing.BilinearGen.subexpDLIN_iff"),
    ("TCSlib.Cryptography.Pairing.BilinearGen.dlinMatrixSample", "TCSlib.Cryptography.Pairing.BilinearGen.dlinMatrixSample_eq"),
    ("TCSlib.Cryptography.Pairing.BilinearGen.dlinMatrixGame", "TCSlib.Cryptography.Pairing.BilinearGen.dlinMatrixGame_eq"),
    ("TCSlib.Cryptography.Pairing.BilinearGen.dlinMatrixAdv", "TCSlib.Cryptography.Pairing.BilinearGen.dlinMatrixAdv_eq"),
    ("TCSlib.Cryptography.Pairing.BilinearGen.dlinMatrixSlack", "TCSlib.Cryptography.Pairing.BilinearGen.dlinMatrixSlack_eq"),
    ("TCSlib.Cryptography.Pairing.BilinearGroup.groupMatrixEnc", "TCSlib.Cryptography.Pairing.BilinearGroup.groupMatrixEnc_eq"),
    ("TCSlib.Cryptography.Pairing.BilinearGen.mddhEnc", "TCSlib.Cryptography.Pairing.BilinearGen.mddhEnc_eq"),
    ("TCSlib.Cryptography.Pairing.BilinearGen.mddhSample", "TCSlib.Cryptography.Pairing.BilinearGen.mddhSample_eq"),
    ("TCSlib.Cryptography.Pairing.BilinearGen.mddhGame", "TCSlib.Cryptography.Pairing.BilinearGen.mddhGame_eq"),
    ("TCSlib.Cryptography.Pairing.BilinearGen.mddhAdv", "TCSlib.Cryptography.Pairing.BilinearGen.mddhAdv_eq"),
    ("TCSlib.Cryptography.Pairing.GroupDescription", "TCSlib.Cryptography.Pairing.groupDescription_eq"),
    ("TCSlib.Cryptography.Pairing.PublicParams.group", "TCSlib.Cryptography.Pairing.PublicParams.group_eq"),
    ("TCSlib.Cryptography.Pairing.PublicParams.orderParam", "TCSlib.Cryptography.Pairing.PublicParams.orderParam_val"),
    ("TCSlib.Cryptography.Pairing.PublicParams.encode", "TCSlib.Cryptography.Pairing.PublicParams.encode_eq"),
    ("TCSlib.Cryptography.Pairing.GeneratorDraw", "TCSlib.Cryptography.Pairing.generatorDraw_eq"),
    ("TCSlib.Cryptography.Pairing.publicParamsCore", "TCSlib.Cryptography.Pairing.publicParamsCore_eq"),
    ("TCSlib.Cryptography.Pairing.publicParamsGen", "TCSlib.Cryptography.Pairing.publicParamsGen_eq"),
    ("TCSlib.Cryptography.Pairing.BilinearGen.MddhAdvice", "TCSlib.Cryptography.Pairing.BilinearGen.mddhAdvice_eq"),
    ("TCSlib.Cryptography.Pairing.BilinearGen.mddhAdviceDefault", "TCSlib.Cryptography.Pairing.BilinearGen.mddhAdviceDefault_eq"),
    ("TCSlib.Cryptography.Pairing.BilinearGen.mddhAdviceEnc", "TCSlib.Cryptography.Pairing.BilinearGen.mddhAdviceEnc_eq"),
    ("TCSlib.Cryptography.Pairing.BilinearGen.mddhAdviceLen", "TCSlib.Cryptography.Pairing.BilinearGen.mddhAdviceLen_eq"),
    ("TCSlib.Cryptography.Pairing.BilinearGen.mddhPreChallenge", "TCSlib.Cryptography.Pairing.BilinearGen.mddhPreChallenge_eq"),
    ("TCSlib.Cryptography.Pairing.BilinearGen.mddhPre", "TCSlib.Cryptography.Pairing.BilinearGen.mddhPre_eq"),
    ("TCSlib.Cryptography.Pairing.BilinearGen.dlinToMddh", "TCSlib.Cryptography.Pairing.BilinearGen.dlinToMddh_eq"),
    ("TCSlib.Cryptography.Pairing.BilinearGen.mddhSlack", "TCSlib.Cryptography.Pairing.BilinearGen.mddhSlack_eq"),
    ("TCSlib.Cryptography.Pairing.BilinearGen.MDDHRealizable", "TCSlib.Cryptography.Pairing.BilinearGen.mddhRealizable_iff")
]

run_cmd do
  let env ← getEnv
  let mut byString : Std.HashMap String (Array Name) := {}
  for (n, _) in env.constants.toList do
    byString := byString.insert n.toString (((byString[n.toString]?).getD #[]).push n)
  let mut verified := 0
  for (target, reader) in phfeReaderPairs do
    let targets := (byString[target]?).getD #[]
    let readers := (byString[reader]?).getD #[]
    if targets.size != 1 || readers.size != 1 then
      IO.println ("PHFE_READER " ++ (Json.mkObj [("target", toJson target),
        ("reader", toJson reader), ("ok", toJson false),
        ("reason", toJson "missing or ambiguous actual Lean name")]).compress)
      continue
    let t := targets[0]!
    let r := readers[0]!
    let some ci := env.find? r | throwError "reader vanished"
    let theoremFlag := match ci with | .thmInfo _ => true | _ => false
    let containsTarget := ci.type.getUsedConstants.contains t
    let ok := theoremFlag && containsTarget
    let home := (env.getModuleIdxFor? r).map fun i => env.header.moduleNames[i.toNat]!.toString
    IO.println ("PHFE_READER " ++ (Json.mkObj [("target", toJson target),
      ("reader", toJson reader), ("reader_home", toJson home), ("ok", toJson ok),
      ("reader_is_theorem", toJson theoremFlag),
      ("reader_type_mentions_target", toJson containsTarget)]).compress)
    if ok then verified := verified + 1
  for (n, ci) in env.constants.toList do
    let some i := env.getModuleIdxFor? n | continue
    let home := env.header.moduleNames[i.toNat]!
    unless phfeOwners.contains home do continue
    unless ci.isDefinition do continue
    let proofFlag ← Lean.Elab.Command.liftTermElabM <| Lean.Meta.isProp ci.type
    let abbrevFlag := match ci with
      | .defnInfo d => match d.hints with | .abbrev => true | _ => false
      | _ => false
    IO.println ("PHFE_DEFINITION " ++ (Json.mkObj [("name", toJson n.toString),
      ("home", toJson home.toString), ("projection", toJson (env.isProjectionFn n)),
      ("instance", toJson (Lean.Meta.isInstanceCore env n)),
      ("matcher", toJson (Lean.Meta.isMatcherCore env n)),
      ("abbrev", toJson abbrevFlag), ("proof_valued", toJson proofFlag)]).compress)
  IO.println ("PHFE_READER_DONE " ++ (Json.mkObj [("requested", toJson phfeReaderPairs.size),
    ("verified", toJson verified)]).compress)
  unless verified == phfeReaderPairs.size do
    throwError "PHFE reader census incomplete: {verified}/{phfeReaderPairs.size}"

run_cmd IO.println "PHFE_SNAPSHOT {\"head\": \"5b5d8430e1d0f514a2edb6cad28847c44894acc4\", \"snapshot_sha256\": \"739836c6975671ac93f9dcca9b6a9b26f559bb0e4a2c6e7ae63d129d26894ba2\"}"
