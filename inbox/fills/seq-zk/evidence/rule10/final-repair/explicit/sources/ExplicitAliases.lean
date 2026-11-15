import Lean
import TCSlib.Cryptography.Composability.SequentialZK
import TCSlib.Cryptography.Composability.SequentialZK.Advice
import TCSlib.Cryptography.Composability.SequentialZK.BoundedMetadata
import TCSlib.Cryptography.Composability.SequentialZK.ComputationalAdvice
import TCSlib.Cryptography.Composability.SequentialZK.ComputationalHybrid
import TCSlib.Cryptography.Composability.SequentialZK.ComputationalPhaseBound
import TCSlib.Cryptography.Composability.SequentialZK.ComputationalReduction
import TCSlib.Cryptography.Composability.SequentialZK.ComputationalTransfer
import TCSlib.Cryptography.Composability.SequentialZK.Congruence
import TCSlib.Cryptography.Composability.SequentialZK.ContinuationProbability
import TCSlib.Cryptography.Composability.SequentialZK.Efficiency
import TCSlib.Cryptography.Composability.SequentialZK.EndpointSampling
import TCSlib.Cryptography.Composability.SequentialZK.ErrSoundness
import TCSlib.Cryptography.Composability.SequentialZK.ExecutionBounds
import TCSlib.Cryptography.Composability.SequentialZK.HybridRecursion
import TCSlib.Cryptography.Composability.SequentialZK.Normalization
import TCSlib.Cryptography.Composability.SequentialZK.NormalizationMachine
import TCSlib.Cryptography.Composability.SequentialZK.NormalizedStep
import TCSlib.Cryptography.Composability.SequentialZK.PaddedProverSpec
import TCSlib.Cryptography.Composability.SequentialZK.PhaseView
import TCSlib.Cryptography.Composability.SequentialZK.Phases
import TCSlib.Cryptography.Composability.SequentialZK.PrefixFolds
import TCSlib.Cryptography.Composability.SequentialZK.PrefixLaws
import TCSlib.Cryptography.Composability.SequentialZK.ProofTransfers
import TCSlib.Cryptography.Composability.SequentialZK.RealPhases
import TCSlib.Cryptography.Composability.SequentialZK.RealPrefixBounds
import TCSlib.Cryptography.Composability.SequentialZK.ReductionAdvantage
import TCSlib.Cryptography.Composability.SequentialZK.RepeatedSoundness
import TCSlib.Cryptography.Composability.SequentialZK.RepeatedVerifier
import TCSlib.Cryptography.Composability.SequentialZK.SimulatorMachine
import TCSlib.Cryptography.Composability.SequentialZK.Soundness
import TCSlib.Cryptography.Composability.SequentialZK.Statistical
import TCSlib.Cryptography.Composability.SequentialZK.StatisticalPostprocess
import TCSlib.Cryptography.Composability.SequentialZK.StatisticalPrefix
import TCSlib.Cryptography.Composability.SequentialZK.StatisticalRecursion
import TCSlib.Cryptography.Composability.SequentialZK.StatisticalTransfer
import TCSlib.Cryptography.Composability.SequentialZK.SuffixLaws
import TCSlib.Cryptography.Composability.SequentialZK.SuffixMachine
import TCSlib.Cryptography.Composability.SequentialZK.VerifierPrefix
import TCSlib.Cryptography.Composability.SequentialZK.WrappedVerifier
import TCSlib.Cryptography.ZeroKnowledge.Defs

set_option maxHeartbeats 0
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let names : Array Name := #[`Classical.not_not, `Complexity.NUPPT.Uniform.advice_eq, `Eq.trans, `Iff.mp, `List.mem_singleton, `List.prefix_iff_eq_append, `MulZeroClass.mul_zero, `MulZeroClass.zero_mul, `TCSlib.Cryptography.AbortRetry.attempt, `TCSlib.Cryptography.AbortRetry.firstHit_map_getD_eq, `TCSlib.Cryptography.AbortRetry.retry, `TCSlib.Cryptography.Composability.PaddedVerifierSpec.first_eq, `TCSlib.Cryptography.Composability.PaddedVerifierSpec.local_length, `TCSlib.Cryptography.Composability.PaddedVerifierSpec.next_eq, `TCSlib.Cryptography.Composability.PaddedVerifierSpec.outV_eq, `TCSlib.Cryptography.Composability.PaddedVerifierSpec.period, `TCSlib.Cryptography.Composability.PaddedVerifierSpec.phase_take, `TCSlib.Cryptography.Composability.PaddedVerifierSpec.rounds_eq, `TCSlib.Cryptography.Composability.PaddedVerifierSpec.terminal_eq, `TCSlib.Cryptography.SequentialZK.PaddedProverSpec.boundary, `TCSlib.Cryptography.SequentialZK.PaddedProverSpec.first, `TCSlib.Cryptography.SequentialZK.PaddedProverSpec.next, `TCSlib.Cryptography.SequentialZK.PaddedProverSpec.realCoinsEquiv_fst_ofFn, `TCSlib.Cryptography.SequentialZK.PaddedProverSpec.rounds_eval]
  for n in names do
    let some ci := env.find? n | throwError "Missing explicit alias {n}"
    let kind := match ci with
      | .defnInfo _ => "def" | .thmInfo _ => "theorem" | .opaqueInfo _ => "opaque"
      | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"
      | .inductInfo _ => "inductive" | .axiomInfo _ => "axiom" | .quotInfo _ => "quotient"
    let home := (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!.toString
    let prop ← liftTermElabM do Meta.isProp ci.type
    IO.println ("EXPLICIT_ALIAS " ++ (Json.mkObj [("name", toJson n.toString),
      ("kind", toJson kind), ("home", toJson home),
      ("projection", toJson (env.isProjectionFn n)), ("type_is_Prop", toJson prop)]).compress)
  IO.println s!"EXPLICIT_ALIAS_DONE {names.size}"
