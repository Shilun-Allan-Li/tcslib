import TCSlib.Cryptography.Games.Machines
import TCSlib.Cryptography.Games.Efficiency
import TCSlib.Cryptography.Games.Efficiency.Replay
import TCSlib.Cryptography.Games.Efficiency.OracleBridge
import TCSlib.Cryptography.Games.Hopping
import TCSlib.Cryptography.Games.OracleComp
import TCSlib.Cryptography.Games.Probability
import TCSlib.Cryptography.Games.Simulate
import TCSlib.Cryptography.Games.BitCodec
import TCSlib.Cryptography.Foundations.BitLists
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.Asymptotic.EnsemblesLemmas
import TCSlib.Cryptography.Asymptotic.Ensembles
import TCSlib.Cryptography.Asymptotic.OneWayLemmas
import TCSlib.Cryptography.Asymptotic.OneWay
import TCSlib.Cryptography.Asymptotic.OneWayYao
import TCSlib.Cryptography.Asymptotic.HardCoreLoops
import TCSlib.Cryptography.Candidates.Factoring
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM.Evaluator
import TCSlib.Cryptography.ZeroKnowledge.Commitment
import TCSlib.Cryptography.ZeroKnowledge.CommitmentLemmas
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.ColRepSound
import TCSlib.Cryptography.Authentication.Signatures.Lamport
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.ReductionMachine
import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Handler
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Handler
import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity
import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity.ChallengeSim
import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity.PaddedCPA
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability.Forward
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability.Decrypt
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability.Encrypt
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Generic
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Hybrid
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.SimIND
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.SimINDGap
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Rounds
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Challenge
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Simulator
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Reduction
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Recover
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.IndSim
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Machines
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.SoundnessRep

open Lean Elab Command

/-! Axioms of every stored constant of the dl-folds superset files (superset), and of the campaign
endpoints. One `AX` line each. -/

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mods : Std.HashSet Name := Std.HashSet.ofList [`TCSlib.Cryptography.Games.Machines, `TCSlib.Cryptography.Games.Efficiency, `TCSlib.Cryptography.Games.Efficiency.Replay, `TCSlib.Cryptography.Games.Efficiency.OracleBridge, `TCSlib.Cryptography.Games.Hopping, `TCSlib.Cryptography.Games.OracleComp, `TCSlib.Cryptography.Games.Probability, `TCSlib.Cryptography.Games.Simulate, `TCSlib.Cryptography.Games.BitCodec, `TCSlib.Cryptography.Foundations.BitLists, `TCSlib.Cryptography.Asymptotic.Adversary, `TCSlib.Cryptography.Asymptotic.EnsemblesLemmas, `TCSlib.Cryptography.Asymptotic.Ensembles, `TCSlib.Cryptography.Asymptotic.OneWayLemmas, `TCSlib.Cryptography.Asymptotic.OneWay, `TCSlib.Cryptography.Asymptotic.OneWayYao, `TCSlib.Cryptography.Asymptotic.HardCoreLoops, `TCSlib.Cryptography.Candidates.Factoring, `TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM.Evaluator, `TCSlib.Cryptography.ZeroKnowledge.Commitment, `TCSlib.Cryptography.ZeroKnowledge.CommitmentLemmas, `TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.ColRepSound, `TCSlib.Cryptography.Authentication.Signatures.Lamport, `TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.ReductionMachine, `TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Handler, `TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Handler, `TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity, `TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity.ChallengeSim, `TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity.PaddedCPA, `TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability.Forward, `TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability.Decrypt, `TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability.Encrypt, `TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability, `TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Generic, `TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Hybrid, `TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.SimIND, `TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.SimINDGap, `TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Rounds, `TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Challenge, `TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Simulator, `TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Reduction, `TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Recover, `TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.IndSim, `TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation, `TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Machines, `TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.SoundnessRep]
  let mut out : Array String := #[]
  for (c, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? c | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless mods.contains mod do continue
    let axs ← liftCoreM <| collectAxioms c
    let axs := (axs.map toString).qsort (· < ·)
    out := out.push s!"AX\t{mod}\t{c}\t{axs.toList}"
  for s in out.qsort (· < ·) do IO.println s
  IO.println s!"TOTAL {out.size}"
