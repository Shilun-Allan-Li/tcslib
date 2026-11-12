import TCSlib.Cryptography.Games.Probability
import TCSlib.Cryptography.Games.Simulate
import TCSlib.Cryptography.Games.Hopping
import TCSlib.Cryptography.Games.BitCodec
import TCSlib.Cryptography.Games.Efficiency
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.Asymptotic.EnsemblesLemmas
import TCSlib.Cryptography.Asymptotic.HardCoreGLColl
import TCSlib.Cryptography.Asymptotic.CollectionsHelpers
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM.Run
import TCSlib.Cryptography.Pseudorandom.NextBit
import TCSlib.Cryptography.ZeroKnowledge.CommitmentLemmas
import TCSlib.Cryptography.SecureComputation.Yao
import TCSlib.Cryptography.Encryption.PublicKey.ElGamal
import TCSlib.Cryptography.Encryption.PublicKey.HybridMachine
import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity
import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity.ChallengeSim
import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity.RecordHandler
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Games
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Handler
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Hybrid
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Reduction
import TCSlib.Cryptography.Encryption.PublicKey.BitwiseCPA
import TCSlib.Cryptography.Encryption.PublicKey.BitwiseCPA.Planted
import TCSlib.Cryptography.Encryption.PublicKey.BitwiseCPA.QueryHandler
import TCSlib.Cryptography.Encryption.PrivateKey.OracleSecurity
import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF
import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Collision
import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Games
import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Handler
import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Lazy
import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Reduction
import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Transfer
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.EfficiencyRep
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.EfficiencyRepGI
import TCSlib.Cryptography.Foundations
import TCSlib.Cryptography.Foundations.BitLists
import TCSlib.Cryptography.Implications.PublicKey
open Lean Elab Command Meta

/-! Declaration and axiom dump: every stored constant of the candidate modules, as
`name | module | kind | type hash | attributes | axioms`, and the axioms of the campaign endpoints. -/

def candMods : List Name := [`TCSlib.Cryptography.Games.Probability, `TCSlib.Cryptography.Games.Simulate, `TCSlib.Cryptography.Games.Hopping, `TCSlib.Cryptography.Games.BitCodec, `TCSlib.Cryptography.Games.Efficiency, `TCSlib.Cryptography.Asymptotic.Adversary, `TCSlib.Cryptography.Asymptotic.EnsemblesLemmas, `TCSlib.Cryptography.Asymptotic.HardCoreGLColl, `TCSlib.Cryptography.Asymptotic.CollectionsHelpers, `TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM.Run, `TCSlib.Cryptography.Pseudorandom.NextBit, `TCSlib.Cryptography.ZeroKnowledge.CommitmentLemmas, `TCSlib.Cryptography.SecureComputation.Yao, `TCSlib.Cryptography.Encryption.PublicKey.ElGamal, `TCSlib.Cryptography.Encryption.PublicKey.HybridMachine, `TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity, `TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity.ChallengeSim, `TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity.RecordHandler, `TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA, `TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Games, `TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Handler, `TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Hybrid, `TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Reduction, `TCSlib.Cryptography.Encryption.PublicKey.BitwiseCPA, `TCSlib.Cryptography.Encryption.PublicKey.BitwiseCPA.Planted, `TCSlib.Cryptography.Encryption.PublicKey.BitwiseCPA.QueryHandler, `TCSlib.Cryptography.Encryption.PrivateKey.OracleSecurity, `TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF, `TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Collision, `TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Games, `TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Handler, `TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Lazy, `TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Reduction, `TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Transfer, `TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.EfficiencyRep, `TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.EfficiencyRepGI, `TCSlib.Cryptography.Foundations, `TCSlib.Cryptography.Foundations.BitLists]

def endpoints : List Name := [`TCSlib.Cryptography.Composability.prfFixedScheme_cpa,
  `TCSlib.Cryptography.Composability.prfFixedScheme_cca1,
  `TCSlib.Cryptography.Composability.not_prfFixedScheme_cca2,
  `TCSlib.Cryptography.Composability.FixedLengthPKScheme.INDSecure.adaptive_cpa,
  `TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.bitwise_padded_cpa,
  `TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.exists_adaptive_cpa,
  `TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.padded_cpa,
  `TCSlib.Cryptography.Implications.PublicKey.exists_adaptiveCPA_of_rsa,
  `TCSlib.Cryptography.Implications.PublicKey.exists_adaptiveCPA_of_factoring]

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut rows : Array String := #[]
  for (c, ci) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? c | continue
    let m := env.header.moduleNames[idx.toNat]!
    unless candMods.contains m do continue
    let kind := match ci with
      | .thmInfo _ => "thm" | .defnInfo _ => "def" | .axiomInfo _ => "axiom"
      | .opaqueInfo _ => "opaque" | .inductInfo _ => "induct" | .ctorInfo _ => "ctor"
      | .recInfo _ => "rec" | .quotInfo _ => "quot"
    let st := getReducibilityStatusCore env c
    let red := match st with | .reducible => "reducible" | .irreducible => "irreducible" | _ => "regular"
    let simp := (simpExtension.getState env).lemmaNames.contains (.decl c)
    let inst := isInstanceCore env c
    let prot := isProtected env c
    let attrs := s!"{red}{if simp then ",simp" else ""}{if inst then ",instance" else ""}{if prot then ",protected" else ""}"
    let axs ← liftCoreM <| Lean.collectAxioms c
    let axs := (axs.map toString).qsort (· < ·)
    rows := rows.push s!"{c} | {m} | {kind} | {ci.type.hash} | {attrs} | {axs.toList}"
  for r in rows.qsort (· < ·) do
    IO.println r
  IO.println s!"constants: {rows.size}"
  for e in endpoints do
    match env.find? e with
    | none => IO.println s!"ENDPOINT {e}: NOT FOUND"
    | some _ =>
      let axs ← liftCoreM <| Lean.collectAxioms e
      IO.println s!"ENDPOINT {e}: {((axs.map toString).qsort (· < ·)).toList}"
