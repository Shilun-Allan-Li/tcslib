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
open Lean Elab Command

/-- Parse a dotted name, numeric components as numbers (private prefixes). -/
def parseName (s : String) : Name :=
  (s.splitOn ".").foldl (fun n c => match c.toNat? with
    | some k => if c.all Char.isDigit then .num n k else .str n c
    | none => .str n c) .anonymous

def renames : List (String × String) := []
def toCheck : List String := ["List.replicate_one", "TCSlib.Cryptography.BitPublicKeyScheme.bitwise_enc_runAtL", "TCSlib.Cryptography.Composability.AdaptiveCPA.castImpl_adaptiveIndImpl", "TCSlib.Cryptography.Composability.AdaptiveCPA.castImpl_indImpl_challenge", "TCSlib.Cryptography.Composability.ChallengeSim.chRun_toCompOn_transport_list", "TCSlib.Cryptography.Composability.ChallengeSim.expect_simulate_eager", "TCSlib.Cryptography.Composability.FixedLengthPKScheme.indCodec_eq_bitCodec", "TCSlib.Cryptography.Composability.FixedLengthScheme.indCodec_eq_bitCodec", "TCSlib.Cryptography.Composability.FixedLengthScheme.ofFn_splitHalf_fst", "TCSlib.Cryptography.Composability.FixedLengthScheme.ofFn_splitHalf_snd", "TCSlib.Cryptography.Composability.PRFGame.ctOf_xorPerm", "TCSlib.Cryptography.Composability.PRFGame.ctP_eval", "TCSlib.Cryptography.Composability.expect_simulate_indImpl_cpa", "TCSlib.Cryptography.EnsembleLemmas.ofFn_padFin_eq_padL", "TCSlib.Cryptography.FunFamily.ofFn_blocks", "TCSlib.Cryptography.Games.InteractiveHandler.impl_of_ret", "TCSlib.Cryptography.Games.InteractiveHandler.rCnt", "TCSlib.Cryptography.Games.InteractiveHandler.rI", "TCSlib.Cryptography.Games.InteractiveHandler.rL", "TCSlib.Cryptography.Games.InteractiveHandler.rS", "TCSlib.Cryptography.Games.InteractiveHandler.rU", "TCSlib.Cryptography.Games.InteractiveHandler.rW", "TCSlib.Cryptography.Games.InteractiveHandler.rX", "TCSlib.Cryptography.Games.InteractiveHandler.rZ", "TCSlib.Cryptography.Games.ProbComp.abs_expect_sub_le", "TCSlib.Cryptography.Games.ProbComp.expect_sample_comm", "TCSlib.Cryptography.Games.ProbComp.expect_sample_coord", "TCSlib.Cryptography.Games.ProbComp.expect_sample_equiv", "TCSlib.Cryptography.Games.ProbComp.expect_sample_mem_le", "TCSlib.Cryptography.Games.ProbComp.expect_sample_unique", "TCSlib.Cryptography.Games.ProbComp.expect_sample_update", "TCSlib.Cryptography.Games.ProbComp.expect_simulate_congr", "TCSlib.Cryptography.Games.ProbComp.expect_sub", "TCSlib.Cryptography.Games.ProbComp.prob_bad_le", "TCSlib.Cryptography.Games.castImpl", "TCSlib.Cryptography.Games.castImpl_eq", "TCSlib.Cryptography.Games.castImpl_self", "TCSlib.Cryptography.Games.decodeFin_nil_getD", "TCSlib.Cryptography.Games.expect_simulate_castImpl_toCompOn", "TCSlib.Cryptography.Games.padFin_nil", "TCSlib.Cryptography.Games.padFin_ofFn_zeroBits", "TCSlib.Cryptography.Games.padFin_replicate_false", "TCSlib.Cryptography.Games.simulate_castImpl_toCompOn", "TCSlib.Cryptography.Games.simulate_eq_of_abs", "TCSlib.Cryptography.Games.simulate_eq_of_abs_bounded", "TCSlib.Cryptography.flatten_ofFn_one", "TCSlib.Cryptography.flatten_ofFn_singleton", "TCSlib.Cryptography.headD_drop", "TCSlib.Cryptography.headD_ofFn_one", "TCSlib.Cryptography.hybridPre_eq", "TCSlib.Cryptography.mem_keys_of_lookup_isSome", "TCSlib.Cryptography.ofFn_arrowCongr_finCongr", "TCSlib.Cryptography.ofFn_cast", "TCSlib.Cryptography.ofFn_padFin_of_length", "TCSlib.Cryptography.xorPerm", "TCSlib.Cryptography.xorPerm_apply", "TCSlib.Cryptography.zipWith_xor_cancel_left", "_private.TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Handler.0.TCSlib.Cryptography.Composability.PRFGame.fields_input", "_private.TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Handler.0.TCSlib.Cryptography.Composability.PRFGame.pkRun.eq_1", "_private.TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Handler.0.TCSlib.Cryptography.Composability.PRFGame.rFlag.eq_1", "_private.TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Handler.0.TCSlib.Cryptography.Composability.PRFGame.rMsg.eq_1", "_private.TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Handler.0.TCSlib.Cryptography.Composability.PRFGame.rNew.eq_1", "_private.TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Handler.0.TCSlib.Cryptography.Composability.PRFGame.rNonce.eq_1", "_private.TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Handler.0.TCSlib.Cryptography.Composability.PRFGame.rRec.eq_1", "_private.TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Handler.0.TCSlib.Cryptography.Composability.PRFGame.rWF.eq_1", "_private.TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Handler.0.TCSlib.Cryptography.Composability.PRFGame.rY.eq_1", "_private.TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Handler.0.TCSlib.Cryptography.Composability.PRFGame.rY_one", "_private.TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Handler.0.TCSlib.Cryptography.Composability.AdaptiveCPA.acRun.eq_1", "_private.TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Handler.0.TCSlib.Cryptography.Composability.AdaptiveCPA.fields_input", "_private.TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Handler.0.TCSlib.Cryptography.Composability.AdaptiveCPA.polyTimeComputable_acRun._proof_1_1", "_private.TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Handler.0.TCSlib.Cryptography.Composability.AdaptiveCPA.polyTimeComputable_acRun._proof_1_2", "_private.TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Handler.0.TCSlib.Cryptography.Composability.AdaptiveCPA.rEnc.eq_1", "_private.TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Handler.0.TCSlib.Cryptography.Composability.AdaptiveCPA.rFwd.eq_1", "_private.TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Handler.0.TCSlib.Cryptography.Composability.AdaptiveCPA.rIst.eq_1", "_private.TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Handler.0.TCSlib.Cryptography.Composability.AdaptiveCPA.rLat.eq_1", "_private.TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Handler.0.TCSlib.Cryptography.Composability.AdaptiveCPA.rMsg.eq_1", "_private.TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Handler.0.TCSlib.Cryptography.Composability.AdaptiveCPA.rNew.eq_1", "_private.TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Handler.0.TCSlib.Cryptography.Composability.AdaptiveCPA.rTape.eq_1", "_private.TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Reduction.0.TCSlib.Cryptography.Composability.AdaptiveCPA.comp_acAbs"]

#eval show CommandElabM Unit from do
  let env ← getEnv
  let m : Std.HashMap Name Name := renames.foldl (fun m (a, b) => m.insert (parseName a) (parseName b)) {}
  for s in toCheck do
    let n := parseName s
    match env.find? n with
    | none => IO.println s!"{s} | absent"
    | some ci =>
      let t := ci.type.replace fun e => match e with
        | .const c ls => (m.get? c).map fun c' => Expr.const c' ls
        | _ => none
      IO.println s!"{s} | {t.hash}"
