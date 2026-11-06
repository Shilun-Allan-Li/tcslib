import TCSlib.Cryptography.ZeroKnowledge.NP
import TCSlib.Cryptography.ZeroKnowledge.Encryption
import TCSlib.Cryptography.Candidates.Factoring
import TCSlib.Cryptography.Candidates.RSA
import TCSlib.Cryptography.Asymptotic.Universal
import TCSlib.Cryptography.Asymptotic.PublicKey
import TCSlib.Cryptography.Asymptotic.HardCoreClaims
import TCSlib.Cryptography.Asymptotic.HardCorePermutation
import TCSlib.Cryptography.Asymptotic.GGMReductionEval
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.SoundnessRepGI
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Protocol

set_option autoImplicit false

open TCSlib.Cryptography TCSlib.Cryptography.Candidates Complexity Turing NumberTheory

attribute [local irreducible] Complexity.NUPPT.coinLen Complexity.NUPPT.ofPolyTime
  Complexity.NUPPT.ofPolyTimeUniform Complexity.NUPPT.wrap Complexity.NUPPT.Uniform
  TCSlib.Cryptography.PermFamily.toFunFamily TCSlib.Cryptography.FunFamily.glPad
  TCSlib.Cryptography.FunFamily.ofString TCSlib.Cryptography.FunFamily.prod
  TCSlib.Cryptography.owpGenPRG TCSlib.Cryptography.PRG.oneBit TCSlib.Cryptography.PRG.expand
  TCSlib.Cryptography.Strategy.coinLen TCSlib.Cryptography.GI.gniProtocol
  TCSlib.Cryptography.GI.gniProtocolRep TCSlib.Cryptography.GI.giProtocol
  TCSlib.Cryptography.GI.giProtocolRep Complexity.PolyExpr.normal TCSlib.Cryptography.OneWay.yaoB
  TCSlib.Cryptography.msgAt TCSlib.Cryptography.edgeIdxOfMsg Complexity.pairFstD Complexity.pairSndD
  TCSlib.Cryptography.GGMRed.coinPoly TCSlib.Cryptography.GGMRed.ggmRedMachine
  TCSlib.Cryptography.tdpPredictor TCSlib.Cryptography.Candidates.encodeDistinctPrimes
  TCSlib.Cryptography.OneWay.YaoMachine.ρP
  TCSlib.Cryptography.Collection.index TCSlib.Cryptography.OneWayPermutation
  TCSlib.Cryptography.FunFamily.Easy TCSlib.Cryptography.HardcoreBit.perfectInverter
  TCSlib.Cryptography.HardcoreBit.majorityInverter TCSlib.Cryptography.HardcoreBit.guessInverter
  TCSlib.Cryptography.owpPredictor
