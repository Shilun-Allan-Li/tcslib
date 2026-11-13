C = 'TCSlib/Cryptography/'
NMI = C + 'Encryption/PublicKey/NonMalleability/Indistinguishability/'
NMS = C + 'Encryption/PublicKey/NonMalleability/Simulation/'
SUPER = [
 C+'Games/Machines.lean', C+'Games/Efficiency.lean', C+'Games/Efficiency/Replay.lean',
 C+'Games/Efficiency/OracleBridge.lean', C+'Games/Hopping.lean', C+'Games/OracleComp.lean',
 C+'Games/Probability.lean', C+'Games/Simulate.lean', C+'Games/BitCodec.lean',
 C+'Foundations/BitLists.lean', C+'Asymptotic/Adversary.lean', C+'Asymptotic/EnsemblesLemmas.lean',
 C+'Asymptotic/Ensembles.lean', C+'Asymptotic/OneWayLemmas.lean', C+'Asymptotic/OneWay.lean',
 C+'Asymptotic/OneWayYao.lean', C+'Asymptotic/HardCoreLoops.lean', C+'Candidates/Factoring.lean',
 C+'Pseudorandom/Functions/Asymptotic/GGM/Evaluator.lean', C+'ZeroKnowledge/Commitment.lean',
 C+'ZeroKnowledge/CommitmentLemmas.lean', C+'ZeroKnowledge/ThreeColoring/ColRepSound.lean',
 C+'Authentication/Signatures/Lamport.lean', C+'Encryption/PrivateKey/FromPRF/ReductionMachine.lean',
 C+'Encryption/PrivateKey/OracleFromPRF/Handler.lean', C+'Encryption/PublicKey/AdaptiveCPA/Handler.lean',
 C+'Encryption/PublicKey/OracleSecurity.lean', C+'Encryption/PublicKey/OracleSecurity/ChallengeSim.lean',
 C+'Encryption/PublicKey/OracleSecurity/PaddedCPA.lean',
 NMI+'Forward.lean', NMI+'Decrypt.lean', NMI+'Encrypt.lean',
 C+'Encryption/PublicKey/NonMalleability/Indistinguishability.lean',
] + [NMS+x+'.lean' for x in ['Generic','Hybrid','SimIND','SimINDGap','Rounds','Challenge','Simulator',
  'Reduction','Recover','IndSim']] + [C+'Encryption/PublicKey/NonMalleability/Simulation.lean',
 C+'ZeroKnowledge/ThreeColoring/Machines.lean', C+'ZeroKnowledge/GraphIsomorphism/SoundnessRep.lean']
def key(p):
    return p[len('TCSlib/Cryptography/'):-5].replace('/', '_')
