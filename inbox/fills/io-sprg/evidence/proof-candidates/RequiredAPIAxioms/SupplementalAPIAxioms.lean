-- Optional diagnostic extension. NOT RUN. No declarations or tactic blocks.
import TCSlib.Cryptography.Obfuscation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

#print axioms Complexity.NUPPT.RealizesOn.runAtL_eq
#print axioms Complexity.NUPPT.RealizesOn.runAt_eq
#print axioms Complexity.NUPPT.realizesOn_self
#print axioms TCSlib.Cryptography.SubexpSmall.mono
#print axioms TCSlib.Cryptography.SubexpSmall.mono_exponent
#print axioms TCSlib.Cryptography.SubexpHard.negligible
#print axioms TCSlib.Cryptography.HardcoreBit.PushesUniform.uprob_eq
#print axioms TCSlib.Cryptography.Games.Bridge.expect_sample_pair
#print axioms TCSlib.Cryptography.Games.ProbComp.expect_sample_equiv
#print axioms TCSlib.Cryptography.Games.ProbComp.abs_prob_sub_le_of_agree
