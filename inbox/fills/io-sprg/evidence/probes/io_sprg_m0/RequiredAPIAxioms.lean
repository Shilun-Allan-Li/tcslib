-- Diagnostic only. NOT RUN. No declarations, tactics, or new import roots.
import TCSlib.Cryptography.Obfuscation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

-- 01-06: shared realisation, targets link, non-vacuity, and verdict transport.
#print axioms Complexity.NUPPT.exists_realizesOn_of_preTarget
#print axioms Complexity.NUPPT.realizesOn_self_take
#print axioms Complexity.NUPPT.RealizesOn.coins_eq
#print axioms Complexity.NUPPT.RealizesOn.distinguisherL_eq
#print axioms Complexity.NUPPT.RealizesOn.runAt_coinsEquivPoly_symm
#print axioms Complexity.NUPPT.RealizesOn.congr

-- 07-11: shared sampler contract, introduction and permitted closure.
#print axioms TCSlib.Cryptography.CoinSampling.SamplesEfficiently.intro
#print axioms TCSlib.Cryptography.CoinSampling.SamplesEfficiently.map
#print axioms TCSlib.Cryptography.CoinSampling.SamplesEfficiently.map_output
#print axioms TCSlib.Cryptography.CoinSampling.SamplesEfficiently.pair
#print axioms TCSlib.Cryptography.CoinSampling.SamplesEfficiently.congr

-- 12-19: the only permitted subexponential API and exact polynomial reindexing.
#print axioms TCSlib.Cryptography.SubexpSmall.negligible
#print axioms TCSlib.Cryptography.SubexpSmall.add
#print axioms TCSlib.Cryptography.SubexpSmall.const_mul
#print axioms TCSlib.Cryptography.SubexpSmall.mul_pow
#print axioms TCSlib.Cryptography.SubexpSmall.comp_of_rpow_le
#print axioms TCSlib.Cryptography.SubexpHard.comp_of_rpow_le
#print axioms TCSlib.Cryptography.subexpSmall_two_pow_neg
#print axioms TCSlib.Cryptography.eventually_const_mul_rpow_mul_two_rpow_neg_le

-- 20-24: exact uniform prefix/translation and existing finite averaging.
#print axioms TCSlib.Cryptography.HardcoreBit.pushesUniform_restrict
#print axioms TCSlib.Cryptography.HardcoreBit.pushesUniform_add_right
#print axioms TCSlib.Cryptography.OneWay.ofFn_castLE_eq_take
#print axioms TCSlib.Cryptography.Games.ProbComp.abs_expect_sub_le_expect
#print axioms TCSlib.Cryptography.Authentication.LamportReduction.exists_expect_sample_le
