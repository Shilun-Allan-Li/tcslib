import TCSlib.Complexity.Randomized.Build.IterateFindHost
import TCSlib.Complexity.Randomized.PPT
import TCSlib.Cryptography.Encryption.PrivateKey.EnsembleSecurity
import TCSlib.Cryptography.Encryption.PublicKey.Trapdoor
import TCSlib.InformationTheory.FinDist
import TCSlib.InformationTheory.Samples
import TCSlib.InformationTheory.Entropy

set_option pp.fullNames true

#check @Complexity.IterateFind.host_dispatch_view
#print axioms Complexity.IterateFind.host_dispatch_view
#check @Complexity.IterateFind.host_branch_view
#print axioms Complexity.IterateFind.host_branch_view
#check @Complexity.IterateFind.host_halt_view
#print axioms Complexity.IterateFind.host_halt_view
#check @Complexity.NUPPT.length_ofFn_coins
#print axioms Complexity.NUPPT.length_ofFn_coins
#check @TCSlib.Cryptography.PrivateKeyScheme.encodeList_eq_flatMap
#print axioms TCSlib.Cryptography.PrivateKeyScheme.encodeList_eq_flatMap
#check @TCSlib.Cryptography.pkPredictor_apply
#print axioms TCSlib.Cryptography.pkPredictor_apply
#check @TCSlib.InformationTheory.FinDist.map_uniform_equiv
#print axioms TCSlib.InformationTheory.FinDist.map_uniform_equiv
#check @TCSlib.InformationTheory.FinDist.sum_map
#print axioms TCSlib.InformationTheory.FinDist.sum_map
#check @TCSlib.InformationTheory.FinDist.probTrue_nonneg
#print axioms TCSlib.InformationTheory.FinDist.probTrue_nonneg
#check @TCSlib.InformationTheory.FinDist.probTrue_le_one
#print axioms TCSlib.InformationTheory.FinDist.probTrue_le_one
#check @TCSlib.InformationTheory.FinDist.uniform_prod
#print axioms TCSlib.InformationTheory.FinDist.uniform_prod
#check @TCSlib.InformationTheory.FinDist.uniform_probTrue
#print axioms TCSlib.InformationTheory.FinDist.uniform_probTrue
#check @TCSlib.InformationTheory.FinDist.expect_map
#print axioms TCSlib.InformationTheory.FinDist.expect_map
#check @TCSlib.InformationTheory.FinDist.probTrue_map
#print axioms TCSlib.InformationTheory.FinDist.probTrue_map
#check @TCSlib.InformationTheory.FinDist.map_apply_expect
#print axioms TCSlib.InformationTheory.FinDist.map_apply_expect
#check @TCSlib.InformationTheory.FinDist.map_map
#print axioms TCSlib.InformationTheory.FinDist.map_map
#check @TCSlib.InformationTheory.FinDist.map_prod_snd
#print axioms TCSlib.InformationTheory.FinDist.map_prod_snd
#check @TCSlib.InformationTheory.FinDist.mixture
#print axioms TCSlib.InformationTheory.FinDist.mixture
#check @TCSlib.InformationTheory.FinDist.mixture_apply
#print axioms TCSlib.InformationTheory.FinDist.mixture_apply
#check @TCSlib.InformationTheory.FinDist.mixture_isSource
#print axioms TCSlib.InformationTheory.FinDist.mixture_isSource
