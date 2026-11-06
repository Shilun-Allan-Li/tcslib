import TCSlib.Cryptography.Candidates.Rabin
set_option autoImplicit false
namespace TCSlib.Cryptography.Candidates
open Complexity Turing NumberTheory Finset
#check @Equiv.ofBijective
#check @OneWay.YaoMachine.off
#check @OneWay.YaoMachine.planted
#check @ZMod.val_lt
#check @polyTimeComputable_padStr
#check @ofFn_padFin_eq_padStr
#check @finProdFinEquiv
#check @FunFamily.StrongOneWay.toCollection_oneWay
#check @ZMod.coe_mul_inv_eq_one
#check @Nat.lt_size_self
#check @Nat.size_le
#check @Nat.lt_size
#check @polyTimeComputable_lenLe
end TCSlib.Cryptography.Candidates
