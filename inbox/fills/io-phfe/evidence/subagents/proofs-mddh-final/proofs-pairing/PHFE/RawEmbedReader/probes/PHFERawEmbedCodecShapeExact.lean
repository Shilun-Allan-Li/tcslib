import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Raw
import Lean.Elab.Tactic.LibrarySearch

set_option maxHeartbeats 200000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20

open Complexity TCSlib.Cryptography.Pairing

example (G : BilinearGen) (ℓ n : PolyExpr) (d : ℕ)
    (PG : PartialGarbling.Raw ℓ (n.mul n) (PHFE.TensorFn ℓ n d)) (κ : ℕ)
    (pp : PublicParams (wee20PHFE_raw G ℓ n d PG).G κ)
    (v : (phfeClass ℓ n G.wG d).Out κ
      ((wee20PHFE_raw G ℓ n d PG).cprm κ pp)) :
    (wee20PHFE_raw G ℓ n d PG).embed κ pp v =
      let pp' := PHFE.publicParamsEquiv G ℓ n d PG κ pp
      pp'.group.pair pp'.generator pp'.generator ^
        (PHFE.scalarValueEquiv G ℓ n d PG κ pp v).val := exact?%

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20
