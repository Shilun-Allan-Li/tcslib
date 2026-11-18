-- Root-only scratch probe. No search or checking has been performed by the agent.
-- Replace one placeholder at a time using exact?, then apply?, in the approved route.
-- Import the current Layered file, without the proposed helper declarations.
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Layered
import Lean.Elab.Tactic.LibrarySearch

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption
namespace PartialGarbling.Layered

variable {p : ℕ+} {l n d : ℕ}

-- Search target 1: proposed public name forward_node.
example (x : Fin l → ZMod (p : ℕ)) (v : TIdx l d) :
    forward x (node v) = forward x (parent v) * xhat x (lastLabel v) := sorry

-- Search target 2: proposed public name matrix_inl.
example (C : PolyTensor p l n d) (x : Fin l → ZMod (p : ℕ))
    (v : TIdx l d) (u : MIdx l d) :
    matrix C x (Sum.inl v) u =
      (if u = parent v then xhat x (lastLabel v) else 0) -
        (if u = node v then 1 else 0) := sorry

end PartialGarbling.Layered
end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption
