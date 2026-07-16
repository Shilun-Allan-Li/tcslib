import Mathlib.Tactic.Common
import Mathlib.Data.Tree.Basic
import Mathlib.Data.Set.Basic

set_option maxHeartbeats 0

set_option relaxedAutoImplicit false

set_option autoImplicit false

namespace CommunicationComplexity.Deterministic
inductive Protocol (X Y α : Type*) where
  | output (val : α) : Protocol X Y α
  | alice (f : X → Bool) (P : Bool → Protocol X Y α) : Protocol X Y α
  | bob (f : Y → Bool) (P : Bool → Protocol X Y α) : Protocol X Y α
end CommunicationComplexity.Deterministic

set_option maxHeartbeats 0

set_option relaxedAutoImplicit false

set_option autoImplicit false

namespace CommunicationComplexity.Deterministic.Protocol
variable {X Y α : Type*}
inductive IsSubprotocol : Protocol X Y α → Protocol X Y α → Prop where
| refl : ∀ p, IsSubprotocol p p
| alice_false : ∀ f P s, IsSubprotocol s (P false) → IsSubprotocol s (Protocol.alice f P)
| alice_true  : ∀ f P s, IsSubprotocol s (P true)  → IsSubprotocol s (Protocol.alice f P)
| bob_false   : ∀ f P s, IsSubprotocol s (P false) → IsSubprotocol s (Protocol.bob f P)
| bob_true    : ∀ f P s, IsSubprotocol s (P true)  → IsSubprotocol s (Protocol.bob f P)
end CommunicationComplexity.Deterministic.Protocol

namespace CommunicationComplexity.Deterministic.Protocol
variable {X Y α : Type*}
inductive SubprotocolPath : Protocol X Y α → Protocol X Y α → Type _ where
| refl : ∀ p, SubprotocolPath p p
| alice_false : ∀ f P s, SubprotocolPath s (P false) → SubprotocolPath s (Protocol.alice f P)
| alice_true  : ∀ f P s, SubprotocolPath s (P true)  → SubprotocolPath s (Protocol.alice f P)
| bob_false   : ∀ f P s, SubprotocolPath s (P false) → SubprotocolPath s (Protocol.bob f P)
| bob_true    : ∀ f P s, SubprotocolPath s (P true)  → SubprotocolPath s (Protocol.bob f P)
end CommunicationComplexity.Deterministic.Protocol

namespace CommunicationComplexity.Deterministic.Protocol
variable {X Y α : Type*}
theorem path_exists_of_isSubprotocol {s p : Protocol X Y α}
    (hsp : IsSubprotocol s p) : Nonempty (SubprotocolPath s p) := by
  induction hsp with
  | refl p => exact ⟨SubprotocolPath.refl p⟩
  | alice_false f P s hs ih =>
    rcases ih with ⟨t⟩
    exact ⟨SubprotocolPath.alice_false f P s t⟩
  | alice_true f P s hs ih =>
    rcases ih with ⟨t⟩
    exact ⟨SubprotocolPath.alice_true f P s t⟩
  | bob_false f P s hs ih =>
    rcases ih with ⟨t⟩
    exact ⟨SubprotocolPath.bob_false f P s t⟩
  | bob_true f P s hs ih =>
    rcases ih with ⟨t⟩
    exact ⟨SubprotocolPath.bob_true f P s t⟩
end CommunicationComplexity.Deterministic.Protocol

namespace CommunicationComplexity.Deterministic.Protocol
variable {X Y α : Type*}
def reachXPath {s p : Protocol X Y α} (hsp : SubprotocolPath s p) : Set X :=
  match hsp with
  | SubprotocolPath.refl _ => Set.univ
  | SubprotocolPath.alice_false f P s hs => reachXPath hs ∩ {x | f x = false}
  | SubprotocolPath.alice_true f P s hs => reachXPath hs ∩ {x | f x = true}
  | SubprotocolPath.bob_false _ _ _ hs => reachXPath hs
  | SubprotocolPath.bob_true _ _ _ hs => reachXPath hs
end CommunicationComplexity.Deterministic.Protocol
