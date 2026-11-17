import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Circular
open TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
open TCSlib.Cryptography
abbrev P5 : Parameters := ⟨⟨1, 2, 5, by decide⟩, 3, by decide⟩
def show' (P : Parameters) (M : Ciphertext P) : List (List ℕ) :=
  List.ofFn fun i => List.ofFn fun j => (M i j).val
#eval show' P5 (gadget P5)
#eval show' P5 (mul P5 (gadget P5) (gadget P5))
#eval show' P5 (select P5 (gadget P5) 0 (gadget P5))
theorem k1 : select P5 (gadget P5) 0 (gadget P5) = gadget P5 := by decide
