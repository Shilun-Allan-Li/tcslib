import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Branching
open TCSlib.Cryptography TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
def mat (P : Parameters) (M : Ciphertext P) : Ciphertext P :=
  let a := Array.ofFn fun i => Array.ofFn fun j => M i j
  fun i j => (a[i.val]'(by simp only [a, Array.size_ofFn]; exact i.isLt))[j.val]'(by
    simp only [a, Array.getElem_ofFn, Array.size_ofFn]; exact j.isLt)
theorem mat_eq (P : Parameters) (M : Ciphertext P) : mat P M = M := by
  funext i j; simp only [mat, Array.getElem_ofFn]
#eval 1
