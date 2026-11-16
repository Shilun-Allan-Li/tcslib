import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Symmetric
import Lean

open Lean Elab Command

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

#print axioms vecMul_secretVector_augmented
#print axioms encrypts_encrypt
#print axioms encrypts_keygen_encrypt
#print axioms decrypt_of_encrypts
#print axioms decrypt_of_encrypts_dyadic
#print axioms decrypt_keygen_encrypt
#print axioms encrypts_symEncrypt
#print axioms distAdv_symEncrypt_le

/-- Dependency trace: list every constant reached from `n` whose value mentions `sorryAx`
directly (the sorried constants in the closure). -/
elab "#sorry_trace " id:ident : command => do
  let env ← getEnv
  let n := `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW ++ id.getId
  let mut seen : NameSet := {}
  let mut stack := [n]
  let mut hits : Array Name := #[]
  while !stack.isEmpty do
    let c := stack.head!
    stack := stack.tail!
    if seen.contains c then continue
    seen := seen.insert c
    match env.find? c with
    | none => pure ()
    | some ci =>
      let refs := ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants)).getD #[]
      if refs.contains ``sorryAx then hits := hits.push c
      for r in refs do
        if !seen.contains r then stack := r :: stack
  logInfo m!"{n}: sorried constants reached = {hits}"

#sorry_trace vecMul_secretVector_augmented
#sorry_trace encrypts_encrypt
#sorry_trace encrypts_keygen_encrypt
#sorry_trace decrypt_of_encrypts
#sorry_trace decrypt_of_encrypts_dyadic
#sorry_trace decrypt_keygen_encrypt
#sorry_trace encrypts_symEncrypt
#sorry_trace distAdv_symEncrypt_le

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
