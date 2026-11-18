import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Branching

/-! gsw-6b-u12, probe U12-P1 (C12, evidence only, outside the library): `select` on toy parameters
`n = 1`, `q = 8`, `ℓ = 3` (two key rows, six columns). With noise-free inputs `C = b·G`, `U = u·G`,
`V = v·G` over `ZMod 8`, `#eval` compares `select P C U V` with `((1 − b)·u + b·v)·G` entrywise,
for the four bit pairs `(b, ·)` and a few messages. Expected: `true` everywhere. -/

open TCSlib.Cryptography TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

def toyP : Parameters :=
  ⟨⟨1, 1, 8, by decide⟩, 3, by decide⟩

def toyCheck (b u v : ℤ) : Bool :=
  let G := gadget toyP
  let C : Ciphertext toyP := (b : ZMod toyP.lwe.modulus) • G
  let U : Ciphertext toyP := (u : ZMod toyP.lwe.modulus) • G
  let V : Ciphertext toyP := (v : ZMod toyP.lwe.modulus) • G
  let lhs := select toyP C U V
  let rhs : Ciphertext toyP := (((1 - b) * u + b * v : ℤ) : ZMod toyP.lwe.modulus) • G
  (List.finRange 2).all fun i => (List.finRange 6).all fun j => lhs i j == rhs i j

#eval [(0, 0, 0), (0, 0, 1), (0, 1, 0), (0, 1, 1), (1, 0, 0), (1, 0, 1), (1, 1, 0), (1, 1, 1),
  (0, 5, 3), (1, 5, 3)].map fun (b, u, v) => ((b, u, v), toyCheck b u v)
