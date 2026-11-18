import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.DecryptFormula

/-! Probe U13-P1 (C12, optional; evidence only, never a proof): `#eval` of
`(decryptFormula P C).eval (keyBits P s)` against `decrypt P s C` for `q ∈ {5, 8}`, `n = 1`,
`ℓ = 3`, three ciphertexts `C i j = a·i + b·j + c` (`(a, b, c)` in `(1, 2, 0)`, `(2, 1, 3)`,
`(0, 1, 1)`) and every secret `s ∈ Z_q` (constant vectors, `n = 1`). Each `#eval` prints the number
of `(C, s)` pairs tried and the number where the two sides agree; `probeOne` prints both sides of
one pair. (A first run over 27 ciphertexts did not finish in 5 minutes: the formula is a tree.) -/

open TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

/-- The probe's parameters: `n = 1`, `m = 1`, modulus `q`, width `3`. -/
def probeParams (q : ℕ) (hq : 2 ≤ q) (hq8 : q ≤ 2 ^ 3) : Parameters :=
  ⟨⟨1, 1, q, hq⟩, 3, hq8⟩

/-- Count the agreements over the three ciphertexts and every secret `s`. -/
def probeCount (P : Parameters) : ℕ × ℕ := Id.run do
  let mut tried := 0
  let mut agree := 0
  for (a, b, c) in [(1, 2, 0), (2, 1, 3), (0, 1, 1)] do
    let C : Ciphertext P := fun i j => ((a * i.val + b * j.val + c : ℕ) : ZMod P.lwe.modulus)
    for v in List.range P.lwe.modulus do
      let s : Fin P.lwe.dimension → ZMod P.lwe.modulus := fun _ => (v : ZMod P.lwe.modulus)
      tried := tried + 1
      if (decryptFormula P C).eval (keyBits P s) == decrypt P s C then agree := agree + 1
  return (tried, agree)

/-- One pair: `q = 5`, `C i j = i + 2j`, `s = 3`: the formula's value and decryption. -/
def probeOne : Bool × Bool :=
  let P := probeParams 5 (by decide) (by decide)
  let C : Ciphertext P := fun i j => ((i.val + 2 * j.val : ℕ) : ZMod P.lwe.modulus)
  let s : Fin P.lwe.dimension → ZMod P.lwe.modulus := fun _ => 3
  ((decryptFormula P C).eval (keyBits P s), decrypt P s C)

#eval probeOne
#eval probeCount (probeParams 5 (by decide) (by decide))
#eval probeCount (probeParams 8 (by decide) (by decide))
