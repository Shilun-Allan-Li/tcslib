import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Branching

/-! gsw-6b-u12, C11: `exact?` probes on the statements of the private glue and of the inline facts
of G2 and G3, to find a published lemma stating them (evidence only). -/

open TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

-- P1: the private glue `encrypts_select_ite`
example (P : Parameters) {t : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus} {b : Bool} {u v : ℕ}
    {β βV : ℕ} {C U V : Ciphertext P} (hC : Encrypts P t (b.toNat : ℤ) β C)
    (hU : Encrypts P t (u : ℤ) βV U) (hV : Encrypts P t (v : ℤ) βV V) :
    Encrypts P t ((if b then v else u : ℕ) : ℤ) (βV + 2 * (P.columns * β)) (select P C U V) := by
  exact?

-- P2: G2's message identity
example {w : ℕ} (a i : Fin w) :
    (((Pi.single a 1 : Fin w → ℕ) i : ℕ) : ℤ) = ((decide (a = i)).toNat : ℤ) := by
  exact?

-- P3: G2's message identity in ℕ
example {w : ℕ} (a i : Fin w) : (Pi.single a 1 : Fin w → ℕ) i = (decide (a = i)).toNat := by
  exact?

-- P4: G3's fixed-point fact
example : BranchingProgram.sigma1 0 ≠ 0 := by
  exact?
