import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Leveled

/-! C6 control (gsw-6b-u14-u16): positive half of every pair: the same facts through the published readers, and `encrypts_bootGate` applied. Must pass in every variant. -/

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

open BoolCircuit
open Encryption.PublicKey

example (P : Parameters) (β : ℕ) :
    bootNoise P β = 4 ^ (decDepth P + 1) * (2 * (P.columns * β)) := bootNoise_eq P β

example (P : Parameters) (evk : Fin P.columns → Ciphertext P) (cts : List (Ciphertext P)) :
    bootGate P evk ⟨.not, []⟩ cts = bootNAND P evk (gadget P) (gadget P) :=
  bootGate_of_args_eq_nil P evk _ cts rfl

example (P : Parameters) {t' : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus}
    (s : Secret P) (βk : ℕ) (evk : Fin P.columns → Ciphertext P)
    (hk : ∀ i, Encrypts P t' ((keyBits P s i).toNat : ℤ) βk (evk i))
    {g : DAGGate} (hg : g.IsNAND) (vals : List Bool) (cts : List (Ciphertext P))
    (hargs : ∀ a ∈ g.args, decrypt P s (cts.getD a 0) = vals.getD a false) :
    Encrypts P t' ((g.eval vals).toNat : ℤ) (bootNoise P βk) (bootGate P evk g cts) :=
  encrypts_bootGate P s βk evk hk hg vals cts hargs

example (P : Parameters) {L : ℕ} (pks : Fin (L + 1) → PublicKey P) (ss : Fin (L + 1) → Secret P)
    (R : LevelCoins P L) (d : Fin L) :
    levelKey P pks ss R d = evalKey P (pks d.succ) (ss d.castSucc) (R d) := levelKey_eq P pks ss R d

example {n : ℕ} (C : DAGCircuit n) : C.depth = C.depthAt C.output := C.depth_eq

example {n : ℕ} (x : Fin n → Bool) : litInput x = Fin.append x fun i => !x i := litInput_eq x

example (P : Parameters) (t : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus) (x : ℤ) (β : ℕ)
    (C : Ciphertext P) :
    Encrypts P t x β C ↔ ∃ e : Fin P.columns → ℤ, (∀ j, (e j).natAbs ≤ β) ∧
      Matrix.vecMul t C = (x : ZMod P.lwe.modulus) • Matrix.vecMul t (gadget P) +
        fun j => (e j : ZMod P.lwe.modulus) := encrypts_iff P t x β C

example (P : Parameters) (χ : LWE.Noise) (rg : KeySeed P χ) :
    (Regev.keygen P.lwe χ rg).2 = rg.2.1 := Regev.keygen_snd P.lwe χ rg

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
