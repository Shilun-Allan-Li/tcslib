import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.DecryptFormula

/-! Probe P4 (gsw-6b statements, check 7): the decryption formula (G5–G8).

Parameters `TP n q ℓ` = GSW parameters with LWE dimension `n`, `m = 2` samples, modulus `q`,
width `ℓ` (`N = (n+1)·ℓ`).
* **P4a** (kernel `decide`): G5 (`vecMul_secretVector_eq_sum`) for **every** secret and **every**
  ciphertext at `TP 1 2 1` (`N = 2`, 16 ciphertexts × 2 secrets) and `TP 0 4 2` (`N = 2`,
  16 ciphertexts), and the proposed owner-side `decrypt_eq_decode_dotProduct` there too. (G6/G7 are not kernel-reducible: `Nat.clog` in `modSumInterval`.)
* **P4b** (`#eval`, evidence): G6 for every secret on every ciphertext (exhaustive where
  marked) or on pseudo-random ciphertexts (a fixed linear congruential sequence), at
  `TP 1 2 1`, `TP 0 4 2`, `TP 1 3 2`, `TP 1 4 2`, `TP 1 5 3`, `TP 1 8 3`; G7 on pseudo-random
  pairs; G5 on the same ciphertexts; G8's depth (`≤ decDepth P + 1`) and fan-in (`≤ 2`) of
  `nandFormula` on the same pairs. Each line prints the mismatch counts (expected 0) and the
  number of checks.
-/

open TCSlib.Cryptography
open TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
open BoolCircuit

namespace P4

abbrev TP (n q ℓ : ℕ) (hq : 2 ≤ q) (hℓ : q ≤ 2 ^ ℓ) : Parameters := ⟨⟨n, 2, q, hq⟩, ℓ, hℓ⟩
abbrev A : Parameters := TP 0 2 1 (by decide) (by decide)
abbrev B : Parameters := TP 1 2 1 (by decide) (by decide)
abbrev C4 : Parameters := TP 0 4 2 (by decide) (by decide)

/-! ### P4a: kernel `decide` -/

theorem g5_B : ∀ (s : Fin 1 → ZMod 2) (C : Ciphertext B),
    secretVector B s ⬝ᵥ decryptColumn B C =
      ∑ i, ((keyBits B s i).toNat : ZMod 2) * decConstants B C i := by
  decide +kernel

theorem g5_C4 : ∀ (s : Fin 0 → ZMod 4) (C : Ciphertext C4),
    secretVector C4 s ⬝ᵥ decryptColumn C4 C =
      ∑ i, ((keyBits C4 s i).toNat : ZMod 4) * decConstants C4 C i := by
  decide +kernel

/-- The owner-side lemma proposed for `GSW/Scheme.lean` (MISSING in the census),
`decrypt P s C = decode P.lwe (secretVector P s ⬝ᵥ decryptColumn P C)`, on every secret and
ciphertext. -/
theorem dot_B : ∀ (s : Fin 1 → ZMod 2) (C : Ciphertext B),
    decrypt B s C = LWE.BitEncoding.decode B.lwe (secretVector B s ⬝ᵥ decryptColumn B C) := by
  decide +kernel

theorem dot_C4 : ∀ (s : Fin 0 → ZMod 4) (C : Ciphertext C4),
    decrypt C4 s C = LWE.BitEncoding.decode C4.lwe (secretVector C4 s ⬝ᵥ decryptColumn C4 C) := by
  decide +kernel

/- G6 and G7 are not kernel-decidable: `decryptFormula` is built with `Nat.clog 2 q`
(`modSumInterval`), and `Nat.clog` is well-founded recursion, on which kernel reduction gets stuck
(a first run of `decide +kernel` on `∀ s C, (decryptFormula A C).eval (keyBits A s) = decrypt A s C`
at `TP 0 2 1` and `TP 1 2 1`, and on G7 at `TP 0 2 1`, failed with "reduction got stuck",
log `P4_kernel_attempt.log`). They are checked by `#eval` below. -/

/-! ### P4b: `#eval` -/

/-- A pseudo-random residue stream (LCG). -/
def lcg (x : ℕ) : ℕ := (1103515245 * x + 12345) % 2147483648

/-- The `k`-th pseudo-random ciphertext. -/
def rnd (P : Parameters) (k : ℕ) : Ciphertext P :=
  fun i j => ((lcg (lcg (k * 7919 + i.val * 104729 + j.val * 1299709 + 17)) / 65536 : ℕ) :
    ZMod P.lwe.modulus)

/-- Every ciphertext, by its index in `[0, q^((n+1)·N))` (base-`q` digits). -/
def nth (P : Parameters) (k : ℕ) : Ciphertext P :=
  fun i j => ((k / P.lwe.modulus ^ (i.val * P.columns + j.val) % P.lwe.modulus : ℕ) :
    ZMod P.lwe.modulus)

/-- Every secret, by its index in `[0, q^n)`. -/
def sec (P : Parameters) (k : ℕ) : Fin P.lwe.dimension → ZMod P.lwe.modulus :=
  fun i => ((k / P.lwe.modulus ^ i.val % P.lwe.modulus : ℕ) : ZMod P.lwe.modulus)

/-- G5, G6 and the proposed `decrypt_eq_decode_dotProduct` on the ciphertexts `cs`, every secret:
(G5 mismatches, G6 mismatches, checks, dotProduct-lemma mismatches). -/
def g56 (P : Parameters) (cs : List (Ciphertext P)) : ℕ × ℕ × ℕ × ℕ :=
  let ss := (List.range (P.lwe.modulus ^ P.lwe.dimension)).map (sec P)
  cs.foldl (fun acc C =>
    let f := decryptFormula P C
    ss.foldl (fun acc s =>
      (acc.1 + (if secretVector P s ⬝ᵥ decryptColumn P C =
          ∑ i, ((keyBits P s i).toNat : ZMod P.lwe.modulus) * decConstants P C i then 0 else 1),
       acc.2.1 + (if f.eval (keyBits P s) = decrypt P s C then 0 else 1),
       acc.2.2.1 + 1,
       acc.2.2.2 + (if decrypt P s C =
          LWE.BitEncoding.decode P.lwe (secretVector P s ⬝ᵥ decryptColumn P C) then 0 else 1)))
      acc) (0, 0, 0, 0)

/-- G7 and G8 on the pairs `ps`, every secret: (G7 mismatches, depth violations, fan-in
violations, checks, max depth seen, decDepth P + 1). -/
def g78 (P : Parameters) (ps : List (Ciphertext P × Ciphertext P)) :
    ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  let ss := (List.range (P.lwe.modulus ^ P.lwe.dimension)).map (sec P)
  ps.foldl (fun acc (C₁, C₂) =>
    let f := nandFormula P C₁ C₂
    let d := f.depth
    let acc := (acc.1, acc.2.1 + (if d ≤ decDepth P + 1 then 0 else 1),
      acc.2.2.1 + (if f.maxFanin ≤ 2 then 0 else 1), acc.2.2.2.1, max acc.2.2.2.2.1 d,
      acc.2.2.2.2.2)
    ss.foldl (fun acc s =>
      (acc.1 + (if f.eval (keyBits P s) = !(decrypt P s C₁ && decrypt P s C₂) then 0 else 1),
       acc.2.1, acc.2.2.1, acc.2.2.2.1 + 1, acc.2.2.2.2)) acc)
    (0, 0, 0, 0, 0, decDepth P + 1)

def allC (P : Parameters) : List (Ciphertext P) :=
  (List.range (P.lwe.modulus ^ ((P.lwe.dimension + 1) * P.columns))).map (nth P)
def rndC (P : Parameters) (k : ℕ) : List (Ciphertext P) := (List.range k).map (rnd P)
def rndPairs (P : Parameters) (k : ℕ) : List (Ciphertext P × Ciphertext P) :=
  (List.range k).map fun i => (rnd P (2 * i + 1000), rnd P (2 * i + 1001))

end P4

open P4

#eval ("TP 1 2 1, all C", g56 (TP 1 2 1 (by decide) (by decide)) (allC _))
#eval ("TP 0 4 2, all C", g56 (TP 0 4 2 (by decide) (by decide)) (allC _))
#eval ("TP 1 3 2, 200 random C", g56 (TP 1 3 2 (by decide) (by decide)) (rndC _ 200))
#eval ("TP 1 4 2, 40 random C", g56 (TP 1 4 2 (by decide) (by decide)) (rndC _ 40))
#eval ("TP 1 5 3, 6 random C", g56 (TP 1 5 3 (by decide) (by decide)) (rndC _ 6))
#eval ("TP 1 8 3, 4 random C", g56 (TP 1 8 3 (by decide) (by decide)) (rndC _ 4))
#eval ("TP 1 2 1, G7/G8, all pairs", g78 (TP 1 2 1 (by decide) (by decide))
  ((allC (TP 1 2 1 (by decide) (by decide))).flatMap fun a =>
    (allC (TP 1 2 1 (by decide) (by decide))).map fun b => (a, b)))
#eval ("TP 1 3 2, G7/G8, 40 random pairs", g78 (TP 1 3 2 (by decide) (by decide)) (rndPairs _ 40))
#eval ("TP 1 4 2, G7/G8, 8 random pairs", g78 (TP 1 4 2 (by decide) (by decide)) (rndPairs _ 8))
#eval ("TP 1 5 3, G7/G8, 2 random pairs", g78 (TP 1 5 3 (by decide) (by decide)) (rndPairs _ 2))

#print axioms P4.g5_B
#print axioms P4.g5_C4
#print axioms P4.dot_B
#print axioms P4.dot_C4
