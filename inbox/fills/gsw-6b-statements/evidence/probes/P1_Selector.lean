import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Branching
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Scheme

/-! Probe P1 (gsw-6b statements, check 7): the selector `select` and G1 (`Encrypts.select`).

* **P1a** (kernel `decide`), toy parameters `n = 1`, `m = 2`, `ℓ = 3`, `q ∈ {4, 5, 8}` (`N = 6`):
  on noise-free encryptions of bits `b • G` (and on `encrypt` under the zero public key, which is
  `b • G`), `select P (b•G) (u•G) (v•G) = ((1 − b)·u + b·v) • G` for all bits `b, u, v`; and the
  exact identity `select P (b•G) U V = (1 − b)•U + b•V` on fixed non-ciphertext matrices `U, V`.
* **P1b** (kernel `decide` on a numeric witness check), `n = 1`, `m = 2`, `ℓ = 8`, `q = 256`
  (`N = 16`, so the bounds are below `q/2 = 128` and not vacuous): ciphertexts with explicit
  integer error vectors under the fixed key vector `t = (−3, 1)` (built as `b•G + X` with
  `tᵀX = e`); for every bit `b` and every message pair, and for error patterns chosen to push the
  noise up (all errors `+β`, `U` decomposing to all ones, `V` to all zeros), the conclusion of G1
  `Encrypts P t ((1 − b)·u + b·v) (βV + 2·(N·β)) (select P C U V)` is proved by kernel `decide`
  of the witness check `checkB` (sound by `encrypts_of_check`, proved below from
  `encrypts_iff`). The `#eval`s print the observed maximal noise against the bound.
-/

open TCSlib.Cryptography
open TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

namespace P1

/-- Toy GSW parameters: `n = 1`, `m = 2`, modulus `q`, width `ℓ`. -/
abbrev TP (q ℓ : ℕ) (hq : 2 ≤ q) (hℓ : q ≤ 2 ^ ℓ) : Parameters := ⟨⟨1, 2, q, hq⟩, ℓ, hℓ⟩

abbrev P4 : Parameters := TP 4 3 (by decide) (by decide)
abbrev P5 : Parameters := TP 5 3 (by decide) (by decide)
abbrev P8 : Parameters := TP 8 3 (by decide) (by decide)

/-- The noise-free encryption `b • G` of an integer message. -/
def enc0 (P : Parameters) (b : ℤ) : Ciphertext P := (b : ZMod P.lwe.modulus) • gadget P

/-- The selector's message `(1 − b)·u + b·v` of three bits. -/
def selMsg (b u v : Bool) : ℤ := (1 - (b.toNat : ℤ)) * u.toNat + b.toNat * v.toNat

/-! ### P1a: noise-free selection, kernel `decide` -/

theorem sel_bits_q4 : ∀ b u v : Bool,
    select P4 (enc0 P4 b.toNat) (enc0 P4 u.toNat) (enc0 P4 v.toNat) = enc0 P4 (selMsg b u v) := by
  decide
theorem sel_bits_q5 : ∀ b u v : Bool,
    select P5 (enc0 P5 b.toNat) (enc0 P5 u.toNat) (enc0 P5 v.toNat) = enc0 P5 (selMsg b u v) := by
  decide
theorem sel_bits_q8 : ∀ b u v : Bool,
    select P8 (enc0 P8 b.toNat) (enc0 P8 u.toNat) (enc0 P8 v.toNat) = enc0 P8 (selMsg b u v) := by
  decide

/-- The coins of a toy encryption (any fixed binary matrix). -/
def R5 : Matrix (Fin 2) (Fin P5.columns) Bool := fun i j => (i.val + j.val) % 3 == 0

/-- Encryption under the zero public key is `μ • G` (phase-5 `encrypt`, zero key). -/
theorem encrypt_zero_pk_q5 : ∀ μ : Bool, encrypt P5 (0, 0) μ R5 = enc0 P5 μ.toNat := by decide

theorem sel_encrypt_zero_pk_q5 : ∀ b u v : Bool,
    select P5 (encrypt P5 (0, 0) b R5) (encrypt P5 (0, 0) u R5) (encrypt P5 (0, 0) v R5) =
      enc0 P5 (selMsg b u v) := by
  decide

/-- Two fixed matrices that are not encryptions of anything in particular. -/
def U5 : Ciphertext P5 := fun i j => ((7 * i.val + 3 * j.val + 1 : ℕ) : ZMod 5)
def V5 : Ciphertext P5 := fun i j => ((2 * i.val * j.val + j.val + 4 : ℕ) : ZMod 5)
def U8 : Ciphertext P8 := fun i j => ((5 * i.val + 3 * j.val + 1 : ℕ) : ZMod 8)
def V8 : Ciphertext P8 := fun i j => ((3 * i.val * j.val + j.val + 6 : ℕ) : ZMod 8)

/-- With a noise-free bit selector the selection is exact on arbitrary matrices:
`select P (b•G) U V = (1 − b)•U + b•V` (`G·G⁻¹(X) = X`). -/
theorem sel_exact_q5 : ∀ b : Bool,
    select P5 (enc0 P5 b.toNat) U5 V5 =
      ((1 - (b.toNat : ZMod 5)) • U5 + (b.toNat : ZMod 5) • V5 : Ciphertext P5) := by
  decide
theorem sel_exact_q8 : ∀ b : Bool,
    select P8 (enc0 P8 b.toNat) U8 V8 =
      ((1 - (b.toNat : ZMod 8)) • U8 + (b.toNat : ZMod 8) • V8 : Ciphertext P8) := by
  decide

/-! ### P1b: G1's noise bound on explicit small errors, kernel `decide` -/

abbrev Q : Parameters := TP 256 8 (by decide) (by decide)

/-- The secret `s = 3` and the key vector `t = (−3, 1)`. -/
def s : Fin 1 → ZMod 256 := fun _ => 3
def t : Fin 2 → ZMod 256 := secretVector Q s

/-- A ciphertext of the integer `b` with error vector `e` under `t`: `b•G + X`, `X` with rows
`r` and `e + 3r`, so `tᵀX = −3r + e + 3r = e`. -/
def mk (b : ℤ) (r : Fin Q.columns → ℕ) (e : Fin Q.columns → ℤ) : Ciphertext Q :=
  fun i j => enc0 Q b i j +
    if i.val = 0 then ((r j : ℤ) : ZMod 256) else ((e j + 3 * r j : ℤ) : ZMod 256)

/-- The minimal integer error of `C` as an encryption of `x` under `t`. -/
def err (P : Parameters) (t : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus) (x : ℤ)
    (C : Ciphertext P) : Fin P.columns → ℤ :=
  fun j => (Matrix.vecMul t C j - (x : ZMod P.lwe.modulus) * Matrix.vecMul t (gadget P) j).valMinAbs

/-- The witness check: every minimal error has magnitude at most `β`. -/
def checkB (P : Parameters) (t : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus) (x : ℤ) (β : ℕ)
    (C : Ciphertext P) : Prop := ∀ j, (err P t x C j).natAbs ≤ β

instance (P : Parameters) (t : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus) (x : ℤ) (β : ℕ)
    (C : Ciphertext P) : Decidable (checkB P t x β C) := by
  unfold checkB; infer_instance

/-- Soundness of the check: it gives `Encrypts` with the minimal error as witness. -/
theorem encrypts_of_check (P : Parameters) (t : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus)
    (x : ℤ) (β : ℕ) (C : Ciphertext P) (h : checkB P t x β C) : Encrypts P t x β C := by
  rw [encrypts_iff]
  refine ⟨err P t x C, h, ?_⟩
  funext j
  simp only [err, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ZMod.coe_valMinAbs]
  ring

/-- Error patterns: all `+β`, alternating signs, and a sparse one. -/
def eAll (β : ℤ) : Fin Q.columns → ℤ := fun _ => β
def eAlt (β : ℤ) : Fin Q.columns → ℤ := fun j => if j.val % 2 = 0 then β else -β
def eSparse (β : ℤ) : Fin Q.columns → ℤ := fun j => if j.val % 5 = 1 then -β else 0
def r0 : Fin Q.columns → ℕ := fun j => (37 * j.val + 11) % 256
def r1 : Fin Q.columns → ℕ := fun j => (101 * j.val + 7) % 256

/-- `U` with all entries `255` (all-ones decomposition) encrypting `u` with error `eU`: its first
row is `255`, so `r = 255 − u·G₀`, and its second row `255` gives the error. We build it as
`mk` with the error read back by `err` (the check is on `err` anyway). -/
def Uones : Ciphertext Q := fun _ _ => 255

/-- G1 instances, β = 2, βV = 3, bound βV + 2·(N·β) = 3 + 2·(16·2) = 67 < 128. -/
theorem g1_a : ∀ b u v : Bool,
    checkB Q t (selMsg b u v) (3 + 2 * (Q.columns * 2))
      (select Q (mk b.toNat r0 (eAll 2)) (mk u.toNat r1 (eAlt 3)) (mk v.toNat r0 (eSparse 3))) := by
  decide

theorem g1_b : ∀ b u v : Bool,
    checkB Q t (selMsg b u v) (3 + 2 * (Q.columns * 2))
      (select Q (mk b.toNat r1 (eAlt 2)) (mk u.toNat r0 (eAll (-3))) (mk v.toNat r1 (eAll 3))) := by
  decide

/-- The all-ones `U` encrypts `0` with error `err Q t 0 Uones` (here `255 − 3·255·…`); its noise
is computed below; with `V = 0` (noise `0`), the product `(G − C) ⊡ U` hits `−e_C·G⁻¹(U)` =
`−N·β` in every coordinate. -/
def βU : ℕ := (List.ofFn fun j => (err Q t 0 Uones j).natAbs).foldl max 0

theorem g1_c : ∀ b : Bool,
    checkB Q t ((1 - (b.toNat : ℤ)) * 0 + b.toNat * 0) (βU + 2 * (Q.columns * 2))
      (select Q (mk b.toNat r0 (eAll 2)) Uones 0) := by
  decide

/-- Instances of G1's conclusion itself (`Encrypts`), through the sound check. -/
theorem g1_encrypts_a (b u v : Bool) :
    Encrypts Q t (selMsg b u v) (3 + 2 * (Q.columns * 2))
      (select Q (mk b.toNat r0 (eAll 2)) (mk u.toNat r1 (eAlt 3)) (mk v.toNat r0 (eSparse 3))) :=
  encrypts_of_check _ _ _ _ _ (g1_a b u v)

/-- The inputs satisfy G1's hypotheses (with the same check). -/
theorem g1_hyps : ∀ b u v : Bool,
    checkB Q t b.toNat 2 (mk b.toNat r0 (eAll 2)) ∧ checkB Q t u.toNat 3 (mk u.toNat r1 (eAlt 3)) ∧
      checkB Q t v.toNat 3 (mk v.toNat r0 (eSparse 3)) := by
  decide

/-- Maximal observed noise of a ciphertext as an encryption of `x`. -/
def noise (x : ℤ) (C : Ciphertext Q) : ℕ := (List.ofFn fun j => (err Q t x C j).natAbs).foldl max 0

end P1

open P1 in
#eval (βU, [false, true].map fun b =>
  (noise ((1 - (b.toNat : ℤ)) * 0) (select Q (mk b.toNat r0 (eAll 2)) Uones 0),
   βU + 2 * (Q.columns * 2)))
open P1 in
#eval [false, true].flatMap fun b => [false, true].flatMap fun u => [false, true].map fun v =>
  ((b, u, v), noise (selMsg b u v)
    (select Q (mk b.toNat r0 (eAll 2)) (mk u.toNat r1 (eAlt 3)) (mk v.toNat r0 (eSparse 3))),
   noise (selMsg b u v)
    (select Q (mk b.toNat r1 (eAlt 2)) (mk u.toNat r0 (eAll (-3))) (mk v.toNat r1 (eAll 3))),
   3 + 2 * (Q.columns * 2))
#print axioms P1.sel_bits_q8
#print axioms P1.sel_exact_q8
#print axioms P1.g1_encrypts_a
#print axioms P1.g1_c

namespace P1
/-- Tightness: with `C` of error `+2` everywhere (`β = 2`) and `U` decomposing to all ones, the
selection at `b = 1` has noise `32 = N·β`, so the bound cannot drop below `N·β`; the decide
below refutes the bound `31`. (G1's `βV + 2·(N·β)` is valid; the observed worst case of this
construction is `N·β + βV`, see the `#eval` above.) -/
theorem g1_tight : ¬ checkB Q t 0 31 (select Q (mk 1 r0 (eAll 2)) Uones 0) := by
  decide
end P1
#print axioms P1.g1_tight
