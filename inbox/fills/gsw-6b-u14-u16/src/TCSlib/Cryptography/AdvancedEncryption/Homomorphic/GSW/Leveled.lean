/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Bootstrap
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Eval
import TCSlib.Complexity.CircuitComplexity.NANDLayering

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Leveled fully homomorphic GSW: the consecutive key chain over layered NAND circuits

## Main definitions

* `LevelCoins`: the coins of the `N·L` level-key encryptions.
* `levelKey`: the level-`d` evaluation key of the consecutive chain, the encryptions under
  `pk_{d+1}` of the key bits of `s_d` (`d : Fin L`, so `evk_{d+1}` in one-based levels).
* `literalCts`: the `2k` level-0 ciphertexts, `cts` followed by their negations `G − cts j`
  (`homNot`).
* `levelGate`: a gate at level `δ ≥ 1` bootstrapped with the level key `δ − 1`.
* `leveledEval`: a layered NAND-form circuit on the `2k` literals run by the host `runWith`
  (registry row H19), each gate by `levelGate` at its level `depthAt`.
* `leveledEvalCircuit`: any fan-in-2 circuit, through `toNANDForm` and the layering
  `layerNAND`.

## Main results

* `encrypts_levelKey` (L1): level-key noise `m·B`, a proved citation of phase 5's
  `encrypts_keygen_encrypt`.
* `encrypts_leveledEval` (L2): the output of a layered NAND circuit of depth at most `L`
  encrypts its value under the key of its level, with noise `max βin (bootNoise P βk)`.
* `decrypt_keygen_leveledEvalCircuit` (L3): honest keys, every fan-in-2 circuit whose NAND form
  has depth at most `L`.

L2 and L3 are proved, as is L1.

**Compactness** holds by typing: `leveledEval` and `leveledEvalCircuit` return a
`Ciphertext P` whatever the circuit [BV14, Def 2.12, p008-b001]; only the evaluation key
(`N·L` ciphertexts) depends on `L` [BV11, Thm 3.1, p015-b001].

**Sources and reconstruction (P6-Q19 B).** The key chain is Gentry's [Gen09, §4.1, `KeyGen` of
`E^(d)`, pp. 46–47, p056-b003]: `d + 1` independent key pairs and, for `i ∈ [1, d]`, the
encryptions under `pk_{i−1}` of the representation of `sk_i` as plaintexts. Gentry encrypts the
keys in reverse order [Gen09, §4.1, p. 46, p056-b002], so his evaluation runs down the index
(inputs under `pk_d`, decryption under `sk_0`); here it runs up, and his level `i` is level
`L − i` (`levelKey`). His circuits are layered as well: every wire joins consecutive levels,
with trivial gates added where needed [Gen09, §4.1, p. 47, p057-b001]. The hybrid order is
[Gen09, Thm 4.2.3, pp. 50–51, p060-b001, p061-b001] (`GSW/LeveledSecurity.lean`). Besides
[Gen09] for the chain, the statements of the leveled scheme cite [BV11, Thm 3.1, Def 3.6],
[BV14, Thm 2.14 first part, Thm 3.7] and [AP14, §5.3]; [BV14, Def 2.12, §3.3] and
[Bar89, Thm 1] are cited for compactness and the literal inputs.

## References

* [BV14] Z. Brakerski, V. Vaikuntanathan, *Lattice-Based FHE as Secure as PKE*, ITCS 2014;
  IACR ePrint 2013/541: Def 2.12, Thm 2.14 (first part), Thm 3.7.
* [BV11] Z. Brakerski, V. Vaikuntanathan, *Efficient Fully Homomorphic Encryption from
  (Standard) LWE*, FOCS 2011 full version; IACR ePrint 2011/344: Def 3.6, Thm 3.1.
* [AP14] J. Alperin-Sheriff, C. Peikert, *Faster Bootstrapping with Polynomial Error*,
  CRYPTO 2014; IACR ePrint 2014/094: §5.3.
* [Bar89] D. A. Mix Barrington, *Bounded-width polynomial-size branching programs recognize
  exactly those languages in NC¹*, J. Comput. System Sci. 38(1) (1989), 150–164: Thm 1
  ("inputs and negated inputs").
* [Gen09] C. Gentry, *A Fully Homomorphic Encryption Scheme*, PhD thesis, Stanford University,
  September 2009: §4.1 (`KeyGen` of `E^(d)`, the reverse order, layered circuits), Thm 4.2.3.

**Deviations.** `L + 1` independent key pairs in a consecutive chain (P6-Q14 B): `evk_{d+1}`
encrypts under `pk_{d+1}` the `N` key bits of `s_d`, `N·L` ciphertexts in all. Circuits are
layered NAND circuits on the `2k` literals (6a's `layerNAND`, `litInput`); the negative
literals are `homNot P [C] = G − C`, under the same key with the same noise. Decryption uses
the circuit's output level, which is public, as the key index ([BV11, Def 3.6]'s `Dec` is
level-agnostic). Noise and correctness are worst case. The evaluation keys are public-key
encryptions under the user's own keys (P6-Q8).
-/

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

open BoolCircuit
open Encryption.PublicKey

/-- The coins of the level keys: one coin matrix for each of the `N` positions of each of the
`L` levels. Reducible notation. -/
abbrev LevelCoins (P : Parameters) (L : ℕ) : Type :=
  Fin L → Fin P.columns → Coins P

/-- `LevelCoins P L` is `Fin L → Fin P.columns → Coins P`. -/
theorem LevelCoins_eq (P : Parameters) (L : ℕ) :
    LevelCoins P L = (Fin L → Fin P.columns → Coins P) := rfl

/-- **The level key** of the consecutive chain (P6-Q14 B) [BV11, Thm 3.1, p015-b001: "only the
length of the evaluation key depends on the level L"; BV14, Thm 2.14 first part, p008-b003]:
for `d : Fin L`, the encryptions under `pk_{d+1}` of the `N` key bits of `s_d`, with the coins
`R d`, `levelKey P pks ss R d = evalKey P (pks d.succ) (ss d.castSucc) (R d)`. In all `N·L`
ciphertexts. The chain is [Gen09, §4.1, `KeyGen` of `E^(d)`, pp. 46–47, p056-b003] with the
levels renumbered: Gentry encrypts `sk_i` under `pk_{i−1}`, in reverse order [Gen09, §4.1,
p. 46, p056-b002], and his level `i` is level `L − i` here. -/
def levelKey (P : Parameters) {L : ℕ} (pks : Fin (L + 1) → PublicKey P)
    (ss : Fin (L + 1) → Secret P) (R : LevelCoins P L) (d : Fin L) :
    Fin P.columns → Ciphertext P :=
  evalKey P (pks d.succ) (ss d.castSucc) (R d)

/-- `levelKey P pks ss R d` is `evalKey P (pks d.succ) (ss d.castSucc) (R d)`. -/
theorem levelKey_eq (P : Parameters) {L : ℕ} (pks : Fin (L + 1) → PublicKey P)
    (ss : Fin (L + 1) → Secret P) (R : LevelCoins P L) (d : Fin L) :
    levelKey P pks ss R d = evalKey P (pks d.succ) (ss d.castSucc) (R d) := rfl

/-- **The level-0 literal ciphertexts** [Bar89, Thm 1, p003-b002: "inputs and negated inputs";
BV14, §3.3, p014-b002: the complements `I − C_k`]: the input ciphertexts followed by their
negations `homNot P [cts j] = G − cts j`, in the order of 6a's `litInput`,
`literalCts P cts = Fin.append cts (fun j => homNot P [cts j])`. -/
def literalCts (P : Parameters) {k : ℕ} (cts : Fin k → Ciphertext P) :
    Fin (k + k) → Ciphertext P :=
  Fin.append cts fun j => homNot P [cts j]

/-- `literalCts P cts` is `Fin.append cts (fun j => homNot P [cts j])`. -/
theorem literalCts_eq (P : Parameters) {k : ℕ} (cts : Fin k → Ciphertext P) :
    literalCts P cts = Fin.append cts fun j => homNot P [cts j] := rfl

/-- The first `k` literal ciphertexts are the inputs:
`literalCts P cts (Fin.castAdd k j) = cts j`. -/
theorem literalCts_castAdd (P : Parameters) {k : ℕ} (cts : Fin k → Ciphertext P) (j : Fin k) :
    literalCts P cts (Fin.castAdd k j) = cts j := by
  rw [literalCts_eq, Fin.append_left]

/-- The last `k` literal ciphertexts are the negations:
`literalCts P cts (Fin.natAdd k j) = homNot P [cts j]`. -/
theorem literalCts_natAdd (P : Parameters) {k : ℕ} (cts : Fin k → Ciphertext P) (j : Fin k) :
    literalCts P cts (Fin.natAdd k j) = homNot P [cts j] := by
  rw [literalCts_eq, Fin.append_right]

/-- **The level gate**: a gate at level `δ` (its `depthAt`) with `1 ≤ δ ≤ L` is bootstrapped
(`bootGate`, with its padding) under the level key `δ − 1`, which encrypts the bits of
`s_{δ−1}` under `pk_δ`; above level `L` it gives the noiseless `0` (never read by the output of
a circuit of depth at most `L`),
`levelGate P lk δ g cts = if h : δ - 1 < L then bootGate P (lk ⟨δ - 1, h⟩) g cts else 0`.
Reconstruction disclosed (module docstring). -/
def levelGate (P : Parameters) {L : ℕ} (lk : Fin L → Fin P.columns → Ciphertext P) (δ : ℕ)
    (g : DAGGate) (cts : List (Ciphertext P)) : Ciphertext P :=
  if h : δ - 1 < L then bootGate P (lk ⟨δ - 1, h⟩) g cts else 0

/-- Below the top: `δ - 1 < L → levelGate P lk δ g cts = bootGate P (lk ⟨δ - 1, h⟩) g cts`. -/
theorem levelGate_of_lt (P : Parameters) {L : ℕ} (lk : Fin L → Fin P.columns → Ciphertext P)
    (δ : ℕ) (g : DAGGate) (cts : List (Ciphertext P)) (h : δ - 1 < L) :
    levelGate P lk δ g cts = bootGate P (lk ⟨δ - 1, h⟩) g cts := by
  unfold levelGate
  rw [dif_pos h]

/-- Above the top: `L ≤ δ - 1 → levelGate P lk δ g cts = 0`. -/
theorem levelGate_of_le (P : Parameters) {L : ℕ} (lk : Fin L → Fin P.columns → Ciphertext P)
    (δ : ℕ) (g : DAGGate) (cts : List (Ciphertext P)) (h : L ≤ δ - 1) :
    levelGate P lk δ g cts = 0 := by
  unfold levelGate
  rw [dif_neg (Nat.not_lt.mpr h)]

/-- **Leveled evaluation** of a layered NAND-form circuit on the `2k` literal ciphertexts
[BV14, Thm 2.14 first part, p008-b003; BV11, Thm 3.1, Def 3.6, p015-b001, p014-b001]: run the
host `runWith` (H19) over the gates, the gate at vertex `v` (the length of the data so far) by
`levelGate` at its level `Cc.depthAt v`, and read the output vertex,
`leveledEval P lk Cc cts = (runWith (fun g vs => levelGate P lk (Cc.depthAt vs.length) g vs)
Cc.gates (List.ofFn cts)).getD Cc.output 0`. Computable. **Compactness by typing**: the
result is a `Ciphertext P` whatever `Cc`. Reconstruction disclosed (module docstring). -/
def leveledEval (P : Parameters) {L k : ℕ} (lk : Fin L → Fin P.columns → Ciphertext P)
    (Cc : DAGCircuit (k + k)) (cts : Fin (k + k) → Ciphertext P) : Ciphertext P :=
  (runWith (fun g vs => levelGate P lk (Cc.depthAt vs.length) g vs) Cc.gates
    (List.ofFn cts)).getD Cc.output 0

/-- `leveledEval P lk Cc cts` is `(runWith (fun g vs => levelGate P lk (Cc.depthAt vs.length) g vs)
Cc.gates (List.ofFn cts)).getD Cc.output 0`. -/
theorem leveledEval_eq (P : Parameters) {L k : ℕ} (lk : Fin L → Fin P.columns → Ciphertext P)
    (Cc : DAGCircuit (k + k)) (cts : Fin (k + k) → Ciphertext P) :
    leveledEval P lk Cc cts =
      (runWith (fun g vs => levelGate P lk (Cc.depthAt vs.length) g vs) Cc.gates
        (List.ofFn cts)).getD Cc.output 0 := rfl

/-- **Leveled evaluation of any fan-in-2 circuit** on `k ≥ 1` inputs [BV14, Thm 2.14 first
part, p008-b003; BV11, Def 3.6, p014-b001]: `leveledEval` of the layered NAND form
`(Cc.toNANDForm hC).layerNAND` (6a's N3–N13) on the literal ciphertexts,
`leveledEvalCircuit P lk Cc hC cts = leveledEval P lk (Cc.toNANDForm hC).layerNAND
(literalCts P cts)`. Computable. **Compactness by typing**. Reconstruction disclosed (module
docstring). -/
def leveledEvalCircuit (P : Parameters) {L k : ℕ} [NeZero k]
    (lk : Fin L → Fin P.columns → Ciphertext P) (Cc : DAGCircuit k)
    (hC : ∀ g ∈ Cc.gates, g.args.length ≤ 2) (cts : Fin k → Ciphertext P) : Ciphertext P :=
  leveledEval P lk (Cc.toNANDForm hC).layerNAND (literalCts P cts)

/-- `leveledEvalCircuit P lk Cc hC cts` is `leveledEval P lk (Cc.toNANDForm hC).layerNAND
(literalCts P cts)`. -/
theorem leveledEvalCircuit_eq (P : Parameters) {L k : ℕ} [NeZero k]
    (lk : Fin L → Fin P.columns → Ciphertext P) (Cc : DAGCircuit k)
    (hC : ∀ g ∈ Cc.gates, g.args.length ≤ 2) (cts : Fin k → Ciphertext P) :
    leveledEvalCircuit P lk Cc hC cts =
      leveledEval P lk (Cc.toNANDForm hC).layerNAND (literalCts P cts) := rfl

/-! ### Targets L1–L3 -/

/-- **L1. Level-key noise.** For a `B`-bounded noise law and honest key generation at every
level, `pk_d = (Regev.keygen P.lwe χ (rgs d)).1` and `s_d = (Regev.keygen P.lwe χ (rgs d)).2`,
every ciphertext of the level key `d` encrypts the key bit `j` of `s_d` under the key vector of
`s_{d+1}` with noise at most `m·B`:
`Encrypts P (secretVector P s_{d+1}) (keyBits P s_d j).toNat (P.lwe.samples * B)
(levelKey P pks ss R d j)` [BV11, Thm 3.1, p015-b001; BV14, Thm 2.14 first part, p008-b003].
A citation, proved: phase 5's `encrypts_keygen_encrypt` read through `levelKey_eq` and
`evalKey_eq`. Reconstruction disclosed (module docstring). -/
theorem encrypts_levelKey (P : Parameters) (χ : LWE.Noise) (B : ℕ) (hχ : χ.Bounded B) {L : ℕ}
    (rgs : Fin (L + 1) → KeySeed P χ) (R : LevelCoins P L) (d : Fin L) (j : Fin P.columns) :
    Encrypts P (secretVector P (Regev.keygen P.lwe χ (rgs d.succ)).2)
      ((keyBits P (Regev.keygen P.lwe χ (rgs d.castSucc)).2 j).toNat : ℤ) (P.lwe.samples * B)
      (levelKey P (fun e => (Regev.keygen P.lwe χ (rgs e)).1)
        (fun e => (Regev.keygen P.lwe χ (rgs e)).2) R d j) := by
  rw [levelKey_eq, evalKey_eq]
  exact encrypts_keygen_encrypt P χ (rgs d.succ) B hχ _ (R d j)

/-- **L2. Leveled correctness, noise form.** Let `ss : Fin (L + 1) → Secret P` be the level
secrets, `lk d` encrypt the key bits of `s_d` under the key vector of `s_{d+1}` with noise at
most `βk`, and the `2k` input ciphertexts encrypt the bits `y j` under `s_0` with noise at most
`βin`. If `2·(ℓ·βin) < ⌊q/2⌋` and `2·(ℓ·bootNoise P βk) < ⌊q/2⌋`, then for every layered
NAND-form circuit `Cc` of depth at most `L`, the output encrypts `Cc.eval y` under the key of
level `Cc.depth` with noise at most `max βin (bootNoise P βk)`:
`Encrypts P (secretVector P (ss ⟨Cc.depth, _⟩)) (Cc.eval y).toNat (max βin (bootNoise P βk))
(leveledEval P lk Cc cts)` [BV14, Thm 2.14 first part, p008-b003; BV11, Thm 3.1, Def 3.6,
p015-b001, p014-b001]. Deviations: layered circuits on literal inputs, the public output level,
worst case; reconstruction disclosed (module docstring).

**Proof sketch.** Apply the host lemma `runWith_rel` (H19) to `DAGGate.eval` from
`List.ofFn y` and to the leveled gate function from `List.ofFn cts`, with the vertex relation:
"if `Cc.depthAt v ≤ L`, the ciphertext encrypts the value under `s_{depthAt v}` with noise at most
`max βin (bootNoise P βk)`". Inputs have level `0` (`depthAt_input`): `hin` (`Encrypts.mono`). A
gate at vertex `v = 2k + i` (`runWith_rel` hands it the data of length `v`) has level
`δ = Cc.depthAt v ≥ 1` (`depthAt_gate`, `DAGGate.depth_eq`); if `δ ≤ L`, `levelGate_of_lt`
selects the level key `δ − 1`. The circuit is layered (`isLayered_iff`), so every argument is
at level `δ − 1` and, by the relation and `decrypt_of_encrypts` (with `hβin` or `hboot`),
decrypts under `s_{δ−1}` to its value. The gate step is `encrypts_bootGate` (`s = s_{δ−1}`,
`t' = t_δ`, `hk` at `δ − 1`, whose successor is `δ`): the padded `G` decrypts to `true`
(`encrypts_gadget`), and the three case readers of `bootGate` and G9 (`encrypts_bootNAND`) give
an encryption under `s_δ` of the NAND of the argument values with noise `bootNoise P βk`, which
is the gate's value (`isNANDForm_iff`, `DAGGate.eval_of_isNAND`, N1).
Gates above level `L` are unconstrained and are never read by a vertex at level `≤ L`. At the
output (`Cc.output_lt`, level `Cc.depth = depthAt Cc.output` by `depth_eq`, at most `L`), read
`DAGCircuit.eval_eq`, `values_eq` and `leveledEval_eq`. -/
theorem encrypts_leveledEval (P : Parameters) {L k : ℕ} (Cc : DAGCircuit (k + k))
    (hNAND : Cc.IsNANDForm) (hlay : Cc.IsLayered) (hdepth : Cc.depth ≤ L)
    (ss : Fin (L + 1) → Secret P) (lk : Fin L → Fin P.columns → Ciphertext P) (βk βin : ℕ)
    (hk : ∀ d j, Encrypts P (secretVector P (ss d.succ)) ((keyBits P (ss d.castSucc) j).toNat : ℤ)
      βk (lk d j))
    (y : Fin (k + k) → Bool) (cts : Fin (k + k) → Ciphertext P)
    (hin : ∀ j, Encrypts P (secretVector P (ss 0)) ((y j).toNat : ℤ) βin (cts j))
    (hβin : 2 * (P.width * βin) < P.lwe.modulus / 2)
    (hboot : 2 * (P.width * bootNoise P βk) < P.lwe.modulus / 2) :
    Encrypts P (secretVector P (ss ⟨Cc.depth, Nat.lt_succ_of_le hdepth⟩)) ((Cc.eval y).toNat : ℤ)
      (max βin (bootNoise P βk)) (leveledEval P lk Cc cts) := by
  have hsep : 2 * (P.width * max βin (bootNoise P βk)) < P.lwe.modulus / 2 := by
    rcases max_cases βin (bootNoise P βk) with ⟨hm, _⟩ | ⟨hm, _⟩
    · rw [hm]; exact hβin
    · rw [hm]; exact hboot
  -- Step 1: the per-vertex invariant, by `runWith_rel`: a vertex at level `≤ L` encrypts its
  -- value under the secret of its level.
  have key := runWith_rel DAGGate.eval (fun g vs => levelGate P lk (Cc.depthAt vs.length) g vs)
    (fun v b C => ∀ hv : Cc.depthAt v < L + 1, Encrypts P (secretVector P (ss ⟨Cc.depthAt v, hv⟩))
      (b.toNat : ℤ) (max βin (bootNoise P βk)) C)
    false 0 Cc.gates (List.ofFn y) (List.ofFn cts) (by rw [List.length_ofFn, List.length_ofFn])
    (by
      -- input vertices are at level `0` and hold the input encryptions
      intro v hv hv'
      rw [List.length_ofFn] at hv
      have h0 : (⟨Cc.depthAt v, hv'⟩ : Fin (L + 1)) = 0 := Fin.ext (Cc.depthAt_input hv)
      rw [List.getD_eq_getElem _ _ (by rwa [List.length_ofFn]),
        List.getD_eq_getElem _ _ (by rwa [List.length_ofFn]), List.getElem_ofFn,
        List.getElem_ofFn, h0]
      exact Encrypts.mono P (hin ⟨v, hv⟩) (le_max_left _ _))
    (by
      intro i hi a ha
      rw [List.length_ofFn]
      exact Cc.args_lt i hi a ha)
    (by
      -- a gate at level `δ ≥ 1`: its arguments are at level `δ - 1` and decrypt under `s_{δ-1}`
      intro i hi vA vB _ hB hargs
      beta_reduce
      rw [hB, List.length_ofFn]
      intro hδ
      have hd1 : 1 ≤ Cc.depthAt (k + k + i) := by
        rw [Cc.depthAt_gate hi, DAGGate.depth_eq]
        omega
      have hlt : Cc.depthAt (k + k + i) - 1 < L := by omega
      rw [levelGate_of_lt P lk _ _ _ hlt]
      have hsucc :
          (⟨Cc.depthAt (k + k + i) - 1, hlt⟩ : Fin L).succ = ⟨Cc.depthAt (k + k + i), hδ⟩ :=
        Fin.ext (by simp only [Fin.val_succ]; omega)
      have hkδ : ∀ j, Encrypts P (secretVector P (ss ⟨Cc.depthAt (k + k + i), hδ⟩))
          ((keyBits P (ss (⟨Cc.depthAt (k + k + i) - 1, hlt⟩ : Fin L).castSucc) j).toNat : ℤ) βk
          (lk ⟨Cc.depthAt (k + k + i) - 1, hlt⟩ j) := by
        intro j
        rw [← hsucc]
        exact hk _ j
      refine Encrypts.mono P (encrypts_bootGate P _ βk _ hkδ
        ((DAGCircuit.isNANDForm_iff Cc).mp hNAND _ (List.getElem_mem hi)) vA vB fun a ha => ?_)
        (le_max_right _ _)
      -- the layered property puts the argument at level `δ - 1`
      have hla := (DAGCircuit.isLayered_iff Cc).mp hlay i hi a ha
      have ha' : Cc.depthAt a < L + 1 := by omega
      have hcast : (⟨Cc.depthAt (k + k + i) - 1, hlt⟩ : Fin L).castSucc = ⟨Cc.depthAt a, ha'⟩ :=
        Fin.ext (by simp only [Fin.coe_castSucc]; omega)
      rw [hcast]
      exact decrypt_of_encrypts P _ _ _ _ (hargs a ha ha') hsep)
  -- Step 2: read the in-range output vertex, at level `Cc.depth ≤ L`.
  have hout := key Cc.output (by rw [List.length_ofFn]; exact Cc.output_lt)
    (by rw [← Cc.depth_eq]; omega)
  have hlev : (⟨Cc.depth, Nat.lt_succ_of_le hdepth⟩ : Fin (L + 1)) =
      ⟨Cc.depthAt Cc.output, by rw [← Cc.depth_eq]; omega⟩ := Fin.ext (Cc.depth_eq)
  rw [hlev, leveledEval_eq, Cc.eval_eq, Cc.values_eq]
  exact hout

/-- **L3. Leveled correctness for honest keys and every fan-in-2 circuit of NAND depth at most
`L`.** For a `B`-bounded noise law, honest key generation at every level (seeds `rgs`), level
coins `R`, input bits `x` encrypted under `pk_0` with coins `R'`, and a circuit `Cc` on
`k ≥ 1` inputs whose NAND form has depth at most `L`, if `2·(ℓ·bootNoise P (m·B)) < ⌊q/2⌋` and
`2·(ℓ·(m·B)) < ⌊q/2⌋`, then the leveled evaluation under the chain of level keys decrypts, under
the secret of level `(Cc.toNANDForm hC).depth`, to `Cc.eval x`
[BV14, Thm 3.7, p016-b001: "a leveled FHE scheme, without additional assumptions"]. Deviations:
decryption uses the public output level; worst case; reconstruction disclosed (module
docstring).

**Proof sketch.** `leveledEvalCircuit_eq`. The level keys satisfy L2's `hk` with `βk = m·B` by
L1 (`encrypts_levelKey`). The literal ciphertexts encrypt `litInput x` under `s_0` with noise
`m·B`: the first half by `encrypts_keygen_encrypt` (`literalCts_castAdd`), the second half by
`homNot_eq`, `homAnd_singleton`, `encrypts_gadget` and `Encrypts.sub` (`literalCts_natAdd`,
noise `0 + m·B`), matched with `litInput_castAdd`, `litInput_natAdd`; every `j : Fin (k + k)`
is one of the two (`Fin.addCases`). The layered circuit `(Cc.toNANDForm hC).layerNAND` is in
NAND form (`layerNAND_isNANDForm` with `toNANDForm_isNANDForm`), layered
(`layerNAND_isLayered`) and of depth `(Cc.toNANDForm hC).depth ≤ L` (`layerNAND_depth`), and
evaluates on `litInput x` to `Cc.eval x` (`layerNAND_eval`, `toNANDForm_eval`). L2 then gives
an encryption under the output level's secret with noise `max (m·B) (bootNoise P (m·B))`, and
`decrypt_of_encrypts` with `hin`/`hsep` finishes. -/
theorem decrypt_keygen_leveledEvalCircuit (P : Parameters) (χ : LWE.Noise) (B : ℕ)
    (hχ : χ.Bounded B) {L k : ℕ} [NeZero k] (rgs : Fin (L + 1) → KeySeed P χ)
    (R : LevelCoins P L) (Cc : DAGCircuit k) (hC : ∀ g ∈ Cc.gates, g.args.length ≤ 2)
    (hdepth : (Cc.toNANDForm hC).depth ≤ L) (x : Fin k → Bool) (R' : Fin k → Coins P)
    (hsep : 2 * (P.width * bootNoise P (P.lwe.samples * B)) < P.lwe.modulus / 2)
    (hin : 2 * (P.width * (P.lwe.samples * B)) < P.lwe.modulus / 2) :
    decrypt P (Regev.keygen P.lwe χ (rgs ⟨(Cc.toNANDForm hC).depth, Nat.lt_succ_of_le hdepth⟩)).2
        (leveledEvalCircuit P
          (levelKey P (fun e => (Regev.keygen P.lwe χ (rgs e)).1)
            (fun e => (Regev.keygen P.lwe χ (rgs e)).2) R) Cc hC
          fun j => encrypt P (Regev.keygen P.lwe χ (rgs 0)).1 (x j) (R' j)) =
      Cc.eval x := by
  rw [leveledEvalCircuit_eq]
  have hNF := DAGCircuit.toNANDForm_isNANDForm Cc hC
  -- the literal ciphertexts encrypt `litInput x` under `s_0` with noise `m·B`
  have hlit : ∀ j, Encrypts P (secretVector P (Regev.keygen P.lwe χ (rgs 0)).2)
      ((litInput x j).toNat : ℤ) (P.lwe.samples * B)
      (literalCts P (fun j => encrypt P (Regev.keygen P.lwe χ (rgs 0)).1 (x j) (R' j)) j) := by
    intro j
    induction j using Fin.addCases with
    | left j =>
      rw [literalCts_castAdd, litInput_castAdd]
      exact encrypts_keygen_encrypt P χ (rgs 0) B hχ (x j) (R' j)
    | right j =>
      rw [literalCts_natAdd, litInput_natAdd, homNot_eq, homAnd_singleton]
      have hm : (((!x j).toNat : ℕ) : ℤ) = 1 - ((x j).toNat : ℤ) := by
        cases x j <;> rfl
      rw [hm]
      exact Encrypts.mono P (Encrypts.sub P (encrypts_gadget P)
        (encrypts_keygen_encrypt P χ (rgs 0) B hχ (x j) (R' j))) (by omega)
  -- L2 on the layered NAND form, with the level keys of L1
  have hL2 := encrypts_leveledEval P (Cc.toNANDForm hC).layerNAND
    (DAGCircuit.layerNAND_isNANDForm _ hNF) (DAGCircuit.layerNAND_isLayered _)
    (by rw [DAGCircuit.layerNAND_depth]; exact hdepth) (fun e => (Regev.keygen P.lwe χ (rgs e)).2)
    _ (P.lwe.samples * B) (P.lwe.samples * B) (fun d j => encrypts_levelKey P χ B hχ rgs R d j)
    (litInput x) _ hlit hin hsep
  rw [DAGCircuit.layerNAND_eval _ hNF, DAGCircuit.toNANDForm_eval] at hL2
  have hlev : (⟨(Cc.toNANDForm hC).depth, Nat.lt_succ_of_le hdepth⟩ : Fin (L + 1)) =
      ⟨(Cc.toNANDForm hC).layerNAND.depth,
        Nat.lt_succ_of_le (by rw [DAGCircuit.layerNAND_depth]; exact hdepth)⟩ :=
    Fin.ext (DAGCircuit.layerNAND_depth _).symm
  rw [hlev]
  refine decrypt_of_encrypts P _ _ _ _ hL2 ?_
  rcases max_cases (P.lwe.samples * B) (bootNoise P (P.lwe.samples * B)) with ⟨hm, _⟩ | ⟨hm, _⟩
  · rw [hm]; exact hin
  · rw [hm]; exact hsep

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
