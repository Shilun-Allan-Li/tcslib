/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import Lean
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Branching
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.DecryptFormula
import TCSlib.Complexity.CircuitComplexity.NANDForm
/- DLC-SEAL lean_proof_u1416_base_BootstrapBase: whole-file closure seal of `lean_proof/u1416/base/BootstrapBase.lean`, variant B (PolyExpr.eval sealed), strict. -/
/-- Strip leading lambdas (seal harness). -/
partial def dlcStripLam : Lean.Expr → Lean.Expr
  | .lam _ _ b _ => dlcStripLam b
  | e => e

set_option maxHeartbeats 0 in
run_cmd do
  let env ← Lean.getEnv
  let excl : List Lean.Name := []
  let coeOpen : Bool := false
  let coeClasses : List Lean.Name := [`CoeFun, `Coe, `CoeSort, `CoeOut, `CoeTail, `CoeHead,
    `CoeTC, `CoeHTCT, `CoeDep]
  let mut sealed : Array Lean.Name := #[]
  let mut abbrevs : Nat := 0
  let mut already : Nat := 0
  let mut excluded : Nat := 0
  let mut coeExcl : Array Lean.Name := #[]
  for (n, ci) in env.constants.map₁.toList do
    let some mi := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[mi.toNat]!
    unless (`TCSlib).isPrefixOf m do continue
    let .defnInfo d := ci | continue
    if excl.contains n then
      excluded := excluded + 1
      continue
    if coeOpen && Lean.Meta.isInstanceCore env n then
      let isCoeCls := match d.type.getForallBody.getAppFn.constName? with
        | some c => coeClasses.contains c
        | none => false
      if isCoeCls then
        let body := dlcStripLam d.value
        let args := body.getAppArgs
        let projArg := match args.back? with
          | some a => match (dlcStripLam a).getAppFn.constName? with
            | some p => (env.getProjectionFnInfo? p).isSome
            | none => false
          | none => false
        if projArg then
          coeExcl := coeExcl.push n
          continue
    match d.hints with
    | .abbrev =>
      abbrevs := abbrevs + 1
      continue
    | _ => pure ()
    let st ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    if st == .irreducible then
      already := already + 1
      sealed := sealed.push n
      continue
    Lean.Elab.Command.elabCommand (← `(command| attribute [local irreducible] $(Lean.mkIdent n):ident))
    let st' ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    unless st' == .irreducible do throwError "DLC-SEAL: not sealed {n}"
    sealed := sealed.push n
  Lean.modifyEnv fun cur =>
    Lean.Meta.globalInstanceExtension.modifyState cur fun s => sealed.foldl (fun s n => s.erase n) s
  let env' ← Lean.getEnv
  for n in sealed do
    if Lean.Meta.isGlobalInstance env' n then throwError "DLC-SEAL: instance unfolding kept for {n}"
  Lean.logInfo m!"DLC-SEAL lean_proof_u1416_base_BootstrapBase: sealed={sealed.size} (already irreducible {already}) abbrev-excluded={abbrevs} excluded={excluded} coe-excluded={coeExcl.size} {coeExcl.toList}"


set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# NAND bootstrapping and pure fully homomorphic evaluation (GSW)

## Main definitions

* `PublicKey`, `Secret`, `Coins`, `KeySeed`: reducible names for the phase-5 types of a public
  key, a secret, a binary coin matrix and a key-generation seed.
* `bootNoise`: the bootstrapped noise `4^(decDepth P + 1)·(2·(N·β))`.
* `bootNAND`: one bootstrapped NAND gate, the formula evaluation of `nandFormula` on the
  evaluation key.
* `bootGate`: `bootNAND` on a gate's arguments, fan-in 1 padded to `(a, a)` and fan-in 0 to
  `(G, G)`.
* `fheEval`: a NAND-form circuit run by the host `runWith` (registry row H19) with `bootGate`.
* `fheEvalCircuit`: any fan-in-2 circuit, through the NAND conversion `toNANDForm`.
* `evalKey`: the evaluation key, encryptions under the user's own `pk` of the key bits.

## Main results

* `encrypts_bootNAND` (G9): bootstrapped NAND in the key-switching form.
* `decrypt_fheEval` (G10), `decrypt_fheEvalCircuit` (G18): pure FHE correctness for circuits
  of every depth.
* `encrypts_evalKey` (G11): evaluation-key noise `m·B`, a proved citation of phase 5's
  `encrypts_encrypt`.
* `decrypt_keygen_fheEvalCircuit` (G12): correctness for honest keys and every circuit.
* `bootNoise_le` (G13): `bootNoise P β ≤ 4^33·N^19·(ℓ + ⌈log₂ N⌉ + 3)^4·(2·β)`.

The targets G9, G10, G12, G13 and G18 are admitted; G11 is proved.

**Compactness** [BV14, Def 2.12, p008-b001; BV11, Def 3.4, p014-b001; Lemma 3.3, p015-b001]
holds by typing: `fheEval` and `fheEvalCircuit` return a `Ciphertext P`, an `(n+1) × N` matrix,
whatever the circuit, so the decryption circuit is independent of the evaluated function. No
separate theorem states it (P6-Q10).

## References

* [BV14] Z. Brakerski, V. Vaikuntanathan, *Lattice-Based FHE as Secure as PKE*, ITCS 2014;
  IACR ePrint 2013/541: Def 2.12, Def 2.13, Thm 2.14, Thm 3.7, Lemma 4.4.
* [BV11] Z. Brakerski, V. Vaikuntanathan, *Efficient Fully Homomorphic Encryption from
  (Standard) LWE*, FOCS 2011 full version; IACR ePrint 2011/344: Defs 3.4–3.5, Thms 3.1–3.2,
  Def 3.8, Lemma 3.3.

**Deviations.** Bootstrapping is NAND only (P6-Q9): a circuit is evaluated in NAND form, every
gate by the augmented formula of [BV14, Def 2.13]. A NAND gate of fan-in 1 is padded to
`(a, a)` (`NAND(a, a) = ¬a`) and one of fan-in 0 to `(G, G)` (`G` encrypts `1` with zero noise
and `NAND(1, 1) = 0 = NAND()`) (r3 §H3.9). The evaluation key holds public-key encryptions under
the user's own `pk` (P6-Q8; [BV11, Def 3.8]'s `{Enc_pk(sk[i])}_i`), not [BV14, Lemma 4.4]'s
secret-key encryptions, which costs a factor `m` in the noise. Noise and correctness are worst
case for every key and coin, not with overwhelming probability [BV14, Thm 3.7].
-/

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

open BoolCircuit
open Encryption.PublicKey

/-! ### Key and coin types -/

/-- A GSW public key: an LWE public key `(A, b)` with `A ∈ Z_q^{m×n}` and `b ∈ Z_q^m`, the type
of `Regev.keygen`'s first component and of `encrypt`'s key. Reducible notation. -/
abbrev PublicKey (P : Parameters) : Type :=
  Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
    (Fin P.lwe.samples → ZMod P.lwe.modulus)

/-- `PublicKey P` is `Matrix (Fin m) (Fin n) (ZMod q) × (Fin m → ZMod q)`. -/
theorem PublicKey_eq (P : Parameters) :
    PublicKey P = (Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus)) := rfl

/-- A GSW secret `s ∈ Z_q^n`, the type of `Regev.keygen`'s second component. Reducible
notation. -/
abbrev Secret (P : Parameters) : Type :=
  Fin P.lwe.dimension → ZMod P.lwe.modulus

/-- `Secret P` is `Fin n → ZMod q`. -/
theorem Secret_eq (P : Parameters) : Secret P = (Fin P.lwe.dimension → ZMod P.lwe.modulus) :=
  rfl

/-- The binary coin matrix `R ∈ {0,1}^{m×N}` of one public-key GSW encryption (`encrypt`).
Reducible notation. -/
abbrev Coins (P : Parameters) : Type :=
  Matrix (Fin P.lwe.samples) (Fin P.columns) Bool

/-- `Coins P` is `Matrix (Fin m) (Fin N) Bool`. -/
theorem Coins_eq (P : Parameters) : Coins P = Matrix (Fin P.lwe.samples) (Fin P.columns) Bool :=
  rfl

/-- A key-generation seed: the public matrix, the secret and one noise seed per sample, the
seed type of `Regev.keygen P.lwe χ`. Reducible notation. -/
abbrev KeySeed (P : Parameters) (χ : LWE.Noise) : Type :=
  Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
    ((Fin P.lwe.dimension → ZMod P.lwe.modulus) × (Fin P.lwe.samples → χ.Coins))

/-- `KeySeed P χ` is `Matrix (Fin m) (Fin n) (ZMod q) × ((Fin n → ZMod q) × (Fin m → χ.Coins))`. -/
theorem KeySeed_eq (P : Parameters) (χ : LWE.Noise) :
    KeySeed P χ = (Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      ((Fin P.lwe.dimension → ZMod P.lwe.modulus) × (Fin P.lwe.samples → χ.Coins))) := rfl

/-! ### Bootstrapping -/

/-- The **bootstrapped noise** for evaluation-key noise `β`:
`bootNoise P β = 4^(decDepth P + 1)·(2·(N·β))`, the noise of `homEvalFormula` on the augmented
NAND formula, whose depth is at most `decDepth P + 1` (r3 §H6) [BV14, Lemma 4.4, p019-b001].
It does not depend on the noise of the ciphertexts being bootstrapped. -/
def bootNoise (P : Parameters) (β : ℕ) : ℕ :=
  4 ^ (decDepth P + 1) * (2 * (P.columns * β))

/-- `bootNoise P β` is `4 ^ (decDepth P + 1) * (2 * (P.columns * β))`. -/
theorem bootNoise_eq (P : Parameters) (β : ℕ) :
    bootNoise P β = 4 ^ (decDepth P + 1) * (2 * (P.columns * β)) := rfl

/-- **One bootstrapped NAND gate** [BV14, Def 2.13, p008-b002, Thm 2.14, p008-b003; Lemma 4.4,
p019-b001]: homomorphically evaluate the augmented formula `f_{C₁,C₂}` on the evaluation key,
`bootNAND P evk C₁ C₂ = homEvalFormula P (nandFormula P C₁ C₂) evk`. Computable. -/
def bootNAND (P : Parameters) (evk : Fin P.columns → Ciphertext P) (C₁ C₂ : Ciphertext P) :
    Ciphertext P :=
  homEvalFormula P (nandFormula P C₁ C₂) evk

/-- `bootNAND P evk C₁ C₂` is `homEvalFormula P (nandFormula P C₁ C₂) evk`. -/
theorem bootNAND_eq (P : Parameters) (evk : Fin P.columns → Ciphertext P)
    (C₁ C₂ : Ciphertext P) : bootNAND P evk C₁ C₂ = homEvalFormula P (nandFormula P C₁ C₂) evk :=
  rfl

/-- The **bootstrapped gate function** of `fheEval`: a gate is read as a NAND gate on its first
two arguments' ciphertexts (`cts.getD a 0`), fan-in 1 padded to `(a, a)` and fan-in 0 to
`(G, G)` (r3 §H3.9, disclosed). The gate's kind is not read: on a NAND-form circuit every gate
is a `¬` gate of fan-in at most two (`DAGGate.IsNAND`). It is the gate function given to the
host `runWith` (H19). Computable. -/
def bootGate (P : Parameters) (evk : Fin P.columns → Ciphertext P) (g : DAGGate)
    (cts : List (Ciphertext P)) : Ciphertext P :=
  match g.args with
  | [] => bootNAND P evk (gadget P) (gadget P)
  | [a] => bootNAND P evk (cts.getD a 0) (cts.getD a 0)
  | a :: b :: _ => bootNAND P evk (cts.getD a 0) (cts.getD b 0)

/-- A gate of fan-in 0 is bootstrapped on `(G, G)`:
`g.args = [] → bootGate P evk g cts = bootNAND P evk (gadget P) (gadget P)`. -/
theorem bootGate_of_args_eq_nil (P : Parameters) (evk : Fin P.columns → Ciphertext P)
    (g : DAGGate) (cts : List (Ciphertext P)) (h : g.args = []) :
    bootGate P evk g cts = bootNAND P evk (gadget P) (gadget P) := by
  unfold bootGate
  rw [h]

/-- A gate of fan-in 1 is bootstrapped on `(a, a)`:
`g.args = [a] → bootGate P evk g cts = bootNAND P evk (cts.getD a 0) (cts.getD a 0)`. -/
theorem bootGate_of_args_eq_singleton (P : Parameters) (evk : Fin P.columns → Ciphertext P)
    (g : DAGGate) (cts : List (Ciphertext P)) (a : ℕ) (h : g.args = [a]) :
    bootGate P evk g cts = bootNAND P evk (cts.getD a 0) (cts.getD a 0) := by
  unfold bootGate
  rw [h]

/-- A gate of fan-in at least 2 is bootstrapped on its first two arguments:
`g.args = a :: b :: l → bootGate P evk g cts = bootNAND P evk (cts.getD a 0) (cts.getD b 0)`. -/
theorem bootGate_of_args_eq_cons_cons (P : Parameters) (evk : Fin P.columns → Ciphertext P)
    (g : DAGGate) (cts : List (Ciphertext P)) (a b : ℕ) (l : List ℕ) (h : g.args = a :: b :: l) :
    bootGate P evk g cts = bootNAND P evk (cts.getD a 0) (cts.getD b 0) := by
  unfold bootGate
  rw [h]

/-- **Pure fully homomorphic evaluation** of a NAND-form circuit [BV14, Thm 2.14 second part,
p008-b003; BV11, Thm 3.2, Def 3.5, p015-b001, p014-b001]: run the host `runWith` (H19) over the
gates with the gate function `bootGate P evk`, from the input ciphertexts, and read the output
vertex (the noiseless `0` out of range):
`fheEval P evk Cc cts = (runWith (bootGate P evk) Cc.gates (List.ofFn cts)).getD Cc.output 0`.
Computable. **Compactness by typing**: the result is a `Ciphertext P` whatever `Cc`. -/
def fheEval (P : Parameters) (evk : Fin P.columns → Ciphertext P) {k : ℕ} (Cc : DAGCircuit k)
    (cts : Fin k → Ciphertext P) : Ciphertext P :=
  (runWith (bootGate P evk) Cc.gates (List.ofFn cts)).getD Cc.output 0

/-- `fheEval P evk Cc cts` is `(runWith (bootGate P evk) Cc.gates (List.ofFn cts)).getD
Cc.output 0`. -/
theorem fheEval_eq (P : Parameters) (evk : Fin P.columns → Ciphertext P) {k : ℕ}
    (Cc : DAGCircuit k) (cts : Fin k → Ciphertext P) :
    fheEval P evk Cc cts = (runWith (bootGate P evk) Cc.gates (List.ofFn cts)).getD Cc.output 0 :=
  rfl

/-- **Pure fully homomorphic evaluation of any fan-in-2 circuit** [BV14, Thm 2.14, p008-b003;
BV11, Def 3.5, p014-b001]: `fheEval` on the NAND form of `Cc` (6a's conversion
`DAGCircuit.toNANDForm`), `fheEvalCircuit P evk Cc hC cts = fheEval P evk (Cc.toNANDForm hC)
cts`. Computable. **Compactness by typing**: the result is a `Ciphertext P` whatever `Cc`. -/
def fheEvalCircuit (P : Parameters) (evk : Fin P.columns → Ciphertext P) {k : ℕ}
    (Cc : DAGCircuit k) (hC : ∀ g ∈ Cc.gates, g.args.length ≤ 2) (cts : Fin k → Ciphertext P) :
    Ciphertext P :=
  fheEval P evk (Cc.toNANDForm hC) cts

/-- `fheEvalCircuit P evk Cc hC cts` is `fheEval P evk (Cc.toNANDForm hC) cts`. -/
theorem fheEvalCircuit_eq (P : Parameters) (evk : Fin P.columns → Ciphertext P) {k : ℕ}
    (Cc : DAGCircuit k) (hC : ∀ g ∈ Cc.gates, g.args.length ≤ 2) (cts : Fin k → Ciphertext P) :
    fheEvalCircuit P evk Cc hC cts = fheEval P evk (Cc.toNANDForm hC) cts := rfl

/-- **The evaluation key** (P6-Q8) [BV11, Def 3.8, p015-b001: `{Enc_pk(sk[i])}_i`; BV14,
Lemma 4.4, p019-b001]: the public-key encryptions under the user's own `pk` of the `N` key bits
of `s`, `evalKey P pk s R i = encrypt P pk (keyBits P s i) (R i)`, one coin matrix per bit.
Deviation: BV14's Lemma 4.4 uses secret-key encryptions. -/
def evalKey (P : Parameters) (pk : PublicKey P) (s : Secret P) (R : Fin P.columns → Coins P)
    (i : Fin P.columns) : Ciphertext P :=
  encrypt P pk (keyBits P s i) (R i)

/-- `evalKey P pk s R i` is `encrypt P pk (keyBits P s i) (R i)`. -/
theorem evalKey_eq (P : Parameters) (pk : PublicKey P) (s : Secret P)
    (R : Fin P.columns → Coins P) (i : Fin P.columns) :
    evalKey P pk s R i = encrypt P pk (keyBits P s i) (R i) := rfl

/-! ### Targets G9–G13, G18 -/

/-- **G9. Bootstrapped NAND, key-switching form.** If every evaluation-key ciphertext `evk i`
encrypts the key bit `keyBits P s i` under the key vector `t'` with noise at most `βk`, then for
**all** ciphertexts `C₁`, `C₂` the bootstrapped gate encrypts, under `t'`, the NAND of their
decryptions under `s`, with noise at most `bootNoise P βk`:
`Encrypts P t' (!(decrypt P s C₁ && decrypt P s C₂)).toNat (bootNoise P βk)
(bootNAND P evk C₁ C₂)` [BV14, Thm 2.14, p008-b003; Lemma 4.4, p019-b001; BV11, Thm 3.1,
p015-b001]. No hypothesis on `C₁`, `C₂`. Pure FHE takes `t' = secretVector P s`; the leveled
scheme takes `s = s_{d−1}` and `t' = t_d`. Deviation: worst case; BV14's coordinate `1` is
`σ 0` here (`homEvalFormula`).

**Proof sketch.** `bootNAND_eq`, then G3 (`encrypts_homEvalFormula`) for the formula
`nandFormula P C₁ C₂` on `N` inputs (instance `Parameters.neZero_columns`) with fan-in at most
two (`maxFanin_nandFormula_le`, G8) and inputs `evk i` encrypting `keyBits P s i` (`hk`). Its
message is `(nandFormula P C₁ C₂).eval (keyBits P s)`, which is
`!(decrypt P s C₁ && decrypt P s C₂)` by G7 (`nandFormula_eval`). Its noise
`4^depth·(2·(N·βk))` is at most `bootNoise P βk` by `depth_nandFormula_le` (G8),
`Nat.pow_le_pow_right` and `bootNoise_eq`, through `Encrypts.mono`. -/
theorem encrypts_bootNAND (P : Parameters)
    {t' : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus} (s : Secret P) (βk : ℕ)
    (evk : Fin P.columns → Ciphertext P)
    (hk : ∀ i, Encrypts P t' ((keyBits P s i).toNat : ℤ) βk (evk i)) (C₁ C₂ : Ciphertext P) :
    Encrypts P t' ((!(decrypt P s C₁ && decrypt P s C₂)).toNat : ℤ) (bootNoise P βk)
      (bootNAND P evk C₁ C₂) := by
  sorry

/-- **G10. Pure-FHE correctness for NAND-form circuits of every depth.** Let `evk` encrypt
the key bits of `s` under `t = secretVector P s` with noise at most `βk`, and the inputs
`cts j` encrypt the bits `x j` with noise at most `βin`. If `2·(ℓ·βin) < ⌊q/2⌋` and
`2·(ℓ·bootNoise P βk) < ⌊q/2⌋`, then for every NAND-form circuit `Cc`, of any depth,
`decrypt P s (fheEval P evk Cc cts) = Cc.eval x` [BV14, Thm 2.14 second part, p008-b003; BV11,
Thm 3.2, Def 3.5, p015-b001, p014-b001]. Deviations: the padding of fan-in 1 to `(a, a)` and
of fan-in 0 to `(G, G)`; worst case.

**Proof sketch.** Apply the host lemma `runWith_rel` (H19) to `DAGGate.eval` from
`List.ofFn x` and `bootGate P evk` from `List.ofFn cts`, with the vertex relation "the
ciphertext encrypts the vertex's value under `t` with noise at most `βin` (an input) or
`bootNoise P βk` (a gate)", as `eval_encrypts` does for phase 5. Inputs: `hin`. A gate `g`
(a NAND gate by `isNANDForm_iff`, `DAGGate.isNAND_iff`): its arguments are earlier vertices
(`Cc.args_lt`), so they decrypt to their values by `decrypt_of_encrypts` with `hβin` or
`hboot`; the padded `G` decrypts to `true` (`encrypts_gadget`, noise `0`, `q ≥ 2`). By the
three case readers `bootGate_of_args_eq_nil`/`_singleton`/`_cons_cons` and G9
(`encrypts_bootNAND`, `t' = t`), the gate's ciphertext encrypts `!(d₁ && d₂)` with noise
`bootNoise P βk`, which is the gate's value by `DAGGate.eval_of_isNAND` (N1): `NAND() = false
= NAND(1, 1)` and `NAND(a) = ¬a = NAND(a, a)`. The output vertex is in range (`Cc.output_lt`);
`decrypt_of_encrypts` with `hβin` or `hboot` and `DAGCircuit.eval_eq`, `values_eq` finish,
through `fheEval_eq`. -/
theorem decrypt_fheEval (P : Parameters) {k : ℕ} (Cc : DAGCircuit k) (hNAND : Cc.IsNANDForm)
    (s : Secret P) (evk : Fin P.columns → Ciphertext P) (βk βin : ℕ)
    (hevk : ∀ i, Encrypts P (secretVector P s) ((keyBits P s i).toNat : ℤ) βk (evk i))
    (x : Fin k → Bool) (cts : Fin k → Ciphertext P)
    (hin : ∀ j, Encrypts P (secretVector P s) ((x j).toNat : ℤ) βin (cts j))
    (hβin : 2 * (P.width * βin) < P.lwe.modulus / 2)
    (hboot : 2 * (P.width * bootNoise P βk) < P.lwe.modulus / 2) :
    decrypt P s (fheEval P evk Cc cts) = Cc.eval x := by
  sorry

/-- **G18. Pure-FHE correctness for every fan-in-2 circuit**, through the NAND conversion:
under the hypotheses of G10, for every circuit `Cc` whose gates have at most two arguments,
`decrypt P s (fheEvalCircuit P evk Cc hC cts) = Cc.eval x` [BV14, Thm 2.14, p008-b003; BV11,
Def 3.5, p014-b001]. Deviation: NAND only (P6-Q9), through 6a's conversion.

**Proof sketch.** `fheEvalCircuit_eq`; G10 (`decrypt_fheEval`) for `Cc.toNANDForm hC`, which
is in NAND form (`DAGCircuit.toNANDForm_isNANDForm`, N4) and computes `Cc.eval`
(`DAGCircuit.toNANDForm_eval`, N3). -/
theorem decrypt_fheEvalCircuit (P : Parameters) {k : ℕ} (Cc : DAGCircuit k)
    (hC : ∀ g ∈ Cc.gates, g.args.length ≤ 2) (s : Secret P)
    (evk : Fin P.columns → Ciphertext P) (βk βin : ℕ)
    (hevk : ∀ i, Encrypts P (secretVector P s) ((keyBits P s i).toNat : ℤ) βk (evk i))
    (x : Fin k → Bool) (cts : Fin k → Ciphertext P)
    (hin : ∀ j, Encrypts P (secretVector P s) ((x j).toNat : ℤ) βin (cts j))
    (hβin : 2 * (P.width * βin) < P.lwe.modulus / 2)
    (hboot : 2 * (P.width * bootNoise P βk) < P.lwe.modulus / 2) :
    decrypt P s (fheEvalCircuit P evk Cc hC cts) = Cc.eval x := by
  sorry

/-- **G11. Evaluation-key noise.** For an honest public key `(A, A s + e)` with errors of
magnitude at most `B`, every evaluation-key ciphertext encrypts its key bit under
`t = secretVector P s` with noise at most `m·B`:
`Encrypts P (secretVector P s) (keyBits P s i).toNat (P.lwe.samples * B)
(evalKey P (A, LWE.noisyValues P.lwe A s e) s R i)` [BV11, Def 3.8, p015-b001; BV14, Lemma 4.4,
p019-b001]. A citation, proved: it is phase 5's `encrypts_encrypt` read through `evalKey_eq`. -/
theorem encrypts_evalKey (P : Parameters)
    (A : Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus)) (s : Secret P)
    (e : Fin P.lwe.samples → ℤ) (B : ℕ) (he : ∀ i, (e i).natAbs ≤ B)
    (R : Fin P.columns → Coins P) (i : Fin P.columns) :
    Encrypts P (secretVector P s) ((keyBits P s i).toNat : ℤ) (P.lwe.samples * B)
      (evalKey P (A, LWE.noisyValues P.lwe A s e) s R i) := by
  rw [evalKey_eq]
  exact encrypts_encrypt P A s e B he (keyBits P s i) (R i)

/-- **G12. Correctness for honest keys and every circuit.** For a `B`-bounded noise law, every
key-generation seed, evaluation-key coins `R`, input bits `x` with encryption coins `R'`, and
every fan-in-2 circuit `Cc`, if `2·(ℓ·bootNoise P (m·B)) < ⌊q/2⌋` then the pure FHE evaluation
under the honest evaluation key decrypts to `Cc.eval x`:
`decrypt P sk (fheEvalCircuit P (evalKey P pk sk R) Cc hC fun j => encrypt P pk (x j) (R' j)) =
Cc.eval x` with `(pk, sk) = Regev.keygen P.lwe χ rg` [BV14, Thm 3.7, p016-b001, worst case and
any depth]. Deviation: worst case for every seed; the ratio condition is explicit.

**Proof sketch.** `Regev.keygen_fst`, `Regev.keygen_snd`, `LWE.sample_fst`, `LWE.sample_snd`
write the key as `(A, A s + e)` with `eᵢ = χ.sample(seedᵢ)` bounded by `B`
(`LWE.Noise.bounded_iff`). The inputs encrypt with noise `m·B` (`encrypts_keygen_encrypt`), and
the evaluation key with noise `m·B` (G11, `encrypts_evalKey`). Since `N ≥ 1`
(`Parameters.neZero_columns`), `m·B ≤ bootNoise P (m·B)` (`bootNoise_eq`), so `hsep` also gives
the input condition. Then G18 (`decrypt_fheEvalCircuit`). -/
theorem decrypt_keygen_fheEvalCircuit (P : Parameters) (χ : LWE.Noise) (rg : KeySeed P χ)
    (B : ℕ) (hχ : χ.Bounded B) (R : Fin P.columns → Coins P) {k : ℕ} (Cc : DAGCircuit k)
    (hC : ∀ g ∈ Cc.gates, g.args.length ≤ 2) (x : Fin k → Bool) (R' : Fin k → Coins P)
    (hsep : 2 * (P.width * bootNoise P (P.lwe.samples * B)) < P.lwe.modulus / 2) :
    decrypt P (Regev.keygen P.lwe χ rg).2
        (fheEvalCircuit P (evalKey P (Regev.keygen P.lwe χ rg).1 (Regev.keygen P.lwe χ rg).2 R)
          Cc hC fun j => encrypt P (Regev.keygen P.lwe χ rg).1 (x j) (R' j)) =
      Cc.eval x := by
  sorry

/-- **G13. Closed form of the bootstrapped noise.** For every noise bound `β`,
`bootNoise P β ≤ 4 ^ 33 * P.columns ^ 19 * (P.width + Nat.clog 2 P.columns + 3) ^ 4 * (2 * β)`:
polynomial in `N` and `ℓ`, with no factor exponential in `ℓ` (r3 §H3.3, §H6). Glue; the
constants of r3 G13 *(fix)* are settled here: `c₀ = 33`, `c₁ = 9`, `c₂ = 2`.

**Proof sketch.** `bootNoise_eq`. If `N = 0` both sides are `0`. Otherwise `decDepth_le` (G8)
gives `decDepth P + 1 ≤ 9a + 2b + 22` with `a = ⌈log₂ N⌉` and `b = ⌈log₂ X⌉`,
`X = ℓ + ⌈log₂ N⌉ + 3 ≥ 1`. For `y ≥ 1`, `2^⌈log₂ y⌉ < 2y` (`Nat.pow_pred_clog_lt_self` for
`y ≥ 2`; `Nat.clog_one_right` for `y = 1`), so `4^⌈log₂ y⌉ ≤ 4y²`. Hence
`4^(decDepth P + 1) ≤ 4^22·(4N²)^9·(4X²)^2 = 4^33·N^18·X^4` (`Nat.pow_le_pow_right`,
`Nat.pow_le_pow_left`, `pow_mul`), and multiplying by `2·(N·β)` gives the bound
(`Nat.mul_le_mul_right`, `ring_nf`). -/
theorem bootNoise_le (P : Parameters) (β : ℕ) :
    bootNoise P β ≤
      4 ^ 33 * P.columns ^ 19 * (P.width + Nat.clog 2 P.columns + 3) ^ 4 * (2 * β) := by
  sorry

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
