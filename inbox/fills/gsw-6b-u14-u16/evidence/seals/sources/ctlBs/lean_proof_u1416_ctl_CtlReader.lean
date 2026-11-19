import Lean
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Leveled
/- DLC-SEAL lean_proof_u1416_ctl_CtlReader: whole-file closure seal of `lean_proof/u1416/ctl/CtlReader.lean`, variant B (PolyExpr.eval sealed), strict. -/
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
  Lean.logInfo m!"DLC-SEAL lean_proof_u1416_ctl_CtlReader: sealed={sealed.size} (already irreducible {already}) abbrev-excluded={abbrevs} excluded={excluded} coe-excluded={coeExcl.size} {coeExcl.toList}"


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
