import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.FakeSimulator
import Lean
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut requested := 0
  let mut excluded := 0
  for (name, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let home := env.header.moduleNames[idx.toNat]!
      if home.toString.startsWith "TCSlib." then
        if let .defnInfo d := ci then
          let status ← liftCoreM <| Lean.getReducibilityStatus name
          let matcher := Lean.Meta.isMatcherCore env name
          let rec body : Nat → Expr → Expr
            | 0, e => e
            | fuel+1, .lam _ _ b _ => body fuel b
            | fuel+1, .letE _ _ v b _ => body fuel (b.instantiate1 v)
            | _, e => e
          let ty := d.type.getForallBody.getAppFn.constName?
          let val := body 64 d.value
          let coe := ty == some `CoeFun || ty == some `Coe
          let map := if val.getAppArgs.isEmpty then val else val.getAppArgs.back!
          let projection := match (body 64 map).getAppFn with
            | .proj .. => true
            | .const n _ => env.isProjectionFn n
            | _ => false
          let isNotation : Bool := (name == `Complexity.PolyExpr.eval && false) ||
            (false && coe && projection)
          if isNotation || (status == .reducible && !matcher) then
            excluded := excluded + 1
            logInfo m!"EXCLUDED\t{home}\t{name}"
          else
            let id := mkIdent name
            if status != .irreducible then
              elabCommand (← `(command| attribute [local irreducible] $id:ident))
            let installed ← liftCoreM <| Lean.getReducibilityStatus name
            unless installed == .irreducible do
              throwError "seal not installed: {name}"
            requested := requested + 1
            logInfo m!"SEALED\t{home}\t{name}"
  logInfo m!"SEAL_COUNTS requested={requested} excluded={excluded}"

set_option maxHeartbeats 0
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Audit
open Complexity Turing BoolCircuit
variable
    (E₁ : List Bool → List Bool)
    (E₂ : List Bool → List Bool)
    (E₁_poly : PolyTimeComputable E₁)
    (E₂_poly : PolyTimeComputable E₂)
    (bound : PolyExpr)
    (inputs : PolyExpr)
    (inA : PolyExpr)
    (inB : PolyExpr)
    (outLen : PolyExpr)
    (gen : List Bool → List Bool)
    (gen_poly : PolyTimeComputable gen)
    (circuit : ∀ n, DAGCircuit (inputs.eval n))
    (output : ∀ n, Fin (outLen.eval n) → ℕ)
    (shape : ∀ n, gen (List.replicate n true) = pairEncode (circuit n).encode
    (BinArith.encWords (List.ofFn fun j => encodeNat (output n j))))
    (input_range : ∀ n, inA.eval n + inB.eval n ≤ inputs.eval n)
    (output_lt : ∀ n j, output n j < (circuit n).size)
    (fanin : ∀ n (i : Fin (circuit n).gates.length), ((circuit n).gates[i]).args.length ≤ 2)
    (seed : ∀ n, List Bool → GarbleSeed (circuit n) (Fin n → Bool)
    ((Fin n → Bool) × (Fin n → Bool)))
    (key : ∀ n r (v : ℕ), v < (circuit n).size → ∀ b,
    keyAt (circuit n) (seed n r) v b = fun t : Fin n =>
      r.getD ((b.toNat * bound.eval n + v) * n + t) false)
    (nonce₀ : ∀ n r (i : Fin (circuit n).gates.length) a t, ((seed n r).2.1 i a).1 t =
    r.getD (2 * bound.eval n * n +
      (4 * i + (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) * (2 * n) + t) false)
    (nonce₁ : ∀ n r (i : Fin (circuit n).gates.length) a t, ((seed n r).2.1 i a).2 t =
    r.getD (2 * bound.eval n * n +
      (4 * i + (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) * (2 * n) + n + t) false)
    (permutation : ∀ n r (i : Fin (circuit n).gates.length) a t,
    (seed n r).2.2 i a t = xor (a t) (r.getD (10 * bound.eval n * n + 2 * i + t) false))

example (n : ℕ) (r f : List Bool) :
    messageAt (Data.make
      (E₁ := E₁)
      (E₂ := E₂)
      (E₁_poly := E₁_poly)
      (E₂_poly := E₂_poly)
      (bound := bound)
      (inputs := inputs)
      (inA := inA)
      (inB := inB)
      (outLen := outLen)
      (gen := gen)
      (gen_poly := gen_poly)
      (circuit := circuit)
      (output := output)
      (shape := shape)
      (input_range := input_range)
      (output_lt := output_lt)
      (fanin := fanin)
      (seed := seed)
      (key := key)
      (nonce₀ := nonce₀)
      (nonce₁ := nonce₁)
      (permutation := permutation)) n r f =
      FakeObjects.message (nestedSpecial E₁ E₂ n) (circuit n) (seed n r)
        (inA.eval n) (outLen.eval n) (output n) (fun j => f.getD j false) :=
  Data.make_messageAt
    (E₁ := E₁)
    (E₂ := E₂)
    (E₁_poly := E₁_poly)
    (E₂_poly := E₂_poly)
    (bound := bound)
    (inputs := inputs)
    (inA := inA)
    (inB := inB)
    (outLen := outLen)
    (gen := gen)
    (gen_poly := gen_poly)
    (circuit := circuit)
    (output := output)
    (shape := shape)
    (input_range := input_range)
    (output_lt := output_lt)
    (fanin := fanin)
    (seed := seed)
    (key := key)
    (nonce₀ := nonce₀)
    (nonce₁ := nonce₁)
    (permutation := permutation)
    n r f
end TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator.Audit
