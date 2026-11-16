/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.ZeroKnowledge.EncodingMachines
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
            (true && coe && projection)
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
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Polynomial-time inputs for bit oblivious transfers

The machines here read the generic layout `⟨1^n, ⟨input, ⟨coins, 1^j⟩⟩⟩`. They
compute the two candidate coin bits and the input's quotient-indexed choice bit used
by bitwise oblivious transfers in [PS10, Protocol 162.6]. Their polynomial-time
contracts include arbitrary, malformed layouts and short coin and input words.

## Main definitions

* `otInputA`: the two coin bits at offsets `inA(n) n + j` and `(S(n) + inA(n)) n + j`.
* `otInputB`: the input bit at offset `j / n`, with the total division convention at zero.

## Main results

* `polyTimeComputable_otInputA`, `polyTimeComputable_otInputB`: both machines are polynomial-time.
* `otInputA_layout`, `otInputB_layout`: their equations on canonical call-input layouts.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Protocol 162.6.
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTInputs

open Complexity Turing TCSlib.Cryptography EncodingMachines

/-- The two-bit call-input machine reads `n = |fst z|`,
`r = fst (snd (snd z))`, and `j = |snd (snd (snd z))|`, and returns
`[r[inA(n) n + j], r[(S(n) + inA(n)) n + j]]`, with missing bits `false`.
[PS10, Protocol 162.6] -/
def otInputA (inA sizeBound : PolyExpr) (z : List Bool) : List Bool :=
  [(pairFstD (pairSndD (pairSndD z))).getD
      (inA.eval (pairFstD z).length * (pairFstD z).length +
        (pairSndD (pairSndD (pairSndD z))).length) false,
    (pairFstD (pairSndD (pairSndD z))).getD
      ((sizeBound.eval (pairFstD z).length + inA.eval (pairFstD z).length) *
        (pairFstD z).length + (pairSndD (pairSndD (pairSndD z))).length) false]

/-- `otInputA inA S z` is the two defaulted coin bits at offsets
`inA(|fst z|) |fst z| + |snd³ z|` and `(S(|fst z|) + inA(|fst z|)) |fst z| + |snd³ z|`. -/
theorem otInputA_eq (inA sizeBound : PolyExpr) (z : List Bool) :
    otInputA inA sizeBound z =
      [(pairFstD (pairSndD (pairSndD z))).getD
          (inA.eval (pairFstD z).length * (pairFstD z).length +
            (pairSndD (pairSndD (pairSndD z))).length) false,
        (pairFstD (pairSndD (pairSndD z))).getD
          ((sizeBound.eval (pairFstD z).length + inA.eval (pairFstD z).length) *
            (pairFstD z).length + (pairSndD (pairSndD (pairSndD z))).length) false] := rfl

/-- `otInputA inA S ⟨1^n, ⟨x, ⟨r, 1^j⟩⟩⟩` returns the coin bits at offsets
`inA(n) n + j` and `(S(n) + inA(n)) n + j`, defaulting to `false`. -/
theorem otInputA_layout (inA sizeBound : PolyExpr) (n j : ℕ) (x r : List Bool) :
    otInputA inA sizeBound (pairEncode (List.replicate n true)
      (pairEncode x (pairEncode r (List.replicate j true)))) =
      [r.getD (inA.eval n * n + j) false,
        r.getD ((sizeBound.eval n + inA.eval n) * n + j) false] := by
  rw [otInputA_eq]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]

/-- For polynomial expressions `inA` and `S`, the two-bit input machine
`otInputA inA S` is polynomial-time on every string. [PS10, Protocol 162.6]

**Proof sketch.** Project the parameter, coin word and call index. Compute both offsets
with the existing unary polynomial-evaluation, addition and multiplication machines.
Extract one defaulted coin bit at each offset, and concatenate the singleton words. -/
theorem polyTimeComputable_otInputA (inA sizeBound : PolyExpr) :
    PolyTimeComputable (otInputA inA sizeBound) := by
  have hn := unaryLength_poly polyTimeComputable_pairFstD
  have htail := polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
  have hj := unaryLength_poly (polyTimeComputable_pairSndD.comp htail)
  have hr := polyTimeComputable_pairFstD.comp htail
  have hA := unaryPolyOf_poly inA hn
  have hS := unaryPolyOf_poly sizeBound hn
  have h₀ := getBit_poly hr (unaryAdd_poly (unaryMul_poly hA hn) hj)
  have h₁ := getBit_poly hr (unaryAdd_poly (unaryMul_poly (unaryAdd_poly hS hA) hn) hj)
  exact (h₀.append h₁).congr fun z => rfl

/-- The one-bit choice-input machine reads `n = |fst z|`, `y = fst (snd z)`,
and `j = |snd (snd (snd z))|`, and returns `[y.getD (j / n) false]`.
Division is total, so malformed layouts and `n = 0` are included.
[PS10, Protocol 162.6] -/
def otInputB (z : List Bool) : List Bool :=
  [(pairFstD (pairSndD z)).getD
    ((pairSndD (pairSndD (pairSndD z))).length / (pairFstD z).length) false]

/-- `otInputB z = [fst(snd z).getD (|snd³ z| / |fst z|) false]`. -/
theorem otInputB_eq (z : List Bool) :
    otInputB z = [(pairFstD (pairSndD z)).getD
      ((pairSndD (pairSndD (pairSndD z))).length / (pairFstD z).length) false] := rfl

/-- `otInputB ⟨1^n, ⟨y, ⟨r, 1^j⟩⟩⟩ = [y.getD (j / n) false]`, including
short `y` and zero `n`. -/
theorem otInputB_layout (n j : ℕ) (y r : List Bool) :
    otInputB (pairEncode (List.replicate n true)
      (pairEncode y (pairEncode r (List.replicate j true)))) =
      [y.getD (j / n) false] := by
  rw [otInputB_eq]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]

/-- The one-bit choice-input machine `otInputB` is polynomial-time on every string,
including the zero-parameter case. [PS10, Protocol 162.6]

**Proof sketch.** Read the parameter and call-index lengths in unary, reuse the public
unary division machine and its quotient equation, and extract the defaulted input bit. -/
theorem polyTimeComputable_otInputB : PolyTimeComputable otInputB := by
  have hn := unaryLength_poly polyTimeComputable_pairFstD
  have htail := polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
  have hj := unaryLength_poly (polyTimeComputable_pairSndD.comp htail)
  have hy := polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hquot : PolyTimeComputable fun z => List.replicate
      ((pairSndD (pairSndD (pairSndD z))).length / (pairFstD z).length) true :=
    (divNum_poly hj hn).congr fun z => by
      simp only [divNum_eq, Function.comp_apply]
  exact (getBit_poly hy hquot).congr fun z => rfl

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTInputs
