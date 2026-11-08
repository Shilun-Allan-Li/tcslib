/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Tactic.FinCases
import TCSlib.Complexity.CircuitComplexity.UniformTableauSpec
import TCSlib.Complexity.CircuitComplexity.Uniform

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The tableau emitter: the program

The counter program (`TCSlib.Complexity.TuringMachine.CounterProg`) that prints the description
`DAGCircuit.encode` of the uniform tableau circuit `Complexity.cfgTab M n z T` of a machine
`M` — the machine of [AB09, Remark 6.7] (the circuit of Thm 6.6 can be computed in
polynomial time).  Its input is `1ⁿ 0 1ᵀ 0 z`.

The program has eleven registers (`Complexity.UTab.rNC`, …) and follows the order of the
circuit's gates: it reads `n` (printing it in unary), `T`, then the hard-wired bits `z`
(printing a constant gate for each), and then runs the `T + 1` steps of the tableau, each
step being: for every work tape the cells `r = 0`, `1 … T − 1` (a loop), `T`,
`T + 1 … 2T − 1` (a loop), `2T`; the input positions `0`, the hard-wired ones (a loop), the
free ones (a loop) and the right end; and the snapshot.  Every instruction of the tableau
is printed by one *template* (`Complexity.UTab.tmpl`): a fixed list of print-a-bit /
print-a-register micro-operations, depending only on the kind of instruction and a few
boundary flags; the vertex numbers it prints are linear expressions in the registers
(`Complexity.UTab.SSrc.toLinE`).  Counters are kept in unary, every loop is a count-down
over a register, and no arithmetic beyond `±1` is used — a shape intended to make a
logarithmic-space version ([AB09, Remark 6.7], second half) straightforward (re-encoding the
counters in binary); no such version is proved here.

## Main definitions

* `Complexity.UTab.ER` — the register file as a record.
* `Complexity.UTab.Tpl`, `Complexity.UTab.tmpl` — templates.
* `Complexity.UTab.Lb`, `Complexity.UTab.prog` — the labels and the program.

## Main results

* `Complexity.UTab.flatMap_exec_sgOps` — a gate template prints the gate's code.
* `Complexity.UTab.goes_instr` — an instruction template prints its micro-operations and
  advances the instruction counters.
* `Complexity.UTab.goes_copy`, `Complexity.UTab.goes_clear` — the register macros.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§6.1, Theorem 6.6; §6.2, Remark 6.7.)
-/

namespace Complexity

namespace UTab

open Turing BoolCircuit CounterProg

/-! ## The register file -/

/-- The eleven registers of the emitter as a record. -/
@[ext]
structure ER where
  /-- `n`, the number of circuit inputs. -/
  nc : ℕ
  /-- `|z|`, the number of hard-wired bits. -/
  z : ℕ
  /-- `T`, the step budget. -/
  t : ℕ
  /-- The current instruction. -/
  i : ℕ
  /-- The current instruction's cell one step earlier. -/
  q : ℕ
  /-- The first instruction of the current step. -/
  lb : ℕ
  /-- The step-loop counter. -/
  lt : ℕ
  /-- The inner loop counter. -/
  ll : ℕ
  /-- The position in the hard-wired part of the input. -/
  pa : ℕ
  /-- The position in the free part of the input. -/
  pb : ℕ
  /-- Scratch. -/
  tmp : ℕ

/-- The register vector of a record. -/
def ER.f (e : ER) : Fin 11 → ℕ
  | ⟨0, _⟩ => e.nc
  | ⟨1, _⟩ => e.z
  | ⟨2, _⟩ => e.t
  | ⟨3, _⟩ => e.i
  | ⟨4, _⟩ => e.q
  | ⟨5, _⟩ => e.lb
  | ⟨6, _⟩ => e.lt
  | ⟨7, _⟩ => e.ll
  | ⟨8, _⟩ => e.pa
  | ⟨9, _⟩ => e.pb
  | ⟨10, _⟩ => e.tmp

/-- Setting one register of a record. -/
def ER.set (e : ER) : Fin 11 → ℕ → ER
  | ⟨0, _⟩, v => { e with nc := v }
  | ⟨1, _⟩, v => { e with z := v }
  | ⟨2, _⟩, v => { e with t := v }
  | ⟨3, _⟩, v => { e with i := v }
  | ⟨4, _⟩, v => { e with q := v }
  | ⟨5, _⟩, v => { e with lb := v }
  | ⟨6, _⟩, v => { e with lt := v }
  | ⟨7, _⟩, v => { e with ll := v }
  | ⟨8, _⟩, v => { e with pa := v }
  | ⟨9, _⟩, v => { e with pb := v }
  | ⟨10, _⟩, v => { e with tmp := v }

/-- Register `NC` of a record is its `nc` field. -/
@[simp] theorem ER.f_nc (e : ER) : e.f rNC = e.nc := rfl
/-- Register `Z` of a record is its `z` field. -/
@[simp] theorem ER.f_z (e : ER) : e.f rZ = e.z := rfl
/-- Register `T` of a record is its `t` field. -/
@[simp] theorem ER.f_t (e : ER) : e.f rT = e.t := rfl
/-- Register `I` of a record is its `i` field. -/
@[simp] theorem ER.f_i (e : ER) : e.f rI = e.i := rfl
/-- Register `Q` of a record is its `q` field. -/
@[simp] theorem ER.f_q (e : ER) : e.f rQ = e.q := rfl
/-- Register `LB` of a record is its `lb` field. -/
@[simp] theorem ER.f_lb (e : ER) : e.f rLB = e.lb := rfl
/-- Register `LT` of a record is its `lt` field. -/
@[simp] theorem ER.f_lt (e : ER) : e.f rLT = e.lt := rfl
/-- Register `LL` of a record is its `ll` field. -/
@[simp] theorem ER.f_ll (e : ER) : e.f rLL = e.ll := rfl
/-- Register `PA` of a record is its `pa` field. -/
@[simp] theorem ER.f_pa (e : ER) : e.f rPA = e.pa := rfl
/-- Register `PB` of a record is its `pb` field. -/
@[simp] theorem ER.f_pb (e : ER) : e.f rPB = e.pb := rfl
/-- Register `TMP` of a record is its `tmp` field. -/
@[simp] theorem ER.f_tmp (e : ER) : e.f rTMP = e.tmp := rfl

/-- Updating the register vector of a record is setting the register. -/
theorem ER.update_f (e : ER) (r : Fin 11) (v : ℕ) : Function.update e.f r v = (e.set r v).f := by
  funext s
  fin_cases r <;> fin_cases s <;> rfl

/-- All registers `0`. -/
def ER.zero : ER := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The all-zero record is the all-zero register vector. -/
theorem ER.zero_f : ER.zero.f = fun _ => 0 := by
  funext s; fin_cases s <;> rfl

/-! ## Run lemmas on records -/

section Records

variable {Λ : Type} {P : Λ → Instr 11 Λ} {x : List Bool} {l l' : Λ} {e : ER} {p : ℕ}

/-- An increment, on records. -/
theorem goes_incR {r : Fin 11} (h : P l = .inc r l') :
    Goes P x l e.f p (some l') (e.set r (e.f r + 1)).f p [] 1 := by
  rw [← ER.update_f]; exact goes_inc h

/-- A decrement, on records. -/
theorem goes_decR {r : Fin 11} (h : P l = .dec r l') :
    Goes P x l e.f p (some l') (e.set r (e.f r - 1)).f p [] 1 := by
  rw [← ER.update_f]; exact goes_dec h

/-- No step at all. -/
theorem goes_refl (l : Λ) (ρ : Fin 11 → ℕ) (p : ℕ) : Goes P x l ρ p (some l) ρ p [] 0 :=
  fun o => ⟨0, le_rfl, by simp [run_zero]⟩

end Records

/-! ## Templates -/

/-- The input positions of a step, as handled by the emitter: position `0`, the hard-wired
positions (the first, `p = 1`, or a later one), the free positions (`p = 1` or later), and
the right end (`p = 1` when the virtual input is empty, or later). -/
inductive IPh where
  | p0 | zA | zB | uA | uB | e1 | e2
  deriving DecidableEq, Fintype

/-- The layout source of an input phase: none, hard-wired, or free. -/
def IPh.lay : IPh → Fin 3
  | .zA | .zB => 1
  | .uA | .uB => 2
  | _ => 0

/-- The templates: the constant gates, a hard-wired bit, the padding, the final output
vertex, and the tableau instructions (a work cell of tape `τ` in one of five phases
`r = 0`, `0 < r < T`, `r = T`, `T < r < 2T`, `r = 2T`; an input position; a snapshot), each
at the first step (`t0`) or a later one. -/
inductive Tpl (k : ℕ) where
  | pre
  | zg (b : Bool)
  | dum
  | fin
  | cell (τ : Fin k) (t0 : Bool) (ph : Fin 5)
  | inp (t0 : Bool) (ph : IPh)
  | snap (t0 : Bool)
  deriving DecidableEq, Fintype

variable {k : ℕ}

/-- The symbolic sources of an input template. -/
def inpPhS (W : ℕ) (t0 : Bool) : IPh → List (SSrc k)
  | .p0 => inpS W t0 true false false 0
  | .zA => inpS W t0 false true false 1
  | .zB => inpS W t0 false false false 1
  | .uA => inpS W t0 false true false 2
  | .uB => inpS W t0 false false false 2
  | .e1 => inpS W t0 false true true 0
  | .e2 => inpS W t0 false false true 0

/-- The (padded) symbolic sources of an instruction template. -/
def Tpl.srcs (W m : ℕ) : Tpl k → List (SSrc k)
  | .cell _ t0 ph => padS m (cellS W t0 (decide (ph ≠ 0)) (decide (ph = 2)) (decide (ph ≠ 4)))
  | .inp t0 ph => padS m (inpPhS W t0 ph)
  | .snap t0 => padS m (snapS W t0)
  | _ => []

/-- The kind of the tableau instruction of a template. -/
def Tpl.kind : Tpl k → CfgKind k
  | .cell τ _ _ => some (some τ)
  | .inp _ _ => some none
  | _ => none

/-- Whether a template is at the first step (no "one step earlier" pointer to advance). -/
def Tpl.t0 : Tpl k → Bool
  | .cell _ t0 _ => t0
  | .inp t0 _ => t0
  | .snap t0 => t0
  | _ => true

/-- The code of a gate list as it appears inside a list code: each gate preceded by `1`. -/
def gbits (gs : List DAGGate) : List Bool := gs.flatMap fun g => true :: g.encode

/-- A list code is the gate bits followed by `0`. -/
theorem encodeList_eq_gbits (gs : List
    DAGGate) : encodeList DAGGate.encode gs = gbits gs ++ [false] := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp [encodeList, gbits, ih]

/-- The gate bits of a concatenation are the concatenation of the gate bits. -/
@[simp] theorem gbits_append (gs hs : List DAGGate) : gbits (gs ++ hs) = gbits gs ++ gbits hs := by
  simp [gbits]

/-- The micro-operations printing a gate (preceded by its list marker `1`) whose arguments
are linear expressions. -/
def sgOps (g : GateKind) (args : List (LinE 11)) : List (MOp 11) :=
  .out true :: (bitsOps g.encode ++
    args.flatMap (fun a => .out true :: (linOps a ++ [.out false])) ++ [.out false])

/-- A list code: each element's code preceded by `1`, then `0`. -/
theorem encodeList_eq_flatMap {α : Type} (f : α → List Bool) (l : List α) :
    encodeList f l = l.flatMap (fun a => true :: f a) ++ [false] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [encodeList, ih]

/-- **A gate template prints the gate's code**, its arguments being the values of the
linear expressions. -/
theorem flatMap_exec_sgOps (ρ : Fin 11 → ℕ) (g : GateKind) (args : List (LinE 11)) :
    (sgOps g args).flatMap (MOp.exec ρ) = true :: DAGGate.encode ⟨g, args.map (LinE.val ρ)⟩ := by
  have h : ∀ a : LinE 11, (MOp.out true :: (linOps a ++ [MOp.out false])).flatMap (MOp.exec ρ) =
      true :: encodeNat (a.val ρ) := by
    intro a; simp [MOp.exec, flatMap_exec_linOps, encodeNat]
  simp only [sgOps, DAGGate.encode, encodeList_eq_flatMap, List.flatMap_cons, List.flatMap_append,
    flatMap_exec_bitsOps, List.flatMap_assoc, h, List.flatMap_map, MOp.exec, List.flatMap_nil,
    List.append_nil, List.cons_append, List.append_assoc, List.nil_append]

/-! ## The templates of a machine -/

variable (M : FinTM Bool)

/-- The number `W` of vertices per instruction of `cfgTab M`. -/
noncomputable abbrev Wd : ℕ := tabW (cfgArity M) (cfgWidth M) (cfgF M)

/-- The base `n + 2 + |z| + W (I + 1)` of the current instruction. -/
noncomputable def baseE : LinE 11 := (rNC :: rZ :: List.replicate (Wd M) rI, 2 + Wd M)

/-- The micro-operations printing a tableau instruction: a copy gate for each (symbolic)
source, then the fixed part of its kind shifted to the base. -/
noncomputable def instrOps (θ : Tpl M.k) : List (MOp 11) :=
  (θ.srcs (snapWidth M) (cfgArity M)).flatMap (fun s => sgOps .and [s.toLinE M]) ++
  (tabFixed (cfgArity M) (cfgWidth M) (cfgF M) θ.kind).flatMap
    (fun g => sgOps g.kind (g.args.map (fun a => ((baseE M).1, (baseE M).2 + a))))

/-- **The templates**: the two constant gates; a hard-wired bit's constant gate; the `W`
padding gates; the end of the gate list and the output vertex (bit `snapWidth` of the
instruction before `I`, the accumulator of the last snapshot); and the tableau
instructions. -/
noncomputable def tmpl : Tpl M.k → List (MOp 11)
  | .pre => bitsOps (gbits [constGate false, constGate true])
  | .zg b => bitsOps (gbits [constGate b])
  | .dum => bitsOps (gbits (List.replicate (Wd M) (constGate false)))
  | .fin => .out false ::
      (linOps ((SSrc.cur (k := M.k) (snapWidth M)).toLinE M) ++ [.out false])
  | θ => instrOps M θ

/-- The longest template. -/
noncomputable def Lmax : ℕ := Finset.univ.sup fun θ : Tpl M.k => (tmpl M θ).length

/-- Every template is at most `Lmax M` micro-operations long. -/
theorem length_tmpl_le (θ : Tpl M.k) : (tmpl M θ).length ≤ Lmax M :=
  Finset.le_sup (f := fun θ : Tpl M.k => (tmpl M θ).length) (Finset.mem_univ θ)

/-! ## Labels -/

/-- The sites of the copy macro (`dst += src`). -/
inductive CpS (k : ℕ) where
  | cA (τ : Fin k) (t0 : Bool)
  | cB (τ : Fin k) (t0 : Bool)
  | iz (t0 : Bool)
  | iu (t0 : Bool)
  | lb (t0 : Bool)
  | lt
  deriving DecidableEq, Fintype

/-- The sites of the clear macro. -/
inductive ClS where
  | pa (t0 : Bool)
  | pb (t0 : Bool)
  | lb (t0 : Bool)
  deriving DecidableEq, Fintype

/-- The count-down loops: the two cell loops of each work tape, the hard-wired and free input
loops, and the step loop. -/
inductive Hd (k : ℕ) where
  | cA (τ : Fin k) (t0 : Bool)
  | cB (τ : Fin k) (t0 : Bool)
  | iz (t0 : Bool)
  | iu (t0 : Bool)
  | lay
  deriving DecidableEq, Fintype

/-- **The labels of the emitter.** -/
inductive Lb (k L : ℕ) where
  | rN | nInc | nOne | nOut0 | rT | tInc | rZ | zInc
  | lay (t0 : Bool)
  | tp (θ : Tpl k) (pc : Fin (L + 1))
  | pI (θ : Tpl k)
  | pQ (θ : Tpl k)
  | cp (s : CpS k) (ph : Fin 7)
  | dA (τ : Fin k) (t0 : Bool)
  | dB (τ : Fin k) (t0 : Bool)
  | hd (h : Hd k)
  | dl (h : Hd k)
  | zb (t0 : Bool)
  | ub (t0 : Bool)
  | ub2 (t0 : Bool)
  | iPA (t0 : Bool)
  | iPB (t0 : Bool)
  | eT (t0 : Bool)
  | eT2 (t0 : Bool)
  | cl (s : ClS) (ph : Fin 2)
  | stop
  deriving DecidableEq, Fintype

variable {L : ℕ}

/-- The first label of a template. -/
def tpL (θ : Tpl k) : Lb k L := .tp θ 0

/-- The start of the cells of work tape `τ` (or of the input positions after the last tape). -/
def cellStart (t0 : Bool) (τ : ℕ) : Lb k L :=
  if h : τ < k then tpL (.cell ⟨τ, h⟩ t0 0) else tpL (.inp t0 .p0)

/-- The source register of a copy site. -/
def CpS.src : CpS k → Fin 11
  | .cA .. => rT
  | .cB .. => rT
  | .iz _ => rZ
  | .iu _ => rNC
  | .lb _ => rI
  | .lt => rT

/-- The destination register of a copy site. -/
def CpS.dst : CpS k → Fin 11
  | .lb _ => rLB
  | .lt => rLT
  | _ => rLL

/-- Where a copy site continues. -/
def CpS.exit : CpS k → Lb k L
  | .cA τ t0 => .dA τ t0
  | .cB τ t0 => .dB τ t0
  | .iz t0 => .hd (.iz t0)
  | .iu t0 => .hd (.iu t0)
  | .lb t0 => if t0 then .cp .lt 0 else .hd .lay
  | .lt => .hd .lay

/-- The register of a clear site. -/
def ClS.reg : ClS → Fin 11
  | .pa _ => rPA
  | .pb _ => rPB
  | .lb _ => rLB

/-- Where a clear site continues. -/
def ClS.exit : ClS → Lb k L
  | .pa t0 => .cl (.pb t0) 0
  | .pb t0 => tpL (.snap t0)
  | .lb t0 => .cp (.lb t0) 0

/-- The counter of a loop. -/
def Hd.reg : Hd k → Fin 11
  | .lay => rLT
  | _ => rLL

/-- Where a loop exits. -/
def Hd.exit : Hd k → Lb k L
  | .cA τ t0 => tpL (.cell τ t0 2)
  | .cB τ t0 => tpL (.cell τ t0 4)
  | .iz t0 => .cp (.iu t0) 0
  | .iu t0 => .eT t0
  | .lay => tpL .fin

/-- The body of a loop. -/
def Hd.body : Hd k → Lb k L
  | .cA τ t0 => tpL (.cell τ t0 1)
  | .cB τ t0 => tpL (.cell τ t0 3)
  | .iz t0 => .zb t0
  | .iu t0 => .ub t0
  | .lay => .lay false

/-- Where a template continues: the next parsing step, or the instruction counters. -/
def Tpl.next : Tpl k → Lb k L
  | .pre => .rZ
  | .zg _ => .zInc
  | .dum => .lay true
  | .fin => .stop
  | θ => .pI θ

/-- Where an instruction continues after advancing the counters. -/
def Tpl.after : Tpl k → Lb k L
  | .cell τ t0 ⟨0, _⟩ => .cp (.cA τ t0) 0
  | .cell τ t0 ⟨1, _⟩ => .hd (.cA τ t0)
  | .cell τ t0 ⟨2, _⟩ => .cp (.cB τ t0) 0
  | .cell τ t0 ⟨3, _⟩ => .hd (.cB τ t0)
  | .cell τ t0 ⟨_ + 4, _⟩ => cellStart t0 (τ + 1)
  | .inp t0 .p0 => .cp (.iz t0) 0
  | .inp t0 .zA => .iPA t0
  | .inp t0 .zB => .iPA t0
  | .inp t0 .uA => .iPB t0
  | .inp t0 .uB => .iPB t0
  | .inp t0 .e1 => .cl (.pa t0) 0
  | .inp t0 .e2 => .cl (.pa t0) 0
  | .snap t0 => .cl (.lb t0) 0
  | _ => .stop

/-- **The emitter program.** -/
noncomputable def prog : Lb M.k (Lmax M) → Instr 11 (Lb M.k (Lmax M))
  | .rN => .rd .stop .nOut0 .nInc
  | .nInc => .inc rNC .nOne
  | .nOne => .out true .rN
  | .nOut0 => .out false .rT
  | .rT => .rd .stop (tpL .pre) .tInc
  | .tInc => .inc rT .rT
  | .rZ => .rd (tpL .dum) (tpL (.zg false)) (tpL (.zg true))
  | .zInc => .inc rZ .rZ
  | .lay t0 => .jz rT .stop (cellStart t0 0)
  | .tp θ pc => tmplInstr (tmpl M θ) (fun i => .tp θ (Fin.ofNat _ i)) θ.next pc.val
  | .pI θ => .inc rI (.pQ θ)
  | .pQ θ => if θ.t0 then .goto θ.after else .inc rQ θ.after
  | .cp s ⟨0, _⟩ => .jz s.src (.cp s 3) (.cp s 1)
  | .cp s ⟨1, _⟩ => .dec s.src (.cp s 2)
  | .cp s ⟨2, _⟩ => .inc s.dst (.cp s 6)
  | .cp s ⟨3, _⟩ => .jz rTMP s.exit (.cp s 4)
  | .cp s ⟨4, _⟩ => .dec rTMP (.cp s 5)
  | .cp s ⟨5, _⟩ => .inc s.src (.cp s 3)
  | .cp s ⟨_ + 6, _⟩ => .inc rTMP (.cp s 0)
  | .dA τ t0 => .dec rLL (.hd (.cA τ t0))
  | .dB τ t0 => .dec rLL (.hd (.cB τ t0))
  | .hd h => .jz h.reg h.exit (.dl h)
  | .dl h => .dec h.reg h.body
  | .zb t0 => .jz rPA (tpL (.inp t0 .zA)) (tpL (.inp t0 .zB))
  | .ub t0 => .jz rPB (.ub2 t0) (tpL (.inp t0 .uB))
  | .ub2 t0 => .jz rZ (tpL (.inp t0 .uA)) (tpL (.inp t0 .uB))
  | .iPA t0 => .inc rPA (.hd (.iz t0))
  | .iPB t0 => .inc rPB (.hd (.iu t0))
  | .eT t0 => .jz rZ (.eT2 t0) (tpL (.inp t0 .e2))
  | .eT2 t0 => .jz rNC (tpL (.inp t0 .e1)) (tpL (.inp t0 .e2))
  | .cl s ⟨0, _⟩ => .jz s.reg s.exit (.cl s 1)
  | .cl s ⟨_ + 1, _⟩ => .dec s.reg (.cl s 0)
  | .stop => .halt

end UTab

end Complexity
