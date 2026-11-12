/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Efficiency

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Forwarding handlers and log readers

Both reductions of [PS10, Theorem 175.9] run the adversary once against the reduction's own
oracles: every query is **forwarded** unchanged to the outer oracle of the same index, and only
the finalization differs. This file builds that handler once, generically in the oracle lengths
(`fwdHandler`), as a `Games.InteractiveHandler` with one outer call per inner query and an empty
state, so that T2 (`Games.exists_interactiveHandlerMachine`) makes it a machine. Its answers are
the outer oracle's (`fwdHandler_impl`), so simulating it is running the adversary against the
outer oracles (`simulate_fwdHandler_impl`).

It also provides the readers of a finalization input `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨a, L⟩⟩⟩` (`finU`,
`finZ`, `finW`, `finA`, `finL`) and of an encoded outer log: `logEmit G L` concatenates `G` of the
successive suffixes of the nested log `L`, is polynomial-time for polynomial-time `G`
(`polyTimeComputable_logEmit`), and on an encoded log is the concatenation of `G`'s values on the
entries (`logEmit_encodeLog`).

## Main definitions

* `NMCCA2.fwdHandler`: the forwarding handler with a given finalization.
* `NMCCA2.finU`, `finZ`, `finW`, `finA`, `finL`: the fields of a finalization input.
* `NMCCA2.logEmit`: concatenated readings of the suffixes of an encoded log.

## Main results

* `NMCCA2.fwdHandler_impl`, `NMCCA2.simulate_fwdHandler_impl`: forwarding.
* `NMCCA2.polyTimeComputable_logEmit`, `NMCCA2.logEmit_encodeLog`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 175.9 (book p. 175).
-/

namespace TCSlib.Cryptography.Composability.NMCCA2

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

variable {k : ℕ}

/-! ### Readers of a round input -/

/-- The state `s` of a round input `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩`. -/
private def rState (w : List Bool) : List Bool := pairFstD (pairSndD w)
/-- The oracle index `1^i` of a round input. -/
private def rIdx (w : List Bool) : List Bool := pairFstD (pairFstD (pairSndD (pairSndD w)))
/-- The query `x` of a round input. -/
private def rQuery (w : List Bool) : List Bool := pairSndD (pairFstD (pairSndD (pairSndD w)))
/-- The outer log `L` of the call so far. -/
private def rLog (w : List Bool) : List Bool := pairSndD (pairSndD (pairSndD w))
/-- The outer answer `y` recorded in a one-entry log `⟨⟨1^j, ⟨x, y⟩⟩, []⟩`. -/
private def rAns (w : List Bool) : List Bool := pairSndD (pairSndD (pairFstD (rLog w)))

/-- The fields of a round input (DL-30–34 overlap: the round-input readers). -/
private theorem fields_input (n : ℕ) (z ω s : List Bool) (i : Fin k) (x L : List Bool) :
    rState (InteractiveHandler.input n z ω s i x L) = s ∧
      rIdx (InteractiveHandler.input n z ω s i x L) = List.replicate i true ∧
      rQuery (InteractiveHandler.input n z ω s i x L) = x ∧
      rLog (InteractiveHandler.input n z ω s i x L) = L := by
  simp only [InteractiveHandler.input_eq, rState, rIdx, rQuery, rLog, pairFstD_pairEncode,
    pairSndD_pairEncode, and_self]

/-- **One forwarding round.** With an empty outer log, ask the outer oracle `i` the query `x`;
with the outer answer `y` in the log, return `y` and keep the state. -/
private def fwdRun (w : List Bool) : List Bool :=
  if decide (rLog w = []) then pairEncode [false] (pairEncode (rIdx w) (rQuery w))
  else pairEncode [true] (rAns w ++ rState w)

/-- The forwarding round is polynomial-time. -/
private theorem polyTimeComputable_fwdRun : PolyTimeComputable fwdRun := by
  have hF := polyTimeComputable_pairFstD
  have hD := polyTimeComputable_pairSndD
  have hS : PolyTimeComputable rState := hF.comp hD
  have hI : PolyTimeComputable rIdx := hF.comp (hF.comp (hD.comp hD))
  have hX : PolyTimeComputable rQuery := hD.comp (hF.comp (hD.comp hD))
  have hL : PolyTimeComputable rLog := hD.comp (hD.comp hD)
  have hA : PolyTimeComputable rAns := hD.comp (hD.comp (hF.comp hL))
  exact polyTimeComputable_ite (polyTimeComputable_isNil.comp hL)
    ((polyTimeComputable_const [false]).pairEncode (hI.pairEncode hX))
    ((polyTimeComputable_const [true]).pairEncode (hA.append hS))

/-! ### The forwarding handler -/

/-- **The forwarding handler** for `k` bit-string oracles with lengths `din`, `dout`, inner and
outer alike: empty state, the seed of `seedLen(n)` bits, one outer call per inner query, which
forwards the query to the outer oracle of the same index and returns its answer; the adversary's
input `advIn`, and the finalization `finRun` with `outLen(n)`-bit output and at most `finCall(n)`
outer queries. -/
def fwdHandler (din dout : Fin k → PolyExpr) (seedLen : PolyExpr)
    (advIn : List Bool → List Bool) (advIn_poly : PolyTimeComputable advIn)
    (outLen finCall : PolyExpr) (finRun : List Bool → List Bool)
    (finRun_poly : PolyTimeComputable finRun) : InteractiveHandler k din dout k din dout where
  stateLen := .const 0
  seedLen := seedLen
  perCall := .const 1
  init _ := zeroBits _
  run := fwdRun
  poly := polyTimeComputable_fwdRun
  advIn := advIn
  advIn_poly := advIn_poly
  outLen := outLen
  finCall := finCall
  finRun := finRun
  finRun_poly := finRun_poly

attribute [simps (config := { isSimp := false }) stateLen seedLen perCall init advIn outLen finCall
  finRun] fwdHandler

section Forward

variable (din dout : Fin k → PolyExpr) (seedLen : PolyExpr) (advIn : List Bool → List Bool)
  (advIn_poly : PolyTimeComputable advIn) (outLen finCall : PolyExpr)
  (finRun : List Bool → List Bool) (finRun_poly : PolyTimeComputable finRun)

/-- **The forwarding handler forwards:** the inner query `x` to oracle `i` in state `s` is the
outer query `x` to oracle `i`, answered with the outer answer `y` and the state kept:
`H.impl n z ω i x s = query i x (fun y => pure (y, s))`.

**Proof sketch.** The call's first round has an empty outer log, so it is the query
`⟨[false], ⟨1^i, x⟩⟩` (`decodeBitMove_query`); its second round reads the answer `y` from the
one-entry log and returns `y ‖ s` (`decodeBitMove_ret`), which `impl` splits back into `y` and
`s` (`Fin.append_left`, `Fin.append_right`). -/
theorem fwdHandler_impl (n : ℕ) (z : List Bool)
    (ω : Fin ((fwdHandler din dout seedLen advIn advIn_poly outLen finCall finRun
      finRun_poly).seedLen.eval n) → Bool) (i : Fin k) (x : Fin ((din i).eval n) → Bool)
    (s : Fin ((fwdHandler din dout seedLen advIn advIn_poly outLen finCall finRun
      finRun_poly).stateLen.eval n) → Bool) :
    (fwdHandler din dout seedLen advIn advIn_poly outLen finCall finRun finRun_poly).impl n z ω
        i x s = .query i x fun y => .pure (y, s) := by
  rw [InteractiveHandler.impl_apply, InteractiveHandler.call_eq, fwdHandler_perCall,
    PolyExpr.eval_const]
  rw [buildComp_succ_of_query (i := i) (x := x) (by
    show decodeBitMove _ _ _ (fwdRun _) = _
    obtain ⟨-, hI, hX, hL⟩ := fields_input (k := k) n z (List.ofFn ω) (List.ofFn s) i
      (List.ofFn x)
      ((bitCodec (fun j => (din j).eval n) (fun j => (dout j).eval n) 0).encodeLog [])
    rw [fwdRun, hI, hX, hL, MachineCodec.encodeLog_nil, if_pos (decide_eq_true rfl)]
    exact decodeBitMove_query (fun j => (din j).eval n) (fun j => (dout j).eval n) _ i x),
    OracleComp.query_bind]
  congr 1
  funext y
  rw [buildComp_zero_of_ret (a := Fin.append y s) (by
    show decodeBitMove _ _ _ (fwdRun _) = _
    obtain ⟨hS, -, -, hL⟩ := fields_input (k := k) n z (List.ofFn ω) (List.ofFn s) i
      (List.ofFn x)
      ((bitCodec (fun j => (din j).eval n) (fun j => (dout j).eval n) 0).encodeLog
        ([] ++ [⟨i, x, y⟩]))
    have hlog : (bitCodec (fun j => (din j).eval n) (fun j => (dout j).eval n) 0).encodeLog
        ([] ++ [⟨i, x, y⟩]) = pairEncode (pairEncode (List.replicate i true)
          (pairEncode (List.ofFn x) (List.ofFn y))) [] := by
      rw [List.nil_append, MachineCodec.encodeLog_cons, MachineCodec.encodeLog_nil,
        bitCodec_encodeEntry]
    have hA : rAns (InteractiveHandler.input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x)
        ((bitCodec (fun j => (din j).eval n) (fun j => (dout j).eval n) 0).encodeLog
          ([] ++ [⟨i, x, y⟩]))) = List.ofFn y := by
      rw [rAns, hL, hlog, pairFstD_pairEncode, pairSndD_pairEncode, pairSndD_pairEncode]
    rw [fwdRun, hA, hS, hL, hlog, if_neg (fun h => pairEncode_ne_nil _ _ (of_decide_eq_true h)),
      ← List.ofFn_fin_append]
    exact decodeBitMove_ret _ _ _ _)]
  rw [OracleComp.pure_bind]
  congr 2
  · funext j
    exact Fin.append_left y s j
  · funext j
    exact Fin.append_right y s j

/-- **Simulating the forwarding handler is running the computation:** for every computation
`c` against the oracles and every state `s`, `simulate (H.impl n z ω) c s = c.bind (fun a =>
pure (a, s))`.

**Proof sketch.** Induction on `c`, with `fwdHandler_impl` at each query. -/
theorem simulate_fwdHandler_impl (n : ℕ) (z : List Bool)
    (ω : Fin ((fwdHandler din dout seedLen advIn advIn_poly outLen finCall finRun
      finRun_poly).seedLen.eval n) → Bool) {α : Type}
    (c : OracleComp (bitSpecAt din dout n) α)
    (s : Fin ((fwdHandler din dout seedLen advIn advIn_poly outLen finCall finRun
      finRun_poly).stateLen.eval n) → Bool) :
    simulate ((fwdHandler din dout seedLen advIn advIn_poly outLen finCall finRun
      finRun_poly).impl n z ω) c s = c.bind fun a => .pure (a, s) := by
  induction c with
  | pure a => rw [simulate_pure, OracleComp.pure_bind]
  | query i x k ih =>
    rw [simulate_query, fwdHandler_impl, OracleComp.query_bind, OracleComp.query_bind]
    congr 1
    funext y
    rw [OracleComp.pure_bind]
    exact ih y

end Forward

/-! ### Readers of a finalization input -/

/-- The parameter `1^n` of a finalization input `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨a, L⟩⟩⟩`. -/
def finU (w : List Bool) : List Bool := pairFstD (pairFstD w)

/-- `finU w = pairFstD (pairFstD w)`. -/
theorem finU_eq (w : List Bool) : finU w = pairFstD (pairFstD w) := rfl

/-- The reduction input `z` of a finalization input. -/
def finZ (w : List Bool) : List Bool := pairFstD (pairSndD (pairFstD w))

/-- `finZ w = pairFstD (pairSndD (pairFstD w))`. -/
theorem finZ_eq (w : List Bool) : finZ w = pairFstD (pairSndD (pairFstD w)) := rfl

/-- The seed `ω` of a finalization input. -/
def finW (w : List Bool) : List Bool := pairSndD (pairSndD (pairFstD w))

/-- `finW w = pairSndD (pairSndD (pairFstD w))`. -/
theorem finW_eq (w : List Bool) : finW w = pairSndD (pairSndD (pairFstD w)) := rfl

/-- The adversary's output `a` of a finalization input. -/
def finA (w : List Bool) : List Bool := pairFstD (pairSndD (pairSndD w))

/-- `finA w = pairFstD (pairSndD (pairSndD w))`. -/
theorem finA_eq (w : List Bool) : finA w = pairFstD (pairSndD (pairSndD w)) := rfl

/-- The outer log `L` of the finalization so far. -/
def finL (w : List Bool) : List Bool := pairSndD (pairSndD (pairSndD w))

/-- `finL w = pairSndD (pairSndD (pairSndD w))`. -/
theorem finL_eq (w : List Bool) : finL w = pairSndD (pairSndD (pairSndD w)) := rfl

/-- **The fields of a finalization input:** on `finInput n z ω s a L = ⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨a,
L⟩⟩⟩` the readers return `1^n`, `z`, `ω`, `a` and `L`. -/
theorem fields_finInput (n : ℕ) (z ω s a L : List Bool) :
    finU (InteractiveHandler.finInput n z ω s a L) = List.replicate n true ∧
      finZ (InteractiveHandler.finInput n z ω s a L) = z ∧
      finW (InteractiveHandler.finInput n z ω s a L) = ω ∧
      finA (InteractiveHandler.finInput n z ω s a L) = a ∧
      finL (InteractiveHandler.finInput n z ω s a L) = L := by
  simp only [InteractiveHandler.finInput_eq, seedIn_eq, finU, finZ, finW, finA, finL,
    pairFstD_pairEncode, pairSndD_pairEncode, and_self]

/-- The finalization-input readers are polynomial-time. -/
theorem polyTimeComputable_finFields :
    PolyTimeComputable finU ∧ PolyTimeComputable finZ ∧ PolyTimeComputable finW ∧
      PolyTimeComputable finA ∧ PolyTimeComputable finL := by
  have hF := polyTimeComputable_pairFstD
  have hD := polyTimeComputable_pairSndD
  exact ⟨hF.comp hF, hF.comp (hD.comp hF), hD.comp (hD.comp hF), hF.comp (hD.comp hD),
    hD.comp (hD.comp hD)⟩

/-! ### Readers of an encoded log -/

/-- **Concatenated readings of an encoded log:** `G` applied to the successive suffixes
`L, snd L, snd (snd L), …` of the nested log `L = ⟨e₁, ⟨e₂, ⟨…, []⟩⟩⟩`, for `|L| + 1` steps, and
concatenated: `logEmit G L = (List.range (|L| + 1)).flatMap fun i => G (pairSndD^[i] L)`. -/
def logEmit (G : List Bool → List Bool) (L : List Bool) : List Bool :=
  (List.range (L.length + 1)).flatMap fun i => G (pairSndD^[i] L)

/-- `logEmit G L = (List.range (|L| + 1)).flatMap fun i => G (pairSndD^[i] L)`. -/
theorem logEmit_eq (G : List Bool → List Bool) (L : List Bool) :
    logEmit G L = (List.range (L.length + 1)).flatMap fun i => G (pairSndD^[i] L) := rfl

/-- The iterated second projection never lengthens a word. -/
private theorem length_iterate_pairSndD_le (L : List Bool) (i : ℕ) :
    (pairSndD^[i] L).length ≤ L.length := by
  induction i with
  | zero => exact le_rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact (length_pairSndD_le _).trans ih

/-- **The readings of an encoded log are polynomial-time** when `G` is
(`Complexity.polyTimeComputable_iterateEmit` with the step `pairSndD`, which never lengthens a
word, and `|L|` rounds). -/
theorem polyTimeComputable_logEmit {G : List Bool → List Bool} (hG : PolyTimeComputable G) :
    PolyTimeComputable (logEmit G) :=
  (polyTimeComputable_iterateEmit polyTimeComputable_pairSndD hG .var .var
    (fun x i _ => by rw [PolyExpr.eval_var]; exact length_iterate_pairSndD_le x i)).congr
    fun L => by rw [PolyExpr.eval_var, logEmit_eq]

section LogEmit

variable {ι : Type} {spec : OracleSpec ι} {α : Type}

/-- The second projection of an encoded log drops its first entry. -/
private theorem iterate_pairSndD_encodeLog (codec : MachineCodec spec α) (h : QueryLog spec)
    (i : ℕ) : pairSndD^[i] (codec.encodeLog h) = codec.encodeLog (h.drop i) := by
  induction i generalizing h with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply]
    cases h with
    | nil =>
      rw [MachineCodec.encodeLog_nil, pairSndD_of_pairDecode_eq_none pairDecode_nil,
        ← MachineCodec.encodeLog_nil codec, ih, List.drop_nil, List.drop_nil]
    | cons e t =>
      rw [MachineCodec.encodeLog_cons, pairSndD_pairEncode, ih, List.drop_succ_cons]

/-- Reading the suffixes of a log within at least its number of steps. -/
private theorem flatMap_range_drop (codec : MachineCodec spec α) (G : List Bool → List Bool)
    (g : (Σ i, spec.dom i × spec.rng i) → List Bool) (hnil : G [] = [])
    (hcons : ∀ e t, G (pairEncode (codec.encodeEntry e) t) = g e) :
    ∀ (h : QueryLog spec) (m : ℕ), h.length ≤ m →
      ((List.range m).flatMap fun i => G (codec.encodeLog (h.drop i))) = h.flatMap g := by
  intro h
  induction h with
  | nil =>
    intro m _
    rw [List.flatMap_nil]
    refine List.flatMap_eq_nil_iff.2 fun i _ => ?_
    rw [List.drop_nil, MachineCodec.encodeLog_nil, hnil]
  | cons e t ih =>
    intro m hm
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by rw [List.length_cons] at hm; omega⟩
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, List.drop_zero,
      MachineCodec.encodeLog_cons, hcons, List.flatMap_cons]
    congr 1
    simp only [List.drop_succ_cons]
    exact ih m' (by rw [List.length_cons] at hm; omega)

/-- An encoded log is at least as long as its number of entries. -/
private theorem length_le_length_encodeLog (codec : MachineCodec spec α) (h : QueryLog spec) :
    h.length ≤ (codec.encodeLog h).length := by
  induction h with
  | nil => exact le_rfl
  | cons e t ih =>
    rw [MachineCodec.encodeLog_cons, length_pairEncode, List.length_cons]
    omega

/-- **The readings of an encoded log are the readings of its entries:** if `G [] = []` and `G`
reads only the first entry of a nonempty log, `G ⟨⟦e⟧, t⟩ = g e`, then
`logEmit G (codec.encodeLog h) = h.flatMap g`.

**Proof sketch.** The `i`-th suffix of the encoded log encodes `h.drop i`; the first `|h|`
readings are `g` of the entries and the rest are `G [] = []`, since `|h| ≤ |L|`. -/
theorem logEmit_encodeLog (codec : MachineCodec spec α) (G : List Bool → List Bool)
    (g : (Σ i, spec.dom i × spec.rng i) → List Bool) (hnil : G [] = [])
    (hcons : ∀ e t, G (pairEncode (codec.encodeEntry e) t) = g e) (h : QueryLog spec) :
    logEmit G (codec.encodeLog h) = h.flatMap g := by
  rw [logEmit_eq]
  simp only [iterate_pairSndD_encodeLog]
  exact flatMap_range_drop codec G g hnil hcons h _
    (Nat.le_succ_of_le (length_le_length_encodeLog codec h))

end LogEmit

end TCSlib.Cryptography.Composability.NMCCA2
