/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Challenge

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The simulator of IND ⇒ SIM

Direction IND ⇒ SIM of [PS10, Theorem 174.8] ([PSV07, Theorem 3], at one message), under CPA.
The simulator runs the SIM adversary `A` on `pk`, answering `Dec` with `⊥`. On `A`'s first
challenge `a` it asks its only query `a`, gets `h(m)`, draws `m̃ = M(a; ρ̃)` with its own coins
(with `M`'s advice, read from its input `⟨pk, α_M⟩`), encrypts `ỹ = Enc_pk(m̃; re)` with its own
coins, answers `⟨ỹ, h(m)⟩` and records it. It outputs `A`'s ciphertexts, each flagged `COPY` iff it
equals `ỹ`, and `σ`.

It is the challenge handler (`chalHandler`) with the parameters `simParams`. Against the history
oracle, its run is `A`'s run against the hybrid oracle `rImpl … true … ρ ρ̃ (some re)`, which
encrypts an independent draw (`simComp_abs`); and the ideal experiment's view of its output is the
hybrid's view of `A`'s (`idealView_simOut`).

## Main definitions

* `NMSim.simMsg`, `NMSim.simCt`: `m̃` and `ỹ` read from a round input.
* `NMSim.flagF`, `NMSim.simOutL`, `NMSim.simFin`: the finalization.
* `NMSim.simParams`: the parameters of the simulator's handler.

## Main results

* `NMSim.simFinish`, `NMSim.simComp_abs`, `NMSim.idealView_simOut`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 174.8 (book p. 174).
* [PSV07] R. Pass, a. shelat, V. Vaikuntanathan, *Relations among notions of non-malleability for
  encryption*, ASIACRYPT 2007, LNCS 4833, pp. 519–535: Theorem 3.
-/

namespace TCSlib.Cryptography.Composability.NMSim

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open NMCCA2 (finU finA fields_finInput polyTimeComputable_finFields)

variable (S : FixedLengthPKScheme) (samp : NUPPT)

/-! ### The dummy challenge -/

/-- The dummy message `m̃ = M(a; ρ̃)` read in a round `w`: with `n = |rdU w|`, `a = rdQuery w`, the
advice `α = snd (rdZ w)` and `ρ̃` the first `coins(n)` bits of the seed, `padL msgLen(n)` of `M`'s
output on `layout 1^n a α ρ̃`. -/
def simMsg (w : List Bool) : List Bool :=
  EnsembleLemmas.padL (S.msgLen.eval (rdU w).length)
    (samp.output (NUPPT.layout (rdU w) (rdQuery w) (pairSndD (rdZ w))
      ((rdW w).take (samp.coins.eval (rdU w).length))))

/-- `simMsg S samp w = padL msgLen(n) (M.output (layout 1^n a α ρ̃))`. -/
theorem simMsg_eq (w : List Bool) :
    simMsg S samp w = EnsembleLemmas.padL (S.msgLen.eval (rdU w).length)
      (samp.output (NUPPT.layout (rdU w) (rdQuery w) (pairSndD (rdZ w))
        ((rdW w).take (samp.coins.eval (rdU w).length)))) := rfl

/-- The dummy challenge `ỹ = Enc_pk(m̃; re)` read in a round `w`: `pk = fst (rdZ w)`, `re` the seed
after `ρ̃`, `padL ctLen(n)` of `Enc`'s output on `⟨⟨⟨1^n, ⟨pk, m̃⟩⟩, []⟩, re⟩`. -/
def simCt (w : List Bool) : List Bool :=
  EnsembleLemmas.padL (S.ctLen.eval (rdU w).length)
    (S.enc.output (pairEncode (pairEncode (pairEncode (rdU w)
      (pairEncode (pairFstD (rdZ w)) (simMsg S samp w))) [])
      ((rdW w).drop (samp.coins.eval (rdU w).length))))

/-- `simCt S samp w = padL ctLen(n) (Enc.output ⟨⟨⟨1^n, ⟨pk, m̃⟩⟩, []⟩, re⟩)`. -/
theorem simCt_eq (w : List Bool) :
    simCt S samp w = EnsembleLemmas.padL (S.ctLen.eval (rdU w).length)
      (S.enc.output (pairEncode (pairEncode (pairEncode (rdU w)
        (pairEncode (pairFstD (rdZ w)) (simMsg S samp w))) [])
        ((rdW w).drop (samp.coins.eval (rdU w).length)))) := rfl

/-- The dummy message is polynomial-time. -/
theorem polyTimeComputable_simMsg : PolyTimeComputable (simMsg S samp) := by
  obtain ⟨hU, hZ, hW, -, -, hQ, -, -⟩ := polyTimeComputable_rd
  have hρ : PolyTimeComputable fun w => (rdW w).take (samp.coins.eval (rdU w).length) :=
    ((polyTimeComputable_pairTakePoly samp.coins).comp (hU.pairEncode hW)).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  exact EnsembleLemmas.polyTimeComputable_padL S.msgLen hU (samp.polyTimeComputable_output.comp
    (NUPPT.polyTimeComputable_layout hU hQ (polyTimeComputable_pairSndD.comp hZ) hρ))

/-- The dummy challenge is polynomial-time. -/
theorem polyTimeComputable_simCt : PolyTimeComputable (simCt S samp) := by
  obtain ⟨hU, hZ, hW, -, -, -, -, -⟩ := polyTimeComputable_rd
  have hre : PolyTimeComputable fun w => (rdW w).drop (samp.coins.eval (rdU w).length) :=
    ((polyTimeComputable_pairDropPoly samp.coins).comp (hU.pairEncode hW)).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  exact EnsembleLemmas.polyTimeComputable_padL S.ctLen hU (S.enc.polyTimeComputable_output.comp
    (((hU.pairEncode ((polyTimeComputable_pairFstD.comp hZ).pairEncode
      (polyTimeComputable_simMsg S samp))).pairEncode (polyTimeComputable_const [])).pairEncode
      hre))

/-! ### The finalization -/

/-- The state `s` of a finalization input `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨a, L⟩⟩⟩`. -/
def finSt (w : List Bool) : List Bool := pairFstD (pairSndD w)

/-- `finSt w = pairFstD (pairSndD w)`. -/
theorem finSt_eq (w : List Bool) : finSt w = pairFstD (pairSndD w) := rfl

/-- The state of a finalization input: `finSt (finInput n z ω s a L) = s`. -/
theorem finSt_finInput (n : ℕ) (z ω s a L : List Bool) :
    finSt (InteractiveHandler.finInput n z ω s a L) = s := by
  rw [finSt, InteractiveHandler.finInput_eq, pairSndD_pairEncode, pairFstD_pairEncode]

/-- The state reader is polynomial-time. -/
theorem polyTimeComputable_finSt : PolyTimeComputable finSt :=
  polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD

/-- **The flagged entry** of a ciphertext `c`, on the context `⟨1^n, s⟩` with the state
`s = [flag] ‖ ỹ ‖ …`: `[flag ∧ c = ỹ]` followed by `c`. -/
def flagF (ctx c : List Bool) : List Bool :=
  ((pairSndD ctx).headD false &&
    decide (c = ((pairSndD ctx).drop 1).take (S.ctLen.eval (pairFstD ctx).length))) :: c

/-- `flagF S ctx c = [snd ctx's flag ∧ c = ỹ] ++ c`. -/
theorem flagF_eq (ctx c : List Bool) :
    flagF S ctx c = ((pairSndD ctx).headD false &&
      decide (c = ((pairSndD ctx).drop 1).take (S.ctLen.eval (pairFstD ctx).length))) :: c := rfl

/-- The flagged entry is polynomial-time, as a function of `⟨ctx, c⟩`. -/
theorem polyTimeComputable_flagF :
    PolyTimeComputable fun z => flagF S (pairFstD z) (pairSndD z) := by
  have hF := polyTimeComputable_pairFstD
  have hD := polyTimeComputable_pairSndD
  have hy : PolyTimeComputable fun z =>
      ((pairSndD (pairFstD z)).drop 1).take (S.ctLen.eval (pairFstD (pairFstD z)).length) :=
    ((polyTimeComputable_pairTakePoly S.ctLen).comp ((hF.comp hF).pairEncode
      (polyTimeComputable_tail.comp (hD.comp hF)))).congr fun z => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have heq : PolyTimeComputable fun z => [decide (pairSndD z =
      ((pairSndD (pairFstD z)).drop 1).take (S.ctLen.eval (pairFstD (pairFstD z)).length))] :=
    (polyTimeComputable_pairEq.comp (hD.pairEncode hy)).congr fun z => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  exact BinArith.polyTimeComputable_cons
    (polyTimeComputable_and (polyTimeComputable_headD.comp (hD.comp hF)) heq) hD

/-- **The simulator's output** at parameter `n`, for the state string `st` and `A`'s output `a`
(`r(n)` ciphertexts, then `σ`): the flagged entries `flagF ⟨1^n, st⟩ c_i`, then `σ`. -/
def simOutL (r : PolyExpr) (n : ℕ) (st a : List Bool) : List Bool :=
  ((List.range (r.eval n)).map fun i =>
    flagF S (pairEncode (List.replicate n true) st) (chunkAt (S.ctLen.eval n) i a)).flatten ++
  a.drop (r.eval n * S.ctLen.eval n)

/-- `simOutL S r n st a = (flagF ⟨1^n, st⟩ c_0 ++ ⋯ ++ flagF ⟨1^n, st⟩ c_{r-1}) ++ σ`. -/
theorem simOutL_eq (r : PolyExpr) (n : ℕ) (st a : List Bool) :
    simOutL S r n st a =
      ((List.range (r.eval n)).map fun i =>
        flagF S (pairEncode (List.replicate n true) st) (chunkAt (S.ctLen.eval n) i a)).flatten ++
      a.drop (r.eval n * S.ctLen.eval n) := rfl

/-- **The simulator's finalization round**: `⟨[true], F ‖ a.drop (r·ctLen)⟩`, with no outer query,
where `F` is `chunkMap ctLen flagF ⟨⟨1^n, s⟩, a.take (r·ctLen)⟩` (the flagged entries) when
`ctLen(n) > 0`, and the `r` flags `[flag]` when `ctLen(n) = 0` (every ciphertext is then empty, and
equal to `ỹ`). -/
def simFin (r : PolyExpr) (w : List Bool) : List Bool :=
  pairEncode [true]
    ((if decide (List.replicate (S.ctLen.eval (finU w).length) true = []) then
        (if (finSt w).headD false then List.replicate (r.eval (finU w).length) true
          else List.replicate (r.eval (finU w).length) false)
      else chunkMap S.ctLen (flagF S) (pairEncode (pairEncode (finU w) (finSt w))
        ((finA w).take ((r.mul S.ctLen).eval (finU w).length)))) ++
    (finA w).drop ((r.mul S.ctLen).eval (finU w).length))

/-- `simFin S r w = ⟨[true], F ‖ a.drop (r·ctLen)⟩`, with `F = flag^r` if `ctLen(n) = 0` and
`F = chunkMap ctLen flagF ⟨⟨1^n, s⟩, a.take (r·ctLen)⟩` otherwise. -/
theorem simFin_eq (r : PolyExpr) (w : List Bool) :
    simFin S r w = pairEncode [true]
      ((if decide (List.replicate (S.ctLen.eval (finU w).length) true = []) then
          (if (finSt w).headD false then List.replicate (r.eval (finU w).length) true
            else List.replicate (r.eval (finU w).length) false)
        else chunkMap S.ctLen (flagF S) (pairEncode (pairEncode (finU w) (finSt w))
          ((finA w).take ((r.mul S.ctLen).eval (finU w).length)))) ++
      (finA w).drop ((r.mul S.ctLen).eval (finU w).length)) := rfl

/-- The finalization round is polynomial-time. -/
theorem polyTimeComputable_simFin (r : PolyExpr) : PolyTimeComputable (simFin S r) := by
  obtain ⟨hU, -, -, hA, -⟩ := polyTimeComputable_finFields
  have hS := polyTimeComputable_finSt
  have htake : PolyTimeComputable fun w => (finA w).take ((r.mul S.ctLen).eval (finU w).length) :=
    ((polyTimeComputable_pairTakePoly (r.mul S.ctLen)).comp (hU.pairEncode hA)).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hdrop : PolyTimeComputable fun w => (finA w).drop ((r.mul S.ctLen).eval (finU w).length) :=
    ((polyTimeComputable_pairDropPoly (r.mul S.ctLen)).comp (hU.pairEncode hA)).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  exact (polyTimeComputable_const [true]).pairEncode
    ((polyTimeComputable_ite (polyTimeComputable_isNil.comp
        ((polyTimeComputable_unaryPoly S.ctLen).comp hU))
      (polyTimeComputable_ite (polyTimeComputable_headD.comp hS)
        ((polyTimeComputable_unaryPoly r).comp hU) (EnsembleLemmas.polyTimeComputable_zeros r hU))
      ((polyTimeComputable_chunkMap S.ctLen (polyTimeComputable_flagF S)).comp
        ((hU.pairEncode hS).pairEncode htake))).append hdrop)

/-- Every flagged entry has one bit more than its ciphertext. -/
theorem length_flagF (ctx c : List Bool) : (flagF S ctx c).length = c.length + 1 := by
  rw [flagF_eq, List.length_cons]

/-- **The finalization round on a finalization input** (for `A`'s output of `r·ctLen + sl` bits)
returns `⟨[true], simOutL …⟩`.

**Proof sketch.** Read the fields of the input in `simFin_eq` and split on `ctLen(n)`. If
`ctLen(n) = 0`, every chunk is empty and equals `ỹ`, so every flagged entry is `[flag]` and the
`r` entries flatten to `flag^r`. Otherwise cut `a.take (r·ctLen)` into its `r` chunks of
`ctLen(n)` bits (`take_eq_flatten_chunkAt`, `length_chunkAt`); `chunkMap_flatten` maps
`flagF` over them, which is `simOutL_eq`. -/
theorem simFin_finInput (r sl : PolyExpr) (n : ℕ) (z ω s a L : List Bool)
    (ha : a.length = r.eval n * S.ctLen.eval n + sl.eval n) :
    simFin S r (InteractiveHandler.finInput n z ω s a L) =
      pairEncode [true] (simOutL S r n s a) := by
  obtain ⟨hU, -, -, hA, -⟩ := fields_finInput n z ω s a L
  rw [simFin_eq, hU, hA, finSt_finInput, List.length_replicate, PolyExpr.eval_mul, simOutL_eq]
  congr 2
  by_cases hct : S.ctLen.eval n = 0
  · rw [if_pos (by rw [hct, List.replicate_zero]; rfl)]
    have hent : ∀ i, flagF S (pairEncode (List.replicate n true) s) (chunkAt (S.ctLen.eval n) i a) =
        [s.headD false] := by
      intro i
      rw [flagF_eq, pairSndD_pairEncode, pairFstD_pairEncode, List.length_replicate, hct,
        chunkAt_eq, List.take_zero, List.take_zero, decide_eq_true rfl, Bool.and_true]
    have hrep : ∀ (b : Bool) (m : ℕ), ((List.range m).map fun _ => [b]).flatten =
        List.replicate m b := by
      intro b m
      induction m with
      | zero => rfl
      | succ m ih => rw [List.range_succ, List.map_append, List.flatten_append, ih,
          List.map_singleton, List.flatten_singleton, List.replicate_succ']
    simp only [hent]
    rw [hrep]
    cases s.headD false <;> rfl
  · rw [if_neg (by rw [decide_eq_true_eq, List.replicate_eq_nil_iff]; exact hct),
      take_eq_flatten_chunkAt,
      chunkMap_flatten _ _ n s _ (fun ch hch => ?_) (Nat.pos_of_ne_zero hct), List.map_map]
    · rfl
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hch
      rw [List.mem_range] at hi
      refine length_chunkAt _ _ _ ?_
      rw [ha]
      have := Nat.mul_le_mul_right (S.ctLen.eval n) (show i + 1 ≤ r.eval n from hi)
      omega

/-! ### The handler -/

variable (pl hl : PolyExpr)

/-- **The parameters of the simulator's handler** (on the real experiment's oracles with parameter
length `pl` and history length `hl`; one outer oracle, the history oracle): the first challenge `a`
asks `a`; it answers `⟨ỹ, h⟩` with `ỹ = simCt` and `h` the outer answer. The seed is `ρ̃ ‖ re`
(the sampler's and `Enc`'s coins), the adversary runs on `pk = fst z`, the output is `r` flagged
entries and `σ` (`r·(ctLen + 1) + sl` bits, `simFin`), and the finalization may ask one query (it
asks none), so that T2's budget is at least `1`. -/
def simParams (r sl : PolyExpr) : ChalParams S pl hl 1 (fun _ => pl) (fun _ => hl) where
  j := 0
  seedLen := samp.coins.add S.enc.coins
  advIn ctx := pairFstD (pairFstD (pairSndD ctx))
  advIn_poly := polyTimeComputable_pairFstD.comp
    (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)
  qry w := EnsembleLemmas.padL (pl.eval (rdU w).length) (rdQuery w)
  qry_poly := EnsembleLemmas.polyTimeComputable_padL pl polyTimeComputable_rd.1
    polyTimeComputable_rd.2.2.2.2.2.1
  qry_len _ := EnsembleLemmas.length_padL _ _
  ansY := simCt S samp
  ansY_poly := polyTimeComputable_simCt S samp
  ansY_len _ := EnsembleLemmas.length_padL _ _
  ansH w := EnsembleLemmas.padL (hl.eval (rdU w).length) (rdAns w)
  ansH_poly := EnsembleLemmas.polyTimeComputable_padL hl polyTimeComputable_rd.1
    polyTimeComputable_rd.2.2.2.2.2.2.2
  ansH_len _ := EnsembleLemmas.length_padL _ _
  outLen := (r.mul (S.ctLen.add (.const 1))).add sl
  finCall := .const 1
  finRun := simFin S r
  finRun_poly := polyTimeComputable_simFin S r

attribute [simps (config := { isSimp := false }) j seedLen advIn qry ansY ansH outLen finCall
  finRun] simParams

section Run

variable (r sl : PolyExpr) (n : ℕ)

/-- The simulator's seed is `ρ̃ ‖ re`: `seedLen = samp.coins + enc.coins`. -/
theorem simParams_seedLen_handler :
    (chalHandler (simParams S samp pl hl r sl)).seedLen = samp.coins.add S.enc.coins := by
  rw [chalHandler_seedLen, simParams_seedLen]

/-- The simulator outputs `r·(ctLen + 1) + sl` bits. -/
theorem simParams_outLen_eval :
    (chalHandler (simParams S samp pl hl r sl)).outLen.eval n =
      r.eval n * (S.ctLen.eval n + 1) + sl.eval n := by
  rw [chalHandler_outLen, simParams_outLen, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_add,
    PolyExpr.eval_const]

/-- The simulator runs `A` on `pk`: `advInput n ⟨pk, α⟩ ω = pk`. -/
theorem simParams_advInput (pk α : List Bool)
    (ω : Fin ((chalHandler (simParams S samp pl hl r sl)).seedLen.eval n) → Bool) :
    (chalHandler (simParams S samp pl hl r sl)).advInput n (pairEncode pk α) ω = pk := by
  rw [InteractiveHandler.advInput_eq, chalHandler_advIn, simParams_advIn, seedIn_eq,
    pairSndD_pairEncode, pairFstD_pairEncode, pairFstD_pairEncode]

/-- **The simulator's finalization** on `A`'s output `a` (`r·ctLen + sl` bits) returns
`simOutL` of the state and `a`, asking nothing. -/
theorem simFinish (z : List Bool)
    (ω : Fin ((chalHandler (simParams S samp pl hl r sl)).seedLen.eval n) → Bool)
    (s : Fin ((chalHandler (simParams S samp pl hl r sl)).stateLen.eval n) → Bool) {d : ℕ}
    (a : Fin d → Bool) (hd : d = r.eval n * S.ctLen.eval n + sl.eval n) :
    (chalHandler (simParams S samp pl hl r sl)).finish n z ω s a =
      .pure (padFin _ (simOutL S r n (List.ofFn s) (List.ofFn a))) := by
  have ha : (List.ofFn a).length = r.eval n * S.ctLen.eval n + sl.eval n := by
    rw [List.length_ofFn, hd]
  refine InteractiveHandler.finish_of_ret_padFin _ n z ω s a _ ?_ ?_
  · rw [simParams_outLen_eval, simOutL_eq, List.length_append, List.length_drop, ha,
      length_flatten_map_range (S.ctLen.eval n + 1) _ _ fun i hi => ?_]
    · rw [Nat.mul_add, Nat.mul_one]
      omega
    · rw [length_flagF, length_chunkAt _ _ _ (by
        rw [ha]
        have := Nat.mul_le_mul_right (S.ctLen.eval n) (show i + 1 ≤ r.eval n from hi)
        omega)]
  · rw [chalHandler_finRun, simParams_finRun]
    exact simFin_finInput S r sl n z _ _ _ _ ha

end Run

/-! ### The simulator against the history oracle -/

section Composite

variable (hist : List Bool → List Bool) (r sl : PolyExpr) (n : ℕ)

/-- **The abstraction of the hybrid's state** to the simulator's and the history oracle's: no
challenge is `(empty, none)`; the challenge `y` on `a` is `(⟨y, h(M(a; ρ)), a⟩, some a)`. -/
def simAbs (ρ : samp.Coins n) :
    Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (pl.eval n) → Bool)) →
      (Fin ((chalHandler (simParams S samp pl hl r sl)).stateLen.eval n) → Bool) ×
        Option (Fin (pl.eval n) → Bool)
  | none => (chalState (simParams S samp pl hl r sl) n none, none)
  | some (y, a) => (chalState (simParams S samp pl hl r sl) n
      (some (y, histWith hist (hl.eval n) (drawWith samp (S.msgLen.eval n) n a ρ), a)), some a)

/-- `simAbs … none = (chalState none, none)`. -/
theorem simAbs_none (ρ : samp.Coins n) :
    simAbs S samp pl hl hist r sl n ρ none =
      (chalState (simParams S samp pl hl r sl) n none, none) := rfl

/-- `simAbs … (some (y, a)) = (chalState (some (y, h(M(a; ρ)), a)), some a)`. -/
theorem simAbs_some (ρ : samp.Coins n) (y : Fin (S.ctLen.eval n) → Bool)
    (a : Fin (pl.eval n) → Bool) :
    simAbs S samp pl hl hist r sl n ρ (some (y, a)) =
      (chalState (simParams S samp pl hl r sl) n
        (some (y, histWith hist (hl.eval n) (drawWith samp (S.msgLen.eval n) n a ρ), a)),
        some a) := rfl

/-- The history oracle's part of the abstraction is the recorded parameter. -/
theorem simAbs_snd (ρ : samp.Coins n)
    (s : Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (pl.eval n) → Bool))) :
    (simAbs S samp pl hl hist r sl n ρ s).2 = s.map Prod.snd := by
  cases s with
  | none => rfl
  | some ya => rfl

/-- **The dummy challenge in a round of the simulator** (input `⟨pk, M.advice n⟩`, seed
`ρ̃ ‖ re`, on
the parameter `x`): `simCt … = ⟦Enc_pk(M(x; ρ̃); re)⟧`. -/
theorem simCt_input (pk : List Bool) (ρ' : samp.Coins n) (re : S.enc.Coins n) (s : List Bool)
    (x : Fin ((snmDin S pl 1).eval n) → Bool) (L : List Bool) :
    simCt S samp (InteractiveHandler.input n (pairEncode pk (samp.advice n))
        (List.ofFn (seedEquiv (simParams_seedLen_handler S samp pl hl r sl) n (ρ', re))) s
        (1 : Fin 2) (List.ofFn x) L) =
      List.ofFn (encWith S n pk (drawWith samp (S.msgLen.eval n) n
        (padFin (pl.eval n) (List.ofFn x)) ρ') re) := by
  obtain ⟨hU, hZ, hW, -, -, hQ, -⟩ := fields_input (k := 2) n (pairEncode pk (samp.advice n))
    (List.ofFn (seedEquiv (simParams_seedLen_handler S samp pl hl r sl) n (ρ', re))) s 1
    (List.ofFn x) L
  have hxl : (List.ofFn x).length = pl.eval n := by
    rw [List.length_ofFn]
    show (snmDin S pl 1).eval n = _
    rw [snmDin_one]
  rw [simCt_eq, simMsg_eq, hU, hZ, hW, hQ, List.length_replicate, pairFstD_pairEncode,
    pairSndD_pairEncode, seedEquiv_ofFn,
    List.take_left' (length_ofFn_coins samp n ρ'), List.drop_left' (length_ofFn_coins samp n ρ'),
    encWith_eq, drawWith_eq, ofFn_padFin_eq_padL, ofFn_padFin_eq_padL,
    ofFn_padFin_of_length hxl, NUPPT.Uniform.runAt_eq S.enc_uniform, NUPPT.advInput_eq,
    NUPPT.runAt_eq, NUPPT.runAtL_eq_output_layout]

/-- **The simulator against the history oracle is the hybrid with an independent draw:** for the
input `⟨pk, M.advice n⟩` and the seed `ρ̃ ‖ re`, the composition of the history oracle (coins `ρ`)
with the simulator's handler, from the abstracted state, is `rImpl … true … ρ ρ̃ (some re)` (under
CPA) with its state abstracted (`simAbs`).

**Proof sketch.** Query by query: `Dec` is `⊥` on both sides (`chalHandler_impl_dec`,
`rImpl_dec_cpa`); a repeated challenge repeats `⟨y, h(M(a; ρ))⟩` (`chalHandler_impl_some`,
`rImpl_some`); a first challenge asks `a`, receives `h(M(a; ρ))` (`histImpl_eq`) and answers
`⟨Enc_pk(M(a; ρ̃); re), h(M(a; ρ))⟩` (`chalHandler_impl_none`, `simCt_input`,
`rImpl_none_eager`). -/
theorem simComp_abs (pk sk : List Bool) (ρ ρ' : samp.Coins n) (re : S.enc.Coins n) (i : Fin 2)
    (x : (bitSpecAt (snmDin S pl) (snmDout S hl) n).dom i)
    (s : Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (pl.eval n) → Bool))) :
    ((histImpl S samp pl hl hist n ρ).comp ((chalHandler (simParams S samp pl hl r sl)).impl n
        (pairEncode pk (samp.advice n))
        (seedEquiv (simParams_seedLen_handler S samp pl hl r sl) n (ρ', re))))
        i x (simAbs S samp pl hl hist r sl n ρ s) =
      (rImpl S .cpa true samp pl hl hist n pk sk ρ ρ' (some re) i x s).bind
        fun p => .pure (p.1, simAbs S samp pl hl hist r sl n ρ p.2) := by
  rw [QueryImpl.comp_apply]
  match i, x, s with
  | 0, x, none =>
    rw [simAbs_none, chalHandler_impl_dec, simulate_pure, OracleComp.pure_bind, rImpl_dec_cpa,
      OracleComp.pure_bind, simAbs_none]
  | 0, x, some (y, a) =>
    rw [simAbs_some, chalHandler_impl_dec, simulate_pure, OracleComp.pure_bind, rImpl_dec_cpa,
      OracleComp.pure_bind, simAbs_some]
  | 1, x, some (y, a) =>
    rw [simAbs_some, chalHandler_impl_some, simulate_pure, OracleComp.pure_bind, rImpl_some,
      OracleComp.pure_bind, simAbs_some]
  | 1, x, none =>
    have hxl : (List.ofFn x).length = pl.eval n := by
      rw [List.length_ofFn]
      show (snmDin S pl 1).eval n = _
      rw [snmDin_one]
    have hq : ∀ (s' : List Bool) (L : List Bool),
        (simParams S samp pl hl r sl).qry
          (InteractiveHandler.input n (pairEncode pk (samp.advice n))
          (List.ofFn (seedEquiv (simParams_seedLen_handler S samp pl hl r sl) n (ρ', re))) s'
          (1 : Fin 2) (List.ofFn x) L) = List.ofFn (padFin (pl.eval n) (List.ofFn x)) := by
      intro s' L
      rw [simParams_qry, (fields_input (k := 2) n _ _ s' 1 _ L).1,
        (fields_input (k := 2) n _ _ s' 1 _ L).2.2.2.2.2.1, List.length_replicate,
        ofFn_padFin_eq_padL]
    have hH : ∀ (s' q : List Bool) (y : Fin (hl.eval n) → Bool),
        (simParams S samp pl hl r sl).ansH
          (InteractiveHandler.input n (pairEncode pk (samp.advice n))
          (List.ofFn (seedEquiv (simParams_seedLen_handler S samp pl hl r sl) n (ρ', re))) s'
          (1 : Fin 2) (List.ofFn x) (pairEncode (pairEncode (List.replicate 0 true)
            (pairEncode q (List.ofFn y))) [])) = List.ofFn y := by
      intro s' q y
      rw [simParams_ansH, (fields_input (k := 2) n _ _ s' 1 _ _).1, List.length_replicate,
        rdAns_input, EnsembleLemmas.padL_eq]
      exact List.take_left' List.length_ofFn
    rw [simAbs_none, chalHandler_impl_none, simulate_query, histImpl_eq, OracleComp.pure_bind,
      simulate_pure, OracleComp.pure_bind, rImpl_none_eager, OracleComp.pure_bind, simAbs_some,
      if_pos rfl]
    simp only [simParams_j, simParams_ansY, Fin.val_zero, hq, hH, simCt_input, Option.getD_none,
      padFin_ofFn (padFin (pl.eval n) (List.ofFn x)),
      padFin_ofFn (encWith S n pk (drawWith samp (S.msgLen.eval n) n
        (padFin (pl.eval n) (List.ofFn x)) ρ') re),
      padFin_ofFn (histWith hist (hl.eval n) (drawWith samp (S.msgLen.eval n) n
        (padFin (pl.eval n) (List.ofFn x)) ρ))]

/-- **The ideal view of the simulator's output is the hybrid's view of `A`'s output:** for `A`'s
output `a` (`r·ctLen + sl` bits) and the hybrid's final state `s`, `idealView` of the simulator's
output (flags from the abstracted state) with the history oracle's state is `realView` of `a` and
`s`.

**Proof sketch.** Entry `i` of the output is `flagF ⟨1^n, st⟩ c_i` (`chunkAt_flatten_append`), whose
flag is `[c_i = y]` for the recorded `y` and `false` without a challenge (`headD_ofFn_chalState`,
`ofFn_chalState_some`), as `realView`'s copy test; `σ` is the tail (`drop_flatten_append`). -/
theorem idealView_simOut (sk : List Bool) (ρ : samp.Coins n)
    (s : Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (pl.eval n) → Bool))) (a : List Bool)
    (ha : a.length = r.eval n * S.ctLen.eval n + sl.eval n) :
    idealView S samp pl n (r.eval n) sk ρ (List.ofFn (padFin
        ((chalHandler (simParams S samp pl hl r sl)).outLen.eval n)
        (simOutL S r n (List.ofFn (simAbs S samp pl hl hist r sl n ρ s).1) a)))
        (simAbs S samp pl hl hist r sl n ρ s).2 =
      realView S samp pl n (r.eval n) sk ρ a s := by
  set st := List.ofFn (simAbs S samp pl hl hist r sl n ρ s).1 with hst
  have hc : ∀ i < r.eval n, (chunkAt (S.ctLen.eval n) i a).length = S.ctLen.eval n := fun i hi =>
    length_chunkAt _ _ _ (by
      rw [ha]
      have := Nat.mul_le_mul_right (S.ctLen.eval n) (show i + 1 ≤ r.eval n from hi)
      omega)
  have hg : ∀ i < r.eval n, (flagF S (pairEncode (List.replicate n true) st)
      (chunkAt (S.ctLen.eval n) i a)).length = S.ctLen.eval n + 1 := fun i hi => by
    rw [length_flagF, hc i hi]
  have hlen : (simOutL S r n st a).length =
      (chalHandler (simParams S samp pl hl r sl)).outLen.eval n := by
    rw [simParams_outLen_eval, simOutL_eq, List.length_append, List.length_drop, ha,
      length_flatten_map_range (S.ctLen.eval n + 1) _ _ hg, Nat.mul_add, Nat.mul_one]
    omega
  rw [ofFn_padFin_of_length hlen, simAbs_snd, idealView_eq, realView_eq, simOutL_eq,
    drop_flatten_append _ _ _ hg]
  congr 3
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  rw [chunkAt_flatten_append _ _ _ hg _ _ hi, flagF_eq, List.headD_cons, List.tail_cons,
    pairSndD_pairEncode, pairFstD_pairEncode, List.length_replicate]
  congr 1
  cases s with
  | none =>
    rw [hst, simAbs_none, headD_ofFn_chalState]
    simp
  | some ya =>
    obtain ⟨y, a'⟩ := ya
    rw [hst, simAbs_some, ofFn_chalState_some, List.headD_cons, List.drop_one, List.tail_cons,
      List.append_assoc, List.take_left' List.length_ofFn]
    simp only [Bool.true_and, Option.map_some, Option.some.injEq, decide_eq_decide]
    exact eq_comm

end Composite

/-! ### The ideal experiment is the hybrid `H_true` -/

section Ideal

variable (hist : List Bool → List Bool) (A : NUPPT) (q r sl : PolyExpr)

/-- **One run of the simulator is one run of the hybrid `H_true`:** let `Sim₀` be T2's machine of
the simulator's handler (coin bijection `φ`). For the input `⟨pk, M.advice n⟩`, coins
`φ (ρ̃ ‖ re, rA)` and budget `1`, the law of `F(idealView)` over `Sim₀`'s run against the history
oracle (coins `ρ`) is the law of `F(realView)` over `A`'s run (coins `rA`) against
`rImpl … true … ρ ρ̃ (some re)`.

**Proof sketch.** Transport the output length (`expect_toCompOn_outLen`); the run at budget `1` is
the run at T2's budget (`NUPPT.toCompOn_budget_eq`: the handler asks at most one query,
`chalHandler_costBoundedBy`, and its finalization none, `simFinish`); T2's equation; the
composition of the two simulations (`simulate_bind`, `simulate_comp`) is the hybrid's run through
the abstraction (`simulate_eq_of_abs`, `simComp_abs`); the views agree (`idealView_simOut`). -/
theorem simRun_eq (Sim₀ : NUPPT) (n : ℕ)
    (φ : (Fin ((chalHandler (simParams S samp pl hl r sl)).seedLen.eval n) → Bool) × A.Coins n ≃
      Sim₀.Coins n)
    (hφ : ∀ (z : List Bool)
      (ω : Fin ((chalHandler (simParams S samp pl hl r sl)).seedLen.eval n) → Bool)
      (rA : A.Coins n),
      (simulate ((chalHandler (simParams S samp pl hl r sl)).impl n z ω)
          (A.toCompOn (bitCodec (fun i => (snmDin S pl i).eval n) (fun i => (snmDout S hl i).eval n)
            (((r.mul S.ctLen).add sl).eval n)) n (q.eval n)
            ((chalHandler (simParams S samp pl hl r sl)).advInput n z ω) rA)
          ((chalHandler (simParams S samp pl hl r sl)).init n)).bind
          (fun res => (chalHandler (simParams S samp pl hl r sl)).finish n z ω res.2 res.1) =
        Sim₀.toCompOn (bitCodec (fun _ => pl.eval n) (fun _ => hl.eval n)
          ((chalHandler (simParams S samp pl hl r sl)).outLen.eval n)) n
          (q.eval n * (chalHandler (simParams S samp pl hl r sl)).perCall.eval n +
            (chalHandler (simParams S samp pl hl r sl)).finCall.eval n) z (φ (ω, rA)))
    (pk sk : List Bool) (ρ ρ' : samp.Coins n) (re : S.enc.Coins n) (rA : A.Coins n)
    (F : List Bool → ℝ) :
    ProbComp.expect (simulate (histImpl S samp pl hl hist n ρ)
        (Sim₀.toCompOn (bitCodec (fun _ => pl.eval n) (fun _ => hl.eval n)
          (r.eval n * (S.ctLen.eval n + 1) + sl.eval n)) n 1 (pairEncode pk (samp.advice n))
          (φ (seedEquiv (simParams_seedLen_handler S samp pl hl r sl) n (ρ', re), rA))) none)
        (fun p => F (idealView S samp pl n (r.eval n) sk ρ (List.ofFn p.1) p.2)) =
      ProbComp.expect (simulate (rImpl S .cpa true samp pl hl hist n pk sk ρ ρ' (some re))
        (A.toCompOn (bitCodec (fun i => (snmDin S pl i).eval n) (fun i => (snmDout S hl i).eval n)
          (r.eval n * S.ctLen.eval n + sl.eval n)) n (q.eval n) pk rA) none)
        (fun p => F (realView S samp pl n (r.eval n) sk ρ (List.ofFn p.1) p.2)) := by
  set ω := seedEquiv (simParams_seedLen_handler S samp pl hl r sl) n (ρ', re) with hω
  set z := pairEncode pk (samp.advice n) with hz
  have hdα : ((r.mul S.ctLen).add sl).eval n = r.eval n * S.ctLen.eval n + sl.eval n := by
    rw [PolyExpr.eval_add, PolyExpr.eval_mul]
  have hfin : ∀ (st : Fin ((chalHandler (simParams S samp pl hl r sl)).stateLen.eval n) → Bool)
      (a : Fin (((r.mul S.ctLen).add sl).eval n) → Bool),
      (chalHandler (simParams S samp pl hl r sl)).finish n z ω st a =
        .pure (padFin _ (simOutL S r n (List.ofFn st) (List.ofFn a))) :=
    fun st a => simFinish S samp pl hl r sl n z ω st a hdα
  -- The output length, the budget and T2.
  refine (expect_toCompOn_outLen _ Sim₀ n 1 z _ none
    (simParams_outLen_eval S samp pl hl r sl n).symm
    (fun p => F (idealView S samp pl n (r.eval n) sk ρ p.1 p.2))).trans ?_
  have hK : 1 ≤ q.eval n * (chalHandler (simParams S samp pl hl r sl)).perCall.eval n +
      (chalHandler (simParams S samp pl hl r sl)).finCall.eval n := by
    rw [chalHandler_finCall, simParams_finCall, PolyExpr.eval_const]
    omega
  rw [NUPPT.toCompOn_budget_eq Sim₀ _ n 1 _ z (φ (ω, rA)) hK (by
    rw [← hφ z ω rA, chalHandler_init]
    refine OracleComp.CostBoundedBy.bind (q₁ := 1) (q₂ := 0) (chalHandler_costBoundedBy _ n z ω _)
      fun res => ?_
    rw [hfin]
    exact OracleComp.costBoundedBy_pure _ _ _), ← hφ z ω rA, simParams_advInput, chalHandler_init,
    simulate_bind,
    simulate_comp, ← simAbs_none S samp pl hl hist r sl n ρ,
    Games.simulate_eq_of_abs _ _ _ (simComp_abs S samp pl hl hist r sl n pk sk ρ ρ' re),
    OracleComp.bind_assoc, OracleComp.bind_assoc]
  simp only [OracleComp.pure_bind, hfin, simulate_pure]
  rw [ProbComp.expect_bind]
  simp only [ProbComp.expect_pure]
  refine (expect_toCompOn_outLen _ A n (q.eval n) pk rA none hdα fun p =>
    F (idealView S samp pl n (r.eval n) sk ρ (List.ofFn (padFin _ (simOutL S r n
      (List.ofFn (simAbs S samp pl hl hist r sl n ρ p.2).1) p.1)))
      (simAbs S samp pl hl hist r sl n ρ p.2).2)).trans ?_
  refine congrArg _ (funext fun p => ?_)
  rw [idealView_simOut S samp pl hl hist r sl n sk ρ p.2 _ (by
    rw [List.length_ofFn])]

/-- **The simulator exists:** for the sampler `samp` (parameter length `pl`, history `hist` of
length `hl`), the adversary `A` and the polynomials `q`, `r`, `sl`, there is a machine `Sim` whose
ideal acceptance rate (budget `1`) is, for every distinguisher and every `n`, the hybrid `H_true`'s
(under CPA).

**Proof sketch.** `Sim₀` is T2's machine of the simulator's handler and `Sim` hard-wires
`M.advice n` as the second input component (`NUPPT.exists_withAdviceOn`). Reindex `Sim`'s coins as
`(ρ̃ ‖ re, rA)` (`coinsCongr`, `φ`, `seedEquiv`, `expect_sample_prod`), draw the hybrid's encryption
coins in advance (`expect_simulate_rImpl_eager`) and reorder the samples (`expect_sample_comm`);
pointwise this is `simRun_eq`. -/
theorem exists_simulator : ∃ Sim : NUPPT, ∀ (X : NUPPT) (n : ℕ),
    idealAcc S samp pl hl hist Sim (r.eval n) (sl.eval n) X n =
      hybAcc S .cpa true samp pl hl hist A (q.eval n) (r.eval n) (sl.eval n) X n := by
  obtain ⟨Sim₀, hT2⟩ := exists_interactiveHandlerMachine A q (snmDin S pl) (snmDout S hl)
    (fun _ : Fin 1 => pl) (fun _ => hl) ((r.mul S.ctLen).add sl)
    (chalHandler (simParams S samp pl hl r sl))
  obtain ⟨Sim, hc, hSim⟩ := NUPPT.exists_withAdviceOn Sim₀ samp.advice samp.adv
    samp.advice_length
  refine ⟨Sim, fun X n => ?_⟩
  obtain ⟨φ, hφ⟩ := hT2 n
  rw [idealAcc_eq, hybAcc_eq]
  refine congrArg _ (funext fun rg => congrArg _ (funext fun ρ => ?_))
  rw [← ProbComp.expect_sample_equiv (NUPPT.coinsCongr hc n)]
  simp only [hSim]
  rw [← ProbComp.expect_sample_equiv φ, ChallengeSim.expect_sample_prod,
    ← ProbComp.expect_sample_equiv (seedEquiv (simParams_seedLen_handler S samp pl hl r sl) n),
    ChallengeSim.expect_sample_prod]
  refine congrArg _ (funext fun ρ' => ?_)
  simp only [expect_simulate_rImpl_eager]
  refine (congrArg _ (funext fun re => congrArg _ (funext fun rA => congrArg _ (funext fun rX =>
    simRun_eq S samp pl hl hist A q r sl Sim₀ n φ hφ _ _ ρ ρ' re rA fun v =>
      if X.distinguisherL n v rX = true then 1 else 0)))).trans ?_
  rw [ProbComp.expect_sample_comm]
  refine congrArg _ (funext fun rA => ?_)
  rw [ProbComp.expect_sample_comm]

end Ideal

end TCSlib.Cryptography.Composability.NMSim
