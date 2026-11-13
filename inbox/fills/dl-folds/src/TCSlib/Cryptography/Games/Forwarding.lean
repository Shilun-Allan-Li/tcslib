/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Efficiency

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Forwarding handlers, calls read on lists, and hard-wired input components

Generic tools for the reductions built with T2 (`Games.exists_interactiveHandlerMachine`) that
were first proved for [PS10, Theorems 174.8 and 175.9].

* **Calls read on lists.** The call lemmas of `Games.InteractiveHandler` (`impl_of_ret`,
  `impl_of_query`, `finish_of_ret`) take the answer and the state as fixed-length vectors. A round
  function usually builds them as lists `u`, `v` of the right lengths; the `_padFin` forms take
  those lists and return `padFin _ u`, `padFin _ v`.
* **The forwarding handler** (`fwdHandler`): a reduction that runs its adversary once against its
  own oracles forwards every query unchanged to the outer oracle of the same index, with one
  outer call per inner query and an empty state; only the finalization differs. Its answers are
  the outer oracle's (`fwdHandler_impl`). Its round reads the round input through the published
  readers `InteractiveHandler.rS`, `rI`, `rX`, `rL` and `rAns`.
* **Hard-wiring a second input component** (`NUPPT.exists_withAdviceOn`): a reduction that
  receives advice as the second component of its input is a machine with that advice built in.

## Main definitions

* `Games.fwdHandler`: the forwarding handler with a given seed, adversary input and finalization.

## Main results

* `Games.InteractiveHandler.impl_of_ret_padFin`, `impl_of_query_padFin`, `finish_of_ret_padFin`:
  the call lemmas with list-valued answers, states and outputs.
* `Games.fwdHandler_impl`: the forwarding handler forwards.
* `Complexity.NUPPT.exists_withAdviceOn`: hard-wiring a second input component.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §2.1 (non-uniform machines), Theorems 174.8 and 175.9 (book pp. 174–175).
-/

namespace TCSlib.Cryptography.Games

open Complexity Turing

variable {k : ℕ}

/-! ### Calls read on lists -/

namespace InteractiveHandler

section Calls

variable {k' : ℕ} {din dout : Fin k → PolyExpr} {din' dout' : Fin k' → PolyExpr}
  (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
  (ω : Fin (H.seedLen.eval n) → Bool)

/-- **A call that returns at once, on lists:** if the first round on the inner query `x` to
oracle `i` in state `s` returns `⟨[true], u ‖ v⟩` with `|u| = dout i`, `|v| = stateLen`, the call
answers `padFin _ u` with the new state `padFin _ v`, asking nothing (`impl_of_ret`, with
`ofFn_padFin_of_length`). -/
theorem impl_of_ret_padFin (i : Fin k) (x : Fin ((din i).eval n) → Bool)
    (s : Fin (H.stateLen.eval n) → Bool) (u v : List Bool) (hu : u.length = (dout i).eval n)
    (hv : v.length = H.stateLen.eval n)
    (hrun : H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x) []) =
      pairEncode [true] (u ++ v)) :
    H.impl n z ω i x s = .pure (padFin _ u, padFin _ v) :=
  H.impl_of_ret n z ω x s _ _ (by rw [ofFn_padFin_of_length hu, ofFn_padFin_of_length hv, hrun])

/-- **A call with one outer query, on lists:** if the first round asks the outer query `x'` to
oracle `j`, and the second round, with the answer `y` in the outer log, returns
`⟨[true], u y ‖ v y⟩` with `|u y| = dout i`, `|v y| = stateLen`, then (with `perCall ≥ 1`) the
call is `query j x' (fun y => pure (padFin _ (u y), padFin _ (v y)))` (`impl_of_query`, with
`ofFn_padFin_of_length`). -/
theorem impl_of_query_padFin (i : Fin k) (x : Fin ((din i).eval n) → Bool)
    (s : Fin (H.stateLen.eval n) → Bool) (j : Fin k') (x' : Fin ((din' j).eval n) → Bool)
    (u v : (Fin ((dout' j).eval n) → Bool) → List Bool)
    (hu : ∀ y, (u y).length = (dout i).eval n) (hv : ∀ y, (v y).length = H.stateLen.eval n)
    (hpc : 1 ≤ H.perCall.eval n)
    (hrun₀ : H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x) []) =
      pairEncode [false] (pairEncode (List.replicate j true) (List.ofFn x')))
    (hrun₁ : ∀ y, H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x)
      (pairEncode (pairEncode (List.replicate j true) (pairEncode (List.ofFn x') (List.ofFn y)))
        [])) = pairEncode [true] (u y ++ v y)) :
    H.impl n z ω i x s = .query j x' fun y => .pure (padFin _ (u y), padFin _ (v y)) :=
  H.impl_of_query n z ω x s j x' _ _ hpc hrun₀ fun y => by
    rw [ofFn_padFin_of_length (hu y), ofFn_padFin_of_length (hv y), hrun₁]

/-- **A finalization that returns at once, on lists:** if its first round returns `⟨[true], b⟩`
with `|b| = outLen(n)`, the finalization is `pure (padFin _ b)`, asking nothing
(`finish_of_ret`, with `ofFn_padFin_of_length`). -/
theorem finish_of_ret_padFin (s : Fin (H.stateLen.eval n) → Bool) {d : ℕ} (a : Fin d → Bool)
    (b : List Bool) (hb : b.length = H.outLen.eval n)
    (hrun : H.finRun (finInput n z (List.ofFn ω) (List.ofFn s) (List.ofFn a) []) =
      pairEncode [true] b) :
    H.finish n z ω s a = .pure (padFin _ b) :=
  H.finish_of_ret n z ω s a _ (by rw [ofFn_padFin_of_length hb, hrun])

end Calls

end InteractiveHandler

/-! ### The forwarding handler -/

open InteractiveHandler in
/-- **One forwarding round.** With an empty outer log, ask the outer oracle `i` the query `x`;
with the outer answer `y` in the log, return `y` and keep the state. -/
private def fwdRun (w : List Bool) : List Bool :=
  if decide (rL w = []) then pairEncode [false] (pairEncode (rI w) (rX w))
  else pairEncode [true] (rAns w ++ rS w)

open InteractiveHandler in
/-- The forwarding round is polynomial-time. -/
private theorem polyTimeComputable_fwdRun : PolyTimeComputable fwdRun :=
  polyTimeComputable_ite (polyTimeComputable_isNil.comp polyTimeComputable_rL)
    ((polyTimeComputable_const [false]).pairEncode
      (polyTimeComputable_rI.pairEncode polyTimeComputable_rX))
    ((polyTimeComputable_const [true]).pairEncode
      (polyTimeComputable_rAns.append polyTimeComputable_rS))

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

**Proof sketch.** `InteractiveHandler.impl_of_query` with `perCall = 1`: the call's first round
has an empty outer log (`rL_input`), so it asks the query `⟨1^i, x⟩` (`rI_input`, `rX_input`);
its second round reads the answer `y` from the one-entry log (`rAns_input`) and returns `y ‖ s`
(`rS_input`). -/
theorem fwdHandler_impl (n : ℕ) (z : List Bool)
    (ω : Fin ((fwdHandler din dout seedLen advIn advIn_poly outLen finCall finRun
      finRun_poly).seedLen.eval n) → Bool) (i : Fin k) (x : Fin ((din i).eval n) → Bool)
    (s : Fin ((fwdHandler din dout seedLen advIn advIn_poly outLen finCall finRun
      finRun_poly).stateLen.eval n) → Bool) :
    (fwdHandler din dout seedLen advIn advIn_poly outLen finCall finRun finRun_poly).impl n z ω
        i x s = .query i x fun y => .pure (y, s) := by
  refine InteractiveHandler.impl_of_query _ n z ω x s i x (fun y => y) (fun _ => s)
    (by rw [fwdHandler_perCall, PolyExpr.eval_const]) ?_ fun y => ?_
  · show fwdRun _ = _
    rw [fwdRun, InteractiveHandler.rL_input, InteractiveHandler.rI_input,
      InteractiveHandler.rX_input, if_pos (decide_eq_true rfl)]
  · show fwdRun _ = _
    rw [fwdRun, InteractiveHandler.rL_input, InteractiveHandler.rAns_input,
      InteractiveHandler.rS_input, if_neg (fun h => pairEncode_ne_nil _ _ (of_decide_eq_true h))]

end Forward

/-! ### Hard-wiring a second input component -/

/-- **Hard-wiring a second input component** [PS10, §2.1, implicit]: for a machine `B` and a
polynomially bounded family `β n` there is a machine `B'` with the same coins (`h`) whose
computation on the input `x` is `B`'s on `⟨x, β n⟩`, for every codec and budget:
`B'.toCompOn codec n q x (coinsCongr h n r) = B.toCompOn codec n q ⟨x, β n⟩ r`.

**Proof sketch.** `B₁ := NUPPT.exists_comp B` with the re-pairing
`⟨⟨x, L⟩, β⟩ ↦ ⟨⟨x, β⟩, L⟩`, then `B' := NUPPT.exists_withAdvice B₁ β`; on `⟨x, L⟩` (the input
and the encoded log) `B'` runs `B` on `⟨⟨x, β n⟩, L⟩`. -/
theorem _root_.Complexity.NUPPT.exists_withAdviceOn (B : NUPPT) (β : ℕ → List Bool)
    (b : PolyExpr) (hβ : ∀ n, (β n).length ≤ b.eval n) :
    ∃ (B' : NUPPT) (h : B.coins = B'.coins), ∀ (n : ℕ) {ι α : Type} {spec : OracleSpec ι}
      (codec : MachineCodec spec α) (q : ℕ) (x : List Bool) (r : B.Coins n),
      B'.toCompOn codec n q x (NUPPT.coinsCongr h n r) =
        B.toCompOn codec n q (pairEncode x (β n)) r := by
  have hpre : PolyTimeComputable fun w : List Bool =>
      pairEncode (pairEncode (pairFstD (pairFstD w)) (pairSndD w)) (pairSndD (pairFstD w)) :=
    ((polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD).pairEncode
      polyTimeComputable_pairSndD).pairEncode
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD)
  obtain ⟨B₁, hc₁, -, -, hB₁⟩ := NUPPT.exists_comp B hpre polyTimeComputable_id
  obtain ⟨B', hc', hB'⟩ := NUPPT.exists_withAdvice B₁ β b hβ
  refine ⟨B', (hc'.trans hc₁).symm, fun n ι α spec codec q x r => ?_⟩
  rw [NUPPT.toCompOn_eq, NUPPT.toCompOn_eq]
  congr 1
  funext hist
  rw [NUPPT.runAt_coinsCongr, hB', hB₁, NUPPT.runAt_eq]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, id_eq]

end TCSlib.Cryptography.Games
