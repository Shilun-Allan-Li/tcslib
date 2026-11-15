/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Composability.SequentialZK.ExecutionBounds
import TCSlib.Cryptography.Composability.SequentialZK.PhaseView

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Statistical comparison of a normalized phase update

The fixed-tape verifier used in sequential zero-knowledge composition [PS10, Theorem 175.1]
has no random bits of its own. Its real view has known metadata and bounded prover messages,
so canonical normalization fixes the real phase exactly. Mapping a raw statistical comparison
through the padded-prefix update therefore costs no additional error.

## Main definitions

There are no new definitions.

## Main results

* `statClose_normalized_step`: a raw one-phase comparison for a verifier with zero coins
  remains valid after prefix extension, canonical bounded normalization, and empty padding.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §7.2.1, Theorem 175.1.
-/

namespace TCSlib.Cryptography.SequentialZK

open Complexity

/-- For protocol `ρ`, simulator `S`, inputs `x,y,aux`, prefix `pre`, count `p`, bit cap `B`, and
error `δ`, suppose the verifier has zero coins, every prover message has at most `B` bits,
and every real received history has length `p`. A raw `δ`-close real-view/simulator pair then
gives `δ`-close prefix updates: the real update appends its received history and `k-p` empty
messages, while the simulated update appends `normalizePhaseMsgs x aux p B` of the output and
the same empty messages, where `k = ρ.rounds.eval |x|`. [PS10, Theorem 175.1].

**Proof sketch.** The zero-coin verifier tape is empty on every real seed. The execution bound
and supplied message count make each real view a fixed point of canonical normalization.
Pull each test back through normalized prefix extension and padding, rewrite its real
event pointwise by that fixed point, and remove the unused verifier coin factor by the public
uniform first-projection reader. No simulator efficiency or output-shape assumption is used. -/
theorem statClose_normalized_step (ρ : Protocol) (S : NUPPT) (x y aux : List Bool)
    (pre : List (List Bool)) (p B : ℕ) (δ : ℝ) (hcoins : ρ.V.coinLen x.length = 0)
    (hP : ∀ r hist, (ρ.P.next x y r hist).length ≤ B)
    (hcount : ∀ rP : List Bool,
      (exec ρ.P ρ.V ρ.verifierFirst x y aux rP [] (ρ.rounds.eval x.length)).2.length = p)
    (hclose : StatClose (fun r : ρ.ExecCoins ρ.P x => (ρ.viewV x y aux r).encode)
      (S.simulate x aux) δ) :
    StatClose
      (fun rP : ρ.P.Coins x.length => pre ++
        ((exec ρ.P ρ.V ρ.verifierFirst x y aux (List.ofFn rP) []
          (ρ.rounds.eval x.length)).2 ++ List.replicate (ρ.rounds.eval x.length - p) []))
      (fun rS : S.Coins x.length => pre ++
        (normalizePhaseMsgs x aux p B (S.simulate x aux rS) ++
          List.replicate (ρ.rounds.eval x.length - p) [])) δ := by
  dbg_trace "NormalizedStep.fixed.begin"
  -- Each real view has the known metadata, empty tape, count and message-length bound.
  have hfixed (r : ρ.ExecCoins ρ.P x) :
      normalizePhaseMsgs x aux p B (ρ.viewV x y aux r).encode =
        (exec ρ.P ρ.V ρ.verifierFirst x y aux (List.ofFn r.1) []
          (ρ.rounds.eval x.length)).2 := by
    dbg_trace "NormalizedStep.fixed.tape.begin"
    have hrV : List.ofFn r.2 = [] :=
      List.eq_nil_of_length_eq_zero (by rw [List.length_ofFn, hcoins])
    dbg_trace "NormalizedStep.fixed.tape.done"
    rw [Protocol.viewV_eq, Protocol.transcriptWith_eq, hrV]
    dbg_trace "NormalizedStep.fixed.application.begin"
    exact normalizePhaseMsgs_of_encode x aux p B
      (exec ρ.P ρ.V ρ.verifierFirst x y aux (List.ofFn r.1) [] (ρ.rounds.eval x.length)).2
      (hcount (List.ofFn r.1))
      (exec_snd_bounded ρ.P ρ.V ρ.verifierFirst x y aux (List.ofFn r.1) [] B
        (ρ.rounds.eval x.length) (fun hist => hP (List.ofFn r.1) hist))
  dbg_trace "NormalizedStep.fixed.done"
  refine (statClose_iff
    (fun rP : ρ.P.Coins x.length => pre ++
      ((exec ρ.P ρ.V ρ.verifierFirst x y aux (List.ofFn rP) []
        (ρ.rounds.eval x.length)).2 ++ List.replicate (ρ.rounds.eval x.length - p) []))
    (fun rS : S.Coins x.length => pre ++
      (normalizePhaseMsgs x aux p B (S.simulate x aux rS) ++
        List.replicate (ρ.rounds.eval x.length - p) [])) δ).2 ?_
  intro T
  dbg_trace "NormalizedStep.test.begin"
  have hrawT :
      |uprob (fun r : ρ.ExecCoins ρ.P x => T (pre ++
          (normalizePhaseMsgs x aux p B (ρ.viewV x y aux r).encode ++
            List.replicate (ρ.rounds.eval x.length - p) []))) -
        uprob (fun rS : S.Coins x.length => T (pre ++
          (normalizePhaseMsgs x aux p B (S.simulate x aux rS) ++
            List.replicate (ρ.rounds.eval x.length - p) [])))| ≤ δ :=
    hclose.abs_uprob_sub_le (fun raw : List Bool => T (pre ++
      (normalizePhaseMsgs x aux p B raw ++ List.replicate (ρ.rounds.eval x.length - p) [])))
  dbg_trace "NormalizedStep.rawtest.done"
  -- The real event is changed only at a concrete execution seed.
  have hpoint (r : ρ.ExecCoins ρ.P x) :
      T (pre ++ (normalizePhaseMsgs x aux p B (ρ.viewV x y aux r).encode ++
          List.replicate (ρ.rounds.eval x.length - p) [])) ↔
        T (pre ++ ((exec ρ.P ρ.V ρ.verifierFirst x y aux (List.ofFn r.1) []
          (ρ.rounds.eval x.length)).2 ++ List.replicate (ρ.rounds.eval x.length - p) [])) := by
    rw [hfixed r]
  dbg_trace "NormalizedStep.point.done"
  have hrealProduct :
      uprob (fun r : ρ.ExecCoins ρ.P x => T (pre ++
          (normalizePhaseMsgs x aux p B (ρ.viewV x y aux r).encode ++
            List.replicate (ρ.rounds.eval x.length - p) []))) =
        uprob (fun r : ρ.ExecCoins ρ.P x => T (pre ++
          ((exec ρ.P ρ.V ρ.verifierFirst x y aux (List.ofFn r.1) []
            (ρ.rounds.eval x.length)).2 ++ List.replicate (ρ.rounds.eval x.length - p) []))) :=
    OneWay.uprob_congr hpoint
  dbg_trace "NormalizedStep.product.done"
  -- The rewritten real event ignores its verifier coin factor.
  have hprojection :
      uprob (fun r : ρ.ExecCoins ρ.P x => T (pre ++
          ((exec ρ.P ρ.V ρ.verifierFirst x y aux (List.ofFn r.1) []
            (ρ.rounds.eval x.length)).2 ++ List.replicate (ρ.rounds.eval x.length - p) []))) =
        uprob (fun rP : ρ.P.Coins x.length => T (pre ++
          ((exec ρ.P ρ.V ρ.verifierFirst x y aux (List.ofFn rP) []
            (ρ.rounds.eval x.length)).2 ++ List.replicate (ρ.rounds.eval x.length - p) []))) :=
    uprob_fst (α := ρ.P.Coins x.length) (β := ρ.V.Coins x.length)
      (fun rP : ρ.P.Coins x.length => T (pre ++
        ((exec ρ.P ρ.V ρ.verifierFirst x y aux (List.ofFn rP) []
          (ρ.rounds.eval x.length)).2 ++ List.replicate (ρ.rounds.eval x.length - p) [])))
  dbg_trace "NormalizedStep.projection.done"
  rw [hrealProduct, hprojection] at hrawT
  dbg_trace "NormalizedStep.transport.done"
  exact hrawT

end TCSlib.Cryptography.SequentialZK
