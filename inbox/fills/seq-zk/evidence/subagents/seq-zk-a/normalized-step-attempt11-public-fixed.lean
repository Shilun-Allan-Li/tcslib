/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.ZeroKnowledge.Defs
import TCSlib.Cryptography.Composability.SequentialZK.ExecutionBounds
import TCSlib.Cryptography.Composability.SequentialZK.PhaseView
import TCSlib.Cryptography.Composability.SequentialZK.StatisticalPostprocess

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

* `normalizePhaseMsgs_viewV`: normalization fixes each bounded real zero-verifier view.
* `statClose_normalized_step`: a raw one-phase comparison for a verifier with zero coins
  remains valid after prefix extension, canonical bounded normalization, and empty padding.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §7.2.1, Theorem 175.1.
-/

namespace TCSlib.Cryptography.SequentialZK

open Complexity

/-- For protocol `ρ`, inputs `x,y,aux`, count `p`, cap `B`, zero verifier coin length,
a uniform `B` bound on prover messages, real received count `p`, and seed `r`, normalization
fixes the real received history:
`normalizePhaseMsgs x aux p B (ρ.viewV x y aux r).encode =
  (exec ρ.P ρ.V ρ.verifierFirst x y aux (List.ofFn r.1) [] (ρ.rounds.eval |x|)).2`.
[PS10, Theorem 175.1, normalization of a real wrapped phase].

**Proof sketch.** The verifier seed encodes an empty tape because its coin length is zero.
Read the real view and transcript through their published equations. The supplied count
and the public execution-message bound make this canonical real view a fixed point of the
bounded-slot normalizer. No simulator or statistical comparison is needed. -/
theorem normalizePhaseMsgs_viewV (ρ : Protocol) (x y aux : List Bool) (p B : ℕ)
    (hcoins : ρ.V.coinLen x.length = 0)
    (hP : ∀ r hist, (ρ.P.next x y r hist).length ≤ B)
    (hcount : ∀ rP : List Bool,
      (exec ρ.P ρ.V ρ.verifierFirst x y aux rP [] (ρ.rounds.eval x.length)).2.length = p)
    (r : ρ.ExecCoins ρ.P x) :
    normalizePhaseMsgs x aux p B (ρ.viewV x y aux r).encode =
      (exec ρ.P ρ.V ρ.verifierFirst x y aux (List.ofFn r.1) []
        (ρ.rounds.eval x.length)).2 := by
  -- The wrapper's verifier tape has no bits.
  have hrV : List.ofFn r.2 = [] :=
    List.eq_nil_of_length_eq_zero (by rw [List.length_ofFn, hcoins])
  rw [Protocol.viewV_eq, Protocol.transcriptWith_eq, hrV]
  -- The real count and message cap give the canonical normalization fixed point.
  exact normalizePhaseMsgs_of_encode x aux p B
    (exec ρ.P ρ.V ρ.verifierFirst x y aux (List.ofFn r.1) [] (ρ.rounds.eval x.length)).2
    (hcount (List.ofFn r.1))
    (exec_snd_bounded ρ.P ρ.V ρ.verifierFirst x y aux (List.ofFn r.1) [] B
      (ρ.rounds.eval x.length) (fun hist => hP (List.ofFn r.1) hist))

/-- For protocol `ρ`, simulator `S`, inputs `x,y,aux`, prefix `pre`, count `p`, bit cap `B`, and
error `δ`, suppose the verifier has zero coins, every prover message has at most `B` bits,
and every real received history has length `p`. A raw `δ`-close real-view/simulator pair then
gives `δ`-close prefix updates: the real update appends its received history and `k-p` empty
messages, while the simulated update appends `normalizePhaseMsgs x aux p B` of the output and
the same empty messages, where `k = ρ.rounds.eval |x|`. [PS10, Theorem 175.1].

**Proof sketch.** The zero-coin verifier tape is empty on every real seed. The execution bound
and supplied message count make each real view a fixed point of canonical normalization.
Apply the generic published postprocessing law with the normalized padded-prefix update
and this real fixed point. Its uniform first-projection reader removes the unused verifier
coin factor without changing the statistical bound. No simulator efficiency or output-shape
assumption is used. -/
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
  -- Each real view has the known metadata, empty tape, count and message-length bound.
  have hfixed (r : ρ.ExecCoins ρ.P x) :
      normalizePhaseMsgs x aux p B (ρ.viewV x y aux r).encode =
        (exec ρ.P ρ.V ρ.verifierFirst x y aux (List.ofFn r.1) []
          (ρ.rounds.eval x.length)).2 :=
    normalizePhaseMsgs_viewV ρ x y aux p B hcoins hP hcount r
  have hpoint (r : ρ.P.Coins x.length × ρ.V.Coins x.length) :
      pre ++ (normalizePhaseMsgs x aux p B (ρ.viewV x y aux r).encode ++
          List.replicate (ρ.rounds.eval x.length - p) []) =
        pre ++ ((exec ρ.P ρ.V ρ.verifierFirst x y aux (List.ofFn r.1) []
          (ρ.rounds.eval x.length)).2 ++ List.replicate (ρ.rounds.eval x.length - p) []) :=
    congrArg (fun msgs : List (List Bool) =>
      pre ++ (msgs ++ List.replicate (ρ.rounds.eval x.length - p) [])) (hfixed r)
  -- Instantiate the opaque generic law with every seed type and function explicit.
  with_reducible exact (TCSlib.Cryptography.Composability.statClose_map_fst
    (α := ρ.P.Coins x.length) (β := ρ.V.Coins x.length) (τ := S.Coins x.length)
    (γ := List Bool) (δ := List (List Bool))
    (fun r : ρ.P.Coins x.length × ρ.V.Coins x.length => (ρ.viewV x y aux r).encode)
    (S.simulate x aux : S.Coins x.length → List Bool)
    (fun raw : List Bool => pre ++ (normalizePhaseMsgs x aux p B raw ++
      List.replicate (ρ.rounds.eval x.length - p) []))
    (fun rP : ρ.P.Coins x.length => pre ++
      ((exec ρ.P ρ.V ρ.verifierFirst x y aux (List.ofFn rP) []
        (ρ.rounds.eval x.length)).2 ++ List.replicate (ρ.rounds.eval x.length - p) []))
    δ hclose hpoint)

end TCSlib.Cryptography.SequentialZK
