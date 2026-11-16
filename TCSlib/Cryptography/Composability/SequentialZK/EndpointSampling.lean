/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Asymptotic.CollectionsHelpers
import TCSlib.Cryptography.Asymptotic.Sampling
import TCSlib.Cryptography.Composability.SequentialZK.PaddedProverSpec
import TCSlib.Cryptography.Composability.SequentialZK.PrefixLaws

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Uniform tape reindexing at sequential-simulation endpoints

## Main definitions

* `coinTableEquiv` reads a tape of known length as a table of equal-size coin blocks.
* `coinBlocksEquiv` separates one verifier tape and a table of phase tapes.
* `PaddedProverSpec.realCoinsEquiv` reindexes real execution coins as verifier and phase coins.

## Main results

* `statClose_reindex` transfers closeness along supplied endpoint equivalences and readers.
* `PaddedProverSpec.realPrefix_eq_exec` identifies the real fold with the padded execution.
* `PaddedProverSpec.viewV_eq_realPrefix` gives the actual encoded real-view endpoint.
* `simulate_eq_simPrefix` identifies a simulator's tape-split endpoint with its typed fold.
* `statClose_view_endpoints` transfers a joint prefix comparison to the actual encoded views.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 175.1 (sequential repetition of zero knowledge).
-/

namespace TCSlib.Cryptography.SequentialZK

open Complexity

/-- For `hlen : m = q*c`, `coinTableEquiv hlen` reindexes `m` bits as `q` blocks of `c` bits,
using the canonical finite-index cast and `FunFamily.blocks`. -/
def coinTableEquiv {m q c : ℕ} (hlen : m = q * c) :
    (Fin m → Bool) ≃ (Fin q → Fin c → Bool) :=
  (Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)).trans (FunFamily.blocks q c)

/-- `coinTableEquiv hlen` is the finite-length cast followed by `FunFamily.blocks q c`.
`coinTableEquiv hlen = (Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)).trans (FunFamily.blocks
q c)`. -/
theorem coinTableEquiv_eq {m q c : ℕ} (hlen : m = q * c) :
    coinTableEquiv hlen =
      (Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)).trans (FunFamily.blocks q c) := rfl

/-- Block `i` of `r` is the encoding of block `i` of `coinTableEquiv hlen r`.
`coinBlock c i (List.ofFn r) = List.ofFn (coinTableEquiv hlen r i)`. -/
theorem coinTableEquiv_block {m q c : ℕ} (hlen : m = q * c) (r : Fin m → Bool)
    (i : Fin q) :
    coinBlock c i (List.ofFn r) = List.ofFn (coinTableEquiv hlen r i) := by
  let e := Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)
  have hword : List.ofFn (e r) = List.ofFn r := (List.ofFn_congr hlen r).symm
  have hblock := FunFamily.ofFn_blocks q c (e r) i
  rw [hword] at hblock
  exact (coinBlock_eq c i (List.ofFn r)).trans hblock.symm

/-- For `hlen : m = v+q*c`, `coinBlocksEquiv v q c hlen` reads the first `v` bits as a
verifier tape and the remaining `q*c` bits as the canonical table of `q` phase tapes. -/
def coinBlocksEquiv {m : ℕ} (v q c : ℕ) (hlen : m = v + q * c) :
    (Fin m → Bool) ≃ (Fin v → Bool) × (Fin q → Fin c → Bool) :=
  (Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)).trans
    ((splitCoins v (q * c)).trans
      (Equiv.prodCongr (Equiv.refl _) (FunFamily.blocks q c)))

/-- `coinBlocksEquiv v q c hlen` is the finite-length cast, then `splitCoins v (q*c)`,
then the product of the identity on verifier coins and `FunFamily.blocks q c`.
`coinBlocksEquiv v q c hlen = (Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)).trans
((splitCoins v (q * c)).trans (Equiv.prodCongr (Equiv.refl _) (FunFamily.blocks q c)))`. -/
theorem coinBlocksEquiv_eq {m : ℕ} (v q c : ℕ) (hlen : m = v + q * c) :
    coinBlocksEquiv v q c hlen =
      (Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)).trans
        ((splitCoins v (q * c)).trans
          (Equiv.prodCongr (Equiv.refl _) (FunFamily.blocks q c))) := rfl

/-- The verifier component of `coinBlocksEquiv v q c hlen r` encodes `(List.ofFn r).take v`.
`List.ofFn (coinBlocksEquiv v q c hlen r).1 = (List.ofFn r).take v`.
-/
theorem coinBlocksEquiv_fst_ofFn {m : ℕ} (v q c : ℕ) (hlen : m = v + q * c)
    (r : Fin m → Bool) :
    List.ofFn (coinBlocksEquiv v q c hlen r).1 = (List.ofFn r).take v := by
  let e := Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)
  have hword : List.ofFn (e r) = List.ofFn r := (List.ofFn_congr hlen r).symm
  have hfirst := ofFn_splitCoins_fst v (q * c) (e r)
  rw [hword] at hfirst
  exact hfirst

/-- Block `i` of the phase component of `coinBlocksEquiv v q c hlen r` encodes
`coinBlock c i ((List.ofFn r).drop v)`.
`coinBlock c i ((List.ofFn r).drop v) = List.ofFn ((coinBlocksEquiv v q c hlen r).2 i)`. -/
theorem coinBlocksEquiv_block {m : ℕ} (v q c : ℕ) (hlen : m = v + q * c)
    (r : Fin m → Bool) (i : Fin q) :
    coinBlock c i ((List.ofFn r).drop v) =
      List.ofFn ((coinBlocksEquiv v q c hlen r).2 i) := by
  let e := Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)
  have hword : List.ofFn (e r) = List.ofFn r := (List.ofFn_congr hlen r).symm
  have hblock := FunFamily.ofFn_blocks q c (splitCoins v (q * c) (e r)).2 i
  rw [ofFn_splitCoins_snd, hword] at hblock
  exact (coinBlock_eq c i ((List.ofFn r).drop v)).trans hblock.symm

/-- If `F,G` are `ε`-close, `eA : A' ≃ A` and `eB : B' ≃ B`, and the endpoint readers
are `F' a = F (eA a)` and `G' b = G (eB b)`, then `F',G'` are `ε`-close. -/
theorem statClose_reindex {A B A' B' O : Type*}
    [Fintype A] [Fintype B] [Fintype A'] [Fintype B']
    (F : A → O) (G : B → O) (F' : A' → O) (G' : B' → O)
    (eA : A' ≃ A) (eB : B' ≃ B) (ε : ℝ) (h : StatClose F G ε)
    (hF : ∀ a, F' a = F (eA a)) (hG : ∀ b, G' b = G (eB b)) :
    StatClose F' G' ε := by
  have hindexed := (h.comp_equiv_left eA).comp_equiv_right eB
  have hleft : (fun a => F (eA a)) = F' := funext fun a => (hF a).symm
  have hright : (fun b => G (eB b)) = G' := funext fun b => (hG b).symm
  rw [hleft, hright] at hindexed
  exact hindexed

namespace PaddedProverSpec

/-- For `h : PaddedProverSpec π ρ x q p`, `j≤q`, and raw prover tape `rP` whose first `j`
blocks are the typed coins `coins`, the real prefix is exactly the repeated verifier's
received history after `2*k*j` moves, where `k=π.rounds.eval |x|`.
[PS10, Theorem 175.1, real endpoint].

**Proof sketch.** Induct on `j`. The empty fold and zero-move execution both have empty
histories. At a successor, the real-fold reader appends one original phase and empty
fillers. The published padded-phase reader appends the same messages to the preceding
execution history. The induction hypothesis identifies the earlier prefixes, and the
supplied block equation identifies the last prover tape. -/
theorem realPrefix_eq_exec {π ρ : Protocol} {x : List Bool} {q p : ℕ}
    (h : PaddedProverSpec π ρ x q p) (V : Strategy) (y z rP rV : List Bool)
    (j : ℕ) (hj : j ≤ q) (coins : Fin j → π.P.Coins x.length)
    (hcoins : ∀ i : Fin j,
      coinBlock (π.P.coinLen x.length) i rP = List.ofFn (coins i)) :
    realPrefix π V x y z rV p j coins =
      (exec ρ.P V π.verifierFirst x y z rP rV (2 * π.rounds.eval x.length * j)).2 := by
  induction j with
  | zero => rw [realPrefix_zero]; simp only [Nat.mul_zero, exec_zero]
  | succ j ih =>
    have hprevious := ih (Nat.le_trans (Nat.le_succ j) hj)
      (fun i : Fin j => coins i.castSucc) (fun i => by
        simpa only [Fin.coe_castSucc] using hcoins i.castSucc)
    have hlast := hcoins (Fin.last j)
    simp only [Fin.val_last] at hlast
    have hphase := h.padded_phase V y z rP rV j (by omega)
    rw [realPrefix_succ, realStep_eq, hprevious, hphase, hlast]

/-- Reindex an actual `ρ.withV V` execution's coins as the verifier tape and the `q`
original prover tapes. The prover split uses only `h.prover_coinLen`; the verifier part
uses the published `withV_vCoinsEquiv`.
`(ρ.withV V).ExecCoins (ρ.withV V).P x ≃ V.Coins x.length × (Fin q → π.P.Coins x.length)`. -/
def realCoinsEquiv {π ρ : Protocol} {x : List Bool} {q p : ℕ}
    (h : PaddedProverSpec π ρ x q p) (V : Strategy) :
    (ρ.withV V).ExecCoins (ρ.withV V).P x ≃
      V.Coins x.length × (Fin q → π.P.Coins x.length) :=
  (Equiv.prodCongr
    (coinTableEquiv (by rw [Protocol.withV_P]; exact h.prover_coinLen))
    (ρ.withV_vCoinsEquiv V x.length)).trans (Equiv.prodComm _ _)

/-- `h.realCoinsEquiv V` applies `coinTableEquiv` to the prover coins and
`withV_vCoinsEquiv` to the verifier coins, then swaps the product coordinates.
`h.realCoinsEquiv V = (Equiv.prodCongr (coinTableEquiv (by rw [Protocol.withV_P]; exact
h.prover_coinLen)) (ρ.withV_vCoinsEquiv V x.length)).trans (Equiv.prodComm _ _)`. -/
theorem realCoinsEquiv_eq {π ρ : Protocol} {x : List Bool} {q p : ℕ}
    (h : PaddedProverSpec π ρ x q p) (V : Strategy) :
    h.realCoinsEquiv V =
      (Equiv.prodCongr
        (coinTableEquiv (by rw [Protocol.withV_P]; exact h.prover_coinLen))
        (ρ.withV_vCoinsEquiv V x.length)).trans (Equiv.prodComm _ _) := rfl

/-- The verifier component of `h.realCoinsEquiv V r` encodes the original verifier tape.
`List.ofFn (h.realCoinsEquiv V r).1 = List.ofFn r.2`. -/
theorem realCoinsEquiv_fst_ofFn {π ρ : Protocol} {x : List Bool} {q p : ℕ}
    (h : PaddedProverSpec π ρ x q p) (V : Strategy)
    (r : (ρ.withV V).ExecCoins (ρ.withV V).P x) :
    List.ofFn (h.realCoinsEquiv V r).1 = List.ofFn r.2 :=
  ρ.withV_vCoinsEquiv_ofFn V x.length r.2

/-- Block `i` of the repeated prover tape is block `i` of `h.realCoinsEquiv V r`.
`coinBlock (π.P.coinLen x.length) i (List.ofFn r.1) = List.ofFn ((h.realCoinsEquiv V r).2 i)`. -/
theorem realCoinsEquiv_block {π ρ : Protocol} {x : List Bool} {q p : ℕ}
    (h : PaddedProverSpec π ρ x q p) (V : Strategy)
    (r : (ρ.withV V).ExecCoins (ρ.withV V).P x) (i : Fin q) :
    coinBlock (π.P.coinLen x.length) i (List.ofFn r.1) =
      List.ofFn ((h.realCoinsEquiv V r).2 i) :=
  coinTableEquiv_block (by rw [Protocol.withV_P]; exact h.prover_coinLen) r.1 i

/-- The actual encoded verifier view in `ρ.withV V` is the canonical view of the jointly
reindexed verifier tape and real prefix. [PS10, Theorem 175.1, real-view endpoint].
`((ρ.withV V).viewV x y z r).encode = View.encode ⟨x, z, List.ofFn (h.realCoinsEquiv V r).1,
realPrefix π V x y z (List.ofFn (h.realCoinsEquiv V r).1) p q (h.realCoinsEquiv V r).2⟩`. -/
theorem viewV_eq_realPrefix {π ρ : Protocol} {x : List Bool} {q p : ℕ}
    (h : PaddedProverSpec π ρ x q p) (V : Strategy) (y z : List Bool)
    (r : (ρ.withV V).ExecCoins (ρ.withV V).P x) :
    ((ρ.withV V).viewV x y z r).encode =
      View.encode ⟨x, z, List.ofFn (h.realCoinsEquiv V r).1,
        realPrefix π V x y z (List.ofFn (h.realCoinsEquiv V r).1) p q
          (h.realCoinsEquiv V r).2⟩ := by
  rw [h.realCoinsEquiv_fst_ofFn V r]
  have hprefix := h.realPrefix_eq_exec V y z (List.ofFn r.1) (List.ofFn r.2) q le_rfl
    (h.realCoinsEquiv V r).2 (fun i => h.realCoinsEquiv_block V r i)
  rw [Protocol.viewV_withV, h.first, h.rounds_eval, hprefix]

end PaddedProverSpec

/-- Suppose `SQ`'s raw tape is split after `v` bits, and its published endpoint reader
outputs the canonical view of `phasePrefix` on the remaining phase tape. Reindexing those
coins by `coinBlocksEquiv` identifies that output with the canonical typed `simPrefix`.
[PS10, Theorem 175.1, simulator endpoint].
`SQ.simulate x z r = View.encode ⟨x, z, List.ofFn (coinBlocksEquiv v q (S.coinLen x.length) hlen
r).1, simPrefix S x z (List.ofFn (coinBlocksEquiv v q (S.coinLen x.length) hlen r).1) (k.eval
x.length) (B.eval x.length) (if verifierFirst …`. -/
theorem simulate_eq_simPrefix (S SQ : NUPPT) (k B : PolyExpr) (verifierFirst : Bool)
    (x z : List Bool) (q v : ℕ)
    (hlen : SQ.coinLen x.length = v + q * S.coinLen x.length)
    (hsim : ∀ r : SQ.Coins x.length, SQ.simulate x z r =
      View.encode ⟨x, z, (List.ofFn r).take v,
        phasePrefix S k B verifierFirst x z ((List.ofFn r).take v)
          ((List.ofFn r).drop v) q⟩) (r : SQ.Coins x.length) :
    SQ.simulate x z r =
      View.encode ⟨x, z, List.ofFn (coinBlocksEquiv v q (S.coinLen x.length) hlen r).1,
        simPrefix S x z (List.ofFn (coinBlocksEquiv v q (S.coinLen x.length) hlen r).1)
          (k.eval x.length) (B.eval x.length)
          (if verifierFirst then k.eval x.length / 2 else (k.eval x.length + 1) / 2) q
          (coinBlocksEquiv v q (S.coinLen x.length) hlen r).2⟩ := by
  have hprefix := simPrefix_eq_phasePrefix S k B verifierFirst x z
    ((List.ofFn r).take v) ((List.ofFn r).drop v) q
    (coinBlocksEquiv v q (S.coinLen x.length) hlen r).2
    (fun i => coinBlocksEquiv_block v q (S.coinLen x.length) hlen r i)
  rw [hsim r, coinBlocksEquiv_fst_ofFn, hprefix]

/-- Given the padded-prover contract and the raw split-tape reader for `SQ`, an
`ε`-closeness bound between joint `(verifier tape, real/simulated prefix)` samplers yields
`StatClose (fun r => ((ρ.withV V).viewV x y z r).encode) (SQ.simulate x z) ε`.
The supplied `hp` identifies the numeric real-message count with the simulator's count.
[PS10, Theorem 175.1, statistical endpoint transfer].

**Proof sketch.** Post-process the joint prefix samplers by canonical view encoding.
The padded-prover coin equivalence reindexes the real execution as its verifier tape and
phase prover coins; its published view reader identifies the real endpoint. The canonical
split/block equivalence reindexes `SQ`'s tape as its verifier and simulator phase coins;
the typed simulator endpoint reader identifies the other endpoint. Uniform probability
is invariant under both equivalences, so the original error is preserved exactly. -/
theorem statClose_view_endpoints {π ρ : Protocol} {x : List Bool} {q p : ℕ}
    (h : PaddedProverSpec π ρ x q p) (V : Strategy) (y z : List Bool)
    (S SQ : NUPPT) (B : PolyExpr)
    (hp : p = if π.verifierFirst then π.rounds.eval x.length / 2
      else (π.rounds.eval x.length + 1) / 2)
    (hlen : SQ.coinLen x.length = V.coinLen x.length + q * S.coinLen x.length)
    (hsim : ∀ r : SQ.Coins x.length, SQ.simulate x z r =
      View.encode ⟨x, z, (List.ofFn r).take (V.coinLen x.length),
        phasePrefix S π.rounds B π.verifierFirst x z
          ((List.ofFn r).take (V.coinLen x.length))
          ((List.ofFn r).drop (V.coinLen x.length)) q⟩)
    (ε : ℝ)
    (hprefix : StatClose
      (fun r : V.Coins x.length × (Fin q → π.P.Coins x.length) =>
        (r.1, realPrefix π V x y z (List.ofFn r.1) p q r.2))
      (fun r : V.Coins x.length × (Fin q → S.Coins x.length) =>
        (r.1, simPrefix S x z (List.ofFn r.1) (π.rounds.eval x.length)
          (B.eval x.length) p q r.2)) ε) :
    StatClose (fun r => ((ρ.withV V).viewV x y z r).encode) (SQ.simulate x z) ε := by
  let encodeState : V.Coins x.length × List (List Bool) → List Bool :=
    fun state => View.encode ⟨x, z, List.ofFn state.1, state.2⟩
  have hencoded : StatClose
      (fun r : V.Coins x.length × (Fin q → π.P.Coins x.length) =>
        View.encode ⟨x, z, List.ofFn r.1,
          realPrefix π V x y z (List.ofFn r.1) p q r.2⟩)
      (fun r : V.Coins x.length × (Fin q → S.Coins x.length) =>
        View.encode ⟨x, z, List.ofFn r.1,
          simPrefix S x z (List.ofFn r.1) (π.rounds.eval x.length)
            (B.eval x.length) p q r.2⟩) ε :=
    StatClose.map hprefix encodeState
  apply statClose_reindex _ _ _ _ (h.realCoinsEquiv V)
    (coinBlocksEquiv (V.coinLen x.length) q (S.coinLen x.length) hlen) ε hencoded
  · exact fun r => h.viewV_eq_realPrefix V y z r
  · intro r
    simpa only [hp] using
      simulate_eq_simPrefix S SQ π.rounds B π.verifierFirst x z q (V.coinLen x.length)
        hlen hsim r

end TCSlib.Cryptography.SequentialZK
