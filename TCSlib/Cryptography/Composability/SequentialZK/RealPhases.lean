/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Composability.SequentialZK.Phases
import TCSlib.Cryptography.Composability.SequentialZK.WrappedVerifier

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Real phases against an arbitrary verifier

The real portion of a padded sequential phase is an original execution against the
fixed-tape phase verifier. The honest repeated prover's remaining replies are empty, while
the other party's filler replies are unrestricted. The phase coupling reuses the published
`Composability.exec_phase_of_moves` reader; this file does not repeat its execution induction.

## Main definitions

There are no new definitions.

## Main results

* `exec_snd_empty`: a suffix of empty prover replies appends only empty received messages.
* `exec_real_phase`: a real phase is coupled to the original prover and phase verifier.
* `exec_padded_real_phase`: the full padded phase appends the real messages and empty fillers.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §7.2.1, Theorem 175.1.
* [Gol01] O. Goldreich, *Foundations of Cryptography, Volume I: Basic Tools*, Cambridge
  University Press, 2001, §4.3.4.
-/

namespace TCSlib.Cryptography.SequentialZK

open Complexity Turing Composability

/-- For strategies `P,V`, orientation `vFirst`, fixed inputs/tapes `x,y,z,rP,rV`, and an
interval of `t` moves after `g`, if every active prover reply is empty, the verifier's
received history appends exactly as many empty messages as its length increases.
[PS10, Theorem 175.1, honest-prover fillers].
`(exec P V vFirst x y z rP rV (g + t)).2 = (exec P V vFirst x y z rP rV g).2 ++ List.replicate
((exec P V vFirst x y z rP rV (g + t)).2.length - (exec P V vFirst x y z rP rV g).2.length) []`.

**Proof sketch.** Induct on the interval length to express the new received history as the
old history followed by some number of empty messages. Verifier moves keep it fixed and
prover moves append one empty message. Taking lengths determines that number exactly.
The verifier's own replies are unrestricted throughout. -/
theorem exec_snd_empty (P V : Strategy) (vFirst : Bool) (x y z rP rV : List Bool) (g t : ℕ)
    (hEmpty : ∀ i < t, moverIsV vFirst (g + i) = false →
      P.next x y rP (exec P V vFirst x y z rP rV (g + i)).1 = []) :
    (exec P V vFirst x y z rP rV (g + t)).2 =
      (exec P V vFirst x y z rP rV g).2 ++ List.replicate
        ((exec P V vFirst x y z rP rV (g + t)).2.length -
          (exec P V vFirst x y z rP rV g).2.length) [] := by
  -- Each active prover move contributes one further empty slot.
  have hex : ∀ u, u ≤ t → ∃ a,
      (exec P V vFirst x y z rP rV (g + u)).2 =
        (exec P V vFirst x y z rP rV g).2 ++ List.replicate a [] := by
    intro u
    induction u with
    | zero =>
      intro _
      exact ⟨0, by rw [Nat.add_zero, List.replicate_zero, List.append_nil]⟩
    | succ u ih =>
      intro hu
      obtain ⟨a, ha⟩ := ih (by omega)
      rw [Nat.add_succ, exec_succ]
      by_cases hm : moverIsV vFirst (g + u) = true
      · simp only [hm, if_true]
        exact ⟨a, ha⟩
      · have hmf : moverIsV vFirst (g + u) = false := by simpa only [Bool.not_eq_true] using hm
        have he := hEmpty u (by omega) hmf
        simp only [hmf, Bool.false_eq_true, if_false]
        refine ⟨a + 1, ?_⟩
        rw [he, ha, List.replicate_add, List.replicate_one, List.append_assoc]
  -- The exact length difference identifies the number of appended slots.
  obtain ⟨a, ha⟩ := hex t le_rfl
  have hlen : (exec P V vFirst x y z rP rV (g + t)).2.length =
      (exec P V vFirst x y z rP rV g).2.length + a := by
    rw [ha, List.length_append, List.length_replicate]
  rw [hlen, Nat.add_sub_cancel_left]
  exact ha

/-- For a repeated prover `Pseq`, original prover `P`, arbitrary verifier `V`, fixed
inputs/tapes, and phase `j<q`, assume the padded next-message equation, recovery of the
global prover-move index, the phase-start prover-history length `j*k`, and the supplied
mover-period equation. For `t≤k`, the source histories at `2*k*j+t` are their phase-start
histories followed by the original execution of `P` on coin block `j` against
`phaseVerifier V` with `phaseAux z rV j` of the earlier verifier history.
[PS10, Theorem 175.1; Gol01, §4.3.4, real-phase coupling].

**Proof sketch.** Apply the published coupling theorem for active moves. Index recovery
gives phase `j` and position `t<k`, so the repeated prover uses exactly the original prover's
coin block and dropped phase history. The wrapped verifier prepends the earlier verifier
history; that history is a prefix of the reached source history by `exec_snd_take`. Its
reply is therefore exactly the source verifier's reply. The existing coupling theorem supplies
both transcript decompositions, without another induction over the real phase. -/
theorem exec_real_phase (Pseq P V : Strategy) (vFirst : Bool)
    (x y z rP rV : List Bool) (k q j : ℕ) (hj : j < q)
    (hPseq : ∀ hist : List (List Bool), Pseq.next x y rP hist =
      let idx := if vFirst then 2 * hist.length - 1 else 2 * hist.length
      if idx % (2 * k) < k then
        P.next x y (coinBlock (P.coinLen x.length) (idx / (2 * k)) rP)
          (hist.drop (idx / (2 * k) * k))
      else [])
    (hidx : ∀ n < 2 * k * q, moverIsV vFirst n = false →
      (if vFirst then 2 * (exec Pseq V vFirst x y z rP rV n).1.length - 1
        else 2 * (exec Pseq V vFirst x y z rP rV n).1.length) = n)
    (hstartP : (exec Pseq V vFirst x y z rP rV (2 * k * j)).1.length = j * k)
    (hturn : ∀ u < k, moverIsV vFirst (2 * k * j + u) = moverIsV vFirst u)
    {t : ℕ} (ht : t ≤ k) :
    (exec Pseq V vFirst x y z rP rV (2 * k * j + t)).1 =
      (exec Pseq V vFirst x y z rP rV (2 * k * j)).1 ++
        (exec P (phaseVerifier V) vFirst x y
          (phaseAux z rV j (exec Pseq V vFirst x y z rP rV (2 * k * j)).2)
          (coinBlock (P.coinLen x.length) j rP) [] t).1 ∧
    (exec Pseq V vFirst x y z rP rV (2 * k * j + t)).2 =
      (exec Pseq V vFirst x y z rP rV (2 * k * j)).2 ++
        (exec P (phaseVerifier V) vFirst x y
          (phaseAux z rV j (exec Pseq V vFirst x y z rP rV (2 * k * j)).2)
          (coinBlock (P.coinLen x.length) j rP) [] t).2 := by
  apply exec_phase_of_moves Pseq V P (phaseVerifier V) vFirst x y z rP rV y
    (phaseAux z rV j (exec Pseq V vFirst x y z rP rV (2 * k * j)).2)
    (coinBlock (P.coinLen x.length) j rP) [] (2 * k * j) k hturn ?_ ?_ ht
  · intro u hu hm
    have hbound : 2 * k * j + 2 * k ≤ 2 * k * q := by
      simpa only [Nat.mul_succ] using Nat.mul_le_mul_left (2 * k) (Nat.succ_le_of_lt hj)
    have hrec := hidx (2 * k * j + u) (by omega) ((hturn u hu).trans hm)
    have hmod : (2 * k * j + u) % (2 * k) = u := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    have hdiv : (2 * k * j + u) / (2 * k) = j := by
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt (by omega),
        Nat.zero_add]
    rw [hPseq]
    dsimp only
    rw [hrec, hmod, if_pos hu, hdiv, hstartP]
  · intro u _ _
    rw [phaseVerifier_next_phaseAux]
    apply congrArg (V.next x z rV)
    have htake := exec_snd_take Pseq V vFirst x y z rP rV (2 * k * j) u
    exact ((congrArg (fun h => h ++
      (exec Pseq V vFirst x y z rP rV (2 * k * j + u)).2.drop
        (exec Pseq V vFirst x y z rP rV (2 * k * j)).2.length) htake.symm).trans
          (List.take_append_drop _ _)).symm

/-- Under the repeated-prover shape/index/period hypotheses, suppose phase `j<q` starts
with both received histories of length `j*k`, ends with verifier history length `(j+1)*k`,
and the original wrapped real phase has `p` prover messages. Then its entire padded phase
appends those real messages followed by exactly `k-p` empty messages to the verifier's
earlier history. No condition is placed on the arbitrary verifier's filler replies.
[PS10, Theorem 175.1; Gol01, §4.3.4, the real padded-phase endpoint].

**Proof sketch.** The real phase is the original wrapped execution by `exec_real_phase`.
During each remaining move, index recovery puts every prover reply in the filler interval,
so the padded next-message reader returns `[]`. Apply `exec_snd_empty` to that suffix.
The supplied start, real-phase and end lengths show that exactly `k-p` further messages
were received. Combining the two prefix equalities gives the complete padded endpoint. -/
theorem exec_padded_real_phase (Pseq P V : Strategy) (vFirst : Bool)
    (x y z rP rV : List Bool) (k q j p : ℕ) (hj : j < q)
    (hPseq : ∀ hist : List (List Bool), Pseq.next x y rP hist =
      let idx := if vFirst then 2 * hist.length - 1 else 2 * hist.length
      if idx % (2 * k) < k then
        P.next x y (coinBlock (P.coinLen x.length) (idx / (2 * k)) rP)
          (hist.drop (idx / (2 * k) * k))
      else [])
    (hidx : ∀ n < 2 * k * q, moverIsV vFirst n = false →
      (if vFirst then 2 * (exec Pseq V vFirst x y z rP rV n).1.length - 1
        else 2 * (exec Pseq V vFirst x y z rP rV n).1.length) = n)
    (hstartP : (exec Pseq V vFirst x y z rP rV (2 * k * j)).1.length = j * k)
    (hstartV : (exec Pseq V vFirst x y z rP rV (2 * k * j)).2.length = j * k)
    (hendV : (exec Pseq V vFirst x y z rP rV (2 * k * (j + 1))).2.length = (j + 1) * k)
    (hlocal : (exec P (phaseVerifier V) vFirst x y
      (phaseAux z rV j (exec Pseq V vFirst x y z rP rV (2 * k * j)).2)
      (coinBlock (P.coinLen x.length) j rP) [] k).2.length = p)
    (hturn : ∀ u < k, moverIsV vFirst (2 * k * j + u) = moverIsV vFirst u) :
    (exec Pseq V vFirst x y z rP rV (2 * k * (j + 1))).2 =
      (exec Pseq V vFirst x y z rP rV (2 * k * j)).2 ++
        ((exec P (phaseVerifier V) vFirst x y
          (phaseAux z rV j (exec Pseq V vFirst x y z rP rV (2 * k * j)).2)
          (coinBlock (P.coinLen x.length) j rP) [] k).2 ++ List.replicate (k - p) []) := by
  have hreal := (exec_real_phase Pseq P V vFirst x y z rP rV k q j hj hPseq hidx
    hstartP hturn (t := k) le_rfl).2
  -- The recovered position is a filler position at every later prover move.
  have hfill := exec_snd_empty Pseq V vFirst x y z rP rV (2 * k * j + k) k
    (fun u hu hm => by
      have hbound : 2 * k * j + 2 * k ≤ 2 * k * q := by
        simpa only [Nat.mul_succ] using Nat.mul_le_mul_left (2 * k) (Nat.succ_le_of_lt hj)
      have hrec := hidx (2 * k * j + k + u) (by omega) hm
      have hmod : (2 * k * j + k + u) % (2 * k) = k + u := by
        rw [show 2 * k * j + k + u = (k + u) + (2 * k) * j by ring,
          Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
      rw [hPseq]
      dsimp only
      rw [hrec, hmod, if_neg (by omega)])
  -- Slot counts identify the empty suffix without restricting verifier filler replies.
  have hend : (2 * k * j + k) + k = 2 * k * (j + 1) := by ring
  rw [hend, hreal, List.length_append, hstartV, hlocal, hendV] at hfill
  have hcount : (j + 1) * k - (j * k + p) = k - p := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  rw [hcount] at hfill
  simpa only [List.append_assoc] using hfill

end TCSlib.Cryptography.SequentialZK
