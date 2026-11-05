/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Compose

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Sequential composition in the hybrid model: the phases of an honest execution

The phase lemmas of `H.compose ρ` (`Compose.lean`), the protocol of the composition theorem
[Gol04, §7.3.1, Theorem 7.3.3]; they let a reader check the layout without unfolding the
strategies. In an honest execution on common input `x`, inputs `zA`, `zB` and tapes `rA`,
`rB` (write `L = calls(|x|)`, `R = ρ.rounds(|x|)`, `M = main.rounds(|x|)`):
- **(a) The runs** (`compose_exec_run`, `compose_exec_runs`). Pair `q = R · j + p < L · R`
  carries the message of `ρ`'s move `p` in the honest execution of `ρ` on the inputs of call
  `j` and the `j`-th `ρ`-tapes (`runExec`), at its mover's position, and a filler `[]` at the
  other. So the run-`j` messages each party received are the transcript of that execution.
- **(b) The main phase** (`compose_exec_main`). After the runs and the leading filler, the
  messages are those of `main`'s honest execution on `⟨zA, aA⟩`, `⟨zB, aB⟩` and the `main`-tapes
  (`mainExec`), where `aA`, `aB` are the parties' outputs of the honest runs read at `G`'s
  output lengths (`answersRealA`, `answersRealB`).
- **(c) The outputs** (`compose_outP`, `compose_outV`). When `M ≥ 1`, each party's output is
  its output in that execution of `main`. With `M = 0` this fails (`Compose.lean`, on D8's
  output convention).

## Main definitions

* `HybridProtocol.runExec`, `runMsg`: the honest run `j` and the message of its move `p`.
* `HybridProtocol.slotFromA`, `slotFromB`: each party's message at a pair.
* `HybridProtocol.answersRealA`, `answersRealB`: the answers of an honest execution.
* `HybridProtocol.mainExec`: the main phase of an honest execution.

## Main results

* `HybridProtocol.compose_exec_run`, `compose_exec_runs`: phase lemma (a).
* `HybridProtocol.compose_exec_main`, `compose_exec_rounds`: phase lemma (b), and the complete
  execution.
* `HybridProtocol.compose_outP`, `compose_outV`: phase lemma (c); `compose_transcript`,
  `compose_viewP`, `compose_viewV`: the transcript and the views.

## References

* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*, Cambridge
  University Press, 2004, §7.3.1 (privacy reductions and a composition theorem), Theorem 7.3.3.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §4.4 (interactive protocols: executions, views, outputs; book pp. 114–116).
-/

namespace TCSlib.Cryptography.SecureComputation

open Complexity Turing TCSlib.Cryptography

open Compose

namespace HybridProtocol

/-! ### The phases of an honest execution -/

section Phases

variable {G : Functionality} (H : HybridProtocol G) (ρ : Protocol) (x zA zB rA rB : List Bool)

/-- **The honest run `j`** after `k` moves: the execution of `ρ` on the common input `x`, the
inputs of call `j` (`runInputA`, `runInputB`) and the `j`-th `ρ`-tapes of Alice's tape `rA` and
Bob's tape `rB`. -/
def runExec (j k : ℕ) : List (List Bool) × List (List Bool) :=
  exec ρ.P ρ.V ρ.verifierFirst x (H.runInputA x zA rA j) (H.runInputB x zB rB j)
    (runTape (H.main.P.coins.eval x.length) (ρ.P.coins.eval x.length) j rA)
    (runTape (H.main.V.coins.eval x.length) (ρ.V.coins.eval x.length) j rB) k

/-- The honest run `j` is `ρ`'s execution on the call inputs and the run tapes. -/
theorem runExec_eq (j k : ℕ) :
    H.runExec ρ x zA zB rA rB j k =
      exec ρ.P ρ.V ρ.verifierFirst x (H.runInputA x zA rA j) (H.runInputB x zB rB j)
        (runTape (H.main.P.coins.eval x.length) (ρ.P.coins.eval x.length) j rA)
        (runTape (H.main.V.coins.eval x.length) (ρ.V.coins.eval x.length) j rB) k := rfl

/-- **The message of `ρ`'s move `p` in the honest run `j`**. -/
def runMsg (j p : ℕ) : List Bool :=
  moveMsg ρ.P ρ.V ρ.verifierFirst x (H.runInputA x zA rA j) (H.runInputB x zB rB j)
    (runTape (H.main.P.coins.eval x.length) (ρ.P.coins.eval x.length) j rA)
    (runTape (H.main.V.coins.eval x.length) (ρ.V.coins.eval x.length) j rB) p

/-- The message of move `p` of run `j` is `moveMsg` of the honest run `j`. -/
theorem runMsg_eq (j p : ℕ) :
    H.runMsg ρ x zA zB rA rB j p =
      moveMsg ρ.P ρ.V ρ.verifierFirst x (H.runInputA x zA rA j) (H.runInputB x zB rB j)
        (runTape (H.main.P.coins.eval x.length) (ρ.P.coins.eval x.length) j rA)
        (runTape (H.main.V.coins.eval x.length) (ρ.V.coins.eval x.length) j rB) p := rfl

/-- **Bob's message at pair `q`** of an honest execution of `H.compose ρ` (`R = ρ.rounds(|x|)`):
`ρ`'s move `q % R` of run `q / R` if Bob makes it, and the filler `[]` otherwise. -/
def slotFromB (q : ℕ) : List Bool :=
  if moverIsV ρ.verifierFirst (q % ρ.rounds.eval x.length) then
    H.runMsg ρ x zA zB rA rB (q / ρ.rounds.eval x.length) (q % ρ.rounds.eval x.length)
  else []

/-- Bob's message at pair `q` is `ρ`'s move `q % R` of run `q / R` if his, `[]` otherwise. -/
theorem slotFromB_eq (q : ℕ) :
    H.slotFromB ρ x zA zB rA rB q =
      if moverIsV ρ.verifierFirst (q % ρ.rounds.eval x.length) then
        H.runMsg ρ x zA zB rA rB (q / ρ.rounds.eval x.length) (q % ρ.rounds.eval x.length)
      else [] := rfl

/-- **Alice's message at pair `q`**: `ρ`'s move `q % R` of run `q / R` if Alice makes it, and the
filler `[]` otherwise. -/
def slotFromA (q : ℕ) : List Bool :=
  if moverIsV ρ.verifierFirst (q % ρ.rounds.eval x.length) then []
  else H.runMsg ρ x zA zB rA rB (q / ρ.rounds.eval x.length) (q % ρ.rounds.eval x.length)

/-- Alice's message at pair `q` is `ρ`'s move `q % R` of run `q / R` if hers, `[]` otherwise. -/
theorem slotFromA_eq (q : ℕ) :
    H.slotFromA ρ x zA zB rA rB q =
      if moverIsV ρ.verifierFirst (q % ρ.rounds.eval x.length) then []
      else H.runMsg ρ x zA zB rA rB (q / ρ.rounds.eval x.length) (q % ρ.rounds.eval x.length) :=
  rfl

/-- **Alice's answers in an honest execution**: her outputs of the honest runs (`ρ.P.next` on
her complete run history), each padded or truncated to `G.outA(|x|)` bits, concatenated. -/
def answersRealA : List Bool :=
  (List.ofFn fun j : Fin (H.calls.eval x.length) =>
    List.ofFn (padFin (G.outA.eval x.length)
      (ρ.P.next x (H.runInputA x zA rA j)
        (runTape (H.main.P.coins.eval x.length) (ρ.P.coins.eval x.length) j rA)
        (H.runExec ρ x zA zB rA rB j (ρ.rounds.eval x.length)).1))).flatten

/-- Alice's answers in an honest execution are her padded outputs of the honest runs. -/
theorem answersRealA_eq :
    H.answersRealA ρ x zA zB rA rB =
      (List.ofFn fun j : Fin (H.calls.eval x.length) =>
        List.ofFn (padFin (G.outA.eval x.length)
          (ρ.P.next x (H.runInputA x zA rA j)
            (runTape (H.main.P.coins.eval x.length) (ρ.P.coins.eval x.length) j rA)
            (H.runExec ρ x zA zB rA rB j (ρ.rounds.eval x.length)).1))).flatten := rfl

/-- **Bob's answers in an honest execution**: his outputs of the honest runs, each padded or
truncated to `G.outB(|x|)` bits, concatenated. -/
def answersRealB : List Bool :=
  (List.ofFn fun j : Fin (H.calls.eval x.length) =>
    List.ofFn (padFin (G.outB.eval x.length)
      (ρ.V.next x (H.runInputB x zB rB j)
        (runTape (H.main.V.coins.eval x.length) (ρ.V.coins.eval x.length) j rB)
        (H.runExec ρ x zA zB rA rB j (ρ.rounds.eval x.length)).2))).flatten

/-- Bob's answers in an honest execution are his padded outputs of the honest runs. -/
theorem answersRealB_eq :
    H.answersRealB ρ x zA zB rA rB =
      (List.ofFn fun j : Fin (H.calls.eval x.length) =>
        List.ofFn (padFin (G.outB.eval x.length)
          (ρ.V.next x (H.runInputB x zB rB j)
            (runTape (H.main.V.coins.eval x.length) (ρ.V.coins.eval x.length) j rB)
            (H.runExec ρ x zA zB rA rB j (ρ.rounds.eval x.length)).2))).flatten := rfl

/-- **The main phase of an honest execution** after `m` moves: the execution of `main` on the
private inputs `⟨zA, Alice's answers⟩` and `⟨zB, Bob's answers⟩` and the `main`-tapes (the first
`main.P.coins(|x|)` bits of `rA`, the first `main.V.coins(|x|)` bits of `rB`). -/
def mainExec (m : ℕ) : List (List Bool) × List (List Bool) :=
  exec H.main.P H.main.V H.main.verifierFirst x (pairEncode zA (H.answersRealA ρ x zA zB rA rB))
    (pairEncode zB (H.answersRealB ρ x zA zB rA rB)) (rA.take (H.main.P.coins.eval x.length))
    (rB.take (H.main.V.coins.eval x.length)) m

/-- The main phase is `main`'s execution on the inputs paired with the honest answers. -/
theorem mainExec_eq (m : ℕ) :
    H.mainExec ρ x zA zB rA rB m =
      exec H.main.P H.main.V H.main.verifierFirst x
        (pairEncode zA (H.answersRealA ρ x zA zB rA rB))
        (pairEncode zB (H.answersRealB ρ x zA zB rA rB)) (rA.take (H.main.P.coins.eval x.length))
        (rB.take (H.main.V.coins.eval x.length)) m := rfl

/-! #### The run phase -/

/-- Division by `R` of `R·j + p` with `p < R`. -/
private theorem mul_add_div_of_lt {R j p : ℕ} (hp : p < R) : (R * j + p) / R = j := by
  rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hp, Nat.add_zero]

/-- Remainder modulo `R` of `R·j + p` with `p < R`. -/
private theorem mul_add_mod_of_lt {R j p : ℕ} (hp : p < R) : (R * j + p) % R = p := by
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hp]

/-- The pairs of run `j < L` come before pair `L·R`. -/
private theorem mul_add_le_of_lt {R j L : ℕ} (hj : j < L) : R * j + R ≤ L * R := by
  have := Nat.mul_le_mul_right R (Nat.succ_le_of_lt hj)
  rw [Nat.succ_mul, Nat.mul_comm j R] at this
  exact this

/-- Bob's message at pair `R·j + p`, `p < R`, is `ρ`'s move `p` of run `j` if his. -/
theorem slotFromB_mul_add {j p : ℕ} (hp : p < ρ.rounds.eval x.length) :
    H.slotFromB ρ x zA zB rA rB (ρ.rounds.eval x.length * j + p) =
      if moverIsV ρ.verifierFirst p then H.runMsg ρ x zA zB rA rB j p else [] := by
  rw [slotFromB_eq, mul_add_div_of_lt hp, mul_add_mod_of_lt hp]

/-- Alice's message at pair `R·j + p`, `p < R`, is `ρ`'s move `p` of run `j` if hers. -/
theorem slotFromA_mul_add {j p : ℕ} (hp : p < ρ.rounds.eval x.length) :
    H.slotFromA ρ x zA zB rA rB (ρ.rounds.eval x.length * j + p) =
      if moverIsV ρ.verifierFirst p then [] else H.runMsg ρ x zA zB rA rB j p := by
  rw [slotFromA_eq, mul_add_div_of_lt hp, mul_add_mod_of_lt hp]

/-- **Alice reads run `j` from the pairs**: if `hist` holds Bob's honest messages at the pairs
before `R·j + p` (`p ≤ R`), her run-`j` history is the one of the honest run `j` after `p`
moves. -/
theorem slotMsgs_runFst {j p : ℕ} (hp : p ≤ ρ.rounds.eval x.length) {hist : List (List Bool)}
    (hh : ∀ i < ρ.rounds.eval x.length * j + p, hist.getD i [] = H.slotFromB ρ x zA zB rA rB i) :
    slotMsgs (moverIsV ρ.verifierFirst) (ρ.rounds.eval x.length * j) p hist =
      (H.runExec ρ x zA zB rA rB j p).1 := by
  rw [slotMsgs_eq_map (f := H.runMsg ρ x zA zB rA rB j), runExec_eq, exec_eq_map]
  · rfl
  · intro p' hp' hsel
    rw [hh _ (by omega), slotFromB_mul_add H ρ x zA zB rA rB (by omega), if_pos hsel]

/-- **Bob reads run `j` from the pairs**: if `hist` holds Alice's honest messages at the pairs
before `R·j + p` (`p ≤ R`), his run-`j` history is the one of the honest run `j` after `p`
moves. -/
theorem slotMsgs_runSnd {j p : ℕ} (hp : p ≤ ρ.rounds.eval x.length) {hist : List (List Bool)}
    (hh : ∀ i < ρ.rounds.eval x.length * j + p, hist.getD i [] = H.slotFromA ρ x zA zB rA rB i) :
    slotMsgs (fun p' => !moverIsV ρ.verifierFirst p') (ρ.rounds.eval x.length * j) p hist =
      (H.runExec ρ x zA zB rA rB j p).2 := by
  rw [slotMsgs_eq_map (f := H.runMsg ρ x zA zB rA rB j), runExec_eq, exec_eq_map]
  · rfl
  · intro p' hp' hsel
    rw [Bool.not_eq_true'] at hsel
    rw [hh _ (by omega), slotFromA_mul_add H ρ x zA zB rA rB (by omega), hsel]
    rfl

/-- **Phase lemma, the run phase**: after the first `q ≤ L·R` pairs of an honest execution of
`H.compose ρ` (`L = calls(|x|)`, `R = ρ.rounds(|x|)`), Alice has received Bob's messages
`slotFromB 0, …, slotFromB (q − 1)` and Bob Alice's `slotFromA 0, …, slotFromA (q − 1)`: at
each pair, `ρ`'s move of the honest run on the call inputs, or a filler.

**Proof sketch.** Induction on `q`. At pair `q < L·R` (run `j = q / R`, position `p = q % R`):
1. Alice moves at `2q` (`moverIsV_false_two_mul`), having received `q` messages, so she computes
   `j` and `p`. If `ρ`'s mover `p` is Bob she sends `[]`. Otherwise her run-`j` history read from
   the pairs is the honest run's after `p` moves (`slotMsgs_runFst`, by the induction
   hypothesis), so she sends `ρ`'s move `p` (`moveMsg`).
2. Bob moves at `2q + 1` having received `q + 1` messages, so he computes the same `j`, `p`, and
   symmetrically sends `ρ`'s move `p` or `[]` (`slotMsgs_runSnd`). -/
theorem compose_exec_run {q : ℕ} (hq : q ≤ H.calls.eval x.length * ρ.rounds.eval x.length) :
    exec (H.compose ρ).P (H.compose ρ).V (H.compose ρ).verifierFirst x zA zB rA rB (2 * q) =
      ((List.range q).map (H.slotFromB ρ x zA zB rA rB),
        (List.range q).map (H.slotFromA ρ x zA zB rA rB)) := by
  induction q with
  | zero => rfl
  | succ q ih =>
    have hq' : q < H.calls.eval x.length * ρ.rounds.eval x.length := by omega
    have hR : 0 < ρ.rounds.eval x.length := by
      rcases Nat.eq_zero_or_pos (ρ.rounds.eval x.length) with h | h
      · rw [h, Nat.mul_zero] at hq'
        omega
      · exact h
    have hpR : q % ρ.rounds.eval x.length < ρ.rounds.eval x.length := Nat.mod_lt _ hR
    have hqd : ρ.rounds.eval x.length * (q / ρ.rounds.eval x.length) +
        q % ρ.rounds.eval x.length = q := Nat.div_add_mod q _
    -- Alice's move at `2q`
    have hA : (H.compose ρ).P.next x zA rA ((List.range q).map (H.slotFromB ρ x zA zB rA rB)) =
        H.slotFromA ρ x zA zB rA rB q := by
      rw [compose_P, composeP_next, List.length_map, List.length_range, if_pos hq',
        slotFromA_eq]
      by_cases hm : moverIsV ρ.verifierFirst (q % ρ.rounds.eval x.length) = true
      · rw [if_pos hm, if_pos hm]
      · rw [if_neg hm, if_neg hm, runNextA_eq, runMsg_eq, moveMsg_eq, if_neg hm,
          slotMsgs_runFst H ρ x zA zB rA rB hpR.le, runExec_eq]
        intro i hi
        rw [getD_map_range (by omega)]
    -- Bob's move at `2q + 1`
    have hB : (H.compose ρ).V.next x zB rB
        ((List.range q).map (H.slotFromA ρ x zA zB rA rB) ++ [H.slotFromA ρ x zA zB rA rB q]) =
        H.slotFromB ρ x zA zB rA rB q := by
      have hlen : ((List.range q).map (H.slotFromA ρ x zA zB rA rB) ++
          [H.slotFromA ρ x zA zB rA rB q]).length - 1 = q := by
        rw [List.length_append, List.length_map, List.length_range, List.length_singleton,
          Nat.add_sub_cancel]
      rw [compose_V, composeV_next, hlen, if_pos hq', slotFromB_eq]
      by_cases hm : moverIsV ρ.verifierFirst (q % ρ.rounds.eval x.length) = true
      · rw [if_pos hm, if_pos hm, runNextB_eq, runMsg_eq, moveMsg_eq, if_pos hm,
          slotMsgs_runSnd H ρ x zA zB rA rB hpR.le, runExec_eq]
        intro i hi
        rw [getD_append_left (by rw [List.length_map, List.length_range]; omega),
          getD_map_range (by omega)]
      · rw [if_neg hm, if_neg hm]
    rw [show 2 * (q + 1) = 2 * q + 1 + 1 by ring, exec_succ, exec_succ, ih hq'.le]
    simp only [compose_verifierFirst, moverIsV_false_two_mul, moverIsV_false_two_mul_add_one,
      if_true, Bool.false_eq_true, if_false]
    rw [hA, hB, List.range_succ, List.map_append, List.map_append, List.map_singleton,
      List.map_singleton]

/-- **Phase lemma (a), the runs**: after the run phase of an honest execution of `H.compose ρ`
(`L·2R` moves), for every run `j < L`, the run-`j` messages Alice received (read at the pairs
where `ρ`'s mover is Bob) and those Bob received (at the pairs where `ρ`'s mover is Alice) are
the transcript of the honest execution of `ρ` on the inputs of call `j` and the `j`-th tapes
(`runExec`, `runInputA_of_lt`).

**Proof sketch.** By `compose_exec_run` with `q = L·R`, the received lists hold the honest pair
messages; the pairs of run `j` come before `L·R`, so `slotMsgs_runFst` and `slotMsgs_runSnd`
read the honest run `j` from them. -/
theorem compose_exec_runs {j : ℕ} (hj : j < H.calls.eval x.length) :
    slotMsgs (moverIsV ρ.verifierFirst) (ρ.rounds.eval x.length * j) (ρ.rounds.eval x.length)
        (exec (H.compose ρ).P (H.compose ρ).V (H.compose ρ).verifierFirst x zA zB rA rB
          (H.calls.eval x.length * (2 * ρ.rounds.eval x.length))).1 =
      (H.runExec ρ x zA zB rA rB j (ρ.rounds.eval x.length)).1 ∧
    slotMsgs (fun p => !moverIsV ρ.verifierFirst p) (ρ.rounds.eval x.length * j)
        (ρ.rounds.eval x.length)
        (exec (H.compose ρ).P (H.compose ρ).V (H.compose ρ).verifierFirst x zA zB rA rB
          (H.calls.eval x.length * (2 * ρ.rounds.eval x.length))).2 =
      (H.runExec ρ x zA zB rA rB j (ρ.rounds.eval x.length)).2 := by
  have hjR := mul_add_le_of_lt (R := ρ.rounds.eval x.length) hj
  rw [show H.calls.eval x.length * (2 * ρ.rounds.eval x.length) =
    2 * (H.calls.eval x.length * ρ.rounds.eval x.length) by ring,
    compose_exec_run H ρ x zA zB rA rB le_rfl]
  refine ⟨slotMsgs_runFst H ρ x zA zB rA rB le_rfl fun i hi => ?_,
    slotMsgs_runSnd H ρ x zA zB rA rB le_rfl fun i hi => ?_⟩
  · exact getD_map_range (by omega)
  · exact getD_map_range (by omega)

/-! #### The main phase -/

/-- Alice's answers read from a history that starts with Bob's honest run messages are her
honest answers. -/
theorem answersFromA_run (Y : List (List Bool)) :
    H.answersFromA ρ x zA rA ((List.range (H.calls.eval x.length * ρ.rounds.eval x.length)).map
      (H.slotFromB ρ x zA zB rA rB) ++ Y) = H.answersRealA ρ x zA zB rA rB := by
  rw [answersFromA_eq, answersRealA_eq]
  refine congrArg List.flatten (congrArg List.ofFn (funext fun j => ?_))
  have hjR := mul_add_le_of_lt (R := ρ.rounds.eval x.length) j.2
  rw [runNextA_eq, slotMsgs_runFst H ρ x zA zB rA rB le_rfl]
  intro i hi
  rw [getD_append_left (by rw [List.length_map, List.length_range]; omega),
    getD_map_range (by omega)]

/-- Bob's answers read from a history that starts with Alice's honest run messages are his
honest answers. -/
theorem answersFromB_run (Y : List (List Bool)) :
    H.answersFromB ρ x zB rB ((List.range (H.calls.eval x.length * ρ.rounds.eval x.length)).map
      (H.slotFromA ρ x zA zB rA rB) ++ Y) = H.answersRealB ρ x zA zB rA rB := by
  rw [answersFromB_eq, answersRealB_eq]
  refine congrArg List.flatten (congrArg List.ofFn (funext fun j => ?_))
  have hjR := mul_add_le_of_lt (R := ρ.rounds.eval x.length) j.2
  rw [runNextB_eq, slotMsgs_runSnd H ρ x zA zB rA rB le_rfl]
  intro i hi
  rw [getD_append_left (by rw [List.length_map, List.length_range]; omega),
    getD_map_range (by omega)]

/-- **Alice's move in the main phase** after `m` moves of `main` (`m ≥ 1` if `main`'s verifier
moves first): her `main`-move on `⟨zA, her honest answers⟩`, her `main`-tape and `main`'s
messages.

**Proof sketch.** She has received `L·R + k` messages, `k` of them in `main`: she is past the
runs, and not at the leading filler, since `k ≥ 1` when `main`'s verifier moves first
(`exec_fst_length_pos`). Her answers are read from the run messages (`answersFromA_run`), and the
messages after the first `L·R` are `main`'s. -/
theorem compose_P_next_main {m : ℕ} (hm : H.main.verifierFirst = true → 0 < m) :
    (H.compose ρ).P.next x zA rA
        ((List.range (H.calls.eval x.length * ρ.rounds.eval x.length)).map
          (H.slotFromB ρ x zA zB rA rB) ++ (H.mainExec ρ x zA zB rA rB m).1) =
      H.main.P.next x (pairEncode zA (H.answersRealA ρ x zA zB rA rB))
        (rA.take (H.main.P.coins.eval x.length)) (H.mainExec ρ x zA zB rA rB m).1 := by
  have hlen : ((List.range (H.calls.eval x.length * ρ.rounds.eval x.length)).map
      (H.slotFromB ρ x zA zB rA rB) ++ (H.mainExec ρ x zA zB rA rB m).1).length =
      H.calls.eval x.length * ρ.rounds.eval x.length +
        (H.mainExec ρ x zA zB rA rB m).1.length := by
    rw [List.length_append, List.length_map, List.length_range]
  have hlead : ¬(H.main.verifierFirst = true ∧
      H.calls.eval x.length * ρ.rounds.eval x.length + (H.mainExec ρ x zA zB rA rB m).1.length =
        H.calls.eval x.length * ρ.rounds.eval x.length) := by
    rintro ⟨hv, hl⟩
    have := exec_fst_length_pos H.main.P H.main.V x (pairEncode zA (H.answersRealA ρ x zA zB rA rB))
      (pairEncode zB (H.answersRealB ρ x zA zB rA rB)) (rA.take (H.main.P.coins.eval x.length))
      (rB.take (H.main.V.coins.eval x.length)) hv (hm hv)
    rw [← mainExec_eq] at this
    omega
  rw [compose_P, composeP_next, hlen, if_neg (by omega), if_neg hlead, answersFromA_run,
    List.drop_left' (by rw [List.length_map, List.length_range])]

/-- **Bob's move in the main phase** after `m` moves of `main` (`m ≥ 1` if `main`'s prover moves
first): his `main`-move on `⟨zB, his honest answers⟩`, his `main`-tape and `main`'s messages.

**Proof sketch.** He has received `L·R + lead + k` messages, `k` of them in `main`, and
`lead + k ≥ 1`: either the leading filler was sent, or `main`'s prover moved first
(`exec_snd_length_pos`). So he is past the runs. His answers are read from the run messages
(`answersFromB_run`), and the messages after the first `L·R + lead` are `main`'s. -/
theorem compose_V_next_main {m : ℕ} (hm : H.main.verifierFirst = false → 0 < m) :
    (H.compose ρ).V.next x zB rB
        ((List.range (H.calls.eval x.length * ρ.rounds.eval x.length)).map
          (H.slotFromA ρ x zA zB rA rB) ++ List.replicate H.lead [] ++
          (H.mainExec ρ x zA zB rA rB m).2) =
      H.main.V.next x (pairEncode zB (H.answersRealB ρ x zA zB rA rB))
        (rB.take (H.main.V.coins.eval x.length)) (H.mainExec ρ x zA zB rA rB m).2 := by
  have hlen : ((List.range (H.calls.eval x.length * ρ.rounds.eval x.length)).map
      (H.slotFromA ρ x zA zB rA rB) ++ List.replicate H.lead [] ++
        (H.mainExec ρ x zA zB rA rB m).2).length =
      H.calls.eval x.length * ρ.rounds.eval x.length + H.lead +
        (H.mainExec ρ x zA zB rA rB m).2.length := by
    rw [List.length_append, List.length_append, List.length_map, List.length_range,
      List.length_replicate]
  have hpos : 0 < H.lead + (H.mainExec ρ x zA zB rA rB m).2.length := by
    cases hv : H.main.verifierFirst
    · have := exec_snd_length_pos H.main.P H.main.V x
        (pairEncode zA (H.answersRealA ρ x zA zB rA rB))
        (pairEncode zB (H.answersRealB ρ x zA zB rA rB)) (rA.take (H.main.P.coins.eval x.length))
        (rB.take (H.main.V.coins.eval x.length)) hv (hm hv)
      rw [← mainExec_eq] at this
      omega
    · rw [H.lead_of_true hv]
      omega
  rw [compose_V, composeV_next, hlen, if_neg (by omega), List.drop_left'
      (by rw [List.length_append, List.length_map, List.length_range, List.length_replicate]),
    List.append_assoc, answersFromB_run]

/-- **Phase lemma (b), the main phase**: after the run phase, the leading filler and `m` further
moves of an honest execution of `H.compose ρ`, Alice has received Bob's run messages followed by
the messages she receives in `main`, and Bob has received Alice's run messages, the leading
filler (`lead` empty messages) and the messages he receives in `main`, where `main` is executed
on `⟨zA, Alice's honest answers⟩`, `⟨zB, Bob's honest answers⟩` and the `main`-tapes
(`mainExec`).

**Proof sketch.** Induction on `m`.
1. `m = 0`: the run phase (`compose_exec_run` with `q = L·R`), then, if `main`'s verifier moves
   first, Alice's leading filler: she has received `L·R` messages, which she reads as the lead.
2. At `m + 1`: position `L·2R + lead + m` has `main`'s mover at `m` (the parity of `lead + m`).
   The mover has received the messages of the runs (and the lead), then `main`'s. It is past the
   runs, and Alice not at the lead, since `main`'s first mover has already moved
   (`exec_fst_length_pos`, `exec_snd_length_pos`). So it plays its `main`-move on its honest
   answers (`answersFromA_run`, `answersFromB_run`) and `main`'s messages
   (`compose_P_next_main`, `compose_V_next_main`). -/
theorem compose_exec_main (m : ℕ) :
    exec (H.compose ρ).P (H.compose ρ).V (H.compose ρ).verifierFirst x zA zB rA rB
        (H.calls.eval x.length * (2 * ρ.rounds.eval x.length) + H.lead + m) =
      ((List.range (H.calls.eval x.length * ρ.rounds.eval x.length)).map
          (H.slotFromB ρ x zA zB rA rB) ++ (H.mainExec ρ x zA zB rA rB m).1,
        (List.range (H.calls.eval x.length * ρ.rounds.eval x.length)).map
          (H.slotFromA ρ x zA zB rA rB) ++ List.replicate H.lead [] ++
          (H.mainExec ρ x zA zB rA rB m).2) := by
  set L := H.calls.eval x.length with hL
  set R := ρ.rounds.eval x.length with hR
  induction m with
  | zero =>
    rw [Nat.add_zero, mainExec_eq, exec_zero]
    simp only [List.append_nil]
    cases hv : H.main.verifierFirst
    · rw [H.lead_of_false hv, Nat.add_zero, List.replicate_zero, List.append_nil,
        show L * (2 * R) = 2 * (L * R) by ring, compose_exec_run H ρ x zA zB rA rB le_rfl]
    · rw [H.lead_of_true hv, show L * (2 * R) + 1 = 2 * (L * R) + 1 by ring, exec_succ,
        compose_exec_run H ρ x zA zB rA rB le_rfl]
      simp only [compose_verifierFirst, moverIsV_false_two_mul, Bool.false_eq_true, if_false]
      have hlead : (H.compose ρ).P.next x zA rA ((List.range (L * R)).map
          (H.slotFromB ρ x zA zB rA rB)) = [] := by
        rw [compose_P, composeP_next, List.length_map, List.length_range, if_neg (lt_irrefl _),
          if_pos ⟨hv, rfl⟩]
      rw [hlead, List.replicate_one]
  | succ m ih =>
    have hmv : moverIsV (H.compose ρ).verifierFirst (L * (2 * R) + H.lead + m) =
        moverIsV H.main.verifierFirst m := by
      rw [compose_verifierFirst, show L * (2 * R) = 2 * (L * R) by ring]
      cases hv : H.main.verifierFirst
      · rw [H.lead_of_false hv, moverIsV_false, moverIsV_false]
        congr 1
        apply propext
        omega
      · rw [H.lead_of_true hv, moverIsV_false, moverIsV_true]
        congr 1
        apply propext
        omega
    rw [← Nat.add_assoc, exec_succ, ih, mainExec_eq H ρ x zA zB rA rB (m + 1), exec_succ,
      ← mainExec_eq]
    simp only [hmv]
    cases hm : moverIsV H.main.verifierFirst m
    · simp only [Bool.false_eq_true, if_false]
      have hm' : H.main.verifierFirst = true → 0 < m := by
        intro hv
        rw [hv, moverIsV_true, decide_eq_false_iff_not] at hm
        omega
      rw [compose_P_next_main H ρ x zA zB rA rB hm', List.append_assoc]
    · simp only [if_true]
      have hm' : H.main.verifierFirst = false → 0 < m := by
        intro hv
        rw [hv, moverIsV_false, decide_eq_true_eq] at hm
        omega
      rw [compose_V_next_main H ρ x zA zB rA rB hm', List.append_assoc]

/-- **Phase lemma, the complete transcript**: the transcript of an honest execution of
`H.compose ρ` (all `L·2R + lead + M` moves) is, for Alice, Bob's run messages followed by
`main`'s messages to her, and for Bob, Alice's run messages, the leading filler and `main`'s
messages to him (`compose_exec_main` with `m = M`). -/
theorem compose_exec_rounds :
    exec (H.compose ρ).P (H.compose ρ).V (H.compose ρ).verifierFirst x zA zB rA rB
        ((H.compose ρ).rounds.eval x.length) =
      ((List.range (H.calls.eval x.length * ρ.rounds.eval x.length)).map
          (H.slotFromB ρ x zA zB rA rB) ++
          (H.mainExec ρ x zA zB rA rB (H.main.rounds.eval x.length)).1,
        (List.range (H.calls.eval x.length * ρ.rounds.eval x.length)).map
          (H.slotFromA ρ x zA zB rA rB) ++ List.replicate H.lead [] ++
          (H.mainExec ρ x zA zB rA rB (H.main.rounds.eval x.length)).2) := by
  rw [compose_rounds_eval, compose_exec_main]

end Phases

/-! ### The phases in terms of `Protocol` -/

section Outputs

variable {G : Functionality} (H : HybridProtocol G) (ρ : Protocol) (x zA zB : List Bool)
  (r : (H.compose ρ).ExecCoins (H.compose ρ).P x)

/-- **The transcript of `H.compose ρ`** on coins `r = (rA, rB)`: Bob's run messages and `main`'s
messages to Alice; Alice's run messages, the leading filler and `main`'s messages to Bob
(`compose_exec_rounds` on the tapes `List.ofFn rA`, `List.ofFn rB`). -/
theorem compose_transcript :
    (H.compose ρ).transcript x zA zB r =
      ((List.range (H.calls.eval x.length * ρ.rounds.eval x.length)).map
          (H.slotFromB ρ x zA zB (List.ofFn r.1) (List.ofFn r.2)) ++
          (H.mainExec ρ x zA zB (List.ofFn r.1) (List.ofFn r.2)
            (H.main.rounds.eval x.length)).1,
        (List.range (H.calls.eval x.length * ρ.rounds.eval x.length)).map
          (H.slotFromA ρ x zA zB (List.ofFn r.1) (List.ofFn r.2)) ++ List.replicate H.lead [] ++
          (H.mainExec ρ x zA zB (List.ofFn r.1) (List.ofFn r.2)
            (H.main.rounds.eval x.length)).2) :=
  H.compose_exec_rounds ρ x zA zB (List.ofFn r.1) (List.ofFn r.2)

/-- **Alice's view in `H.compose ρ`**: the common input, her input, her whole tape, and Bob's run
messages followed by `main`'s messages to her. -/
theorem compose_viewP :
    (H.compose ρ).viewP x zA zB r =
      ⟨x, zA, List.ofFn r.1,
        (List.range (H.calls.eval x.length * ρ.rounds.eval x.length)).map
          (H.slotFromB ρ x zA zB (List.ofFn r.1) (List.ofFn r.2)) ++
          (H.mainExec ρ x zA zB (List.ofFn r.1) (List.ofFn r.2)
            (H.main.rounds.eval x.length)).1⟩ := by
  show (⟨x, zA, List.ofFn r.1, ((H.compose ρ).transcript x zA zB r).1⟩ : View) = _
  rw [compose_transcript]

/-- **Bob's view in `H.compose ρ`**: the common input, his input, his whole tape, and Alice's run
messages, the leading filler and `main`'s messages to him. -/
theorem compose_viewV :
    (H.compose ρ).viewV x zA zB r =
      ⟨x, zB, List.ofFn r.2,
        (List.range (H.calls.eval x.length * ρ.rounds.eval x.length)).map
          (H.slotFromA ρ x zA zB (List.ofFn r.1) (List.ofFn r.2)) ++ List.replicate H.lead [] ++
          (H.mainExec ρ x zA zB (List.ofFn r.1) (List.ofFn r.2)
            (H.main.rounds.eval x.length)).2⟩ := by
  show (⟨x, zB, List.ofFn r.2, ((H.compose ρ).transcript x zA zB r).2⟩ : View) = _
  rw [compose_transcript]

/-- **Phase lemma (c), Alice's output** in terms of `Protocol.outP`: when `main` has at least one
move, Alice's output in `H.compose ρ` is her `main`-output on `⟨zA, her honest answers⟩`, her
`main`-tape and her complete `main`-history.

**Proof sketch.** Her complete history is Bob's run messages followed by `main`'s messages to
her (`compose_exec_rounds`). If `main`'s verifier moves first, it has moved, as `M ≥ 1`, so she
is not at the leading filler, and `compose_P_next_main` applies. -/
theorem compose_outP (hM : 0 < H.main.rounds.eval x.length) :
    (H.compose ρ).outP x zA zB r =
      H.main.P.next x (pairEncode zA (H.answersRealA ρ x zA zB (List.ofFn r.1) (List.ofFn r.2)))
        ((List.ofFn r.1).take (H.main.P.coins.eval x.length))
        (H.mainExec ρ x zA zB (List.ofFn r.1) (List.ofFn r.2)
          (H.main.rounds.eval x.length)).1 := by
  show (H.compose ρ).P.next x zA (List.ofFn r.1) (exec (H.compose ρ).P (H.compose ρ).V
    (H.compose ρ).verifierFirst x zA zB (List.ofFn r.1) (List.ofFn r.2)
    ((H.compose ρ).rounds.eval x.length)).1 = _
  rw [compose_exec_rounds]
  exact compose_P_next_main H ρ x zA zB _ _ fun _ => hM

/-- **Phase lemma (c), Bob's output** in terms of `Protocol.outV`: when `main` has at least one
move, Bob's output in `H.compose ρ` is his `main`-output on `⟨zB, his honest answers⟩`, his
`main`-tape and his complete `main`-history.

**Proof sketch.** His complete history is Alice's run messages, the leading filler and `main`'s
messages to him (`compose_exec_rounds`). He is past the runs, because the leading filler or
`main`'s first move (by Alice, as `M ≥ 1`) follows them, and `compose_V_next_main` applies. -/
theorem compose_outV (hM : 0 < H.main.rounds.eval x.length) :
    (H.compose ρ).outV (H.compose ρ).P x zA zB r =
      H.main.V.next x (pairEncode zB (H.answersRealB ρ x zA zB (List.ofFn r.1) (List.ofFn r.2)))
        ((List.ofFn r.2).take (H.main.V.coins.eval x.length))
        (H.mainExec ρ x zA zB (List.ofFn r.1) (List.ofFn r.2)
          (H.main.rounds.eval x.length)).2 := by
  show (H.compose ρ).V.next x zB (List.ofFn r.2) (exec (H.compose ρ).P (H.compose ρ).V
    (H.compose ρ).verifierFirst x zA zB (List.ofFn r.1) (List.ofFn r.2)
    ((H.compose ρ).rounds.eval x.length)).2 = _
  rw [compose_exec_rounds]
  exact compose_V_next_main H ρ x zA zB _ _ fun _ => hM

end Outputs

end HybridProtocol

end TCSlib.Cryptography.SecureComputation
