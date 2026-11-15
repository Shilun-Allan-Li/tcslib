/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Hybrid

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Sequential composition in the hybrid model: the composed protocol

The protocol of the composition theorem [Gol04, §7.3.1, Theorem 7.3.3]: a protocol `H` in the
`G`-hybrid model (`HybridProtocol`, ideal calls first) with its ideal calls replaced by runs of
a protocol `ρ` meant to compute `G`, on the interaction model of
`ZeroKnowledge/Interaction.lean` (D8). Its phase lemmas are in `ComposePhases.lean`, and the
composition theorem, `hbcSecure_compose`, in `ComposeSecurity.lean`. The section and theorem
numbers of [Gol04] are cited from memory and should be verified at audit.

**The layout** of `H.compose ρ` (`HybridProtocol.compose`). Write `n = |x|` for the common input
`x = 1^n`, `L = calls(n)`, `R = ρ.rounds(n)`, `M = main.rounds(n)`, and `lead = 1` if `main`'s
verifier (Bob) moves first, `0` otherwise. Alice (the prover) moves first and the parties
alternate, Alice at the even positions `t` and Bob at the odd ones, for `L · 2R + lead + M`
moves.
- **The runs.** The positions `t < L · 2R` form the `L · R` pairs `(2q, 2q + 1)`. Pair
  `q = R · j + p` carries `ρ`'s move `p` of run `j`: at its even position if `ρ`'s mover `p` is
  Alice, at its odd one if it is Bob. The other position is a **filler**, the empty message `[]`.
  Run `j` is an honest execution of `ρ` on the inputs of call `j` (`callA`, `callB`, computed
  from the parties' inputs and their tapes for `main`) and on the parties' `j`-th `ρ`-tapes.
- **The main phase.** If `main`'s verifier moves first, one leading `[]` from Alice; then
  `main`'s `M` moves. Each party's private input in `main` is its input paired with its
  **answers**: its outputs of the `L` runs, each read at `G`'s output length (`padFin`) and
  concatenated, in place of the ideal answers of the hybrid model.
- **Coins.** Each party's tape is its tape for `main`, then one `ρ`-tape per run.
- **Positions.** A party finds its position from the number of messages it has received:
  Alice, having received `k`, is at pair `k`; Bob, having received `c ≥ 1`, at pair `c − 1`.

**Why fillers.** D8 executions alternate strictly, while consecutive runs of `ρ` may give one
party two moves in a row (when `R` is odd), and so may the passage from the runs to `main`.
Giving each move of `ρ` its own pair keeps the alternation without parity arithmetic on
`PolyExpr`s; the leading filler does the same before `main`.

**Why no trailing filler: D8's output convention.** A party's output is its next-message
function on its complete history, so the last mover's output is its last message, which the
other party receives. With `M ≥ 1` the last move is `main`'s last move, whose mover outputs that
message in `main` as well. A trailing filler would make its sender's output part of the other
party's view. For the same reason the composition needs `M ≥ 1`: with `M = 0` the last move is a
run move or the leading filler, and its sender's output is that message, not its output in
`main` (`ComposePhases.lean`, `ComposeSecurity.lean`).

**Deviations from [Gol04, §7.3.1].**
- **Calls first only.** Gol04's oracle-aided protocols interleave calls and messages. Here all
  calls come first (`HybridProtocol`), so all runs of `ρ` precede `main`.
- **Strict alternation by fillers**, as above: `2R` moves per run and the leading filler.
- **Answers at `G`'s lengths.** A party's answer from a run is its `ρ`-output padded or truncated
  to `G`'s output length; it is the ideal answer when `ρ`'s output is correct.

## Main definitions

* `Compose.moveMsg`, `Compose.slotMsgs`, `Compose.runTape`: the message of a move, the messages
  of a run read at the pair positions, and the tape of a run.
* `HybridProtocol.lead`: the leading filler of the main phase.
* `HybridProtocol.runInputA`, `runInputB`, `runNextA`, `runNextB`, `answersFromA`,
  `answersFromB`: the parties' inputs, moves and answers of the runs.
* `HybridProtocol.composeP`, `composeV`, `compose`: the composed protocol.

## Main results

* `Compose.exec_eq_map`: the messages each party receives are the messages of the other party's
  moves, in order.
* `HybridProtocol.compose_rounds`, `compose_rounds_eval`, `compose_verifierFirst`,
  `compose_P_coinLen`, `compose_V_coinLen`: the shape of `H.compose ρ`.

## References

* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*, Cambridge
  University Press, 2004, §7.3.1 (privacy reductions and a composition theorem), Theorem 7.3.3.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §4.4 (interactive protocols) and §6.2, Definition 155.1 (book pp. 114–116, 155).
-/

namespace TCSlib.Cryptography.SecureComputation

open Complexity Turing TCSlib.Cryptography

namespace Compose

/-! ### Executions, slots and tapes -/

/-- **The message of move `k`** of the execution `P_{rP}(x, zP) ↔ V_{rV}(x, zV)` with first mover
`vF` [PS10, §4.4]: the next message of the party moving at `k` on the messages it has received
in the first `k` moves. -/
def moveMsg (P V : Strategy) (vF : Bool) (x zP zV rP rV : List Bool) (k : ℕ) : List Bool :=
  if moverIsV vF k then V.next x zV rV (exec P V vF x zP zV rP rV k).2
  else P.next x zP rP (exec P V vF x zP zV rP rV k).1

/-- The message of move `k` is `V.next` on `V`'s received messages if `V` moves at `k`, and
`P.next` on `P`'s otherwise. -/
theorem moveMsg_eq (P V : Strategy) (vF : Bool) (x zP zV rP rV : List Bool) (k : ℕ) :
    moveMsg P V vF x zP zV rP rV k =
      if moverIsV vF k then V.next x zV rV (exec P V vF x zP zV rP rV k).2
      else P.next x zP rP (exec P V vF x zP zV rP rV k).1 := rfl

/-- **The received messages are the other party's moves**: after `k` moves, `P` has received the
messages of the moves `i < k` made by `V`, and `V` those of the moves `i < k` made by `P`, in
order.

**Proof sketch.** Induction on `k`: move `k` appends its message, `moveMsg k`, to the list of the
party not moving (`exec_succ`), and `k` joins that party's side of the filter of
`range (k + 1)`. -/
theorem exec_eq_map (P V : Strategy) (vF : Bool) (x zP zV rP rV : List Bool) (k : ℕ) :
    exec P V vF x zP zV rP rV k =
      (((List.range k).filter (moverIsV vF)).map (moveMsg P V vF x zP zV rP rV),
        ((List.range k).filter fun i => !moverIsV vF i).map (moveMsg P V vF x zP zV rP rV)) := by
  induction k with
  | zero => simp only [exec_zero, List.range_zero, List.filter_nil, List.map_nil]
  | succ k ih =>
    rw [exec_succ, List.range_succ, List.filter_append, List.filter_append, List.map_append,
      List.map_append]
    cases h : moverIsV vF k
    · have hm : moveMsg P V vF x zP zV rP rV k =
          P.next x zP rP (exec P V vF x zP zV rP rV k).1 := by
        rw [moveMsg_eq, h, if_neg Bool.false_ne_true]
      simp only [h, Bool.false_eq_true, if_false, List.filter_cons, List.filter_nil,
        Bool.not_false, if_true, List.map_cons, List.map_nil, List.append_nil]
      rw [hm, ih]
    · have hm : moveMsg P V vF x zP zV rP rV k =
          V.next x zV rV (exec P V vF x zP zV rP rV k).2 := by
        rw [moveMsg_eq, h, if_pos rfl]
      simp only [h, if_true, List.filter_cons, List.filter_nil, Bool.not_true,
        Bool.false_eq_true, if_false, List.map_cons, List.map_nil, List.append_nil]
      rw [hm, ih]

/-- With the verifier first, the prover has received a message after any positive number of
moves. -/
theorem exec_fst_length_pos (P V : Strategy) {vF : Bool} (x zP zV rP rV : List Bool) {k : ℕ}
    (hv : vF = true) (hk : 0 < k) : 0 < (exec P V vF x zP zV rP rV k).1.length := by
  rw [exec_eq_map, List.length_map]
  refine List.length_pos_of_mem (a := 0) (List.mem_filter.2 ⟨List.mem_range.2 hk, ?_⟩)
  rw [hv, moverIsV_true]
  rfl

/-- With the prover first, the verifier has received a message after any positive number of
moves. -/
theorem exec_snd_length_pos (P V : Strategy) {vF : Bool} (x zP zV rP rV : List Bool) {k : ℕ}
    (hv : vF = false) (hk : 0 < k) : 0 < (exec P V vF x zP zV rP rV k).2.length := by
  rw [exec_eq_map, List.length_map]
  refine List.length_pos_of_mem (a := 0) (List.mem_filter.2 ⟨List.mem_range.2 hk, ?_⟩)
  rw [hv, moverIsV_false]
  rfl

/-- **The messages of a run read from the pairs**: the entries `off + p'` of `hist` (`[]` beyond
its end), for the `p' < p` with `sel p'`, in order. -/
def slotMsgs (sel : ℕ → Bool) (off p : ℕ) (hist : List (List Bool)) : List (List Bool) :=
  ((List.range p).filter sel).map fun p' => hist.getD (off + p') []

/-- `slotMsgs sel off p hist` lists `hist[off + p']` over the `p' < p` with `sel p'`. -/
theorem slotMsgs_eq (sel : ℕ → Bool) (off p : ℕ) (hist : List (List Bool)) :
    slotMsgs sel off p hist = ((List.range p).filter sel).map fun p' => hist.getD (off + p') [] :=
  rfl

/-- If `hist[off + p'] = f p'` at the selected `p' < p`, the run's messages are the `f p'`. -/
theorem slotMsgs_eq_map {sel : ℕ → Bool} {off p : ℕ} {hist : List (List Bool)}
    {f : ℕ → List Bool} (hf : ∀ p' < p, sel p' = true → hist.getD (off + p') [] = f p') :
    slotMsgs sel off p hist = ((List.range p).filter sel).map f := by
  refine List.map_congr_left fun p' hp' => ?_
  rw [List.mem_filter, List.mem_range] at hp'
  exact hf p' hp'.1 hp'.2

/-- **The tape of run `j`**: the `c` bits after the first `c₀ + j · c` bits of `r`. -/
def runTape (c₀ c j : ℕ) (r : List Bool) : List Bool := (r.drop (c₀ + j * c)).take c

/-- The tape of run `j` is `r[c₀ + j·c, c₀ + (j + 1)·c)`. -/
theorem runTape_eq (c₀ c j : ℕ) (r : List Bool) : runTape c₀ c j r = (r.drop (c₀ + j * c)).take c :=
  rfl

/-- The tape of run `j < L` of a tape of `c₀ + L·c` bits has `c` bits. -/
theorem length_runTape {c₀ c j L : ℕ} {r : List Bool} (hr : r.length = c₀ + L * c)
    (hj : j < L) : (runTape c₀ c j r).length = c := by
  have := Nat.mul_le_mul_right c (Nat.succ_le_of_lt hj)
  rw [Nat.succ_mul] at this
  rw [runTape_eq, List.length_take, List.length_drop, hr]
  omega

/-- Entry `i < q` of `[f 0, …, f (q − 1)]` is `f i`. -/
theorem getD_map_range {f : ℕ → List Bool} {q i : ℕ} (h : i < q) :
    ((List.range q).map f).getD i [] = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]
  rfl

/-- An entry of the first part of an append. -/
theorem getD_append_left {l₁ l₂ : List (List Bool)} {i : ℕ} (h : i < l₁.length) :
    (l₁ ++ l₂).getD i [] = l₁.getD i [] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h, ← List.getD_eq_getElem?_getD]

/-- With the prover first, the prover moves at the even positions. -/
theorem moverIsV_false_two_mul (q : ℕ) : moverIsV false (2 * q) = false := by
  rw [moverIsV_false, decide_eq_false_iff_not]
  omega

/-- With the prover first, the verifier moves at the odd positions. -/
theorem moverIsV_false_two_mul_add_one (q : ℕ) : moverIsV false (2 * q + 1) = true := by
  rw [moverIsV_false, decide_eq_true_eq]
  omega

end Compose

open Compose

namespace HybridProtocol

/-! ### The composed protocol -/

section Construction

variable {G : Functionality} (H : HybridProtocol G) (ρ : Protocol)

/-- **The leading filler** of the main phase: `1` if `main`'s verifier (Bob) moves first, so that
Alice's empty message hands the move to Bob; `0` otherwise. -/
def lead : ℕ := if H.main.verifierFirst then 1 else 0

/-- `lead = 1` if `main`'s verifier moves first, `0` otherwise. -/
theorem lead_eq : H.lead = if H.main.verifierFirst then 1 else 0 := rfl

/-- With `main`'s verifier first there is one leading filler. -/
theorem lead_of_true (h : H.main.verifierFirst = true) : H.lead = 1 := by
  rw [lead_eq, if_pos h]

/-- With `main`'s prover first there is no leading filler. -/
theorem lead_of_false (h : H.main.verifierFirst = false) : H.lead = 0 := by
  rw [lead_eq, h]
  rfl

/-- **Alice's input to run `j`**, on common input `x`, input `z` and composed tape `r`: her input
to ideal call `j`, `callA(|x|, z, r_main, j)` with `r_main` the first `main.P.coins(|x|)` bits
of `r`, when `j < calls(|x|)`; `[]` otherwise (never used). -/
def runInputA (x z r : List Bool) (j : ℕ) : List Bool :=
  if h : j < H.calls.eval x.length then
    List.ofFn (H.callA x.length z (r.take (H.main.P.coins.eval x.length)) ⟨j, h⟩)
  else []

/-- For `j < calls(|x|)`, Alice's input to run `j` is her input to call `j`. -/
theorem runInputA_of_lt (x z r : List Bool) {j : ℕ} (h : j < H.calls.eval x.length) :
    H.runInputA x z r j =
      List.ofFn (H.callA x.length z (r.take (H.main.P.coins.eval x.length)) ⟨j, h⟩) := by
  rw [runInputA, dif_pos h]

/-- For `j ≥ calls(|x|)`, Alice's input to run `j` is `[]`. -/
theorem runInputA_of_ge (x z r : List Bool) {j : ℕ} (h : H.calls.eval x.length ≤ j) :
    H.runInputA x z r j = [] := by
  rw [runInputA, dif_neg (Nat.not_lt.2 h)]

/-- **Bob's input to run `j`**: his input to ideal call `j`, `callB(|x|, z, r_main, j)` with
`r_main` the first `main.V.coins(|x|)` bits of his tape, when `j < calls(|x|)`; `[]`
otherwise. -/
def runInputB (x z r : List Bool) (j : ℕ) : List Bool :=
  if h : j < H.calls.eval x.length then
    List.ofFn (H.callB x.length z (r.take (H.main.V.coins.eval x.length)) ⟨j, h⟩)
  else []

/-- For `j < calls(|x|)`, Bob's input to run `j` is his input to call `j`. -/
theorem runInputB_of_lt (x z r : List Bool) {j : ℕ} (h : j < H.calls.eval x.length) :
    H.runInputB x z r j =
      List.ofFn (H.callB x.length z (r.take (H.main.V.coins.eval x.length)) ⟨j, h⟩) := by
  rw [runInputB, dif_pos h]

/-- For `j ≥ calls(|x|)`, Bob's input to run `j` is `[]`. -/
theorem runInputB_of_ge (x z r : List Bool) {j : ℕ} (h : H.calls.eval x.length ≤ j) :
    H.runInputB x z r j = [] := by
  rw [runInputB, dif_neg (Nat.not_lt.2 h)]

/-- **Alice's `ρ`-move in run `j` after `p` pairs of the run**: `ρ.P.next` on her input to run
`j`, her `j`-th `ρ`-tape, and Bob's run-`j` messages among the pairs `R·j + p'`, `p' < p`, where
`ρ`'s mover `p'` is Bob (Bob's message of pair `q` is `hist[q]`). With `p = R` it is her output of
run `j`. -/
def runNextA (x z r : List Bool) (hist : List (List Bool)) (j p : ℕ) : List Bool :=
  ρ.P.next x (H.runInputA x z r j)
    (runTape (H.main.P.coins.eval x.length) (ρ.P.coins.eval x.length) j r)
    (slotMsgs (moverIsV ρ.verifierFirst) (ρ.rounds.eval x.length * j) p hist)

/-- Alice's `ρ`-move in run `j` is `ρ.P.next` on her run input, run tape and run messages. -/
theorem runNextA_eq (x z r : List Bool) (hist : List (List Bool)) (j p : ℕ) :
    H.runNextA ρ x z r hist j p =
      ρ.P.next x (H.runInputA x z r j)
        (runTape (H.main.P.coins.eval x.length) (ρ.P.coins.eval x.length) j r)
        (slotMsgs (moverIsV ρ.verifierFirst) (ρ.rounds.eval x.length * j) p hist) := rfl

/-- **Bob's `ρ`-move in run `j` after `p` pairs of the run**: `ρ.V.next` on his input to run `j`,
his `j`-th `ρ`-tape, and Alice's run-`j` messages among the pairs `R·j + p'`, `p' < p`, where
`ρ`'s mover `p'` is Alice (Alice's message of pair `q` is `hist[q]`). With `p = R` it is his
output of run `j`. -/
def runNextB (x z r : List Bool) (hist : List (List Bool)) (j p : ℕ) : List Bool :=
  ρ.V.next x (H.runInputB x z r j)
    (runTape (H.main.V.coins.eval x.length) (ρ.V.coins.eval x.length) j r)
    (slotMsgs (fun p' => !moverIsV ρ.verifierFirst p') (ρ.rounds.eval x.length * j) p hist)

/-- Bob's `ρ`-move in run `j` is `ρ.V.next` on his run input, run tape and run messages. -/
theorem runNextB_eq (x z r : List Bool) (hist : List (List Bool)) (j p : ℕ) :
    H.runNextB ρ x z r hist j p =
      ρ.V.next x (H.runInputB x z r j)
        (runTape (H.main.V.coins.eval x.length) (ρ.V.coins.eval x.length) j r)
        (slotMsgs (fun p' => !moverIsV ρ.verifierFirst p') (ρ.rounds.eval x.length * j) p
          hist) := rfl

/-- **Alice's answers** read from her history: her outputs of the `calls(|x|)` runs, each padded
or truncated to `G.outA(|x|)` bits, concatenated. -/
def answersFromA (x z r : List Bool) (hist : List (List Bool)) : List Bool :=
  (List.ofFn fun j : Fin (H.calls.eval x.length) =>
    List.ofFn (padFin (G.outA.eval x.length)
      (H.runNextA ρ x z r hist j (ρ.rounds.eval x.length)))).flatten

/-- Alice's answers are her padded run outputs, concatenated. -/
theorem answersFromA_eq (x z r : List Bool) (hist : List (List Bool)) :
    H.answersFromA ρ x z r hist =
      (List.ofFn fun j : Fin (H.calls.eval x.length) =>
        List.ofFn (padFin (G.outA.eval x.length)
          (H.runNextA ρ x z r hist j (ρ.rounds.eval x.length)))).flatten := rfl

/-- **Bob's answers** read from his history: his outputs of the runs, each padded or truncated to
`G.outB(|x|)` bits, concatenated. -/
def answersFromB (x z r : List Bool) (hist : List (List Bool)) : List Bool :=
  (List.ofFn fun j : Fin (H.calls.eval x.length) =>
    List.ofFn (padFin (G.outB.eval x.length)
      (H.runNextB ρ x z r hist j (ρ.rounds.eval x.length)))).flatten

/-- Bob's answers are his padded run outputs, concatenated. -/
theorem answersFromB_eq (x z r : List Bool) (hist : List (List Bool)) :
    H.answersFromB ρ x z r hist =
      (List.ofFn fun j : Fin (H.calls.eval x.length) =>
        List.ofFn (padFin (G.outB.eval x.length)
          (H.runNextB ρ x z r hist j (ρ.rounds.eval x.length)))).flatten := rfl

/-- **Alice in `H.compose ρ`** [Gol04, §7.3.1, the composed protocol], on common input `x`
(`n = |x|`, `L = calls(n)`, `R = ρ.rounds(n)`), input `z` and tape `r`, having received the
`k = |hist|` messages `hist`; her move is at position `2k`, in pair `k`.
- If `k < L·R` (run `j = k / R`, position `p = k % R`): `[]` if `ρ`'s mover `p` is Bob; otherwise
  her `ρ`-move (`runNextA`).
- Else, if `main`'s verifier moves first and `k = L·R`: the leading filler `[]`.
- Else: `main.P.next` on `⟨z, her answers⟩`, her `main`-tape (the first `main.P.coins(n)` bits)
  and the messages received after the runs.

Her tape is her `main`-tape followed by `L` tapes for `ρ`. -/
def composeP : Strategy where
  next x z r hist :=
    if hist.length < H.calls.eval x.length * ρ.rounds.eval x.length then
      if moverIsV ρ.verifierFirst (hist.length % ρ.rounds.eval x.length) then []
      else H.runNextA ρ x z r hist (hist.length / ρ.rounds.eval x.length)
        (hist.length % ρ.rounds.eval x.length)
    else if H.main.verifierFirst = true ∧
        hist.length = H.calls.eval x.length * ρ.rounds.eval x.length then []
    else H.main.P.next x (pairEncode z (H.answersFromA ρ x z r hist))
      (r.take (H.main.P.coins.eval x.length))
      (hist.drop (H.calls.eval x.length * ρ.rounds.eval x.length))
  coins := .add H.main.P.coins (.mul H.calls ρ.P.coins)

/-- Alice's next message in `H.compose ρ` (see `composeP`). -/
theorem composeP_next (x z r : List Bool) (hist : List (List Bool)) :
    (H.composeP ρ).next x z r hist =
      if hist.length < H.calls.eval x.length * ρ.rounds.eval x.length then
        if moverIsV ρ.verifierFirst (hist.length % ρ.rounds.eval x.length) then []
        else H.runNextA ρ x z r hist (hist.length / ρ.rounds.eval x.length)
          (hist.length % ρ.rounds.eval x.length)
      else if H.main.verifierFirst = true ∧
          hist.length = H.calls.eval x.length * ρ.rounds.eval x.length then []
      else H.main.P.next x (pairEncode z (H.answersFromA ρ x z r hist))
        (r.take (H.main.P.coins.eval x.length))
        (hist.drop (H.calls.eval x.length * ρ.rounds.eval x.length)) := rfl

/-- Alice's coins in `H.compose ρ`: `main.P.coins + calls · ρ.P.coins`. -/
theorem composeP_coins : (H.composeP ρ).coins = .add H.main.P.coins (.mul H.calls ρ.P.coins) :=
  rfl

/-- **Bob in `H.compose ρ`**, on common input `x`, input `z` and tape `r`, having received the
`c = |hist|` messages `hist`; his move is at position `2c − 1`, in pair `q = c − 1`.
- If `q < L·R` (run `j = q / R`, position `p = q % R`): his `ρ`-move (`runNextB`) if `ρ`'s mover
  `p` is Bob; otherwise `[]`.
- Else: `main.V.next` on `⟨z, his answers⟩`, his `main`-tape and the messages received after
  the runs and the leading filler.

His tape is his `main`-tape followed by `L` tapes for `ρ`. -/
def composeV : Strategy where
  next x z r hist :=
    if hist.length - 1 < H.calls.eval x.length * ρ.rounds.eval x.length then
      if moverIsV ρ.verifierFirst ((hist.length - 1) % ρ.rounds.eval x.length) then
        H.runNextB ρ x z r hist ((hist.length - 1) / ρ.rounds.eval x.length)
          ((hist.length - 1) % ρ.rounds.eval x.length)
      else []
    else H.main.V.next x (pairEncode z (H.answersFromB ρ x z r hist))
      (r.take (H.main.V.coins.eval x.length))
      (hist.drop (H.calls.eval x.length * ρ.rounds.eval x.length + H.lead))
  coins := .add H.main.V.coins (.mul H.calls ρ.V.coins)

/-- Bob's next message in `H.compose ρ` (see `composeV`). -/
theorem composeV_next (x z r : List Bool) (hist : List (List Bool)) :
    (H.composeV ρ).next x z r hist =
      if hist.length - 1 < H.calls.eval x.length * ρ.rounds.eval x.length then
        if moverIsV ρ.verifierFirst ((hist.length - 1) % ρ.rounds.eval x.length) then
          H.runNextB ρ x z r hist ((hist.length - 1) / ρ.rounds.eval x.length)
            ((hist.length - 1) % ρ.rounds.eval x.length)
        else []
      else H.main.V.next x (pairEncode z (H.answersFromB ρ x z r hist))
        (r.take (H.main.V.coins.eval x.length))
        (hist.drop (H.calls.eval x.length * ρ.rounds.eval x.length + H.lead)) := rfl

/-- Bob's coins in `H.compose ρ`: `main.V.coins + calls · ρ.V.coins`. -/
theorem composeV_coins : (H.composeV ρ).coins = .add H.main.V.coins (.mul H.calls ρ.V.coins) :=
  rfl

/-- **The composed protocol** `H.compose ρ` [Gol04, §7.3.1, the protocol of Theorem 7.3.3]: `H`
with its ideal calls to `G` replaced by runs of `ρ`. Alice (`composeP`) moves first; the
`calls · (2 · ρ.rounds) + lead + main.rounds` moves are the `calls` runs of `ρ`, each in `2 ·
ρ.rounds` moves with fillers, the leading filler, and `main` (see the module docstring). -/
def compose : Protocol where
  P := H.composeP ρ
  V := H.composeV ρ
  rounds := .add (.add (.mul H.calls (.mul (.const 2) ρ.rounds)) (.const H.lead)) H.main.rounds
  verifierFirst := false

/-- Alice's strategy in `H.compose ρ` is `composeP`. -/
theorem compose_P : (H.compose ρ).P = H.composeP ρ := rfl

/-- Bob's strategy in `H.compose ρ` is `composeV`. -/
theorem compose_V : (H.compose ρ).V = H.composeV ρ := rfl

/-- `H.compose ρ` has `calls · (2 · ρ.rounds) + lead + main.rounds` moves. -/
theorem compose_rounds :
    (H.compose ρ).rounds =
      .add (.add (.mul H.calls (.mul (.const 2) ρ.rounds)) (.const H.lead)) H.main.rounds := rfl

/-- At `n`, `H.compose ρ` has `calls(n) · (2 · ρ.rounds(n)) + lead + main.rounds(n)` moves. -/
theorem compose_rounds_eval (n : ℕ) :
    (H.compose ρ).rounds.eval n =
      H.calls.eval n * (2 * ρ.rounds.eval n) + H.lead + H.main.rounds.eval n := rfl

/-- In `H.compose ρ` Alice (the prover) moves first. -/
theorem compose_verifierFirst : (H.compose ρ).verifierFirst = false := rfl

/-- Alice's tape in `H.compose ρ` has `main.P.coins(n) + calls(n) · ρ.P.coins(n)` bits.

**Proof sketch.** Read the strategy and its coin polynomial through their public equations,
evaluate the sum and product, and re-express the two component lengths with `Strategy.coinLen_eq`. -/
theorem compose_P_coinLen (n : ℕ) :
    (H.compose ρ).P.coinLen n = H.main.P.coinLen n + H.calls.eval n * ρ.P.coinLen n :=
  calc
    (H.compose ρ).P.coinLen n = (H.composeP ρ).coins.eval n :=
      (Strategy.coinLen_eq ((H.compose ρ).P) n).trans
        (congrArg (fun S : Strategy => S.coins.eval n) (H.compose_P ρ))
    _ = (PolyExpr.add H.main.P.coins (PolyExpr.mul H.calls ρ.P.coins)).eval n :=
      congrArg (fun p : PolyExpr => p.eval n) (H.composeP_coins ρ)
    _ = H.main.P.coins.eval n + H.calls.eval n * ρ.P.coins.eval n :=
      (PolyExpr.eval_add H.main.P.coins (.mul H.calls ρ.P.coins) n).trans
        (congrArg (fun c : ℕ => H.main.P.coins.eval n + c)
          (PolyExpr.eval_mul H.calls ρ.P.coins n))
    _ = H.main.P.coinLen n + H.calls.eval n * ρ.P.coinLen n :=
      congrArg₂ (fun a b : ℕ => a + b) (Strategy.coinLen_eq H.main.P n).symm
        (congrArg (fun c : ℕ => H.calls.eval n * c) (Strategy.coinLen_eq ρ.P n).symm)

/-- Bob's tape in `H.compose ρ` has `main.V.coins(n) + calls(n) · ρ.V.coins(n)` bits.

**Proof sketch.** Read the strategy and its coin polynomial through their public equations,
evaluate the sum and product, and re-express the two component lengths with `Strategy.coinLen_eq`. -/
theorem compose_V_coinLen (n : ℕ) :
    (H.compose ρ).V.coinLen n = H.main.V.coinLen n + H.calls.eval n * ρ.V.coinLen n :=
  calc
    (H.compose ρ).V.coinLen n = (H.composeV ρ).coins.eval n :=
      (Strategy.coinLen_eq ((H.compose ρ).V) n).trans
        (congrArg (fun S : Strategy => S.coins.eval n) (H.compose_V ρ))
    _ = (PolyExpr.add H.main.V.coins (PolyExpr.mul H.calls ρ.V.coins)).eval n :=
      congrArg (fun p : PolyExpr => p.eval n) (H.composeV_coins ρ)
    _ = H.main.V.coins.eval n + H.calls.eval n * ρ.V.coins.eval n :=
      (PolyExpr.eval_add H.main.V.coins (.mul H.calls ρ.V.coins) n).trans
        (congrArg (fun c : ℕ => H.main.V.coins.eval n + c)
          (PolyExpr.eval_mul H.calls ρ.V.coins n))
    _ = H.main.V.coinLen n + H.calls.eval n * ρ.V.coinLen n :=
      congrArg₂ (fun a b : ℕ => a + b) (Strategy.coinLen_eq H.main.V n).symm
        (congrArg (fun c : ℕ => H.calls.eval n * c) (Strategy.coinLen_eq ρ.V n).symm)

end Construction

end HybridProtocol

end TCSlib.Cryptography.SecureComputation
