/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.ComposePhases

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The composition theorem for the semi-honest model (statement phase)

[Gol04, §7.3.1, Theorem 7.3.3]: if a protocol `H` privately computes `F` in the `G`-hybrid model
and a protocol `ρ` privately computes `G`, then `H` with every ideal call replaced by a run of `ρ`
privately computes `F`. Here "privately computes" is honest-but-curious security
[PS10, Definition 155.1] (`HBCSecure`, and `HybridProtocol.HBCSecure` in the hybrid model), and
the composed protocol is `H.compose ρ` (`Compose.lean`). The section and theorem numbers of
[Gol04] are cited from memory and should be verified at audit.

[PS10]'s proof of Theorem 163.7 (Yao's protocol) uses this theorem without stating it. By the
ruling of 2026-11-05, Yao's protocol is proved secure with an ideal OT, and the real protocol
follows from this theorem with Protocol 160.4 for `ρ`.

**Polynomial time** (ruling of 2026-11-05: security includes polynomial-time parties). The
messages of `H.compose ρ` are bounded by the sum of `main`'s and `ρ`'s bounds
(`compose_msg_bound`, proved). This uses that `H.PolyTime` bounds `main`'s messages for **any**
answers of the right lengths, since in `H.compose ρ` `main` runs on `ρ`'s outputs. That the
composed strategies are PPT is stated, with `sorry`s under their sketches.

**Deviations from [Gol04, Theorem 7.3.3].**
- **Calls first only**, and the layout with fillers (`Compose.lean`).
- **`main` has at least one move** (`hM`), forced by D8's output convention: if
  `main.rounds(n) = 0`, the last move of `H.compose ρ` is a run move or the leading filler, and
  its sender's output is that message instead of its output in `main`. The theorem then fails.
  For example, take `F = G` the swap functionality `(x, y) ↦ (y, x)` on bits, one call on the
  parties' inputs, `main` with no moves whose parties output their answers, and `ρ` the
  three-message protocol in which Alice sends `x`, Bob `y`, and Alice `y` (her output, as last
  mover). In `H.compose ρ` (six moves, `main`'s prover first) Bob's last message is a filler, so
  he outputs `[]`, not `x`. As `PolyExpr.eval` is monotone, `0 < main.rounds(n)` for a single
  `n` would suffice up to finitely many `n`; the uniform form is stated.
- **Uniform bounds**, as in `HBCSecure`: one negligible bound for all inputs of each length.

## Main definitions

* None: the composed protocol is defined in `Compose.lean` and its phases in
  `ComposePhases.lean`.

## Main results

* `HybridProtocol.exists_runExec_eq_transcript`, `exists_mainExec_eq_transcript`: the runs and
  the main phase are transcripts of `ρ` and `main` on inputs and coins of the right types.
* `HybridProtocol.compose_msg_bound`: the messages of `H.compose ρ` are polynomially bounded.
* `HybridProtocol.composeP_efficient`, `composeV_efficient` (stated; `sorry`s under their
  sketches), and `polyTime_compose` (proved from the three).
* `HybridProtocol.hbcSecure_compose` ([Gol04, Theorem 7.3.3], stated; a `sorry` under its
  sketch).

## References

* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*, Cambridge
  University Press, 2004, §7.3.1 (privacy reductions and a composition theorem), Theorem 7.3.3.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2, Definition 155.1 and Theorem 163.7 (book pp. 155–164).
-/

namespace TCSlib.Cryptography.SecureComputation

open Complexity Turing TCSlib.Cryptography

open Compose

namespace HybridProtocol

/-! ### Polynomial time -/

section Efficiency

variable {G : Functionality} (H : HybridProtocol G) (ρ : Protocol)

/-- A list of length `c` is the encoding of a `c`-bit string. -/
private theorem exists_ofFn_eq {c : ℕ} {l : List Bool} (h : l.length = c) :
    ∃ t : Fin c → Bool, List.ofFn t = l := by
  subst h
  exact ⟨fun i => l[i.1], List.ofFn_getElem l⟩

/-- Alice's honest answers have `calls(|x|) · G.outA(|x|)` bits. -/
theorem length_answersRealA (x zA zB rA rB : List Bool) :
    (H.answersRealA ρ x zA zB rA rB).length = H.calls.eval x.length * G.outA.eval x.length := by
  rw [answersRealA_eq, List.length_flatten, List.map_ofFn]
  simp only [Function.comp_def, List.length_ofFn, List.ofFn_const, List.sum_replicate,
    smul_eq_mul]

/-- Bob's honest answers have `calls(|x|) · G.outB(|x|)` bits. -/
theorem length_answersRealB (x zA zB rA rB : List Bool) :
    (H.answersRealB ρ x zA zB rA rB).length = H.calls.eval x.length * G.outB.eval x.length := by
  rw [answersRealB_eq, List.length_flatten, List.map_ofFn]
  simp only [Function.comp_def, List.length_ofFn, List.ofFn_const, List.sum_replicate,
    smul_eq_mul]

/-- **The main phase is a hybrid-format execution of `main`**: on common input `1^n`, inputs of
`F`'s lengths and tapes at least as long as the `main`-tapes, the main phase of an honest
execution of `H.compose ρ` is the transcript of `main` on `⟨x, aA⟩`, `⟨y, aB⟩` for answers `aA`,
`aB` of the hybrid lengths and some coins of `main` (those answers are the honest ones, the
coins the `main`-tapes).

**Proof sketch.** The honest answers have `calls(n) · G.outA(n)` and `calls(n) · G.outB(n)` bits
(`length_answersRealA`, `length_answersRealB`), and the `main`-tapes the lengths of `main`'s
coins, so each is `List.ofFn` of a string of the right type; `mainExec` is then `main`'s
transcript on them by definition. -/
theorem exists_mainExec_eq_transcript {F : Functionality} (n : ℕ) (x : Fin (F.inA.eval n) → Bool)
    (y : Fin (F.inB.eval n) → Bool) {rA rB : List Bool}
    (hrA : H.main.P.coins.eval (List.replicate n true).length ≤ rA.length)
    (hrB : H.main.V.coins.eval (List.replicate n true).length ≤ rB.length) :
    ∃ (aA : Fin (H.calls.eval n * G.outA.eval n) → Bool)
      (aB : Fin (H.calls.eval n * G.outB.eval n) → Bool) (r : H.Coins n),
      H.mainExec ρ (List.replicate n true) (List.ofFn x) (List.ofFn y) rA rB
          (H.main.rounds.eval (List.replicate n true).length) =
        H.main.transcript (List.replicate n true) (pairEncode (List.ofFn x) (List.ofFn aA))
          (pairEncode (List.ofFn y) (List.ofFn aB)) r := by
  obtain ⟨aA, haA⟩ := exists_ofFn_eq (c := H.calls.eval n * G.outA.eval n)
    (l := H.answersRealA ρ (List.replicate n true) (List.ofFn x) (List.ofFn y) rA rB)
    (by rw [length_answersRealA, List.length_replicate])
  obtain ⟨aB, haB⟩ := exists_ofFn_eq (c := H.calls.eval n * G.outB.eval n)
    (l := H.answersRealB ρ (List.replicate n true) (List.ofFn x) (List.ofFn y) rA rB)
    (by rw [length_answersRealB, List.length_replicate])
  obtain ⟨tA, htA⟩ := exists_ofFn_eq (c := H.main.P.coinLen (List.replicate n true).length)
    (l := rA.take (H.main.P.coins.eval (List.replicate n true).length))
    (by rw [List.length_take]; exact Nat.min_eq_left hrA)
  obtain ⟨tB, htB⟩ := exists_ofFn_eq (c := H.main.V.coinLen (List.replicate n true).length)
    (l := rB.take (H.main.V.coins.eval (List.replicate n true).length))
    (by rw [List.length_take]; exact Nat.min_eq_left hrB)
  refine ⟨aA, aB, (tA, tB), ?_⟩
  rw [mainExec_eq, ← haA, ← haB, ← htA, ← htB]
  rfl

/-- **Run `j` is an execution of `ρ` on inputs of `G`'s lengths**: on common input `1^n`, for
`j < calls(n)` and composed tapes of the right lengths, the honest run `j` is the transcript of
`ρ` on some inputs of `G`'s lengths and some coins of `ρ` (the call inputs and the run tapes).

**Proof sketch.** For `j < calls(n)` the run inputs are the call inputs (`runInputA_of_lt`,
`runInputB_of_lt`), of `G`'s input lengths, and the run tapes have the lengths of `ρ`'s coins
(`length_runTape`), so each is `List.ofFn` of a string of the right type; `runExec` is then
`ρ`'s transcript on them by definition. -/
theorem exists_runExec_eq_transcript (n : ℕ) (zA zB : List Bool) {rA rB : List Bool} {j : ℕ}
    (hj : j < H.calls.eval (List.replicate n true).length)
    (hrA : rA.length = H.main.P.coins.eval (List.replicate n true).length +
      H.calls.eval (List.replicate n true).length * ρ.P.coins.eval (List.replicate n true).length)
    (hrB : rB.length = H.main.V.coins.eval (List.replicate n true).length +
      H.calls.eval (List.replicate n true).length *
        ρ.V.coins.eval (List.replicate n true).length) :
    ∃ (xA : Fin (G.inA.eval n) → Bool) (yB : Fin (G.inB.eval n) → Bool)
      (r : ρ.ExecCoins ρ.P (List.replicate n true)),
      H.runExec ρ (List.replicate n true) zA zB rA rB j
          (ρ.rounds.eval (List.replicate n true).length) =
        ρ.transcript (List.replicate n true) (List.ofFn xA) (List.ofFn yB) r := by
  obtain ⟨xA, hxA⟩ := exists_ofFn_eq (c := G.inA.eval n)
    (l := H.runInputA (List.replicate n true) zA rA j)
    (by rw [H.runInputA_of_lt _ _ _ hj, List.length_ofFn, List.length_replicate])
  obtain ⟨yB, hyB⟩ := exists_ofFn_eq (c := G.inB.eval n)
    (l := H.runInputB (List.replicate n true) zB rB j)
    (by rw [H.runInputB_of_lt _ _ _ hj, List.length_ofFn, List.length_replicate])
  obtain ⟨tA, htA⟩ := exists_ofFn_eq (c := ρ.P.coinLen (List.replicate n true).length)
    (l := runTape (H.main.P.coins.eval (List.replicate n true).length)
      (ρ.P.coins.eval (List.replicate n true).length) j rA) (length_runTape hrA hj)
  obtain ⟨tB, htB⟩ := exists_ofFn_eq (c := ρ.V.coinLen (List.replicate n true).length)
    (l := runTape (H.main.V.coins.eval (List.replicate n true).length)
      (ρ.V.coins.eval (List.replicate n true).length) j rB) (length_runTape hrB hj)
  refine ⟨xA, yB, (tA, tB), ?_⟩
  rw [runExec_eq, ← hxA, ← hyB, ← htA, ← htB]
  rfl

/-- `ρ`'s move `p < R` of the honest run `j` is a message of that run's transcript. -/
theorem runMsg_mem (x zA zB rA rB : List Bool) (j : ℕ) {p : ℕ}
    (hp : p < ρ.rounds.eval x.length) :
    H.runMsg ρ x zA zB rA rB j p ∈ (H.runExec ρ x zA zB rA rB j (ρ.rounds.eval x.length)).1 ++
      (H.runExec ρ x zA zB rA rB j (ρ.rounds.eval x.length)).2 := by
  rw [runExec_eq, exec_eq_map, runMsg_eq]
  by_cases hm : moverIsV ρ.verifierFirst p = true
  · exact List.mem_append_left _
      (List.mem_map.2 ⟨p, List.mem_filter.2 ⟨List.mem_range.2 hp, hm⟩, rfl⟩)
  · refine List.mem_append_right _
      (List.mem_map.2 ⟨p, List.mem_filter.2 ⟨List.mem_range.2 hp, ?_⟩, rfl⟩)
    simpa using hm

/-- **The messages of `H.compose ρ` are polynomially bounded** (the message half of
`Functionality.PolyTime`): every message of an honest execution on common input `1^n` and inputs
of `F`'s lengths has at most `B_main(n) + B_ρ(n)` bits, with `B_main` the bound of `H.PolyTime`
and `B_ρ` that of `G.PolyTime ρ`.

**Proof sketch.** By `compose_transcript` a message is a filler (empty), a message of an honest
run, or a message of the main phase.
1. A run message is `ρ`'s move in the honest run `j < calls(n)` (`runMsg_mem`), a transcript of
   `ρ` on inputs of `G`'s lengths (`exists_runExec_eq_transcript`): at most `B_ρ(n)` bits.
2. A main-phase message is a message of `main` on `⟨x, aA⟩`, `⟨y, aB⟩` with answers of the
   hybrid lengths (`exists_mainExec_eq_transcript`); `H.PolyTime` bounds those for **any** such
   answers: at most `B_main(n)` bits. -/
theorem compose_msg_bound {F : Functionality} (hH : H.PolyTime F) (hρ : G.PolyTime ρ) :
    ∃ B : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool)
      (r : (H.compose ρ).ExecCoins (H.compose ρ).P (List.replicate n true)),
      ∀ msg ∈ ((H.compose ρ).transcript (List.replicate n true) (List.ofFn x) (List.ofFn y) r).1 ++
          ((H.compose ρ).transcript (List.replicate n true) (List.ofFn x) (List.ofFn y) r).2,
        msg.length ≤ B.eval n := by
  obtain ⟨-, -, -, -, B₁, hB₁⟩ := hH
  obtain ⟨-, -, B₂, hB₂⟩ := hρ
  refine ⟨.add B₁ B₂, fun n x y r msg hmsg => ?_⟩
  rw [PolyExpr.eval_add]
  have hrA : (List.ofFn r.1).length = H.main.P.coins.eval (List.replicate n true).length +
      H.calls.eval (List.replicate n true).length *
        ρ.P.coins.eval (List.replicate n true).length := by
    rw [List.length_ofFn]
    rfl
  have hrB : (List.ofFn r.2).length = H.main.V.coins.eval (List.replicate n true).length +
      H.calls.eval (List.replicate n true).length *
        ρ.V.coins.eval (List.replicate n true).length := by
    rw [List.length_ofFn]
    rfl
  -- a message of an honest run
  have hrun : ∀ j p, j < H.calls.eval (List.replicate n true).length →
      p < ρ.rounds.eval (List.replicate n true).length →
      (H.runMsg ρ (List.replicate n true) (List.ofFn x) (List.ofFn y) (List.ofFn r.1)
        (List.ofFn r.2) j p).length ≤ B₁.eval n + B₂.eval n := by
    intro j p hj hp
    obtain ⟨xA, yB, r', h⟩ := H.exists_runExec_eq_transcript ρ n (List.ofFn x) (List.ofFn y) hj
      hrA hrB
    have hmem := H.runMsg_mem ρ (List.replicate n true) (List.ofFn x) (List.ofFn y)
      (List.ofFn r.1) (List.ofFn r.2) j hp
    rw [h] at hmem
    exact (hB₂ n xA yB r' _ hmem).trans (Nat.le_add_left _ _)
  -- a message of the main phase
  obtain ⟨aA, aB, r', hmain⟩ := H.exists_mainExec_eq_transcript ρ n x y
    (rA := List.ofFn r.1) (rB := List.ofFn r.2) (by omega) (by omega)
  have hmainB : ∀ msg ∈ (H.mainExec ρ (List.replicate n true) (List.ofFn x) (List.ofFn y)
      (List.ofFn r.1) (List.ofFn r.2) (H.main.rounds.eval (List.replicate n true).length)).1 ++
      (H.mainExec ρ (List.replicate n true) (List.ofFn x) (List.ofFn y)
        (List.ofFn r.1) (List.ofFn r.2) (H.main.rounds.eval (List.replicate n true).length)).2,
      msg.length ≤ B₁.eval n + B₂.eval n := by
    intro msg hmsg
    rw [hmain] at hmsg
    exact (hB₁ n x y aA aB r' msg hmsg).trans (Nat.le_add_right _ _)
  rw [compose_transcript] at hmsg
  simp only [List.mem_append, List.mem_map, List.mem_range] at hmsg
  have hR : ∀ q, q < H.calls.eval (List.replicate n true).length *
      ρ.rounds.eval (List.replicate n true).length →
      q / ρ.rounds.eval (List.replicate n true).length <
        H.calls.eval (List.replicate n true).length ∧
      q % ρ.rounds.eval (List.replicate n true).length <
        ρ.rounds.eval (List.replicate n true).length := by
    intro q hq
    have hR0 : 0 < ρ.rounds.eval (List.replicate n true).length := by
      rcases Nat.eq_zero_or_pos (ρ.rounds.eval (List.replicate n true).length) with h | h
      · rw [h, Nat.mul_zero] at hq
        omega
      · exact h
    exact ⟨(Nat.div_lt_iff_lt_mul hR0).2 hq, Nat.mod_lt _ hR0⟩
  rcases hmsg with ((⟨q, hq, rfl⟩ | hm) | ((⟨q, hq, rfl⟩ | hm) | hm))
  · rw [slotFromB_eq]
    split_ifs
    · exact hrun _ _ (hR q hq).1 (hR q hq).2
    · exact Nat.zero_le _
  · exact hmainB msg (List.mem_append_left _ hm)
  · rw [slotFromA_eq]
    split_ifs
    · exact Nat.zero_le _
    · exact hrun _ _ (hR q hq).1 (hR q hq).2
  · rw [List.eq_of_mem_replicate hm]
    exact Nat.zero_le _
  · exact hmainB msg (List.mem_append_right _ hm)

/-- **Alice's strategy in `H.compose ρ` is PPT** (`Strategy.Efficient`), when `main`'s and `ρ`'s
are and the call inputs are polynomial-time.

**Proof sketch.** A uniform machine with the coin polynomial `main.P.coins + calls · ρ.P.coins`
computes `composeP.next` on `⟨⟨x, z⟩, hist⟩` and the tape `r`:
1. it computes `n = |x|`, `L`, `R`, `|hist|` and the pair, run and position indices;
2. it recomputes the run inputs with the polynomial-time function of `H.PolyTime` on
   `⟨1^n, ⟨z, ⟨r_main, 1^j⟩⟩⟩`, cuts the run tapes out of `r`, and reads the run histories from
   `hist` (`slotMsgs`);
3. it runs the uniform machine of `ρ.P` once (a run move) or `L(n)` times (the answers), and that
   of `main.P` once, each on an input of length polynomial in its own.

Each piece is polynomial-time on the raw layout, and `L` is a polynomial, so the composition is
(`NUPPT.ofPolyTimeUniform`). -/
theorem composeP_efficient {F : Functionality} (hH : H.PolyTime F) (hρ : G.PolyTime ρ) :
    (H.composeP ρ).Efficient := by
  sorry

/-- **Bob's strategy in `H.compose ρ` is PPT** (`Strategy.Efficient`), when `main`'s and `ρ`'s
are and the call inputs are polynomial-time.

**Proof sketch.** As for Alice (`composeP_efficient`), with `ρ.V`, `main.V`, the call-input
function for Bob, and the coin polynomial `main.V.coins + calls · ρ.V.coins`. -/
theorem composeV_efficient {F : Functionality} (hH : H.PolyTime F) (hρ : G.PolyTime ρ) :
    (H.composeV ρ).Efficient := by
  sorry

/-- **The composed parties run in polynomial time** [Gol04, §7.3.1, the efficiency of the
protocol of Theorem 7.3.3]: if `H` runs in polynomial time on `F`'s inputs (`H.PolyTime F`) and
`ρ` on `G`'s (`G.PolyTime ρ`), then `H.compose ρ` runs in polynomial time on `F`'s inputs.
The two strategies are PPT (`composeP_efficient`, `composeV_efficient`; `sorry`s under their
sketches), and the messages are bounded by `B_main + B_ρ` (`compose_msg_bound`, proved). The
message bound uses that `H.PolyTime` bounds `main`'s messages for **any** answers of the right
lengths, since `main` runs on `ρ`'s outputs. -/
theorem polyTime_compose {F : Functionality} (hH : H.PolyTime F) (hρ : G.PolyTime ρ) :
    F.PolyTime (H.compose ρ) :=
  ⟨H.composeP_efficient ρ hH hρ, H.composeV_efficient ρ hH hρ, H.compose_msg_bound ρ hH hρ⟩

end Efficiency

/-! ### The composition theorem -/

/-- **The composition theorem for the semi-honest model** [Gol04, §7.3.1, Theorem 7.3.3; the
numbering is cited from memory and should be verified at audit]: if `H` is honest-but-curious
secure for `F` in the `G`-hybrid model (`H.HBCSecure F`) and `ρ` is honest-but-curious secure for
`G` ([PS10, Definition 155.1], `HBCSecure ρ G`), then `H.compose ρ` is honest-but-curious secure
for `F`, provided `main` has at least one move at every `n`.

**Deviations.** Ideal calls first, with the layout of `Compose.lean`; Definition 155.1 with
polynomial-time parties and one negligible bound for all inputs of each length; and the
hypothesis `hM` that `main` has at least one move. Without `hM` the statement is false under
D8's output convention (the module docstring gives an example): if `main.rounds(n) = 0`, the
last move of `H.compose ρ` is a run move or the leading filler, and its sender outputs that
message instead of its output in `main`.

**Proof sketch.** Write `L = calls(n)`. Efficiency is `polyTime_compose`. Fix a non-uniform
PPT distinguisher `D`. Alice's side follows; Bob's is symmetric.
1. *The simulator* `S_A`, on `⟨1^n, ⟨x, f_A(x, y)⟩⟩`: run the hybrid simulator `S_A^H` on the
   same input and read its output as a view of `main` with private input `⟨x, a⟩` and tape
   `r_main`. For each `j < L`, recompute Alice's input to call `j`, `callA(n, x, r_main, j)`
   (polynomial time by `H.PolyTime`), and run `ρ`'s simulator `S_A^ρ` on it and the `j`-th
   `G.outA(n)`-bit block of `a`, with fresh coins; read its output as a view of `ρ` (tape `r_j`,
   messages `m_j`). Output Alice's view of `H.compose ρ`: input `x`, tape
   `r_main r_0 ⋯ r_{L−1}` (each cut to its length), and the messages `m_j` at Bob's pairs, with
   fillers, followed by the hybrid view's messages (the layout of `compose_viewP`). `S_A` makes
   `L(n) + 1` simulator calls and polynomial-time work: a non-uniform PPT.
2. *Correct answers.* By the output clause of `HBCSecure ρ G`, applied to the distinguisher that
   compares the second component of Bob's `ρ`-sample with a string given as advice (Alice's
   ideal output on the worst-case inputs of length `n`, so one non-uniform machine serves every
   `n`), Alice's `ρ`-output differs from her ideal output with probability at most `ε₁(n)`,
   uniformly over the inputs (`ε` before the inputs in `HBCSecure`); likewise Bob's. By the
   union bound, except with probability `2L(n)ε₁(n)` over the coins, every run's outputs are
   the ideal answers, read back exactly by `padFin` (`padFin_ofFn`). Then `answersRealA`,
   `answersRealB` are the hybrid answers `answersA`, `answersB`, and the main phase and both
   outputs are those of the hybrid execution (`compose_exec_main`, `compose_outV`, using `hM`).
   So the real sample is within statistical distance `2L(n)ε₁(n)` of the sample in which `main`
   runs on the ideal answers.
3. *Hybrid argument over the runs.* In `H_i` the first `i` runs of Alice's view are replaced by
   `S_A^ρ` on the call inputs and the ideal answers, the others are real, and `main` runs on the
   ideal answers. `H_i` and `H_{i+1}` differ in run `i` only (`compose_exec_runs`: run `i` is an
   honest execution of `ρ` on the call inputs and the run tapes, independent of the other
   runs given the `main`-tapes). A distinguisher between them gives one for `ρ`'s Alice side,
   holding as advice the worst-case `i`, inputs, `main`-tapes and ideal answers for length `n`;
   it simulates the other runs, runs `main` on the ideal answers, and assembles the sample in
   polynomial time. So `|Pr[H_i] − Pr[H_{i+1}]| ≤ ε₂(n)`, and `H_0`, `H_L` are within `L(n)ε₂(n)`.
4. *The hybrid model.* `H_L` is the post-processing `Φ` of step 1 applied to the hybrid real
   sample `H.realA F n x y` (Bob's output there is `main`'s, as in `H_L`), and `idealA S_A` is
   `Φ` applied to `F.idealA S_A^H`. `D ∘ Φ` is a non-uniform PPT, so `H.HBCSecure F` bounds the
   remaining distance by `ε₃(n)`.
5. In total `L(n)(2ε₁(n) + ε₂(n)) + ε₃(n)`, negligible since `L` is a polynomial. -/
theorem hbcSecure_compose {G F : Functionality} (H : HybridProtocol G) (ρ : Protocol)
    (hM : ∀ n, 0 < H.main.rounds.eval n) (hH : H.HBCSecure F)
    (hρ : SecureComputation.HBCSecure ρ G) : SecureComputation.HBCSecure (H.compose ρ) F := by
  sorry

end HybridProtocol

end TCSlib.Cryptography.SecureComputation
