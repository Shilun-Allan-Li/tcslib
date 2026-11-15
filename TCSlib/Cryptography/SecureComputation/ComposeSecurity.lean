/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.ComposePhases
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Machines
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Efficiency
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Probability
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Reductions
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Assembly
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Runs
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Bounds
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Sim
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Chain
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Accept
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Correct
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Template
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Lengths
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.SideA
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.SideB

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The composition theorem for the semi-honest model

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
answers of the right lengths, since in `H.compose ρ` `main` runs on `ρ`'s outputs. The composed
strategies are PPT (`composeP_efficient`, `composeV_efficient`): each is a polynomial-time
function of the machine layout built from `main`'s and `ρ`'s machines and the call-input
functions (`ComposeSecurity/Efficiency.lean`).

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

## Contents

* `ComposeSecurity/Machines.lean`: polynomial-time machines on encoded histories (loops over a
  data-dependent range, the interleaved-slot map, strategies as functions of the layout).
* `ComposeSecurity/Efficiency.lean`: the composed parties as polynomial-time functions of the
  machine layout.
* `ComposeSecurity/Probability.lean`: distinguishing-advantage tools (the statistical switch,
  fixing coordinates, a negligible function times a polynomial).
* `ComposeSecurity/Reductions.lean`: machines with advice-dependent pre- and post-processing.
* `ComposeSecurity/Assembly.lean`: a view of the composed protocol assembled from run views.
* `ComposeSecurity/Runs.lean`: the coins of the composed protocol run by run, and the real
  samples when every run gives the ideal answers.
* `ComposeSecurity/Bounds.lean`: lengths of encodings, transcripts and machine outputs.
* `ComposeSecurity/Sim.lean`: the post-processing `Φ`, the simulators and the reduction to the
  hybrid model.
* `ComposeSecurity/Chain.lean`: the hybrid argument over the runs.
* `ComposeSecurity/Accept.lean`: acceptance of machines with split coins; test machines.
* `ComposeSecurity/Correct.lean`: a secure protocol is correct; the union bound over the runs.
* `ComposeSecurity/Template.lean`: the reduction of one hybrid step to the sub-protocol.
* `ComposeSecurity/Lengths.lean`: polynomial bounds on the words of the templates.
* `ComposeSecurity/SideA.lean`, `ComposeSecurity/SideB.lean`: Alice's and Bob's sides of the
  composition theorem.

## Main results

* `HybridProtocol.exists_runExec_eq_transcript`, `exists_mainExec_eq_transcript`: the runs and
  the main phase are transcripts of `ρ` and `main` on inputs and coins of the right types.
* `HybridProtocol.compose_msg_bound`: the messages of `H.compose ρ` are polynomially bounded.
* `HybridProtocol.composeP_efficient`, `composeV_efficient`: the composed strategies are PPT;
  `polyTime_compose` (proved from the three).
* `HybridProtocol.hbcSecure_compose` ([Gol04, Theorem 7.3.3]): from Alice's and Bob's sides
  (`exists_simA`, `exists_simB`).

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
    (by rw [Strategy.coinLen_eq, List.length_take]; exact Nat.min_eq_left hrA)
  obtain ⟨tB, htB⟩ := exists_ofFn_eq (c := H.main.V.coinLen (List.replicate n true).length)
    (l := rB.take (H.main.V.coins.eval (List.replicate n true).length))
    (by rw [Strategy.coinLen_eq, List.length_take]; exact Nat.min_eq_left hrB)
  refine ⟨aA, aB, (tA, tB), ?_⟩
  rw [mainExec_eq, ← haA, ← haB, ← htA, ← htB]
  rw [Protocol.transcript_eq_transcriptWith, Protocol.transcriptWith_eq]

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
      (ρ.P.coins.eval (List.replicate n true).length) j rA)
    ((length_runTape hrA hj).trans
      (Strategy.coinLen_eq ρ.P (List.replicate n true).length).symm)
  obtain ⟨tB, htB⟩ := exists_ofFn_eq (c := ρ.V.coinLen (List.replicate n true).length)
    (l := runTape (H.main.V.coins.eval (List.replicate n true).length)
      (ρ.V.coins.eval (List.replicate n true).length) j rB)
    ((length_runTape hrB hj).trans
      (Strategy.coinLen_eq ρ.V (List.replicate n true).length).symm)
  refine ⟨xA, yB, (tA, tB), ?_⟩
  rw [runExec_eq, ← hxA, ← hyB, ← htA, ← htB]
  rw [Protocol.transcript_eq_transcriptWith, Protocol.transcriptWith_eq]

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
  obtain ⟨-, -, -, -, B₁, hB₁⟩ := (HybridProtocol.polyTime_iff H F).mp hH
  obtain ⟨-, -, B₂, hB₂⟩ := (Functionality.polyTime_iff G ρ).mp hρ
  refine ⟨.add B₁ B₂, fun n x y r msg hmsg => ?_⟩
  rw [PolyExpr.eval_add]
  have hrA : (List.ofFn r.1).length = H.main.P.coins.eval (List.replicate n true).length +
      H.calls.eval (List.replicate n true).length *
        ρ.P.coins.eval (List.replicate n true).length :=
    (List.length_ofFn (f := r.1)).trans
      ((H.compose_P_coinLen ρ (List.replicate n true).length).trans
        (congrArg₂ (fun a b : ℕ => a + H.calls.eval (List.replicate n true).length * b)
          (Strategy.coinLen_eq H.main.P (List.replicate n true).length)
          (Strategy.coinLen_eq ρ.P (List.replicate n true).length)))
  have hrB : (List.ofFn r.2).length = H.main.V.coins.eval (List.replicate n true).length +
      H.calls.eval (List.replicate n true).length *
        ρ.V.coins.eval (List.replicate n true).length :=
    (List.length_ofFn (f := r.2)).trans
      ((H.compose_V_coinLen ρ (List.replicate n true).length).trans
        (congrArg₂ (fun a b : ℕ => a + H.calls.eval (List.replicate n true).length * b)
          (Strategy.coinLen_eq H.main.V (List.replicate n true).length)
          (Strategy.coinLen_eq ρ.V (List.replicate n true).length)))
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

**Proof sketch.** Take polynomial-time functions of the machine layout for the efficient
strategies `ρ.P` and `main.P` (`ComposeMachines.Efficient.exists_polyTime`) and Alice's
call-input function from `H.PolyTime`. Alice's next message is `composePW` on the layout
`⟨⟨⟨1^n, ⟨⟨x, z⟩, hist⟩⟩, []⟩, r⟩` (`composeP_next_eq_composePW`):
1. the number `k = |hist|` of messages received, `L`, `R`, `k / R`, `k % R` and the mover test
   are unary computations (`GI.msgCount_poly`, `divNum_poly`, `modNum_poly`);
2. a run move is one activation of `ρ.P`'s machine on the call input (recomputed from the
   `main`-tape), the run tape cut from `r` and the run's messages read at the interleaved
   pairs (`ComposeMachines.runW`, `ComposeMachines.polyTimeComputable_slots`);
3. the main move is one activation of `main.P`'s machine on `⟨z, answers⟩` and the messages
   after the runs, the answers being `L(n)` such activations of `ρ.P`'s machine, padded and
   concatenated (`ComposeMachines.ansW`, `ComposeMachines.polyTimeComputable_flatMap_range`).
So `composePW` is polynomial-time (`polyTimeComputable_composePW`), and its uniform machine with
the coin polynomial `main.P.coins + calls · ρ.P.coins` computes `composeP`
(`GI.efficient_of_polyTime`). -/
theorem composeP_efficient {F : Functionality} (hH : H.PolyTime F) (hρ : G.PolyTime ρ) :
    (H.composeP ρ).Efficient := by
  obtain ⟨hmain, -, ⟨fA, hfA, hcallA⟩, -, -⟩ := (HybridProtocol.polyTime_iff H F).mp hH
  obtain ⟨hρP, -, -⟩ := (Functionality.polyTime_iff G ρ).mp hρ
  obtain ⟨Fρ, hFρ, hρeq⟩ := ComposeMachines.Efficient.exists_polyTime hρP
  obtain ⟨Fm, hFm, hmeq⟩ := ComposeMachines.Efficient.exists_polyTime hmain
  exact GI.efficient_of_polyTime _ (H.polyTimeComputable_composePW ρ hFρ hFm hfA)
    (H.composeP_next_eq_composePW ρ hρeq hmeq hcallA)

/-- **Bob's strategy in `H.compose ρ` is PPT** (`Strategy.Efficient`), when `main`'s and `ρ`'s
are and the call inputs are polynomial-time.

**Proof sketch.** As for Alice (`composeP_efficient`): Bob's next message is `composeVW` on the
layout (`composeV_next_eq_composeVW`), with `ρ.V`'s and `main.V`'s machines, Bob's call-input
function, the count `k = |hist| − 1`, the selector of Alice's moves, the drop count
`L·R + lead` before the main phase, and the coin polynomial `main.V.coins + calls · ρ.V.coins`;
`composeVW` is polynomial-time (`polyTimeComputable_composeVW`). -/
theorem composeV_efficient {F : Functionality} (hH : H.PolyTime F) (hρ : G.PolyTime ρ) :
    (H.composeV ρ).Efficient := by
  obtain ⟨-, hmain, -, ⟨fB, hfB, hcallB⟩, -⟩ := (HybridProtocol.polyTime_iff H F).mp hH
  obtain ⟨-, hρV, -⟩ := (Functionality.polyTime_iff G ρ).mp hρ
  obtain ⟨Fρ, hFρ, hρeq⟩ := ComposeMachines.Efficient.exists_polyTime hρV
  obtain ⟨Fm, hFm, hmeq⟩ := ComposeMachines.Efficient.exists_polyTime hmain
  exact GI.efficient_of_polyTime _ (H.polyTimeComputable_composeVW ρ hFρ hFm hfB)
    (H.composeV_next_eq_composeVW ρ hρeq hmeq hcallB)

/-- **The composed parties run in polynomial time** [Gol04, §7.3.1, the efficiency of the
protocol of Theorem 7.3.3]: if `H` runs in polynomial time on `F`'s inputs (`H.PolyTime F`) and
`ρ` on `G`'s (`G.PolyTime ρ`), then `H.compose ρ` runs in polynomial time on `F`'s inputs.
The two strategies are PPT (`composeP_efficient`, `composeV_efficient`, proved), and the
messages are bounded by `B_main + B_ρ` (`compose_msg_bound`, proved). The
message bound uses that `H.PolyTime` bounds `main`'s messages for **any** answers of the right
lengths, since `main` runs on `ρ`'s outputs. -/
theorem polyTime_compose {F : Functionality} (hH : H.PolyTime F) (hρ : G.PolyTime ρ) :
    F.PolyTime (H.compose ρ) :=
  (Functionality.polyTime_iff F (H.compose ρ)).mpr
    ⟨Eq.mpr (congrArg Strategy.Efficient (H.compose_P ρ))
        (H.composeP_efficient ρ hH hρ),
      Eq.mpr (congrArg Strategy.Efficient (H.compose_V ρ))
        (H.composeV_efficient ρ hH hρ),
      H.compose_msg_bound ρ hH hρ⟩

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

**Proof sketch.** Write `L = calls(n)`. Efficiency is `polyTime_compose`. Alice's side is
`exists_simA` (`ComposeSecurity/SideA.lean`), Bob's is symmetric (`exists_simB`); for a
distinguisher `D` the sum of the two negligible bounds bounds both advantages. On Alice's side:
1. *The simulator* `S_A` (`ComposeSim.exists_simulator`), on `⟨1^n, ⟨x, f_A(x, y)⟩⟩`: run the
   hybrid simulator `S_A^H` on the same input and read its output as a view of `main` with
   private input `⟨x, a⟩` and tape `r_main`. For each `j < L`, recompute Alice's input to call
   `j`, `callA(n, x, r_main, j)` (polynomial time by `H.PolyTime`), and run `ρ`'s simulator
   `S_A^ρ` on it and the `j`-th `G.outA(n)`-bit block of `a`, with the `j`-th block of fresh
   coins. Output Alice's view of `H.compose ρ` (`ComposeSim.asmView`): input `x`, tape
   `r_main r_0 ⋯ r_{L−1}` (each cut or padded to its length), and the run messages at Bob's
   pairs, with fillers, followed by the hybrid view's messages (the layout of `compose_viewP`).
2. *Correct answers* (`ComposeProb.exists_correct`). The output clause of `HBCSecure ρ G`,
   applied to the machine that compares the second component of a sample with an advice string
   (each party's ideal output on the worst-case inputs of length `n`), bounds the probability
   that a party's `ρ`-output is not its ideal output by `ε_c(n)`, uniformly over the inputs. By
   the union bound, every run gives the ideal answers except with probability `L(n)ε_c(n)`
   (`uprob_not_goodRuns_le`), and then the real sample is the assembled view of the real run
   views with the hybrid main phase and Bob's output in `main` (`realA_compose_eq`, using `hM`;
   the statistical switch `ComposeProb.distAdv_le_uprob_of_eq`).
3. *Hybrid argument over the runs* (`ComposeProb.abs_chain_le`). In hybrid `i` the first `i`
   run views are `S_A^ρ`'s outputs on the call inputs and the ideal answers. Resampling run `i`
   at fixed other coordinates (`exists_hyb_step`), neighbouring hybrids give a distinguisher for
   `ρ`'s Alice side that holds as advice the template of the worst-case inputs, run index and
   coordinates at length `n`: the header of the view, the other runs' words and Bob's output,
   of polynomial length (`exists_tmplA_bound`). It inserts the `ρ`-view and assembles the
   sample in polynomial time (`ComposeSim.exists_gap_le`), so each step is within `ε₂(n)`.
4. *The hybrid model.* With every run simulated the sample is `Φ` applied to the hybrid real
   sample `H.realA F n x y` (`acceptProb_realA_dPhi`), and `idealA S_A` is `Φ` applied to
   `F.idealA S_A^H` (`ComposeProb.acceptProb_post_pre`). `D ∘ Φ` is a non-uniform PPT
   (`ComposeSim.exists_dPhi`), so `H.HBCSecure F` bounds the remaining distance by `ε₃(n)`.
5. In total `L(n)(ε_c(n) + ε₂(n)) + ε₃(n)`, negligible since `L` is a polynomial
   (`ComposeProb.negligible_polyExpr_mul`). -/
theorem hbcSecure_compose {G F : Functionality} (H : HybridProtocol G) (ρ : Protocol)
    (hM : ∀ n, 0 < H.main.rounds.eval n) (hH : H.HBCSecure F)
    (hρ : SecureComputation.HBCSecure ρ G) : SecureComputation.HBCSecure (H.compose ρ) F := by
  have hHpt := ((HybridProtocol.hbcSecure_iff H F).mp hH).1
  have hρpt := ((SecureComputation.hbcSecure_iff ρ G).mp hρ).1
  obtain ⟨SA, hSA⟩ := H.exists_simA ρ hM hH hρ
  obtain ⟨SB, hSB⟩ := H.exists_simB ρ hM hH hρ
  refine (SecureComputation.hbcSecure_iff (H.compose ρ) F).mpr
    ⟨H.polyTime_compose ρ hHpt hρpt, SA, SB, fun D => ?_⟩
  obtain ⟨εA, hεA, hA⟩ := hSA D
  obtain ⟨εB, hεB, hB⟩ := hSB D
  refine ⟨fun n => εA n + εB n, hεA.add hεB, fun n x y => ⟨?_, ?_⟩⟩
  · -- `εB n` bounds a distinguishing advantage, so it is nonnegative
    have h0 : 0 ≤ εB n := (abs_nonneg _).trans ((distAdv_def _ _ _).symm.le.trans (hB n x y))
    exact (hA n x y).trans (le_add_of_nonneg_right h0)
  · have h0 : 0 ≤ εA n := (abs_nonneg _).trans ((distAdv_def _ _ _).symm.le.trans (hA n x y))
    exact (hB n x y).trans (le_add_of_nonneg_left h0)

end HybridProtocol

end TCSlib.Cryptography.SecureComputation
