/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.SpaceComplexity.Logspace.InputAccess

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The oracle-input simulator: logspace preimages along implicit functions

[AB09, proof of Lemma 4.17, Fig. 4.3]: to decide whether `f x ∈ C`, run `C`'s logspace decider
`M` on a **virtual input** `f x` that is never written down. Whenever `M` reads its input, its
head position (in binary) is a query `⟨x, i⟩` to the length and bit deciders of `f`. The
received `LogProg` call protocol does not host this by itself. A call's virtual input is read
physically, as the whole input or its leading run of `1`s followed by register words, and
nothing serves a decider's input symbols through further calls (P0 reception audit,
`audits/ch34-p0-findings.md`, note 10). This file adds the missing engine as a register-tape
program on the received compiler.

The **oracle-input simulator** `Complexity.LogProg.OIS.prog M` keeps `M`'s work tapes on
registers `0, …, M.k − 1`, where they are touched only by `M`'s own transitions. It keeps `M`'s
input position `p` as the index `p − 1` in binary on the last register `q` (with `p = 0`, the
left blank, recorded in the control state). Each step of `M` runs as follows:

1. one `whole`-mode call on `[q]` asks the length decider whether `p − 1 < |f x|`;
2. if so, a second call asks the bit decider for the symbol;
3. one ordinary step applies `M`'s transition to the work registers;
4. the increment and decrement fragments move `q` as `M`'s clamped input move dictates.

Phase P4.4b of `AroraBarakChapters3-4Plan.md`; `audits/ch4-p44-resolutions-addendum.md`
records it as the route of `Complexity.mem_LOGSPACE_of_logspaceReducible`. The simulator is
campaign-owned and lives here (decision D3), beside its only class-level corollary.

## Main definitions

* `Complexity.LogProg.OIS.Ph`, `OIS.tr`, `OIS.call` — the phases, ordinary transitions and
  call nodes of the simulator.
* `Complexity.LogProg.OIS.prog`, `OIS.start` — the simulator program and its start state.
* `Complexity.LogProg.OIS.lo`, `OIS.hi` — its register ranges.

## Main results

* `Complexity.LogProg.OIS.run` — the run contract: against any oracle answering the two
  queries truthfully, the program halts with `M`'s output on the virtual input, inside the
  ranges, with well-formed calls (sorried; phase-P4.4b statement).
* `Complexity.LogProg.OIS.compile_decides` — the space contract: compiled against a bank of
  the two deciders, it computes `M`'s output on the virtual input within the ranges plus the
  bank's space (sorried; phase-P4.4b statement).
* `Complexity.mem_LOGSPACE_preimage` — logspace preimages along implicitly logspace
  computable maps are in `L` (sorried; phase-P4.4b statement).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.3, Lemma 4.17 and its proof, Figure 4.3.)
-/

namespace Complexity

open Turing

namespace LogProg.OIS

/-- The phases of the simulator: the length call (`ask`) and the bit call (`bit`); the
simulated step with the symbol read (`work a lb`, `lb` marking the left blank); the zero test
before a left move (`zt`); the increment (`iC`, `iB`) and decrement (`dD`, `dL`, `dE`, `dB`)
of the index register. -/
inductive Ph where
  | ask | bit
  | work (a : Option Bool) (lb : Bool)
  | zt
  | iC | iB
  | dD | dL | dE | dB
  deriving DecidableEq, Fintype

variable (M : FinTM Bool)

/-- The index register of the simulator, the last one. -/
abbrev q : Fin (M.k + 1) := Fin.last M.k

/-- The phase after a simulated step, from the decider's input move `d`, at the left blank
(`lb`) or at the right blank (`rb`): from the left blank, a right move reaches position `1`
(index `0`); elsewhere a left move first tests the index for zero, and a right move increments
it unless clamped at the right blank. -/
def nextPh (d : SignType) (lb rb : Bool) : Ph :=
  if lb then (if d = 1 then .ask else .work none true)
  else if d = -1 then .zt
  else if d = 1 ∧ rb = false then .iC
  else .ask

/-- The decider's action on the work registers: input head and index register still, output
forwarded, the next phase by `nextPh`. -/
def liftAct (A : Action M.k Bool M.State) (lb rb : Bool) : Action (M.k + 1) Bool (M.State × Ph) :=
  ⟨0, Fin.lastCases (none, 0) A.workTapes, A.output,
    A.state.map fun s' => (s', nextPh A.inputTape lb rb)⟩

/-- **The ordinary transitions of the simulator.** `work a lb` applies `M`'s transition at the
symbol `a` (at the right blank exactly when `a = none` and not `lb`); `zt` reads the index
register's cell `0` (blank iff the index is `0`); the increment and decrement fragments act on
the index register and return to `ask`. The call phases' transitions are never used. -/
def tr : M.State × Ph → Option Bool → (Fin (M.k + 1) → Option Bool) →
    Action (M.k + 1) Bool (M.State × Ph)
  | (s, .work a lb), _, w =>
    liftAct M (M.tm.tr s a fun i => w i.castSucc) lb (a.isNone && !lb)
  | (s, .zt), _, w =>
    regAct (q M) none 0 (match w (q M) with
      | none => (s, .work none true)
      | some _ => (s, .dD))
  | (s, .iC), _, w => incCAct (q M) (s, .iC) (s, .iB) (w (q M))
  | (s, .iB), _, w => incBAct (q M) (s, .iB) (s, .ask) (w (q M))
  | (s, .dD), _, w => decDAct (q M) (s, .dD) (s, .dL) (s, .dB) (w (q M))
  | (s, .dL), _, w => decLAct (q M) (s, .dE) (s, .dB) (w (q M))
  | (s, .dE), _, _ => decEAct (q M) (s, .dB)
  | (s, .dB), _, w => incBAct (q M) (s, .dB) (s, .ask) (w (q M))
  | (_, .ask), _, _ => junkAct
  | (_, .bit), _, _ => junkAct

/-- **The call nodes of the simulator.** `ask` asks decider `0` (the length language) about
`⟨x, bits i⟩`, `i` the index register: on *yes* go on to `bit`; on *no* the symbol is the right
blank. `bit` asks decider `1` (the bit language) and goes on to the simulated step with the
answer. -/
def call : M.State × Ph → Option (CallSpec (M.k + 1) 2 (M.State × Ph))
  | (s, .ask) => some ⟨0, .whole, [q M], (s, .bit), (s, .work none false)⟩
  | (s, .bit) => some ⟨1, .whole, [q M], (s, .work (some true) false),
      (s, .work (some false) false)⟩
  | _ => none

/-- **The oracle-input simulator** of the decider `M`: a register-tape program over `M.k + 1`
registers calling two deciders. A hand-built program: no received layer serves a decider's
input from oracle calls. -/
def prog : RProg (M.k + 1) 2 (M.State × Ph) := ⟨⟨(M.tm.q₀, .ask), tr M⟩, call M⟩

/-- The start state of the simulator: `M`'s start state, about to ask for symbol `0`. -/
def start : M.State × Ph := (M.tm.q₀, .ask)

/-- The lower register bounds: `-S` on the work registers, `-1` on the index register. -/
def lo (S : ℕ) : Fin (M.k + 1) → ℤ := Fin.lastCases (-1) fun _ => -(S : ℤ)

/-- The upper register bounds: `S` on the work registers, `W` on the index register. -/
def hi (S W : ℕ) : Fin (M.k + 1) → ℤ := Fin.lastCases (W : ℤ) fun _ => (S : ℤ)

/-- **The run contract of the simulator** (phase P4.4b; spec, fill pending). Let `M` halt
by time `t` on the virtual input `v`. Let the oracle answer every length query
`⟨x, bits i⟩` with `i ≤ |v|`, and every bit query with `i < |v|`, truthfully. Then the
program, started on the host input `x`:

* halts with `M`'s output on `v`;
* keeps the work registers in `[-S, S]`, with `S` the space `M` uses up to `t`;
* keeps the index register in `[-1, |bits (|v| + 1)|]`;
* at every call has the input head on position `1` and the index register holding some
  `bits i`, `i ≤ |v|`, with its head on cell `0` — so the call's virtual input is
  `⟨x, bits i⟩` (`Complexity.LogProg.vword_whole₁`).

**Proof sketch.** Encode `M`'s configuration `c` on `v` as the program configuration with:

* the work tapes and heads of `c` on registers `castSucc i`;
* `bits (p − 1)` on `q`, with its head on `0` (`p` the input position of `c`; `bits 0` at
  `p = 0`);
* the host input head on `1`, and `c`'s output;
* state `(s, ask)`, or `(s, work none true)` at `p = 0`.

By induction on `n ≤ t`, the run reaches the encoding of `M.tm.runFrom (M.tm.initCfg v) n`
until `M` halts. One step goes as follows.

1. At most two calls fix the symbol `inSym v p`: by the oracle laws, the length call says
   `p − 1 < |v|`.
2. `work` applies `M.tm.tr` to the `castSucc` block (`liftAct`), so the work registers move
   exactly as `M`'s tapes.
3. The clamped move of `p` is realized by `nextPh`:
   * `inc_run` only when `p − 1 < |v|`;
   * the zero test and `dec_run` only when `p − 1 ≥ 1`;
   * a phase change at the left blank.

Intermediate configurations are those of the received fragments on `q`. The work heads are
`M`'s, so they lie in `[-S, S]` by `Turing.MultiTapeTM.abs_pos_lt_card_visited`. Template:
`ImplicitEnum.{round, rounds, run}`. -/
theorem run (x v : List Bool) (o : Fin 2 → List Bool → Bool)
    (ho0 : ∀ i ≤ v.length, o 0 (pairEncode x (Nat.bits i)) = decide (i < v.length))
    (ho1 : ∀ i < v.length, o 1 (pairEncode x (Nat.bits i)) = v.getD i false)
    (t : ℕ) (ht : (M.tm.runFrom (M.tm.initCfg v) t).state = none) :
    ∃ N, (rrun (prog M) o (Cfg.init (start M) x) N).state = none ∧
      (rrun (prog M) o (Cfg.init (start M) x) N).output =
        (M.tm.runFrom (M.tm.initCfg v) t).output ∧
      (∀ n ≤ N, ∀ r,
        lo M (M.tm.spaceUsed (M.tm.initCfg v) t) r ≤
            (rrun (prog M) o (Cfg.init (start M) x) n).workTapePos r ∧
          (rrun (prog M) o (Cfg.init (start M) x) n).workTapePos r ≤
            hi M (M.tm.spaceUsed (M.tm.initCfg v) t) (Nat.bits (v.length + 1)).length r) ∧
      ∀ n < N, ∀ l cs, (rrun (prog M) o (Cfg.init (start M) x) n).state = some l →
        (prog M).call l = some cs →
          (rrun (prog M) o (Cfg.init (start M) x) n).inputPos.val = 1 ∧
          (rrun (prog M) o (Cfg.init (start M) x) n).workTapePos (q M) = 0 ∧
          ∃ i ≤ v.length, (rrun (prog M) o (Cfg.init (start M) x) n).workTapes (q M) =
            FinTM.bufferTape (Nat.bits i) := by
  sorry

/-- **The space contract of the simulator** (phase P4.4b; spec, fill pending). Let:

* deciders `Ms j` decide `As j` in space `sb j`;
* on genuine queries about the host input `x`, `As 0` be the length language and `As 1` the
  bit language of the virtual input `v`;
* `M` compute `w` on `v` by time `t`;
* `B` bound the bank's clean-run radius on every query `⟨x, bits i⟩` with `i ≤ |v|`.

Then the simulator, compiled against the bank of the `Ms j`, computes `w` on `x`, visiting at
most `M.k (2S + 1) + (|bits (|v| + 1)| + 2) + kD (2B + 1)` work cells, where `S` is the space
`M` uses up to `t` and `kD` the bank's tape count.

**Proof sketch.** Take `OIS.run` with the oracle `j, V ↦ [V ∈ As j]`, whose laws are the two
hypotheses. Then apply `compile_space` with the ranges `OIS.lo` and `OIS.hi`; their sizes sum
to the first two terms. Each call's precondition `CallOK` comes from `OIS.run`'s call clause:

* the virtual input is `⟨x, bits i⟩` by `vword_whole₁` and `tapeWord_bufferTape`;
* the clean run of the bank is `bank_cleanRun`, weakened to `B` by `CleanRun.mono`;
* `|bits i| ≤ |bits (|v| + 1)|` by `length_bits_mono`. -/
theorem compile_decides (Ms : Fin 2 → FinTM Bool) (As : Fin 2 → Language Bool)
    (sb : Fin 2 → ℕ → ℕ) (hMs : ∀ j, (Ms j).DecidesInSpace (As j) (sb j)) (x v w : List Bool)
    (hA0 : ∀ i ≤ v.length, pairEncode x (Nat.bits i) ∈ As 0 ↔ i < v.length)
    (hA1 : ∀ i < v.length, pairEncode x (Nat.bits i) ∈ As 1 ↔ v.getD i false = true)
    (t : ℕ) (ht : M.ComputesInTime v w t) (B : ℕ)
    (hB : ∀ j, ∀ i ≤ v.length, max (sb j (pairEncode x (Nat.bits i)).length) 1 ≤ B) :
    ∃ T, (compileFinTM (prog M) (start M) (bankTM Ms) (bankStart Ms)).ComputesInTime x w T ∧
      (compileFinTM (prog M) (start M) (bankTM Ms) (bankStart Ms)).tm.spaceUsed
          ((compileFinTM (prog M) (start M) (bankTM Ms) (bankStart Ms)).tm.initCfg x) T ≤
        M.k * (2 * M.tm.spaceUsed (M.tm.initCfg v) t + 1) +
          ((Nat.bits (v.length + 1)).length + 2) + (bankK Ms + bankK Ms) * (2 * B + 1) := by
  sorry

end LogProg.OIS

/-- **Logspace preimages along implicitly logspace computable maps are logspace**
(phase P4.4b; spec, fill pending): if `f` is implicitly logspace computable and `C ∈ L`, then
`{x | f x ∈ C} ∈ L`. [AB09, Lemma 4.17(2), in preimage form; its proof's Fig. 4.3] It is stated,
and will be proved, as a corollary of `Complexity.LogProg.OIS.compile_decides`.

**Proof sketch.** Unpack `f`'s bound `C₀ (|x| + 1)^e` and its two deciders (spaces `c₀`,
`c₁` times `logSpace`), and `C`'s decider `M` (space `c · logSpace`). For each `x`, take the
time `t` of `M` on `v := f x`, and apply `OIS.compile_decides` with:

* the bank `![length decider, bit decider]`;
* the laws `pairEncode_mem_indexLang`;
* `B := (c₀ + c₁) · logSpace (2|x| + 2 + |bits (|f x| + 1)|) + 1`.

The indicator `[f x ∈ C]` is `[x ∈ {x | f x ∈ C}]`. The bound is `O(logSpace |x|)`:
`logSpace |f x|` and `|bits (|f x| + 1)|` are at most `K · logSpace |x|` by
`LogProg.log_poly_bound`, since `|f x| ≤ C₀ (|x| + 1)^e`. The arithmetic follows
`ImplicitlyLogspaceComputable.computesInSpace`. -/
theorem mem_LOGSPACE_preimage {f : List Bool → List Bool} (hf : ImplicitlyLogspaceComputable f)
    {C : Language Bool} (hC : C ∈ LOGSPACE) : ({x | f x ∈ C} : Language Bool) ∈ LOGSPACE := by
  sorry

end Complexity
