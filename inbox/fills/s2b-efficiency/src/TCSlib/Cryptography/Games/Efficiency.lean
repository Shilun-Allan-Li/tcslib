/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.BitCodec
import TCSlib.Cryptography.Games.Probability
import TCSlib.Cryptography.Games.Bridges.Machines
import TCSlib.Cryptography.Games.Efficiency.Strings
import TCSlib.Cryptography.Games.Efficiency.Handler

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The efficiency of reductions (skeleton for the efficiency fill)

A reduction runs a machine adversary `A` and answers `A`'s queries with a polynomial-time
**handler**. Proved once, the targets below say that the result is again a machine, so the
hardness assumptions, which quantify over machines (`Complexity.NUPPT`), apply to it. The route is
`briefs/pass-shelat-ch5-8/design/S2b-efficiency.md`. The template is Frederick Dehmel's GGM
reduction machine (`Asymptotic/GGMReduction*.lean`), whose loop `GGMRed.stateLoopFun` is reused.

**Status: skeleton.** The definitions (T0) are final. The statements of T1, T2 and T4 and of the
companion `exists_toCompOn_of_toComp` are frozen at the issue of the fill brief
(`briefs/pass-shelat-ch5-8/fills/efficiency/`). Their proofs are the fill's.

## The shape of a reduction

A handler describes everything a reduction does around one run of the adversary. At parameter
`n` the reduction has an input `z` and a seed `ω` (its own coins). Every function of the handler
reads them from the **context** `⟨1^n, ⟨z, ω⟩⟩` (`seedIn`):
1. **the adversary's input** is a polynomial-time function of the context (`advIn`), for example
   a public key built from `z` and `ω`; the adversary runs as `A.toCompOn` on it;
2. **each query** of the adversary is answered from the handler's state, by the handler alone
   (`PolyHandler`) or with queries to the reduction's own oracles (`InteractiveHandler`);
3. **the reduction's output** is computed from the context, the final state and the adversary's
   output: by a polynomial-time function (`PolyHandler.out`), or by a last phase that may itself
   query the reduction's oracles, within its own budget (`InteractiveHandler.finish`).

## Fixed lengths

Every length is an explicit polynomial in the parameter `n`: queries and answers (`din i`,
`dout i`), the adversary's output (`dα`), the handler's state and seed, and, for an interactive
handler, the reduction's output. This bounds every history, which the guarded state loop needs.

## Scope

* **Covered:** a reduction that runs one adversary once, on an input computed from its own,
  answers the adversary's queries with or without its own oracles, and post-processes the final
  state and the adversary's output (with further oracle queries if it is interactive). T1 makes
  the machine's output exactly the finalized output; T2 makes the machine's computation exactly
  the simulation followed by the finalization, with the budgets added.
* **Adversaries without input** are adversaries with an input they ignore
  (`exists_toCompOn_of_toComp`).
* **Reductions to a pseudorandom function** reach `OracleEnsemble.Indist` through T4: an oracle
  machine against one bit-string oracle with a one-bit output is, on evaluations, a next-query
  machine of the ch. 2–4 layer (`NUPPT.toOracleAdversary`).
* **Non-uniform handlers** (for example one that runs a non-uniform distinguisher) receive their
  advice through the input `z`; it is hard-wired into the machine afterwards
  (`NUPPT.exists_withAdvice`, with `NUPPT.exists_comp` to re-pair the input).
* **Not covered:** reductions that rewind the adversary or run it more than once, and variable
  lengths.

## Main definitions

* `Games.seedIn n z ω`: the context `⟨1^n, ⟨z, ω⟩⟩`.
* `Games.PolyHandler k din dout`: a polynomial-time handler for `k` bit-string oracles, with its
  state and seed lengths, initial state, adversary input and finalization.
* `Games.PolyHandler.answer`, `Games.PolyHandler.impl`: its answers, and its semantics as a
  stateful `QueryImpl` that asks no oracle, at parameter `n`, reduction input `z` and seed `ω`;
  `PolyHandler.advInput` and `PolyHandler.result`: the adversary's input and the reduction's
  output.
* `Games.InteractiveHandler`, `InteractiveHandler.call`, `InteractiveHandler.impl`: a
  polynomial-time handler that may itself query outer bit-string oracles, up to `perCall(n)`
  times per inner query, and its semantics as a `QueryImpl` of the inner oracles by the outer ones;
  `InteractiveHandler.advInput` and `InteractiveHandler.finish`: the adversary's input and the
  finalization, with up to `finCall(n)` outer queries.

## Main results

* `Games.exists_handlerMachine` (T1, the fill's target): a reduction with a polynomial-time
  handler is a machine, whose output is exactly the finalized output of the simulation.
* `Games.exists_interactiveHandlerMachine` (T2, the fill's target): a reduction with an
  interactive handler is an oracle machine against the outer oracles, with budget
  `q(n) · perCall(n) + finCall(n)`, whose computation is exactly the simulation followed by the
  finalization. The reductions that forward or answer queries with their own oracle need it (the
  PRF MAC's distinguisher, hash-and-sign's forger, the CPA and CCA reductions).
* `Games.exists_toCompOn_of_toComp` (the fill's target): a machine without input is a machine
  with an input that it ignores, with the same coins.
* `Games.exists_toOracleAdversary_of_bitCodec` (T4, the fill's target): an oracle machine
  against one `bitCodec` oracle with a one-bit output, on the empty input, evaluates as a
  next-query machine of the ch. 2–4 layer.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010:
  every reduction of ch. 5–8 (for example the proofs of Thms 135.4 and 168.2).
-/

namespace TCSlib.Cryptography.Games

open Complexity Turing

variable {k : ℕ}

/-- The bit-string oracles at parameter `n`, with polynomial lengths. -/
abbrev bitSpecAt (din dout : Fin k → PolyExpr) (n : ℕ) : OracleSpec (Fin k) :=
  bitSpec (fun i => (din i).eval n) (fun i => (dout i).eval n)

/-- The bit-string oracles at parameter `n` are `bitSpec` of the evaluated lengths:
`bitSpecAt din dout n = bitSpec (fun i => (din i).eval n) (fun i => (dout i).eval n)`. -/
theorem bitSpecAt_eq (din dout : Fin k → PolyExpr) (n : ℕ) :
    bitSpecAt din dout n = bitSpec (fun i => (din i).eval n) (fun i => (dout i).eval n) :=
  rfl

/-- The **context** of a reduction at parameter `n`, with the reduction's input `z` and its seed
`ω`: the string `⟨1^n, ⟨z, ω⟩⟩`. Every function of a handler reads it. -/
def seedIn (n : ℕ) (z ω : List Bool) : List Bool :=
  pairEncode (List.replicate n true) (pairEncode z ω)

/-- The context is `⟨1^n, ⟨z, ω⟩⟩`:
`seedIn n z ω = pairEncode (List.replicate n true) (pairEncode z ω)`. -/
theorem seedIn_eq (n : ℕ) (z ω : List Bool) :
    seedIn n z ω = pairEncode (List.replicate n true) (pairEncode z ω) :=
  rfl

/-- A **polynomial-time handler** for `k` bit-string oracles with query lengths `din` and answer
lengths `dout`: a reduction that runs the adversary once and answers its queries by itself. Its
three functions are polynomial-time, and each reads the context `⟨1^n, ⟨z, ω⟩⟩` (`seedIn`: the
parameter, the reduction's input `z` and its seed `ω`):
- `advIn` maps the context to the adversary's input;
- `run` answers one query: on `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨1^i, x⟩⟩⟩` (the context, the state `s`, and
  the query `x` to oracle `i`), it returns `⟨y, s'⟩`, the answer and the new state;
- `out` maps `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, a⟩⟩` (the context, the final state and the adversary's output)
  to the reduction's output. -/
structure PolyHandler (k : ℕ) (din dout : Fin k → PolyExpr) where
  /-- The length of the state. -/
  stateLen : PolyExpr
  /-- The length of the seed (the handler's own coins). -/
  seedLen : PolyExpr
  /-- The initial state at each parameter. -/
  init : ∀ n, Fin (stateLen.eval n) → Bool
  /-- The handler as a string function. -/
  run : List Bool → List Bool
  /-- It is polynomial-time computable. -/
  poly : PolyTimeComputable run
  /-- The adversary's input, as a function of the context `⟨1^n, ⟨z, ω⟩⟩` (for example a public
  key built from `z` and the seed). For an adversary without input it is ignored. -/
  advIn : List Bool → List Bool
  /-- The adversary's input is polynomial-time computable. -/
  advIn_poly : PolyTimeComputable advIn
  /-- The finalization: the reduction's output, as a function of `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, a⟩⟩` (the
  context, the final state `s` and the adversary's output `a`). -/
  out : List Bool → List Bool
  /-- The finalization is polynomial-time computable. -/
  out_poly : PolyTimeComputable out

namespace PolyHandler

variable {din dout : Fin k → PolyExpr}

/-- The handler's input string for the query `x` to oracle `i` in state `s`. -/
def input (n : ℕ) (z : List Bool) (ω : List Bool) (s : List Bool) (i : Fin k) (x : List Bool) :
    List Bool :=
  pairEncode (pairEncode (List.replicate n true) (pairEncode z ω))
    (pairEncode s (pairEncode (List.replicate i true) x))

/-- The handler's input string is `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨1^i, x⟩⟩⟩`. -/
theorem input_eq (n : ℕ) (z ω s : List Bool) (i : Fin k) (x : List Bool) :
    input n z ω s i x =
      pairEncode (pairEncode (List.replicate n true) (pairEncode z ω))
        (pairEncode s (pairEncode (List.replicate i true) x)) :=
  rfl

/-- The adversary's input at parameter `n`, for the reduction input `z` and the seed `ω`: `advIn`
of the context `⟨1^n, ⟨z, ω⟩⟩`. -/
def advInput (H : PolyHandler k din dout) (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) : List Bool :=
  H.advIn (seedIn n z (List.ofFn ω))

/-- The adversary's input is `advIn` of the context:
`H.advInput n z ω = H.advIn (seedIn n z (List.ofFn ω))`. -/
theorem advInput_eq (H : PolyHandler k din dout) (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) :
    H.advInput n z ω = H.advIn (seedIn n z (List.ofFn ω)) :=
  rfl

/-- The reduction's output at parameter `n`, for the reduction input `z` and the seed `ω`, when
the final state is `s` and the adversary's output is `a`: `out` of
`⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, a⟩⟩`. -/
def result (H : PolyHandler k din dout) (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool) {d : ℕ}
    (a : Fin d → Bool) : List Bool :=
  H.out (pairEncode (seedIn n z (List.ofFn ω)) (pairEncode (List.ofFn s) (List.ofFn a)))

/-- The reduction's output is `out` of the context, the final state and the adversary's output:
`H.result n z ω s a = H.out (pairEncode (seedIn n z (List.ofFn ω))
(pairEncode (List.ofFn s) (List.ofFn a)))`. -/
theorem result_eq (H : PolyHandler k din dout) (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool) {d : ℕ}
    (a : Fin d → Bool) :
    H.result n z ω s a =
      H.out (pairEncode (seedIn n z (List.ofFn ω)) (pairEncode (List.ofFn s) (List.ofFn a))) :=
  rfl

/-- The handler's answer and new state, decoded with fixed lengths. If `run`'s output is not a
pair, both are all-`false`; otherwise each component of the wrong length is replaced by
all-`false` independently (a total default; well-behaved handlers never produce one). An
interactive handler defaults jointly instead (`InteractiveHandler`). -/
def answer (H : PolyHandler k din dout) (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool) (i : Fin k)
    (x : Fin ((din i).eval n) → Bool) :
    (Fin ((dout i).eval n) → Bool) × (Fin (H.stateLen.eval n) → Bool) :=
  match pairDecode (H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x))) with
  | some (yw, sw) =>
    ((decodeFin _ yw).getD (zeroBits _), (decodeFin _ sw).getD (zeroBits _))
  | none => (zeroBits _, zeroBits _)

section Answer

variable (H : PolyHandler k din dout) {n : ℕ} {z : List Bool} {ω : Fin (H.seedLen.eval n) → Bool}
  {s : Fin (H.stateLen.eval n) → Bool} {i : Fin k} {x : Fin ((din i).eval n) → Bool}

/-- If `run`'s output is not a pair, the answer and the new state are all-`false`. -/
theorem answer_of_pairDecode_eq_none
    (h : pairDecode (H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x))) = none) :
    H.answer n z ω s i x = (zeroBits _, zeroBits _) := by
  unfold answer
  rw [h]

/-- If `run`'s output is the pair `⟨yw, sw⟩`, the answer is `yw` and the new state `sw`, each
decoded with its fixed length and all-`false` if that length is wrong:
`H.answer n z ω s i x = ((decodeFin _ yw).getD (zeroBits _), (decodeFin _ sw).getD (zeroBits _))`.
-/
theorem answer_of_pairDecode_eq_some {yw sw : List Bool}
    (h : pairDecode (H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x))) =
      some (yw, sw)) :
    H.answer n z ω s i x =
      ((decodeFin _ yw).getD (zeroBits _), (decodeFin _ sw).getD (zeroBits _)) := by
  unfold answer
  rw [h]

/-- **A well-formed output:** if `run` returns `⟨y, s'⟩` with `y` and `s'` of the fixed lengths,
the answer is `y` and the new state `s'`. -/
theorem answer_of_run_eq {y : Fin ((dout i).eval n) → Bool} {s' : Fin (H.stateLen.eval n) → Bool}
    (h : H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x)) =
      pairEncode (List.ofFn y) (List.ofFn s')) :
    H.answer n z ω s i x = (y, s') := by
  have h' : pairDecode (H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x))) =
      some (List.ofFn y, List.ofFn s') := by
    rw [h, pairDecode_pairEncode]
  rw [answer_of_pairDecode_eq_some H h', decodeFin_ofFn, decodeFin_ofFn, Option.getD_some,
    Option.getD_some]

end Answer

/-- The handler as an implementation of the bit-string oracles at parameter `n`, for the
reduction input `z` and seed `ω`: it keeps its state and asks no oracle (the non-interactive
case). -/
def impl (H : PolyHandler k din dout) (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) :
    QueryImpl (bitSpecAt din dout n) (Fin (H.stateLen.eval n) → Bool) unifSpec :=
  fun i x s => .pure (H.answer n z ω s i x)

/-- The handler answers the query `x` to oracle `i` in state `s` with no coins and no queries:
`H.impl n z ω i x s = pure (H.answer n z ω s i x)`. -/
theorem impl_apply (H : PolyHandler k din dout) (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) (i : Fin k) (x : Fin ((din i).eval n) → Bool)
    (s : Fin (H.stateLen.eval n) → Bool) :
    H.impl n z ω i x s = .pure (H.answer n z ω s i x) :=
  rfl

end PolyHandler

/-- **T1 (the efficiency fill's target; non-interactive handlers).** For a machine adversary `A`
with query budget `q` and `dα`-bit outputs against `k` bit-string oracles, and a polynomial-time
handler `H`, there is a machine `B` and, at every parameter, a bijection `φ` from (the handler's
seed, `A`'s coins) to `B`'s coins, with the following property. Run `A` on the input
`H.advInput n z ω`, answer its queries by `H` (input `z`, seed `ω`) from `H`'s initial state, and
let `a` be `A`'s output and `s` the final state. Then `B`'s output on input `z` with coins
`φ (ω, r)` is exactly the reduction's output `H.result n z ω s a`.

**Proof sketch** (the fill's; route note §"T1").
1. `B`'s raw function is the activation loop `EffFill.hRaw` (`GGMRed.stateLoopFun` through
   `EffFill.actLoop`) on the layout `⟨⟨⟨1^n, ⟨z, ω⟩⟩, ⟨α_A, s₀⟩⟩, r⟩`. The initial state
   `s₀ = H.init n` is part of the advice, beside `A`'s advice `α_A`, since `init` is an arbitrary
   function of `n`; so `B` is non-uniform even when `A` is uniform. The loop state is
   `⟨L, ⟨s, 1^t⟩⟩` (`A`'s encoded log, `H`'s state, the answered queries); the context
   `seedIn n z ω` and `A`'s input are recomputed in every round.
2. A round runs `A` on `⟨A's input, L⟩` (`NUPPT.polyTimeComputable_output`) and reads its move
   through the canonical decoder `EffFill.canonWord`, which returns the canonical word of
   `decodeBitMove`'s move on every word (`EffFill.canonWord_eq`, canonicity tested by re-encoding).
   It stops with `H.out ⟨ctx, ⟨s, a⟩⟩` on an output `a`, and with `H.out ⟨ctx, ⟨s, 0^{dα(n)}⟩⟩` on a
   query when `t = q(n)`. Otherwise it feeds the query to `H.run`, decodes the answer and the new
   state componentwise (`EffFill.fixLen`, `EffFill.ofFn_getD_decodeFin` and the `answer` lemmas),
   and appends the entry to `L` (`EffFill.encodeLog_append_single`).
3. At most `q(n) + 1` rounds, with states of polynomial length (all lengths are fixed), so the raw
   function is polynomial-time (`EffFill.hRaw_poly`, from `GGMRed.stateLoopFun_poly`).
4. The functional equation (`EffFill.hRaw_spec`): by induction on the remaining budget, the loop's
   state after `t` rounds encodes the simulation after `t` queries (`toCompOn_eq`, `buildComp`'s
   case lemmas, `simulate_query`, `PolyHandler.impl_apply`); `GGMRed.stateLoopFun_eval` reads off
   the output (`EffFill.runsTo_stop`), and `result_eq` and `seedIn_eq` identify it.
5. `B` is `NUPPT.ofPolyTime` of the raw function followed by `NUPPT.exists_split` with
   `p = H.seedLen` (`EffFill.exists_splitMachine`); `φ` appends the seed and the coins. -/
theorem exists_handlerMachine (A : NUPPT) (q : PolyExpr) (din dout : Fin k → PolyExpr)
    (dα : PolyExpr) (H : PolyHandler k din dout) :
    ∃ B : NUPPT, ∀ n : ℕ, ∃ φ : (Fin (H.seedLen.eval n) → Bool) × A.Coins n ≃ B.Coins n,
      ∀ (z : List Bool) (ω : Fin (H.seedLen.eval n) → Bool) (r : A.Coins n),
        ∃ (a : Fin (dα.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool),
          simulate (H.impl n z ω)
              (A.toCompOn
                (bitCodec (fun i => (din i).eval n) (fun i => (dout i).eval n) (dα.eval n))
                n (q.eval n) (H.advInput n z ω) r) (H.init n) = .pure (a, s) ∧
            B.runAt n z (φ (ω, r)) = H.result n z ω s a := by
  -- The machine: the handler loop of `EffFill.hRaw`, with `⟨A.advice n, s₀⟩` as advice and the
  -- seed passed as data.
  obtain ⟨B, hB⟩ := EffFill.exists_splitMachine A
    (EffFill.hRaw_poly A q dα din dout H.stateLen H.poly H.advIn_poly H.out_poly)
    (.add (.add (.mul (.const 2) A.adv) (.const 2)) H.stateLen)
    (fun n => pairEncode (A.advice n) (List.ofFn (H.init n))) (fun n => by
      rw [length_pairEncode, List.length_ofFn]
      simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
      have := A.advice_length n
      omega) H.seedLen
  refine ⟨B, fun n => ?_⟩
  obtain ⟨φ, hφ⟩ := hB n
  refine ⟨φ, fun z ω r => ?_⟩
  -- The handler's answers are `run`'s output decoded componentwise.
  have hans : ∀ (i : Fin k) (x : Fin ((din i).eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool),
      List.ofFn (H.answer n z ω s i x).1 = EffFill.fixLen ((dout i).eval n) (pairFstD (H.run
        (pairEncode (pairEncode (List.replicate n true) (pairEncode z (List.ofFn ω)))
          (pairEncode (List.ofFn s) (pairEncode (List.replicate i true) (List.ofFn x)))))) ∧
      List.ofFn (H.answer n z ω s i x).2 = EffFill.fixLen (H.stateLen.eval n) (pairSndD (H.run
        (pairEncode (pairEncode (List.replicate n true) (pairEncode z (List.ofFn ω)))
          (pairEncode (List.ofFn s) (pairEncode (List.replicate i true) (List.ofFn x)))))) := by
    intro i x s
    rw [← PolyHandler.input_eq]
    cases h : pairDecode (H.run (PolyHandler.input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x)))
      with
    | none =>
      rw [PolyHandler.answer_of_pairDecode_eq_none H h, pairFstD_of_pairDecode_eq_none h,
        pairSndD_of_pairDecode_eq_none h, EffFill.fixLen_nil, EffFill.fixLen_nil, ofFn_zeroBits,
        ofFn_zeroBits]
      exact ⟨rfl, rfl⟩
    | some p =>
      obtain ⟨yw, sw⟩ := p
      rw [PolyHandler.answer_of_pairDecode_eq_some H h, eq_pairEncode_of_pairDecode _ _ _ h,
        pairFstD_pairEncode, pairSndD_pairEncode, EffFill.ofFn_getD_decodeFin,
        EffFill.ofFn_getD_decodeFin]
      exact ⟨rfl, rfl⟩
  obtain ⟨a, s, hsim, hraw⟩ := EffFill.hRaw_spec A q dα din dout H.stateLen H.run H.advIn H.out
    (spec' := unifSpec) n z (List.ofFn ω) r (H.init n) (fun i x s => H.answer n z ω s i x) hans
  refine ⟨a, s, ?_, ?_⟩
  · have himpl : H.impl n z ω = fun i x s => OracleComp.pure (H.answer n z ω s i x) := by
      funext i x s
      exact H.impl_apply n z ω i x s
    rw [himpl, PolyHandler.advInput_eq, seedIn_eq]
    exact hsim
  · rw [hφ, hraw, PolyHandler.result_eq, seedIn_eq]

/-! ### Interactive handlers (T2) -/

variable {k' : ℕ}

/-- A **polynomial-time interactive handler** for `k` inner bit-string oracles that may itself
query `k'` outer bit-string oracles. Like `PolyHandler`, it computes the adversary's input from
the context `⟨1^n, ⟨z, ω⟩⟩` (`advIn`); it answers the adversary's queries (`run`), and computes the
reduction's output in a last phase (`finRun`), both with outer queries.

One inner query `x` to oracle `i` is answered with at most `perCall(n)` outer queries, in at most
`perCall(n) + 1` rounds of `run` (the last returns the answer; a further query after the budget
is spent is cut off with the default). In each round, `run` sees `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩`, where `L` is
the outer log of the call so far (encoded as `bitCodec` encodes logs), and returns a move in
`bitCodec`'s format: a query `⟨[false], ⟨1^j, x'⟩⟩` to outer oracle `j`, or the answer
`⟨[true], y ‖ s'⟩` (the inner answer, then the new state). A malformed round output, including a
payload `y ‖ s'` of the wrong total length, gives the all-`false` answer and state together (a
joint default, unlike `PolyHandler.answer`, which defaults each component separately).

The finalization works the same way on `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨a, L⟩⟩⟩` (the final state, the
adversary's output and the outer log of the finalization so far), with at most `finCall(n)` outer
queries; it returns the reduction's `outLen(n)`-bit output as `⟨[true], b⟩`, the all-`false`
output on a malformed round output or on a further query after the budget is spent. (A return at
zero remaining budget is accepted: only a query then hits the timeout.) -/
structure InteractiveHandler (k : ℕ) (din dout : Fin k → PolyExpr) (k' : ℕ)
    (din' dout' : Fin k' → PolyExpr) where
  /-- The length of the state. -/
  stateLen : PolyExpr
  /-- The length of the seed. -/
  seedLen : PolyExpr
  /-- The bound on outer queries per inner query. -/
  perCall : PolyExpr
  /-- The initial state at each parameter. -/
  init : ∀ n, Fin (stateLen.eval n) → Bool
  /-- One round of the handler, as a string function. -/
  run : List Bool → List Bool
  /-- It is polynomial-time computable. -/
  poly : PolyTimeComputable run
  /-- The adversary's input, as a function of the context `⟨1^n, ⟨z, ω⟩⟩`. For an adversary
  without input it is ignored. -/
  advIn : List Bool → List Bool
  /-- The adversary's input is polynomial-time computable. -/
  advIn_poly : PolyTimeComputable advIn
  /-- The length of the reduction's output. -/
  outLen : PolyExpr
  /-- The bound on the outer queries of the finalization. -/
  finCall : PolyExpr
  /-- One round of the finalization, as a string function: on `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨a, L⟩⟩⟩` it
  returns an outer query `⟨[false], ⟨1^j, x'⟩⟩` or the reduction's output `⟨[true], b⟩`. -/
  finRun : List Bool → List Bool
  /-- The finalization's round is polynomial-time computable. -/
  finRun_poly : PolyTimeComputable finRun

namespace InteractiveHandler

variable {din dout : Fin k → PolyExpr} {din' dout' : Fin k' → PolyExpr}

/-- The handler's input string for one round. -/
def input (n : ℕ) (z ω s : List Bool) (i : Fin k) (x L : List Bool) : List Bool :=
  pairEncode (pairEncode (List.replicate n true) (pairEncode z ω))
    (pairEncode s (pairEncode (pairEncode (List.replicate i true) x) L))

/-- The handler's input string for one round is `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩`. -/
theorem input_eq (n : ℕ) (z ω s : List Bool) (i : Fin k) (x L : List Bool) :
    input n z ω s i x L =
      pairEncode (pairEncode (List.replicate n true) (pairEncode z ω))
        (pairEncode s (pairEncode (pairEncode (List.replicate i true) x) L)) :=
  rfl

/-- The adversary's input at parameter `n`, for the reduction input `z` and the seed `ω`: `advIn`
of the context `⟨1^n, ⟨z, ω⟩⟩`. -/
def advInput (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) : List Bool :=
  H.advIn (seedIn n z (List.ofFn ω))

/-- The adversary's input is `advIn` of the context:
`H.advInput n z ω = H.advIn (seedIn n z (List.ofFn ω))`. -/
theorem advInput_eq (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) :
    H.advInput n z ω = H.advIn (seedIn n z (List.ofFn ω)) :=
  rfl

/-- **One call** of the handler on the inner query `x` to oracle `i` in state `s`: at most
`perCall(n)` outer queries, in at most `perCall(n) + 1` rounds of `run`. A malformed round output
is the all-`false` answer and state (`decodeBitMove`'s default), and so is a further query after
the budget is spent (a return at zero remaining budget is accepted). -/
def call (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool) (i : Fin k)
    (x : Fin ((din i).eval n) → Bool) :
    OracleComp (bitSpecAt din' dout' n) (Fin ((dout i).eval n + H.stateLen.eval n) → Bool) :=
  buildComp (fun L => decodeBitMove (fun j => (din' j).eval n) (fun j => (dout' j).eval n) _
      (H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x)
        ((bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) 0).encodeLog L))))
    (zeroBits _) (H.perCall.eval n) []

/-- One call is `buildComp` of the handler's rounds, from the empty outer log, with budget
`perCall(n)` and the all-`false` result on a query after it is spent: `H.call n z ω s i x =
buildComp (fun L => decodeBitMove _ _ _ (H.run (input … L))) (zeroBits _) (H.perCall.eval n) []`.
-/
theorem call_eq (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool) (i : Fin k)
    (x : Fin ((din i).eval n) → Bool) :
    H.call n z ω s i x =
      buildComp (fun L => decodeBitMove (fun j => (din' j).eval n) (fun j => (dout' j).eval n)
          ((dout i).eval n + H.stateLen.eval n)
          (H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x)
            ((bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) 0).encodeLog L))))
        (zeroBits _) (H.perCall.eval n) [] :=
  rfl

/-- The interactive handler as an implementation of the inner oracles by the outer ones, at
parameter `n`, reduction input `z` and seed `ω`: one `call` per inner query, its result split
into the answer and the new state. -/
def impl (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) :
    QueryImpl (bitSpecAt din dout n) (Fin (H.stateLen.eval n) → Bool) (bitSpecAt din' dout' n) :=
  fun i x s => (H.call n z ω s i x).bind fun w =>
    .pure (fun j => w (Fin.castAdd _ j), fun j => w (Fin.natAdd _ j))

/-- The inner query `x` to oracle `i` in state `s` is answered by one `call`, whose result is
split into the answer (its first `dout i` bits) and the new state (the rest):
`H.impl n z ω i x s = (H.call n z ω s i x).bind fun w =>
pure (fun j => w (Fin.castAdd _ j), fun j => w (Fin.natAdd _ j))`. -/
theorem impl_apply (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) (i : Fin k) (x : Fin ((din i).eval n) → Bool)
    (s : Fin (H.stateLen.eval n) → Bool) :
    H.impl n z ω i x s =
      (H.call n z ω s i x).bind fun w =>
        .pure (fun j => w (Fin.castAdd _ j), fun j => w (Fin.natAdd _ j)) :=
  rfl

/-- The input string of one round of the finalization: `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨a, L⟩⟩⟩`, with the
final state `s`, the adversary's output `a` and the outer log `L` of the finalization so far. -/
def finInput (n : ℕ) (z ω s a L : List Bool) : List Bool :=
  pairEncode (seedIn n z ω) (pairEncode s (pairEncode a L))

/-- The input string of one round of the finalization is `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨a, L⟩⟩⟩`:
`finInput n z ω s a L = pairEncode (seedIn n z ω) (pairEncode s (pairEncode a L))`. -/
theorem finInput_eq (n : ℕ) (z ω s a L : List Bool) :
    finInput n z ω s a L = pairEncode (seedIn n z ω) (pairEncode s (pairEncode a L)) :=
  rfl

/-- **The finalization** in the final state `s`, after the adversary's output `a`: the
reduction's `outLen(n)`-bit output, computed with at most `finCall(n)` outer queries, in at most
`finCall(n) + 1` rounds of `finRun`. A malformed round output is the all-`false` output
(`decodeBitMove`'s default), and so is a further query after the budget is spent (a return at
zero remaining budget is accepted). -/
def finish (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool) {d : ℕ}
    (a : Fin d → Bool) : OracleComp (bitSpecAt din' dout' n) (Fin (H.outLen.eval n) → Bool) :=
  buildComp (fun L => decodeBitMove (fun j => (din' j).eval n) (fun j => (dout' j).eval n)
      (H.outLen.eval n)
      (H.finRun (finInput n z (List.ofFn ω) (List.ofFn s) (List.ofFn a)
        ((bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) 0).encodeLog L))))
    (zeroBits _) (H.finCall.eval n) []

/-- The finalization is `buildComp` of its rounds, from the empty outer log, with budget
`finCall(n)` and the all-`false` output on a query after it is spent: `H.finish n z ω s a =
buildComp (fun L => decodeBitMove _ _ _ (H.finRun (finInput … L))) (zeroBits _)
(H.finCall.eval n) []`. -/
theorem finish_eq (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool) {d : ℕ}
    (a : Fin d → Bool) :
    H.finish n z ω s a =
      buildComp (fun L => decodeBitMove (fun j => (din' j).eval n) (fun j => (dout' j).eval n)
          (H.outLen.eval n)
          (H.finRun (finInput n z (List.ofFn ω) (List.ofFn s) (List.ofFn a)
            ((bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) 0).encodeLog L))))
        (zeroBits _) (H.finCall.eval n) [] :=
  rfl

end InteractiveHandler

/-- **T2 (the efficiency fill's target; interactive handlers).** For a machine adversary `A`
with query budget `q` and `dα`-bit outputs against `k` bit-string oracles, and an interactive
handler `H` answering them through `k'` outer oracles, there is an oracle machine `B` against the
outer oracles, with budget `q(n) · perCall(n) + finCall(n)`, and at every parameter a bijection
`φ` from (`H`'s seed, `A`'s coins) to `B`'s coins, with the following property. `B` on input `z`
with coins `φ (ω, r)` is, as an oracle computation, exactly the reduction: `A` run on the input
`H.advInput n z ω`, its queries answered by `H` (input `z`, seed `ω`) from `H`'s initial state,
followed by `H`'s finalization on the final state and `A`'s output.

**Proof sketch** (the fill's; route note §"The route", with the log replay).
1. `B`'s next-move function, on `⟨z, outer log⟩` with coins `(ω, r)`, first computes `A`'s input
   `H.advIn (seedIn n z ω)` (`H.advIn_poly`). It then replays: it splits the outer log into the
   calls of `H` and the finalization. Within each call it reruns `H.run` round by round, and
   between calls it reruns `A`'s next-move function on `⟨A's input, inner log⟩`, the inner log
   rebuilt from the calls' answers. Once `A` returns `a` (or meets its own budget), it reruns
   `H.finRun` on `⟨seedIn n z ω, ⟨s, ⟨a, L⟩⟩⟩` with the rest `L` of the log. It stops at the first
   pending outer query (and asks it) or at the finalization's output (and returns its canonical
   word, `encodeBitMove`). Every length is fixed, so each replay is polynomial
   (`stateLoopFun_poly`, as in T1).
2. `B`'s budget suffices: each of `A`'s at most `q(n)` queries costs at most `perCall(n)` outer
   queries and the finalization at most `finCall(n)` (`buildComp_costBoundedBy`,
   `simulate_costBoundedBy`, `CostBoundedBy.bind`), so `B` never meets its own timeout before
   the reduction ends, and it mirrors every default of `A`, of a call and of the finalization.
3. The functional equation: by induction on the outer log, the two computation trees agree node
   by node (`simulate_query`, `impl_apply`, `call_eq`, `finish_eq`, `toCompOn_eq`, `buildComp`'s
   case lemmas, `decodeBitMove_encodeBitMove`). Coins split as `(ω, r)` by `exists_split`. -/
theorem exists_interactiveHandlerMachine (A : NUPPT) (q : PolyExpr)
    (din dout : Fin k → PolyExpr) (din' dout' : Fin k' → PolyExpr) (dα : PolyExpr)
    (H : InteractiveHandler k din dout k' din' dout') :
    ∃ B : NUPPT, ∀ n : ℕ, ∃ φ : (Fin (H.seedLen.eval n) → Bool) × A.Coins n ≃ B.Coins n,
      ∀ (z : List Bool) (ω : Fin (H.seedLen.eval n) → Bool) (r : A.Coins n),
        (simulate (H.impl n z ω)
            (A.toCompOn (bitCodec (fun i => (din i).eval n) (fun i => (dout i).eval n) (dα.eval n))
              n (q.eval n) (H.advInput n z ω) r) (H.init n)).bind
            (fun res => H.finish n z ω res.2 res.1) =
          B.toCompOn
            (bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) (H.outLen.eval n))
            n (q.eval n * H.perCall.eval n + H.finCall.eval n) z (φ (ω, r)) := by
  sorry

/-! ### Companions: adversaries without input, and the bridge to pseudorandom functions (T4) -/

/-- **A machine without input is a machine with an input that it ignores.** For every machine
`A` there is a machine `A'` with the same coins whose computation on any input `x` is `A`'s
computation, for every codec and budget, the coins related by a bijection `φ`. So T1 and T2,
stated for adversaries with input, cover adversaries without one.

**Proof sketch.** `A'` is `NUPPT.exists_comp` of `A` with `pre = pairSndD` and `post = id`, so
`A'.coins = A.coins` and `A'.runAtL n ⟨x, L⟩ r = A.runAtL n L r` (`pairSndD_pairEncode`). The
bijection `φ` is `NUPPT.coinsCongr`, which transports the coins along the equal coin polynomials
and keeps the coin string (`NUPPT.runAt_coinsCongr`); with `runAt_eq` the next-move functions of
`A'.toCompOn codec n q x (φ r)` and `A.toComp codec n q r` agree on every log, and
`toCompOn_eq`, `toComp_eq` conclude. -/
theorem exists_toCompOn_of_toComp (A : NUPPT) :
    ∃ A' : NUPPT, A'.coins = A.coins ∧ ∀ n : ℕ, ∃ φ : A.Coins n ≃ A'.Coins n,
      ∀ {ι α : Type} {spec : OracleSpec ι} (codec : MachineCodec spec α) (q : ℕ)
        (x : List Bool) (r : A.Coins n),
        A'.toCompOn codec n q x (φ r) = A.toComp codec n q r := by
  obtain ⟨A', hc, -, -, hA'⟩ :=
    NUPPT.exists_comp A polyTimeComputable_pairSndD polyTimeComputable_id
  refine ⟨A', hc, fun n => ⟨NUPPT.coinsCongr hc.symm n, ?_⟩⟩
  intro ι α spec codec q x r
  have hnext : (fun hist => codec.decodeMove
      (A'.runAt n (pairEncode x (codec.encodeLog hist)) (NUPPT.coinsCongr hc.symm n r))) =
      fun hist => codec.decodeMove (A.runAt n (codec.encodeLog hist) r) := by
    funext hist
    rw [NUPPT.runAt_coinsCongr, hA', pairSndD_pairEncode, id_eq, ← NUPPT.runAt_eq]
  rw [NUPPT.toCompOn_eq, NUPPT.toComp_eq, hnext]

/-- **T4 (the efficiency fill's target; the bridge to pseudorandom functions).** An oracle
machine `B` against one `bitCodec` oracle (`ℓ₁(n)`-bit queries, `ℓ₂(n)`-bit answers) with a
one-bit output, run on the empty input, is a next-query machine of the ch. 2–4 layer: there is a
machine `B'` with the same coins whose oracle adversary `B'.toOracleAdversary`, run against any
`f`, returns the bit of `B`'s computation evaluated with `f`, the coins related by a bijection
`φ`. So `OracleEnsemble.Indist`, and with it `PRF`, applies to the machines of T2 with one outer
oracle and a one-bit output (through `oracleDist_apply` and `Bridge.eval_eq_evalFn`).

**Proof sketch.**
1. `B'` translates between the two formats around `B` (`NUPPT.exists_comp` with polynomial-time
   pre- and post-processing, or `NUPPT.ofPolyTime` of the composite to read `1^{ℓ₁(n)}`):
   - its input, the history `⟨⟨x₁, y₁⟩, ⟨…, []⟩⟩` (`encodeHist`), becomes `⟨[], ⟨⟨[], ⟨x₁, y₁⟩⟩,
     ⟨…, []⟩⟩⟩`, `B`'s empty input and its log (`encodeHist_cons`, `encodeLog_cons`,
     `bitCodec_encodeEntry` with `1^0 = []`), polynomial-time by iterating over the pairs;
   - `B`'s output, a move decoded by `decodeBitMove` (`decodeBitMove_eq_query_iff`,
     `decodeBitMove_of_not_canonical`, `decodeIdx_eq_some_iff` at `k = 1`), becomes the query
     `⟨[false], x⟩` for a query `x`, and the verdict `[true, b]` for an output `[b]` and for the
     default.
2. Both trees branch on corresponding moves, so by induction on the budget
   (`toOracleAdversary_eq` and `buildTree`'s case lemmas against `toCompOn_eq` and `buildComp`'s)
   their evaluations against `f` and `fun _ => f` agree (`QueryTree.eval_query`,
   `OracleComp.evalFn_query`); at the timeout the verdict `false` is bit `0` of `zeroBits 1`
   (`zeroBits_apply`).
3. `φ` transports the coins along `B.coins = B'.coins`, as in `exists_toCompOn_of_toComp`. -/
theorem exists_toOracleAdversary_of_bitCodec (B : NUPPT) (ℓ₁ ℓ₂ : PolyExpr) :
    ∃ B' : NUPPT, B'.coins = B.coins ∧ ∀ n : ℕ, ∃ φ : B.Coins n ≃ B'.Coins n,
      ∀ (q : ℕ) (r : B.Coins n) (f : (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)),
        (B'.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) q (φ r)).eval f =
          (B.toCompOn (bitCodec (fun _ : Fin 1 => ℓ₁.eval n) (fun _ => ℓ₂.eval n) 1) n q []
              r).evalFn (fun _ => f) 0 := by
  sorry

end TCSlib.Cryptography.Games
