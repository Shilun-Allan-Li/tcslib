# S2b design note: the efficiency of reductions (the machine layer's crux)

Status: **statements restated under ruling R-04-3, at `243598b7cb0c3fdd50b22a92a011f1b77f55c8c6`
(PR #195, `Games/Efficiency.lean`); gate 04 round 2 (closing) dispatched 2026-11-05; proofs not
started.** The four targets are `sorry` under their sketches; they are the efficiency fill
(`fills/efficiency/brief-draft.md`). This note was redrafted on 2026-11-05. It replaces the note of
2026-11-04/05, whose statements (adversary without input, hidden final state, output padded with
`padFin`, no finalization, no bridge to the PRF assumption) predate R-04-3.

## The statement needed

A reduction of ch. 5–8 runs a machine adversary `A` once and answers its oracle queries with a
polynomial-time **handler**. Proved once, the targets say that the result is again a machine, so
the hardness assumptions, which quantify over machines (`Complexity.NUPPT`), apply to it. The
reduction then needs no machine construction of its own: the ch. 2–4 layer built one per reduction
(`Asymptotic/GGMReduction*`, `HardCoreGL*`, …), each several hundred lines.

### The shape of a reduction (T0, written; frozen at the fill's issue)

At parameter `n` the reduction has an input `z` and a seed `ω`, its own coins. Every function of a
handler reads them from the **context** `⟨1^n, ⟨z, ω⟩⟩`:

```lean
def seedIn (n : ℕ) (z ω : List Bool) : List Bool :=
  pairEncode (List.replicate n true) (pairEncode z ω)
```

(`seedIn_eq`). All lengths are polynomials in `n`, as `PolyExpr`s: queries and answers `din i`,
`dout i` (`bitSpecAt din dout n`, the abbreviation of `bitSpec` at the evaluated lengths), the
adversary's output `dα`, the handler's state and seed.

**`PolyHandler k din dout`** (no oracle of its own; the target spec is `unifSpec`). Fields, with
their types as in the file:

| Field | Type | Role |
|---|---|---|
| `stateLen`, `seedLen` | `PolyExpr` | lengths of the state and of the seed `ω` |
| `init` | `∀ n, Fin (stateLen.eval n) → Bool` | initial state; an arbitrary function of `n` |
| `run`, `poly` | `List Bool → List Bool`, `PolyTimeComputable run` | one query: `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨1^i, x⟩⟩⟩ ↦ ⟨y, s'⟩` |
| `advIn`, `advIn_poly` | `List Bool → List Bool`, `PolyTimeComputable advIn` | the adversary's input, from the context |
| `out`, `out_poly` | `List Bool → List Bool`, `PolyTimeComputable out` | the reduction's output, from `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, a⟩⟩` |

Derived (each with its `_eq` or case lemmas beside it): `PolyHandler.input`, `advInput`
(`H.advIn (seedIn n z (List.ofFn ω))`), `result` (`H.out` of the context, the final state and the
output), `answer` (the decoded `⟨y, s'⟩`, **componentwise** default: not a pair gives both
all-`false`, a wrong-length component is replaced by all-`false` on its own; lemmas
`answer_of_pairDecode_eq_none`, `answer_of_pairDecode_eq_some`, `answer_of_run_eq`), and `impl`,
the `QueryImpl (bitSpecAt din dout n) (Fin (H.stateLen.eval n) → Bool) unifSpec` answering with
`.pure (H.answer n z ω s i x)` (`impl_apply`).

**`InteractiveHandler k din dout k' din' dout'`** (it may query `k'` outer bit-string oracles):

| Field | Type | Role |
|---|---|---|
| `stateLen`, `seedLen` | `PolyExpr` | as above |
| `perCall` | `PolyExpr` | outer queries per inner query, at most |
| `init` | `∀ n, Fin (stateLen.eval n) → Bool` | as above |
| `run`, `poly` | `List Bool → List Bool`, `PolyTimeComputable run` | one round of a call, on `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩` (`L`: the call's outer log so far) |
| `advIn`, `advIn_poly` | `List Bool → List Bool`, `PolyTimeComputable advIn` | as above |
| `outLen` | `PolyExpr` | length of the reduction's output |
| `finCall` | `PolyExpr` | outer queries of the finalization, at most |
| `finRun`, `finRun_poly` | `List Bool → List Bool`, `PolyTimeComputable finRun` | one round of the finalization, on `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨a, L⟩⟩⟩` |

A round returns a move in `bitCodec`'s format: an outer query `⟨[false], ⟨1^j, x'⟩⟩`, or the result
`⟨[true], w⟩`. The derived definitions are `buildComp` computations over the outer oracles:

```lean
def call (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool) (i : Fin k)
    (x : Fin ((din i).eval n) → Bool) :
    OracleComp (bitSpecAt din' dout' n) (Fin ((dout i).eval n + H.stateLen.eval n) → Bool) :=
  buildComp (fun L => decodeBitMove (fun j => (din' j).eval n) (fun j => (dout' j).eval n) _
      (H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x)
        ((bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) 0).encodeLog L))))
    (zeroBits _) (H.perCall.eval n) []
```

```lean
def finish (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool) {d : ℕ}
    (a : Fin d → Bool) : OracleComp (bitSpecAt din' dout' n) (Fin (H.outLen.eval n) → Bool) :=
  buildComp (fun L => decodeBitMove (fun j => (din' j).eval n) (fun j => (dout' j).eval n)
      (H.outLen.eval n)
      (H.finRun (finInput n z (List.ofFn ω) (List.ofFn s) (List.ofFn a)
        ((bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) 0).encodeLog L))))
    (zeroBits _) (H.finCall.eval n) []
```

`impl` runs one `call` per inner query and splits its `(dout i).eval n + H.stateLen.eval n` bits
into the answer and the new state (`Fin.castAdd`, `Fin.natAdd`). The default is **joint**
(`decodeBitMove`'s `zeroBits`): a malformed round output, a wrong total length or a spent budget
gives the all-`false` answer and state. Equation lemmas: `input_eq`, `advInput_eq`, `call_eq`,
`impl_apply`, `finInput_eq`, `finish_eq`.

### The targets

**T1** (`exists_handlerMachine`): the machine's output is exactly the finalized output of the
simulation.

```lean
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
  sorry
```

**T2** (`exists_interactiveHandlerMachine`): an oracle machine against the outer oracles, with
budget `q(n)·perCall(n) + finCall(n)`, whose computation tree is exactly the simulation followed
by the finalization.

```lean
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
```

**The companion** (`exists_toCompOn_of_toComp`): a machine without input is a machine that
ignores its input, with the same coins, for every codec and budget.

```lean
theorem exists_toCompOn_of_toComp (A : NUPPT) :
    ∃ A' : NUPPT, A'.coins = A.coins ∧ ∀ n : ℕ, ∃ φ : A.Coins n ≃ A'.Coins n,
      ∀ {ι α : Type} {spec : OracleSpec ι} (codec : MachineCodec spec α) (q : ℕ)
        (x : List Bool) (r : A.Coins n),
        A'.toCompOn codec n q x (φ r) = A.toComp codec n q r := by
  sorry
```

**T4** (`exists_toOracleAdversary_of_bitCodec`): the bridge to the PRF assumption. A one-oracle
`bitCodec` machine with a one-bit output, on the empty input, evaluates as a ch. 2–4 next-query
machine (an equality of evaluations, not of trees: the index types are `Unit` and `Fin 1`).

```lean
theorem exists_toOracleAdversary_of_bitCodec (B : NUPPT) (ℓ₁ ℓ₂ : PolyExpr) :
    ∃ B' : NUPPT, B'.coins = B.coins ∧ ∀ n : ℕ, ∃ φ : B.Coins n ≃ B'.Coins n,
      ∀ (q : ℕ) (r : B.Coins n) (f : (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)),
        (B'.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) q (φ r)).eval f =
          (B.toCompOn (bitCodec (fun _ : Fin 1 => ℓ₁.eval n) (fun _ => ℓ₂.eval n) 1) n q []
              r).evalFn (fun _ => f) 0 := by
  sorry
```

**Who consumes them** (`gates/04-s2b/resolutions-r1.md`, the table of the eight prong sketches):
T1 for Lamport (Thm 137.2), hash-and-sign's `B` (Thm 144.1) and `padded_cpa`; T2 for hash-and-sign's
`C`, the PRF MAC (Thm 135.4), the CPA/CCA1 scheme (Thm 168.2), CCA2 (Thm 170.4) and
non-malleability (Thm 175.9 ⇒); T4 with T2 for the three PRF-based ones; the companion wherever the
adversary has no input. Two consumer-side notes:
- **T4 after T2.** T2's machine runs on the input `z` with codec index `H.outLen.eval n`; T4 needs
  the empty input, one outer oracle with `din' = fun _ => ℓ₁` and `dout' = fun _ => ℓ₂`, and the
  literal output length `1`. A consumer hard-wires `z` (`NUPPT.exists_withAdvice`, then
  `NUPPT.exists_comp` to re-pair the input) and rewrites `H.outLen.eval n = 1` with
  `PolyExpr.eval_const`. That glue is the prongs', not the fill's.
- **Time in `n + |z|`.** `B`'s running time is polynomial in its whole input, so in `n + |z|`. A
  reduction that claims time polynomial in `n` alone bounds `|z|` itself.

## A close relative (found 2026-11-05)

Frederick's GGM reduction machine (`TCSlib/Cryptography/Asymptotic/GGMReduction.lean`,
`GGMReductionEval.lean`) is T1's construction for one handler, a lazily sampled table:
- it runs a next-query machine to completion in a state loop, holding the encoded history and the
  table; each round runs the machine, decodes the move and answers from the reduction's own coins;
- its loop, `GGMRed.stateLoopFun` with `stateLoopFun_poly` and `stateLoopFun_eval`, is generic in
  start, step, acceptance and output, and **is reused verbatim** (by citation);
- the round, `rawFun_poly` and the GGM identity are specific, and are generalized by analogy.

The fill adds the **log-replay variant** (T2) for reductions that are oracle machines. GGM becomes
an instance of T1 at the integration of ch. 2–4 (coordination point F-4). That is not a target of
this fill: the T3 of earlier drafts is gone from the file, and the near-duplication of GGM's round
goes in the duplication ledger at the fill's landing, until F-4.

## Relation to P^O = P (checked 2026-11-05, at the user's prompt)

In substance the efficiency result is *FP with an efficiently implementable oracle is FP*. The
Turing-machine form is `Turing.FinOracleTM.exists_plain_simulation`
(`Complexity/TuringMachine/Build/OracleSim.lean`), behind `Complexity.POracle_eq_P_of_mem_P`
(`ClassOracle/Classes.lean`). Both are now on this branch (`main` was merged, #186). They are
**not reused**:
1. **The machine model.** They are about oracle Turing machines ([AB09, Def 3.4]: query tape,
   `qQuery`/`qYes`/`qNo`). Our adversaries are plain machines restarted on the encoded history
   (D7). In that model the statement is function-level: closure of polynomial-time functions under
   polynomially bounded iteration (`Complexity.polyTimeComputable_iterateFind`, through
   `GGMRed.stateLoopFun`).
2. **The oracles.** They need a *language* oracle decided by a plain machine (one-bit answers, no
   state, no coins). Our handlers answer strings, keep state and read a seed.

Routing through them would need a bridge from `NUPPT` next-move machines to oracle Turing
machines, which costs more than the function-level route.

## The route

Common to every proof: the machine is `NUPPT.ofPolyTime` of a polynomial-time function of the raw
layout `⟨⟨⟨1^n, y⟩, α⟩, r⟩`, read only through `runAtL_eq_output_layout`, `output_ofPolyTime`,
`advice_ofPolyTime`, `coins_ofPolyTime` and the projections `inParam_layout`, `inArg_layout`,
`inAdvice_layout`, `inCoins_layout` (`Complexity/Randomized/Closure.lean`, `PPT.lean`), or it comes
from a closure theorem (`NUPPT.exists_comp`, `exists_split`). Polynomial time is
`GGMRed.stateLoopFun_poly` on a round built from the pairing calculus, `polyTimeComputable_ite`,
`polyTimeComputable_unaryPoly` (to write `1^{p(n)}` from `1^n`) and
`NUPPT.polyTimeComputable_output`.

### Shared pieces

- **S1. The string layer of `bitCodec`.**
  - *Appending to a log is concatenation:* `(bitCodec …).encodeLog (h ++ [e]) = encodeLog h ++
    pairEncode (encodeEntry e) []`, by induction from `MachineCodec.encodeLog_nil`/`_cons` and
    `GGMRed.pairEncode_append_right` (the pattern of `GGMRed.histEnc_append_single`). With
    `encodeLog_bitCodec` the output length of the codec does not matter.
  - *A polynomial-time canonical decoder* that agrees with `decodeBitMove` on **every** word:
    canonical query word, canonical output word, or the default. It is read through
    `decodeBitMove_query`, `decodeBitMove_ret`, `decodeBitMove_eq_query_iff` and
    `decodeBitMove_of_not_canonical`, and `decodeIdx_eq_some_iff`/`_eq_none_iff` for the index.
    Canonicity is tested by **re-encoding and comparing** (`polyTimeComputable_pairEq`), never by
    projections alone: `pairFstD`/`pairSndD` return `[]` on a malformed word, and when `din i (n)`
    or `dα(n)` is `0` an empty payload is valid. The payload length `(din i).eval n` is selected
    by a `k`-way case split on the decoded index (`k` is fixed), by induction on `k` with
    `polyTimeComputable_ite`.
  - *Fixed-length decoding with a default* (`(decodeFin ℓ w).getD (zeroBits ℓ)` as a string
    function), read through `decodeFin_ofFn`, `length_eq_of_decodeFin_eq_some` and
    `GGMRed.decodeFin_eq_some_iff`; and splitting a `dout + stateLen` word.
- **S2. Machine glue.**
  - **The initial state goes into the advice.** `init` is an arbitrary function of `n`, not a
    polynomial-time one. The machine takes `⟨A.advice n, List.ofFn (H.init n)⟩` as its advice
    (`combineAdvice` or a pair, length bound from `advice_length` and `stateLen`). So `B` is
    non-uniform even when `A` is uniform. T1 and T2 do not claim uniformity, and the assumptions
    quantify over non-uniform machines. Neither Lean sketch says this yet.
  - **Coins.** `NUPPT.exists_split` with `p = H.seedLen` turns `B₀` (argument `⟨y, ω⟩`, coins `r`,
    with `B₀.coins = A.coins`) into `B` with `B.coins = .add H.seedLen A.coins`. `φ` is
    `Fin.appendEquiv` composed with the transport along `B.coinLen n = H.seedLen.eval n +
    A.coinLen n`. That equation needs `NUPPT.coinLen_eq` (prerequisite 1, below) and
    `PolyExpr.eval_add`. Then `List.ofFn (φ (ω, r)) = List.ofFn ω ++ List.ofFn r`
    (`List.ofFn_fin_append`, `List.ofFn_congr`), and `take`/`drop` give `ω` and `r`. This is the
    pattern of `exists_queryChain_nuppt` (`Asymptotic/MultiMessageLemmas.lean`).
- **S3. A replay lemma for `buildComp`.** Say that a next-move function `next` *replays* a tree
  `t` from a log `O` when `next O` is `t`'s first move and, at a query node, `next` replays every
  continuation from `O` extended by that query and its answer. If `next` replays `t` from `O`, and
  `t` is `CostBoundedBy (fun _ => 1)` within `b`, then `buildComp next timeout b O = t`. The proof
  is an induction on `t` with `buildComp`'s four case lemmas. T2 uses it. (T4 compares two
  different specs, so it needs its own induction.) It is a private helper, requested for promotion
  in the report.

### T1 (`exists_handlerMachine`): simulation inside a plain machine

1. **The loop.** `B₀`'s raw function is `GGMRed.stateLoopFun start step acc out R Bd` on the layout
   `x = ⟨⟨⟨1^n, ⟨z, ω⟩⟩, α⟩, r⟩`. The state holds only fixed-length data: `A`'s encoded inner log
   (at most `q(n)` entries `⟨1^i, ⟨x, y⟩⟩`), `H`'s state (`stateLen(n)` bits), a unary query
   counter, and on stopping `A`'s output and a done flag. The context `seedIn n z ω` and `A`'s
   input `H.advIn (seedIn n z ω)` are **recomputed from `x` in every round**, so they need no
   bound. (Keeping `A`'s input in the state instead needs `PolyTimeComputable.output_length_le` on
   `H.advIn_poly`.)
2. **A round.**
   - Run `A` on `⟨A's input, encoded log⟩` with the coins `r` and `A`'s half of the advice
     (`runAtL_eq_output_layout` read backwards), and decode the move (S1).
   - On a query `(i, x)` with the counter below `q(n)`: run `H.run` on `⟨ctx, ⟨s, ⟨1^i, x⟩⟩⟩`,
     decode `⟨y, s'⟩` with `answer`'s componentwise default, append `⟨1^i, ⟨x, y⟩⟩` (S1), set the
     state to `s'` and count.
   - On a query with the counter at `q(n)`: stop with `zeroBits dα` (the codec's timeout).
   - On an output `a`: stop with `a`.
3. **Rounds.** At most `q(n) + 1`, one activation of `A` per round, so `R := q + 1`.
   `stateLoopFun_eval` needs `N ≤ R.eval |x|`, which holds because `n ≤ |x|` and
   `PolyExpr.eval_mono`.
4. **Output.** `out` returns `H.out ⟨seedIn n z ω, ⟨s, a⟩⟩`, so `B`'s output is exactly
   `H.result n z ω s a` (`result_eq`, `seedIn_eq`).
5. **The functional equation.** By induction on the remaining budget `b`: start the orbit from the
   inner log `h`, the state `s` and the counter `q(n) − b`. It stops, within `b + 1` rounds, with
   some `(a, s_fin)`, and `simulate (H.impl n z ω) (buildComp next (zeroBits _) b h) s =
   .pure (a, s_fin)` for that same pair. The ingredients are `toCompOn_eq`, `buildComp`'s case
   lemmas, `bitCodec_decodeMove`, `bitCodec_timeout`, `simulate_pure`, `simulate_query`,
   `PolyHandler.impl_apply`, `OracleComp.pure_bind` and the `answer` lemmas. Then
   `stateLoopFun_eval` and `StateLoop.orbit_succ` read off the result, and S2 transports the
   coins.

### T2 (`exists_interactiveHandlerMachine`): simulation by an oracle machine (log replay)

1. **The next-move function.** `B₀`'s argument is `⟨⟨z, O⟩, ω⟩` (`B`'s input `⟨z, O⟩`, then
   `exists_split`), where `O` is `B`'s encoded outer log. The raw function replays the whole
   reduction in a state loop. The state holds:
   - the phase (adversary, call, finalization, done);
   - `A`'s inner log and remaining budget, and `H`'s state;
   - in a call: the pending inner query `(i, x)`, the call's log `L` and its counter;
   - in the finalization: `a`, its log and its counter;
   - a cursor into `O`;
   - when done, the word to output.

   Each round performs **one activation**:
   - **adversary:** run `A`; a query within budget opens a call; an output `a`, or a query at
     budget `q(n)` (`a := zeroBits dα`), opens the finalization;
   - **call:** run `H.run` on `⟨ctx, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩`, decoded with
     `decodeBitMove din' dout' ((dout i).eval n + stateLen(n))`:
     - an answer `w` (or the joint default) is split into `y` and `s'`; append `⟨1^i, ⟨x, y⟩⟩` to
       the inner log and return to the adversary;
     - an outer query with the call's budget spent gives `zeroBits`, as `buildComp` does at `0`;
     - an outer query within budget is answered from `O` at the cursor: append that entry to `L`
       and advance;
     - if `O` is exhausted, stop: **this is `B`'s next move**, the canonical query word
       (`encodeBitMove`);
   - **finalization:** the same with `H.finRun` on `⟨ctx, ⟨s, ⟨a, L⟩⟩⟩`; an output `b`, or the
     default at budget `finCall(n)`, stops with the canonical output word `⟨[true], b⟩`.
2. **The round bound.** The worker's figure **`(q + 1) + q·(perCall + 1) + finCall + 1` is
   correct**, checked against the definitions. It counts the most activations a replay can make:
   - `A.toCompOn … (q.eval n)` is `buildComp` with budget `q(n)`, so at most `q(n) + 1`
     activations of `A`, of which at most `q(n)` open a call;
   - each `call` is `buildComp` with budget `perCall(n)`, so at most `perCall(n) + 1` rounds of
     `run`;
   - `finish` is `buildComp` with budget `finCall(n)`, so at most `finCall(n) + 1` rounds of
     `finRun`.

   With one activation per round, and with the context and `A`'s input computed in `start` or
   recomputed in each round, the stopping round `N` is at most `2q + q·perCall + finCall + 2`. As a
   `PolyExpr` in `|x|`: `.add (.add (.add q (.const 1)) (.mul q (.add perCall (.const 1))))
   (.add finCall (.const 1))`. If `A`'s input is computed in a first round instead of in `start`,
   add 1. The figure is the **loop's** bound; `B`'s **query** budget is `q·perCall + finCall`.
   (The round 1 auditor's count, `q + 1` activations of `A` and `q·(perCall + 1)` of `run`,
   predates the finalization.)
3. **Polynomial size.** Every stored item has a fixed polynomial length in `n`, except the cursor
   into `O`, which is bounded by `|x|`. A per-entry bound over `Fin k` or `Fin k'` is a finite sum
   of `PolyExpr`s.
4. **The budget never binds early.** The reduction tree is `CostBoundedBy (fun _ => 1)` within
   `q·perCall + finCall`. This follows from `NUPPT.toCompOn_costBoundedBy`,
   `buildComp_costBoundedBy` for `call` and `finish`, `simulate_costBoundedBy` with cost
   `perCall(n)` per inner query, and `CostBoundedBy.bind`. Charging `perCall` per query needs a
   small scaling lemma from `CostBoundedBy (fun _ => 1) c q` to
   `CostBoundedBy (fun _ => p) c (q * p)`, which the library lacks (by induction, with
   `CostBoundedBy.mono`).
5. **The functional equation.** `B`'s decoded next move **replays** the reduction tree from the
   empty log (S3). The proof is by induction along the reduction's positions:
   - at each position, `stateLoopFun_eval` evaluates the replay on the position's outer log;
   - the reduction side unfolds through `simulate_query`, `simulate_bind`, `impl_apply`,
     `call_eq`, `finish_eq`, `OracleComp.bind_assoc`, `pure_bind` and `query_bind`;
   - `B`'s side through `toCompOn_eq`, `bitCodec_decodeMove` and `decodeBitMove_encodeBitMove`.

   S3 with step 4 gives the equality of trees. The equality is required on **every branch**, since
   the outer answers are arbitrary: the replay copies each answered entry from `O` and never
   checks it.

### The companion (`exists_toCompOn_of_toComp`)

`A' :=` `NUPPT.exists_comp A` with `pre = pairSndD` (`polyTimeComputable_pairSndD`) and
`post = id` (`polyTimeComputable_id`). Then `A'.coins = A.coins` and
`A'.runAtL n ⟨x, L⟩ r = A.runAtL n L r` (`pairSndD_pairEncode`). `φ` transports the coins along
`A.coinLen n = A'.coinLen n` (`NUPPT.coinLen_eq`, `finCongr`), so that
`List.ofFn (φ r) = List.ofFn r` (`List.ofFn_congr`). With `runAt_eq` the two next-move functions
agree on every log, and `toCompOn_eq` and `toComp_eq` conclude.

### T4 (`exists_toOracleAdversary_of_bitCodec`)

1. **`B' :=` `NUPPT.exists_comp B pre post`**, so `B'.coins = B.coins`. Neither map needs `n`: both
   decoders check the payload length `ℓ₁(n)` themselves, and they agree on it.
   - **`pre`** maps the history `⟨⟨x₁, y₁⟩, ⟨…, []⟩⟩` (`encodeHist`) to `⟨[], ⟨⟨[], ⟨x₁, y₁⟩⟩,
     ⟨…, []⟩⟩⟩`, the empty input followed by `B`'s log (`bitCodec_encodeEntry` with `1^0 = []`,
     `encodeLog_cons`, `encodeHist_cons`). It is polynomial-time as
     `Complexity.polyTimeComputable_iterateEmit` with `g = pairSndD`, emitting `⟨⟨[], e⟩, []⟩` for
     the head `e` of a non-empty suffix and nothing for `[]` (`StateLoop.isNil_poly`,
     `polyTimeComputable_ite`), with `R = var`. The emitted pieces concatenate to the nested
     encoding by `GGMRed.pairEncode_append_right`.
   - **`post`** maps a canonical query word `⟨[false], ⟨[], x⟩⟩` (tested by re-encoding) to
     `⟨[false], x⟩`, the word `⟨[true], [true]⟩` to `[true, true]`, and every other word to
     `[true, false]`. With `decodeIdx 1` accepting only `[]`, these agree with `decodeBitMove` at
     `k = 1` and `dα = 1` (`decodeBitMove_eq_query_iff`, `decodeBitMove_ret`,
     `decodeBitMove_of_not_canonical`, `decodeIdx_eq_some_iff`) and with `decodeOracleMove ℓ₁`. The
     agreement includes a payload of the wrong length, which is the verdict `false` on both sides.
     Reading `decodeOracleMove` needs its case lemmas (prerequisite 2).
2. **Evaluation.** `toOracleAdversary_eq` and `buildTree`'s case lemmas give the left side;
   `toCompOn_eq` and `buildComp`'s give the right. (Alternatively, `toComp_singleCodec` and
   `Bridge.eval_eq_evalFn` turn the left side into `OracleComp.evalFn`.) By induction on the budget,
   generalizing the corresponding histories and logs, both evaluations take the same branch: the
   answer is `f x` on both sides (`QueryTree.eval_query`, `OracleComp.evalFn_query`). At the
   timeout, `false` is bit `0` of `zeroBits 1` (`zeroBits_apply`).
3. **`φ`** transports the coins, as in the companion.

### Rule 10 map

Every proof reads other files' definitions only through published lemmas. Two are missing today and
are the fill's **prerequisites**:
1. `NUPPT.coinLen_eq`, beside `coinLen` (`Complexity/Randomized/PPT.lean`): `A.coinLen n =
   A.coins.eval n`. It is needed for every `φ`.
2. `decodeOracleMove`'s case lemmas, beside its definition (`Cryptography/Asymptotic/PRF.lean`):
   - the query word `⟨[false], x⟩` with `|x| = ℓ₁` decodes as the query;
   - with `|x| ≠ ℓ₁` it decodes as `ret false`;
   - `[true, b]` decodes as `ret b`;
   - every other word decodes as `ret false`.

   Today only the private `decodeOracleMove_eq` exists, and it is not citable (rule 11). T4 needs
   these lemmas.

Both land in the **ch. 2–4 clean-up PR** (G3-5's, after #195), before the fill is issued
(`QUEUE.md`, "G3-5 clean-up PR to-do"). The rest is published:
- the codec (`BitCodec.lean`), `buildComp`, `toComp`/`toCompOn` and `encodeLog` (`Machines.lean`);
- `simulate` (`Simulate.lean`); `bind` and `CostBoundedBy` (`OracleComp.lean`);
- `evalFn` and `eval` (`Bridges/QueryTree.lean`, `OracleAdversary.lean`);
- `toOracleAdversary`, `buildTree` and `encodeHist` (`PRF.lean`);
- the layout and closure theorems (`Closure.lean`, `PPT.lean`);
- `orbit` (`Build/StateLoop.lean`);
- `stateLoopFun` (`GGMReduction.lean`), and `decodeFin` (`Adversary.lean`, `GGMReductionEval.lean`).

`NUPPT.Coins`, `bitSpecAt`, `bitSpec`, `QueryTree` and `OracleAdversary` are abbreviations, read
through as notation.

## Obligations and size (estimate)

| Piece | Kind | Lines |
|---|---|---|
| S1: the string layer (log append, canonical decoder with the `Fin k` dispatch, fixed-length decoding, word splitting) | FP + framework | 200–350 |
| S2: machine glue (advice with `init`, `exists_split`, the coin bijection) | glue | 80–150 |
| S3: the replay lemma for `buildComp` | framework | 40–80 |
| T1: round, `start`/`acc`/`out`, polynomial time | FP | 150–250 |
| T1: orbit bound | arithmetic | 60–120 |
| T1: functional equation | framework | 150–250 |
| T2: replay round (three phases, cursor, three counters), polynomial time | FP | 250–400 |
| T2: orbit bound and round count | arithmetic | 80–150 |
| T2: cost bound (with the scaling lemma) and the replay induction | framework | 250–450 |
| The companion | glue | 30–60 |
| T4: `pre` and `post` and their polynomial time, the move correspondence, evaluation by induction | FP + framework | 150–250 |
| **Total** | | **about 1.4–2.5k** |

**Against the earlier estimates.** The old note estimated 0.8–1.5k lines, of which 150–250 were
the T0 definitions, now written, so 0.65–1.25k were proofs. The gate 04 review added 400–700 lines
for R-04-3. My breakdown of that increase agrees, at about +430–760:
- input threading, +50–100;
- exact output through `out`, +50–100;
- the finalization as a third replay phase, +150–250;
- T4, +150–250;
- the companion, +30–60.

That sum, about 1.1–2.0k, still omits three items that do not depend on R-04-3:
- the canonical decoder (S1, about +150–250). The old route assumed a handler step format of its
  own; `bitCodec`'s strict grammar came later (R-04-1);
- `init` through the advice and the coin transport (S2, about +50–100);
- T2's conclusion is an equality of trees on every branch, not of outputs, so it needs S3, the
  cost invariant and the scaling lemma (about +100–200).

Hence 1.4–2.5k. A calibration: GGM's machine (`GGMReduction.lean` 863 lines,
`GGMReductionEval.lean` 749) is one T1-like reduction.
- About 0.5–0.6k of its 1.6k lines is handler-specific: the table, the lookup loop, the tree walk
  and the concrete distinguisher's recursion.
- The rest, about 1.0k, is the part a generic T1 redoes.
- My T1 share (S1, S2, the T1 rows) is 0.64–1.12k, which is consistent.

**File size.** Efficiency.lean has 574 lines and would reach about 2–3k. `policy.md` says a file
approaching 1000 lines should be split unless there is a positive reason not to, and the campaign
lint warns above 1000 lines. Ruling below.

## Dependencies

- **Landed or in review:**
  - the S2a core (gate 02, closed): `OracleComp`, `simulate`, `QueryImpl`, `CostBoundedBy`;
  - S2b's T0, `BitCodec`, `Machines` and `Bridges` (#195; gate 04 round 2 dispatched; head
    `243598b7`);
  - the ch. 2–4 layer: `GGMRed.stateLoopFun`, `StateLoop`, `Repetition`, `Closure`, `PPT`, the
    pairing calculus, `PRF.lean`.

  Everything cited is in `Games/Efficiency.lean`'s import closure, through `Bridges/Machines` →
  `Asymptotic/PRF` → `GGMReduction`/`GGMReductionEval`.
- **Prerequisites** (ch. 2–4 clean-up PR, before issue):
  - `NUPPT.coinLen_eq`;
  - `decodeOracleMove`'s case lemmas.

  The same PR consolidates `decodeFin_eq_some_iff` (today `GGMRed.decodeFin_eq_some_iff`) and makes
  the `stateFind` family public. The fill needs neither, but the brief names their homes at issue.
- **Mathlib:** `List.ofFn_congr`, `List.ofFn_fin_append`, `Fin.appendEquiv`, `finCongr`.
- **Host rule** (`policy.md`, "Hosts come first"). The host is the shared state loop
  (`GGMRed.stateLoopFun` over `Complexity.StateLoop`). T1 and T2 are themselves the public,
  statement-gated contracts of the reduction runner. The fill's rounds are private leaf steps
  plugged into that host. S1 and S3 are candidates for the shared layer: the report requests them.

## Out of scope

- **Rewinding** the adversary: forking-lemma reductions, and simulators that rewind a verifier.
- **Several runs of the adversary**, sequential or with shared state: two-run hybrids,
  amplification by repetition. One run, once, is covered. Several runs compose at the consumer
  through `NUPPT.exists_seq`, outside these targets.
- **Variable lengths:**
  - queries, answers, outputs or states whose length depends on anything but `n`;
  - a number of oracles that depends on `n`.
- **Uniformity** of `B`: not claimed (the initial state is advice).
- **Time polynomial in `n` alone** when `|z|` is unbounded (the consumer's bound).
- **GGM as an instance** (F-4), and the consumer glue: the eight prong re-citations, and
  hard-wiring `z` before T4.

## Decisions before issue

1. **File layout** (ruling).
   - (A, recommended) The fill may add upstream helper files under `Games/Efficiency/`, imported by
     `Efficiency.lean` with one new import line. Candidates are the string layer S1 and the replay
     lemma S3, which need only `BitCodec`/`Machines`, and possibly the T2 replay round over raw
     string functions. Their public declarations carry docstrings and lemmas per policy, and are
     audited at the fill gate.
   - (B) Everything stays in `Efficiency.lean`, with a recorded justification for the 1000-line
     warning: one statement-frozen file, private helpers.
2. **Sketch edits.** Should the fill update the targets' `**Proof sketch.**` paragraphs, for example
   to add the advice for `init`, and keep the statement prose byte-identical? Recommended yes
   (`policy.md` §3, synchronization), each edit reported.

## Who and when

- **Fill item** (D-7: a Claude fill; ruled 2026-11-05), on GGM's pattern. It is issued after gate
  04 closes, #195 merges and the clean-up PR lands with the two prerequisites.
- **Pre-ship probes**, at the issue tree:
  - an import probe of every cited name;
  - a route probe: `GGMRed.stateLoopFun_eval` on a toy handler (one that answers every query with
    a fixed function), and the T4 `post` correspondence at `ℓ₁ = 0`;
  - a duplication probe (`exact?` on the S1 and S3 lemmas, the scaling lemma, and log append).
- **Suggested order:** the companion, T4, S1–S3, T1, then T2. If the budget runs short, T1
  complete beats T1 and T2 partial.
