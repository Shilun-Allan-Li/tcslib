# Fill brief (DRAFT, not issued): the efficiency of reductions (`Games/Efficiency.lean`)

**Status: draft, 2026-11-05, redrafted after ruling R-04-3.** The targets are those of PR #195 at
`243598b7cb0c3fdd50b22a92a011f1b77f55c8c6`: T1, T2, the companion `exists_toCompOn_of_toComp`
and T4, each `sorry` under its sketch. T3 (GGM as an instance) is no longer a target; it goes to
coordination point F-4.
- **Ruled:** a Claude fill on the GGM reduction machine's pattern (D-7, 2026-11-05); R-04-3
  (extend T0–T2 before issue; applied in `243598b7`).
- **Before issue:**
  - gate 04 round 2 closes and #195 merges into `cryptography/pass-shelat-ch2-4`; any statement
    repair re-freezes the targets below, and their quotes are refreshed;
  - the **ch. 2–4 clean-up PR** lands with the two prerequisites (below), and this brief names
    their final lemma names;
  - two rulings: file layout and sketch edits (route note, "Decisions before issue");
  - pre-ship probes at the issue tree:
    - an import probe of every name cited here;
    - a route probe: `GGMRed.stateLoopFun_eval` on a toy handler, and T4's move correspondence at
      `ℓ₁ = 0`;
    - a duplication probe (`exact?` on each planned helper);
  - the order list, its Mathlib roots and the base sorry set (four in `Games/Efficiency.lean`);
  - a review of this brief by a review sub-agent;
  - the issue commit (`@ANCESTOR@`).

The route note is `briefs/pass-shelat-ch5-8/design/S2b-efficiency.md`; **read it first**. Its
section "The route" is the one the Lean sketches cite.

## Repository and branch — read this before anything else

- Clone `https://github.com/Shilun-Allan-Li/tcslib` and check out `cryptography/pass-shelat-ch2-4`
  at the issue commit `@ANCESTOR@`. #195 and the clean-up PR are merged there by then.
- Create your working branch from it (suggested `fill/s2b-efficiency`). Record the base hash in
  `REPORT.md`, and never rebase.
- **Delivery is by zip**, `fill-s2b-efficiency.zip`, with the standard contents:
  - `REPORT.md`;
  - the owned file(s);
  - a `git format-patch` series and a git bundle;
  - the sweep log and the axiom prints;
  - `SHA256SUMS`.

  Send a checkpoint zip (`fill-s2b-efficiency-cpN.zip`) at each milestone below.

## What this is

A reduction runs a machine adversary `A` once and answers `A`'s queries with a polynomial-time
**handler**. The handler reads the context `⟨1^n, ⟨z, ω⟩⟩` (`seedIn`: the parameter, the
reduction's input `z` and its seed `ω`). It computes `A`'s input from it (`advIn`), answers each
query from its state, and finalizes from the final state and `A`'s output. A `PolyHandler` does
this alone (`out`). An `InteractiveHandler` may query outer oracles: at most `perCall(n)` queries
per inner query, then a finalization `finRun` with at most `finCall(n)` queries and an
`outLen(n)`-bit output. The targets say that such a reduction is again a machine's computation,
so assumptions quantified over `Complexity.NUPPT` apply to it.

## Targets (owned file `TCSlib/Cryptography/Games/Efficiency.lean`; lines at `243598b7`)

| Target | Declaration | Line | What |
|---|---|---|---|
| T1 | `TCSlib.Cryptography.Games.exists_handlerMachine` | 300 | a `PolyHandler` reduction is a machine with exactly the finalized output |
| T2 | `TCSlib.Cryptography.Games.exists_interactiveHandlerMachine` | 507 | an `InteractiveHandler` reduction is an oracle machine with budget `q·perCall + finCall`, equal as a tree |
| companion | `TCSlib.Cryptography.Games.exists_toCompOn_of_toComp` | 535 | a machine without input is a machine that ignores its input |
| T4 | `TCSlib.Cryptography.Games.exists_toOracleAdversary_of_bitCodec` | 566 | a one-oracle, one-bit `bitCodec` machine evaluates as a ch. 2–4 `toOracleAdversary` |

**Follow each docstring's proof sketch and the route note, or report why they fail.** The sketches
name the lemmas to use. Two route points that the sketches omit:
- the initial state `H.init n` is not polynomial-time; it goes into `B`'s **advice**;
- T2 needs a cost-scaling lemma.

Both are in the route note.

### The frozen statements (verbatim)

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

```lean
theorem exists_toCompOn_of_toComp (A : NUPPT) :
    ∃ A' : NUPPT, A'.coins = A.coins ∧ ∀ n : ℕ, ∃ φ : A.Coins n ≃ A'.Coins n,
      ∀ {ι α : Type} {spec : OracleSpec ι} (codec : MachineCodec spec α) (q : ℕ)
        (x : List Bool) (r : A.Coins n),
        A'.toCompOn codec n q x (φ r) = A.toComp codec n q r := by
  sorry
```

```lean
theorem exists_toOracleAdversary_of_bitCodec (B : NUPPT) (ℓ₁ ℓ₂ : PolyExpr) :
    ∃ B' : NUPPT, B'.coins = B.coins ∧ ∀ n : ℕ, ∃ φ : B.Coins n ≃ B'.Coins n,
      ∀ (q : ℕ) (r : B.Coins n) (f : (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)),
        (B'.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) q (φ r)).eval f =
          (B.toCompOn (bitCodec (fun _ : Fin 1 => ℓ₁.eval n) (fun _ => ℓ₂.eval n) 1) n q []
              r).evalFn (fun _ => f) 0 := by
  sorry
```

### The frozen definitions (T0)

Every definition and lemma of the file other than the four bodies is frozen. That covers:
- `bitSpecAt`, `seedIn`;
- the structures `PolyHandler` and `InteractiveHandler` (every field);
- `PolyHandler.input`/`advInput`/`result`/`answer`/`impl`;
- `InteractiveHandler.input`/`advInput`/`call`/`impl`/`finInput`/`finish`;
- their `_eq`, `_apply` and `answer_of_…` lemmas.

The ones your proofs unfold most:

```lean
def seedIn (n : ℕ) (z ω : List Bool) : List Bool :=
  pairEncode (List.replicate n true) (pairEncode z ω)
```

```lean
def answer (H : PolyHandler k din dout) (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool) (i : Fin k)
    (x : Fin ((din i).eval n) → Bool) :
    (Fin ((dout i).eval n) → Bool) × (Fin (H.stateLen.eval n) → Bool) :=
  match pairDecode (H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x))) with
  | some (yw, sw) =>
    ((decodeFin _ yw).getD (zeroBits _), (decodeFin _ sw).getD (zeroBits _))
  | none => (zeroBits _, zeroBits _)
```

```lean
def impl (H : PolyHandler k din dout) (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) :
    QueryImpl (bitSpecAt din dout n) (Fin (H.stateLen.eval n) → Bool) unifSpec :=
  fun i x s => .pure (H.answer n z ω s i x)
```

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
def impl (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) :
    QueryImpl (bitSpecAt din dout n) (Fin (H.stateLen.eval n) → Bool) (bitSpecAt din' dout' n) :=
  fun i x s => (H.call n z ω s i x).bind fun w =>
    .pure (fun j => w (Fin.castAdd _ j), fun j => w (Fin.natAdd _ j))
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

The structures' fields (types verbatim; docstrings omitted here, see the file):
- `PolyHandler k din dout`: `stateLen seedLen : PolyExpr`,
  `init : ∀ n, Fin (stateLen.eval n) → Bool`, `run : List Bool → List Bool`,
  `poly : PolyTimeComputable run`, `advIn : List Bool → List Bool`,
  `advIn_poly : PolyTimeComputable advIn`, `out : List Bool → List Bool`,
  `out_poly : PolyTimeComputable out`;
- `InteractiveHandler k din dout k' din' dout'`: `stateLen seedLen perCall : PolyExpr`,
  `init : ∀ n, Fin (stateLen.eval n) → Bool`, `run : List Bool → List Bool`,
  `poly : PolyTimeComputable run`, `advIn : List Bool → List Bool`,
  `advIn_poly : PolyTimeComputable advIn`, `outLen finCall : PolyExpr`,
  `finRun : List Bool → List Bool`, `finRun_poly : PolyTimeComputable finRun`.

The file's own definitions may be unfolded, but prefer their equation lemmas.

## Prerequisites (landed before issue)

Rule 10 forbids reading another file's definition without a published lemma. Two such lemmas are
missing at `243598b7`. They land in the **ch. 2–4 clean-up PR** (G3-5's clean-up, after #195),
which merges into `cryptography/pass-shelat-ch2-4` before this brief is issued. The issued brief
gives their exact names; the forms below are what that PR is asked for.

| Prerequisite | Beside | Form | Used by |
|---|---|---|---|
| `NUPPT.coinLen_eq` | `coinLen` (`TCSlib/Complexity/Randomized/PPT.lean`) | `A.coinLen n = A.coins.eval n` | every coin bijection `φ` (T1, T2, the companion, T4) |
| `decodeOracleMove`'s case lemmas | `decodeOracleMove` (`TCSlib/Cryptography/Asymptotic/PRF.lean`) | for every word: `⟨[false], x⟩` with `x` of length `ℓ₁` decodes as `query x`; with `x` of any other length as `ret false`; `[true, b]` as `ret b`; anything else as `ret false` | T4 |

The private `decodeOracleMove_eq` (PRF.lean) is not citable (rule 11). The same PR consolidates
`decodeFin_eq_some_iff`; until then cite `GGMRed.decodeFin_eq_some_iff` (`GGMReductionEval.lean`).

## Templates and tools (cite; do not copy)

- **The GGM reduction machine** (`Asymptotic/GGMReduction.lean`, `GGMReductionEval.lean`) is T1's
  construction for one handler.
  - Reuse verbatim, by citation, `GGMRed.stateLoopFun`, `stateLoopFun_poly`, `stateLoopFun_eval`,
    and `GGMRed.pairEncode_append_right`, the lemma behind "a log append is a concatenation".
  - Generalize by analogy its round, `rawFun_poly`, `rawFun_rawInput` and
    `ggmRedMachine_distinguisher`.
- **State loops:** `Complexity.StateLoop.orbit` (`orbit_zero`, `orbit_succ`), `gstep_iterate_eq`
  and `find?_range_eq_some` (`Complexity/Randomized/Build/StateLoop.lean`). Also
  `Complexity.polyTimeComputable_iterateEmit` (T4's `pre`), `polyTimeComputable_pairEq`
  (canonicity tests) and `polyTimeComputable_iterateFind` (`Repetition.lean`).
- **Machines:**
  - `NUPPT.ofPolyTime`, with `runAtL_ofPolyTime`, `output_ofPolyTime`, `advice_ofPolyTime`,
    `coins_ofPolyTime`, `runAt_eq` and `NUPPT.polyTimeComputable_output`;
  - the layout: `runAtL_eq_output_layout`, `inParam_layout`, `inArg_layout`, `inAdvice_layout`,
    `inCoins_layout` and `polyTimeComputable_layout`;
  - the closure theorems `NUPPT.exists_comp`, `exists_split` and `exists_withAdvice`, with
    `combineAdvice` (`Complexity/Randomized/Closure.lean`).
- **Coins:** `exists_queryChain_nuppt` (`Asymptotic/MultiMessageLemmas.lean`) is a worked
  bijection `φ`. Mathlib supplies `Fin.appendEquiv`, `List.ofFn_fin_append`, `List.ofFn_congr` and
  `finCongr`.
- **Pairing calculus:**
  - `PolyTimeComputable.pairEncode`, `.append` and `.comp`; `polyTimeComputable_pairFstD`,
    `polyTimeComputable_pairSndD`; `pairFstD_pairEncode`, `pairSndD_pairEncode`;
  - `polyTimeComputable_ite`, `polyTimeComputable_const`, `polyTimeComputable_id`
    (`ClassNP/PolyTimePairing.lean`, `PolyTime.lean`);
  - `polyTimeComputable_unaryPoly` (`Randomized/Primitives.lean`) and
    `PolyTimeComputable.output_length_le`.
- **The framework:**
  - `buildComp`'s case lemmas (`buildComp_zero_of_ret`, `buildComp_zero_of_query`,
    `buildComp_succ_of_ret`, `buildComp_succ_of_query`) and `buildComp_costBoundedBy`;
  - `NUPPT.toComp_eq`, `toCompOn_eq` and `toCompOn_costBoundedBy`; `MachineCodec.encodeLog_nil`
    and `encodeLog_cons`;
  - `simulate_pure`, `simulate_query`, `simulate_bind` and `simulate_costBoundedBy`;
  - `OracleComp.pure_bind`, `query_bind`, `bind_assoc`, `CostBoundedBy.bind` and
    `CostBoundedBy.mono`;
  - `OracleComp.evalFn_pure`/`_query`, `Bridge.eval_eq_evalFn`, `QueryTree.eval_ret`/`_query`.
- **The codec:**
  - `bitCodec_decodeMove`, `bitCodec_encodeEntry`, `bitCodec_timeout` and `encodeLog_bitCodec`;
  - `decodeBitMove_query`, `decodeBitMove_ret`, `decodeBitMove_eq_query_iff`,
    `decodeBitMove_of_not_canonical` and `decodeBitMove_encodeBitMove`; `encodeBitMove_query` and
    `encodeBitMove_ret`;
  - `decodeIdx_replicate`, `decodeIdx_eq_some_iff` and `decodeIdx_eq_none_iff`; `zeroBits_apply` and
    `ofFn_zeroBits`;
  - `decodeFin_ofFn` and `length_eq_of_decodeFin_eq_some`.
- **The ch. 2–4 decoder:**
  - `NUPPT.toOracleAdversary_eq`; `buildTree_zero_of_ret`, `buildTree_zero_of_query`,
    `buildTree_succ_of_ret` and `buildTree_succ_of_query`;
  - `encodeHist_nil` and `encodeHist_cons`;
  - `toComp_singleCodec`, `encodeLog_singleCodec` and `toHist` with its lemmas
    (`Games/Bridges/Machines.lean`).

## Allowed and forbidden moves

**Allowed:**
- Replace the four `sorry` bodies.
- Add `private` declarations in `namespace EffFill` (inside `TCSlib.Cryptography.Games`). If the
  layout ruling allows them, also add the helper files it names, with their one import line in
  `Efficiency.lean`.
- Edit the `**Proof sketch.**` paragraph of a target's docstring to match your proof, for example
  to add the advice for `init`, if the sketch-edit ruling allows it. Report every such edit.

**Forbidden:**
- **Statement changes of any kind.** The four statements, every T0 definition and field, every
  existing lemma, and the docstrings' statement prose stay byte-identical. A target that looks
  false or unprovable as stated is **reported** with the missing hypothesis or a counterexample,
  never patched.
- **Rule 10.** Never pass another file's TCSlib definition to `unfold`, `simp`, `rw`,
  `delta` or `dsimp`, and never read it through `rfl`, `show`, `decide` or term-mode defeq. Use
  its published lemmas: the lists above, and the two prerequisites.
  - Core and Mathlib definitions may reduce in a `rfl`, `decide` or `show` step, but are never
    passed to `simp`, `rw` or `unfold`; use their lemmas.
  - Abbreviations (`NUPPT.Coins`, `bitSpecAt`, `bitSpec`, `QueryTree`, `OracleAdversary`) are
    notation and may be read through.
- **Rule 11:**
  - cite no private declaration of another file (for example `decodeOracleMove_eq`, Closure's
    `ptc_comp`, BitCodec's `eq_ofFn_of_decodeFin`);
  - keep every new name under `EffFill`.
- **Reuse, not copy.** Do not copy GGM's proofs. If a lemma you need is private there, request it
  in `REPORT.md` and reprove a generic version under `EffFill`.
- **No new `@[simp]` attributes** and no new public declarations (except under the layout ruling).
  Also forbidden: `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `unsafe` and
  `set_option allowUnsafeReducibility`.
- **Never `lake build`**, and never an unfiltered `lake exe cache get`.
  - Check **one file at a time** with `bash scripts/lean_check_tree.sh <module path without .lean>`,
    in dependency order, one Lean process at a time.
  - Follow the environment addendum attached at dispatch: preflight, and the Mathlib cache for the
    order list's roots only.

## Deliverable and checks

1. `bash scripts/lean_check_tree.sh TCSlib/Cryptography/Games/Efficiency` exits 0, with **no
   `declaration uses 'sorry'` warning**: all four targets are filled. Do the same for every helper
   file, in order.
2. `bash scripts/lean_check_tree.sh TCSlib/Cryptography/Games/Bridges` (the facade, the only
   importer) exits 0.
3. **Axioms.** Run a scratch file (not delivered in the tree) with `#print axioms` for
   `exists_handlerMachine`, `exists_interactiveHandlerMachine`, `exists_toCompOn_of_toComp` and
   `exists_toOracleAdversary_of_bitCodec`, under the same `LEAN_PATH` as `lean_check_tree.sh`.
   Each prints at most `[propext, Classical.choice, Quot.sound]`. Deliver the prints.
4. **Rule 10 seal.** Compile a sealed copy of each owned file: `attribute [local irreducible]` on
   every other-file TCSlib definition your proofs mention, and `attribute [-simp]` on those of
   them that are `@[simp]`. Add one control that closes unsealed and fails sealed. List the sealed
   names in `REPORT.md`.
5. **Lint.** `python3 scripts/campaign_style_lint.py TCSlib/Cryptography/Games --check8b` reports
   0 FAIL on the owned file(s). The file-size WARN is recorded as the layout ruling says.
6. **Freeze and scope.** The diff touches only the owned file(s) and changes only the four bodies,
   the `EffFill` helpers and the allowed sketch edits. The maintainer checks the freeze at intake.

## Suggested order and milestones

- **M0, preflight.**
  - Sweep to `Games/Efficiency` and confirm exactly four `sorry`s.
  - Confirm that the two prerequisites are present at the base under the names this brief gives.
- **M1, the companion** (about 30–60 lines). `exists_comp` with `pre = pairSndD`, then `φ` by
  `coinLen_eq`. It exercises the coin transport that every target reuses. Checkpoint 1.
- **M2, T4** (about 150–250).
  - `pre` with `polyTimeComputable_iterateEmit`; `post` with canonicity tests by re-encoding.
  - The move correspondence: `decodeOracleMove`'s case lemmas against `decodeBitMove` at `k = 1`,
    `dα = 1`, including `ℓ₁(n) = 0`.
  - The evaluation equality, by induction on the budget. Checkpoint 2.
- **M3, the shared layer** (about 320–580).
  - S1, the string layer: log append; a canonical decoder that agrees with `decodeBitMove` on every
    word, with the `Fin k` length dispatch; fixed-length decoding with defaults.
  - S2, advice `⟨A.advice n, init n⟩` and the coins through `exists_split`.
  - S3, the replay lemma for `buildComp`.
- **M4, T1** (about 360–620).
  - The round and its polynomial time.
  - The orbit bound: fixed lengths, so recompute the context and `A`'s input from the retained
    input in each round.
  - The functional equation by induction on the remaining budget; `stateLoopFun_eval` with
    `R = q + 1`. Checkpoint 3.
- **M5, T2** (about 580–1000).
  - The replay round: three phases, a cursor into the outer log, three counters.
  - The round bound `(q + 1) + q·(perCall + 1) + finCall + 1`.
  - The cost bound: a scaling lemma for `CostBoundedBy`, then `simulate_costBoundedBy` and
    `CostBoundedBy.bind`.
  - The replay induction, then S3. Checkpoint 4, then the final delivery.

**Budget:** the companion, T4 and T1 complete beat T1 and T2 partial. A partial T2 is delivered with
its frontier: the remaining `sorry`s, each under a sketch, named in `REPORT.md`.

## REPORT.md checklist

- [ ] The base hash; each target filled, partial (with its frontier), or escalated (with the
  reason).
- [ ] Every new `private` (and helper-file declaration), with its role. Name S1, S3 and the scaling
  lemma as requested shared lemmas.
- [ ] The reuse-not-copy screen: what is cited from `GGMRed`, what is new, and any requests.
- [ ] Every sketch edit (if allowed).
- [ ] The sweep tail, the four axiom prints, the seal list with its control, and the lint line.
- [ ] The diff touches only the owned file(s).

## Known pitfalls

- **`init` is advice.** `H.init n` is an arbitrary function of `n`, so `B` takes
  `List.ofFn (H.init n)` in its advice, and `B` is non-uniform. No target claims uniformity.
- **Canonicity.** `pairFstD`/`pairSndD` return `[]` on malformed words, and with `din i (n)`,
  `dα(n)` or `ℓ₁(n)` equal to `0` an empty payload is valid. Decide "canonical query or output word"
  by re-encoding and comparing; never infer it from projections.
- **Two defaults.** `PolyHandler.answer` defaults **componentwise**; `InteractiveHandler.call`
  defaults **jointly**, through `decodeBitMove` at length `(dout i).eval n + stateLen(n)`.
  Mirror each exactly.
- **Budgets at zero.** `buildComp` still inspects the move at budget `0`: an output stops, a query
  gives the timeout without asking. This holds for `A` (timeout `zeroBits dα`), for each `call`
  and `finish` (`zeroBits`), and for `B` itself.
- **Tree equality (T2).** The equation is between trees, on every branch. Answers in `B`'s log are
  arbitrary, so the replay copies each answered entry and checks nothing. `B`'s budget
  `q·perCall + finCall` must never bind before the reduction ends (the cost invariant).
- **Round bound (T2).** `(q + 1) + q·(perCall + 1) + finCall + 1` assumes one activation per round
  (of `A`, `run` or `finRun`). Add 1 if `A`'s input is computed in a round rather than in
  `start`. The bound is in `|x|`, where `n ≤ |x|` (`PolyExpr.eval_mono`).
- **Log encodings.** A call's log is encoded with `bitCodec … 0`, and `B`'s log with
  `bitCodec … (H.outLen.eval n)`. `encodeLog_bitCodec` identifies them, and an append is a
  concatenation (`GGMRed.pairEncode_append_right`).
- **History lengths.** Prove that the genuine orbit fits the guard bound, which is where a missing
  length bound shows up. A bound uniform in `i : Fin k` is a finite sum of `PolyExpr`s.
