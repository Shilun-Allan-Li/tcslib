# U2: the two-work-tape universal machine at linear overhead, and the parameterized diagonal argument (design note)

**Status: design draft for the user. No repository edit has been made.** Written read-only
against the campaign tip `c52663f159c05b1280ea5b5b129a8cfa22e04bb9`
(`origin/complexity/arora-barak-ch3-4`, with #92, the B6 hosts, #93, and #94, the H1 harvest,
merged; MEASURED by `git rev-parse` and `git diff --stat`). Probes were elaborated with
`tools/leanelab.sh` against the snapshot `oleans-lh1`. Earlier probe runs at `759471be`
(`oleans-lm0b`) and `fd63239a` (`oleans-lb6`) are superseded.
- `TimeHierarchy/*`, `Codes2Tape`, `Build/StepBlock` and `Universal` are byte-identical across
  the three tips (MEASURED, `git diff --stat`).
- `CodeSimulator` changed with #94 (35 insertions, 326 deletions). No public `theorem`, `lemma`
  or `def` line differs (MEASURED, `git diff`): only the private H1 assembly moved out to
  `Build/StepBlockLoop`.
- The final probe runs are at `oleans-lh1`.

Sizes are labelled MEASURED (counted in the tree or the probe) or ESTIMATE.

**Evidence** (in `design-u2/probes/`):

| File | sha256 (prefix) | Result at `oleans-lh1` |
|---|---|---|
| `U2DeclCheck.lean` | `e8d9d7a51ec52c1a` | 0 errors. Every cited declaration exists with the type quoted below (`U2DeclCheck.out`) |
| `U2DiagParam.lean` | `6e827fdb29d3068a` | 0 errors. Exactly 6 `sorry` warnings, all deliberate (§7) |

The axiom prints in `U2DiagParam.out` support three claims:
- **The parameterization is fully proved, with standard axioms only.** This covers the generic
  layer, the `f²` instance, the re-derivations of every public theorem of `Diagonal.lean` with
  their statements verbatim, and the `f log f` layer from one hypothesis.
- **The chain to the book-strength theorem is proved except for two inputs.** Its only
  remaining gaps are the G5 interface and the U2 statements.

---

## 0. The recommendation in brief

1. **The two-tape universal is not a rewrite of `Universal.lean`. It is a new row on H2.**
   H2 is `Turing.StepBlock.roundTM k`, the step block, public and proved. Each simulated step
   costs at most `50 · (|tableBitsK| + 1)`, a constant for a fixed code. So H2 gives linear
   overhead per code directly. The bespoke one-tape interpreter is hard-wired to one work tape:
   its `Fin 9` record counters and four tapes in `UniversalInterpreter`/`UniversalBlock` would
   all have to be re-proved. The approved backlog item U-1/MIG-2 already plans to retire it onto
   H2.
2. **Build one construction, generic in the work-tape count `k`.** At `k = 1` it is B6's gated
   self-application universal `U₀` and the U-1 re-derivation of `Turing.universal`. At `k = 2`
   it is U2. The pieces:
   - **H2-F**, a public host: the *emitting round loop*, stated as a `Turing.Lockstep`;
   - **U2-S**, the `k`-generic startup;
   - **U2-U**, the self-application universal, with time and space ledgers in both directions;
   - **U2-E**, the code-first evaluator, through B6's ruler host.

   The probe shows that B6's two gated statements and `Turing.universal`'s statement are
   corollaries at `k = 1`, verbatim.
3. **The hierarchy needs only U2-U at `k = 2`, through the native input device.** It needs no
   input-copy device, no clock (Hydroxyi's `clockTM` clocks *any* machine's own steps), no
   uniformity (B5a's two open contracts are irrelevant) and no output forwarding beyond a
   one-bit verdict.
4. **Parameterize `Diagonal.lean` with a two-level hypothesis:**
   - `DiagSimulator Φ`: a padded simulation of every `DTIME T` language within `A · Φ (T n) n`;
   - above it, `SelfSimulator Ψ`: a universal machine that runs codes on their own padded input
     at per-code linear cost, plus a normal form with overhead `Ψ`.

   The received theorem is the instance at `diagSim` with `Ψ = (t + 1)²`. The book's theorem is
   the instance at U2-U with the Hennie–Stearns `Ψ = (t + 1)(log₂(t + 1) + 1)`. Both are proved
   in the probe.

---

## 1. What the time hierarchy at `f log f` needs, precisely

**The chain.** Start with a language `L ∈ DTIME f`, decided by some machine `M` (any number of
work tapes) within `c₀ · f(n)`.

| Step | Object | Time | Status |
|---|---|---|---|
| G5 (Hennie–Stearns, then `Turing.FinTM.alphabet_reduction`) | a two-work-tape binary `M'` | `c₁ · (c₀ f + 1)(log₂(c₀ f + 1) + 1)` | G2–G4 at their statement gate; G5 has its own statement phase |
| constant absorption | | `≤ c₁ · K(c₀) · (f + 1)(log₂(f + 1) + 1)`, with `K(c₀) = (c₀ + 1)(log₂(c₀ + 1) + 2)` | **proved**: `logOverhead_mul_le` |
| the two-tape coding step | a `Code2TM` `N`, with identical runs | the same | **proved**: `exists_code2TM`, the mirror of `exists_codeTM` |
| the code | `α := code₂.encode N`, with `code₂.decode α = N` | — | `MachineCode2.decode_encode`; `exists_effectiveMachineCode2` is sorry-free (axiom print) |
| U2-U on the padded input `x = pairEncode α 1^m`, `|x| = n ≥ 2|α| + 2` | `W` halts with `[χ_L x]` | `≤ C_α · (t + 1)` with `t` as above, so `≤ A · ((f + n + 1)(log₂(f + n + 1) + 1))` | U2 (§2) |
| the clocked diagonal machine `D = clockTM K W` | decides `diagLangOf W g` | `≤ (c_K + 15)(g n + 1)` | **proved**: `diagLangOf_mem_DTIME`, Hydroxyi's proof with `W` as a parameter |
| contradiction | at any `n ≥ N₀` with `A · Φ(f n, n) ≤ g n` | — | **proved**: `DiagSimulator.diagLang_not_mem_DTIME` |

**The hypothesis delivered.** In the received shape the hypothesis is
`∀ A, ∃ N, ∀ n ≥ N, A · ((f n + n + 1)(log₂(f n + n + 1) + 1)) ≤ g n`, the `f log f` analogue
of the received `A · (f n + n + 1)² ≤ g n`. The book form follows under `n ≤ f n`, which every
time-constructible `f` satisfies. It reads `∀ A, eventually A · f n · log₂ f n ≤ g n`, which is
`f log f = o(g)`. The arithmetic is `(f + n + 1)(log₂(f + n + 1) + 1) ≤ 12 · f · log₂ f` for
`2 ≤ n ≤ f` (`logDiagOverhead_le_book`, proved).

**Checked against [AB09].**
- **§1.7.** The book's universal machine does the zone simulation *inside* `U`, at cost
  `O(k · Σᵢ T/2^{i-1} · 2^i) = O(T log T)` (book p. 32). Here it is split into G5, a machine
  transformation, followed by a linear universal on the two-tape code. For the hierarchy the two
  are equivalent, because the code `α` of `HS(M)` is fixed per `M`. The G2–G4 fit probe already
  checks G5's `O(k · T log T)` sum (`run_cost_le` in `G24FitProbe`).
- **Theorem 3.1's proof (p. 69).** The book bounds the simulation of a time-`c n` machine by
  `c′ c n log n`, and uses the fact that every machine has infinitely many codes. Here the code
  is fixed and the *input* is padded instead, as Hydroxyi's received design already does,
  because the universal constant depends on the code string. The clock counts `D`'s own steps
  (`clockTM`), so the code-dependent `C_α` never enters `D`'s running time. The book's
  `f(n) log f(n) = o(g(n))` becomes `A · Φ(f n, n) ≤ g n` eventually, for every `A`.
- **Deviations kept from the received theorem:** `DTIME(g + 1)` (a positive-bound form gives
  `DTIME g`), and no time-constructibility hypothesis on `f` beyond `n ≤ f n` in the book form.

**What is *not* needed.**
- No clocked or timed universal machine: `clockTM` is generic in `W`.
- No uniform scheme: per-code constants suffice. `UniformMachineCode2`, `exists_polyCanonizer`
  and `exists_uniformSimulator` (sorried) are not on this path.
- No input copy and no suffix device: self-application uses the native input.

---

## 2. The two-tape universal machine: statements, construction and registry

### 2.1 The scheme interface

A `k`-tape effective scheme `EffectiveCodeK k` (probe, §5):
- a decoding `machine α : MultiTapeTM k Bool (Fin (numStates α + 1))`;
- a canonizer computing `serializeK (machine α)` in arbitrary time.

The two received schemes are instances, `toK₁ : EffectiveMachineCode → EffectiveCodeK 1` and
`toK₂ : EffectiveMachineCode2 → EffectiveCodeK 2`; both are proved, with `toFinTM` agreeing by
`rfl`. They need the serialization bridges `CodeTM.serialize = serializeK` and
`Code2TM.serialize = serializeK`. These exist today only as **private** lemmas (`oneTape_serialize_eq` in
`CodeSimulator`, `twoTape_serialize_eq` in `Codes2Tape`). The probe re-proves them publicly from
the public `workReadsK_one`/`tableBitsK_two`. At landing, **promote the two private lemmas**
rather than adding twins.

**The code-scheme properties the diagonal argument uses:**
- (a) effective canonization, used inside U2-U's startup to decode an arbitrary input code. Its
  time `canonizerTime |α|` is a constant per code;
- (b) `decode (encode N) = N`, so every two-tape machine is reached;
- (c) totality of `decode`, implicitly: U2-U is specified on every `pairEncode α w`.

Padding (`decode_encode_pad`) and uniformity are **not** used.

### 2.2 The statements (all elaborated in the probe; sorried there)

**H2-F: the emitting round loop. A host, which is the one new host U2 introduces.** It is
H2's *unclocked* loop form: the step block plus a forwarding leaf. The leaf blanks the summary
cell, runs a round on the output-erased source, emits the round's exact emission (by
`summaryEmit_none`), and halts physically after a simulated halt. This is B6's wrapped round,
made public.

```lean
def emitLoopCfg (entry : Q) (M : MultiTapeTM k Bool (Fin (n + 1))) (c : Cfg k Bool (Fin (n + 1)) x) :
    Cfg (k + 2) Bool Q x   -- bank and input head = c's; tape k = tableBitsK M.tr; tape k+1 =
                           -- summaryCells none (unary state); aux heads 0; output = c.output;
                           -- state = entry while c is live, none once it halts
theorem StepBlock.exists_emitLoopTM (k : ℕ) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (L : MultiTapeTM (k + 2) Bool Q) (entry : Q) (C : ℕ),
      ∀ {n x} (M : MultiTapeTM k Bool (Fin (n + 1))), ∃ cost,
        Lockstep M L (emitLoopCfg entry M) cost {none} {none} ∧
        (∀ c, c.state ≠ none → 0 < cost c ∧ cost c ≤ 50 * ((tableBitsK M.tr).length + 1) + C) ∧
        (visited-set clauses: bank ⊆ source's; auxiliary tapes within ±(50·(|table|+1) + C))
```

The contract library's `Turing.Lockstep` already provides `runFrom`, the sum of the step costs,
and `cut`, no early halt. So the time and the converse come for free.

Notes on H2-F:
- **It discharges the H2 gate's consumer obligation CO-RF once**, for B6's `U₀`, U2, U-1 and
  the addend-free `space_universal`.
- **Fill proof.** Each live step is `roundTM_effect`, with its exact time by
  `roundTM_firstExit_unique`, plus the leaf; the space clauses follow from `roundTM_visited`.
- **Why the step block alone is not enough.** `roundTM k` already iterates by itself: its
  `exit k true` is its own `entry`, and `roundTM_iterate` gives the unclocked iteration. What
  it lacks is emission and a physical halt.

**U2-S: the `k`-generic startup.** This is B6's `exists_selfStartupTM` with tapes
`0, …, k − 1` mirrored, the table on tape `k`, and the unary state from cell 2 of tape `k + 1`,
on `K + (k + 2)` tapes. The probe derives B6's gated statement, verbatim, at `k = 1`, so B6's
statement is kept and gets a one-line proof.

**U2-U: the self-application universal, with time and space ledgers in both directions.**

```lean
theorem exists_selfUniversalK (k : ℕ) (E : EffectiveCodeK k) :
    ∃ U : FinTM Bool, ∀ α, ∃ C, 0 < C ∧ ∀ w,
      (∀ output t, (E.toFinTM α).ComputesInTime (pairEncode α w) output t →
        U.ComputesInTime (pairEncode α w) output (C * (t + 1)) ∧
        U.tm.spaceUsed (U.tm.initCfg (pairEncode α w)) (C * (t + 1)) ≤
          C * ((E.toFinTM α).tm.spaceUsed ((E.toFinTM α).tm.initCfg (pairEncode α w)) t + 1)) ∧
      ∀ output, (∃ t', U.ComputesInTime (pairEncode α w) output t') →
        ∃ t, (E.toFinTM α).ComputesInTime (pairEncode α w) output t
```

**What depends on the code:** `C` collects
- the startup time and space `T_α`, `B_α`, which contain `canonizerTime |α|`, arbitrary for an
  arbitrary scheme (the received Argument E);
- the per-step bound `50 · (|tableBitsK (machine α).tr| + 1) + C_leaf`.

**What depends on `k` only:** the step block's control and the coefficient 50. Nothing depends
on `w`, on `t`, or on the tape contents. The probe derives B6's gated
`Turing.exists_selfUniversal` from U2-U at `k = 1`, verbatim (time clause dropped, space clause
weakened).

**Construction.** U2-S, then a seam into H2-F, then `Lockstep.runFrom`. The total time is
`T_α + Σ cost ≤ T_α + (50 · (|table| + 1) + C) · t ≤ C_α · (t + 1)`.

**U2-E: the code-first evaluator (Theorem 1.9's core).** It has `Turing.universal`'s shape for
`EffectiveCodeK k`, with `C · (t + 1)` and no `|x|` term. At `k = 1` it is
`Turing.universal`'s statement verbatim (probe), which is U-1. The construction:
- a code-first startup that writes the unary ruler `true^ℓ`, with `ℓ = 2|α| + 2`, while it
  scans the header, then canonizes;
- B6's `exists_rulerHostTM` (sorried, gated, landed) around H2-F's machine.

That costs `≤ C · (ℓ + 1)` per H2-F step, still a constant per code. The buffered device
(`hostedLoopTM`, Z1) is **not** suitable here: copying `x` costs `Θ(|x|)` steps, which breaks the
no-`|x|` bound that Theorem 1.9 states.

**Not proposed: U2-V.** The probe states a verdict-only self-simulator (U2-V) as the *minimal*
hypothesis the hierarchy needs. The probe's `twoTapeSelfSimulator` is built from it, to show
that nothing more is needed. U2-U implies the one-bit form the diagonal argument uses, so
**U2-V is not proposed for landing** (decision Q4).

### 2.3 Rewrite or new row: the cost comparison

| | Bespoke `Universal.lean` interpreter | H2-based (proposed) |
|---|---|---|
| Per simulated step | `universalBlockBound c α` (table scans) | `≤ 50 · (|tableBitsK| + 1)` (`roundTM_effect`, proved) + an `O(1)` leaf |
| Work tapes of the simulated machine | 1 (hard-wired: `Fin 9` record indices, 4 tapes) | any `k` (`roundTM k`) |
| Proof effort for `k = 2` | re-prove the interpreter trace (`UniversalInterpreter` 1,027 lines + `UniversalBlock` 794 + `Universal` 2,884 lines, MEASURED) at 27 records per state | none for the step: H2 is proved; new work is the leaf/loop, the startup and the ledgers |
| Space | marker tape `Θ(|x|)` (Finding B) | native: exactly the source's cells plus `O_α(1)`; ruler: `+ ℓ + 2` |
| Reuse | none | B6's `U₀`, U-1, `space_universal`, U2 |

Both are linear per code. The H2 route is the only one that does not re-prove an interpreter.
The "retrofit pilot" role of plan §4b item 2 passes to U-1, which becomes the `k = 1` instance
(U2-E) plus the deletion of the bespoke layers.

### 2.4 StepBlockLoop (#94): where it fits

`Turing.StepBlock.loopTM` and `hostedLoopTM` (proved, axiom prints in `U2DeclCheck.out`) are
the **clocked** loop forms: a binary counter of deadline `t`, the exits `done`/`escape`, and the
early-escape bound `t′ · B + 4t′ + 2|w|`. The hierarchy's `W` must be **unclocked**, because
`clockTM` supplies the clock. Simulating inside `W` against a deadline would require `W` to know
`g(n)`, and the clock would then count simulated steps, which Hydroxyi's design note rules out:
`C_α` is unbounded over codes. So `loopTM` is **not** on the hierarchy's path.

`loopTM` is the right host for a *clocked* two-tape universal (the book's "universal TM with
time bound", §1.4.1). Its bound `C_α · (t + 1) + 2|bits t|` would improve `timed_universal`'s
`(t + 1)²`. That belongs to U-1/MIG-2, under the TMSAT constraint that
`timed_universal_concrete`'s coefficient must not grow. It is recorded there, not built here.

### 2.5 Registry (§14)

- **H2-F is a host.** It is H2's second loop form, beside the counter loop, with named consumers
  B6's `U₀`, U2-U, U2-E/U-1 and the addend-free `space_universal`. Proposed home:
  `Build/StepBlockLoop.lean`, namespace `Turing.StepBlock`.
- **U2-S, U2-U and U2-E are consumer rows, not hosts.** This follows B6's classification of
  `U₀` as "a public row built from H2's step block and H5's native device". Proposed home: a
  new `TuringMachine/UniversalK.lean` with `EffectiveCodeK` and the instances, imported by
  `SelfUniversal.lean`, whose two statements then get proofs as `k = 1` instances.
- **`exists_code2TM`** goes into `Codes2Tape.lean` (additive).

### 2.6 What B5a contributes

- **H2**: proved and promoted (H2-M). This is all the hierarchy uses from B5a.
- **The uniform layer**: not needed. The two-tape *effective* scheme
  (`exists_effectiveMachineCode2`) is proved and sorry-free (MEASURED, axiom print). The uniform
  scheme (`exists_uniformMachineCode2`) carries `sorryAx` through `exists_polyCanonizer` and
  `exists_uniformSimulator`. It serves variable-code consumers (EXPCOM) only.

---

## 3. The parameterization of `Diagonal.lean`

The full text is in `probes/U2DiagParam.lean` §1–4, all proved. The proposed declarations, in
namespace `Complexity.TimeHierarchy`:

```lean
def diagLangOf (W : FinTM Bool) (g : ℕ → ℕ) : Language Bool :=
  {x | ¬W.ComputesInTime x [true] (g x.length)}
theorem diagLangOf_mem_DTIME (W) (hg : TimeConstructible g) : diagLangOf W g ∈ DTIME (g · + 1)

structure DiagSimulator (Φ : ℕ → ℕ → ℕ) where
  W : FinTM Bool
  simulates : ∀ T (L : Language Bool), L ∈ DTIME T → ∃ A N₀, ∀ n ≥ N₀, ∃ x, x.length = n ∧
    W.ComputesInTime x [MultiTapeTM.indicator (L : Set (List Bool)) x] (A * Φ (T n) n)
def DiagSimulator.mono (S) (K) (h : ∀ t n, Φ t n ≤ K * Φ' t n) : DiagSimulator Φ'
theorem DiagSimulator.diagLang_not_mem_DTIME (S) (hT : ∀ A N, ∃ n ≥ N, A * Φ (T n) n ≤ g n) :
  diagLangOf S.W g ∉ DTIME T
theorem DiagSimulator.time_hierarchy (S) (hΦ : ∀ t n, t ≤ Φ t n) (hg) (hfg : ∀ A, ∃ N, ∀ n ≥ N, A * Φ (f n) n ≤ g n) :
  DTIME f ⊂ DTIME (g · + 1)
theorem DiagSimulator.time_hierarchy_of_pos ...      -- the same with DTIME g for positive g

structure SelfSimulator (Ψ : ℕ → ℕ) where            -- the universal-machine-level hypothesis
  W : FinTM Bool
  decode : List Bool → FinTM Bool
  simulates : ∀ α, ∃ C, ∀ w (b : Bool) t, (decode α).ComputesInTime (pairEncode α w) [b] t →
    W.ComputesInTime (pairEncode α w) [b] (C * (t + (pairEncode α w).length + 1))
  normalForm : ∀ T L, L ∈ DTIME T → ∃ α c, ∀ x,
    (decode α).ComputesInTime x [indicator L x] (c * (Ψ (T x.length) + 1))
def SelfSimulator.toDiagSimulator (S : SelfSimulator Ψ) : DiagSimulator (fun t n => Ψ t + n + 1)
```

**What the hypothesis says.** The universal machine needs only this: one machine, *unclocked*,
that on `pairEncode α w` reproduces the one-bit verdict of the machine coded by `α`, run on that
same input, within `C_α · (t + |input| + 1)`. There is no clocked form, no uniformity, and no
dependence of `C` on anything but the code. The `+ |input|` slack admits the received
`diagSim`, whose `preTM` costs `O(n)`.

### 3.1 The received `f²` theorem as an instance

- `oneTapeSelfSimulator : SelfSimulator (fun t => (t + 1)²)` has `W := diagSim` and
  `decode α := (code.decode α).toFinTM`.
  - Simulation: `univTM_spec`, `preTM_computes`, `scanPre_pairEncode_append` and
    `bufferedCompTM_computesInTime`, with constant `C + 7`.
  - Normal form: `one_work_tape_binary` with `exists_codeTM`.
- `sqDiagSimulator : DiagSimulator (fun t n => (t + n + 1)²)` is
  `oneTapeSelfSimulator.toDiagSimulator.mono 2`. Its `W` is `diagSim` by `rfl`
  (`sqDiagSimulator_W`).

### 3.2 The `f log f` instance

- `twoTapeSelfSimulator : SelfSimulator logOverhead`, with
  `logOverhead t := (t + 1)(Nat.log 2 (t + 1) + 1)`, has `W := U2-U at k = 2 over code₂`, with
  `code₂ := Classical.choice exists_effectiveMachineCode2` (the `TimeHierarchy.code` pattern).
  - Normal form: G5 with `exists_code2TM` and `logOverhead_mul_le`.
- Then:
  - `time_hierarchy_log`: the hypothesis on `(f n + n + 1)(log₂(f n + n + 1) + 1)`;
  - `time_hierarchy_book`: `n ≤ f n` and `f log f = o(g)`;
  - the illustration `DTIME(n + 1) ⊊ DTIME((n + 1)²)`, below the received quadratic threshold,
    using `timeConstructible_poly 1 1`.

### 3.3 Edits to `Diagonal.lean`

Each edit is statement-preserving. The user authorized this file only (2026-10-14).

1. **Add** `diagLangOf`, `diagLang_eq_diagLangOf` (`rfl`), `diagLangOf_mem_DTIME`, the two
   structures, `mono`, `toDiagSimulator`, the three generic theorems, `le_sq_overhead`,
   `oneTapeSelfSimulator` and `sqDiagSimulator`.
2. **Keep verbatim** `code`, `univTM`, `univTM_spec`, `diagSim`, `diag_cost_le` (unused after
   the edit, but public) and **the definition of `diagLang`**. `diagLang`'s body is unchanged;
   `diagLangOf` sits beside it, so no consumer's unfolding is affected.
3. **Re-prove, statements verbatim**, as one-line instances. The argument then exists once (no
   copied argument):
   - `diagLang_mem_DTIME := diagLangOf_mem_DTIME diagSim hg`;
   - `diagLang_not_mem_DTIME := sqDiagSimulator.diagLang_not_mem_DTIME hT`;
   - `time_hierarchy := sqDiagSimulator.time_hierarchy le_sq_overhead hg hfg`;
   - `time_hierarchy_of_pos := sqDiagSimulator.time_hierarchy_of_pos le_sq_overhead hg hpos hfg`.

   The probe's §3 `example`s have the tip's `#check` types copied verbatim and elaborate.
4. **At the end of the chain**, add the `f log f` layer:
   - `logOverhead`, `logDiagOverhead`, `logOverhead_mul_le`, `logDiagOverhead_le_book`,
     `code₂`, `twoTapeSelfSimulator`, `time_hierarchy_log`, `time_hierarchy_book`, and the
     illustration;
   - imports: `Mathlib.Data.Nat.Log`, the U2 module, G5's module, and `ClassNP/TMSAT` for
     `timeConstructible_poly`.

   **One proof must change from the probe.** The illustration's log lemma cannot cite
   `Separation`'s `eventually_poly_le_two_pow`: `Separation` imports `Diagonal`, and
   `Separation.lean` is not covered by the authorization. It needs a self-contained lemma of
   about 20 lines (ESTIMATE).
5. **The module docstring's "Divergences" section** is rewritten, because the overhead is now a
   parameter.

**Consumers at the tip** (MEASURED by `git grep` over `TCSlib/*.lean`):

| Consumer | Uses | Effect |
|---|---|---|
| `TimeHierarchy/Separation.lean` | `diagLang`, `diagLang_mem_DTIME`, `diagLang_not_mem_DTIME`, `time_hierarchy_of_pos` | statements and `diagLang`'s body unchanged; no edit |
| `SpaceComplexity/Hierarchy.lean` (`space_universal`) | `TimeHierarchy.code` | unchanged |
| `Diagonalization/NotTimeConstructible.lean` | `TimeHierarchy.code` | unchanged |
| `Diagonalization/EXPCOM.lean` | the import; prose only | unchanged |
| `SelfUniversal.lean`, `NTimeHierarchy.lean` | prose only | unchanged |
| facade `TimeHierarchy.lean` | docstring: "quadratic overhead in place of the book's `f log f`" | stale after step 4; a one-sentence docstring edit, which is **outside the authorization** (Q8) |

**Replay.** The five importers and their downstream. If step 4 adds imports, every importer's
closure grows by the U2 and G5 modules. There is no cycle: nothing in those modules imports
`Diagonal`, and this is to be re-checked by the import graph at landing.

---

## 4. Theorem 1.9 at book strength

Beyond §1–§3, Theorem 1.9 needs the following.

1. **U2-E**, the code-first evaluator (§2.2). Its fill needs B6's ruler host
   (`exists_rulerHostTM`), whose fill is B6's.
2. **G5 per run, with the converse**:
   `two_work_tapes_run M : ∃ M' c, M'.k = 2 ∧ (∀ x out t, M.ComputesInTime x out t →
   M'.ComputesInTime x out (c · (t + 1)(log₂(t + 1) + 1))) ∧ (completed outputs of M' are M's)`.
   The function-level form the hierarchy uses, `two_work_tapes_binary`, follows in two lines
   (proved in the probe). A per-run G5 needs a per-run alphabet reduction:
   `alphabet_reduction` is stated only at the function level, but its private `arTM_computes` is
   per run. That calls for an additive public export in `Robustness/AlphabetReduction.lean`,
   20–40 lines (ESTIMATE).
3. **The assembly `universal_TlogT`** (proved in the probe, modulo the two inputs). One machine
   `U`, such that every binary machine `M` has a code `α`, has two properties:
   - each halting run of `M` of `t` steps is reproduced on `pairEncode α x` within
     `C · (t + 1)(log₂(t + 1) + 1)`;
   - every completed output of `U` is one of `M`'s.

**Deviation.** As in `universal_quadratic`, the code is that of a normal-formed equivalent of
`M` ("∀ M, ∃ α"), not a description of `M` itself. The literal form, where `α` describes any
`k`-tape `M`, would need two things: a variable-`k` code scheme, and either an effective
Hennie–Stearns *compiler on serializations* or an on-the-fly multi-track interpreter. Neither
has a consumer. Not recommended (Q11).

---

## 5. Space: Exercise 4.1 and Theorem 4.8

**Carrying space through the two-tape universal adds nothing for Theorem 4.8.**
- The space hierarchy needs only a space-faithful normal form. One work tape already gives
  constant-factor space: `one_work_tape_binary_spaceUsed` and `alphabet_reduction_spaceUsed`
  are both proved, so the Z4 annotation is in effect landed.
- B6's route (`U₀` at `k = 1` with the native device for `space_hierarchy`, and `U₀` with the
  ruler for the addend-free `space_universal`) is Exercise 4.1.

**The recommendation is to pursue no separate space route, and instead to make the space ledger
part of the generic construction.** U2-U carries `C · (s + 1)` from H2's `roundTM_visited`
through H2-F's visited clauses. Its `k = 1` instance *is* `U₀` (the probe derives B6's statement
from it). So B6's fill and U2 become one proof, with no second universal machine.

This settles the open item §13 Z4's design-time obligation left (stated again in A-S2-5's note):
"does the two-tape universal yield Ex 4.1?" Yes, as the `k = 1` instance of the same
construction, through the native or ruler device, never an input copy.

---

## 6. Work breakdown, gates, dependencies

Every row below is an ESTIMATE of lines landed unless marked MEASURED.

| # | Item | Size | Depends on | Gate |
|---|---|---|---|---|
| 1 | **U2 statement unit**: `EffectiveCodeK`, `toK₁`/`toK₂`, the two serialization bridges (promoted), `exists_code2TM` (proved), H2-F with `emitLoopCfg`, U2-S, U2-U, U2-E (sorried with sketches), B6's two statements and `Turing.universal`'s statement re-derived as `k = 1` corollaries (proved, modulo) | 350–450 (the probe's §5 core is about 310 lines, MEASURED) | H2 (landed), B6 hosts (landed), the effective two-tape scheme (proved) | **U2-S statement gate**, then a landing PR the user merges |
| 2 | Fill H2-F (`exists_emitLoopTM`) | 600–1,100 | 1 | fill gate (with 3–4) |
| 3 | Fill U2-S (`exists_selfStartupTMK`) | 500–1,000 (B6's estimate for `k = 1`; the generic indices add little) | 1 | fill gate |
| 4 | Fill U2-U from 2 + 3; B6's `U₀` statements as corollaries | 250–500, plus 30–60 | 2, 3 | fill gate |
| 5 | Fill U2-E: the code-first startup plus the ruler host around H2-F | 500–1,000 | 2, 3, B6's ruler-host fill (400–800, B6's) | separate fill gate (Theorem 1.9 only) |
| 6 | G5 (§13d process rule: PR + gate) — interface only, owned by the G5 statement phase: `two_work_tapes_run` with its converse, `two_work_tapes_binary`, `Nat.log 2`, and the per-run `alphabet_reduction` export (20–40) | not U2's | G2–G4 fills | G5 statement gate, fill gate |
| 7 | **`Diagonal.lean`** — part 1 (generic layer, `f²` instance, one-line re-proofs) | +120 to +170 net (313 → about 450; MEASURED probe §1–3: 233 lines) | nothing | **one gate and one PR, at the end of the chain** (user, 2026-10-14) |
| 7 | **`Diagonal.lean`** — part 2 (`f log f` layer, book form, illustration) | +150 to +220 (the probe's §4 plus the absorption and the instance: about 160, MEASURED; plus the self-contained log lemma) | 4, 6 | same PR as part 1 |
| 8 | `universal_TlogT` (Theorem 1.9 at `T log T`) | 40–60 (proved in the probe, modulo 5 and 6) | 5, 6 | with 5 or 6 |

**Totals (ESTIMATE).**
- U2 proper (items 1–5, 8): about 2.3k–4.2k lines.
- The hierarchy alone (items 1–4 and 7): about 1.8k–3.3k lines.

**Order.** Items 1–4 are independent of G2–G5 and can run in parallel with them, off the
critical path. The critical path for Theorem 3.1 at `f log f` is G2–G4 fills → G5 statements →
G5 fill → item 7.

B6's `U₀` fill should be **briefed against items 2–4** (generic in `k`), not as a separate
`k = 1` construction. That requires gate 1 before B6's fill brief (Q2).

**Dependency on B5a:** H2 only (done). **On G2–G5:** only through the normal form in item 7,
part 2, and in item 8.

---

## 7. The probe's six sorries (all deliberate)

| Line | Declaration | Owner |
|---|---|---|
| 463 | `two_work_tapes_run` | G5's statement phase |
| 502 | `StepBlock.exists_emitLoopTM` (H2-F) | U2 |
| 532 | `exists_selfVerdictTMK` (U2-V; the minimal hypothesis, not proposed for landing) | — |
| 543 | `exists_selfStartupTMK` (U2-S) | U2 |
| 600 | `exists_selfUniversalK` (U2-U) | U2 |
| 631 | `universalK` (U2-E) | U2 |

Proved and standard-axiom (axiom prints in `U2DiagParam.out`):
- the whole `Diagonal.lean` parameterization, including the `f²` instance and the `f log f`
  layer from its hypothesis;
- `toK₂`, `exists_code2TM` and `logOverhead_mul_le`.

`twoTapeSelfSimulator`, `time_hierarchy_book` at it, the illustration and `universal_TlogT`
carry `sorryAx` only through the rows above.

---

## 8. Open questions for the user (recommendations in italics)

1. **Q1. The hierarchy's simulator.** Self-application U2-U through the native device, or the
   code-first U2-E plus `preTM`, which mirrors `diagSim`. *Self-application: no suffix device on
   the critical path.*
2. **Q2. Generalize B6's `U₀` and its startup to `k` before B6's `U₀` fill is briefed.** B6's
   two gated statements stay verbatim as `k = 1` corollaries (shown in the probe). *Yes: one
   construction, hosts-first.*
3. **Q3. H2-F as a public host in `Build/StepBlockLoop`, stated as a `Turing.Lockstep`.** *Yes:
   it discharges CO-RF once for four consumers.*
4. **Q4. A separate verdict-only U2-V.** *No: U2-U suffices, since the diagonal argument uses
   only one-bit verdicts.*
5. **Q5. G5's form.** Per run with the converse, plus the function-level corollary and an
   additive per-run alphabet-reduction export; or function-level only. *Per run: Theorem 1.9's
   per-input form needs it, and the construction is per run anyway.* To be forwarded to the G5
   statement phase.
6. **Q6. The logarithm.** *`Nat.log 2` in every public statement. `Nat.log2_eq_log_two` bridges
   `Build/Zone`'s `Nat.log2`; the lemma is confirmed present.*
7. **Q7. The hypothesis of the new theorems.** *State both: the general
   `(f n + n + 1)(log₂(f n + n + 1) + 1)` form, parallel to the received one, and the book form
   under the weakest condition `∀ n, n ≤ f n`, rather than `TimeConstructible f`.*
8. **Q8. The home of the book-strength corollaries.**
   - *Recommended: the end of `Diagonal.lean`*, per "no new file". Its imports then grow by the
     U2 and G5 modules and `ClassNP/TMSAT`, and its five importers inherit them.
   - The alternative is a new campaign file, which keeps `Diagonal`'s closure light but needs
     the user's OK.
   - Either way, the facade `TimeHierarchy.lean`'s stale docstring sentence needs a mechanical
     one-sentence edit. It is outside the `Diagonal.lean`-only authorization: *ask the user*.
9. **Q9. When part 1 of the `Diagonal.lean` edit lands.** *At the end of the chain, as decided.*
   Part 1 is independent and fully proved, so it could land early if the user prefers.
10. **Q10. The illustration.** *`DTIME(n + 1) ⊊ DTIME((n + 1)²)`, which is cheap and existing.
    The book's `n^1.5` needs a new time-constructibility witness for `n · ⌊√n⌋`; put it in the
    backlog.*
11. **Q11. Theorem 1.9's code quantifier.** *Relaxed, "∀ M, ∃ α", as `universal_quadratic`
    already is.* The literal form needs a variable-`k` scheme and an effective Hennie–Stearns
    compiler, with no consumer.
12. **Q12. The home of `universal_TlogT`.** *G5's module*, since [AB09] §1.7 is titled
    "Proof of Theorem 1.9". Alternatively a small sibling module, if G5 should stay a pure
    conversion.
13. **Q13. U2-E.** *State it at gate 1 and fill it after B6's ruler-host fill.* Only
    Theorem 1.9 and U-1 need it.
14. **Q14. The serialization bridges.** *Promote the two private lemmas instead of adding
    public twins.* The one in `CodeSimulator` sits in a region of the B5a continuation; schedule
    the promotion in a B5a window.
