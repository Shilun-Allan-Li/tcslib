# §12.8 fill, stream D — R8.0b: generalize `counterLoopTM`'s machinery in place (`counterLoopTMVia`), and R8.6


## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor 182e6f44c5135f07cb4965a42fc6865da720d553 HEAD` succeeds.
  That commit contains the §12.8 statement layer and its closed gate (PR #28,
  `audits/s12-8-statements-{findings,r2-findings,resolutions}.md`), the Catalog
  trace promotion (PR #32), the shared pre-issue layer (`5afed90b`: the overlay transport
  in `SymbolLift`, `counter_cfg_eq` made public) and this brief's order list. If the check
  fails, **stop**.
- Create your working branch off the campaign branch (suggested `fill/s128-D`). Record the
  base hash in `REPORT.md`. Never rebase.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-s128-D.zip`, containing
  `REPORT.md`, the full modified `Build/CounterLoop.lean`, a `git format-patch` series
  against your base, a git bundle, the final sweep log, the axiom logs (base and after), the
  evidence files listed under "Evidence for the R8.0b gate", and `SHA256SUMS`.
- Integration note, no action for you: this batch changes audited public signatures, so,
  under the §13d process rule, the maintainer integrates on a side branch, opens a PR, and
  runs a **separate R8.0b audit gate** before the user merges.

## What this is

Design `machine-library-design.md` §12.8a §1 "R8.0b" and §8 "R8.0b target signatures",
under the user's decision **O2**. `counterLoopTM` (§12.7) runs only `Bool` bodies, and
every rich-alphabet consumer of §12.8 (S1b's round, Savitch's frame step, the record rows)
needs a counter loop with a **rich body**. You build it **in place**:

1. generalize `counterLoopCfg`, `counterLoopOrbit` and `counterLoop_time_le` to any symbol
   type (types only; bodies verbatim; every call site unchanged);
2. add `lastEmb`, `counterLoopTMVia` and its two contracts
   `counterLoopTMVia_run_done`/`_escape`, proved by **the existing round induction,
   generalized in place**;
3. re-derive the landed `counterLoopTM_run_done`/`_escape` (statements byte-identical) from
   the generic contracts at `e := Function.Embedding.refl Bool` through Z5,
   `MultiTapeTM.runFrom_eq_of_agreeOn`. There is **one** round induction. There is no second
   host with its own induction;
4. fill R8.6, `expandTM_run_ofCfg` (§12.8 gate: round-1 note 25, round-2 note 26),
   proved modulo Scan's sorried `writeAdvTM_run_ofCfg`.

**No new trace.** The decrement is the landed `decrementTM`, run through R1 and the
symbol lift; its framed contracts are cited, never re-traced.

**Pre-ship check (maintainer, executed):** `audits/evidence/s12-8/R80bPreShip.lean.txt`
(output `.out`). Against the round-2 olean tree it gave **0 errors and exactly 2 `sorry`
warnings**, both on the two generic contracts. Its pre-issue-2 variant cites the landed
overlay layer and adds the generic layout (Part 3(h)). Against the pre-issue-2 tree it
gives the same result: 0 errors and the same two warnings. It contains:

- **Part 1:** the three generalized declarations as probe-local copies, with `rfl` and
  instance checks against the landed `Bool` ones, including the landed `expandTM_run_ofCfg`
  statement restated over the generalized configuration;
- **Part 2:** the exact text of the four new declarations;
- **Part 3:** your route, proved piece by piece: (a) the decrement table is
  input-oblivious and writes no blank; (b) its lift at `refl` is the same table; (c) R1's
  action at `lastEmb k` from Embed's public surface; (d) the dec-table agreement and the
  whole-host `AgreeOn … Set.univ`; (e) **both landed `Bool` contracts, statements copied
  verbatim, re-derived from the generic ones by Z5**; (f) the frame-respecting lift: its
  step, run, shadow and decoding lemmas (landed in `SymbolLift` at `5afed90b`; the variant
  applies them to `decrementTM 1 0` from an arbitrary rich start); (g) the dec-phase
  configuration as an R1 configuration at `lastEmb k`; (h) the generic host layout, with the
  public `Bool` `counter_cfg_eq`, statement verbatim, as its instance;
- **Part 4:** `decide` runs of `counterLoopTMVia` over `Fin 3`, with foreign symbols in
  the input, on the body tape and in the counter tape's frame: the returning case at value 2
  with a leading-zero counter (exact time 16), escape (time 5), `k = 0`, `w = [false]` and
  `w = []`.

## Owned file and the freeze (modify this file and nothing else)

`TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean` (1279 lines at `5afed90b`).

| Class | Declarations (base line) |
|---|---|
| **Frozen: statement and body byte-identical** | `Action.mapWorkSymbols` 114, `Cfg.mapWorkSymbols` 123, `MultiTapeTM.mapWorkSymbols` 130, `MultiTapeTM.mapWorkSymbols_runFrom` 173, `decFixed` 189, `decrementTM` 225, `decrementTM_run_succ_ofCfg` 252, `decrementTM_run_underflow_ofCfg` 308, `counterWord` 355, `counterOverhead` 366, `counterWord_length` 419, `counterWord_value` 439, `counterOverhead_le_of_le` 501, `counterOverhead_le` 531, `CounterLoopState` 546 (with its `deriving`), `counterLoopStateFintype` 557, `counterLoopRedirect` 563, `counterLoopDecExit` 570, `counterLoopTM` 583, `expandTM` 1221 |
| **Frozen statement, sanctioned body swap** | `counter_cfg_eq` 626: public since `5afed90b`, it stays `Bool`-typed over the generalized `counterLoopCfg`. **Authorized body swap of a frozen public** (maintainer-confirmed): its statement stays byte-identical and its body becomes the instance `counter_layout q c ct cp` (route 2); `counterLoopTM_run_done` 1048, `counterLoopTM_run_escape` 1141 (the Z5 re-derivation, route 3); `expandTM_run_ofCfg` 1242 (`sorry` to proof, route 4) |
| **Type-only generalization, body verbatim** | `counterLoopCfg` 600, `counterLoopOrbit` 609, `counterLoop_time_le` 1197 |
| **New public** | `lastEmb`, `counterLoopTMVia` (directly after `counterLoopTM`, since the generalized privates use them); `counterLoopTMVia_run_done`, `counterLoopTMVia_run_escape` (directly before `counterLoopTM_run_done`, after `counter_rounds`). The ordered declaration sequence is otherwise unchanged |

### Exact statements (binding; probe Part 1–2 with the landed names)

```lean
def counterLoopCfg {k : ℕ} {Symbol S : Type} {x : List Symbol}
    (q : Option (CounterLoopState S)) (c : Cfg k Symbol S x)
    (ct : ℤ → Option Symbol) (cp : ℤ) : Cfg (k + 1) Symbol (CounterLoopState S) x :=
  { (embedEmitCfg Fin.castSuccEmb (fun _ => ct) (fun _ => cp) [] c).mapState
      CounterLoopState.body with state := q }

def counterLoopOrbit {k : ℕ} {Symbol S : Type} {x : List Symbol} (M : MultiTapeTM k Symbol S)
    (τ : Cfg k Symbol S x → ℕ) (c : Cfg k Symbol S x) (r : ℕ) : Cfg k Symbol S x :=
  (fun c => M.runFrom c (τ c))^[r] c

theorem counterLoop_time_le {k : ℕ} {Symbol S : Type} {x : List Symbol}
    (M : MultiTapeTM k Symbol S) (τ : Cfg k Symbol S x → ℕ) (c : Cfg k Symbol S x)
    (w : List Bool) (d : ℕ) (hd : Nat.ofDigits 2 (w.map Bool.toNat) = d) (B : ℕ)
    (hB : ∀ r < d, τ (counterLoopOrbit M τ c r) ≤ B) :
    ∑ r ∈ Finset.range d, τ (counterLoopOrbit M τ c r) + counterOverhead w (d + 1) ≤
      d * B + 4 * d + 2 * w.length + 2

def lastEmb (k : ℕ) : Fin 1 ↪ Fin (k + 1) :=
  ⟨fun _ => Fin.last k, fun a b _ => Subsingleton.elim a b⟩

def counterLoopTMVia {k : ℕ} {Γ S : Type} [DecidableEq S] [DecidableEq Γ] (e : Bool ↪ Γ)
    (M : MultiTapeTM k Γ S) (a : S) (exit : Option S) :
    MultiTapeTM (k + 1) Γ (CounterLoopState S) where
  q₀ := .dec .run
  tr := fun q inp work =>
    match q with
    | .body s =>
      ((embedEmitTM Fin.castSuccEmb M).tr s inp work).mapState (counterLoopRedirect a exit)
    | .dec f =>
      ((embedEmitTM (lastEmb k) ((decrementTM 1 0).liftSymbols e)).tr f inp work).mapState
        (counterLoopDecExit a)
    | .done => ⟨0, fun _ => (none, 0), none, some .done⟩
    | .escape => ⟨0, fun _ => (none, 0), none, some .escape⟩

theorem counterLoopTMVia_run_done {k : ℕ} {Γ S : Type} [DecidableEq S] [DecidableEq Γ]
    {x : List Γ} (e : Bool ↪ Γ)
    (M : MultiTapeTM k Γ S) (a : S) (exit : Option S)
    (τ : Cfg k Γ S x → ℕ) (c : Cfg k Γ S x)
    (w : List Bool) (ct : ℤ → Option Γ) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape (w.map e) p)
    (d : ℕ) (hd : Nat.ofDigits 2 (w.map Bool.toNat) = d)
    (hround : ∀ r < d,
      (counterLoopOrbit M τ c r).state = some a ∧
      0 < τ (counterLoopOrbit M τ c r) ∧
      (∀ u, 0 < u → u < τ (counterLoopOrbit M τ c r) →
        ∃ s, (M.runFrom (counterLoopOrbit M τ c r) u).state = some s ∧
          s ≠ a ∧ exit ≠ some s) ∧
      (counterLoopOrbit M τ c (r + 1)).state = some a)
    (T : ℕ)
    (hT : T = ∑ r ∈ Finset.range d, τ (counterLoopOrbit M τ c r) +
      counterOverhead w (d + 1)) :
    (counterLoopTMVia e M a exit).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) T =
        counterLoopCfg (some .done) (counterLoopOrbit M τ c d)
          (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ) then some (e true) else ct q) cp ∧
      (∀ t < T,
        ((counterLoopTMVia e M a exit).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠ some .done ∧
        ((counterLoopTMVia e M a exit).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠ some .escape) ∧
      (∀ t ≤ T,
        ((counterLoopTMVia e M a exit).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos (Fin.last k) ∈
          Finset.Icc (cp - 1) (cp + (w.length : ℤ))) ∧
      (∀ t ≤ T, ∃ r u,
        ((r < d ∧ u ≤ τ (counterLoopOrbit M τ c r)) ∨ (r = d ∧ u = 0)) ∧
        ∀ j : Fin k,
          ((counterLoopTMVia e M a exit).runFrom
              (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos j.castSucc =
            (M.runFrom (counterLoopOrbit M τ c r) u).workTapePos j)

theorem counterLoopTMVia_run_escape {k : ℕ} {Γ S : Type} [DecidableEq S] [DecidableEq Γ]
    {x : List Γ} (e : Bool ↪ Γ)
    (M : MultiTapeTM k Γ S) (a ex : S) (hea : ex ≠ a)
    (τ : Cfg k Γ S x → ℕ) (c : Cfg k Γ S x)
    (w : List Bool) (ct : ℤ → Option Γ) (cp : ℤ)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape (w.map e) p)
    (r₀ : ℕ) (hr₀ : r₀ < Nat.ofDigits 2 (w.map Bool.toNat))
    (hround : ∀ r ≤ r₀,
      (counterLoopOrbit M τ c r).state = some a ∧
      0 < τ (counterLoopOrbit M τ c r) ∧
      (∀ u, 0 < u → u < τ (counterLoopOrbit M τ c r) →
        ∃ s, (M.runFrom (counterLoopOrbit M τ c r) u).state = some s ∧ s ≠ a ∧ s ≠ ex))
    (hexit : (counterLoopOrbit M τ c (r₀ + 1)).state = some ex)
    (T : ℕ)
    (hT : T = ∑ r ∈ Finset.range (r₀ + 1), τ (counterLoopOrbit M τ c r) +
      counterOverhead w (r₀ + 1)) :
    (counterLoopTMVia e M a (some ex)).runFrom (counterLoopCfg (some (.dec .run)) c ct cp) T =
        counterLoopCfg (some .escape) (counterLoopOrbit M τ c (r₀ + 1))
          (fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ)
            then FinTM.bufferTape ((counterWord w (r₀ + 1)).map e) (q - cp) else ct q) cp ∧
      (∀ t < T,
        ((counterLoopTMVia e M a (some ex)).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠ some .done ∧
        ((counterLoopTMVia e M a (some ex)).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).state ≠ some .escape) ∧
      (∀ t ≤ T,
        ((counterLoopTMVia e M a (some ex)).runFrom
            (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos (Fin.last k) ∈
          Finset.Icc (cp - 1) (cp + (w.length : ℤ))) ∧
      (∀ t ≤ T, ∃ r u,
        ((r ≤ r₀ ∧ u ≤ τ (counterLoopOrbit M τ c r)) ∨ (r = r₀ + 1 ∧ u = 0)) ∧
        ∀ j : Fin k,
          ((counterLoopTMVia e M a (some ex)).runFrom
              (counterLoopCfg (some (.dec .run)) c ct cp) t).workTapePos j.castSucc =
            (M.runFrom (counterLoopOrbit M τ c r) u).workTapePos j)
```

The three generalized declarations keep their bodies (for `counterLoop_time_le`, its
proof) verbatim. Each generic contract is its `Bool` counterpart with exactly these
substitutions: `M, τ, c, ct` over `Γ`; `counterLoopTM M a …` becomes `counterLoopTMVia e M
a …`; `hw` has `w.map e`; the done finish is `some (e true)`; the escape finish is
`(counterWord w (r₀ + 1)).map e`; and the escape exit state is `ex`, since `e` is the
embedding. The done contract's first no-exit clause is re-wrapped to stay under 100
columns. All four clauses are kept in both.

## Proof routes (binding)

1. **The generic decrement phase**: `counter_debit`, rewritten. Its statement is the landed
   one over `Γ`, with host `counterLoopTMVia e M a exit`, `hw` over `w.map e`, and
   conclusion `counterPatch ct cp (v.map e)`. Steps:
   - Guarded transport, as now (`MultiTapeTM.runFrom_mapState_of_agreeOn`, `emb :=
     counterLoopDecExit a`, agreement by `rfl` on the pre-verdict controls). Its source is
     `embedEmitTM (lastEmb k) ((decrementTM 1 0).liftSymbols e)`.
   - The state-renamed start is the R1 configuration `embedEmitCfg (lastEmb k)
     (Fin.lastCases ct c.workTapes) (Fin.lastCases cp c.workTapePos) [] d₁`, with `d₁ :=
     ⟨some .run, c.inputPos, fun _ => ct, fun _ => cp, c.output⟩` (probe 3(g): public
     selected-tape and frame lemmas only). Then `embedEmitTM_runFrom`.
   - The **overlay transport** landed in `SymbolLift` (cite it; never re-prove it).
     `Cfg.liftOver_decodeSymbols e d₁` rewrites `d₁` as the overlay of its decoded shadow
     `Cfg.decodeSymbols e d₁`. Then `MultiTapeTM.liftSymbols_runFrom_over` makes the lifted
     decrement's run the overlay of the `Bool` run from the shadow. Its two hypotheses for
     `decrementTM 1 0` are input-obliviousness (`fun _ _ _ _ => rfl`) and no blank write
     (case analysis, probe 3(a)).
   - On the shadow, apply the **landed** `decrementTM_run_succ_ofCfg` and
     `decrementTM_run_underflow_ofCfg` at `k := 1`, `i := 0`. The shadow's `hw` is `hw`
     rewritten by `FinTM.bufferTape_map_decode`.
   - Read back: on `[cp, cp + |w|)` the overlay is `bufferTape (v.map e)`, by
     `decodeBool_eq_some` and `FinTM.bufferTape_map`; off it, the cell is `ct`'s. State,
     heads and the verdict cut transfer unchanged. The trajectory gives `counterSpan`'s
     three parts as now.

   The plain `MultiTapeTM.liftSymbols_runFrom` **does not apply here**. It needs a
   configuration that is a lift everywhere, input included (`Cfg.liftSymbols` has input
   `x.map e`), while the host input `x : List Γ` and `ct` off the word are arbitrary. That
   is why the overlay layer was landed.
2. **The host layout and the round induction.** `counter_cfg_eq` is public and frozen at
   `Bool`, but the generic privates need the layout at `Γ`. Add one private
   `counter_layout`: `counter_cfg_eq`'s statement and body with `Bool` ↦ `Symbol` (binders
   `{k : ℕ} {Symbol S : Type} {x : List Symbol}`), and `counter_last_unselected` inlined
   (probe 3(h)). Every present use of `counter_cfg_eq` (base lines 773–967) cites
   `counter_layout`, and `counter_cfg_eq`'s body becomes `counter_layout q c ct cp`. This is
   G1's "specialization proved by instantiation", not a parallel copy.

   Then `counter_rounds`, generalized in place. It is the landed
   proof with the host `counterLoopTMVia e M a exit`, the counter words mapped by `e` in
   every `counterPatch` and frame hypothesis (lengths by `List.length_map`,
   `counterWord_length`), and `counter_body` generalized the same way (types plus host
   substitution only). It stays **the only host induction**, with its unrestricted final
   state (§12.7 fill F4). The generic contracts' bodies are the landed `Bool` bodies under
   the same substitutions; the done case's fill uses `List.map_replicate`.
3. **The `Bool` contracts by Z5** (probe 3(c)–(e)). One private `counter_refl_agree :
   (counterLoopTMVia (Function.Embedding.refl Bool) M a exit).AgreeOn (counterLoopTM M a
   exit) Set.univ`. Body controls, `done` and `escape` agree by `rfl`. For `dec f`, compute
   R1's action at `lastEmb k` from the **public** surface: `conv_lhs => whnf`, `split` on
   the slot search, and `show` its defining term `(List.finRange 1).find? fun i => decide
   ((lastEmb k) i = j)`. Name **no** private Embed declaration. The lift at `refl` is the
   identity table (`decodeBool refl` is `some`; `Option.map refl` is `id`), and the
   remaining comparison is `incrementTM`'s table by cases. Then each `Bool` contract is
   `simp only [z5]` followed by the generic contract at `refl`, with `hw` converted by
   `Function.Embedding.coe_refl` and `List.map_id`. These are about 15 lines each and contain
   no induction.
4. **R8.6, `expandTM_run_ofCfg`.** `counterLoopTM_run_done` with `τ := fun _ => pat.length
   + 1`.
   - The orbit's closed form (`r` copies of `pat` from `pos`, head at `pos + r·|pat|`,
     state `some 0`) by induction on `r` **over the writer's orbit**, from
     `writeAdvTM_run_ofCfg`, never over host rounds. Keep it a `have`.
   - Intermediate liveness from the writer's finish by
     `MultiTapeTM.runFrom_state_ne_none_of_le`, since the writer contract has no liveness
     clause.
   - The sum is `Finset.sum_const` with `Finset.card_range`. The head clauses come from the
     loop's body-head clause and the writer's interval.
   - Checks named by the gate: `d = 0`, `w = []`, and `pat = []` with `d > 0`.
   - `writeAdvTM_run_ofCfg` is sorried at base in `Build/Scan.lean`, which is not yours:
     cite it. **Deliver R8.6 proved modulo it** (D5). The axiom print keeps `sorryAx` until
     Scan's fill lands; state that in `REPORT.md`.

## Ground rules (binding)

1. **Statement shape.** The type-only generalizations are their base statements with
   exactly `{S : Type}` ↦ `{Symbol S : Type}`, `x : List Bool` ↦ `x : List Symbol`, and
   `Bool` ↦ `Symbol` where it denotes the tape alphabet (`Cfg`, `MultiTapeTM`, `ct`). The
   counter word `w : List Bool` is **not** the tape alphabet and stays. The new declarations
   are the text above, character for character. Nothing else may change: no new
   hypotheses, no reordering, no renaming, no `Type*`.
2. **Docstrings.** Frozen declarations keep theirs. One flagged sentence in the module
   docstring may note alphabet genericity. The two `Bool` contracts and `counter_cfg_eq`
   get one flagged **Re-derivation appendix** paragraph each (their sketches describe the
   generic proof; policy §3 synchronization). New declarations get statement prose, the tag "(design
   §12.8a, R8.0b)" and a **Proof sketch**. Module docstring: add the four new names to
   `## Main definitions`/`## Main results`, a Design bullet for R8.0b, and update the
   status line (flagged; it names `writeAdvTM_run_ofCfg` while that is still sorried).
3. **Instance attestation (evidence, mandatory)**: `evidence/R80bInstances.lean.txt`,
   checked as a module against your tree. It must contain:
   - an `example` whose type is the **base** `counterLoop_time_le` statement, copied
     verbatim, proved by the generalized one;
   - the base statements of `counter_cfg_eq`, `counterLoopTM_run_done`,
     `counterLoopTM_run_escape` and `expandTM_run_ofCfg`, copied verbatim, each proved by
     the in-tree theorem (so each still elaborates over the generalized `counterLoopCfg`);
   - the probe's Part 4 instances run against the real `counterLoopTMVia` by `decide`.

   For the two generalized definitions, the mechanical diff of rule 6 is the evidence.
4. **No consumer edits; no parallel copies.** No file other than CounterLoop changes. If a
   call site fails because nothing fixes the alphabet, restore that one declaration's
   `Bool` form, record an escalation with the error, and continue. Never keep a `Bool` and
   a generic copy of the same declaration (no `counterLoopCfgVia`). The only `Bool`
   specialization kept beside a generic private is `counter_cfg_eq`, proved by
   instantiating `counter_layout`. There is no second host, round induction or decrement
   trace. Nothing private restates the landed `SymbolLift` overlay layer.
5. **Imports and privates.** Exactly one new import, `TCSlib.Complexity.TuringMachine.
   SymbolLift`. It is the fill's only new import edge. It is checked on `5afed90b`: no
   cycle (SymbolLift's closure is `Configuration`, `Deterministic`, `Finite`,
   `Simulation`), and it adds SymbolLift only to the closures of CounterLoop and InputCall.
   - Sanctioned new privates: `counter_refl_agree` (route 3) and `counter_layout`
     (route 2).
   - The single-use privates may be inlined: `counter_last_unselected` (into
     `counter_layout`), `counter_orbit_succ`, `counter_dec_injective`,
     `counter_redirect_injective`, `counter_patch_initial`.
   - **Net private count in CounterLoop: strictly below the base's 24** (D3; it was 25
     before `counter_cfg_eq` went public). List every added, removed and rewritten private,
     with its role.
   - `counter_buffer_complement` (line 211) is a special case of the public
     `FinTM.bufferTape_map`: its statement is `FinTM.bufferTape_map
     Equiv.boolNot.toEmbedding w p` by definition (checked read-only at the issue tree). Do
     **not** keep the duplicate proof. Take one of the two authorized dispositions, and keep
     every frozen public statement byte-identical:
     - **(i) Preferred: a private body swap.** Its statement is unchanged and its body
       becomes `FinTM.bufferTape_map Equiv.boolNot.toEmbedding w p`. The four call sites are
       untouched. It counts as a rewritten private.
     - **(ii) Deletion.** Delete it and re-point its four call sites (lines 280, 292, 333
       and 340, in the bodies of `decrementTM_run_succ_ofCfg` and
       `decrementTM_run_underflow_ofCfg`) to `FinTM.bufferTape_map Equiv.boolNot.toEmbedding`.
       These are authorized body changes of those two frozen publics; their statements stay
       byte-identical. It counts −1. `simp`/`rw` see `⇑Equiv.boolNot.toEmbedding`, not
       `not`, so a re-pointed site needs the instance with its `not`-form type ascribed. If
       that would add a local copy at each site, take (i).

     Either way it counts toward the target of **at most 23**.
6. **Mechanical surface diff (evidence):** a declaration-level, comment-stripped
   comparison of CounterLoop against the base. Every public declaration is listed in its
   freeze class above: unchanged, type-only (show the exact token diff), body-swapped, or
   new. Every body change is listed. Lines 106–541 of the base (symbol transport, C1
   decrement, counter arithmetic) are **byte-identical**, bodies included. The one exception
   is rule 5's authorized `counter_buffer_complement` disposition: its body (lines 211–213),
   or, under (ii), its deletion and the four re-pointed call sites.
7. **Escalation** on anything unprovable as stated: stop on that item, record the
   obstruction, continue.
8. **Size: report only** (D7). Report the final line count. No new file may be created;
   12.2c owns the per-theme split.

## Gate guidance carried forward (binding)

- §12.7 fill gate (`audits/s12-counter-fill-findings.md`): **F4**, one round induction
  with an unrestricted final state; **F5**, the injectivity and guard discipline (anchor
  priority when `exit = some a`); **F6**, every physical cost within `r ≤ value + 1`
  (`counterOverhead`'s docstring).
- §12.8 gate: round-1 note 25 and round-2 note 26 (R8.6 is the stated counter-loop
  instance: "retain the single existing loop induction"). Round-2 notes 31 and 32 (consumers
  keep the dedicated-digit-tape discipline and O6 validation). The generic contract's
  arbitrary `ct` frame is strictly more general; do not restate it.

## Cited infrastructure (public and proved at the issue commit)

R1 (`Build/Embed`): `embedEmitTM`, `embedEmitCfg`, `embedEmitTM_runFrom`,
`embedEmitTM_frame`, `embedEmitCfg_selected_tape`/`_pos`,
`MultiTapeTM.runFrom_mapState_of_agreeOn`. Z5 (`Simulation`): `MultiTapeTM.AgreeOn`,
`MultiTapeTM.runFrom_eq_of_agreeOn`, `FinTM.bufferTape` and its lemmas. Transport
(`SymbolLift`): `decodeBool`, `decodeBool_apply`, `MultiTapeTM.liftSymbols`,
`Cfg.liftSymbols`, and the overlay layer landed at `5afed90b`: `Cfg.liftOver`,
`MultiTapeTM.liftSymbols_step_over`, `MultiTapeTM.liftSymbols_runFrom_over`,
`Cfg.decodeSymbols`, `Cfg.liftOver_decodeSymbols`, `decodeBool_eq_some`,
`FinTM.bufferTape_map`, `FinTM.bufferTape_map_decode`. `Finite`:
`MultiTapeTM.runFrom_state_ne_none_of_le`.
Catalog: `incrementTM`, `FlagPhase`. Scan: `writeAdvTM`, and `writeAdvTM_run_ofCfg`
(sorried; cite only). Mathlib: `Function.Embedding.coe_refl`,
`Function.Semiconj.iterate_right`.

## Duplication governance (binding)

Run the text-level screen **before and after** (base: `audits/logs/s12-8-fill-D-screen-base.txt`,
539 declarations, 414 pairs at `5afed90b`):

```sh
python3 -I audits/evidence/retrofit/copy-text-screen.py <repo-root> \
  TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean \
  TCSlib/Complexity/TuringMachine/Build/Catalog.lean \
  TCSlib/Complexity/TuringMachine/Build/Embed.lean \
  TCSlib/Complexity/TuringMachine/Build/Seam.lean \
  TCSlib/Complexity/TuringMachine/Simulation.lean \
  TCSlib/Complexity/TuringMachine/SymbolLift.lean
```

- **No new cross-file pair** with a CounterLoop declaration on one side.
- **Known hazards:**
  - the generic contracts against the `Bool` ones they replace: the `Bool` bodies shrink to
    Z5 re-derivations, so no pair should survive;
  - `counter_refl_agree` against Embed's core;
  - `counter_layout` against `counter_cfg_eq`: the body moves, so it must not be left in
    both;
  - the generic `counter_debit` against the overlay lemmas: cite them, never unfold them;
  - the expand orbit induction against `counter_rounds`.
- List every new in-file pair with a one-line justification. At 90% or more it is a copy:
  factor it.
- Quote both outputs in `REPORT.md`, which carries **"new copies: none"**.

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake build`**. Use
  `scripts/lean_check_tree.sh` for every check.
- **Bootstrap once** from `briefs/orders/s128-fill-D.txt` (74 modules: the upstream closure
  of CounterLoop with the new `SymbolLift` edge, plus everything downstream and its
  closure; `TCSlib` and `TCSlib/ComputationalModels` excluded). Since `5afed90b`,
  `CfgRecord` imports `InputCall`, so `CfgRecord`, TQBF and the `ClassPSPACE` facade are
  downstream of CounterLoop:

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < briefs/orders/s128-fill-D.txt )
  ```

  **Base sorry-warning set, 37.** Yours: `CounterLoop` 1 (`expandTM_run_ofCfg`).
  Elsewhere: `Seam` 1, `Catalog` 12, `Scan` 4, `InputCall` 2, `CfgRecord` 5, TQBF 4,
  `NDCodes` 1, `Constructible` 2, `ConfigGraph` 3, `Inclusions` 2. Record the base list
  by name first.
- **Full downstream replay**: `Build/CounterLoop`, `Build/InputCall`, `Build/CfgRecord`,
  `ClassPSPACE/TQBF`, the `ClassPSPACE` facade and the `TuringMachine` facade, all with
  **zero errors**. Sorry warnings must be exactly the base's minus `expandTM_run_ofCfg`
  (36), by name.
- **Axiom prints, base and after,** for every public declaration of CounterLoop (base:
  `audits/logs/s12-8-fill-D-axioms-base.log`, 28 names). Every frozen and type-only name
  must be byte-identical with its base print, except that `expandTM_run_ofCfg` loses
  `sorryAx` only once `writeAdvTM_run_ofCfg` is proved (D5). The four new names must be
  within `[propext, Classical.choice, Quot.sound]`.
- Lint: `python3 scripts/campaign_style_lint.py` on `TCSlib/Complexity/TuringMachine` and
  `TCSlib/Complexity/TuringMachine/Build`, 0 FAIL each.

## Evidence for the R8.0b gate (the zip must contain all of it)

1. The full downstream replay log, and the bootstrap log with the base sorry list.
2. The mechanical surface diff (rule 6), with the freeze class of every public declaration.
3. `evidence/R80bInstances.lean.txt` and its check output (rule 3).
4. The axiom logs, base and after, name by name.
5. The two copy-text screen outputs and their delta.
6. The private ledger (rule 5) and the file size.
7. The lint lines.

## Out-of-scope sorries you will see (leave every one untouched)

Catalog's twelve (`fieldsTape_field`, `compareTM_run_ofCfg`, the four seeks,
`scanTM_run_ofCfg`, the five `scanResult_*` identities); Scan's four (cite
`writeAdvTM_run_ofCfg`, never prove it); Seam's `seamCompTM₂_run_ofCfg`; CfgRecord's five;
InputCall's `exists_inputCallTM`, `exists_inputSeekTM`; NDCodes'
`exists_effectiveNDMachineCode`. Downstream, TQBF's four (`exists_adjacency_codec_cnf`,
`TQBF_mem_PSPACE`, `TQBF_PSPACEHard`, `TQBF_PSPACEComplete`). Upstream of TQBF:
`spaceConstructible_logSpace`, `spaceConstructible_linear`, `NSPACE_subset_exp_dtime`,
`NL_subset_P`, `polyTimeReducible_of_mem_NL`, `NP_subset_PSPACE`, `SAT3_mem_PSPACE`.
Other streams and batches own them. If a proof seems to *need*
one of them beyond the cited `writeAdvTM_run_ofCfg`, that is an escalation.

## REPORT.md checklist

- [ ] The base hash and the ancestor check.
- [ ] Every declaration per freeze class; every body change; the private ledger and delta
      (at most 23); the `counter_buffer_complement` disposition, (i) or (ii).
- [ ] R8.6 stated as proved modulo `writeAdvTM_run_ofCfg`, with its axiom print.
- [ ] Escalations (rule 4, rule 7), or "none".
- [ ] The instance attestation file and its result; the mechanical surface diff.
- [ ] Both screens, in-file pairs justified, "new copies: none".
- [ ] The replay (modules, zero errors, sorry set by name), the axiom comparison, the lint
      lines, the file size. The diff touches only CounterLoop.

## Known pitfalls at this pin (hard-won)

- **Embed's R1 core is private.** `(embedEmitTM ι N).tr` unfolds to `embedActionCore✝`,
  and `decide (Fin.last k = Fin.last k)` does not reduce for a variable `k`. Use probe 3(c)'s
  `conv_lhs => whnf`, `split` and `show` pattern; `Action` has no `@[ext]`, so compare
  fields with a local `have`.
- **`x.map (Function.Embedding.refl Bool)` is not `x` definitionally.** Re-derive at the
  level of runs (Z5), never by casting configurations. `simp` needs
  `Function.Embedding.coe_refl` (it is not `@[simp]`) and `List.map_id`.
- **Close the re-derivations with `exact`.** After `simp only [z5]`, `exact` the generic
  contract at `refl` (probe 3(e)); `Function.Embedding.refl Bool true` and `true` unify by
  definition. Rewrite the escape finish's `.map refl` away first.
- **The overlay layer's hypotheses** are table-level. For `decrementTM 1 0`,
  input-obliviousness is `fun _ _ _ _ => rfl`; the no-blank-write proof is probe 3(a). The
  shadow's input is `x.map fun _ => false`; pass the length proof as `by simp`.
- **The writer has no liveness clause.** Use `MultiTapeTM.runFrom_state_ne_none_of_le`.
- **`Inference needs context`** (G1): a `def`/`let` naming `counterLoopCfg` with no typed
  argument cannot infer `Symbol`. All landed call sites pass a typed `c` (probe Part 1).
