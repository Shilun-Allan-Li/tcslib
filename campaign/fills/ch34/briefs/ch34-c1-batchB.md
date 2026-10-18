# Ch3–4 fill campaign — Epoch C1, Batch C1b: the zero-space layer, parity in `L`, and the S9 run bound

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch,
  NOT `main`.
- Before you start, confirm that
  `git merge-base --is-ancestor 44853c6f3177fed8f7f8d2288210593e9c094f7e HEAD`
  succeeds. That commit lands the two shared lemmas this brief cites
  (below) and the order list. If the check fails, **stop**.
- Create your working branch off the campaign branch (suggested name
  `fill/ch34-c1b`). Record the base commit hash in `REPORT.md`. Never rebase.
- **Delivery is by zip, not PR or push** (`workflow.md` §4):
  `fill-ch34-c1b.zip`, containing `REPORT.md`, the full modified sources, a
  `git format-patch` series against your recorded base, a git bundle, the
  final sweep log, the axiom log, and `SHA256SUMS`.

## What this is

Fill the **13 audited-true statements** that epoch C1 assigns to this
batch (plan §4e):

- the eleven `ZeroSpace` sanity statements of the P0 reception gate (S1–S6
  and round 2's two timed witnesses);
- parity in `L` ([AB09, Example 4.7], P4.1);
- the reachable-register run bound S9 in the received `CounterProgRun`.

Both gates closed with 0 blockers and 0 majors. Read in full
`audits/ch34-p0-r2-findings.md` ("R2"; its "S1–S6" and "S9" derivations are your
**binding routes**), then `audits/ch34-p0-{findings,resolutions}.md`,
`audits/ch4-p41-findings.md` (finding 4, row 14), `policy.md` §1,
`workflow.md` §4, and plan §4e.

C1a, C1c, C1d and S1 run concurrently on disjoint files. Nothing outside
your files cites your targets.

**Pre-ship check (maintainer, executed):**
`audits/evidence/ch34-c1/C1bPreShip.lean.txt`, with output `C1bPreShip.out`.
It elaborates with 0 errors and the one expected sorry, a stand-in for the
parity contract. It restates all 13 frozen statements. It covers the
shared lemmas at the Z3, Z5 and Z6 shapes, `Bin`'s names after the import
(with no clash), `Cfg.ext_zero_tapes`, `inputSymbol_at` at the right blank,
the S9 call to `sim_run` at headroom 1, and its time arithmetic.

**Two shared lemmas were landed for you** in `SpaceComplexity/Basic.lean`.
Cite them, and write no private variant of either:

- `Complexity.SPACE.mono_const {s₁ s₂} {a} (h : ∀ n, s₁ n ≤ a * s₂ n) : SPACE s₁ ⊆ SPACE s₂`;
- `Turing.FinTM.computesInSpace_zero_of_k_eq_zero {M} {f} (hk : M.k = 0)
  (h : ∀ x, ∃ t, M.ComputesInTime x (f x) t) : M.ComputesInSpace f fun _ => 0`
  ("the bridge").

## Owned files and targets (modify these and nothing else)

Lines are at the issue commit (declaration / `sorry`).

| # | File:line | Target | Route | Uses |
|---|---|---|---|---|
| E1 | `SpaceComplexity/Examples.lean:62/63` | `Complexity.evenLang_mem_LOGSPACE` | the exported scanner + bridge | — |
| Z1 | `SpaceComplexity/ZeroSpace.lean:67/69` | `Turing.FinTM.k_le_spaceUsed` | each visited image nonempty; sum | — |
| Z2 | `ZeroSpace.lean:79/82` | `Turing.FinTM.ComputesInSpace.k_eq_zero_of_exists_zero` | instantiate at `List.replicate n₀ false` | Z1 |
| Z3 | `ZeroSpace.lean:101/103` | `Complexity.SPACE_eq_zero_of_exists_zero` | `⊆` Z2 + bridge; `⊇` `SPACE.mono` | Z2 |
| Z4 | `ZeroSpace.lean:113/114` | `Complexity.SPACE_id_eq_SPACE_zero` | Z3 at `⟨0, rfl⟩` | Z3 |
| Z5 | `ZeroSpace.lean:122/124` | `Complexity.SPACE_succ_of_pos` | `SPACE.mono`; `mono_const` at `a = 2` | — |
| Z6 | `ZeroSpace.lean:132/134` | `Complexity.SPACE_succ_eq_max_one` | the same, with `max 1` | — |
| Z7 | `ZeroSpace.lean:151/153` | `Turing.pairEncode_bits_inj` | `pairEncode_injective`, then `bits_injective` | — |
| Z8 | `ZeroSpace.lean:168/169` | `Complexity.trueLang_mem_SPACE_zero` | constant machine + bridge | — |
| Z9 | `ZeroSpace.lean:185/186` | `Complexity.evenLang_mem_SPACE_zero` | E1's exports + bridge | E1 |
| Z10 | `ZeroSpace.lean:196/199` | `Complexity.exists_zeroTape_const_oneStep` | the Z8 machine | — |
| Z11 | `ZeroSpace.lean:212/215` | `Complexity.exists_zeroTape_parity_decider` | `⟨evenScanTM, rfl, evenScanTM_decidesInTime⟩` | E1 |
| C1 | `TuringMachine/CounterProgRun.lean:343/346` | `Complexity.CounterProg.sim_run_of_regs_le` | R2's induction, steps by `sim_run` | — |

**Fill order.** Do `Examples` first, then `ZeroSpace` in file order; C1
can go at any time. **Z8 and Z9 precede Z10 and Z11** in the file and so
cannot cite them. Place the constant machine and its contract, `private`,
above line 161.

### Proof routes (binding; the audit's derivations, amplified)

1. **E1** (P4.1 row 14; R2 "S6"). Add two flagged public exports between
   `evenLang` and E1, each with a statement-prose docstring citing
   `[AB09, Example 4.7]`:
   - `Complexity.evenScanTM : Turing.FinTM Bool` (`k := 0`,
     `State := Bool`, start state "even");
   - `Complexity.evenScanTM_decidesInTime : evenScanTM.DecidesInTime evenLang fun n => n + 1`.

   **The machine** keeps its state on `false` and toggles it on `true`,
   moving right on each symbol. At the right blank it emits the indicator
   and halts. **The one `private` invariant**, by induction on
   `j ≤ x.length`: after `j` steps the state is the parity of
   `(x.take j).count true`, the head is at `j + 1`, and the output is `[]`.

   **E1** is then `⟨0, evenScanTM, …⟩`: the bridge (`rfl : k = 0`), then
   `.mono fun _ => Nat.zero_le _`. Keep it **direct**. Importing `ZeroSpace`
   here closes a cycle with `ZeroSpace.lean:6`.
2. **Z1, Z2.**
   - **Z1:** `0 ∈ Finset.range (t + 1)` makes each visited image nonempty
     (`Finset.Nonempty.image`, `Finset.card_pos`). Then
     `M.k = ∑ _ : Fin M.k, 1 ≤ spaceUsed` by `Finset.sum_le_sum`. No halting
     is needed.
   - **Z2:** `h (List.replicate n₀ false)`, then Z1 and `omega`. This is the
     `DTIME_eq_empty_of_exists_zero` pattern: follow it, don't copy it.
3. **Z3, Z4.**
   - **Z3 ⊆:** Z2 at `fun n => c * s n`, then the bridge on
     `fun x => (hM x).imp fun _ h => h.1`, then `.mono`.
   - **Z3 ⊇:** `SPACE.mono fun _ => Nat.zero_le _`.
   - **Z4:** `SPACE_eq_zero_of_exists_zero ⟨0, rfl⟩`.
4. **Z5, Z6.** Each is `SPACE.mono` in one direction and
   `SPACE.mono_const (a := 2)` in the other.
   - **Z5:** uses `s n + 1 ≤ 2 * s n`, from `hpos n` at **every** length.
   - **Z6:** uses `max 1 (s n) ≤ s n + 1 ≤ 2 * max 1 (s n)`, by `omega`.
5. **Z7.**
   - `Turing.pairEncode_injective` gives `(x, Nat.bits i) = (y, Nat.bits j)`.
     This is R2's `pairDecode` argument, so do not rerun it.
   - Then `Complexity.LogProg.bits_injective` (`Machines/Bin.lean:80`).
   - **No `Nat.bits` induction**: it would be a third copy, after `Bin` and
     `ClassNP/Nondeterminism.lean:2834`'s private `e3c_bits_injective`.
6. **Z8, Z10.** One `private` machine: no work tapes, one live state, a
   single transition that emits `true` **and** halts. Its `private`
   contract is `∀ x, M.ComputesInTime x [true] 1`.
   - **Z8** is the bridge plus `indicator {x | True} x = true`.
   - **Z10** is `⟨M, rfl, contract⟩`.
7. **Z9, Z11.** Both cite E1's exports, Z9 via the bridge. **No parity
   machine in `ZeroSpace`.**
8. **C1** (R2 "S9"). Induct on `t`, generalizing `s`.
   - **Each step** is `sim_run P x l₀ (B + 1) 1 s hp _`, with headroom from
     `hB 0`. This is R2's sanctioned "`sim_step` at `B + 1`" with
     `sim_run`'s own halted case, at exactly `2B + 5`.
   - **The suffix** runs from `run P x s 1`, by `step_pos_le` and
     `hB (1 + j)` with `run_add`.
   - **Compose** by `runFrom_add`/`run_add`, then `nlinarith`.
   - **Alternative.** R2's direct `sim_step` at `B` re-traces `sim_run`.
     Use it only if the screen shows no new pair.
   - **The statement stays at `t * (2 * B + 5)`.** "Fills may sharpen it"
     refers to the internal witness only; add no `2B + 3` corollary.

## Cited infrastructure (public and proved at the issue commit)

| File | Declarations used |
|---|---|
| `SpaceComplexity/Basic.lean` | the shared lemmas; `ComputesInSpace.mono`; `SPACE.mono` |
| `TuringMachine/Deterministic.lean` | `spaceUsed_zero_tapes_eq_zero`; `runFrom_add` |
| `TuringMachine/Configuration.lean` | `Cfg.init`; `Cfg.ext_zero_tapes`; `moveInputPos_pos_of_ne_right` |
| `TuringMachine/Simulation.lean` | `FinTM.inputSymbol_at` (reads `x[i]?` at position `i + 1`, the blank included); `controlAction` |
| `TuringMachine/Finite.lean` | `computesInTime_iff` |
| `TuringMachine/Encoding.lean` | `pairEncode_injective` |
| `SpaceComplexity/Machines/Bin.lean` | `LogProg.bits_injective` |
| `TuringMachine/CounterProg{,Run}.lean` | `sim_run`; `step_pos_le`; `run_{zero,succ,add}` |

Two catalog machines come close, but neither fits:

- `transducer_run` halts silently, so it cannot emit a verdict.
- The private `constTM` takes two steps.

Both of your machines are therefore hand-built. Each docstring names the
missing catalog row (policy §1).

Every module upstream of your files is sorry-free, so the **"proved
modulo" set is empty** and a complete delivery has no `sorryAx`.

## Inherited audit contracts (verbatim; binding on the fill)

From `audits/ch34-p0-r2-findings.md`, **"S1–S6: statement truth and delivered strength"** (`[...]` marks an elided display):

> S1. For every work tape `j`, time zero lies in `Finset.range (t + 1)`. Its image under the head-position function therefore contains the initial head position, which is zero. Thus
> [...]
> This includes `t=0` and `M.k=0`. The received `Clean.visited_interval` interface independently confirms origin membership. No halting hypothesis is needed for S1.
>
> S2. Given `s n₀ = 0`, instantiate the total computing contract at `x = List.replicate n₀ false`. Since `x.length = n₀`, some halting time satisfies
> [...]
> Hence `M.k = 0`. This concerns one fixed machine for every input, not a different machine at each length. The restriction to binary inputs makes a word of every natural length available.
>
> S3. If `L ∈ SPACE s`, take its witnesses `c,M`. A zero of `s` is also a zero of `fun n => c * s n`, so S2 forces `M.k=0`. Consequently, on every input and at every time,
> [...]
> The same machine and halting times witness membership in `SPACE (fun _ => 0)`. Conversely, a zero-space contract weakens to `c * s n` because that bound is nonnegative. Both inclusions hold, including when `c=0`. The identity-bound instance follows by choosing `n₀=0`.
>
> S4. For everywhere-positive natural-valued `s`,
> [...]
> Monotonicity gives one inclusion, and replacing the existential constant `c` by `2c` gives the reverse inclusion. For arbitrary `s`, the corresponding inequalities are
> [...]
> These prove both stated identities without constructibility, monotonicity, or eventual-growth assumptions. Positivity must hold at **every** length for the first identity; eventual positivity does not suffice. The second identity deliberately compares two normalized bounds and does not equate unnormalized `SPACE s` to them.
>
> S5. Apply `pairDecode` to the asserted equality. `pairDecode_pairEncode` gives
> [...]
> Therefore `x=y` and the two bit lists agree. Applying the received `bitsVal` inverse gives `i=j`. Conversely, substituting those equalities gives the encoded equality. At zero,
> [...]
>
> S6. `trueLang_mem_SPACE_zero` asserts membership of the full language. A machine with no work tapes, one live state, and a transition that emits `true` and halts computes the required one-bit output in one step. Its space is the empty sum, independently of input length.
>
> Use two live states representing even and odd parity, initially even, and no work tapes. A `false` leaves the state unchanged; a `true` toggles it. After consuming `j` symbols, the state equals
> [...]
> At the right blank, emit the indicator that this value is zero and halt. In this model the input head begins at the first symbol, so the construction consumes `x.length` symbol steps and one final step. It uses zero work cells, including on empty input. Moreover, `[]` is accepted and `[true]` rejected, so the language is nonconstant. Both S6 statements are true and imply zero-tape witnesses through S2. Their omission of the explicit time contracts is precisely finding 12. No formal regular-language equivalence is claimed or required here.

From the same file, **"S9 and the repaired boundary cases"**, and the boundary rows your proofs must survive:

> S9 is true. In fact, its hypotheses also permit the tighter bound `t(2B+3)`: the received `CounterProg.sim_step` requires only that the registers in its starting abstract state are at most `B`. It does not require the resulting registers to remain at most `B`.
>
> To derive that bound, induct on the abstract run length. At zero, use machine time zero. If the abstract state is halted, both encodings are stationary. Otherwise, the hypothesis at `j=0` supplies `sim_step`'s register bound; `hp` supplies its input-position bound. One simulated step costs at most `2B+3`. For the suffix, `step_pos_le` preserves the position condition, and
> [...]
> transfers the remaining register bounds. Compose the physical runs using `runFrom_add`. The induction's time calculation is
> [...]
> Thus the supplied constant `2B+5` is conservative and sound; it need not be changed. Applying `sim_step` at `B+1`, as the sketch proposes, is also valid. No final abstract register bound is needed.

> | Case | Result |
> |---|---|
> | `B=0`, `t=1`, one final increment from zero | S9's pre-step hypothesis holds; the final value is one. One machine step is within its five-step budget. |
> | S6 on `[]`, `[false]`, and `[true]` | The first two have even bit parity and the third odd parity. The zero-tape scanner outputs exactly one correct bit in one, two, and two steps, respectively. |

From `audits/ch4-p41-findings.md`, **row 14** (finding 4 is route 1's "direct" rule):

> | # | Statement | True-as-stated argument |
> |---|---|---|
> | 14 | `evenLang_mem_LOGSPACE` | A two-live-state finite controller scans the input, toggles on `true`, and emits the correct singleton indicator at the right blank. Zero work tapes suffice; alternatively the stated stationary work tape costs one cell, bounded by `logSpace`. |

## Ground rules (binding)

1. **File ownership.** Edit only the three owned files, and in them only:
   the 13 targets' bodies, new `private` helpers, and the two `Examples`
   exports. In the received `CounterProgRun`, only S9's body changes. List
   every new declaration with its role.
2. **Statement freeze.** No renames, re-signatures, restatements,
   reorderings or attribution edits. Docstrings stay, with two exceptions,
   each flagged: sketch appendices, and **status text**. The status text is
   the "sorried" labels at `ZeroSpace.lean:27` and `Examples.lean:27` and
   the "fill obligations" clause at `ZeroSpace.lean:21`. In addition,
   `Examples`' module docstring gains one *Main definitions*/*Main results*
   bullet per new export. Nothing else changes.
3. **Escalation.** If a target is unprovable as stated, stop on it, record
   the obstruction, and continue with the rest.
4. **Leave every other sorry alone.**
5. **Cite, never re-prove.** Exactly two machines; one proof per shared
   argument.
6. **Imports.** Add exactly one:
   `import TCSlib.Complexity.SpaceComplexity.Machines.Bin`, in `ZeroSpace`.
   `Bin` is Mathlib-only. Beyond that, only a flagged Mathlib tactic import
   is allowed.
7. **Requested shared lemmas:** none expected. If one arises, keep a
   `private` copy and list it.
8. **Continuation.** A partial zip lists:
   - the targets proved;
   - the helpers left `sorry`, each with a "Proof sketch";
   - the targets proved modulo one of yours.

## Duplication governance (binding)

Run the text-level screen **before and after**:

```sh
python3 -I audits/evidence/retrofit/copy-text-screen.py <repo-root> \
  TCSlib/Complexity/SpaceComplexity/ZeroSpace.lean TCSlib/Complexity/SpaceComplexity/Examples.lean \
  TCSlib/Complexity/SpaceComplexity/Basic.lean TCSlib/Complexity/SpaceComplexity/Machines/Bin.lean \
  TCSlib/Complexity/TuringMachine/CounterProgRun.lean TCSlib/Complexity/TuringMachine/CounterProg.lean \
  TCSlib/Complexity/TuringMachine/Simulation.lean TCSlib/Complexity/TuringMachine/Composition.lean \
  TCSlib/Complexity/TuringMachine/Encoding.lean TCSlib/Complexity/ClassNP/Transducer.lean \
  TCSlib/Complexity/ClassP/DTIME.lean
```

- **No new cross-file pair.** `CounterProgRun::run_pos_le` ↔
  `CounterProg::run_regs_le` is received base debt; leave it.
- **E1 ↔ Z9 is the one pre-identified pairing.** Both bodies are just the
  export plus the bridge. If the screen pairs them, report the fraction.
- **Hazards:**
  - E1's scan lemma against `transducer_run` (write transitions with
    `controlAction`);
  - Z7 against `pairEncode_injective` and `pairEncode_replicate_inj`;
  - C1 against `sim_run`.
- **List every new in-file pair** with a one-line justification. A pair at
  90% or more is a copy, so factor it.
- **Quote both outputs.** `REPORT.md` carries **"new copies: none"**.

## Environment and verification

- Lean 4 v4.25.0 with mathlib pinned. Run `lake exe cache get`, and
  **never `lake build`**: use `scripts/lean_check_tree.sh` for every check.
- **Bootstrap once** from `briefs/orders/ch34-c1b.txt`. It is the
  dependency-ordered closure of your files and of the replay set, with
  `Machines/Bin` before `ZeroSpace`:
  `( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done < briefs/orders/ch34-c1b.txt )`.
  Record the base sorry-warning set first.
- **Final checks.**
  1. Your three modules have zero errors and zero sorry warnings.
  2. The 15-module replay set, rechecked in that file's order, has zero
     errors and sorry warnings equal to the base's minus your 13. The set is
     your three files, `TuringMachine/CounterProgInput`,
     `ClassNP/{CounterProgPolyTime, PolyTimePrefix, PolyTimeBlockLoop,
     PolyTimeBlockTests, PolyTimeBlockMajority, PClosure}`,
     `SpaceComplexity/{CounterProgSim, CounterProgSimRun}`, and the
     `ClassNP`, `SpaceComplexity` and `TuringMachine` facades.

  The maintainer replays `PolyHierarchy`, `CircuitComplexity` and
  `Randomized` at integration. Root `TCSlib` is excluded.
- **Axiom prints** for the 13 targets and the two exports: at most
  `[propext, Classical.choice, Quot.sound]`, and no `sorryAx`.
- **Lint:** `python3 scripts/campaign_style_lint.py` on
  `TCSlib/Complexity/SpaceComplexity` and on
  `TCSlib/Complexity/TuringMachine`, 0 FAIL each.

## Out-of-scope sorries you will see (leave every one untouched)

- **C1a:** `NondeterministicSpace`, `NSPACE`, `SpaceClasses`, and two in
  `Inclusions` (B2 has the other two).
- **S1:** `ConfigGraph`.
- **C1d:** one in `Logspace/Reductions` (the rest are B7's).
- **Later epochs:** `Constructible`, `Savitch`, `Hierarchy`,
  `Logspace/{Path, ImmermanSzelepcsenyi, Mult}` and `NDCodes`.

If a proof seems to *need* one of these, that is an escalation, not a
license.

## REPORT.md checklist

- [ ] 13/13 or the partial frontier; the base hash and the ancestor check.
- [ ] The two exports and every new `private`, each with its role.
- [ ] Imports: `Bin`, plus any flagged Mathlib import.
- [ ] Status-text updates and appendices, flagged; escalations, or "none".
- [ ] C1's step discharge.
- [ ] Duplication: the screen before and after, every new pair justified,
      and "new copies: none".
- [ ] The sweep tail (owned modules, then the replay set), the 15 axiom
      prints, and both lint lines.
- [ ] The diff touches only the three owned files.

## Known pitfalls at this pin (hard-won)

- **The bridge's `M` and `f` are implicit.** Dot notation elaborates the
  head first, so write
  `refine (computesInSpace_zero_of_k_eq_zero (M := M) hk ?_).mono ?_`.
- **`SPACE`'s bound arrives as `fun n => c * s n`.** At `c = 0` and
  `s = fun _ => 0` it is defeq to `0`; `0 * logSpace n` is not, so E1 needs
  `.mono`. Dot notation sees through `DecidesInSpace`, as `SPACE.mono`
  shows.
- **`Language` is a Mathlib `def`.** Discharge `indicator` by
  `simp [MultiTapeTM.indicator]`, the `ClassNP/NTIME.lean` pattern.
  `evenLang` is **bit** parity, not length parity (round 1 has it wrong; R2
  corrects it).
- **`Cfg.init` puts the input head at `1`.** On `[]`, step 1 reads the
  blank (`transducer_run`'s caller proves `inputPos.val = 0 + 1` by `rfl`).
- **Zero-tape configurations.** Use `Cfg.ext_zero_tapes` with work fields
  `fun i => i.elim0`, and unfold steps as `transducer_run` does.
- **C1.**
  - Use `induction t generalizing s`.
  - `(run_succ P x s 0).trans (run_zero P x _)` gives
    `run P x s 1 = step P x s`.
  - `omega` rejects `t * (2 * B + 5)`, so use `nlinarith`.
- **No Linarith in `ZeroSpace` or `Examples`.** They reach
  `Mathlib.Tactic.Ring` but not `Mathlib.Tactic.Linarith`, so use
  `Nat.mul_le_mul_left` and `omega` there.
- **Z7 sits in `namespace Turing`.** Write
  `Complexity.LogProg.bits_injective` in full, and instantiate
  `pairEncode_injective (a₁ := …) (a₂ := …)`.
- **The linter** wants "Proof sketch" before every `sorry` (partial
  deliveries only) and a docstring on each export.
