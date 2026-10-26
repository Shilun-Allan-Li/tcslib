# E-Q: the stage query's route, before its brief (design note, maintainer, 2026-10-25)

**What this is for.** Megafill D's review (`campaign/fills/megafill/reviews/megafill-d/REVIEW.md`,
"What the maintainer should do next", item 4) turns E-Q's dossier into a fill brief at A1's landing
(#164). The target is `Turing.NTimeDiag.exists_queryTM` (`Diagonalization/NTimeDiagonalizer.lean:270`,
frozen by gate 39). The dossier's route (`megafill-D-DRAFTING-REPORT.md`, "Dossier 2") fixes the
mathematics. Its route probe proves, sealed:
- the witness elimination (through A1's `timeConstructible_iff`);
- the timeout deduction;
- the stop rule (`eq_decide_spec`, `eq_stage_of_stop`);
- the passed-rung bound (`eq_round_le`) and the ledger (`∑_{h<s} ℓ_{h+1} ≤ 2ℓ_s`).

It leaves the machine open: "the fill's bulk, 2–4k lines". Before the brief binds a route, this note
sets out the machine-level choices that decide most of that size. It ends with the decisions.
Nothing here is checked in Lean yet. Every size is an ESTIMATE.

## The shape (recommended)

1. **The guard, at the function level.** `query f g x` is
   `if p x then F |x| else []`, with `p x` "unary and `|x| ≥ 3`" and `F n := query f g 1ⁿ`
   (`query_eq`, `query_of_not_guard`).
   - `Turing.FinTM.computesFunInTime_cond` takes a decider for `p` (a private finite-state leaf,
     linear), a main machine `M₁` for `x ↦ F |x|`, and `computesFunInTime_const []`. Its bound
     `c (T₀ + max T₁ T₂ + 1)` is `O(g n + 1)`.
   - `M₁` may read only `|x|`, and only `|x| ≥ 3` matters. This splits off every non-unary case
     with no machine reasoning.
2. **`M₁`, one machine-level composite** (seams, R1 embeddings, the install and input calls):
   - the setup;
   - the locator loop;
   - the stage code;
   - `g`'s witness (the middle) or the budget (the top);
   - the writer.

   The locator's state lives on tapes and the writer reads it, so a function-level pipeline
   would have to serialize and re-parse it at every stage. The function-level kit has
   `pairDup`/`pairMapSnd` but no `pairMapFst`, swap or two-function pairing.

## The locator (the bulk)

**Rounds.** `Turing.Round.iterate_seq` (#167, once merged; or `Round.iterate` over an orbit), with
per-round times. The ledger is the dossier's: passed rounds `O(ℓ_{h+1})`, the last `O(n)`.
- **Not** the FinTM loop hosts `exists_loopFindTM`/`exists_loopTM`: their bound is
  `c (T + 1)(R + 2)`, one uniform round time times the round count. The locator has
  `R ≈ log* n` rounds, each up to `O(n)`, so that would be `O(n log* n)`, not linear.

**State** (tapes): the rung `ℓ` in unary, the stage index `h` in unary, `bits n` and
`L = ⌊log₂ n⌋` in unary (from `|bits n| − 1`), and the clock's counter.

**One round** at a rung `ℓ < n`, with `a = ℓ + 1 ≤ n`:
1. **The witness under the cap, as a clocked install call** (refined while drafting, below).
   `f`'s witness `M_f` computes `x ↦ bits (f |x|)` within `c_f (f |x| + 1)`. Its install call `C`
   (`exists_installCallTM`) turns `1^a` on its tape `0` into `bits (f a)`. All its other tapes
   are blank at both ends, and its first return to `exit` is within
   `c' (c_f (f a + 1) + a + |bits (f a)| + 1)`. Run `C` under `exists_stepClockTMVia` with the
   stop states `{exit}`.
   - **The counter needs no multiplication:** an all-ones word of width
     `m = |bits n| + |bits D₀|` has value `2^m − 1 ≥ D₀ (n + 1)`, with `D₀` a constant bounding
     `C`'s time whenever `f a ≤ n` (then `a ≤ n` and `|bits (f a)| ≤ n`). Also `2^m ≤ 4 D₀ n`.
     Write it by `copyMapTM` from `bits n` (every symbol mapped to `true`) and a constant tail.
     Restore it each round the same way, since the clock leaves "some word of the same width".
   - **Timeout:** `C` has not returned within `D₀ (n + 1)`, so `n < f a` (the analogue of
     `eq_timeout` through the call's bound), and the round stops inside the stage. Its cost is
     `O(n)`. Nothing needs restoring: it is the last round.
   - **Finish:** `bits (f a)` is on the call's tape `0`, and every other tape of the call is blank
     again. Its cost is `O(f a + 1)`, which is `O(ℓ_{h+1})` when the round passes
     (`eq_round_le`).

   **Why not `vhostSilentTM`** (the dossier's first sketch): a passed round leaves the witness's
   work tapes dirty within radius `τ`, and the next run needs them blank. The only clearing
   machinery for that is `ExhaustiveReplay`'s private window clear and translation lemma
   (C1E-1(g)), which would have to be harvested first. The install call's tracked banks already
   restore the scratch, so no harvest is needed.
2. **`n < f a`?** A binary `≤` on `bits (f a)` against `bits n` (a leaf: lengths first, then from
   the top bit; `Nat.bits` has no trailing `false`). Do not expand `f a` to unary first: a fast
   witness can output `bits (f a)` with `f a` up to `2^τ`.
3. **`X = f a + a + 1` in unary** (only when `f a ≤ n`): `expandTM_run_ofCfg` with counter
   `bits (f a)` and pattern `[true]` (`counterValue_bits`), then two copies of the rung plus a cell.
   Its cost is `O(X)`.
4. **`X⁴` against `L`, in unary with a cutoff.** First compare `X` with `L` (`X > L` means
   interior). Otherwise square twice with cutoff `L + 2`: a nested-copy leaf whose cost is
   `O(X + L)` per product. All operands of a passed round are at most `L ≤ log₂ n`, so the
   arithmetic is polylogarithmic per round and `O(log n)` rounds add `o(n)`.

   **No binary multiplication is needed anywhere.** This replaces the docstring's "fixed-degree
   binary arithmetic". The docstring names its rows as obligations, not hosts, so the frozen
   statement is unaffected.
5. **Decide** (`eq_decide_spec`'s three cases):
   - **interior:** stop;
   - **top** (`X⁴ = L` and `n` a power of two: a scan of `bits n`): stop, keeping `X²` as the
     budget;
   - **next:** write `ℓ' = 2^{X⁴}` in unary by `expandTM` with the counter
     `replicate (X⁴) false ++ [true]` (cost `O(ℓ')`, with `ℓ' < n`), and increment `h`.

**After the loop:**
- **The stage code.** `j = (Nat.unpair h).1` by a unary leaf: `h < log₂ n`, by
  `two_mul_lt_ladder_succ` (any polynomial in `h` is `o(n)`). Then `bits (j + 1)` by an install
  call of `computesFunInTime_lengthBits` on `1^{j+1}`, and `dropLast`.
- **The budget field:**
  - **middle:** `bits (g n)` by `g`'s witness on the native input (`exists_inputCallTM`, cost
    `c_g (g n + 1)`);
  - **top:** `bits (X²)` by the same install call on `1^{X²}`.
- **The writer.** Emit the flag, the inner pair (each bit doubled, then `[false, true]`), `α`, the
  separator, and the unary tail (`1^{n+1}` or `1^{ℓ+1}`). This needs one leaf that emits a tape
  word doubled. Every other piece is a constant or a raw copy.

## Leaves and sizes (ESTIMATE)

| Piece | Kind | Lines |
|---|---|---|
| guard decider | private finite-state scan | 150–250 |
| setup (`bits n`, `L`, the counter) | install call, `copyMapTM`, constants | 200–300 |
| one round as a contract (clock, vhost, compare, `X`, `X⁴`, decide, next rung) | composite with three leaves (binary `≤`, cutoff square, power-of-two scan) | 900–1,500 |
| the loop and its ledger | `Round.iterate_seq`, the dossier's lemmas | 300–500 |
| stage code (unary `unpair`, `dropLast`) | two leaves, an install call | 250–400 |
| budget field, writer | input call, install call, the doubled emitter | 300–500 |
| `M₁`'s assembly, the guard split, the final ledger | seams, `computesFunInTime_cond` | 300–500 |

That is about 2,400–3,900 lines, as in the C1-E design. A session will likely end partial, so the
brief's checkpoints follow the table. The guard split and the setup land first; one round as a
contract is the largest single checkpoint.

## Copy hazards the brief names

- `ExhaustiveReplay`'s capped replays: the `xr_` privates over the same clock, including its
  window clear and translation lemma. Cite the clock and the install call; never re-walk them.
- `TimeHierarchy/ClockLoop`, a colleague's file.
- #135's `ClassP/BinaryArith` (on `main`'s side, polynomial-time only). The unary route avoids its
  multiplication, and the binary `≤` leaf is the only overlap. Ledger it against `BinaryArith`'s
  `le` (Q-D6).
- The two counter families (`counterLoopTMVia`, `expandTM`). Cite them, and write no third
  counter.

## Decisions

**Ruled (user, 2026-10-25): the recommendation on 1–4**, with 5 as stated. The clocked install
call in "One round" step 1 is a refinement found while drafting the brief, within those rulings:
it replaces the virtual-input host, which would have needed a bank clear.

1. **The arithmetic: unary with cutoffs** (recommended; no multiplication leaf, simpler run
   lemmas, cost polylogarithmic per round), or the binary rows of the docstring (add, square,
   compare on `O(log n)`-bit words).
2. **The split: the guard at the function level, `M₁` machine-level** (recommended), or all
   machine-level (the guard as the composite's first phase), or a function-level pipeline for
   the post-loop pieces. The pipeline needs `pairMapFst` or a two-function pairing, which is not
   published, so it would need a small API PR first.
3. **Timing:** issue at the later of A1's and #167's landings (recommended: the brief then cites
   `Round.iterate_seq` and A1's `timeConstructible_iff`), or at A1's landing with `Round.iterate`.
4. **Who drafts the brief:** the maintainer, from this note, with a pre-ship run (overlay, import
   probe extended by this note's rows, route probe, seal controls, duplication probe, order list,
   base sorries, screen base) and a review sub-agent (recommended). The alternative is a drafting
   agent, as for megafill C.
5. **Megafill D's cover:** E-Q alone, since `spaceConstructible_poly` landed directly as #166.
   The agent is Codex.
