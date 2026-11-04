# S2b design note: the efficiency of reductions (the machine layer's crux)

Status: **route identified, 2026-11-04; nothing written yet.**

## The statement needed

Every reduction in prongs A–D has the same shape. Given a machine adversary `A` against the
oracles `spec`, the reduction answers `A`'s queries with an implementation `impl : QueryImpl spec σ
spec'` that may query its own oracles `spec'` and draw coins. The composite must be a machine
adversary against `spec'`, so that the hardness assumption (a PRF, a OWF, a TDP, …), which
quantifies over machines, applies to it. Informally:

> If `impl`'s work per query is a polynomial-time function of encoded strings, and `A` makes at
> most `q(n)` queries, then there are a machine `B` and a codec for `spec'` such that, for every
> `n` and coin string, `B.toComp codec' n q'(n) r'` equals the simulation of
> `A.toComp codec n q(n) r` by `impl` (outputs only), with `q'(n) = q(n) · (per-query cost)` and
> the coins `r'` split into `A`'s and `impl`'s.

Proved once, it spares every reduction of prongs A–D a machine construction of its own. The ch. 2–4
layer built one per reduction (`Asymptotic/GGMReduction*`, `HardCoreGL*`, …), each several hundred
lines.

## The route

1. **Handlers as string functions.** A `PolyHandler` packages `impl` as polynomial-time maps on
   encodings:
   - `step : ⟨state, query⟩ ↦` either "ask `spec'` this query, with this intermediate state", or
     "answer the adversary with this, and this new state";
   - the per-query number of target queries bounded by a constant `c` (or a polynomial).

   Coins are drawn from a segment of `B`'s tape, by Frederick's `exists_split` (`Closure.lean`).
2. **The replay step.** `B`'s next-move function, on its own encoded log, recomputes the whole
   simulated interaction. Starting from the empty log of `A` and the initial state, it repeats:
   - run `A`'s next-move function (`A.output`, polynomial-time by
     `NUPPT.polyTimeComputable_output`);
   - feed `A`'s query to the handler's `step`;
   - read the answers to the handler's target queries from `B`'s log.

   It ends when it reaches a target query not yet answered (`B`'s next move) or `A`'s final
   output (`B`'s output). Each round is a polynomial-time function of a state word of polynomial
   size.
3. **Iteration.** The replay is a polynomial number of rounds (at most `q(n)·(c + 1)`). The library
   has `Complexity.polyTimeComputable_iterate` (`Complexity/Randomized/Repetition.lean`):
   iterating a polynomial-time step `R(|x|)` times, with the orbit's lengths bounded by `P(|x|)`,
   is polynomial-time. The replay's number of rounds is a polynomial in `n`, and `1^n` is part
   of the input, so `R(|x|)` dominates it.
4. **The machine.** `NUPPT.ofPolyTime` of the replay function, with `A`'s advice and coin
   polynomial combined with the handler's (`exists_seq`/`exists_split`), is `B`.
5. **The functional equation.** `B.toComp codec' n q' r'` equals the simulation. The proof is by
   induction on `A`'s budget, matching `buildComp`'s unfolding against `simulate`'s. This part
   is pure framework reasoning on top of the decoder lemmas (`buildComp`, `toComp_singleCodec`'s
   pattern).

## Obligations and size (estimate)

| Piece | Kind | Lines |
|---|---|---|
| `PolyHandler` and its semantics as a `QueryImpl` | definitions, small lemmas | 150–250 |
| the replay step and its polynomial-time computability (pairing calculus, `polyTimeComputable_ite`, length bounds) | FP-level | 300–600 |
| the orbit length bound | arithmetic | 100–200 |
| the functional equation | framework | 200–400 |
| the headline lemma | glue | 50–100 |

The total estimate is 0.8–1.5k lines. The FP-level part reuses Frederick's pairing calculus and
his `Repetition` and `StateLoop` toolkit. It cites them only through published statements, since
under rule 10 his definitions are not unfolded.

## Who and when

- It depends only on the S2a core (gate 02) and the B3 decoder.
- It is a natural **fill item** (D-7: Claude), dispatched once gate 02 closes, with a brief built
  on this note. Alternatively the maintainer writes it.
- **Pre-ship probe** for the brief: instantiate `polyTimeComputable_iterate` on a toy replay
  (a handler answering every query with a fixed function), so that the brief's route is checked
  in Lean before dispatch.
