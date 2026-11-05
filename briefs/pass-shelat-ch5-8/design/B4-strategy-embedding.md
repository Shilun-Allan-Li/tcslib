# B4: strategies embedded as parties (design)

**Ruling (user, 2026-11-05):** Frederick's `Strategy`/`View`/`Protocol`/`exec` (D8) stay the
definitions of interaction for IP, ZK and ch. 5–8's protocol notions (Def 155.1, Thm 175.1).
`Games.Party` is the proof calculus. B4 proves that a strategy's execution equals the `Party`
execution of its embedding. The construction follows gate 02 round 2 (findings 1–2 and the answer
to question 6).

## The embedding

`Strategy.toPartyWith S x z r role rounds : Party (List Bool) (List Bool) (List Bool)` takes a
fixed tape `r`:
- **Schedule.** The party keeps its received history `M` and the number of moves left. D8
  alternates strictly (`moverIsV`), so turns alternate.
- **On its turn,** it sends `S.next x z r M`. If that was the last scheduled move, the reply is
  `none` (closing), and it returns `S.next x z r M`. That is D8's output on the complete history,
  equal to its last message, as `Protocol.outV_eq_getLast_of_moverIsV` requires. Otherwise the
  reply is `some y`; it appends `y` to `M` and continues.
- **The second mover** receives the first message as its argument (`some y`, or `none` when
  `rounds = 0`, in which case it returns `S.next x z r []`).
- **A reply off schedule** (`none` too early, or `some` after the last move) cannot happen against
  an embedded counterpart. The party then returns `S.next x z r M`, a total default. The theorems
  quantify over embedded pairs only.

`Strategy.toParty S x z role rounds` first samples its whole tape, `r ← sample (S.Coins |x|)`, then
runs `toPartyWith` on `List.ofFn r`. Under this convention the round 2 finding 2 is answered: the
full [PS10] view is in the trace.

## The theorems

1. **Deterministic agreement.** For `π : Protocol`, inputs `x y z` and fixed tapes `(rP, rV)`,
   with `k = π.rounds.eval |x|` and the first mover chosen by `π.verifierFirst`,
   `Party.exec k (first) (second)` is `pure (done outFirst outSecond)`. The outputs are
   `π.outP`/`π.outV` in the right order.
2. **Traces.** `Party.execT` with fixed tapes returns, as received lists, the components of
   `π.transcriptWith`. With sampled tapes, its coin draws decode to `List.ofFn rP` and
   `List.ofFn rV`. So `π.viewP`/`π.viewV` are deterministic projections of the trace.
3. **Probabilities.** For any event on views and outputs, its probability over the sampled game
   equals `uprob` over `π.ExecCoins` (through B2's `prob_sample_eq_uprob` and `prob_sample_pair`).
4. **Fuel.** Exactly `k` messages are delivered; with fuel `k` the outcome is `done`, and with
   fuel `k − 1` it is `outOfFuel` (for `k ≥ 1`).

## Prerequisites (S2b)

- **The trace invariants** of gate 02 round 2, note 5: `|M_A| + |M_B| ≤ fuel`; alternation;
  equality on `outOfFuel`. They are stated with `AllOutputs`, which moves from `Hopping.lean` to
  `OracleComp.lean`. The review sub-agent's proof sketch is in
  `gates/02-s2a/review-r2/subagent-review.md`.
- **Induction** on `rounds`, generalizing over the history and the role, as the proof of
  `execT_outcome` does.

## Uses

- Thm 175.1 (sequential composition): `Q(n)` sessions are a recursion of `Party.exec` with the
  verifier's state and tape carried across sessions, transferred to D8's `ZK` by theorem 3.
- Def 155.1: views jointly with the other party's output, from one run (theorem 2).
