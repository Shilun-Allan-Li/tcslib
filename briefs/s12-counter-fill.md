# §12.7 fill — counter-driven loops (`Build/CounterLoop.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch,
  NOT `main`.
- Before you start, confirm that
  `git merge-base --is-ancestor fe89d903db48bf07a67f67dba5d0d95439ff0e9a HEAD`
  succeeds. That commit merges RB5, which makes public the state-transport
  lemma this fill cites. If the check fails, **stop**.
- Create your working branch off the campaign branch (suggested name
  `fill/s12-counter`). Record the base commit hash in `REPORT.md`. Never
  rebase.
- **Delivery is by zip, not PR or push**: `s12-counter-fill.zip`, containing
  `REPORT.md`, the full modified source, a `git format-patch` series against
  your recorded base, a git bundle, the final sweep log, the axiom log, and
  `SHA256SUMS`.

## What this is

Fill the **ten audited-true statements** of design §12.7 in
`Build/CounterLoop.lean`. The statement gate closed in round 1 (0 blockers,
0 majors, 1 minor, 5 notes). Read in full:

- `audits/s12-counter-findings.md`, whose per-theorem derivations are your
  binding routes;
- `audits/s12-counter-resolutions.md`;
- `machine-library-design.md` §12.7.

| Target | Content |
|---|---|
| `MultiTapeTM.mapWorkSymbols_runFrom` | symbol transport, every configuration and time |
| `decrementTM_run_succ_ofCfg` | framed success at exact `2q + 2` |
| `decrementTM_run_underflow_ofCfg` | framed underflow at exact `2|w| + 2` |
| `counterWord_length`, `counterWord_value` | width and value of the counter |
| `counterOverhead_le_of_le`, `counterOverhead_le` | the amortized bounds |
| `counterLoopTM_run_done`, `counterLoopTM_run_escape` | the host's exact whole-run contracts |
| `counterLoop_time_le` | the uniform per-round bound |

## Owned file (modify this and nothing else)

`Build/CounterLoop.lean`: the ten proof bodies plus new `private` helpers.
All 13 definitions, both instances, and every statement and docstring are
**frozen and byte-identical**. Docstring sketch appendices are allowed if
flagged. **Imports:** you may add Mathlib imports if a needed lemma requires
one; flag each in `REPORT.md`. No other import changes. The promoted lemma is
already reachable: `CounterLoop` imports `Catalog`, which imports `Loop`,
which imports `Embed`.

## Proof routes (from the statement gate's findings; binding)

1. **Symbol transport.** Prove a one-step commutation: the conjugate reads
   `e.symm (e s) = s`, so it chooses the original action, and renamed writes
   commute with `Function.update`. Then iterate with
   `MultiTapeTM.runFrom_comm_of_step` (`Deterministic.lean`). This has the
   same shape as `StateRenaming.lean`'s `relabelState_step`. **Do not copy
   that proof.** Write the work-symbol version directly; if the copy screen
   below pairs the two, justify it.
2. **Decrement: transports, never traces.** Prove **one** private transport
   lemma relating `decrementTM k i` from `d` to `incrementTM k i` from the
   complemented configuration. Derive both decrement contracts from
   `incrementTM_run_succ_ofCfg` and `incrementTM_run_overflow_ofCfg` through
   it. The facts you need (findings, "Symbol transport and framed
   decrement"):
   - `decFixed w = (incFixed (w.map not)).map (List.map not)`, by list
     induction;
   - complementing twice is the identity on every cell;
   - `FinTM.bufferTape` commutes with `map not`, delimiters included;
   - `((w.map not).takeWhile id).length = (w.takeWhile not).length`.

   **No decrement trace may be written.** A private re-trace of the carry or
   borrow pass is a copy of Catalog's increment trace and will be rejected.
3. **Counter arithmetic.**
   - `counterWord_length` and `counterWord_value` follow from list induction
     on `decFixed`, then induction on `r`.
   - **Amortization uses the auditor's telescoping potential, not Legendre or
     Kummer** (findings, "Amortized bounds"). With `ones` the number of `true`
     bits, a successful decrement with `q` leading `false`s gives
     `ones v + 1 = ones w + q`, hence `(2q + 2) + 2·ones w = 4 + 2·ones v`.
   - Summing gives
     `counterOverhead w r + 2·ones w = 4r + 2·ones (counterWord w r)` for
     `r ≤ value`.
   - Width preservation and `ones u ≤ |u|` give the prefix bound. At
     `r = value` the word is all `false`, and its underflow sweep gives the
     whole-run bound.
   - `counterLoop_time_le` is then a termwise sum
     (`Finset.sum_le_card_nsmul`) plus `counterOverhead_le`.
4. **The host: one round induction, two theorems.** Prove **one** private
   lemma for the invariant before decrement `r`. At elapsed time
   `Σ_{j<r} τ(c_j) + counterOverhead w r`, the host configuration is
   `counterLoopCfg (some (.dec .run)) c_r ct_r cp`, where:
   - `c_r = counterLoopOrbit M τ c r`;
   - `ct_r` holds `counterWord w r` framed at `cp`;
   - no exit anchor occurred earlier;
   - the trajectory clauses hold up to that time.

   Derive `counterLoopTM_run_done` and `counterLoopTM_run_escape` from it.
   Do not restate the induction per theorem. The two phases of a round:
   - **Decrement phase.** On the working phases, the host's transition
     equals `decrementTM (k+1) (Fin.last k)` relabelled by
     `counterLoopDecExit a`, and that map is **injective**. Both facts are
     checked by the maintainer in
     `audits/evidence/s12-counter/CounterFillPreShip.lean.txt`. So apply the
     public `Turing.MultiTapeTM.runFrom_mapState_of_agreeOn`, with
     `emb := ⟨counterLoopDecExit a, _⟩` and the good set being the
     non-`done` phases. Its guard is the decrement contract's
     no-earlier-verdict clause, and its final step lands in `body a` or
     `done`. Cite `decrementTM_run_succ_ofCfg` or `_underflow_ofCfg` on the
     host's counter tape.
   - **Body phase.** The round starts in `body a`, whose image under
     `counterLoopRedirect a exit` is `dec run`, not `body a`. So execute the
     **first step explicitly** with `embedEmitTM`'s transition. Then
     transport the rest with `runFrom_mapState_of_agreeOn`, using
     `emb := ⟨counterLoopRedirect a exit, _⟩` (injective, also checked) and
     the good set of states that are neither the anchor nor the exit. The
     round hypothesis supplies the guard. Relate the body run by
     `embedEmitTM_runFrom` and the selected-tape exports along
     `Fin.castSucc`. RB5's private `emitterP2_call_phase`
     (`Build/Primitives.lean`) is the worked pattern of "one explicit
     step, then guarded transport". Follow it; do not copy it.
   - **Edge cases.** Time and the final configuration are exact, with no
     dispatch steps (findings, "Exact time and final configurations"). The
     `d = 0` case holds for every `c.state`. Escape at the last allowed
     round, `r₀ = value − 1`, has no trailing underflow.

## Ground rules (binding)

1. **Statement freeze**, as above.
2. **Cite only proved contracts**: the §12.6 framed increment contracts, R1
   (`embedEmitTM`, `embedEmitTM_runFrom`, `embedEmitCfg_selected_tape`/`_pos`,
   `embedEmitTM_frame`), Z5, and the RB5 lemma.
3. **One proof per shared argument**: one decrement transport lemma, one
   round induction (rules 2 and 4 of the routes). This repeats the lesson of
   the §12.6 fill gate, whose sibling proofs grew mutual copies.
4. **Escalation** on anything unprovable as stated; never restate.
5. **Optional export** (statement gate, note SC-5; flagged, rides the fill
   gate): a public corollary of the host trajectory clauses. On each body
   tape, the host's visited set is contained in
   `M.visitedByTapeHead c (Σ τ)`; on the counter tape, `spaceUsedByTape` is
   at most `|w| + 2`. Add it only if it falls out of your induction.

## Duplication governance (binding)

Run the text-level screen before and after:

```sh
python3 -I audits/evidence/retrofit/copy-text-screen.py <repo-root> \
  TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean \
  TCSlib/Complexity/TuringMachine/Build/Catalog.lean \
  TCSlib/Complexity/TuringMachine/Build/Embed.lean \
  TCSlib/Complexity/TuringMachine/Build/Loop.lean \
  TCSlib/Complexity/TuringMachine/StateRenaming.lean
```

- **No new pair may have a `CounterLoop.lean` declaration on one side and
  another file's declaration on the other**, except one justified pairing
  with `relabelState_step` (route 1).
- **List every new in-file pair**, with a one-line justification. A pair at
  90% or more is a copy; factor it.
- Quote both outputs. `REPORT.md` carries "new copies: none", with each
  proof's citations named.

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake
  build`**. Use `scripts/lean_check_tree.sh` for every check.
- Final: `Build/CounterLoop` with **zero errors and zero sorry warnings**.
  It is not yet in the `TuringMachine` facade; check it directly. The
  facade must also report zero errors.
- **Axiom prints** for all ten theorems and the 13 definitions: at most
  `[propext, Classical.choice, Quot.sound]`, and no `sorryAx`.
- Lint: `python3 scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine/Build`
  must report 0 FAIL.

## REPORT.md checklist

- [ ] 10/10, or a frontier; the base hash and the ancestor check.
- [ ] Every new `private` listed with its role; requested shared lemmas, or
      "none"; imports added, if any.
- [ ] The decrement transport lemma and the round induction named, with
      each derived theorem's citations.
- [ ] Duplication: the copy-text screen before and after, every new pair
      justified, and "new copies: none".
- [ ] The final sweep tail, the axiom prints, and the lint line.
- [ ] Diff touches only `Build/CounterLoop.lean`.

## Known pitfalls at this pin (hard-won)

- **`counterLoopCfg` ignores `c.state`.** Its state field is the host
  state. The body's state matters only through the orbit's run.
- **`counterWord` freezes at zero; the machine wraps.** `counterOverhead`
  equals the physical cost only for `r ≤ value + 1` (SC-1). Stay in that
  range.
- **The redirection happens on the final step of each phase.** A guard
  stated for all `u < t` must exclude the endpoint, as in the RB5 lemma's
  `hguard`.
- **Through-halt traps do not apply**, since nothing here halts. The live
  anchors `done` and `escape` are stationary self-loops, so the post-exit
  trajectory is constant.
- `Function.update_of_ne`; `dsimp only` after `cases` on control; feed
  `omega` the `Nat.two_pow_pos`/`pow_succ` facts it cannot see.
- The style linter requires a literal "Proof sketch" before **every**
  `sorry`; this matters only for a partial delivery.
