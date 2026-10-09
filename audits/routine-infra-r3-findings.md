# Machine-routine layer (§12), round 3: repair audit

**Verdict: PASS — 0 blockers, 0 majors, 1 minor, 0 notes.** The statement gate meets its zero-blocker/zero-major criterion. Both through-halt contracts are repaired. Round-2 R2-1 and the remaining round-1 R1 obligation are closed at statement level. The sole new finding is a documentation qualification; no further theorem hypothesis or conclusion change is needed.

Audited packet: `routine-infra-r3-bundle.md`, reported commit `2b82cbb3932438a3c6cda77d992d2fc4018d9923`, branch `complexity/arora-barak-ch3-4`. Audit date: 2026-10-09. Independently computed SHA-256:

```text
bb6514407d11a4a72b9dd4ad6d20a7acffd01a564fe3d369afbb49f30248d89b
```

Scope: the 38-line repair diff, both amended contracts, their use at live seams, and preservation of the previous dispositions. References below use extracted attachment line numbers. This is a mathematical statement audit, not a kernel-checked proof fill. No source files were changed.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| R3-1 | minor | `Build/Embed.lean:478` · docstring of `embedSilentRetTM_run`; opening pack repeats the qualification | The equivalence between `hc` and `0 < T` needs both existing first-halt hypotheses, not `hhalt` alone. | For an initially halted `c` and `T = 1`, absorption gives `hhalt`, and `0 < T` holds, but `hc` fails. This example violates `hlive` at zero, so it does **not** refute either amended contract. The forward implication uses `hhalt`; the reverse uses `hlive 0`. | Replace “under `hhalt`” with “under `hlive` and `hhalt`” in the source docstring. Acknowledge the same qualification for the shipped pack without editing it. |

**Replay and positive-time proof.** Both amended declarations retain exactly their old conclusions: transported lockstep at all times before `T`, the complete transported configuration with a live return anchor at `T`, and exclusion of that anchor before `T`. The suppressing contract retains `hcap`; forwarding needs no capture-tape condition.

1. **The old counterexample is excluded.** Reuse round 2's choices: `m = 0`, `k = 1`, `S = Unit`, empty input, the empty injection, `cap = 0`, and

   ```lean
   c := { M.initCfg [] with state := none }
   T := 0
   ```

   The capture condition holds. The hypothesis `hlive` is vacuous and `hhalt` follows from `runFrom_zero`. But the new premise reduces to

   \[
   \mathrm{hc}:\quad \mathrm{none}\ne\mathrm{none},
   \]

   which is impossible. Neither amended theorem can be instantiated. The old state-projection contradiction remains a valid diagnosis of the old statement, but is no longer a counterexample to the new one.

2. **Positive time follows, and the equivalence is precise.** For a live `c`,

   \[
   T=0
   \Longrightarrow
   c.\mathrm{state}=(M.\mathrm{runFrom}\ c\ 0).\mathrm{state}
   =\mathrm{none}\quad(\mathrm{hhalt}),
   \]

   contradicting `hc`. Since `T` is natural, `0 < T`. Conversely,

   \[
   0<T
   \Longrightarrow
   (M.\mathrm{runFrom}\ c\ 0).\mathrm{state}\ne\mathrm{none}
   \quad(\mathrm{hlive}\ 0)
   \Longrightarrow c.\mathrm{state}\ne\mathrm{none}.
   \]

   Thus, under **both** `hlive` and `hhalt`,

   \[
   c.\mathrm{state}\ne\mathrm{none}\quad\Longleftrightarrow\quad 0<T.
   \]

3. **The same action is executed completely.** Fix either flavor. Write `E` for its configuration transport with the stated parameters fixed, and `R` for its returning machine. From any live source configuration `c`, the definitions give

   \[
   \begin{aligned}
   &R.\mathrm{step}\bigl((E(c)).\mathrm{mapState}\ \mathrm{Sum.inl}\bigr)\\
   &\quad=\left\{E(M.\mathrm{step}\ c)\ \mathrm{with}\
   \mathrm{state}:=\mathrm{some}\!\left(
   (M.\mathrm{step}\ c).\mathrm{state}.\mathrm{elim}
   \ (\mathrm{Sum.inr}())\ \mathrm{Sum.inl}\right)\right\}.
   \end{aligned}
   \]

   Here is the component check. Injectivity of `ι` gives `embedSlot ι (ι i) = some i`; the transported selected tapes and heads therefore supply exactly the source's work symbols. The input position also agrees. Consequently both machines select the same source action. `embedActionCore` copies its input movement and every selected work-tape write and movement. Other frame tapes receive no write or movement. In the suppressing case, `hcap` keeps capture outside the selected bank: no emission leaves capture unchanged, while emission of a bit appends that bit at the old word length, by `bufferTape_append`; physical output remains `out₀`. In the forwarding case, output becomes `pre ++` the new source output, by list-append associativity. `Action.apply` performs these effects regardless of whether the successor is halted. Only the successor control differs, exactly as displayed.

4. **Induct up to the last live time.** At zero, `runFrom_zero` gives the required transported equality. If `t + 1 < T`, `hlive` makes the source live at both `t` and `t + 1`. Apply step 3 to the configuration at time `t`: its successor is `some q` for a source state `q`, and `Option.elim` sends it to `Sum.inl q`. The induction hypothesis and `runFrom_succ_eq_step'` yield

   \[
   R.\mathrm{runFrom}\bigl((E(c)).\mathrm{mapState}\ \mathrm{Sum.inl}\bigr)\ t
   =\bigl(E(M.\mathrm{runFrom}\ c\ t)\bigr).\mathrm{mapState}\ \mathrm{Sum.inl}
   \qquad(t<T).
   \]

5. **Execute the final step.** Since `0 < T`, the predecessor satisfies `T - 1 < T` and `(T - 1) + 1 = T`. The source is live there by `hlive`, so step 3 applies. Its successor is `none` by `hhalt`, hence `Option.elim` now selects `Sum.inr ()`. This proves exactly

   \[
   R.\mathrm{runFrom}\bigl((E(c)).\mathrm{mapState}\ \mathrm{Sum.inl}\bigr)\ T
   =\{E(M.\mathrm{runFrom}\ c\ T)\ \mathrm{with}\
      \mathrm{state}:=\mathrm{some}(\mathrm{Sum.inr}())\}.
   \]

   At every earlier time, step 4 and `hlive` put control in `some (Sum.inl q)`, distinct from `some (Sum.inr ())`. This proves the first-visit clause. These are all three conjuncts of each amended contract. The round-2 positive-time argument applies unchanged; no additional premise is needed.

The smallest positive case, S8, still has `T = 1`: a live, one-state source emits `true` and halts. With silent capture prefix `[false]` and physical output `[true]`, the return configuration has capture word `[false,true]`, capture head `2`, physical output `[true]`, and state `some (Sum.inr ())`. Forwarding with prefix `[false]` gives physical output `[false,true]` at the same live anchor. A final selected-tape write and head movement also survive by step 3. A final action with no emission works identically, leaving the capture head or physical output unchanged.

**Consumers and unchanged contracts.** The new premise is discharged by the supplied live launch configurations:

\[
\begin{aligned}
(M.\mathrm{initCfg}\ x).\mathrm{state}&=\mathrm{some}(M.q_0),\\
(\mathrm{Cfg.ofWords}\ q\ w).\mathrm{state}&=\mathrm{some}(q),\\
c_1.\mathrm{state}=\mathrm{some}(\mathrm{exit})
&\Longrightarrow
(c_1.\mathrm{mapState}(\mathrm{fun}\ \_\Rightarrow\mathrm{entry})).\mathrm{state}
=\mathrm{some}(\mathrm{entry}).
\end{aligned}
\]

Similarly, the release adapter assumes `c.state = some anchor` and starts its transported configuration at a live fresh state. Tape residue, displaced heads, and accumulated output do not affect these equations. Thus the added premise excludes only the unsupported initially halted launch; it imposes no extra condition on the advertised live-seam consumers.

| Unchanged round-2 contract(s) | Why the repair causes no regression |
|---|---|
| `embedSilentRetTM_visitedByTapeHead`, `embedEmitRetTM_visitedByTapeHead` | Compare the returning and closed **host** machines directly. While their controls correspond, their non-control actions agree; after the first host halt, the closed machine is absorbed and the returning anchor idles. Initially halted starts leave both machines fixed. This proof needs neither `hc` nor `hcap`, and also covers nonhalting runs. It does not depend on applying a through-halt theorem to an initially halted source. |
| `seamCompTM_run_ofCfg` | The full transported return and first-visit cut proved above still supply its phase-one hypotheses; stationary dispatch still costs exactly one step. |
| `seamCompTM_firstReturn_ofCfg` | Left/right state separation and the second-phase cut are unchanged. |
| `seamCompTM_visitedByTapeHead_ofCfg` | The two run segments and stationary dispatch are unchanged, hence so is the union containment. |
| `seamReleaseTM_firstReturn`, `seamReleaseTM_visitedByTapeHead` | Their definitions, live-start hypotheses, and execute-first arguments are byte-identical. S7's positive self-return remains valid. |

S9's arbitrary-frame, output-carrying composition is unaffected. Round-1 R2–R10 retain their accepted round-2 dispositions; R1 now closes. Round-2 R2-2 is addressed by the acknowledged pack erratum: **five run/first-return contracts and four visited-set contracts**, totaling nine.

**Integrity and evidence limits.** I independently obtained the round-2 packet and verified its SHA-256 as `fc7afcb8a469914c4b6a672348769329cfe708c013c64cfbb957481aadb2a3cf`, then compared the extracted files directly.

| Check | Result |
|---|---|
| Complete §12 source change | Exactly the supplied 38-line diff: two `hc` insertions and one docstring paragraph edit. All machine definitions and theorem conclusions are unchanged; the other 54 theorem declarations are unchanged. |
| Diff blob identities | Old `Embed.lean`: `e1d69d240310e4d080d9640dfe8faf0223b90798`; new: `b44c447984dcc5e6e91636986aeacb862f1024af`. Both match the diff's index prefixes. |
| Frozen context | All ten other attached Lean files, including `Seam.lean` and `Catalog.lean`, are byte-identical to round 2. The design document, policy, workflow, audit template, and round-1 report are also byte-identical. |
| Inventory | The theorem-name lists are unchanged. Exactly **56** sorried declarations: **Embed 13 + Seam 11 + Catalog 32**. |
| Supplied elaboration log | Header names the reported commit; 56 sorry warnings and zero `error:` lines. Every warning line points to the corresponding attached theorem declaration. |
| Supplied style log | Zero FAIL lines and nine WARN lines, agreeing with its summary. |

“Nothing else moved” holds for the §12 source and frozen Lean context. The broader campaign plan additionally appends four status rows recording repair batches and other gate closures; this is administrative context, not an unreported §12 source change.

No fresh Lean build was possible: `lean` and `lake` are unavailable, and the packet is not a complete checkout. The supplied logs were checked for internal consistency; fresh `.olean` production and the repository's commit association were not independently reproduced. This limitation does not affect the direct source comparison or the mathematical repair argument.

**Notation glossary.** `E` denotes the chosen configuration transport (`embedSilentCfg` or `embedEmitCfg`) with all non-configuration parameters fixed; `R` denotes its matching returning machine (`embedSilentRetTM` or `embedEmitRetTM`). All other symbols are the source declarations' parameters, state constructors, fields, and operations; `q` is a live source state in the induction.
