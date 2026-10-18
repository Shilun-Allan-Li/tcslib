# Ch3–4 fill campaign — Batch B2b: certificate cycling (`NP ⊆ PSPACE`, `3SAT ∈ PSPACE`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor 2483ff81d2e20427bd193595295f3b1ef53b1a57 HEAD` succeeds. That
  commit contains:
  - the §12.7 counter loop (proved);
  - the Z1 virtual-input host (proved);
  - **§12.8 pre-issue 2** (`b214c28c`): the phase host `phaseHostTM`/`phaseHostTM_run` and the
    public `FinTM.rewind_heads`, both proved;
  - the order list `briefs/orders/ch34-b2b.txt`.

  No other pre-issue landing is required. If the check fails, **stop**.
- Create your working branch off the campaign branch (suggested `fill/ch34-b2b`). Record the
  base hash in `REPORT.md`. Never rebase.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-ch34-b2b.zip`, containing
  `REPORT.md`, the full modified source, a `git format-patch` series against your base, a git
  bundle, the final sweep log, the axiom log, and `SHA256SUMS`.

## What this is

Fill the **two audited-true P4.1 statements of cluster B2b** (plan §4e, group B2: "a certificate
enumerator over a virtual-input decider"). [AB09, Example 4.6] cycles through every certificate,
re-executing the verifier in reused space. The construction is an **assembly of proved public
rows**, and **the proved-modulo set is empty**.

| Rows | Source | Role |
|---|---|---|
| `counterLoopTM` | §12.7 | the certificate loop, with exact round accounting and trajectory clauses |
| `incrementTM` | §12 R3, space-annotated, framed | steps the certificate in place |
| `vhostEmitTM` | §13 Z1 | the verifier on the virtual input `x ++ u`; also the setup's work-tape rewind |
| `Complexity.LogProg.cleanTM_run` | received (Hydroxyi) | blank tapes and origin heads after every call |
| `embedSilentRetTM`, `embedEmitRetTM`, `embedEmitTM` | R1′ / R1 | capture, halt-to-live, tape selection |
| `phaseHostTM` | pre-issue 2 | **all** sequencing and branching, including the loop body's return to its anchor and the two continuations after the loop |
| `copyTM`, `clearTM` | R3, framed | copy and clear |

R8.8 (`seamCompTM₂_run_ofCfg`) and R8.5e (`exists_inputCallTM`) are **not used**; see "Why not
the L row" below. Only four tiny private glue machines are new (route 1, step G).

Read in full:
- `audits/ch4-p41-findings.md` (rows 12–13, notes 8–9, **Question 5**, and the edge-case table)
  and `audits/ch4-p41-resolutions.md`: your **binding audit** (section below);
- design §12.6, §12.7, §12.8a §6 and §13 Z1;
- `Build/Seam.lean`'s phase-host section;
- `policy.md`, `workflow.md` §4 and plan §4e.

**Pre-ship check (maintainer, executed).** The probe is
`audits/evidence/b2b/B2bProbe.lean.txt` (output `.out`), elaborated at `b214c28c`. Its result:
0 errors, and no `sorry` of its own. It covers the following:
- every cited name, `#check`ed;
- the SAT3 corollary;
- the cleaned verifier run from `P_subset_PSPACE` and `cleanTM_run` (`clean_verifier`), proved;
- the rewind glue as a `timed_rewind`/`rewind_heads` instance, with its first halt;
- **the virtual-input rewind of a work tape** (`vhost_rewind`): buffer head back to `0`, buffer
  unchanged;
- the verdict reader's two steps;
- the counter value `2^Q − 1`;
- the certificate orbit and its completeness through `Complexity.Meyer.*`;
- the final PSPACE packaging with the Question 5 normalization;
- a `phaseHostTM` body inside `counterLoopTM` (`loopOverPhases`), with `Fintype`/`DecidableEq`
  inference for its state types;
- the dispatch retagging identity (`dispatch_retag`);
- the type-level assembly of the hosted source `D` and its call.

Every probe lemma's axioms are within `[propext, Classical.choice, Quot.sound]`.

## Owned file and targets (modify this file and nothing else)

Lines are at the issue commit.

| # | File:line | Target | Route | Uses |
|---|---|---|---|---|
| 1 | `SpaceComplexity/Inclusions.lean:103` | `Complexity.NP_subset_PSPACE` | certificate cycling over proved public rows | — |
| 2 | `SpaceComplexity/Inclusions.lean:112` | `Complexity.SAT3_mem_PSPACE` | `NP_subset_PSPACE SAT3_mem_NP` | 1 |

The file's proved `DTIME_subset_SPACE` and `P_subset_PSPACE` are frozen, and are cited by route 1.

### Proof routes (binding; the docstring's sketch, amplified)

1. **`NP_subset_PSPACE`.**

   **A. Data.**
   - `rintro L ⟨C, c, V, hV, hL⟩`; write `Q n := C * (n + 1) ^ c`.
   - **Verifier space** comes from `P_subset_PSPACE hV` (that is, `DTIME_subset_SPACE` at `V`'s
     polynomial time, degree by degree): `obtain` `e cV MV` with
     `MV.DecidesInSpace V (fun n => cV * (n ^ e + 1))`.
   - `obtain ⟨M_id, c_id, hid, hids⟩ := computesFunInTime_id_spaceUsed`.
   - `obtain ⟨M_p, c_p, hp, hps⟩ := computesFunInTime_polyUnary_spaceUsed C c`, which computes
     `x ↦ replicate (Q |x|) true` in space `≤ c_p(|x| + 1)`.
   - **No time bound is used.** Every phase time is an exact first-arrival time, existential, and
     `τ` is chosen classically.

   **B. Cleaned runs** (the probe's `clean_verifier`, transcribe it). For every input word, the
   machines `cleanTM MV.tm MV.tm.q₀`, `cleanTM M_id.tm M_id.tm.q₀` and `cleanTM M_p.tm M_p.tm.q₀`,
   started at `Cfg.init (.init q₀) _`, halt with the source's output, blank work tapes and origin
   heads, every head within the source's space bound. Use:
   - `cleanTM_run`, whose `hs` comes from `spaceUsedByTape_le_spaceUsed` and the space row;
   - `MultiTapeTM.exists_first_halt` to pass to the **first** halt, which the R1′ `_run` lemmas
     need.

   **C. Tapes.** The body has `k_B` work tapes:
   - `U`, the certificate;
   - `BUF`, the buffer;
   - `CAP`, the verdict;
   - `2·MV.k` banks;
   - `2·M_id.k` identity tapes;
   - `2·M_p.k` setup tapes.

   `counterLoopTM` appends the counter `Fin.last k_B`. Fix the selections as explicit `Fin`
   embeddings, with injectivity by `Fin.ext`/`omega`.

   **D. The test host `testTM`.** Defined **once**, on `k_B` tapes: `phaseHostTM` over the phases
   below, each phase a public row embedded by R1/R1′. Each redirect maps a phase's live exit anchor
   to the next phase's entry, and the stepping is `phaseHostTM_run` with `dispatch_retag`. Start
   from `Γ(u)`: state at the anchor, input head at `1`, `U = bufferTape u` at head `0`, every other
   body tape blank at head `0`, output `[]`.
   - **φ0** `anchorTM` (one stationary state). Its state is the loop anchor `s₀`, always
     redirected to φ1, and never revisited inside a round (sigma tags).
   - **φ1** `embedSilentRetTM ι_id BUF (cleanTM M_id.tm M_id.tm.q₀)` captures `x` onto `BUF`, with
     its head at `|x|` (step B with `embedSilentRetTM_run`).
   - **φ2** `embedEmitRetTM refl (rewindTM k_B true)` returns the native input head to `1`
     (`rewind_heads`, then `exists_first_halt`, then `embedEmitRetTM_run`).
   - **φ3** `copyTM k_B U BUF` (`copyTM_run_ofCfg`, with the destination head at `|x|`). Then
     `BUF = bufferTape (x ++ u)` globally: a pure lemma assembles the concatenation from the two
     writes.
   - **φ4** `embedSilentRetTM ι_call CAP (vhostEmitTM D)`, with buffer `↦ BUF` and bank `↦` the
     banks. The hosted source is
     `D := seamCompTM (embedEmitRetTM refl (rewindTM _ true)) (Sum.inr ()) (seamCompTM (embedEmitRetTM refl (cleanTM MV.tm MV.tm.q₀)) (Sum.inr ()) (rewindTM _ true) .start) (Sum.inl (Sum.inl (.init MV.tm.q₀)))`
     (the probe's `hostedSource`, verbatim; R2 inside `D` is proved).
     - Start `D` at virtual position `|x| + 1` with tag `true`.
     - **Finish:** `BUF` is unchanged with its head at `0`; the banks are blank at `0`;
       `CAP = bufferTape [b]` with its head at `1`, where `b = indicator V (x ++ u)`; the physical
       output is still `[]`.
   - **φ5** `verdictTM k_B CAP` reaches `done b`, with `CAP` blank at `0`. Its exits are
     `e_t := ⟨φ5, done true⟩` and `e_f := ⟨φ5, done false⟩`, and neither is redirected inside
     `testTM`.

   **E. The loop body** `B := phaseHostTM` over `[testTM, clearTM k_B BUF, incrementTM k_B U]`.
   Its redirects:
   - `testTM`'s `e_f` goes to the clear;
   - the clear's `done` goes to the increment;
   - the increment's `done true` goes to `⟨testTM, s₀⟩`, which is **the return to the anchor**.

   The body exit is `e := ⟨testTM, e_t⟩`.
   - `clearTM_run_ofCfg` applies because `BUF` is delimited at head `0`.
   - `incrementTM_run_succ_ofCfg` applies because `incFixed u = some _` in every loop round
     (`Complexity.Meyer.incFixed_enumWord`, at `r < 2^Q − 1`).
   - **Round lemma (one lemma, used for every round and for the continuation's call)**, from
     `Γ(u)`:
     - if `x ++ u ∈ V`, the body first reaches `e`;
     - otherwise it first returns to the anchor at `Γ(succ u)`.

     In both cases no state between is the anchor or `e`, every state is live, and **every body
     head stays in the windows of step H**.

   **F. The host** `H := phaseHostTM`, packaged as a `FinTM`, over these phases on `k_B + 1` tapes:
   1. the setup phases S1–S5;
   2. `counterLoopTM B s₀ (some e)`;
   3. `embedEmitTM Fin.castSuccEmb testTM`, the continuation;
   4. `ans true` and `ans false`.

   Its redirects:

   | From | To |
   |---|---|
   | S1 → S2 → S3 → S4 → S5 | each to the next |
   | S5 | `⟨loop, .dec .run⟩` |
   | `⟨loop, .done⟩` | the continuation's anchor |
   | `⟨loop, .escape⟩` | `ans true` |
   | the continuation's `e_t` / `e_f` | `ans true` / `ans false` |

   - **Setup, all proved rows:**
     - **S1** `embedSilentRetTM ι_p U (cleanTM M_p.tm M_p.tm.q₀)` captures `1^Q` onto `U`, with
       its head at `Q`.
     - **S2** `embedEmitRetTM ι_U (vhostEmitTM (rewindTM 0 true))`, with buffer `↦ U`. Start at
       virtual position `Q + 1`, tag `true`. **The buffer head returns to `0` with `U`
       unchanged** (the probe's `vhost_rewind`, then `exists_first_halt`, then
       `embedEmitRetTM_run`). This is the work-tape origin finder; no new rewind proof is
       written.
     - **S3** `copyTM U (Fin.last k_B)` writes the counter `1^Q`.
     - **S4** `incrementTM U` overflows (`incrementTM_run_overflow_ofCfg`, exit `done false`),
       leaving `0^Q = enumWord Q 0`.
     - **S5** `embedEmitRetTM refl (rewindTM _ true)` returns the native input head to `1`.
   - The counter value is `Nat.ofDigits 2 ((replicate Q true).map Bool.toNat) = 2^Q − 1` (pure;
     `ofDigits_replicate_true`).
   - `counterLoopTM_run_escape` covers an accepting round `r₀ < 2^Q − 1`, and
     `counterLoopTM_run_done` covers exhaustion. Their round hypotheses are the round lemma along
     `Γ(enumWord Q r)`.
   - After `done`, `U = enumWord Q (2^Q − 1) = 1^Q` (`Meyer.enumWord_ones`), and the continuation
     tests that last certificate.
   - **At `Q = 0`** there are zero rounds, and the continuation makes the single call on `u = []`.
   - The answers are `emitAction [b]` with `emit_halts`; the output is `[] ++ [b]`.

   **G. Glue: exactly these private pieces** (each probe-checked), plus pure lemmas.

   | Glue | What it is |
   |---|---|
   | `rewindTM k true` | 3 states over `FinTM.controlAction`; its contract is the `rewind_heads` instance |
   | `verdictTM k i` | built from `tapeAction`/`inputMoveAction`; two steps |
   | `anchorTM k` | one stationary state |
   | the answer emitters | `emitAction [b]` with `emit_halts` |

   The pure lemmas are:
   - the `bufferTape` concatenation;
   - the counter value;
   - `embedEmitCfg (Function.Embedding.refl _) _ _ [] c = c` (`Cfg.ext` with
     `embedEmitCfg_selected_{tape,pos}`);
   - `dispatch_retag`;
   - the ledger sum.

   No other machine may be defined.

   **H. Space (obligation 5): fixed windows, no factor `2^Q`.** Every round starts at `Γ(u)`, with
   body heads at `0`. The **fourth clause** of `counterLoopTM_run_done`/`_escape` puts every host
   body head at a round-run head; the phase lemmas and the rows' trajectory clauses then give the
   windows below.

   | Tape | Window | From |
   |---|---|---|
   | `U` | `[-1, Q]` | capture head `≤ Q`, `vhostCfg_buffer_head_mem`, copy, increment |
   | `BUF` | `[-1, n + Q]` | capture, copy destination, `vhostCfg_buffer_head_mem`, clear |
   | `CAP` | `[0, 1]` | |
   | banks | `[-s, s]`, with `s = cV((n + Q)^e + 1)` | step B through `vhostEmitTM_visitedByTapeHead_bank`; the rewinds move no work head (`rewind_heads`) |
   | identity tapes | `[-c_id, c_id]` | |
   | setup tapes | `[-c_p(n + 1), c_p(n + 1)]` | |
   | counter | `[-1, Q]` | `counterLoopTM`'s third clause, plus S3 |

   - Window to cardinality: `Finset.card_le_card` and `Int.card_Icc`, inline as
     `vhostEmitTM_spaceUsed_le` does.
   - The sum is `≤ D(n + 1)^f`; finish with the probe's `mem_PSPACE_of_ledger`.
   - **Never** bound the whole run's space by `spaceUsed_le_mul_succ`: its time is exponential.

   **I. Correctness.** `H` outputs `[true]` iff `∃ r ≤ 2^Q − 1, x ++ enumWord Q r ∈ V`. By
   `Meyer.enumWord_ctrVal`, `ctrVal_lt` and `length_enumWord`, this holds iff
   `∃ u, u.length = Q ∧ x ++ u ∈ V`, that is, iff `x ∈ L`. Begin with `classical`.

2. **`SAT3_mem_PSPACE`.** `NP_subset_PSPACE SAT3_mem_NP`, as the docstring says.

**Why not the L row** (decision Q-C, recorded). `exists_loopTM_spaceUsed` has three requirements
this construction cannot meet with proved rows:
- every round within a polynomial `T`, and `T` enters its space bound;
- a startup that installs the state word at a canonical `stateWord` seam;
- a canonical-seam body.

The only proved reset for a captured, displaced word is `cleanTM_run`, which states no time bound.
The time-bounded clean calls (`exists_installCallTM`/`emitCallTM`) need a canonical argument,
which needs `x` on a tape at the origin, and only the sorried R8.5a/R8.5e provide that. The L row
therefore costs at least one modulo citation, plus a function-level step pipeline
(`splitSolveWith`, `pairMapSnd`, `incFixed`, `pairConcat`, a marker strip). `counterLoopTM`
needs no time bounds, and with `phaseHostTM` and the virtual-input rewind it costs none.

## Gate guidance (binding; `audits/ch4-p41-resolutions.md`)

The P4.1 gate closed in round 1 with both statements true as stated. Its notes bind the fill:

- **Note 8.** The fill has a hard dependency on space-preserving embedding, seam and reset
  contracts. Route 1 discharges it with R1/R1′, the phase host, R3's framed trajectory clauses,
  Z1's space rows and `cleanTM_run`. A time-only citation discharges nothing.
- **Note 9.** `SAT3_mem_PSPACE` is delivered at polynomial strength.
- **Question 5's five obligations** (verbatim below) are each a `REPORT.md` line, naming the lemma
  that discharges it.

## Cited infrastructure (public and proved at the issue commit)

- **Classes.** `NP`, `P`, `PSPACE`, `SPACE`, `P_subset_PSPACE`, `DTIME_subset_SPACE`,
  `SAT3_mem_NP`, `SPACE.mono_const`, `space_poly_subset_PSPACE`, `succ_pow_le`,
  `FinTM.computesInTime_iff`, `MultiTapeTM.{spaceUsedByTape_le_spaceUsed, exists_first_halt}`.
- **§12.7 / R3.** `counterLoopTM`, `counterLoopCfg`, `counter_cfg_eq`, `counterLoopOrbit`,
  `counterLoopTM_run_done`, `counterLoopTM_run_escape`; `incrementTM_run_succ_ofCfg`,
  `incrementTM_run_overflow_ofCfg`, `copyTM_run_ofCfg`, `clearTM_run_ofCfg`.
- **Catalog space rows.** `computesFunInTime_id_spaceUsed`,
  `computesFunInTime_polyUnary_spaceUsed`.
- **Z1.** `vhostEmitTM`, `vhostCfg`, `vhostBuffer`, `vhostBank`, `vhostEmitTM_runFrom`,
  `vhostEmitTM_visitedByTapeHead_{bank,buffer}`, `vhostCfg_buffer_head_mem`,
  `vhostEmitTM_spaceUsed_le`, `FinTM.VirtualTag`.
- **R1/R1′, phases, R2.** `embedEmitTM{,_runFrom,_visitedByTapeHead,_visitedByTapeHead_frame}`,
  `embedSilentRetTM{,_run,_visitedByTapeHead}`, `embedEmitRetTM{,_run,_visitedByTapeHead}`,
  `embedEmitCfg_selected_{tape,pos}`, **`phaseHostTM`, `phaseHostTM_run`**, `seamCompTM`,
  `seamCompTM_run_ofCfg`, `seamCompTM_firstReturn_ofCfg`, `seamCompTM_visitedByTapeHead_ofCfg`
  (inside `D` only), `MultiTapeTM.runFrom_mapState_of_agreeOn`.
- **Received.** `Complexity.LogProg.cleanTM`, `Complexity.LogProg.cleanTM_run`.
- **Glue vocabulary.** `FinTM.{rewind_heads, timed_rewind, controlAction, emitAction, emit_halts}`,
  `tapeAction`, `inputMoveAction`.
- **Arithmetic** (Q-A: MeyerTableau). `Complexity.enumWord`,
  `Complexity.Meyer.{length_enumWord, enumWord_zero, enumWord_ones, incFixed_enumWord, enumWord_ctrVal, ctrVal_enumWord, ctrVal_lt}`.

**The "proved modulo" set is empty.** A complete delivery has no `sorryAx` in either target's
axiom print. Any need for a sorried row is an escalation. **Do not cite**:
- `seamCompTM₂_run_ofCfg`, `exists_inputCallTM` or `exists_inputSeekTM`;
- any `Build/Scan` row, the seek rows, `compareTM_run_ofCfg` or `scanTM_run_ofCfg`;
- `expandTM_run_ofCfg`, or any `CfgRecord`, `ConfigGraph` or `Savitch` row.

## Inherited audit contracts (verbatim; binding on the fill)

From `audits/ch4-p41-findings.md`:

> | 12 | `NP_subset_PSPACE` | Enumerate exactly the certificate strings prescribed by the received NP definition, invoking the polynomial-time verifier in reusable polynomial workspace. The fixed-window construction and full ledger appear in question 5. |
> | 13 | `SAT3_mem_PSPACE` | Apply row 12 to the attached, proved `SAT3_mem_NP`. Its total-decoding treatment of malformed strings is inherited unchanged; this theorem introduces no new parser. |

From **Question 5**:

> 1. Construct exactly \(Q(n)\), preserve the certificate width, enumerate every such word once, and detect overflow. When \(Q(n)=0\), there is exactly one candidate, the empty word.
> 2. Preserve the original input and certificate while simulating the verifier on exactly \(x++u\), including the input-head boundary behavior.
> 3. Capture the verifier’s one-bit result internally. Emit no trial result on the host’s append-only physical output; emit its own single decision bit only on final termination.
> 4. Clear the verifier scratch and restore the heads before another trial. A cleanup that retains a whole history of all trials is not acceptable.
> 5. Prove all invocations and resets stay inside fixed polynomial-size tape windows. Equal per-call cardinality bounds alone do not imply a bound on the union of visited locations across calls.

> There is no factor equal to the number of certificates. Fixed windows bound the union over all trials.

From the edge-case table:

> | Empty certificate | Let \(C=0\), so \(Q(n)=0\). There is one candidate \(u=[]\), and \(x++u=x\). At \(n=0\) with \(C>0\), \(Q(0)=C\). | Enumeration must execute one verifier call in the zero-width case and must not assume empty input forces empty certificates. |

Obligation 1's "detect overflow" is discharged by the *count*. There are `2^Q − 1` counted rounds
plus the continuation's final call. The setup's single overflow produces `0^Q`, and no loop round
overflows. Say this in `REPORT.md`.

## Ground rules (binding)

1. **File ownership.** Only `SpaceComplexity/Inclusions.lean`, and in it only the two targets'
   bodies plus new `private` declarations. List every new declaration with its role.
2. **Statement freeze** over both targets and over `DTIME_subset_SPACE` and `P_subset_PSPACE`
   (statements and proofs). Docstrings stay. A flagged **"Fill appendix"** on `NP_subset_PSPACE`
   is expected. It names `counterLoopTM` as the round counter, `phaseHostTM` as the dispatch,
   `cleanTM_run` as the reset, and the copy-assembled buffer (P4.1 Question 5: "Copying is an
   optional simpler implementation here").
3. **Status text.** Only the module docstring's "first two proved; remaining phase-P4.1 statements
   sorried" may change, to "proved". Flag it. New exports: none.
4. **Imports: add exactly these**, and flag them:
   - `TCSlib.Complexity.TuringMachine.Build.CounterLoop`;
   - `TCSlib.Complexity.TuringMachine.Build.VirtualInput`;
   - `TCSlib.Complexity.TuringMachine.Build.Seam`;
   - `TCSlib.Complexity.SpaceComplexity.Machines.Clean`;
   - `TCSlib.Complexity.CircuitComplexity.MeyerTableau` (Q-A).

   All are cycle-free at `b214c28c`. Add no other TCSlib import. Add a Mathlib import only if a
   needed lemma requires it, and flag it.
5. **Escalation** on anything unprovable as stated, including a cited row that does not compose
   as route 1 says. Stop on that item, record the obstruction, and continue with the rest.
6. **No touching other sorries.** Cite proved material; never re-prove it.
7. **One proof per shared argument.**
   - `testTM` is one definition, used in the body and in the continuation.
   - The round lemma is one lemma.
   - `rewindTM` is one definition with five instances: φ2, S5, S2's hosted source, and `D`'s two
     rewinds.
   - The window ledger is one lemma.
8. **Size.** No cap. Report the file's line count and its new public and private declaration
   counts in `REPORT.md`.
9. **Continuation budget.** If your budget runs out, deliver a partial zip whose `REPORT.md`
   states which target is proved, and which `private` helpers remain `sorry` (each with a "Proof
   sketch").

## Duplication governance (binding)

Run the text-level screen **before and after**. The base is `audits/logs/b2b-screen-base.txt`
(the draft's `screen-base-F4-extended.txt`: 784 declarations, 626 pairs at `b214c28c`; no pair has an `Inclusions`
declaration on either side).

```sh
python3 -I audits/evidence/retrofit/copy-text-screen.py <repo-root> \
  TCSlib/Complexity/SpaceComplexity/Inclusions.lean \
  TCSlib/Complexity/TuringMachine/Build/{Catalog,CounterLoop,VirtualInput,Seam,Embed,Wrappers}.lean \
  TCSlib/Complexity/TuringMachine/{Simulation,UniversalStartup}.lean \
  TCSlib/Complexity/SpaceComplexity/Machines/{Clean,CleanSweep}.lean \
  TCSlib/Complexity/CircuitComplexity/{MeyerTableau,MeyerTab}.lean \
  TCSlib/Complexity/ClassNP/EXP.lean
```

- **No new cross-file pair** with an `Inclusions` declaration on one side.
- **Known hazards, forbidden:**
  - **ch2's enumerator.** Do not copy, adapt or re-derive `ClassNP/EXP.lean`'s private
    enumerator: `enumCont_*` (`concatTM`, `logTM`/`undoTM`, `cleanTM`, `bodyTM`, `returnAction`,
    `padAction`, `rewind`), `enumMachine_contracts`, `enumLoop_run`, `enumAny*`, `enumInc*`,
    `enumValue*`, `enumWord_complete`.
  - **`exists_proj_decider`.** Do not wrap it.
  - **Counters and loop hosts.** Use no second counter or loop host: `loopDebit`,
    `f2_loopDebitTM`, `timedUniversalTM`, `clockTM`, the `exists_loop*TM` family,
    `exists_loopTM_spaceUsed`.
  - **Dispatch.** Write no new seam or dispatch combinator, and no loopback adapter:
    `phaseHostTM` is the dispatch.
  - **Virtual input.** Write no new virtual-input transformer or lockstep (no split
    native-plus-tape input; no re-proof of `bufferedCompTM`'s phase two, `a2_mapVirtual*`,
    `f2_splitCount*` or `universalInput_*`). S2 *uses* `vhostEmitTM`.
  - **Rewinds.** Write no rewind induction. `f2_catalogRewind` and `enumCont_rewind` are 100%
    copies of `timed_rewind`; cite `rewind_heads`/`timed_rewind`.
  - **First halt.** Write no first-halt lemma (FH-1). Use `exists_first_halt`.
  - **Halt-to-live.** Write no verdict register à la `redirectTM`/`captureAction`.
  - **Window lemmas.** Write no visited-interval lemma.
  - **Wrong layer.** Use no `LogProg` register-program enumeration (`ImplicitEnum`,
    `CounterProgSim*`).
- **Glue tables** use `tapeAction`/`inputMoveAction`/`controlAction` (the §12.8 change-9
  discipline).
- List every new in-file pair with a one-line justification; ≥ 90% is a copy, so factor it. Quote
  both outputs in `REPORT.md`, which carries **"new copies: none"**.

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; run `lake exe cache get`; **never `lake build`**. Use
  `scripts/lean_check_tree.sh` for every check.
- **First add the sanctioned imports.** Then **bootstrap once** from `briefs/orders/ch34-b2b.txt`.
  It has **112 modules**: the upstream closure of `Inclusions` with those imports, plus
  `ClassPSPACE/TQBF` and the `ClassPSPACE` and `SpaceComplexity` facades, with their closures.

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < briefs/orders/ch34-b2b.txt )
  ```

- **Base sorry-warning set: 54** at the issue commit (60 before the first B7 delivery filled six
  Logspace targets):
  - yours: `Inclusions` 2;
  - `Build/{Seam 1, InputCall 2, Catalog 12, Scan 4, CounterLoop 1, CfgRecord 5}`;
  - `Constructible` 2, `ConfigGraph` 3, `ClassPSPACE/TQBF` 4, `Savitch` 3, `Hierarchy` 4;
  - `Logspace/{InputAccess 1, QueryReshape 2, Reductions 2, Path 2, ImmermanSzelepcsenyi 3, Mult 1}`.
- **Final checks.**
  1. `Inclusions`: zero errors, zero sorry warnings.
  2. Downstream (`ClassPSPACE/TQBF`, the `ClassPSPACE` facade, the `SpaceComplexity` facade):
     zero errors, and sorry warnings exactly the base's (root `TCSlib` excluded).
  3. Re-run the pre-ship probe: 0 errors.
- **Axiom prints** for both targets are within `[propext, Classical.choice, Quot.sound]`.
- **Lint:** `python3 scripts/campaign_style_lint.py TCSlib/Complexity/SpaceComplexity`, 0 FAIL.

## Out-of-scope sorries you will see (leave every one untouched)

Every base sorry above except your two: the §12.8 statement layer
(`Build/{Seam, InputCall, Catalog, Scan, CounterLoop, CfgRecord}`), B2's `ConfigGraph` targets,
B3 (`Constructible`, `Savitch`), B4 (`TQBF`), B6 (`Hierarchy`), and B7/C2 (`Logspace/*`). If a
proof seems to *need* one of these, that is an escalation, not a license.

## REPORT.md checklist

- [ ] 2/2, or the partial frontier (rule 9); the base hash and the ancestor check.
- [ ] Every new declaration with its role: the four glue pieces, `testTM`, the body, the host,
      the round lemma, the window ledger, the pure lemmas.
- [ ] Question 5's five obligations, one line each, with the discharging lemma.
- [ ] Imports (flagged), appendix, status update, and escalations (or "none").
- [ ] Duplication: both screens, in-file pairs justified, "new copies: none".
- [ ] File size and declaration counts; the final sweep tail; the re-run probe; two axiom prints
      within the standard triple; the lint line. The diff touches only `Inclusions.lean`.

## Known pitfalls at this pin (hard-won)

- **Phase host and counter loop.**
  - `phaseHostTM` executes no action at a redirected state. Redirect **only** live exit anchors,
    and discharge `hguard` from each row's no-earlier-exit clause; R1′ returns redirect
    `Sum.inr ()`.
  - The dispatch lands at `c'.mapState (fun _ => q')`. Rewrite it with `dispatch_retag` before
    the next phase's lemma.
  - `counterLoopTM` needs `S : Type` and `[DecidableEq S]`. Index phase families by a small
    inductive `I` with `Ph : I → Type`, and get the `Fintype`/`DecidableEq` instances by cases.
  - The counter value is `Nat.ofDigits 2 (w.map Bool.toNat)`, not `ctrVal`.
- **Virtual input and capture.**
  - `vhostCfg` installs `bufferTape y` on the **whole** buffer tape, so `U` (in S2) and `BUF`
    (in φ4) must hold exactly their word with blanks elsewhere.
  - At the right blank, `VirtualTag` needs tag `true`; `true` is valid at every position `≥ 1`.
  - `embedSilentCfg` puts the capture head at `|pre ++ output|`, not `0`. That is why S1 leaves
    `U`'s head at `Q`, φ1 leaves `BUF`'s at `|x|` (which φ3 uses), and φ4 leaves `CAP`'s at `1`
    (which φ5 reads).
- **Clean-up and halting.**
  - `cleanTM_run` gives *some* halting `T'`, and it does not restore the input head. Take
    `exists_first_halt` before any R1′ `_run`, which needs a live start. Use `D`'s trailing
    rewind.
  - No public first-arrival lemma exists for a stationary live anchor, so every rewind is the
    halting variant under `embedEmitRetTM`. Do not write such a lemma.
- **Lean mechanics.**
  - `MultiTapeTM.indicator` is classical: start with `classical`, and type the language as
    `(V : Set (List Bool))`.
  - `omega` cannot see through products, powers or `Finset.card`. Use `ring`, then `omega` with
    atoms; the polynomial step is `succ_pow_le`. The linter needs a literal "Proof sketch" before
    every `sorry`.
