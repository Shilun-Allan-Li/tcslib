# Ch3–4 fill campaign — Batch B2b, continuation 2: the certificate search contract (`NP ⊆ PSPACE`, `3SAT ∈ PSPACE`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor d71c389ae36e55661a066397c22123351970d015 HEAD` succeeds. That
  commit contains:
  - **the first B2b delivery** (PR #40): the certificate host fully defined from the prescribed
    public rows, 15 proved private theorems, and both targets packaged around one admitted
    private helper. Its report is `audits/b2b-fill-agent-reports/fill-1-REPORT.md`;
  - the §12.8 fills since landed (Catalog Part 3, Seam, Scan, InputCall and CfgRecord rows,
    PRs #41 and #42);
  - **the second B2b delivery** (S1–S5 setup proved; the admission narrowed to
    `b2b_search_contract`), whose report is `audits/b2b-fill-agent-reports/fill-2-REPORT.md`
    and whose record is `audits/b2b-fill-integration-2.md`;
  - the order list `briefs/orders/ch34-b2b-cont.txt`, which is unchanged and still valid.

  If the check fails, **stop**.
- Create your working branch off the campaign branch (suggested `fill/ch34-b2b-cont2`). Record
  the base hash in `REPORT.md`. Never rebase.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-ch34-b2b-cont2.zip`,
  containing `REPORT.md`, the full modified source, a `git format-patch` series against your
  base, a git bundle, the final sweep log, the axiom log, and `SHA256SUMS`.

## What this is

**A continuation** (`workflow.md` §4) of `briefs/ch34-b2b.md`, which still binds. Read it in
full first. Its "What this is" section, the rows table and the reading list, is not
repeated here. Its route 1, with "Why not the L row", is restated below verbatim.

The first agent built the whole construction of route 1 in `SpaceComplexity/Inclusions.lean`
and stopped at its budget, with no escalation.

**What was delivered.**
- **The machine is fully defined:**
  - glue G: `b2b_rewindTM`, `b2b_verdictTM`, `b2b_anchorTM`, `b2b_answerTM`;
  - the hosted source `b2b_hostedSource` (route 1's `D`, verbatim);
  - the shared test `b2b_testTM` (route 1's `testTM`), with its phases and redirects;
  - the body `b2b_bodyTM`;
  - the outer host `b2b_host`, with its phases, redirects and exactly one `counterLoopTM`;
  - the explicit tape selections `b2b_wordTape`, `b2b_bankEmb`, `b2b_callEmb`,
    `b2b_singleEmb`.
- **Proved, 15 private theorems** (all within the standard triple). Reuse them; never restate
  them:
  - `b2b_clean_run`, `b2b_clean_verifier` (step B);
  - `b2b_rewind_run`, `b2b_vhost_rewind` (S2's work-tape origin finder);
  - `b2b_verdict_trace`, `b2b_answer_run`;
  - `b2b_embed_refl`, `b2b_dispatch_retag`;
  - `b2b_hostedSource_run`: `D`'s execution from any native position `≥ 1`, with one bit, blank
    banks, origin bank heads, input head `1` and the fixed bank radius throughout;
  - `b2b_counter_value` (`2^Q − 1`), `b2b_certificate_orbit`, `b2b_verifies_iff` (step I's
    arithmetic);
  - `b2b_buffer_concat` (φ3's concatenation);
  - `b2b_ledger_bound`, `b2b_mem_PSPACE_of_ledger` (step H's arithmetic and the PSPACE
    normalization).
- **One admitted private helper (first delivery):** `b2b_host_contract` (then at line 740, with a literal
  Proof sketch). It states the host's run, output and fixed-window space bound. `NP_subset_PSPACE`'s
  body is the packaging around it, and `SAT3_mem_PSPACE` is the corollary.

**What the second delivery added (all proved; reuse, never restate):**
- `b2b_capture_shape`, `b2b_clean_capture`: the reusable first-halt silent capture, with live
  return, empty physical output, the capture interval, the clean bank radius and fixed
  unselected heads;
- `b2b_setup_capture` (S1), `b2b_origin_shape` and `b2b_origin_run` (S2's virtual rewind),
  `b2b_rewind_return` (the native returning rewind), `b2b_setupCfg` (a configuration
  definition, not a machine) and `b2b_seed_run` (S3 copy and S4 overflow);
- `b2b_setup_run`: the complete S1–S5 run. It ends exactly at the outer loop's `.dec .run`
  seam, with native input `1`, certificate `0^Q`, counter `1^Q`, blank other tapes, all work
  heads at `0` and output `[]`, and every prefix head within `s + Q + 1`.

**`b2b_host_contract` is proved modulo one narrower admitted helper,
`b2b_search_contract`** (`Inclusions.lean:1388`, with a literal Proof sketch). Its body
composes the setup, the search contract and the inline window-to-cardinality calculation
(`Finset.card_le_card`, `Int.card_Icc`, the tape sum). **Your task: discharge
`b2b_search_contract`**, so that both targets are admission-free. It starts the existing outer
host at `b2b_setupCfg`, with control `⟨loop, .dec .run⟩`. It must establish:
- eventual halt;
- the singleton indicator for `∃ u, u.length = Q ∧ x ++ u ∈ V`;
- the uniform head radius `n + Q + cV·((n + Q)^e + 1) + cI + 1`.

The second report's "Next proof boundary" is written for you. In outline:
1. **One shared test/round contract**, used for every counted trial and the final continuation.
   Compose identity capture (`b2b_clean_capture`), the native rewind (`b2b_rewind_return`), the
   append copy (`b2b_buffer_concat`), the captured virtual verifier (`b2b_hostedSource_run`)
   and the verdict reader (`b2b_verdict_trace`) once. Then add the rejecting clear and
   increment suffix.
2. **The counter loop.** `counterLoopTM_run_escape`/`_done` along `b2b_certificate_orbit`, with
   classically chosen first-arrival times from the shared round.
3. **The final call and the answer** (`b2b_answer_run`), with the global physical-output
   invariant: trials capture internally, and only the final answer emits.
4. **The search windows**, from the public counter-loop trajectory clauses on the fixed round
   windows. Do not bound the search by its total time.

**Pre-ship check (maintainer, executed at this brief's ancestor):**
`audits/evidence/b2b/B2bProbe.lean.txt`, re-run at the issue tree
(`audits/logs/b2b-cont2-preship.log`). It gives 0 errors and no `sorry`, and every probe print
is within the standard triple. The maintainer's admission walk
(`audits/logs/b2b-fill-2-axioms.log`) shows that both targets rest only on
`b2b_search_contract`: every cited library row is admission-free.

## Owned file and targets (modify this file and nothing else)

| # | File:line (at the issue commit) | Declaration | Task |
|---|---|---|---|
| — | `SpaceComplexity/Inclusions.lean:1388` | `b2b_search_contract` (private) | **prove it** |
| — | `SpaceComplexity/Inclusions.lean:1428` | `b2b_host_contract` (private) | proved modulo the search contract; frozen |
| 1 | `SpaceComplexity/Inclusions.lean:1513` | `Complexity.NP_subset_PSPACE` | packaged; admission-free once the search contract is |
| 2 | `SpaceComplexity/Inclusions.lean:1535` | `Complexity.SAT3_mem_PSPACE` | `NP_subset_PSPACE SAT3_mem_NP` |

**Route-name mapping.** The first delivery prefixed route 1's names with `b2b_`:
- `testTM` is `b2b_testTM`, and `rewindTM` is `b2b_rewindTM`;
- the body `B` is `b2b_bodyTM`, and the host `H` is `b2b_host`;
- the probe's `dispatch_retag`, `vhost_rewind` and `clean_verifier` are the corresponding
  `b2b_*` theorems.

### Proof routes (binding; route 1 of the first brief, verbatim)

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

**Note for this continuation:** R8.5e (`exists_inputCallTM`) has since been proved (PR #41).
Decision Q-C stands regardless: the counter-loop route needs no time bounds, and the first
delivery has already built it. Do not switch to the L row.

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

**The "proved modulo" set is empty** (and still is). A complete delivery has no `sorryAx` in either target's
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

1. **File ownership.** Only `SpaceComplexity/Inclusions.lean`. In it, change only
   `b2b_search_contract`'s body (and, under rule 2, its statement, with `b2b_host_contract`'s
   body only as minimally as rule 2 requires) and the two targets' bodies,
   and add new `private` declarations. List every new declaration with its role.
2. **Statement freeze** over both targets, and over `DTIME_subset_SPACE` and `P_subset_PSPACE`
   (statements and proofs).
   - **The first delivery's machine definitions are frozen:** the glue, `b2b_hostedSource`,
     `b2b_testTM`, `b2b_bodyTM`, `b2b_host`, their phase and redirect families, and the tape
     selections. So are its 15 proved theorems. A genuine defect in a definition is an
     escalation (rule 5), never a silent edit.
   - **The second delivery's ten declarations** (the setup lemmas, `b2b_setupCfg`, and
     `b2b_host_contract`'s new body) are frozen too.
   - **`b2b_search_contract` is private and unaudited.** Prove it as stated, or split it into
     private lemmas.
     - You may change its statement only if `b2b_host_contract`'s body, and both targets'
       packaging, still go through. The host contract's body may then be adjusted minimally.
     - The change may not weaken what the packaging needs: run, output and the fixed-window
       space bound.
     - Record any change, with the old and new statements, in `REPORT.md`.
   - Docstrings stay. The flagged "Fill appendix (B2b)" may be extended.
3. **Status text.** Only the module docstring's status sentence may change, to "proved"; flag
   it. New exports: none.
4. **Imports: unchanged.** The five sanctioned imports landed with the first delivery. Add no
   TCSlib import. Add a Mathlib import only if a needed lemma requires it, and flag it.
5. **Escalation** on anything unprovable as stated, including a cited row that does not compose
   as route 1 says, or a defect in a frozen definition. Stop on that item, record the
   obstruction, and continue with the rest.
6. **No touching other sorries.** Cite proved material; never re-prove it.
7. **One proof per shared argument.**
   - `b2b_testTM` is one definition, used in the body and in the continuation.
   - **The round lemma is one lemma**, covering every counted trial and the final call.
   - `b2b_rewindTM` has its five instances.
   - The window ledger is one lemma.
8. **Size.** No cap. Report the file's line count and its new public and private declaration
   counts in `REPORT.md`.
9. **Continuation budget.** If your budget runs out, deliver a partial zip whose `REPORT.md`
   states:
   - which obligations of the frontier are proved;
   - which `private` helpers remain `sorry` (each with a "Proof sketch");
   - whether the targets are proved modulo them.

## Duplication governance (binding)

Run the text-level screen **before and after**. The base, at this brief's issue tree, is the
second delivery's after-screen, `audits/logs/b2b-fill-2-screen-after.txt`: **854 screened
declarations, 634 pairs, 177,277 characters**. `Inclusions`' only existing pair is
`b2b_callEmb` ← `b2b_bankEmb` (66%), the two explicit `Fin` selections. Do not use the issued
`b2b-screen-base.txt`, a narrower run (erratum in `audits/b2b-fill-integration.md`).

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
- **Bootstrap once** from `briefs/orders/ch34-b2b-cont.txt`. It has **112 modules**, the same
  set as the first order list, recomputed at the issue tree: the upstream closure of
  `Inclusions`, plus `ClassPSPACE/TQBF` and the `ClassPSPACE` and `SpaceComplexity` facades,
  with their closures.

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < briefs/orders/ch34-b2b-cont.txt )
  ```

- **Base sorry-warning set: 29** at the issue commit: the first continuation's names
  (`audits/logs/b2b-cont-base-sorries.txt`), with `b2b_search_contract` in place of
  `b2b_host_contract`. If PR #38 (R8.0b) has merged by your base, `expandTM_run_ofCfg` is
  proved, and the base set is 28.
  - Yours: `Inclusions` 1 (`b2b_search_contract`).
  - `Build/CounterLoop` 1 (`expandTM_run_ofCfg`), `Build/CfgRecord` 1
    (`exists_recordStepTM`).
  - `Constructible` 2, `ConfigGraph` 3, `ClassPSPACE/TQBF` 4, `Savitch` 3, `Hierarchy` 4.
  - `Logspace/{QueryReshape 2, Reductions 2, Path 2, ImmermanSzelepcsenyi 3, Mult 1}`.

  Record the base list by name first.
- **Final checks.**
  1. `Inclusions`: zero errors, zero sorry warnings.
  2. Downstream (`ClassPSPACE/TQBF`, the `ClassPSPACE` facade, the `SpaceComplexity` facade):
     zero errors, and sorry warnings exactly the base's minus yours (root `TCSlib` excluded).
  3. Re-run the pre-ship probe: 0 errors.
- **Axiom prints** for both targets, for `b2b_host_contract`, and for `b2b_search_contract` (or
  its replacements), within `[propext, Classical.choice, Quot.sound]`.
- **Lint:** `python3 scripts/campaign_style_lint.py TCSlib/Complexity/SpaceComplexity`, 0 FAIL.

## Out-of-scope sorries you will see (leave every one untouched)

Every base sorry above except yours:
- §12.8's `expandTM_run_ofCfg` (PR #38) and `exists_recordStepTM`;
- B2's `ConfigGraph` targets;
- B3 (`Constructible`, `Savitch`);
- B4 (`TQBF`);
- B6 (`Hierarchy`);
- B7/C2 (`Logspace/*`).

If a proof seems to *need* one of these, that is an escalation, not a license.

## REPORT.md checklist

- [ ] `b2b_search_contract` proved and both targets admission-free, or the partial frontier
      (rule 9); the base hash and the ancestor check.
- [ ] Every new declaration with its role: the setup lemmas, **the one round lemma**, the loop
      instantiation, the composition, the window ledger.
- [ ] Any change to `b2b_search_contract`'s statement, or to `b2b_host_contract`'s body
      (rule 2), old and new.
- [ ] Question 5's five obligations, one line each, with the discharging lemma. Include the
      count argument for overflow.
- [ ] Imports unchanged; appendix and status update, flagged; escalations, or "none".
- [ ] Duplication: both screens, in-file pairs justified, "new copies: none".
- [ ] File size and declaration counts; the final sweep tail; the re-run probe; the axiom prints
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
