# seq-zk-c soundness work log

Issue base: `107f1e8c218733eac12d6b9bee6fece441271317`.

Read policy.md and issued brief and both addenda. No Lean or Lake process started.

Initial searches:
- `rg -n "exists_proverCoins|uprob.*prod|uprob.*equiv|uprob.*fst|uprob.*snd|sound.*rep|Sound.*rep|seqRep" TCSlib/Cryptography TCSlib/InformationTheory`

## Searches before execution-prefix declarations

- Searched TCSlib for `exec.*(IsPrefix|take)|IsPrefix.*exec|take.*exec`: no matching general
  interactive-execution reader. An unrelated WordRAM execution was excluded.
- Searched Lean 4.25.0 `Init/Data/List`: reused `List.prefix_append_of_prefix`,
  `List.prefix_rfl`, `List.prefix_iff_eq_take` instead of re-proving prefix algebra.
- Searched the lead Mathlib clone at HEAD `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`
  using `git grep` because cache checkout was in progress:
  `exec.*(IsPrefix|take)|IsPrefix.*exec|take.*exec` under Mathlib/Data/List and
  Mathlib/Computability. No applicable interactive-execution theorem found.
- `prefix_iff_eq_take|IsPrefix.*take|prefix_append` under Mathlib/Data/List found
  `Mathlib/Data/List/Infix.lean:41` (prefix monotonicity of take), not needed because the core
  characterization gives the exact recovery equations directly.

## Overlap and reuse

- `Composability.exec_prefix` is a new iteration consequence of the published `exec_succ`
  reader at `TCSlib/Cryptography/ZeroKnowledge/Interaction.lean:266`; it does not restate an
  existing execution-prefix result. It directly reuses core List prefix transitivity through
  `List.prefix_append_of_prefix` (`Init/Data/List/Sublist.lean:706`).
- `exec_fst_take` and `exec_snd_take` specialize core `List.prefix_iff_eq_take`
  (`Init/Data/List/Sublist.lean:1315`) to the two execution histories. They publish the
  execution-specific interface requested by the lead; proof is direct reuse.
- Promotion request: the three generic execution-prefix readers belong beside `exec_succ`
  in `ZeroKnowledge/Interaction.lean` at a future shared-file window. This fill keeps them in
  its permitted helper module without editing that frozen file.

## Draft status

Wrote Soundness.lean's three complete declaration bodies. No Lean process has run: waiting
for the lead's package/bootstrap authorization. These declarations remain unverified drafts.

## Adaptive soundness helper

Added the complete but uncompiled draft `uprob_adaptive_all_le`. Search first:
- TCSlib `uprob_and_le_mul|uprob_adaptive_escape`: found and directly reused
  `OneWay.uprob_and_le_mul` at `OneWayFunctions/Basic.lean:90`.
- Mathlib pinned source `prob.*(prefix|adapt)|adaptive.*prob|prob.*pi` under
  `Mathlib/Probability/ProbabilityMassFunction` and `Mathlib/Probability/Kernel`:
  no applicable finite uniform adaptive-rate theorem.
- Mathlib `snocEquiv` search: reused `Fin.snocEquiv` at
  `Mathlib/Data/Fin/Tuple/Basic.lean:701`, rather than duplicating the private equivalence.

Overlap disclosure:
- `uprob_adaptive_all_le` generalizes `ThreeColoring/Protocol.lean:307`
  `uprob_adaptive_escape`, from challenges in `Fin m` with escape rate `1-1/m` to an
  arbitrary finite type and arbitrary nonnegative rate. The existing theorem cannot supply
  the exact frozen bound `s^Q` for a general error function `s`.
- Its local prefix equalities re-derive the cast arithmetic of private
  `challengesBefore_snoc_castSucc` (`ThreeColoring/Protocol.lean:275`) and private
  `challengesBefore_snoc_last` (`:286`) for a general finite type and explicit restriction.
  Those lemmas are private and specialized to `Fin m`; no private lemma was copied or
  referenced. The proof uses core `Fin.ext` and published `Fin.snoc_castSucc`.
- No new host or definition is introduced. Promotion request: the generic adaptive bound
  belongs in `Foundations/Probability.lean` or `HardcoreBit/Basic.lean` at a shared-file window.

Direct Mathlib imports `Mathlib.Data.Fin.Tuple.Basic` and `Mathlib.Tactic.Ring` are both already in supplied roots.txt.

## Compilation attempts

- Attempt 01: slot wait from 09:10:07 UTC; checker finished 09:11:14 UTC, exit 1. Syntax error: `prefix` is reserved, renamed binder to `pre`. Removed unused `if_false` simp argument. Max RSS 2,129,903,616 bytes. Raw log check-01.log retained.

- Attempt 02: exit 1, two dependent-function inference errors in local `Fin.snoc` prefix equalities. Added explicit codomain ascriptions `Fin (q + 1) → α`. Max RSS 2,143,354,880 bytes. Raw log check-02.log retained.

- Attempt 03: exit 1, simplifier did not match the dependent prefix functions. Introduced explicitly typed intermediate phase propositions before rewriting the prefix equalities. Max RSS 2,143,535,104 bytes. Raw log check-03.log retained.

- Attempt 04: exit 0, no errors or warnings. The helper emitted a fresh olean. Max RSS 2,152,775,680 bytes. Raw log check-04.log retained.

## Checked delivery status

All four new theorem declarations compile without admissions. The final source has 163 lines, maximum width 94, SHA-256 `71f0a20ff0b94ff6e064238cf6c4c105ceb68f856419e2ec37d61f695f29e653`.

The lead supplied APFS clones of the first 209 baseline modules into this worktree’s own `.lake/seq-zk-c-oleans`. `.lake/packages` links read-only to the lead package tree. No Lake command was run by this sub-agent. Every Lean invocation held a slot through the shared wrapper, with `LEAN_SLOT_TAG=seq-zk-c`; slot records are included. Host cap: at most three Lean processes across all jobs.

Exact invocation for all four attempts:

```sh
LEAN_SLOT_TAG=seq-zk-c TCSLIB_OLEANS=/Users/seyoonr/.codex/worktrees/seq-zk-c/tcslib-exchange/.lake/seq-zk-c-oleans /private/tmp/seq-zk-lean-slot.sh /usr/bin/time -l bash scripts/lean_check_tree.sh TCSlib/Cryptography/Composability/SequentialZK/Soundness
```

The lead must run the final merged-branch sweep, axioms, seals, and lint as required by the brief.

## Checkpoint 1 read-only review

The lead asked for a read-only review of its checkpoint 1 snapshot. No owned-file edit was
made. `checkpoint1-review.md` records the declaration-level review and API checks. No
mathematical obstruction or definite Lean failure was identified by inspection.

## Prefix-hardwired prover and offset execution

After approving the proposed interface, the lead assigned a NEW helper `Phases.lean`,
importing the stable Soundness helper. The new public construction `prefixProver` fixes
an earlier received history, auxiliary input and prover tape; generated `coins` and `next`
readers expose its zero coin polynomial and append contract. The new theorem `exec_phase`
identifies any corresponding segment of the full execution, under the mover and verifier
reply hypotheses, with a run of this prefix-hardwired prover. No owned definitions are
imported or unfolded. The optional bounded verifier-congruence theorem remains a design
proposal only and has not been added.

Overlap and promotion:
- `prefixProver` is a fixed-tape/fixed-prefix strategy wrapper. The nearest owned wrapper is
  `Protocol.seqProver`, original `SequentialZK.lean:200`; the latter slices prover coins and
  drops earlier received messages, while this one fixes the original tape and prepends
  earlier received messages. It does not restate that construction. No equivalent public
  wrapper was found by the recorded searches for `hardwir`, fixed tape, prefix strategy,
  zero-coin strategies, and prover next-message append calls.
- `prefixProver_coins` and `prefixProver_next` are generated field readers of this new
  construction, not re-proved foreign readers.
- `exec_phase` shares the induction architecture of the owned honest-run
  `Protocol.seqRep_exec_phase` (`SequentialZK.lean:280` at issue base), but applies to any
  prover and any two verifier strategies under an explicit real-phase contract. It uses
  only published `exec_zero`/`exec_succ`, generated prefixProver readers, and core List
  append/drop equations. No proof block or private declaration was copied.
- The nearest other general execution comparison is public
  `LevinTransfer.exec_congr` at `ZeroKnowledge/NPLemmas.lean:88`; it compares whole runs
  from empty histories under equality on all histories. It cannot supply an execution
  segment with fixed nonempty earlier histories. It is outside the supplied bootstrap
  closure and is not imported.
- Promotion request: prefixProver and exec_phase belong beside the interactive-execution
  API in `ZeroKnowledge/Interaction.lean` at a shared-file window. The permitted helper
  retains them for this fill.

Phases check history:
- Attempt 01: exit 1 with one unresolved false-mover branch. The branch retained
  `if false = true`; adding the public Bool false-equality and if-false simplification
  closed it. Max RSS 2,147,205,120 bytes. Raw log retained.
- Attempt 02: exit 0 with 0 errors and 0 warnings, fresh olean produced. Max RSS
  2,154,381,312 bytes. Raw log retained.

Final Phases.lean: 96 lines, maximum width 94, SHA-256 `22d94a4e178f0a0f34b4fabb3609a7ca33a171a9e38cf275d8dcf0e79e33a9e2`. No admissions.

## Congruence along the reached source histories

The lead assigned a NEW `Congruence.lean` for checkpoint 2 tape nonanticipation and later
ZK. It imports only `ZeroKnowledge/Interaction.lean` and introduces the public theorem
`exec_congr_reachable`. Its hypotheses compare replies only at active positions before
`g`, on each source execution's actual received history; prover and verifier tapes may
both differ. The conclusion is equality of the complete executions after `g` moves.
It uses only published `exec_zero` and `exec_succ` readers and public Bool equalities.
No previous helper source was changed.

Overlap and promotion:
- Nearest relative: public `LevinTransfer.exec_congr`,
  `TCSlib/Cryptography/ZeroKnowledge/NPLemmas.lean:88`. That theorem permits different
  inputs but requires each party's replies to agree on **every** possible history.
  The new theorem has a weaker reached-history premise at a bounded number of moves,
  and identical common/auxiliary inputs. The published theorem cannot directly discharge
  this premise and is outside the supplied order closure. No existing proof block was
  copied; the standard induction is re-derived from the public execution readers.
- Searches for `exec_congr|exec_eq_of|next_eq_on|reachable.*exec|exec.*reachable` across
  TCSlib and for execution congruence/reachability under pinned Mathlib/Computability
  found no closer reusable theorem. Raw output is in congruence-searches.log.
- Promotion request: `exec_congr_reachable` belongs beside `exec_succ` in
  `ZeroKnowledge/Interaction.lean` in a shared-file window.

Congruence check attempt 01: exit 0 with 0 errors and 0 warnings, fresh olean produced.
Max RSS 1,549,713,408 bytes; raw log and structured result retained. The invocation used
this sub-agent's own olean tree and tag through the host-wide shared slot wrapper.

Final Congruence.lean: 68 lines, maximum width 94, SHA-256 `724fb756e96ac9f210b2a0f75dd9d403bddc2a0c226225a4ba01e9f284efcb56`; no admissions.

## Earlier verifier blocks determine the earlier transcript

The lead assigned NEW `VerifierPrefix.lean`. The public theorem
`exec_eq_of_verifier_blocks` accepts an arbitrary padded verifier, an arbitrary terminal
reply function, and a move-index recovery hypothesis on the actual source run. It proves
that agreement of verifier coin blocks below `j<q` gives equality of the full transcript
before move `2*k*j`, against the same arbitrary prover and fixed prover tape.

The zero-round case has no moves. In the positive-round case the recovered index gives
`2*received.length ≤ t+1`, excluding the terminal history `q*k` before the cutoff. The
phase index is below `j` by the public core theorem `Nat.div_lt_of_lt_mul`. Reusing
`exec_congr_reachable` and the supplied padded reply reader then identifies the runs.
The proof does not unfold any owned definition or the body of `coinBlock`; `dsimp only`
reduces the local `let idx` appearing explicitly in its own hypothesis.

Overlap and reuse:
- Directly reuses this sub-agent's published `Composability.exec_congr_reachable` in
  `SequentialZK/Congruence.lean:42`. No congruence proof is duplicated.
- The nearest owned construction reader is `Protocol.seqRep_exec_phase`, original
  `SequentialZK.lean:280`, which compares an honest phase with an original execution.
  That theorem neither handles arbitrary cheating provers nor compares two full verifier
  tapes, so it cannot give this nonanticipation statement.
- The lead's new `Protocol.seqVerifier_exec_first` handles phase zero against the original
  verifier; it also does not identify earlier transcripts for arbitrary two tapes and a
  phase cutoff. The new helper contains no copy of that proof.
- Specialized earlier transcript readers such as `GI.exec_vfirst_eq` in
  `ZeroKnowledge/GraphIsomorphism/SoundnessRep.lean:90` describe history-independent
  verifier messages. Here the underlying verifier may depend on its within-phase history,
  so that interface cannot be reused. No specialized proof was copied.
- The move-index arithmetic is supplied by the lead, not re-proved from a foreign count
  function. Core `Nat.div_lt_of_lt_mul` is directly reused rather than copied.
- The statement belongs to this fill's padded-phase helper layer; no frozen-file promotion
  or reader request is required for it.

Searches for coin-block execution/prefix and verifier-tape dependencies in TCSlib and
pinned Mathlib/Computability are recorded in verifier-prefix-searches.log. No equivalent
published padded-verifier nonanticipation theorem was found. No new Mathlib root was
added, and no earlier helper was changed.

VerifierPrefix attempt 01: exit 0, 0 errors, 0 warnings, fresh olean produced. Max RSS
2,170,912,768 bytes. Exact invocation, raw log, source audit, and slot lines are included.

Final VerifierPrefix.lean: 89 lines, maximum width 94, SHA-256 `6be4e9f9c220e9ba15798dc0b61bc9a7cafc5c9ea1ec62a673de7c2d5e26c7f7`; no admissions.

## Explicit soundness error and fixed-prefix section bounds

NEW `ErrSoundness.lean` contains three checked declarations:
- `InteractiveProofErr.uprob_accept_le`: for every no-instance and prover, acceptance
  probability is at most the stated error `s(|x|)`.
- `InteractiveProofErr.sound_nonneg`: the error is nonnegative at every no-instance length.
- `Composability.prefixProver_accept_le`: when the earlier received messages and original
  prover tape are hardwired, the acceptance probability over a fresh original verifier
  tape alone is at most `s(|x|)`. The wrapper's public zero-coin reader shows that every
  local prover coin string is empty. Published output/transcript equations, `uprob_prod`,
  and `HardcoreBit.uexp_const` then remove its unused coin coordinate.

Search and overlap disclosure:
- No `InteractiveProofErr` acceptance or nonnegativity bound was found by the recorded
  TCSlib/Mathlib searches. Nearest public relative is
  `InteractiveProof.exists_uprob_accept_lt` at `ZeroKnowledge/InteractiveProofs.lean:193`.
  It returns a strict bound for an existential negligible error; it cannot provide the
  frozen arbitrary explicit-error value `s`. The new acceptance proof adapts the same
  complement-of-rejection argument, directly reusing `uprob_mono`, `uprob_not`, and the
  public soundness field. This overlap is explicit; it is not a copied private theorem.
- `sound_nonneg` directly specializes the public Mathlib order equivalence
  `sub_le_self_iff` generated at
  `Mathlib/Algebra/Order/Group/Unbundled/Basic.lean:214`, using `uprob_le_one`. No order or
  probability fact is re-proved.
- `prefixProver_accept_le` specializes the new acceptance bound to the existing public
  prefixProver wrapper. Its marginalization is direct reuse of the uniform product and
  constant-average readers. It does not re-prove the generic uniform second-projection law
  (`HardcoreBit.pushesUniform_snd`, HardcoreBit/Basic.lean:210) or the averaging statement
  `Protocol.exists_proverCoins_le` (Interaction.lean:548).
- Promotion request: the first two generic methods belong in
  `ZeroKnowledge/InteractiveProofs.lean` at a shared-file window. The prefix-specific bound
  remains in this fill's helper layer. No frozen file was edited.

Diagnosed elaboration and authorized proof-debugging exception:
- Attempt 01 started 09:37:03 UTC, acquired its slot at 09:37:08, and was running rather
  than queued. The sub-agent initially inferred a slot wait from the empty buffered output;
  the lead corrected this status, and the process snapshot confirmed the running child.
- A read-only one-second stack sample showed active `evalCalc`/`elabCalcSteps` and deep
  `isExprDefEqExpensive` recursion in the probability calculation. Mac headroom measured
  by the lead was 6.438 GiB, above the floor; this was not E-RES.
- The lead explicitly authorized a graceful interruption under Seyoon's best-judgment
  exception. Its verbatim instruction is preserved in err-soundness-debug-authorization.md.
  The exact child PID96807 and parent96799 and full Lean command were re-verified before
  SIGINT. Only that child was signaled; no wrapper or other job was touched.
- The complete attempt source, raw checker output, process inspection, interruption record,
  and stack sample are retained. Lean exited130, checker exited1, and no olean was produced.
  It ran619.72s with maxRSS3,831,316,480 bytes. This was diagnosed proof debugging, not an
  elapsed-time timeout, resource shortage, or claimed proof failure.
- Replaced only the pathological probability calc with an explicit reader-based product
  proof. Attempt02 passed with 0 errors and 0 warnings, fresh olean, runtime6.63s,
  CPU1.43s, maxRSS2,164,834,304 bytes. No previous helper source changed.

Large raw diagnostic representation:
- Raw sample size145,047,604 bytes, SHA256
  `440251c95334e50dfb92d8140690daa5315ec081bb69b6135602a9ce0187deec`.
- Deliver the lossless numbered part `err-soundness-diagnostics-01.zip`, with its entry list
  and verification log. Its sole member is the complete original err-soundness-sample.log;
  streamed decompression was SHA256-checked byte-for-byte, with the original length.
- ZIP size1,916,631 bytes. The original raw local sample remains outside the payload at
  `.lake/seq-zk-c-raw-diagnostics/err-soundness-sample.log`. The completed sample was moved
  only after verified compression; no running log was moved. No raw bytes are omitted.

Final ErrSoundness.lean: 85 lines, maximum width 94, SHA-256 `4ada2d316efd3efd4d387dde0880b9360ea66fff55581b2535081dc09ac76705`; no admissions.

## General phase-coupling extension for the simulator worker

At the lead's request, added `exec_phase_of_moves` to Phases.lean with arbitrary local
strategies, auxiliary inputs and tapes. Each supplied active-move equation reads a local
party on the reached source history with its fixed old prefix dropped. The generic
induction proves both prefix-append history decompositions. The previous `exec_phase`
statement is unchanged and now applies this theorem; its prover premise follows from
`exec_prefix`, the public List prefix append equation, and prefixProver_next. Its sketch
was synchronized. There is only one phase induction; no duplicate proof was retained.

Overlap: the new theorem generalizes this same file's prior exec_phase, whose old source
and source audit are retained as phases-before-generalization files. The new generic
induction replaces that old induction; the old API is a direct published-theorem reuse.
No foreign or private proof was copied. This belongs beside the generic interactive
execution API at a shared-file window, extending the prior promotion request.

Phase generalization check01: exit0, no errors/warnings, fresh olean, runtime4.67s,
maxRSS2,155,839,488 bytes. Dependent ErrSoundness recheck: exit0, no errors/warnings,
fresh olean, runtime2.70s, maxRSS2,165,014,528 bytes. It is the only owned helper directly
importing Phases; the simulator worker was sent the exact checked signature and source
and will recheck its new consuming helpers in its own tree. Existing API preserved.

Current Phases.lean: 142lines/max94, SHA256`dcec347fe5aaf7407861a8248809c400c4d1f8ad85b6c6195bacd4a7261d13be`.

## Full generic explicit-error repetition engine

The lead approved the PaddedVerifierSpec interface before substantial implementation.
`RepeatedVerifier.lean` supplies the public proposition-valued structure and its two
phase readers. `RepeatedSoundness.lean` supplies the actual probability engine. Neither
imports or unfolds the owned SequentialZK module, and no target statement is weakened.

New declarations and formulas:
- `PaddedVerifierSpec π ρ x q p terminal`: the nine displayed coin/round/first-mover,
  padded-next, binary-terminal, actual-index, boundary-length, original-length, and mover
  periodicity properties. Every public field has a formula docstring in Lean argument order.
- `PaddedVerifierSpec.phase_exec`: both histories of a real phase equal their fixed earlier
  histories followed by an original-verifier execution against prefixProver.
- `PaddedVerifierSpec.phase_take`: taking the p real prover slots of a final phase history
  recovers that original-verifier history. The k=0 branch is explicit.
- Private `phaseTape` and `phaseTape_block`: table coins are read through the canonical
  FunFamily.blocks equivalence and its published ofFn reader.
- Private `zeroTail`: a finite table with prescribed earlier blocks and explicit all-false
  future blocks. Private `phaseGood`: original acceptance with its induced earlier
  received history and fixed prover tape. Private `phaseGood_section` specializes the
  checked prefixProver acceptance bound. Private `phaseGood_of_test` identifies actual
  phase tests using VerifierPrefix and phase_take.
- `PaddedVerifierSpec.outV_eq`: repeated output equals its terminal function on the
  complete source transcript, through public Protocol output/transcript readers.
- `PaddedVerifierSpec.accept_le`: original explicit error s gives aggregate acceptance
  probability at most s(|x|)^q against every prover.
- `PaddedVerifierSpec.sound`: the binary aggregate verdict gives rejection probability at
  least1-s(|x|)^q. The q=0 branch is explicit. No q-positivity premise is added to this
  helper, and the frozen owned statements retain their original hypotheses.

Overlap and reuse, including every restatement/specialization:
- PaddedVerifierSpec's fields package the owned equations as caller-supplied hypotheses;
  they are not new proofs or claims that an arbitrary protocol satisfies them. Nearest
  original SequentialZK.lean readers: seqVerifier/its generated readers at236;
  seqVerdict_eq at222; seqRep_rounds_eval at261 and seqRep fields at254;
  verifierMoveIndex_eq at117 and verifierMoveIndex_exec at182; exec_fst_length at153 and
  exec_snd_length at163 with countP_moverIsV at133/countP_not_moverIsV at143;
  proverMoves_eq at127; moverIsV_two_mul_add at128. They cannot be imported into a helper
  without a cycle; the lead instantiates each field from exactly these published readers.
- phase_exec directly reuses exec_phase, including its generic induction. Its nearest
  owned relative is honest-only seqRep_exec_phase (issue-base line280); the new reader
  permits an arbitrary prover and an abstract verifier specification. Its quotient and
  remainder arithmetic directly reuses the core Nat add-multiple division/modulo readers;
  it does not copy a private lemma or add another execution induction.
- phase_take directly reuses phase_exec, exec_snd_take and the supplied length readers.
  Nearest lead checkpoint1 reader: Protocol.seqRep_exec_phase_take at owned line478
  (source queried during this work); that theorem is honest-only and unavailable to the
  abstract helper. The new reader generalizes the final-phase restriction to every prover.
- Private phaseTape is a local string alias for (FunFamily.blocks q c).symm. Nearest alias
  is public GI.blocksEquiv at GraphIsomorphism/SoundnessRep.lean:207. Private phaseTape_block
  has nearest relative public GI.coinSlice_blocksEquiv at that file:224. It is not a copy
  of the latter's entrywise proof: it directly specializes the already-imported canonical
  FunFamily.ofFn_blocks reader (Asymptotic/Adversary.lean:277), using Equiv.apply_symm_apply.
  This canonical public reader is the reused interface; no GI implementation is duplicated.
- Private zeroTail has nearest public relative extendStream at
  Pseudorandom/Functions/LazySampling.lean:196 (inside the supplied closure). extendStream
  returns a stream on all naturals and uses Classical.arbitrary beyond its prefix. The new
  finite-table leaf uses the explicitly requested all-false fallback, including truncation
  if i exceeds q; extendStream does not publish that exact fallback. Mathlib Function.extend
  (Logic/Function/Basic.lean:686) is a choice-based extension along a map, not this explicit
  total finite-prefix/truncation leaf. The two-line conditional definition is disclosed;
  no existing extension theorem or private proof was copied or re-proved.
- phaseGood is a local predicate naming the original verifier/prefixProver test, rather
  than a new iteration host. phaseGood_section directly reuses prefixProver_accept_le;
  it merely substitutes the earlier transcript of the zero-tail table as its fixed prefix.
- phaseGood_of_test directly reuses exec_eq_of_verifier_blocks and phase_take. Its only
  extra table fact reads the prescribed prefix of zeroTail; Fin casts reduce by the core
  projection equations. There is no duplicated nonanticipation or phase induction.
- outV_eq's nearest lead reader is Protocol.seqRep_outV_eq, owned line453 when queried.
  The new theorem is the abstract-spec counterpart; it directly reads supplied rounds,
  first-mover, boundary, and next equations through published Protocol readers. It cannot
  import that construction-specific owned theorem without a cycle.
- accept_le directly reuses Protocol.exists_proverCoins_le (Interaction.lean:548), the
  canonical FunFamily.blocks equivalence/readers, VerifierPrefix through the phase-test
  reader, prefixProver_accept_le through phaseGood_section, and uprob_adaptive_all_le.
  Nearest specialized repetition proof is GI.gniRep_accept_le at
  GraphIsomorphism/SoundnessRep.lean:344, with its protocol-specific 2^-n+sampling-error
  rate. It does not supply arbitrary s or this abstract padded verifier; no proof was copied.
- sound uses outV_eq, the supplied binary terminal equation, OneWay.uprob_congr,
  uprob_not, and Mathlib sub_le_sub_left directly. The nearest specialized complement
  conversion is GI.gi_rep_efficientProverProofErr at SoundnessRepGI.lean:438. Its
  protocol-specific conclusion cannot supply this generic reader. No probability
  complement or order fact was re-proved.

Promotion/readers: PaddedVerifierSpec and these abstract padded-phase readers belong in
this topic helper layer. General prerequisites already carry the earlier Interaction and
InteractiveProofs promotion requests. No frozen-file edit, scope extension, private host,
new Mathlib root, or new simp attribute was introduced.

Validation history and resource evidence:
- RepeatedVerifier01: syntax cascade from reserved capital Π; changed the bound protocol
  name to valid ρ. RepeatedVerifier02: explicit first-mover projection case split was
  needed for the index arithmetic; fixed through if_pos/if_neg on its equality. Both raw
  failures retained. RepeatedVerifier03 passed spec+phase_exec. RepeatedVerifier04 passed
  the complete phase_take extension with0errors/0warnings, actual runtime2.87s,
  maxRSS2,194,358,272. Its slot wait was10:04:53–10:15:32 UTC, normal host contention;
  not a stall or E-RES.
- RepeatedSoundness01 found one local-notation simplifier mismatch. Attempt02 fixed the
  outer block but exposed the inner occurrence's local c alias. Attempt03 normalized that
  local proposition explicitly and passed the full engine with0errors/0warnings, fresh
  olean, runtime2.41s, maxRSS2,172,452,864 bytes. All raw logs and structured results remain.
- The full engine uses explicitly typed probability intermediates and public product/
  equivalence readers; no pathological dependent calc or proof-debug interruption occurred.
- Each check used this sub-agent's own olean tree and shared wrapper/tag. Source files
  remain below1000lines and100characters. The lead owns the final merged sweep, axioms,
  seals, lint, commits and delivery.

## Read-only NormalizedStep assistance

At the lead’s request, reviewed seq-zk-a NormalizedStep snapshots and the public Sampling/probability readers. No mathematical/domain flaw was found. Sent direct per-test scalar probability transport and explicit reader/motive recommendations, plus a core-source-checked immediate flushed IO marker proposal. Details and inspected source hashes are in normalized-step-readonly-review.md. No foreign edits, source copies, probes, Lean processes, checker runs, sampling, or interruption occurred in this review.

## Uniform advice selector and opaque statistical post-processing

At the lead's request, inspected the published NUPPT closure/advice APIs and nearest
ThreeColoring finite-selector/hybrid proofs. The initial finite-kernel alternative is
unnecessary: maximizing the finitely many real suprema over arbitrary witnesses gives a
selector independent of the eventual negligible bound. The lead approved that route.
The complete design and remaining concrete obligations are recorded in
computational-advice-design.md; exact raw API searches are in advice-postprocess-searches.log.

Advice.lean introduces only exists_uniform_bound_selector: finite nonempty metadata,
arbitrary witness type, and a common nonnegative upper bound yield a metadata value whose
nonnegative uniform witness bounds also bound every metadata/witness pair. The proof
directly reuses Mathlib Finite.exists_max, le_csSup, and csSup_le. The nearest existing
ColZK.exists_hidingView_bound (ColZKMachine.lean:323) selects among finite colour/advice
triples and has a specialized commitment conclusion; it does not supply the arbitrary
witness-domain implication. No proof was copied. Promotion request: place this generic
bounded-family selector in a future shared order/probability helper. New precise imports
Mathlib.Data.Fintype.Lattice and Mathlib.Data.Real.Archimedean were approved by the lead;
both pinned olean files were already cached, and the lead owns required roots/pin/cache
updates. This agent ran no Lake command. Check01 passed with0errors/0warnings, 1.69s actual
runtime and maxRSS1,466,220,544 bytes. The slot wait from10:55:20 to10:57:10 UTC was normal
host contention, not an elapsed-time diagnosis, interruption, or resource shortage.

NormalizedStep's concrete elaboration remained slow inside the raw test bound despite
explicit public-reader arguments. The lead and a requested an opaque generic helper;
StatisticalPostprocess.lean introduces only statClose_map_fst. Its pair-indexed fixed-point
hypothesis matches a's existing proof directly. The ignored product factor is explicitly
Nonempty, necessary for the uniform-probability projection law (and automatically true
for verifier coin function spaces even with zero bits). It directly reuses StatClose.map,
statClose_iff, OneWay.uprob_congr and uprob_fst. Searches found no combined public map/fst
law. Nearest laws are those four imported public readers; no statistical switch, uniform
product, or event congruence proof was duplicated. Promotion request: this general law
belongs in Asymptotic/Sampling.lean if accepted; that file is frozen, so it stays in the
approved topic helper. Check01 passed with0errors/0warnings, 2.19s actual runtime and
maxRSS2,110,701,568 bytes. Source/API/hash sent to a and lead for independent copying and
checking. No concrete protocol or NUPPT appears in the helper, and no NormalizedStep edit,
check, sample, or interruption was performed by this agent.

Both new source files are stable. Every own Lean-running command used the shared wrapper,
seq-zk-c tag, one module, and own olean tree. Full raw checks, source hashes, searches,
structured attempt results, and refreshed source/diagnostic audits accompany this record.
No new simp attribute, frozen-file edit, scope extension, admission, or target change.
