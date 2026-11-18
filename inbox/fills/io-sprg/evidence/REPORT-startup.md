> Historical pre-source/pre-ruling snapshot. Superseded by the active REPORT.md.
> The source folder/hash and SP-W1 are resolved; source and Lean work have proceeded.
> Retained only to preserve the original mathematical obstruction and proposed options.

# io-sprg startup status (pre-M0; incomplete)

E-ROUTE review requested: the intended T5 target is unattainable for some allowed arbitrary-real noise exponents. The source folder is also not specified in the dispatch, so source verification and paper-dependent work are pending.

**Not yet ready for the statements gate — no Lean declarations have been written.**

## Bases and milestones

- Lean base and current fill/io-sprg head: 5ed465f62e4ae0f93ded1a1ba49e807591b589eb.
- Records reviewed: dbea2807532392781304e004715f3b0190025f5e.
- Host inputs: bc9d982b83cb35ea351e2fb373752e8688945b1c.
- Rule 10 tools: 2467bc3befdad8472b1f359337bf3a203e3651e1.
- Own worktree: /Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange.
- M0-M6: not reached. No implementation commits, exchange commits, or axiom prints.
- No exchange push: the first-push M0 condition has not been met.
- Evidence is untracked in the fill worktree. No PDF has been read, copied, committed or pushed.

## Source

The dispatch names jls26.pdf and its expected SHA-256 but supplies no folder path. A question asking for that path is pending. This is not a finding that an identified file is absent or mismatched. No source hash has been recorded because no source file has been identified.

## Host

Both pinned host hashes match; see logs/host-hashes.json. Initial headroom was 4,207,099,904 bytes = 3.918167 GiB, below the 4 GiB floor. Disk was 102,809,427,968 bytes = 95.748741 GiB, above the 12 GiB floor. Hardware: 12 CPUs, 18 GiB RAM. Initial sample: 2026-11-18 08:48:10 UTC. No Lean or cache command has run. The first delayed remeasurement PASSED: 4,690,444,288 bytes = 4.368317 GiB. It is recorded in logs/preflight-retry-1.log; no Lean/cache has run. The initial sample alone is not represented as exhaustion of the host retry schedule.

The host cap is three Lean processes across all jobs; this job holds at most one. All future Lean/lake/probe/seal invocations must use the exact pinned lean-slot.sh and LEAN_SLOT_TAG=io-sprg. The narrowed cache fetch alone holds three slots. No package tree has been fetched or reused.

## E-ROUTE: arbitrary-real exponent and T5

This is a mathematical obstruction to the intended design, independently reviewed by both review agents, not a claim about already-authored Lean declarations or a source-fidelity audit. It uses the specified one-draw type, an injective explicit draw encoding, and the intended parameter word containing only pp and the index.

The obligation is P.drawSamplerTarget for every P : Params, where Params permits every real delta in (0,1), and w(k) = max 1 floor((k^E)^(delta/2)), W(k)=w(k)^2. In particular, the proposed existence hypothesis forall P : Params, P.Targets would imply this T5 obligation for all such deltas.

Choose E=d=D=1 and an allowed Boolean PRG whose index/draw is Unit and whose output length is zero. Its evaluation and multilinear representation are trivial; Params does not require stretch. For k>=1, ell=n=k, m=0, B=1 and Gamma=0. Choose the zero matrix/index and a computable prime schedule (unbounded prime enumeration is used only in this meta-level counterexample, not as an honest algorithm). The encoded parameter word is then computable and independent of delta.

The specified seed draw is

    (Fin k -> Bool) x
      (Fin k -> (Fin k -> ZMod p) x (Fin k -> Fin W x ZMod p)),

so its cardinality is

    2^k * W(k)^(k^2) * p^(2*k^2).

Suppose T5 held. Its fixed polynomial c and UniformSampler.raw give a computable procedure: enumerate every c(k)-bit string, run raw on its prescribed layout, and count distinct nonfailure output strings. Failure <= 2^(-k) < 1 and exactness on success ensure that every draw appears. Encoding compatibility and injectivity therefore make this count exactly the cardinality above. Integer division and roots recover W(k), and then w(k), for every k>=1.

This would compute delta. To see an effective error bound using only integer logarithms, let k=2^q and L=floor(log2(w(k))). Since w(k)<=k^(delta/2)<w(k)+1<=2*w(k),

    2*L/q <= delta < 2*(L+2)/q.

Taking q=2^(N+3) yields an explicitly computable interval of width 2^(-N-1) containing delta. Thus delta would be computable. Choosing a noncomputable delta in (0,1) contradicts T5.

This does not refute the raw security inequalities or a conditional theorem under P.Targets. It shows that the intended universal target hypothesis cannot be inhabited for the full proposed Params type. No finite-time or polynomial-time lower bound is needed; computability already fails. Supplying a noncomputable w schedule in the parameter word would alter the intended honest-input contract and is not adopted silently.

### Proposed minimal repair (SP-W1)

Recommended: retain analytic delta : Real, add rational rate data a with 0<a<=delta, define w using a/2 (with an exact integer-root formulation available for Phase B), use the same a in the construction LPN family, and state the free schedule-exponent threshold E0 in terms of a. This preserves arbitrary analytic delta and the safe direction 1/W >= ell^(-delta). Claim 4.2 still has a positive fixed exponent; its eventual threshold remains uniform in pp. Every affected rounding, parameter, target, and stretch statement would be disclosed before M0.

Alternative: restrict delta itself to rational data (coerced to Real for analysis). This is a smaller interface but narrows the stated parameter range.

No repair has been implemented pending the ruling requested by the dispatch's E-ROUTE rule.

## Other design refinement

At k=0, rc=k*w=0. The proposed total indexMap : Fin m -> Fin rc x Fin rc cannot exist when m>0, which BoolPRG permits at n=0. Use Option (Fin rc x Fin rc), with none on overfull buckets, and express the correction polynomial as a coordinate sum. This preserves the settled rc/cap rounding and the good-case statements. This is a refinement of a proposed helper shape, rather than a weakening of a headline theorem.

BoolPRG's sampler efficiency must be tied to its actual law through IdDraw/idCore with derived idSamp or an equality field. T5 targets the entire product draw; no product UniformSampler is built in Phase A.

## Rule 10 preparation

The pinned 24-file suite is prepared under tools/. Only runner_full.py changed; its header records every host-path change. Static syntax checks passed for 21 Python files and two shell drivers. These are preparation checks only, not Lean seal/control results. No Lean ran. The Linux pool runner and BB1-specific control generators are not usable as io-sprg verification. New control rows must be authored after the definitions exist. Detailed provenance and caveats are in tools/EXTRACTION.json, tools/SYNTAX-CHECK.json and the runner header.

## Statement changes; deviations; overlap and reuse

No statements are frozen or changed; M0 does not exist. No helper has been proved or re-proved. Required APIs and module inventory are recorded in review/design-audit.txt. Proposed repairs above are disclosed, unapplied, and require resolution before final definitions. The helper-search, fidelity, rule-15, non-vacuity, size, build, axiom and gate tables remain pending implementation/source access.

## Open questions

- Source input: provide the local folder containing jls26.pdf.
- SP-W1: recommended rational minorant rate data while retaining analytic delta; alternative rational delta only.
