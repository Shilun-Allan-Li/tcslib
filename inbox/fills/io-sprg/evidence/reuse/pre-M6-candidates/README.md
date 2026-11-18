# Targets M6 proof candidates — NOT RUN

Read-only preparation against the managed io-sprg worktree, 2026-11-18. No
Lean/lake/build/cache, source edit, or git mutation was performed. Bindings are
in source-binding.json. Nine replacement bodies are staged for the nine
existing nonreader theorems of Targets.lean. Eight have no explicit placeholder;
one is deliberately PARTIAL with a single named M1 support gap. None has been
elaborated, axiom-checked, or seal-checked. No new statement/import is proposed.

## Candidate inventory and actual upstream dependencies

| Existing theorem | File | Reuse and dependencies |
|---|---|---|
| Params.realizable_of_targets | 01-realizable_of_targets.lean.txt | reductionTargets_iff; each preTarget_iff; shared exists_realizesOn_of_preTarget; kappaOf(_N)_le; advice length bounds; shared RealizesOn.congr plus named reduction readers |
| Params.evalEfficient_of_target | 02-evalEfficient_of_target.lean.txt | evalTarget_iff, SPRG.Raw.evalEfficient_iff, jlsSPRG_raw_eq, encPP/encSeed/encSeed'/PrimeParam encoding readers |
| Params.idSampEfficient_of_targets | 03-idSampEfficient_of_targets.lean.txt | coreTarget_iff, drawSamplerTarget_iff, shared drawSamplable_iff/coreComputable_iff, SamplesEfficiently.intro, record/word/prime readers |
| Params.sdSampEfficient_of_targets | 04-sdSampEfficient_of_targets.lean.txt | same shared contract; specialize seed parameter to (pi(kappa),I); also encSeed'_eq |
| Params.lpnSamplerEfficient_of_target | 05-lpnSamplerEfficient_of_target.lean.txt | lpnSamplerTarget_iff; SamplesEfficiently.drawSamplable/coreComputable; shared iff readers and intro |
| Params.hasComplexityEff_of_target | 06-hasComplexityEff_of_target.PARTIAL.lean.txt | qGenTarget_iff, HasComplexityEff reader, explicit G4 witness, G4_degrees; M1 specific-G4 support equality remains one explicit sorry |
| theorem41_of_targets | 07-theorem41_of_targets.lean.txt | raw theorem41, realizable_of_targets, hasComplexityEff_of_target; primitive property readers and jlsSPRG_toRaw |
| exists_sprg_of_targets | 08-exists_sprg_of_targets.lean.txt | choose E=max1(E0); theorem41_of_targets; exact scheduled modulus via toRaw and jlsSPRG_raw_modulus |
| exists_sprg_of_targets_subexp | 09-exists_sprg_of_targets_subexp.lean.txt | choose same E; raw theorem41_subexp; M6 realisability/complexity; SPRG.adv_eq and toRaw transport the SAME SubexpHard predicate |

Each staged file contains exactly one tactic block. All lines are at most100
characters (actual maxima84–98). Insert only the replacement body, preserving
the existing source docstring and proof sketch. Candidate1 and9 exceed15 lines
and depend on the existing source sketch; root may add local step comments
when landing the proof without changing its statement.

## Shared contract restriction, not a new sampler

The contract has no public parameter-restriction/contramap lemma. Searches for
restrict/reparam/contramap on DrawSamplable, CoreComputable and
SamplesEfficiently found none. A new generic substitute is unnecessary:

1. Read coreTarget/drawSamplerTarget and select the appropriate conjunction half.
2. Normalize the parameter word (and seed encoding for the seed sampler) through
   published equation lemmas BEFORE unpacking dependent sampler witnesses.
3. Read DrawSamplable with drawSamplable_iff and CoreComputable with
   coreComputable_iff. This gives U,c,e,he,hfail and f,hf,hcore.
4. At the fixed schedule, retain EXACTLY U,c,f. Restrict e/he/hfail/hcore to pp=pi
   for the index core, to q=(pi,I) for the seed core, or to pi for the LPN core.
5. Repack the two hypotheses through the shared iff readers and
   SamplesEfficiently.intro. No product sampler, UniformSampler record literal,
   machine construction, new coin layout, failure estimate, or choice equivalence
   is introduced. Reusing an existing quantified witness is not constructing one.

No target itself is proved here. These theorems only turn the supplied Phase B
hypotheses into the required fields of the already defined primitive assembly.
Uniform witnesses remain chosen before all parameters. Schedule specialization
does not compute a prime or hard-wire one into an honest machine.

## Dependent record transport

The candidates read jlsSPRG_raw through its published FULL record equation
before simplifying type-indexed projections. This avoids attempting to silently
reduce a foreign raw bundle while its constants are sealed. All other foreign
definitions are read through _eq/_iff lemmas. Core/Mathlib definitions are not
passed to simp/rw/unfold. Word/encoding normalization uses equation lemmas only;
no simp attribute or global attribute is introduced.

The most likely untested elaboration adjustments are dependent record rewrites
and simplifier normalization of the two width expressions kappa+1+1 vs kappa+2.
Those are honest NOT_RUN concerns, not a reason to claim a successful proof.
The witnesses/quantifier order are fixed; if Lean needs explicit argument types,
add those to the candidate rather than unfolding a foreign definition.

## Realisability link: exact public API shape

Candidate1 specializes one fL/fG to the supplied schedule, then calls
Complexity.NUPPT.exists_realizesOn_of_preTarget with:

- phi=P.kappaOf or P.kappaOfN;
- p=PolyExpr.var, with bound from the existing inverse-map lemma and eval_var;
- EXACT named challenge encoders and advice encoders;
- EXACT lpnPre/prgPre maps and their target equations;
- the supplied arbitrary advice family and published polynomial advice bound.

The helper returns the runAtL/prefix function. Shared RealizesOn.congr and the
named lpnRed_eq/prgRed_eq identify it with the desired reduction. The congruence
proof is valid on every coin string, hence in particular on the shared layout
length. No private realization predicate, bare computes witness, explicit Turing
machine, or unconditional realisability assertion is added.

The advice-length and inverse-map lemmas are genuine named upstream obligations;
they are still sorried at M0. Candidate1 therefore depends on their eventual
proofs even though its own staged body has no explicit sorry.

## The one deliberate M1 gap

HasComplexityEff must generate the SPECIFIC polynomial G4 from the term list.
Existing jls_hasComplexity only states existence of SOME witness Q, so its
existential cannot be silently identified with G4. Candidate6 chooses G4
explicitly and leaves only its seed-support evaluation branch unfinished.

The needed mathematical bridge is:

  (P.sdSamp' kappa pp I).AllOutputs (fun sd => forall j,
    ((P.eval' kappa pp I sd j).toNat : ZMod pp.p) =
      MvPolynomial.eval (Sum.elim sd.1 sd.2) (P.G4 kappa pp I j)).

Derive this in M1 from the same explicit full core law and G4_eval_sdCore/
G4_eval_eq plus eval'_correct, then project through sdSamp'_eq. The existing
OracleComp.AllOutputs.mono/bind and pure/query readers suffice for support
transport. Search found no AllOutputs.and helper in the allowed Games files;
allOutputs_bind_iff is in the explicitly FORBIDDEN Games.Closeness module and
MUST NOT be imported. A deterministic draw-level route avoids needing it.

This is an implementation dependency, not a false existing theorem or request
to weaken the statement. The gap is clearly labeled and is the only explicit
sorry in these staged bodies.

## Reuse searches and probes

Read the shared Contract.lean definitions/readers/closure in full. Text searches
in TCSlib and pinned Mathlib for the target theorem names found only these
owner declarations/call sites, not another public target assembly theorem.
Parameter restriction searches and allOutputs shape searches are documented
above. Mathlib is the job's pinned029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e.
No new generic helper is proposed, and the construction does not reprove an
existing shared contract/realisation lemma.

Public API source locations:

- CoinSampling/Contract.lean:96 drawSamplable_iff;113 coreComputable_iff;
  162/169 SamplesEfficiently.drawSamplable/coreComputable;176 .intro.
- Asymptotic/Realization.lean:157 RealizesOn.congr;220
  exists_realizesOn_of_preTarget. The return type is the shared RealizesOn.
- StructuredSeed/Defs.lean:320 raw eval efficiency reader;363 efficient
  complexity reader;409/426/434 primitive Secure/HasComplexityEff/HasPolyStretch
  readers;441 primitive advantage reader.
- StructuredSeed/Samplers.lean:398 full jlsSPRG_raw_eq and individual
  type/algorithm/encoding/width readers. No direct unfolding is proposed.
- Games/OracleComp.lean:297/303 allOutputs_pure/query,316 AllOutputs.mono,
  324 AllOutputs.bind (the argument order should be read when filling the M1 gap).

Root exact?/apply? probes are still pending on ALL nine existing statements.
Use a temporary owner-body replacement so search cannot find the same imported
sorried theorem as a spurious solution. The reusable probe body templates in
../SparseFactor/probe-exact.lean.txt and probe-apply.lean.txt can be used one at
a time. Do not report candidate text as an elaborated or sorry-free theorem.
