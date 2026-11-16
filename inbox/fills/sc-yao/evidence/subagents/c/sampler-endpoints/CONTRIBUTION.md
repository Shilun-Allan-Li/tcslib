# Subagent c: exact sampler endpoint transport

Source `TCSlib/Cryptography/SecureComputation/Yao/HybridProof/SamplerEndpoints.lean`. Namespace `...YaoHybridProof.SamplerEndpoints`.
238 lines,width<=100,8 source/10 stored constants,no definitions/admissions.

## Contract

The supplied real sampler is a parameter with its explicit encoded-view
equation. No real protocol/message/seed/hybrid is redefined. Four addressed
seed readers, fanin<=2 and C.size<=S identify the concrete complete-tape
relabeling. real_eq_stage0_on_tape composes the supplied real equation with
GateHybridMessage.sample_relabel and CoinSeedRelabel.seed_relabel.

acceptProb_real_eq_stage0 then invokes the published acceptProb_comp_equiv
on CoinRelabel.relabel. The equality holds for every randomized D.
acceptProb_real_eq_stage0_fst drops an independent ignored Bob tape by
acceptProb_fst. distAdv_real_stage0_zero is directly distAdv_def plus that
exact equality. All use the full Fin(10*S*n+2*S) tape and include n=0.

sample_end_of_result identifies the final stage with the canonical fake view
when wire-output values match the prescribed typed result.
acceptProb_end_eq_fake transports that pointwise equation.
acceptProb_end_eq_ideal accepts an arbitrary coin bijection and the ideal
sampler's explicit canonical fake-view reader, then reuses
acceptProb_comp_equiv. distAdv_end_ideal_zero is the direct distAdv_def
corollary. The prescribed Alice output is the outer second component.

Actual protocol view/answer equations, the initial correctness/off-Bad output
switch, actual functionality result consistency and the chosen simulator
coin-bijection reader remain lead instantiations. The interface does not
assume a complete real-to-hybrid or hybrid-to-ideal sampler identity.

## Reuse and overlap

Search first found Foundations.Experiments.acceptProb_comp_equiv/distAdv_def
and Pseudorandom.Indistinguishability.acceptProb_fst; these are used directly.
The neighbouring EnsembleLemmas.acceptProb_coins_equiv moves distinguisher
coins, while the present application relabels sampler seeds. No probability
measure, finite-sum argument, marginal law or change-of-coins proof is copied.
Pointwise function equality is transported by core congrArg/funext.

The only new mathematical content is the specialized composition of the
existing tape/seed and garbled-view equations. Prior CoinSeedRelabel SY5
disclosure covers the unmerged assignment-code fact; no additional unmerged
lemma is re-derived or imported here. The explicit real view occurs only as
a parameter hypothesis, following root's SY1 scope correction.

## Verification

Normal01 through07 all PASS. Final07 whole-file seals (4 evalA/B by strict/coe)
PASS with -DmaxErrors=0; the previous pre-documentation seals also PASS and
are retained separately. Axioms-01 enumerates all10 stored constants,
standard axioms only,every closure sorried=[]. Final07 style lint0findings.
The earlier style finding, source versions, all raw logs and both error-form
counts are preserved. Seal tools follow the provenance-recorded c/gate-message
runners with only evidence path changes. No frozen-file edits or commits.
Lead must run final merged checks.
