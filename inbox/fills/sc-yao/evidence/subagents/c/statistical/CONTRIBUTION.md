# Subagent c: statistical switch

`HybridProof/StatisticalSwitch.lean` has two generic contracts for same-coins
samplers agreeing outside a bad event. No definitions are added.

The dependency import
`TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.HybridLemmas` is outside the
issued184-module order. The lead requested its approval before this source was
written; user answer (verbatim): "Approve this probability-helper import".
Wait for the lead's dependency bootstrap seed before checking this module.

## Overlap and reuse

- `statClose_of_eq_off` specializes the existing public
  `MultiMsg.abs_uexp_sub_le_uprob` (`FromPRF/HybridLemmas.lean:61`) to zero-one
  indicators, then composes its probability bound with the given upper bound.
  It reuses `Sampling.lean:133` `statClose_iff` and `Probability.lean:81`
  `uprob_eq_uexp`. The only local proofs establish the trivial indicator ranges
  and transport pointwise equality through a test. No expectation/probability
  inequality is re-derived.
- `distAdv_le_of_eq_off` composes that specialization with the existing public
  `Sampling.lean:249` `distAdv_le_of_statClose`.
- Search of EnsembleLemmas and OneWayLemmas found related sampler/coin identities
  but no published same-coins/off-event `StatClose` interface. `search.log` records
  the searches, including the exact closest public coupling result.

This source is independent of Yao definitions and covers empty finite seed types.

## Verified result

StatisticalSwitch-02 passed with zero errors; the only repair reduced the local
indicator lambdas before splitting their if expressions. `dsimp only` performs
beta reduction here and names no TCSlib definition. Both stored theorem axioms
use only propext, Classical.choice and Quot.sound, and their transitive closures
report sorried=[]. All four A/B by strict/coe diagnostic whole-file seals pass.
Source length is 74, width at most100, and no source sorry.
