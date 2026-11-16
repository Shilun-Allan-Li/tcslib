# Subagent c: generic receiver statistical output switch

Source `TCSlib/Cryptography/SecureComputation/Yao/HybridProof/BobStatistical.lean`. Namespace `...YaoHybridProof.BobStatistical`.
77 lines,width<=100,1 public/2 stored theorem. No definitions,admissions,
new simp attributes,actual protocol imports or frozen-file changes.

## Contract

statClose_real_output_switch is generic over G,H:HybridProtocol G,F and the
sender coin polynomial p. It takes the explicit H.main.P.coins=p reader,
a canonical Fin(p.eval n) BadWord probability bound, and the actual outP
correctness equation outside that word event. It concludes uniformly in n,x,y
that H.realB is StatClose at delta(n) to Bob's unchanged actual encoded view
paired with the prescribed Alice output.

No two-move,OT-specific,matching functionality output,or Bob-coin-length
premise is imposed. The independent Bob tape can have arbitrary length.
Security parameter zero and zero-length tapes are included by the types.

## Reuse and overlap

The proof first invokes the existing realB_output_switch. The remaining
canonical-to-actual bound uses uprob_fst,Strategy.coinLen_eq,hCoins,
strategyTapeEquiv/ofFn and uprob_comp_equiv. No probability measure,finite
sum or inequality is re-proved. No strategy,protocol or output sampler is
redefined. Foreign definitions are consumed only through their public readers.

Root requested extraction from its checked concrete working probe
evidence/probes/BobOutputSwitchGlue.lean (lead reference SHA256 60502b9e989fce22f3cc7bfe2a7bc0bb55e5e2146bfc950904f901a739a66f78).
AliceStatistical's local tape-normalization calculation was also consulted;
the same public strategy-tape/marginal APIs are composed for the Bob output
switch. No inaccessible probability lemma is copied or generalized.
SimulationBound source+matching olean was seeded by root, source SHA256
e67691de21816836b721c4841bbef451e6f891ab0aed7356cf74df5a4684f676,
with the seed ledger retained in lead evidence/logs/.

This is a new generic consumer contract of the existing probability APIs,
not an additional sc-garble/sc-compose/#318 general re-derivation.

## Verification

Normal01 PASS; style-lint-01 reports0findings. All four whole-file strict/coe
by evalA/B seals PASS with -DmaxErrors=0. Axioms-01 enumerates all2
stored constants: standard axioms only; the main closure has12565 constants,
and every stored closure has sorried=[].
Both error forms counted; every source/log/probe/manifest retained.

Source+matching olean API snapshot is byte-identical to final source:
/private/tmp/sc-yao-c-bobstatistical-api-normal01-resume3/.
Seal tools are the provenance-recorded c/gate-step-cases runners with path
changes only. Root reruns final merged checks. No child commits.
