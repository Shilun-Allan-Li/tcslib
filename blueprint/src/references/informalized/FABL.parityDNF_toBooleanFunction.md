<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.parityDNF_toBooleanFunction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity DNF represents parity

**Claim.** For every natural number $n$, the Boolean function represented by the minterm DNF of parity on all $n$ coordinates equals parity on all $n$ coordinates.

**Proof.** By definition, the parity DNF is the minterm DNF applied to the parity function on all coordinates. The minterm DNF representation property says that this DNF represents its input function (FABL.mintermDNF_toBooleanFunction), which gives the asserted equality.

**Key facts.** `FABL.mintermDNF_toBooleanFunction`.
