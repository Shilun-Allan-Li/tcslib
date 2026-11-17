<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.SAT_reducible_SAT3 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Reduction from SAT to three-SAT

**Claim.** For a width-$w$ CNF of size $s$, with $w\ge 3$, the stated construction yields an equivalent width-three CNF of size at most $(w-2)s$, using the original variables and at most $(w-3)s$ auxiliary variables.

**Proof.** Use the reduction function `satReduction`. Its polynomial-time computability is established by `satReduction_poly`, and `satReduction_correct` says that an input belongs to SAT exactly when its image belongs to three-SAT. Together these facts give the polynomial-time many-one reduction. The stated size and variable bounds are properties of the construction; they are not separately established by the two upstream facts supplied here.

**Key facts.** `Complexity.satReduction_poly`, `Complexity.satReduction_correct`.

**Caveat.** The supplied proof and upstream statements establish polynomial-time reducibility and preservation of SAT membership, but do not state or prove the specific size and auxiliary-variable bounds in the informal statement.
