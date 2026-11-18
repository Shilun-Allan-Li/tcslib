# Diagonal-gap local hGood candidate

Status: scratch proof-only fragment, checked by inspection; native verification pending.
No Lean/lake/build/Git/live edits/extra agent were run. Exactly one tactic block, four-space
body for the existing outer skeleton's two-space haves. No remaining hole/sorry in THIS
fragment. The main skeleton and exact searched theorem header/prose are untouched, and its
hBadMass remains explicitly admitted. No complete diagonal-gap or standard-only claim.

Paste this fragment at the existing local target:

  hGood : forall ab : Fin 2 -> K, ab 0 != 0 -> ab 1 != 0 -> A ab = B ab

It uses precisely the existing local A/B/H/K and its bound coordinate parameters. H's range
bounds, bad event and hBadMass are not used in good-law equality.

## Existing equivalence composition

scale is assembled from already-published Equiv objects:

Fin2->K --finTwoArrowEquiv--> K×K
        --prodCongr(mulLeft₀ ab0 ha0)(mulLeft₀ ab1 ha1)--> K×K
        --finTwoArrowEquiv.symm--> Fin2->K.

Thus each used diagonal multiplication is a permutation because its supplied scalar is
nonzero. No hand-built inverse or sampler is defined. e applies scale to the first component
of (Fin2->K)×K and then uses (Fin.succFunEquiv K 2).symm to append the last coordinate.
Its image is the exact vector [ab0*rs0,ab1*rs1,t].

hShape checks the THREE canonical Fin3 coordinates, using fin_cases then rfl. This reduces
only Mathlib/core Equiv/finite-vector constructions and local aliases in the explicitly
permitted reflexivity step. No core/Mathlib or foreign TCSlib definition is passed to
simp/rw/unfold, and no generated defining-equation reader is used. It avoids relying on
uncertain generated simps names for the composed finite equivalences.

Reverse expect_sample_equiv transports the uniform Fin3 average to the uniform pair draw
along e. Reverse Bridge.expect_sample_pair and existing expect_bind/expect_pure read that
pair as the two independent draws already present in B. hShape identifies their output;
reflexivity closes. This reuses the shared product-sampling law rather than duplicating
finite-average/cardinality/Fubini proofs.

## Precise imports for root to check

The three potentially needed precise API roots are:

* Mathlib.Algebra.GroupWithZero.Units.Equiv (Equiv.mulLeft₀).
* Mathlib.Logic.Equiv.Fin.Basic (finTwoArrowEquiv, Fin.succFunEquiv).
* TCSlib.Cryptography.Games.Bridges.Experiments (Bridge.expect_sample_pair).

The fin_cases tactic's precise root is Mathlib.Tactic.FinCases if it is not already in the
installed Diagonal module's import closure. This path was verified statically with rg --files.
No import/live source change was performed by this agent. None of these is Games.Closeness,
CoinSampling, or a sampler/machine-construction module.

## Actual static searches/read inspections this invocation

Read the exact searched target and the complete local diagonal skeleton. Queried finite tuple,
succFunEquiv/piFinSucc/appendEquiv and coordinate-apply reader names in Mathlib Equiv/Fin.
No existing finThreeArrowEquiv was found. Read Logic/Equiv/Fin/Basic.lean:42-53 and :404-420,
GroupWithZero/Units/Equiv.lean:19-36, and Logic/Equiv/Basic.lean:140-153.

Searched existing uses of Fin.succFunEquiv/finTwoArrowEquiv and Equiv.mulLeft₀ apply names
through Mathlib and TCSlib. Confirmed the existing direct finite-product equivalences and
compositional use in TCSlib/Cryptography/Pseudorandom/GeneratorFromPermutation.lean:217-219;
no proof or private helper was copied. Generated apply-reader names have differing fully-
applied conventions, so the candidate uses allowed rfl at concrete coordinates instead.

Read Games/Probability.lean:299-309 for exact expect_sample_equiv (304), and
Games/Bridges/Experiments.lean:75-90 for exact expect_sample_pair (80). Searched their existing
in-tree use, including BonehBoyenMachine/Reduction.lean:148-160 and Lamport/AveragingExtra.lean
:71-88, to confirm the published reverse pair-reader plus expect_bind/pure route. No generic
product sampling lemma is re-proved or privately duplicated.

The natively searched whole-helper target had no full exact?/apply? match; those valid
root-run records remain evidence/search/diagonal-and-parameter-codec/run. This fragment adds
no extra generic lemma target/proof and needs no separate new-helper search.

## Remaining native focus and dependency status

Root is checking the outer skeleton separately. This fragment's unchecked details are the
three rfl coordinate reductions through the standard composed equivalences, exact implicit
sample types for the reverse pair reader, and ordinary local A/B alias reduction. hBadMass
remains the only substantive local obligation after this fragment passes and is integrated;
its exact 2/N-1/N² statement is unchanged.

## Parent native skeleton update during this invocation

Root reported that live MatrixDH/Diagonal.lean now checks natively rc0, both error counts0,
with only hGood/hBadMass admissions. Root inserted `swap` before the hPoint hole's bullet
because `have ... := ?_` queues the local proof goal after the main goal. This hGood fragment
now likewise includes `swap` before its hShape coordinate-proof bullet. The fragment's own
native check is still pending. No additional proof block or header change was introduced.
