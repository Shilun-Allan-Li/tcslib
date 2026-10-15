# Arora–Barak Chapter 7 (printed, pp. 123–143) — completion plan

Target: every mathematical item of the printed chapter body (`ch7/ch7_book_pp123-143.txt`),
mapped in `ch7/SURVEY.md`. Already proved by the earlier campaign (do not redo): Lemma 7.5,
Thm 7.8 (abort-form ZPP), Lemma 7.9, Thm 7.10, Note 7.11's core bound, Thm 7.14, Thm 7.15,
BPP = coBPP. Out of scope: the web-draft expander appendix (`Expanders/`, incl. the intentional
`walk_visits_concentration` sorry) — not in printed ch. 7 (it is printed ch. 21).

Pipeline (as for chapter 6): per unit a **formalizer** agent writes the unit's files, a fresh
**critic** agent reviews them against `ch7/REVIEW_CRITERIA.md` (policy.md outranks it), the
formalizer (or the orchestrator) fixes, repeat until `PASS`; when all units land, a
cross-track pass, then a **completeness grader** reads the printed chapter against the repo and
returns `GRADE: COMPLETE` or the missing list. Builds only through
`scratchpad/ch7/lb.sh` (serialized). No commits.

Status legend: `TODO` · `WIP` · `DONE` (critic PASS, builds) · `SKIP` (reason recorded in
`ch7/NOT_FORMALIZED.md`).

## Design decisions (orchestrator)

* **PTM = `Turing.FinNDTM`.** Def 7.1's two transition functions are `tr false`/`tr true`;
  coins are the choice word of `runWith`. A PTM decides in time `T` when every length-`T(|x|)`
  word halts (`HaltsWithin`); acceptance probability is `randProb (T |x|)` over choice words.
  `BPTIME`, `RTIME`, `BPP`, `RP` (machine form) are new definitions; the certificate classes
  `Randomized.InBPP polyTimeModel` etc. stay, and Def 7.2 ≡ Def 7.3 is proved (U2).
* **Expected time without measure theory.** `T_{M,x}` is handled through the finite tail sums
  `E_N = ∑_{t<N} Pr_{w ∈ {0,1}^t}[M has not halted on x by step t]`; "expected time ≤ B" means
  `∀ N, E_N ≤ B`. Def 7.7's `ZTIME` uses this on PTMs that need not halt on every branch.
* **Polynomial-time arithmetic.** §7.2's algorithms need binary arithmetic in `P`, which the
  library lacks (only unary arithmetic, `FormulaKit/Emit.lean`). U4 builds it once.
* **Perfect matching over a prime field.** The book evaluates `det` over ℤ; we evaluate over
  `ZMod p` for a prime `p ≥ 2n` found by trial division (Bertrand), class-preserving because
  the Edmonds polynomial's coefficients are ±1 on distinct monomials. Recorded as a divergence.
* **Random walks for UPATH.** The graph is padded with self-loops to a `D`-regular multigraph,
  `D` a power of two, so a uniform neighbour costs `log₂ D` fair coins; the hitting-time bound
  is proved for that walk (Ex 7.11's route).

## Work units

### U1 — PTM model, BPTIME/RTIME, easy inclusions · DONE (PASS r2)
Files: `Randomized/PTM.lean`, `Randomized/Inclusions.lean`.
Def 7.1 (PTM, `T(n)`-time), Def 7.2 (`BPTIME`, `BPP_PTM := ⋃ BPTIME(n^c+1)`), Def 7.6
(`RTIME`, `RP_PTM`), coRP; remarks: P ⊆ BPP (PTM and certificate forms), RP ⊆ NP, RP ⊆ BPP,
coRP ⊆ BPP, BPP ⊆ EXP; NP = P ⇒ BPP = P (p.135/140); BPP is closed under ≤ₚ and hence
3SAT ∈ BPP ⇒ PH = Σ₂ᵖ (p.135, via Thm 7.14 + Karp–Lipton); Ex 7.4 (RP error reduction).

### U2 — Def 7.2 ≡ Def 7.3 · DONE (PASS r2; Nondeterminism.lean +129 additive lines)
File: `Randomized/PTMEquiv.lean`. `L ∈ BPP_PTM ↔ InBPP polyTimeModel L`, same for RP/coRP.
Forward: the choice-word verifier (`ClassNP/Nondeterminism.lean` `choiceVerifier`,
`cont_choiceVerifier_mem_P`; export what is private by adding public wrappers there only if
unavoidable — flag it). Backward: compile a verifier into a PTM guessing the random string;
the new obligation is that the branch → certificate map pushes the uniform measure to uniform
(a coordinate-projection lemma for `randProb`).

### U3 — §7.2.1 median, Claim 7.4 · DONE (critic PASS r1; 3 advisories for U11)
File: `Randomized/Median.lean`. `FindKthElement` as a randomized algorithm (finite
distributions, e.g. Mathlib `PMF` or a ℚ-weighted tree), correctness (always outputs the k-th
smallest), and Claim 7.4: expected number of comparisons ≤ 10n (the book's T(n) bound).

### U4 — binary arithmetic in P · DONE (core PASS r2; DetMod + PrimeFind PASS r1)
Files: `ClassP/BinaryArith*.lean` (or `ClassNP/PolyTimeArith*.lean`, whichever fits the
existing `PolyTimeComputable` closure kit). On `Nat.bits`-encoded inputs: comparison, add,
sub, mul, divmod, modular exponentiation (Ex 7.3), gcd and the Jacobi symbol (§7.2.2 fact 2),
plus a reusable "iterate a polynomial-time step polynomially often with polynomially bounded
state" lemma. Consumers: U5, U6, U7 (and U10's BPL ⊆ P if attempted).

### U5 — §7.2.2 primality testing · DONE (PrimalityMath PASS r1; Primality PASS r1)
File: `Randomized/Primality.lean`. QR/Jacobi facts 1–3 (Euler's criterion; Jacobi computable;
for odd composite N at most half of the units are Euler liars), Solovay–Strassen:
`PRIMES ∈ coRP` (certificate form over `polyTimeModel`) and hence `∈ BPP`.

### U6 — §7.2.3 polynomial identity testing · DONE (math PASS r2; class half PASS r2)
File: `Randomized/ZeroP.lean`. Algebraic circuits over {+,−,×} with an encoding, the integer
polynomial they compute, PIT → ZEROP via C − C′, degree ≤ 2^m, the fingerprinting lemma
(needs a Chebyshev-type lower bound on the number of primes below 2^{2m}; prove it if Mathlib
lacks it), and `ZEROP ∈ coRP`.

### U7 — §7.2.4 perfect matching · DONE (MatchingMath PASS r1; Matching + MatchingWords PASS r1)
File: `Randomized/Matching.lean`. Edmonds matrix; bipartite `G` has a perfect matching ⇔
`det X ≢ 0`; Lovász's test (random values, one-sided error ≤ 1/2 via Schwartz–Zippel);
`BipartitePerfectMatching ∈ RP` over `polyTimeModel` (determinant over `ZMod p`, see design).

### U8 — §7.3/§7.4 robustness: expected time, ZTIME, coins · DONE (PASS r2; ExpectedTime, Coins, ZPPEquiv)
File: `Randomized/ExpectedTime.lean`, `Randomized/Coins.lean`. `T_{M,x}` and expected running
time (design above); Def 7.7 `ZTIME`, `ZPP_PTM`; §7.4.2 Markov truncation (expected-time PTM ⇒
worst-case 100T with error ≤ 1/100); Ex 7.6(a): `ZPP_PTM` = the abort-form `InZPP` (machine
level, via U2's equivalence); Lemma 7.12 (ρ-coin from fair coins, expected ≤ 2 bits, exact
probability ρ in the limit) and Lemma 7.13 (von Neumann extractor: exactly fair, expected
`1/(2ρ(1−ρ))` pairs).

### U8b — ZPP converse: machine hosts · DONE (PASS r1)
Files: `TuringMachine/Build/` or `Randomized/Hosts*.lean`. A clocked runner (FinNDTM run cut at T steps, from `clockTM`), a three-valued host (P-deciders → `[true]/[false]/abort`), and a restart host (loop until a non-abort answer, clearing tapes). Gives `ZPPAbort_PTM = ZPP_PTM = {L | InZPP polyTimeModel L}` and Thm 7.8 for Def 7.7's ZPP: `ZPP_PTM = RP_PTM ∩ coRP_PTM`; machine-level §7.4.2.

### U9 — §7.6 randomized reductions · DONE (PASS r2; Reductions + NPPoly; Ex 7.8 collapse needs Yap's theorem)
File: `Randomized/Reductions.lean`. Def 7.16 (`≤_r`, PTM or certificate form, both if cheap),
`C ∈ BPP ∧ B ≤_r C ⇒ B ∈ BPP`, Def 7.17 `BP·NP`; Ex 7.7 (BP·NP ⊆ NP/poly — define NP/poly)
and Ex 7.8 if cheap.

### U10 — §7.7 randomized space: BPL, RL, UPATH ∈ RL · TODO
* U10a [DONE, PASS r1] `Randomized/Space{,Amplify,AmplifyRun}.lean`: PTM space, Def 7.18 BPL/RL over `FinNDTM` (read-once coins),
  RL ⊆ NL ⊆ P, log-space error reduction remark. (After U1.)
* U10b [DONE, PASS r2] `Randomized/RandomWalk{,Hitting,Pad}.lean` (pure math): random walk on a connected `D`-regular
  multigraph with self-loops; Ex 7.11(a)–(e) route: stationarity, return time, hitting time
  `≤ poly(n)`; the walk of length `100n⁴`-scale reaches `t` w.p. ≥ 3/4 (finite ℚ statement).
* U10c [DONE, critic PASS r1] `Machines/NARMProb.lean`: probabilistic transfer for the nondeterministic ARM — the
  compiled `FinNDTM`'s acceptance probability over coin words equals the NARM's over its own
  `choose` bits (each `choose` consumes a fresh coin). (Independent, now.)
* U10d [DONE, PASS r2] `Randomized/UPath*.lean`: UPATH def; Thm 7.19 `UPATH ∈ RL` by a NARM random walk. (After
  a–c.)

### U11 — cross-track pass and policy · DONE (full TCSlib build EXIT 0, axiom sweep clean)

### U12 — Yap's theorem (finishes Ex 7.8) · DONE (critic PASS round 1)
Dedup, facade, docstring names, `[AB09, …]` printed numbering, NOT_FORMALIZED.md final.

## Grader
After U11: a fresh grader reads the printed chapter and the repo and returns
`GRADE: COMPLETE` or a list; anything left must be in `ch7/NOT_FORMALIZED.md` with a reason the
grader accepts.

## Running ledger for U11 (cross-track)
- Unify `bitsVal` (LogProg.bitsVal vs Randomized.bitsVal in Fingerprint.lean) and its lemmas into Machines/Bin.lean (PrimalityMath, Fingerprint, BinaryArith, Codec/Word copies).
- randProb_const/drop/one_eq/succ in NARMProb.lean → candidates for Randomized/Classes.lean.
- PrimalityMath Main definitions: add jacobiSymZMod.
- Register NARMProb in SpaceComplexity facade (and all new Randomized modules in Randomized facade).
- Median.lean advisories (divergence example, sketch for comparisons_le, trim docstring).
- Move exists_ofFn_of_randProb_pos to Classes.lean; ensure PTM-form transfers of BPP⊆EXP, P=NP⇒BPP=P, 3SAT corollary, Ex 7.4 exist (U2 asked).
- Hoist bit-block sampling (MatchingMath bitBlock vs Fingerprint blockVal) + Schwartz–Zippel domain version to shared places; delete exists_prime_two_mul_lt_le; trim lovasz_test sketch.
- After U6 r2: RandomBits.lean is the hub — re-point MatchingMath bitBlock/randProb_bitBlock, PrimalityMath bitsVal lemmas, RandomWalk randProb_append, NARMProb randProb_succ/drop/const to it (or move into Classes.lean).
- Hoist ONE public randProb_succ (+ randProb_drop/const/one_eq/append) into Classes.lean; replace private copies in PTMEquiv, Coins, NARMProb, RandomWalk. Hoist indicator_eq_true/false_iff near MultiTapeTM.indicator. Replace private contSelect with maskSelect in Nondeterminism.
- Orchestrator renamed Reductions.randProb_append → randProb_append_split (clash with RandomWalk.randProb_append); all finished modules co-import (orch_all check EXIT 0).
- Hoist blockCount_add_not (Space.lean:333 / Reductions) and exists_forall_not_of_randProb_le (refactor adleman) into Classes.lean. orch_all check must include Space*, Reductions, NPPoly, all new modules.
- Register ClassP.BinaryArith in ClassP.lean facade.
- U10a advisories: Space.lean halting wording, tags on amp*, UsesSpace.k_le placement, halted_of_le note.
- U8 advisories: ZPPEquiv:126 title, InZPP.restart sketch, Main results entries, RP_ExpPTM = RP_PTM analogue.
- Hoist eff_boolVerifier_of_test (Primality.lean) into PolyTimeModel/PTMEquiv; Primality wording advisories; canonical-encoding note.
- BinaryArith U11: privatize loop internals (zipStep etc.), hoist lovaszBits bounds into PrimeFind, optional DetMod split, generic list helpers.
- Fix stale ZPPEquiv/ExpectedTime divergence lines (converses now in ZPPHostsClasses); register Build/ND* in TuringMachine facade; U8b renames.
- Move PSem/ansProb/narm_mem_RL/psem loops into Machines/ next to NARMProb; consider generic det-only-loop lemma for NSem/PSem.
- U7 advisories: zipWith_map_map → core; lovaszRows/bitBlock via blockVal; adjWord shared with Path.lean; privatize tU..tDet; eq_of_bitsVal_eq hoist.
- U6 class advisories: hoist forLoop/getW/uHead/uRest/hasFalse/app lemmas to BinaryArith; wrap 8 long lines; Fingerprint future-tense docstring; testLen lemma dedup.

## Phase 2 — closing every remaining printed item (no deferrals) · DONE: completeness grader round 3 GRADE: COMPLETE (2026-10-14)

After U11, SURVEY shows these items still missing or provisional. Each one is assigned below; NOT_FORMALIZED.md keeps only items the book itself cites without proof or defers to a later chapter.

### U13a — Ex 7.1, Ex 7.2 (general form), Note 7.11 sample-count corollary, Ex 7.5 · DONE (critic PASS round 2)
New files `Randomized/UniformSample.lean`, `Randomized/BiasedCoin.lean` (names may vary).

### U13b — Ex 7.10, §7.5.3 BPP-hardness of ⟨M,x,1^t⟩, §7.5.3 undecidability of the BPTIME property · DONE (critic PASS round 2); row 43 not formalized (needs effective PTM codes + s-m-n)
New files `Randomized/DirectedWalk.lean`, `Randomized/BPPHard.lean`.

### U14 — Ex 7.9 BPL ⊆ P · DONE (critic PASS round 2)
New file(s) `Randomized/BPLInP*.lean`.

### U15 — Ex 7.11(b) convergence to uniform; Ex 7.11(e) probability transfer · DONE (critic PASS round 2; files RandomWalkCover, RandomWalkMixing, RandomWalkMixingPad)
New file(s) `Randomized/RandomWalkMixing*.lean`.

### U16 — p.139 BPL error reduction to 2^{-n^d}; §7.2.3 poly-time map ⟨C,C′⟩ ↦ code(C−C′) · DONE (critic PASS round 2)
New file(s) `Randomized/SpaceAmplifyPoly*.lean`, `Randomized/ZeroPReduce.lean`.
