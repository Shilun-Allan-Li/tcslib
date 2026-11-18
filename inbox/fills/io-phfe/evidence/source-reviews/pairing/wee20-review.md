# Wee20 source review

Source read in place: /Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-exchange/sources/wee20.pdf.
The lead verified the dispatch SHA-256 before authorization to read. No PDF was copied.
Review method: pdftotext -layout for navigation; all 14 complete pages rendered by pdftoppm
at 100 dpi and inspected. Printed page numbers equal PDF page numbers.
No Lean, lake, build command, or git mutation was run.

## Verified source locations

- p.1, abstract and section 1.1: public-key quadratic FE and PHFE with NC1 public computation,
  selective simulation security against unbounded collusion; footnote 1 explicitly strengthens
  selective to semi-adaptive security.
- pp.2-3, section 1.2: the overview uses asymmetric groups, bilateral k-Lin, and the
  tensor/mixed-product identities. Bilateral 1-Lin is explicitly false. This overview is
  explanatory; the formal group definition on p.4 does not require distinct source groups.
- p.4, section 2.1, Assumption 1: M uniformly distributed over l-by-k field matrices,
  S over k-by-d, and U over l-by-d. The challenge is ([M]1,[MS]1) versus ([M]1,[U]1).
  The paper states a tight k-Lin => MDDH^1_{k,k+1} => MDDH^d_{k,l} chain and attributes it
  to reference 10, Escala et al. This paper does not give that reduction's construction.
  It says l<=k holds unconditionally; that means statistical security, not necessarily
  exact equality for unconditioned uniform M (rank-deficient M has positive probability).
- p.5, section 2.2: mpk first; adversary then chooses x*,z*; ct* next; adaptive KeyGen
  queries afterward. KeyGen* receives f and scalar h(z*) f(x*)^T. Statefulness is explicit.
  Remark 1 restricts scalar-value decryption to bounded outputs because the implementation
  computes the result in the exponent. The Phase A target should retain group-valued output.
- pp.5-6, section 3, unnumbered claim: quadratic PHFE is SA-SIM secure under bilateral k-Lin
  and k'-Lin. The paper recommends k=2,k'=1 for efficiency; our symmetric instantiation
  uses k=k'=2. Decryption gives the target-group exponent, while simulation needs source-
  group g^mu only. The main scheme has no numbered theorem.
- p.6, section 3.1: M is stacked A1 tensor I and I tensor A2. Ciphertext masks y1,y2 and
  invokes Pi on s1 tensor z2 concatenated with y1 tensor s2. Equations (4)-(5) are the
  tensor identity and its scalar evaluation. Honest Enc can form the Pi input in the group.
- p.7, section 3.2: simulator stores y1,y2 from Enc* for KeyGen*. In particular the simulator
  state must thread through Enc* and later key queries. The printed G_T/source-group mismatch
  in KeyGen* is the ruled W4 reading. Enc* prints [y2]1 rather than [y2]2 (W2).
- pp.7-8, section 3.3: Game0 real; Game1 simulates Pi, Game2 rewrites leak using equation (5),
  Game3 replaces y1 by uniform under bilateral k-Lin, Game4 replaces y2 under k'-Lin.
  The reduction to Pi sends the private challenge in the clear, whose components it knows.
  Game3 explicitly permits z1* adaptive after [A1]1,[A1]2. The second replacement uses known
  y1 and group-valued [y2]2. W2/W3 occurrences are visually confirmed.
- p.8, section 4: Pi permits a different group matrix [M]2 with every function key. Dec gets
  [M]2, not M. Its ideal leak is [z M f(x)^T]2. This can be computed using powers and products
  of [M]2 with known z and f(x), with no discrete-log recovery.
- pp.8-9, Lemma 1: syntax, reconstruction for EVERY coin vector, and statistical privacy.
  The L0/L1 prose and syntax shapes are swapped as dispatch W1 records. Section 4.2 KeyGen
  on p.9 supplies the dimensionally correct L1=t-by-(mn), L0=t-by-m.
- p.9, section 4.2: Setup A is UNCONDITIONED uniform k-by-(k+1); W,U,V are unconditioned
  uniform matrices. Enc is the three components [sA], [z+sAW], [sAU(x^T tensor I)+sAV].
  KeyGen samples T and R and returns [Tbar+WM], [TL1+U(I tensor R)], [TL0+VR], [R].
  Decryption is equations (6)-(8).
- p.10, correctness: equations (9)-(11) identify the decrypted vector with partial garbling
  at coins sAT. The mixed-product identity cancels U and V terms. For group-valued M,
  prove this as a group identity; do not invert its exponentiation in any algorithm.
- p.10, simulator: Setup* samples column-oriented A uniformly in (k+1)-by-k and independent
  c uniformly in dimension k+1; it uses inverse columns Cperp,aPerp of (A|c)^T. Enc* emits
  [c^T],[wtilde],[vtilde]. KeyGen* uses partial garbling and only the leakage [mu]2.
- p.12, Appendix B, Theorem 1: two MDDH advantages plus the printed 1/p term. The two
  dimensions are MDDH^1_{k,k+1} and MDDH^n_{k,mQ}. This numbered theorem concerns Pi only.
- pp.12-13: Game0 to Game1 substitutes c for sA via the first MDDH challenge. W,U,V can
  be hardwired in advice. Games1/2 are equal only on the full-rank event, because the
  decomposition matrix requires the inverse of (A|c)^T.
- pp.13-14, Lemma 3: the required coordinate-distribution identity is stated for every
  full-rank (A|c). Its proof explicitly acknowledges adaptive x*,z* and invokes a random-
  guessing argument after noting that the public projected coordinates are unchanged.
- pp.13-14, Lemma 4: all query blocks R_j are bundled into the second MDDH challenge.
  The common hidden utilde is multiplied against each R_j. m is common to all functions.
- p.14, Lemma 5: the source changes uhat_j to uhat_j - ttilde_j L1_j and invokes partial
  garbling privacy. With an exact PG instance this hop is an exact distribution identity.
- p.11 references and p.12 Appendix A were read; Appendix A is a separate concrete
  quadratic special case and is not needed for the PHFE development.

## Newly verified source discrepancy: full-rank probability

The statement on p.10 that (A|c) is full rank with probability 1-1/p is false for its printed
unconditioned uniform sampling. For k=2, (A|c) is a uniform 3-by-3 matrix. Exact success is

  (1 - p^-1) (1 - p^-2) (1 - p^-3),

so exact failure is

  p^-1 + p^-2 - p^-4 - p^-5 + p^-6.

This exceeds 1/p; at p=2 the failure is 43/64. The 1/p expression is correct conditional
on A already having full column rank. Honest Setup on p.9 does not impose that conditioning.
The source's printed Theorem 1 slack cannot simply be copied with unconditioned A.
The dispatch permits an explicit full-rank term and design-r3 mentions exact card_GL_field;
thus the exact term may fit the authorized intended statement, but the discrepancy must be
reported and its handling disclosed. No source or Lean statement was changed by this review.
The simulator also requires a specified total behavior on the singular event.

## Adaptive Lemma 3: exact route succeeds on full rank

Write H=(A|c)^T, with inverse columns (Cperp|a). Then A^T a=0, c^T a=1.
Fix pp,A,c and adversary coins. The challenge x*,z* depends only on public projections
P=(A^T U,A^T W,A^T V) and other unchanged public data. Let u=c^T U and X=x*^T tensor I_k.
The triangular map

  U'=U,
  W'=W+a z*,
  V'=V+a(u X)

preserves P and U, hence preserves the x*,z*,u used to define its shifts. Its inverse
subtracts exactly those shifts. Its low coordinates are u, w=c^T W+z*, and
v=c^T V+u X. Since multiplication by H is a linear equivalence, these low coordinates
are uniform independently of public projections. The distribution is exactly the one
needed by Game3, without any guessing loss. For each fresh adaptive key query, H T_j
separates A^T T_j and ttilde_j as independent coordinates; the transcript induction preserves
the query f_j and group matrix [M_j]. This establishes the promised route in principle;
no failure of the adaptive bijection was found.

## Additional notation readings needing disclosure

1. Pi's rectangular M requires distinct private input dimension and function-output dimension.
   On p.9 W's n' columns name the input dimension, but the same page says Tbar has n' rightmost
   columns. In Tbar+WM the number of selected T columns is necessarily the output dimension
   of f (M's column count), which can differ. The outer M on p.6 is rectangular in general.
2. p.6 describes [M]2 as belonging to G1; its group label conflicts with the notation [M]2.
   This is harmless when the groups coincide but should be recorded as a reading.
3. p.6 Enc also samples s0 although Enc0 supplies its own randomness. Section 3.3 Game1's
   reduction repeats this unused sample; dispatch R3 directs dropping it.
4. p.7 Game1 prints Enc0(msk*,x*) rather than the intended Enc0*(msk0*,x*), while the preceding
   sentence explicitly replaces the underlying triple by its simulated triple.
5. p.10 describes pgb*(f,x*,[mu]2) using group input although Lemma1 itself is scalar-valued;
   implementation needs the group-lifted reader demanded by the dispatch.

## Symmetric adaptation

No algorithm or reduction in pp.6-10 or Appendix B needs distinct source groups after
k=k'=2 and the source-group tags are identified. All uses are group operations, powers by
known scalars, and pairings. No asymmetric-only step or discrete-log inversion was found in
this proof route. The bounded-value discrete log in p.5 Remark1 and AppendixA Dec belongs to
the scalar-output variant; the required in-the-exponent correctness avoids it.

## MDDH reduction warning

The paper asserts the tight implication but does not describe it. A naive attempt to spread
one challenge vector c into d columns as MS+c r produces one common residual direction,
not a uniform l-by-d random matrix. It is not by itself an exact simulation of the random
branch. This is a warning about a tempting proof route, not a contradiction of the source's
claimed tight implication. The dispatch allows a disclosed column-hybrid fallback.
