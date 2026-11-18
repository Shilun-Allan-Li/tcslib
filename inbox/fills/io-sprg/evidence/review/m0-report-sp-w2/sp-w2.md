## SP-W2: semantic hybrid correspondence before M0

The two discarded draft obligations were

```
P.hyb A .prg kappa pp = P.chainGame A true 0 kappa pp
P.hyb A .uniform kappa pp = P.chainGame A false 0 kappa pp
```

They are false as equalities in the inductive free oracle monad. After bind/map
normalization, hyb makes four queries (index draw, seed draw, uniform tail,
adversary coins); chainGame makes five, including an extra uniform public-vector
query that is unused at chain index zero. Following the first answer at each query
distinguishes tree depths four and five. At kappa=0 the added draw is a singleton
but still contributes a query. OracleComp is an inductive program representation;
semantic marginalization does not erase its query constructor.

The chosen minimal pre-M0 repair is

```
accept (P.hyb A .prg kappa pp) = accept (P.chainGame A true 0 kappa pp)
accept (P.hyb A .uniform kappa pp) = accept (P.chainGame A false 0 kappa pp)
```

The source names make the probability-level statement explicit:
`Params.hyb_prg_accept_eq_chain_zero` (Hybrids.lean:157) and
`Params.hyb_uniform_accept_eq_chain_zero` (:167). Their proofs should use published
acceptance/expectation laws to sum out the unused exact uniform draw, then rewrite
advantage through `Games.advantage_eq`. Neither proof should assert a free-program
equality or erase an unused query through an invalid monad law.

This matches the semantic distributions compared in JLS26 Lemma4.2, p.19, and is
sufficient for the headline hybrid advantage inequality. The algorithms, hybrid
definitions, assumptions, efficiency targets, prop41, and all main conclusions are
unchanged. M5 candidates consume prop41's interface and require no body update.

The exact obligation, counterexample, selected repair, and authorization record are
kept verbatim in `evidence/route-requests/SP-W2.txt`. The user authorized best judgment
while asleep with downstream disclosure; E-ROUTE requires this record and minimal
repair, while its rule does not demand a new approval question. Work remains within
owned new files. No M0 checkpoint/freeze had occurred, so this is a disclosed
pre-freeze refinement rather than a post-M0 statement amendment.

The earlier independent draft review missed this syntax/semantics distinction.
That immutable historical snapshot must be read with this superseding correction.
The current report and declaration/hole tables name and quote only the repaired
acceptance statements. No elaboration, seal, or axiom result is claimed by this
report refresh; the lead owns those actual gate logs.
