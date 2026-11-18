# Two mandatory M1 bridge candidates and isolated searches — NOT_RUN

Existing frozen bodies only:

- 01-HasComplexityEff-hasComplexity.proof: six lines, one tactic block. Read
  SPRG.Raw.hasComplexityEff_iff, retain its Q/degree/support witnesses via
  SPRG.Raw.hasComplexity_iff, and discard f/efficiency/term-list generation.
- 02-primeWidthBound.proof: three lines, one tactic block. Normalize only the
  published PolyExpr add/var/const equations and use pp.le_two_pow.

No source definition, statement/header, reader, algorithm, sampler, machine or
hypothesis changes. Both proofs are untested. Existing source docstrings/sketches
remain appropriate and should stay with the declarations. No old body candidate
was found by the initial packet text/path search.

The two zero-tactic-block templates use the same one-file materialize.py CLI as
OverlapEncoding. Each has one marker. Every selected import root is already in its
actual owner closure, and a fresh source graph excludes ALL Obfuscation modules.
No owned result or sibling can be a library-search self-hit.

HasComplexityEff.hasComplexity expands the EXACT reader logical shape while
abstracting only relevant structure fields:

    Idx kappa = S.Idx kappa
    QTy kappa = Fin(S.outLen kappa) -> MvPolynomial(...)(ZMod(...))
    Eff f = PolyTimeComputable f
    Gen f kappa I Q = the full forall-j/exists-term-list code and denotation equations
    Bound kappa Q = the full forall-j public/private degree conjunction
    Correct kappa I Q = the exact sdSamp AllOutputs evaluation property

The one f still precedes all parameters, and the one Q witness is retained with
its same degree/support properties. No conclusion is assumed as an input. These
predicates are irrelevant to the logical forgetting step and need no reconstruction
of SPRG.Raw or a copied polynomial/OracleComp model. All Idx/QTy families are Type0.
In particular this goal imports no OracleSpec API at all: that API accepts Type,
not arbitrary Type*, as source OracleComp.lean:74/84 confirms. There is no universal
sampling, proof of PolyTimeComputable, or new generic logical helper to land.

primeWidthBound uses arbitrary natural p and its ACTUAL upper-interval field.
Primality and the unused lower endpoint are irrelevant to this monotone reader
normalization, so they are omitted in the stronger isolated comparison goal.
No unnecessary BigOperators scoped-open command appears in either template.

One root authoring invocation can materialize ONE selected mode, for example:

    python3 /private/tmp/io-sprg-proof-notes/M1Bridges/materialize.py \
      HasComplexityEff.hasComplexity --tactic 'exact?' \
      --output /private/tmp/io-sprg-overlap/M1Bridge_complexity-exact.lean

Use the independent apply? mode/output next and the same name/index for primeWidthBound.
Materialization executes no Lean. No materializer or search was run in this preparation.
Root must record actual results, residual goals, source/log hashes, bounded timeouts and
harness errors separately. A partial apply? suggestion is not a closing proof.

name-shape-searches.log records read-only external searches and selected public APIs.
The public generic Exists.imp and logical conjunction constructors are the relevant
existing witness-forgetting primitives; actual source proof consumes the two owner
readers. PolyExpr.eval_const/var/add are the exact existing normalization equations.
No external full named counterpart was located by the literal-name search; that is
not a claim of global theorem absence. All type/elaboration/axiom/seal checks remain
root-only and pending. Source hashes and static/import checks are adjacent JSON files.

No Lean/git/cache, implementation source edit, agent spawn or REPORT write occurred.
