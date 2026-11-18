# Polys10 + Correctness18 + specific-G4 helper overlap probes — NOT_RUN

The 29 templates, names/index/mapping, compatible materializer, actual text-search
log and fresh source import audit are ready. No Lean, lake/build/cache, source/import
edit, git operation, agent spawn, materializer invocation, or tactic block occurred.
All 58 exact?/apply? outcomes are explicitly pending in search-results.PENDING.json.

## Isolation

Every template imports only existing precise Mathlib roots or the public
TCSlib.Cryptography.Games.OracleComp module, plus the toolchain library-search
elaborator. A fresh comment/string-aware import graph confirms that ALL 29 exclude
EVERY TCSlib.Cryptography.Obfuscation module. Thus neither the target's sorried
constant nor a newly proved owned sibling can be found by the search. Every selected
public root is already present in the corresponding current owner import closure.
No new implementation import is proposed. The source hash record binds Polys,
Correctness, Samplers, Defs and the currently filled Degree owner.

Each template has one anonymous example, zero tactic blocks and one
__PROBE_BODY__ marker. There are no preceding helper declarations, axioms, owned
copies or local lemmas that assert the goal. Local lets only display literal
construction formulas. They are scratch goal syntax, not new algorithm definitions.
The materializer is copied unchanged from OverlapEncoding and writes ONE selected
file under /private/tmp. Compiling unrelated owned modules on disk does not load
those declarations into these isolated search environments.

## Exact expansion and stated abstractions

mapping.tsv and probe-index.json give the per-body source mapping, exact premises,
probe kind and selected public API names. Full constructor/record expansion of
Params/BoolPRG/Raw would import or recreate irrelevant primitive data. Instead the
numeric dimensions, matrix, representation polynomial, coordinate maps and exact
support facts become arbitrary mathematical inputs with their actual relevant
premises. This does not change any implementation theorem or add an implementation
assumption. No positivity/nonempty shortcut is added; zero dimensions are retained.

Polys:

- Slot count is the literal pair of filtered optional sorted-support reads.
- Both half-form degrees expand linearCoeff and halfForm completely, with the
  actual padding/last-coordinate branch and tensor sum/product. Coordinate maps
  may be arbitrary because neither evaluation nor degree bounds need injectivity.
- prgPoly_degrees expands the full coefficient sum and both half forms. Only total
  degree is retained: multilinearity is unnecessary for its support-cardinality
  bound. This stronger generic comparison goal is intentional and documented.
- correctionPoly_degrees contains BOTH optional branches and literal U*V sums.
- G3/G4 degree probes consume exactly the preceding degree facts and use the literal
  addition or renamed repetition sum, with indicator weights written explicitly.
- halfForm_eval includes the complete augmented-secret tensor formula and public
  matrix-vector premise. G1_eval includes the complete integer coefficient lift,
  multilinearity, total-degree bound and d<=D+D consequence. No halfForm_eval
  conclusion is assumed in the G1 probe.
- G3_eval_of_scaled is explicitly a STRUCTURAL CORE, not a token-for-token complete
  nested G3 expansion. The finite first-half tensor/monomial index becomes i;
  a i is its unchanged coefficient product times the unscaled second half. The
  actual hcopy restricts to its tensor/U instances. The polynomial sums and each
  scaled/unscaled private X are literal. An absent correction uses an empty finite
  correction index. This tests the existing eval/factor-out-scalar machinery.

Correctness:

- The three firstGood probes use literal List.finRange/find?, including the precise
  earlier-index order. The five packing probes are complete concrete branch
  functions applied through arbitrary public/private equivalences; no packing
  reader conclusion is supplied as a hypothesis.
- oneFlag_bounds expands decide, the entire three-part success predicate, every
  bucket filter/load cardinality and rc squared versus rc*rc.
- corr_zero_of_not_bad keeps the exact no-variable/error-intersection premise,
  integer Boolean representation equation, field casting and correction difference.
- G1_eval_of_good keeps that same premise and the actual upstream G1 evaluation
  equality. G2_eval_of_flag keeps the actual erroneous and correcting evaluations;
  success is used upstream only to obtain the correction equality. The final
  evaluated sum is literal.
- correctionPoly_eval_oneSd keeps the actual matrix factor product, existing and
  injective optional position, and literal bucket matrix finite sum. The target
  is the pointwise factor-slot sum. Its eval_sum/mul/X reader step is omitted from
  this composition core; no bucket-entry theorem conclusion is assumed.
- oneSd_factors_mul is explicitly a STRUCTURAL CORE reused verbatim from the
  existing OverlapProbes/sparse_reconstruct template. It contains the full padded
  list factors, generic matrix, actual Nodup/support-coverage/capacity premises.
  It does not include the concrete bucket support-count transport or the oneSd
  success-reader equations. Those are construction-specific reader compositions
  covered in the AlgebraEvaluation body map. A failed core search does not imply
  that no specialized public theorem exists for some omitted composition.
- G4_eval_sdCore keeps literal first-success selection, polynomial sum and rename.
  hq is exactly scaled G3 after the separately tested packing coordinates; hgood is
  exactly the successful G2 evaluation. No deterministic-core conclusion is assumed.
- G4_eval_eq uses the actual deterministic pointwise equality and the literal map
  over a draw computation. It is valid for arbitrary OracleComp, so uniformity,
  finiteness and nonempty-draw assumptions are unnecessary and omitted.
- eval'_correct includes the literal equality-to-one decide. Nontrivial R and
  DecidableEq R are supplied because the actual prime-field instances supply them;
  classical in a proof cannot synthesize an instance needed in the statement.
- The new G4_seed_allOutputs helper has both actual support facts on the SAME c and
  the literal seed projection map. It does not assume a generic conjunction lemma.
- jls_hasComplexity expands the complete Raw complexity conclusion after its public
  record reader. G is the specific G4 witness and its actual degree/support facts
  are premises; no existential conclusion is assumed. Arbitrary kappa/index are
  universally bound example parameters, retaining the original quantifier scope.

The exact source headers and all expanded statements have not been elaborated.
These are useful isolated comparison goals, not a declaration that every generic
probe is definitionally identical to the entire original dependent record type.

## One-file search materialization

For one root tool invocation, choose ONE mode and ONE name:

    python3 /private/tmp/io-sprg-proof-notes/OverlapAlgebra/materialize.py G1_eval \
      --tactic 'exact?' --output /private/tmp/io-sprg-probes/algebra/G1_eval_exact.lean

For the independent apply? pass, use the same name with --tactic 'apply?' and a
separate output path. This writes exactly one tactic block and executes no Lean.
Use the root-authorized single-slot runner afterwards. Quote apostrophized names,
for example "eval'_correct". Do not concatenate several materializer invocations
into one authoring call if that would violate the one-block invocation rule.

Record the full search log, suggestion and ALL residual goals. A successful exact?
result must close the entire goal. apply? returning e.g. equality transitivity,
Matrix.ext, a weighted-degree inequality or a map/bind rule with unsolved premises
is a partial suggestion, not a closing proof. Diagnostic/elaboration failure must
be recorded separately from a completed unsuccessful theorem search.

## Name/shape search evidence and reuse

name-shape-searches.log records 29 actual external exact-name declaration searches
and seven grouped mathematical-shape searches, with paths and matching lines.
The exact source theorem names have no external declarations with those names;
this alone says nothing about logically equivalent differently named theorems.
The public_apis index column supplies the intended public components. In particular,
reuse the existing finite distributivity, list-find minimum, weighted support degree,
variable-set evaluation congruence, matrix-entry sum and AllOutputs readers; do not
rederive their generic counterparts. Existing OverlapProbes/sparse_reconstruct
search evidence can be reused only if its recorded goal/imports match this copied
core exactly. No private or generated _private declaration is referenced.

Games.Closeness.allOutputs_bind_iff is an adjacent public broader support lemma;
this packet does not import it. No public AllOutputs.and/map helper is declared in
the minimal OracleComp owner. Public generated to_additive names are documented
explicitly: Finset.card_nsmul_le_sum comes from pow_card_le_prod; the additive
Fin.sum_univ_castSucc comes from prod_univ_castSucc. Core and exact-manifest source
searches in the earlier AlgebraEvaluation APIs.tsv give the remaining exact names.

Every template is at most 97 columns. Python source compilation, marker counts,
file hashes and source import-graph checks are STATIC evidence only. None is a Lean
parse/type/search/kernel/axiom/seal result. Root owns all such execution.
