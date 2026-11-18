# Full original M4 Security bounds — UNRUN

lemma42.proof and prop41.proof are complete one-block replacements for the two
frozen original Security.lean bodies. They have41 and109 lines respectively,
maximum width80, no sorry/admit placeholders and no new public helper or definition.
No Lean, source/import edit, Git, cache or agent was used. These are unelaborated
candidates, not proof-check or axiom passes. Exact frozen signatures, current
source hashes and two full strong-interface public-only cores are staged alongside.

## lemma42: one chain and one global advice family

At each κ>0, existing exists_advantage_hybrid_gap selects i<κ with endpoint gap/κ
at most the selected real-tail adjacent gap. A positive natural cast allows
multiplying by κ. The index is carried as Fin(κ+1), so at κ=0 the explicitly chosen
zero sentinel remains inhabited; its legality/bound is required only when κ>0.
Classical choice assembles the whole hop family before calling lpn_hop with the
constant true-tail family. That theorem supplies ωL BEFORE every BL. prg_hop
similarly supplies ωG BEFORE every BG. Only then does the body introduce BL/BG,
their exact shared RealizesOn proofs and κ.

For κ>0 the selected LPN hop bound is multiplied by κ. For κ=0 the prefix endpoints
are identical and advantage_self gives zero; no division by zero, Fin0 witness or
illegal LPN hop is used. One public advantage_triangle composes that prefix with
the all-uniform-public PRG hop. No realiser is constructed or chosen in the proof.

## prop41: strongest common LPN selector across BOTH tails

At each κ>0, Finset.exists_max_image is applied to the finite set Bool×Finκ,
with the actual gap function

  gap κ b i = advantage (chainGame A b i κ πκ) (chainGame A b (i+1) κ πκ).

Thus the selected tail/hop bounds every adjacent gap of BOTH LPN chains. This
matters: two independent lpn_hop invocations would generally give two incompatible
advice families/realisers and would not prove the frozen single-BL conclusion.
The body instead assembles global tails/hops first and calls lpn_hop ONCE.
At κ=0 it selects a true-tail zero sentinel and requires no valid below-κ hop.
The same ωL then works for every BL and every κ exactly as the source statement asks.

After BL/BG and their shared reader proofs are introduced, advantage_hybrid and
sum_le_sum bound each chain by κ times that one BL advantage. The false-tail
prefix is reversed by advantage_comm. Two advantage_triangle applications insert
the PRG endpoint hop. SP-W2 endpoint results are used only through advantage_eq
and their ACCEPTANCE equalities; no equality of free programs is inferred after
removing queries. The real/prg and uniform/random statistical inequalities each
add precisely the same errProb slack. Raw.adv_eq and the exact raw-game endpoint
readers identify the frozen raw advantage. The final scalar association is ring.

The selector proof uses existing finite maximum/telescoping facts directly. It
introduces no new generic maximum, hybrid, averaging, sampling or realization
lemma. Proof-local classical selection does not alter any frozen encoder or
preprocessor definition, and the advice family never depends on BL or BG.

## Dependency order and actual source assumptions

Both bodies consume the existing lpn_hop and prg_hop every-realiser statements.
They are prerequisite results to be proved first, not independent proof evidence
merely because their current source stubs elaborate. prop41 additionally consumes
all six existing Hybrids endpoint/statistical results. lemma42 does not assume
realisability; the strong shared contract is used only as the input implication
in each hop theorem, preserving the source's ∃advice/∀realisers order.
The later M5 Realizable hypothesis supplies actual realisers for exactly these
advice families. No alternate contract or all-coin-strings assumption is introduced.

No new source import is needed. Finset.exists_max_image is already available via
the existing Lamport averaging dependency. Game comparison APIs are already in
Games.Advantage through the current owners. Explicit Finset.sum notation avoids
requiring a new scoped BigOperators opening in Security. The templates explicitly
import Games.Advantage and Finset.Max; their fully qualified namespace openings
are valid and all probabilistic types are Type0.

## Isolated search goals and scope

overlap/ has two original-goal templates and two supplemental selector controls,
all PENDING_ROOT exact?/apply? runs. No owned StructuredSeed module is imported,
so the existing stubs/new candidates cannot become self hits. The100000-heartbeat
bound is diagnostic only, and absence is not inferred from any future timeout.

The two original cores keep the FULL strong LPN/PRG interfaces: arbitrary global
tail/hop selectors yield one advice BEFORE all realisers and all κ; the conclusion
also puts both advice values before all realisers and κ. LA/GA stand for the entire
actual dependent advice families. relL/relG are abstract copies of the exact shared
RealizesOn predicate applications, not new source contracts. aL/aG are the actual
canonical assumption advantages at ellκ/nκ. The prop41 core additionally retains
raw endpoint equality, the two acceptance-only links and both statistical bounds.
It does not assume its target combined inequality or a common worst-hop bound.

The controls isolate only the two existing finite selector constructions used by
the bodies; they are not new public source helpers. No κ>0 hypothesis is added to
either final original goal. Strong source formulas/headers and all advice/realiser
quantifiers are unchanged. No source statement is weakened to selected machines.

## Source-size effect and remaining mechanical checks

The two bodies add148 lines to the present source stubs. Together with the corrected
seven M5 bodies, the known Security source would be492 lines, excluding future
repair/doc additions. This is below800; no split is required by the known payload.
The earlier M5 conditional split remains a fallback if later source growth changes
that estimate, not a change performed here.

Untested mechanical points are dependent choose elaboration of the global
Fin(κ+1) family; definitional projection of the selected Fin value; rewriting the
κ=0 scalar branch after local lets; and matching the endpoint acceptance readers.
All finite-function arguments at the maximum/telescope calls are explicitly typed.
Only local gap/aL/aG are reduced. No foreign construction, game, encoding or
realization definition is unfolded. APIs.tsv cites exact public signatures read
before candidate preparation; source-bindings.json records the text provenance.
