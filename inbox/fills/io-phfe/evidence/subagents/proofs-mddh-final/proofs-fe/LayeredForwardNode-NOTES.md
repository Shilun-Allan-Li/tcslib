# Proposed PartialGarbling.Layered.forward_node helper proof

Status: new technical helper draft, not elaborated. No live source edits, Lean, lake,
build, or Git commands. No additional helper, import, or admitted term is introduced.

## Deliverable and exact interface

`LayeredForwardNode.lean.inc` contains the exact proposed header and original proposed
docstring/sketch/tag from the sibling's `Layered.forward-action-helpers.proposed.lean.inc`,
with its placeholder body replaced by one tactic block. Maximum line width 83.

```lean
theorem forward_node (x : Fin l → ZMod (p : ℕ)) (v : TIdx l d) :
    forward x (node v) = forward x (parent v) * xhat x (lastLabel v)
```

Context is the existing namespace
`TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Layered`,
inside `section Algorithms` with `{p : ℕ+} {l n d : ℕ}`. This theorem does not use n.
Suggested placement remains immediately after `forward_root`, before `rec`.
A static check confirmed the current live Layered source has no existing
`theorem forward_node` declaration.

The preserved docstring begins with the actual recurrence in natural language,
identifies it as technical glue for the layered path-sum specialization, and cites
`[AGW20, Appendix A, (32), p.38]`. It does not claim that AGW states this particular
formal helper. The supplied sketch names the exact tuple/product readers used.

## Proof route and published reuse

`node_eq` represents v at depth `v.1.val + 1`; `parent_eq` represents its tuple-init
prefix at predecessor depth; `lastLabel_eq` reads the final label. The public
`forward_eq` reader expresses both path values as finite products.

Apply the existing `Fin.prod_univ_castSucc` directly to
`fun i : Fin (v.1.val + 1) => xhat x (v.2 i)`.
Its prefix product is exactly the parent's product by `Fin.init_def`, and its
last factor is exactly the final edge weight. `Fin.val_succ` and
`Fin.coe_castSucc` are the published depth/cast equations. Ordinary Sigma projection
and function-application reduction align the remaining expressions.

Dependencies:

- `Layered.lean:83`: `node_eq`.
- `Layered.lean:89`: `parent_eq`.
- `Layered.lean:96`: `lastLabel_eq`.
- `Layered.lean:233`: `forward_eq`.
- `Mathlib/Algebra/BigOperators/Fin.lean:80`: `Fin.prod_univ_castSucc`, requiring
  the existing commutative-monoid instance for `ZMod p`.
- `Mathlib/Data/Fin/Tuple/Basic.lean:489`: `Fin.init_def` gives
  `Fin.init q = fun k => q k.castSucc`.
- Pinned Lean v4.25 core `Init/Data/Fin/Lemmas.lean:392`: `Fin.val_succ`.
- Same file :541: `Fin.coe_castSucc`.

No defining equation of node, parent, lastLabel, forward, xhat, Fin.init, or a cast
is explicitly unfolded. Only their published readers and the existing generic
finite-product theorem occur in `simpa only`. No new local or public cast/product
lemma is needed. The proof uses no admitted theorem, in particular neither
`forward_root` nor the later `forward_action`.

The claim holds for p=1 and arbitrary l,d; at d=0 its TIdx parameter has no values.
No extra nonzero, prime, degree, or dimension hypothesis is needed.

## Search and probe history

The parent reports native `exact?` and `apply?` searches before this helper, against
a source prefix ending before `forward_root`; therefore later admitted
`forward_action` was unavailable. The searches had no complete match, only partial
generic suggestions. Parent also reported a trailing section-end typo outside the
probe goals and is correcting it. This report is not a claim that the probe file
passed or that this proof elaborated. No native search was run by this agent.

Sibling's earlier source-shape search evidence and proposed header were read from:

- `proofs-pairing/Layered.forward-action-helpers.proposed.lean.inc`;
- `proofs-pairing/Layered.forward-action-helper-review.md`;
- `proofs-pairing/Layered.forward-action-helper-searches.txt`.

Actual read/search commands for this invocation, in
`/Users/seyoonr/.codex/worktrees/tcslib-io-phfe/tcslib-exchange`:

```sh
sed -n '1,265p' TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/PartialGarbling/Layered.lean
rg -n 'prod_univ_castSucc|init.*castSucc|castSucc.*init|init_snoc|snoc_init|snoc.*last|last.*snoc|cast.*last|init.*cast' .lake/packages/mathlib/Mathlib/Algebra/BigOperators/Fin.lean .lake/packages/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean .lake/packages/mathlib/Mathlib/Data/Fin/Tuple/Reflection.lean .lake/packages/mathlib/Mathlib/Data/Fin/Basic.lean
rg -n 'forward_node|forward_root|forward_action|node_eq|parent_eq|lastLabel_eq|forward_eq|def node|def parent|def lastLabel' TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/PartialGarbling/Layered.lean
rg --files /private/tmp/io-phfe-drafts | rg -i 'forward|layered.*proof|proof.*layered' | head -35
cat /private/tmp/io-phfe-drafts/proofs-pairing/Layered.forward-action-helpers.proposed.lean.inc
sed -n '1,180p' /private/tmp/io-phfe-drafts/proofs-pairing/Layered.forward-action-helper-review.md
sed -n '478,496p' .lake/packages/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean
sed -n '72,85p' .lake/packages/mathlib/Mathlib/Algebra/BigOperators/Fin.lean
rg -n 'coe_succ|val_succ|coe_castSucc|val_castSucc' .lake/packages/mathlib/Mathlib/Data/Fin/Basic.lean /Users/seyoonr/.elan/toolchains/leanprover--lean4---v4.25.0/src/lean/Init/Data/Fin/Lemmas.lean | head -40
rg -n 'prod_univ_castSucc.*init|Fin\.init_def|init_def' TCSlib .lake/packages/mathlib/Mathlib/Algebra/BigOperators/Fin.lean .lake/packages/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean | head -30
```

Also read the relevant repository policy and AGENTS attribution/sorry-ladder sections,
and the sibling's forward_root review. The new helper's proposed docstring and tag
were preserved exactly, including the source specialization disclosure.

## Static snapshot and limits

Live Layered SHA-256 at drafting: 09b1074dd541ec70c64dbdf3d8dd93e3c022f82b3724474d804bcf80c5899475.
Textual checks verified the proposed docstring/header match, helper-name absence,
width, exactly one tactic block, and no admitted terms. Native elaboration and
post-insertion audit/declaration inventory updates remain the parent's work.
No missing published tuple/cast interface or mathematical obstruction was found.
