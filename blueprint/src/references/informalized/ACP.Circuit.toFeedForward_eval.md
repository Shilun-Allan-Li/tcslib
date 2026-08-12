<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/FeedForwardCircuit.lean :: Circuit.toFeedForward_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The feedforward embedding computes the same function

**Claim.** For every `C : BoolCircuit.Circuit n` and every `x : Fin n → Bool`,
`C.toFeedForward.eval₁ x = C.eval x`. Since the embedding has output type `Unit`, `eval₁`
reads off its unique output node.

**Proof.** One `convert` against the layer-wise lemma:

* apply `Circuit.toFeedForward_evalNode_const C x` at the top layer
  `m := C.toFeedForward.depth`;
* both of its side conditions — `m < C.depth + 1 + 1` and `0 < m` — reduce to arithmetic on
  the literal `depth` field and are discharged by
  `simp +decide [Circuit.toFeedForward]`;
* `convert` then reconciles `eval₁`/`eval` with `evalNode` at `Fin.last`, i.e. the transport
  along `nodes_last`.

**Remark.** All the work is in the private lemma; this statement is the public interface,
and it is the reason the identity-padding layers of `toFeedForward` are harmless.
