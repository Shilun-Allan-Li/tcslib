# Proposed public SAT linear-certificate reader

UNAPPROVED API PROPOSAL. No repository Lean source is changed. The proposed name is `Complexity.SAT_exists_linear_verifier`, immediately after `SAT_mem_NP` in `ClassNP/SAT.lean`:

```lean
∃ V : Language Bool, V ∈ P ∧
  ∀ x : List Bool, x ∈ SAT ↔
    ∃ u : List Bool, u.length = x.length + 1 ∧ x ++ u ∈ V
```

This exposes the exact existing `(1,1)` certificate witness, without exposing its private verifier representation. Its proof is the existing `satVerifier false`, `satVerifier_of_poly false satVerdict_false_poly`, and `sat_verifier_equiv`. There are no new machine/data definitions, imports, simp attributes, renames or changes to existing statements. This is a public statement/name/home ruling under START-HERE§2; the prior approval of `SAT_mem_NP` or Ladner’s mathematical choices does not silently approve this new reader.

Why needed: the public statement `SAT ∈ NP` hides its certificate exponent. A generic exponential search using an arbitrary polynomial certificate bound does not supply a polynomial bound on logarithmic-length SAT queries. The displayed exact n+1 bound plugs into the existing `exists_proj_decider 1 1`; it preserves the actual concatenation `x ++ u`, rather than substituting pairEncode.

Actual checks: the entire hypothetical owner passes native exit0/errors0/sorries0. It was separately compiled through leanelab-o into a complete895-object MAC8 clone after unlinking its own output. The actual named imported consumer then passes exit0/errors0/sorries0 with the existing public search host, obtaining clock `b*2^(n+1)*(a*(2n+2)^d+(2n+2)^2)`. Its printed new-reader axioms are exactly propext/Classical.choice/Quot.sound. All original895 input hashes equal the published MAC8 adoption and remain unchanged; only the hypothetical SAT object changes. This is owner/consumer preflight, not a downstream replay, full foreign-boundary seal, gate closure or permission to publish the API.

The six Ladner mathematical targets remain sorries in the separate proposal. Short-query preparation, numeric simulation-budget arithmetic and memo-state correctness/size remain explicit fill obligations. This new reader would remove the specific sharp-verifier interface gap; it does not by itself finish Ladner’s route or authorize a fill dispatch. If approved, implement by a gated PR; Seyoon alone merges.

The original/proposed/instrumented owner, exact patch, actual consumer, complete logs/exit receipts, helper drivers and toolchain context are retained. Live projects and compiled overlays are excluded from this frozen payload.
