<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Expressions.lean :: Light.Compiler.cT_mem_temps_of_height -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expression temporary membership

**Claim.** If $k+\mathrm{height}(e)\le 2F+1$, then the temporary address $-(23+4k)$ belongs to the specified temporary set.

**Proof.** The expression height is positive (\(\mathrm{height}(e)>0\), by `Light.Expr.height_pos`). Hence $k<k+\mathrm{height}(e)$. Combining this with the assumed upper bound gives $k<2F+1$, so in particular $k\le 2F$. The temporary set contains every address of the form $-(23+4j)$ for an index $j$ between $k$ and $2F$; choose $j=k$. The address in question is exactly this element, so it belongs to the set.

**Key facts.** `Light.Expr.height_pos`.
