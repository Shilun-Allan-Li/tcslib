<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/Peres.lean :: FABL.linearThresholdClass_closedUnderNegatingInputVariables -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sign-Flips Preserve Linear Thresholds

**Claim.** Composing a linear threshold function with coordinatewise multiplication by a fixed sign vector produces another linear threshold function.

**Proof.** Represent the given function using threshold parameters $a_0$ and $a_i$. After replacing each input coordinate $x_i$ by $z_i x_i$, the threshold expression has variable contribution $a_i\,\mathrm{signValue}(z_i)\,\mathrm{signValue}(x_i)$, because multiplication of signs corresponds to multiplication of their real values. Thus the composed function is represented by the same constant term $a_0$ and the new coefficient $a_i\,\mathrm{signValue}(z_i)$ at coordinate $i$. It is therefore a linear threshold function.
