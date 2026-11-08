<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Cryptography/SecretSharing/Shamir.lean :: TCSlib.Shamir.natCard_coins_view -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Number of Compatible Sharing Polynomials

**Claim.** If $F$ is a finite field, $k>0$, $k\le |F|$, and $B$ is a set of fewer than $k$ nonzero field elements, then for any secret $s$ and prescribed values on $B$, exactly $|F|^{k-1-|B|}$ sharing polynomials of the form $s+Xq(X)$ with $\deg q<k-1$ realize those values.

**Proof.** First choose a set $S$ of $k-1$ parties containing $B$. This is possible because $|B|\le k-1$ and the number of parties, which are the nonzero elements of $F$, is $|F|-1\ge k-1$. Party labels are injective, so interpolation nodes indexed by $S$ are distinct. For a polynomial $q$ and party $b$, its share is $s+\operatorname{label}(b)q(\operatorname{label}(b))$. Because every party label is nonzero, requiring this share to equal $w(b)$ is equivalent to prescribing
\[
q(\operatorname{label}(b))=\frac{w(b)-s}{\operatorname{label}(b)}.
\]
Thus the compatible randomness polynomials are in bijection with degree-less-than-$(k-1)$ polynomials satisfying these evaluation prescriptions on $B$. The interpolation counting theorem says that for distinct nodes indexed by $S$, prescribing values on its subset $B$ leaves exactly $|F|^{|S|-|B|}$ such polynomials (`TCSlib.Interpolation.natCard_degreeLT_eval_eq`). Since $|S|=k-1$, this number is $|F|^{k-1-|B|}$.

**Key facts.** `TCSlib.Shamir.label_injective`, `TCSlib.Shamir.scheme_share`, `TCSlib.Shamir.poly_eval`, `TCSlib.Interpolation.natCard_degreeLT_eval_eq`.
