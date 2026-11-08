<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Cryptography/SecretSharing/Shamir.lean :: TCSlib.Shamir.perfectPrivacy -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Perfect Privacy of Threshold Sharing

**Claim.** For any set $B$ of fewer than $k$ parties and any two secrets $s,s'$, there is a bijection of the randomness space that makes the shares of $s'$ under the transformed randomness agree on $B$ with the shares of $s$ under the original randomness.

**Proof.** Since $B$ is unauthorized for the threshold-$k$ access structure, $|B|<k$. Interpolate a polynomial $r$ through the values $(s-s')/\operatorname{label}(b)$ at the nodes $\operatorname{label}(b)$ for $b\in B$. These nodes are distinct because party labels are injective. The interpolating polynomial has degree less than $|B|$, hence less than or equal to the required bound $k-2$; thus it is an allowed randomness polynomial. Translate every randomness polynomial $q$ by this fixed $r$. Translation is a bijection of the randomness space. At each $b\in B$, interpolation ensures that $r(\operatorname{label}(b))=(s-s')/\operatorname{label}(b)$. The sharing polynomial for secret $s'$ and translated randomness therefore evaluates there as
\[
s'+\operatorname{label}(b)(q(\operatorname{label}(b))+r(\operatorname{label}(b)))=s+\operatorname{label}(b)q(\operatorname{label}(b)),
\]
which is the share of $s$ with randomness $q$. Hence the translated randomness gives the required matching view.

**Key facts.** `TCSlib.Shamir.label_injective`, `TCSlib.Shamir.scheme_share`, `TCSlib.Shamir.poly_eval`.
