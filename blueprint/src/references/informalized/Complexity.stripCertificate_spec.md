<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/NP.lean :: Complexity.stripCertificate_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterisation of certificate stripping

**Claim.** Stripping a binary string is undefined exactly when the string consists entirely of zeros; it returns $u$ exactly when the string is $u$ followed by a $1$ and some finite number of zeros.

**Proof.** Induct on the string $v$, using its first bit and whether stripping the tail is undefined or returns a list. If stripping the tail is undefined, the induction hypothesis identifies that tail as a string of zeros. With first bit false, the whole string is all zeros and stripping remains undefined; with first bit true, stripping returns the empty list, which is precisely the marker followed by that zero tail. Conversely, the all-zero tail gives the undefined result, while the padded-string lemma (Complexity.stripCertificate_pad) verifies the stated output for a marker followed by zeros. If stripping the tail returns some $w$, the induction hypothesis says the tail has the form $w$ followed by a marker and zeros. The recursive definition then shows that stripping the whole string returns its first bit prepended to $w$; this case cannot yield `none`. Conversely, any string of the required padded form strips to its prefix by the padded-string lemma. These cases establish both characterisations.

**Key facts.** `Complexity.stripCertificate_false`, `Complexity.stripCertificate_pad`.
