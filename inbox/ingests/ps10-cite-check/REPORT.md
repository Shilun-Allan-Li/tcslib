# Report · `ps10-cite-check` (PS10 ch. 5–8 citation check)

Documentation only: no Lean was run, no lake process was started, no `.lean` file was changed, nothing was transcribed.

## Inputs and verification

| Input | Pin | Check |
|---|---|---|
| Issue folder `outbox/ingests/ps10-cite-check/` | `exchange/pass-shelat-ch5-8` @ `6641966254eaeaeb1873d104069ada59fbda082f` (tip at start) | `sha256sum -c SHA256SUMS`: `README.md`, `brief.md`, `citations-ch5-8.tsv` all OK |
| Records tree | `cryptography/pass-shelat-ch2-4` @ `b76f804b4615123e6084a00d23fd9e6ff88fac92`, separate local checkout | `TCSlib/` identical to `ff0c2552` (the TSV's base) and to the branch tip `afd22b5d` |
| `Pass–Shelat.pdf` (root of the records tree) | same | SHA-256 `7624556077a7a272ba0b3ddb7cd47b96574fb0b4b4947a25467d1f91bb61bda8` ✔; 204 pages; book page = PDF page − 12 confirmed (p. 133 = PDF 145, p. 184 = PDF 196). Not copied, not committed. |

Method: `pdftotext -layout` per page for book pp. 131–185, plus `pdftoppm` page images where the layout mattered (for example pp. 157, 161, 179–180, and the printed labels of algorithms 99.1 and 104.3). Python was run as `python3 -I`, with scripts kept outside every extraction folder. Every one of the 871 (site, locator) pairs was read against the cited passage. One reviewer pass per chapter chunk (7 chunks) wrote a row for each pair, and every reported mismatch was then re-checked against the PDF text and the pinned source before entering this report.

## Summary

- **Check 1 (existence and kind):** all 48 numbered locators exist on the cited page with the cited kind. No wrong page, wrong kind or missing item.
- **Check 2 (lettered locators):** all 7 lettered passages exist where cited (table below).
- **Check 4 (section headings):** all 12 §-locators are real headings. §8.3.3 is the last line of p. 184 and has no body. The 3 page and 4 chapter locators also resolve.
- **Check 3 (content per site):** 871 (site, locator) pairs at 789 lines.
  - **831 OK.**
  - **40 content mismatches (Tier A)** at 40 sites, under 15 locators; 17 of them are one recurring "step 4" label.
  - **21 advisory notes (Tier B)**, a non-exhaustive list (see §3).
- **Recomputed list:** identical to `citations-ch5-8.tsv`: 67 locators, 871 sites, 789 lines, no difference (see §4).

Severity is "major" when a reader would be misled about what the book states (wrong step number, wrong quote, a bound or clause the book does not have). It is "minor" for loose quotes and for unlabelled generalizations or readings.

## 1. Per-locator status table

"A" counts sites whose description makes a claim the cited item does not make. "B" counts advisory label notes (§3), which do not change the status.

| Locator | Found in PDF (book page: printed label / heading) | Sites | A: content mismatch | B: advisory | Status |
|---|---|---:|---:|---:|---|
| Definition 134.1 | p. 134: "Definition 134.1 (MAC)" | 3 |  |  | OK |
| Definition 134.2 | p. 134: "Definition 134.2 (Security of a MAC)" | 7 |  |  | OK |
| Protocol 134.3 | p. 134: "protocol 134.3: MAC Scheme" | 3 |  |  | OK |
| Definition 135.1 | p. 135: "Definition 135.1 (Digital Signatures)" (printed after Theorem 135.4) | 3 |  |  | OK |
| Theorem 135.4 | p. 135: "Theorem 135.4" (PRF ⇒ secure MAC) | 10 | 1 |  | content mismatch (1 site) |
| Definition 136.2 | p. 136: "Definition 136.2 (Security of Digital Signatures)" | 11 |  |  | OK |
| Protocol 137.1 | p. 137: "protocol 137.1: One-Time Digital Signature Scheme" | 7 |  |  | OK |
| Theorem 137.2 | p. 137: "Theorem 137.2" (OWF ⇒ one-time secure) | 31 | 1 |  | content mismatch (1 site) |
| Definition 140.1 | p. 140: "Definition 140.1" (CRH family) | 9 | 1 |  | content mismatch (1 site) |
| Protocol 142.2 | p. 142: "protocol 142.2: Collision Resistant Hash Function" | 12 |  |  | OK |
| Theorem 142.3 | p. 142: "Theorem 142.3" (DL ⇒ CRH compressing by 1 bit) | 18 |  |  | OK |
| Theorem 144.1 | p. 144: "Theorem 144.1" (CRH + one-time sig. ⇒ sig. for {0,1}*) | 25 |  |  | OK |
| Protocol 144.2 | p. 144: "protocol 144.2: One-time Digital Signature for {0,1}*" | 2 |  |  | OK |
| Definition 152.1 | p. 152: "Definition 152.1 ((k, n) Secret Sharing)" | 3 |  |  | OK |
| Lemma 153.2 | p. 153: "Lemma 153.2 (Lagrange)" | 2 |  |  | OK |
| Protocol 154.4 | p. 154: "protocol 154.4: Shamir Secret Sharing Protocol" | 2 |  |  | OK |
| Proposition 154.5 | p. 154: "Proposition 154.5" (Shamir is secure) | 2 |  |  | OK |
| Definition 155.1 | pp. 155–156: "Definition 155.1 (Two-party Honest-but-Curious Secure Protocol)" | 13 | 3 |  | content mismatch (3 sites) |
| Algorithm 157.2 | p. 157: "algorithm 157.2: A Special Encryption Scheme" | 15 |  |  | OK |
| Claim 157.a | p. 157, §6.2.2 (unnumbered): "It is easy to modify construction 99.1 in order to build such an encryption scheme" (multi-message secure + "extra property") | 8 |  |  | OK |
| Construction 158.a | pp. 158–159, §6.2.3 (unnumbered): garbled gate by "doubly-encrypting each row of the table", rows shuffled | 2 |  |  | OK |
| Claim 159.a | p. 159, §6.2.3 (unnumbered): "All but one row will evaluate to ⊥"; evaluator learns no intermediate value | 11 |  |  | OK |
| Protocol 160.4 | p. 161 (float numbered from p. 160): "protocol 160.4: Oblivious Transfer Protocol"; Prop. 161.5 calls it "Construction 160.4" | 17 |  |  | OK |
| Definition 160.a | p. 160, §6.2.4 (unnumbered): 1/k-oblivious transfer, OT1/2(a1, a2, b) = (⊥, a_b) | 2 |  |  | OK |
| Proposition 161.5 | p. 161: "Proposition 161.5" (Construction 160.4 is h.b.c. OT) | 16 | 2 |  | content mismatch (2 sites) |
| Protocol 162.6 | p. 162: "protocol 162.6: Honest-but-Curious Secure Computation" | 106 | 1 |  | content mismatch (1 site) |
| Theorem 163.7 | p. 163: "Theorem 163.7" (proof to p. 164) | 146 | 1 | 4 | content mismatch (1 site) |
| Definition 168.1 | p. 168: "Definition 168.1 (CPA/CCA-Secure Encryption)" | 8 |  |  | OK |
| Theorem 168.2 | p. 168: "Theorem 168.2 π in construction 99.1 is CPA and CCA1 secure" | 17 |  |  | OK |
| Algorithm 169.3 | p. 169 (box continues to p. 170): "algorithm 169.3: π′: Many-message CCA2-secure Encryption" | 8 | 2 |  | content mismatch (2 sites) |
| Claim 169.a | p. 169, §7.1.3 (unnumbered): "the encryption scheme π is not CCA2 secure" + attack | 3 |  |  | OK |
| Theorem 170.4 | p. 170: "Theorem 170.4 π′ is CCA2-secure" | 22 |  |  | OK |
| Definition 171.5 | p. 171 (oracle table on p. 172): "Definition 171.5 (CPA/CCA-Secure Public Key Encryption)" | 19 | 2 |  | content mismatch (2 sites) |
| Definition 172.6 | p. 172: "Definition 172.6 (Non-Malleable Encryption)" | 7 |  |  | OK |
| Claim 172.a | p. 172 (unnumbered): "the encryption scheme in Construction 104.3 is CPA secure" | 1 |  |  | OK |
| Definition 173.7 | p. 173: "Definition 173.7 (Relation-Based Non-Malleable Encryption)" | 4 |  |  | OK |
| Theorem 174.8 | p. 174: "Theorem 174.8" (scheme is non-malleable) | 13 |  |  | OK |
| Theorem 175.1 | p. 175: "Theorem 175.1 (Sequential Composition)" (printed after Theorem 175.9; proof to p. 176) | 105 | 3 | 9 | content mismatch (3 sites) |
| Theorem 175.9 | p. 175: "Theorem 175.9" (CCA2 ⇒ non-malleable) | 8 |  |  | OK |
| Theorem 179.1 | p. 179: "Theorem 179.1" (p.p.t. decidable concept not learnable) | 12 |  | 8 | OK |
| Definition 179.a | p. 179, §8.1 (unnumbered): "The Learning Question" | 1 |  |  | OK |
| Theorem 180.1 | p. 180: "Theorem 180.1" (PRG ⇒ BPP ⊆ DTIME(2^{n^ε})) | 39 | 19 |  | content mismatch (19 sites) |
| Definition 181.1 | p. 181: "Definition 181.1 (ε-closeness)" | 6 |  |  | OK |
| Definition 181.2 | p. 181: "Definition 181.2 (ε-extractors)" | 5 |  |  | OK |
| Definition 182.3 | p. 182: "Definition 182.3 (Entropy)" | 3 |  |  | OK |
| Definition 183.4 | p. 183: "Definition 183.4 (Min Entropy)" | 3 |  |  | OK |
| Definition 183.5 | p. 183: "Definition 183.5 (k-source)" | 4 |  |  | OK |
| Theorem 183.6 | p. 183: "Theorem 183.6" (no extractor for efficiently computable (n−2)-sources) | 7 |  |  | OK |
| §6.2 | p. 154: heading "6.2 Yao Circuit Evaluation" | 1 |  |  | OK |
| §6.2.1 | p. 156: heading "6.2.1 Circuit Representations" | 1 |  |  | OK |
| §6.2.1–6.2.3 | pp. 156–159: headings 6.2.1, 6.2.2, 6.2.3 | 1 |  |  | OK |
| §6.2.2 | p. 157: heading "6.2.2 Garbled Wires" | 15 | 4 |  | content mismatch (4 sites) |
| §6.2.2–6.2.3 | pp. 157–159: headings 6.2.2, 6.2.3 | 3 |  |  | OK |
| §6.2.3 | p. 157: heading "6.2.3 Garbled Gates" | 16 |  |  | OK |
| §7.1.3 | p. 169: heading "7.1.3 A CCA2-Secure Encryption Scheme" | 3 |  |  | OK |
| §7.1.4 | p. 171: heading "7.1.4 CCA-secure Public-Key Encryption" | 1 |  |  | OK |
| §7.2.1 | p. 175: heading "7.2.1 Sequential Composition" | 5 |  |  | OK |
| §8.1 | p. 179: heading "8.1 A Negative Result for Learning" | 7 |  |  | OK |
| §8.2 | p. 180: heading "8.2 Derandomization" | 22 |  |  | OK |
| §8.3.3 | p. 184, last line: heading "8.3.3 Left-over hash lemma" (no body) | 2 |  |  | OK |
| p. 169 | p. 169 exists (§7.1.2 proof end, §7.1.3, Algorithm 169.3) | 1 |  |  | OK |
| p. 172 | p. 172 exists (Def. 171.5 oracle table, Claim 172.a, §7.1.5, Def. 172.6) | 1 |  |  | OK |
| p. 182 | p. 182 exists (§8.3.2, Definition 182.3 and the uniform example) | 2 |  |  | OK |
| ch. 5 | p. 133: "Chapter 5 Authentication" | 1 |  |  | OK |
| ch. 5–8 | pp. 133–184: chapters 5–8 | 3 |  |  | OK |
| ch. 7 | p. 167: "Chapter 7 Composability" | 4 |  |  | OK |
| ch. 8 | p. 179: "Chapter 8 *More on Randomness and Pseudorandomness" | 1 |  |  | OK |
| **Total** | | **871** | **40** | **21** | |

### Lettered locators (check 2)

| Locator | Passage found |
|---|---|
| Claim 157.a | p. 157, §6.2.2: "It is easy to modify construction 99.1 in order to build such an encryption scheme", i.e. a multi-message secure scheme with the "following extra property" (wrong key ⇒ ⊥ w.h.p.), realised by algorithm 157.2 |
| Construction 158.a | pp. 158–159, §6.2.3: the garbled gate, "doubly-encrypting each row of the table" with randomly shuffled rows |
| Claim 159.a | p. 159, §6.2.3: "All but one row will evaluate to ⊥", plus "the evaluating party does not learn any intermediate value" |
| Definition 160.a | p. 160, §6.2.4: "A 1/k-oblivious transfer protocol …", OT1/2(a1, a2, b) = (⊥, a_b) |
| Claim 169.a | p. 169, §7.1.3: "the encryption scheme π is not CCA2 secure", with the r‖c + 1 attack |
| Claim 172.a | p. 172: "It is not hard to see that the encryption scheme in Construction 104.3 is CPA secure" (stated without proof) |
| Definition 179.a | p. 179, §8.1: "The Learning Question" |

### Notes on the brief and the book's labels

- **160.4 is printed as a *protocol*:** "protocol 160.4: Oblivious Transfer Protocol". The float is numbered from p. 160 but set at the top of p. 161. Only the statement of Proposition 161.5 calls it "Construction 160.4". The brief's note "160.4 is a 'Construction'" therefore describes the cross-reference, not the label. "Protocol 160.4" (the form every repository site uses) is correct.
- **Out-of-order numbering in the book:** Definition 135.1 is printed after Theorem 135.4 on p. 135, and Theorem 175.1 after Theorem 175.9 on p. 175. Both exist as cited.
- **Labels the book also calls "construction":** 99.1 and 104.3 are printed as "algorithm 99.1" and "algorithm 104.3", while pp. 168 and 172 call them "construction". Either kind is defensible.
- **Book typos the repository already records correctly:** algorithm 157.2 writes `x` for `m`, protocol 160.4 sends "(z1, …, z4)", and algorithm 169.3 outputs `f_k2(c)` with `c` undefined while `Dec′` checks `f_k2(c1)`.

## 2. Mismatching sites (Tier A), with suggested docstring corrections

Paths are relative to the repository root at `b76f804b`. Each entry gives the citation, the problem, and a suggested correction.

### A1. Theorem 180.1, "step 4" (17 sites; major)
The proof of Theorem 180.1 (p. 180) numbers only two items, steps 1–2 of the machine M′. It has no step 4. The content these sites mean, deterministic enumeration of all seeds, is the proof's final paragraph: "Since M′ only uses n^{ε/2} random bits, a deterministic machine that simulates M′ on all possible random tapes will take time 2^{n^{ε/2}}·poly(n) ∈ O(2^{n^ε})". No repository sketch defines "step 4" either; the number comes from the campaign's route numbering.

Sites:
- `TCSlib/Complexity/Randomized/Build/IterateFind.lean:566`
- `TCSlib/Complexity/Randomized/SeedMajority.lean:26`, `:74`, `:173`, `:235`
- `TCSlib/Complexity/Randomized/SeedMajority/Enumeration.lean:42`
- `TCSlib/Complexity/Randomized/SeedMajority/State.lean:70`, `:99`, `:142`, `:155`, `:183`, `:220`
- `TCSlib/Complexity/Randomized/SeedMajority/Words.lean:45`, `:88`, `:116`, `:131`, `:163`

Correction: replace "step 4" / "step 4 of the proof" with "final paragraph of the proof", for example `[PS10, §8.2, Theorem 180.1, final paragraph of the proof]`.

### A2. Theorem 180.1, other sites (2 sites; major)
- `TCSlib/Complexity/Randomized/SeedMajority.lean:83`
  - Citation: "with the test **and** the width of the paper proof, both piecewise in a threshold length `n₀`".
  - Problem: the book's proof has no threshold and no piecewise test or width. It runs one machine M′ with seed length n^{ε/2} at every length. The piecewise construction is the repository's route.
  - Correction: "with a test and width adapted from the paper proof (a repository construction, piecewise in a threshold length `n₀`; the book uses seed length `n^{ε/2}` at every length)".
- `TCSlib/Cryptography/Randomness/Derandomization/RootSchedule.lean:16`
  - Citation: "The schedule in the proof of [PS10, Theorem 180.1] is the least natural `t` with `n ≤ t ^ d`."
  - Problem: the book's seed length is n^{ε/2}. The ceiling integer root with exponent `d` (1/d < ε) is a repository substitute that the docstring does not label.
  - Correction: "The seed schedule replacing the book's `n^{ε/2}` in the proof of [PS10, Theorem 180.1] (a repository substitute: integer exponents) is the least natural `t` with `n ≤ t ^ d`."

### A3. Theorem 135.4, nonexistent "step 6" (1 site; major)
- `TCSlib/Cryptography/Authentication/MAC/FromPRF/Reduction.lean:16`
  - Citation: "Steps 2, 3 and 6 of the proof of [PS10, Theorem 135.4]".
  - Problem: the book's proof (p. 135) is one unnumbered paragraph. The repository's own numbered sketch, the `prfMAC_secure` docstring in `MAC/FromPRF.lean`, has steps 1–5 only. The content described is steps 2–3, as `Reduction.lean:196` itself says.
  - Correction: "Steps 2 and 3 of the proof of [PS10, Theorem 135.4]".

### A4. Theorem 137.2, "best-position advice step" (1 site; minor)
- `TCSlib/Cryptography/Authentication/Signatures/Lamport/Advice.lean:112`
  - Citation: "This is the best-position advice step in [PS10, proof of Theorem 137.2]."
  - Problem: the book's reduction B picks the position i and the bit c at random ("Pick a random i ∈ {1, …, n} and c ∈ {0, 1}", p. 138). It has no advice step. Fixing the best position as non-uniform advice is the repository's replacement.
  - Correction: "This replaces the random choice of position in [PS10, proof of Theorem 137.2] by non-uniform advice (a repository step)."

### A5. Theorem 175.1 (3 sites; 1 major, 2 minor)
- `TCSlib/Cryptography/Composability/SequentialZK.lean:916` (major)
  - Citation: `[PS10, Theorem 175.1, "(P_Q, V_Q) is an interactive proof"]`.
  - Problem: this text is not in the book. Theorem 175.1 *assumes* "let (P_Q, V_Q) be an interactive proof (argument)" and concludes only that it is a "perfect/computational ZK interactive proof".
  - Correction: `[PS10, Theorem 175.1, the hypothesis that (P_Q, V_Q) is an interactive proof (argument), here proved]`.
- `TCSlib/Cryptography/Composability/SequentialZK/Normalization.lean:18` (minor)
  - Citation: "the normalization in [PS10, Theorem 175.1]".
  - Problem: the proof (pp. 175–176) has no normalization. S_Q simply takes the messages m̄_{i+1} from S's view.
  - Correction: "the repository's message normalization for [PS10, Theorem 175.1] (the book reads m̄_{i+1} from the simulated view directly)".
- `TCSlib/Cryptography/Composability/SequentialZK/NormalizationMachine.lean:15` (minor)
  - Citation: "The message-slot normalization of [PS10, Theorem 175.1]".
  - Problem: same as the previous site.
  - Correction: "The message-slot normalization (a repository step in the proof of [PS10, Theorem 175.1])".

### A6. Algorithm 169.3, tag over the whole ciphertext (2 sites; minor)
As printed (pp. 169–170), algorithm 169.3 draws k1, k2 ← U_n, outputs `(r, c1, f_k2(c))` with `c` undefined, and `Dec′` tests `f_k2(c1)`. Tagging `r‖c1` under a 2n-bit key is the repository's reading. It is explained in the source notes of `EncryptThenTag.lean` but presented as the book's at:
- `TCSlib/Cryptography/Encryption/PrivateKey.lean:70`
  - Citation: "the encrypt-then-tag scheme, which tags the whole ciphertext under an independent key [PS10, Algorithm 169.3]".
  - Correction: "… which tags `r ‖ c₁` under an independent key (the repository's reading of [PS10, Algorithm 169.3], whose printed tag is `f_{k₂}(c)` / `f_{k₂}(c₁)`; see `EncryptThenTag`)".
- `TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Games.lean:16`
  - Citation: "The scheme of [PS10, Algorithm 169.3] encrypts `m` as `⟨r, ⟨c₁, t⟩⟩` … `t = g(r ‖ c₁)` … at parameters `n` and `2n`".
  - Correction: "The scheme of [PS10, Algorithm 169.3], in the reading fixed in `EncryptThenTag.lean` (tag over `r ‖ c₁`, `k₂` of `2n` bits), encrypts …".

### A7. Definition 171.5, the claim after it (2 sites; 1 major, 1 minor)
- `TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity/ChallengeSim.lean:18` (major; the quote is at lines 27–28)
  - Citation: `the informal "condition on the adversary's choice of messages" in the proof of the claim after Definition 171.5`.
  - Problem: the claim on p. 172 is stated without proof ("It is not hard to see …"), and the quoted phrase does not occur in the book.
  - Correction: "This replaces the informal step of conditioning on the adversary's choice of messages in the repository's proof of the claim after [PS10, Definition 171.5] (the book gives no proof)." Drop the quotation marks.
- `TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity/PaddedCPA.lean:16` (minor)
  - Citation: "The claim after [PS10, Definition 171.5]: a single-bit secure public-key scheme, padded to fixed length, … is CPA-secure".
  - Problem: the claim on p. 172 is about "the encryption scheme in Construction 104.3" only. The general statement is an unlabelled generalization.
  - Correction: "A generalization of the claim after [PS10, Definition 171.5] (stated there for Construction 104.3; that instance is `TrapdoorCPA`): …".

### A8. Definition 140.1, deviation note (1 site; minor)
- `TCSlib/Cryptography/Hashing/CollisionResistant.lean:45` (note in the same docstring)
  - Citation: the note says "in Construction 142.2 the exponents range over Z_{p−1}".
  - Problem: protocol 142.2 (p. 142) takes "an n-bit string x and bit b", and the proof of Theorem 142.3 says the input is in Z*_p × {0,1}. The book never says Z_{p−1}. The description of Definition 140.1 itself is correct.
  - Correction: "in protocol 142.2 the input `x` is an `n`-bit string (the proof of Theorem 142.3 treats it as an element of `Z*_p`); the repository restricts it to `x < p − 1`".

### A9. §6.2.2, quote "the extra property" (4 sites; minor)
p. 157 says "with the following extra property", and the string "the extra property" is not in the book. The property is stated for one key and for n-bit messages m ∈ {0,1}^n.
- `TCSlib/Cryptography/SecureComputation/Garbling.lean:40`: `[PS10]'s "the extra property" (§6.2.2)`, applied to key *lists*.
- `TCSlib/Cryptography/SecureComputation/Garbling.lean:160`: `[PS10, §6.2.2, "the extra property"]`, a two-position version, unlabelled.
- `TCSlib/Cryptography/SecureComputation/SpecialEncryptionSecurity.lean:23`: `([PS10, §6.2.2], "the extra property")`.
- `TCSlib/Cryptography/SecureComputation/SpecialEncryptionSecurity.lean:234`: `[PS10, §6.2.2, "the extra property"]`, stated for any polynomial length ℓ(n).

Correction: quote "the following extra property" or cite without quotes, as in `[PS10, §6.2.2, extra property]`. At `Garbling.lean:40` and `:160` add "(generalized from one key to key lists / two positions)". At `SpecialEncryptionSecurity.lean:234` add "(the book: n-bit messages)".

### A10. Proposition 161.5, a 2δ(n) bound attributed to the proof (2 sites; major)
The proof of Proposition 161.5 (p. 162) says the two views "are identically distributed", since f is a permutation. The 2δ(n) slack comes from the repository's approximately uniform sampler.
- `TCSlib/Cryptography/SecureComputation/ObliviousTransfer/ViewA.lean:18`
  - Citation: "any distinguisher's advantage is at most `2δ(n)` [PS10, Proposition 161.5, proof]".
  - Correction: "… at most `2δ(n)` (the book's proof has identical distributions for a uniform sampler; the `δ` slack is the repository's sampler) [PS10, Proposition 161.5, proof]".
- `TCSlib/Cryptography/SecureComputation/ObliviousTransfer/ViewA.lean:50`
  - Citation: "`eval ⟨i, Sample(i; s)⟩` is `2δ(n)`-close to `Sample(i; s)` [PS10, Proposition 161.5, proof]".
  - Correction: the same annotation.

### A11. Definition 155.1, clauses it does not have (3 sites; major)
Definition 155.1 (pp. 155–156) requires only n.u. p.p.t. simulators S_A, S_B whose output is indistinguishable from the (view, output) pair. It has no efficiency clause for the parties, no message-length bound and no ideal calls. `SecureComputation/Defs.lean` itself labels polynomial-time parties a repository deviation (ruling of 2026-11-05).
- `TCSlib/Cryptography/SecureComputation/ObliviousTransfer/Efficiency.lean:530`
  - Citation: `[PS10, Definition 155.1, efficiency]`.
  - Correction: `[PS10, Protocol 160.4]; efficiency of the parties is a repository requirement added to [PS10, Definition 155.1] (ruling of 2026-11-05)`.
- `TCSlib/Cryptography/SecureComputation/Yao.lean:853`
  - Citation: "(the efficiency clause of [PS10, Definition 155.1], `HybridProtocol.PolyTime`, ruling of 2026-11-05)".
  - Correction: "(the efficiency requirement `HybridProtocol.PolyTime` that the repository adds to [PS10, Definition 155.1], ruling of 2026-11-05)".
- `TCSlib/Cryptography/SecureComputation/Yao/HybridProof/Lengths.lean:18`
  - Citation: "message bounds independent of ideal-call answers, as required by [PS10, Definition 155.1]".
  - Correction: "… as required by the repository's efficiency clause (cf. [PS10, Definition 155.1], which sets no length bound)".

### A12. Protocol 162.6, output decoding information (1 site; major)
- `TCSlib/Cryptography/SecureComputation/Yao/HybridProof/AliceProgram.lean:90`
  - Citation: "[PS10, Protocol 162.6], the output decoding information".
  - Problem: Alice's message in protocol 162.6 (p. 162) is the garbled circuit and the keys of x's input wires. It contains no output-decoding information, and the module docstring of `Yao.lean` lists output decoding as a deviation.
  - Correction: "the output decoding information (a repository addition to [PS10, Protocol 162.6]; see the deviations in `Yao.lean`)".

### A13. Theorem 163.7, "statistical parts" (1 site; major)
- `TCSlib/Cryptography/SecureComputation/Yao/HybridProof/StatisticalSwitch.lean:18` (module docstring; the reference entry is at line 32)
  - Citation: "for the statistical parts of [PS10, Theorem 163.7]", with the reference entry "Theorem 163.7 (the statistical output switch)".
  - Problem: the proof (pp. 163–164) has no statistical or bad-event step. It ends "the last step is also identically distributed". The output switch outside a decryption-failure event is the repository's repair.
  - Correction: "for the statistical output switch that the repository adds to the proof of [PS10, Theorem 163.7] (the book asserts the last step is identically distributed)". Reference entry: "Theorem 163.7 (proof; the statistical switch is a repository addition)".

## 3. Advisory notes (Tier B, non-exhaustive)

These sites attach a `[PS10, Item, <label>]` tag whose label names a repository proof step the book does not contain, with no deviation marker at the site. The brief does not ask that a whole item be cited only for parts the book spells out, so these do not change the status. They were collected where the review noticed them; not every part-label in the 871 sites was audited to this standard. Suggested fix throughout: mark the label as the repository's, for example `[PS10, Theorem 163.7; coin relabeling is a repository step]`.

| Site | Label | Book |
|---|---|---|
| `TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinRelabel.lean:132` | Theorem 163.7, "coin relabeling" | the proof says only "Using a hybrid argument …" (p. 164) |
| `…/Yao/HybridProof/SimulationBound.lean:84` | Theorem 163.7, "Bob's statistical output switch" | no statistical step (see A13) |
| `…/Yao/HybridProof/StatisticalSwitch.lean:41`, `:67` | Theorem 163.7, "statistical switch" | same |
| `TCSlib/Cryptography/Composability/SequentialZK/RepeatedSoundness.lean:139` | Theorem 175.1, "multiplication of sequential soundness error" | the theorem states no soundness bound (soundness of (P_Q, V_Q) is a hypothesis) |
| `…/SequentialZK/RepeatedSoundness.lean:196` | Theorem 175.1, "sequential soundness error `s^q`" | same |
| `…/SequentialZK/SimulatorMachine.lean:192`, `:312` | Theorem 175.1, "strict-PPT sequential simulation" | the book's S_Q runs in *expected* polynomial time (p. 176); strict PPT is declared a deviation only in `SequentialZK.lean` |
| `…/SequentialZK/PhaseView.lean:49`, `:67`, `:159` | Theorem 175.1, "canonical phase-view fallback", "phase-shape normalization", "bounded canonical phase-view normalization" | no normalization in the book (see A5) |
| `…/SequentialZK/NormalizedStep.lean:47` | Theorem 175.1, "normalization of a real wrapped phase" | same |
| `…/SequentialZK/SuffixMachine.lean:161` | Theorem 175.1, "normalized simulated suffix" | same |
| `TCSlib/Cryptography/Randomness/Learning.lean:117` | heading "Theorem 179.1 (b)", sketch called "the source's, made explicit" | Theorem 179.1 has no parts; its "Proof sketch" (p. 179) only fixes S, C_i, I and asserts unpredictability |
| `…/Randomness/Learning/Distinguisher.lean:14`, `:82` | "Step 1 of [PS10, Theorem 179.1, proof]", "The distinguisher of [PS10, Theorem 179.1, proof]" | the sketch has no steps and no distinguisher |
| `…/Randomness/Learning/Law.lean:16`, `:144` | "Step 1 …", "proof, step 1" | same |
| `…/Randomness/Learning/Random.lean:15`, `:135` | "Step 2 …", "proof, step 2" | same |
| `…/Randomness/Learning/Sample.lean:15` | "The distinguisher of [PS10, Theorem 179.1, proof]" | same |

Related notes, outside the listed (site, locator) pairs and therefore not counted:
- `TCSlib/Cryptography/SecureComputation/ObliviousTransfer/Efficiency.lean:15–16`: "the efficiency requirement `Functionality.PolyTime` of Definition 155.1". This is the same problem as A11; the site's listed locator is Protocol 160.4.
- `TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity.lean:63`: "The claim after Definition 171.5 … (single-bit security gives CPA security)". This is the same generalization as A7 and is on a line without "PS10".
- `TCSlib/Cryptography/SecureComputation/ObliviousTransfer/Simulators.lean:14`, `:153`: "the simulators S_A and S_B of [PS10, Proposition 161.5]". The book constructs only S_A; "The construction of S_B is left as an exercise" (p. 162).
- `TCSlib/Cryptography/SecureComputation/YaoReal.lean:86`: describes Proposition 161.5's hypotheses with an *enhanced* hard-core predicate. The book uses "a hardcore predicate" (pp. 160–161).
- `TCSlib/Cryptography/Hashing/FromDiscreteLog.lean:709`: cites the "probability bound in Theorem 142.3" for a bound with an extra additive (1/2)^n that the book does not have. It is explained only in the main theorem's sketch, at line 751.
- `TCSlib/Cryptography/Authentication/Signatures/Defs.lean:156`: the forgery game runs A on pk, while Definition 136.2 writes A^{Sign_sk(·)}(1^n). This is a reasonable reading (the book's proofs run A(pk, 1^n)) and is left OK.

## 4. Recomputed citation list vs. the TSV

Command: `git grep -n "PS10" b76f804b -- 'TCSlib/**.lean'` gives 2,842 lines. These were filtered to ch. 5–8 by the brief's ranges: items 133.x–184.x, §5–8, pp. 133–184, ch. 5–8. Abbreviated kinds (Def/Defs, Thm, Prop, Prot, Lem, Alg) and plural lists ("Definitions 183.4 and 183.5") are normalized to the canonical kind.

**Result: no difference.** The recomputed list has the same 67 locators, and every locator has exactly the same sites as `citations-ch5-8.tsv`: 871 (site, locator) pairs at 789 distinct lines. The pin's `TCSlib/` tree is identical to `ff0c2552`.

The TSV is reproduced exactly only with two counting conventions that the brief does not spell out:
1. **Continuation lines.** A `[PS10, …` bracket left open at the end of a line is followed to its closing `]`, and locators on the continuation line are credited to the line that holds "PS10". A strict one-line grep would **miss 11 pairs**:
   - `Authentication/Signatures/Lamport.lean:894`, `Lamport/Averaging.lean:127`, `Lamport/Machine.lean:322` and `Lamport/Realization.lean:81` (Theorem 137.2);
   - `SecureComputation/ComposeSecurity/Correct.lean:44` (Definition 155.1);
   - `SecureComputation/Yao.lean:170` (§6.2.1);
   - `Yao.lean:681` and `:795` (Claim 159.a);
   - `Yao.lean:744` (Theorem 163.7);
   - `Encryption/PublicKey/BitwiseCPA/Planted.lean:17` (Definition 171.5);
   - `InformationTheory/Entropy.lean:84` (Definition 182.3).
2. **Other sources on PS10 lines.** Locators that belong to another source on a PS10 line are excluded: Vad12 Ch. 6 and §6.1 (`InformationTheory/Extractors.lean:124`, `:166`), AB09 §6.2 and §7.1, Gol04 §7.3 and §7.3.2, and "DESIGN §7". Counting them would **add 7 spurious locators**: ch. 6, §6.1, §6.2-from-AB09, §7, §7.1, §7.3 and §7.3.2.

Locators on the same line as "PS10" but outside its brackets are counted. Examples are the bold declaration names (`**Claim 157.a …** [PS10, §6.2.2]`) and prose after a bare `[PS10]`, as in `Extractors.lean:166`, "its §8.3.3".

Outside the brief's scope: 419 lines in `TCSlib/**.lean` name a ch. 5–8 item ("Protocol 162.6", …) on a line without "PS10". They are not in the TSV, were not classified, and were not checked.
