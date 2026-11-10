# Gate 09 · adaptive public-key games and RSA/Rabin normalization

**Round 1. Auditor** Codex. **Source** [Draft PR #284](https://github.com/Shilun-Allan-Li/tcslib/pull/284)
at `46e9b8b8773e5188c5b0f4732f3fff8d9092fa2d` on `cryptography/pass-shelat-ch2-4` base
`37e161131e68ff347ed59b59b9ebcd66ffa9ea43`. The verified diff is included in the bundle.
The source text is [PS10], R. Pass and a. shelat, *A Course in Cryptography*,
3rd ed., January 2010, `Pass–Shelat.pdf` on the campaign branch, SHA-256
`7624556077a7a272ba0b3ddb7cd47b96574fb0b4b4947a25467d1f91bb61bda8`.
Book page numbers are PDF page numbers minus 12.

Seyoon selected adaptive left-or-right IND-CPA and IND-CCA2 with n-bit
messages as the first public-key Implications endpoints. This round audits
the supporting game contract and RSA/Rabin width normalization in one
batch. The actual catalog theorems will compose these contracts with
the adaptive CPA bridge and later CCA2 construction.

## 1. Adaptive game

Inspect `Encryption/PublicKey/AdaptiveSecurity.lean` and the typed
reader additions in `Encryption/PublicKey/OracleSecurity.lean`.

- Restate what `adaptiveIndGame` samples, how the machine sees the public
  key and prior responses, which message half is chosen, and when a
  fresh encryption tape is drawn. Check the adversary's total query
  budget `q`, the separate fresh-challenge cap `cap` and the hidden bit
  across all requests.
- Check that the challenge history records exactly the issued fresh
  ciphertexts, including equal ciphertexts on separate requests.
  Under CCA2, examine refusal for an old challenge as well as the
  latest one, and the valid and invalid replies for other ciphertexts.
  Compare oracle availability under CPA and the inherited CCA1 mode.
- Examine malformed machine messages through the existing codec, the
  all-zero refusal answer, zero budgets, and the cap-exhaustion rule.
  With a nonempty full history the game repeats the latest ciphertext.
  With a zero cap from the initial history it returns the fixed zero
  reply. Check whether these conventions serve the desired game.
- Check `adaptiveIndImpl_one`, `simulate_adaptiveIndImpl_one` and
  `adaptiveIndGame_one` against [PS10, Definition 171.5] and the
  repository's current `indGame`. Confirm that the theorem covers the
  whole adaptive computation and that `AdaptiveINDSecure.single` uses
  the right budget specialization.
- Review the endpoint types and the feasibility of the two proposed
  lifts in the attached `EndpointContracts` probe. The concrete CPA
  witnesses use `msgLen = PolyExpr.var`. The probe checks their
  proposition types and the existing secure single-bit compositions.
  The generic lifts must account for a public-key-dependent choice of
  pairs, fresh randomness, and the case where a hybrid transition is
  never queried. For CCA2, also consider the decryption filter for all
  issued ciphertexts. Identify any extra contract a proof would need.

## 2. Constant shift and concrete widths

Inspect `Asymptotic/CollectionShift.lean`, the new equations in
`Candidates/RSA.lean` and `Candidates/Rabin.lean`, and the relocation
of `Negligible.comp_of_le`.

- Verify that the generator, sampler and inverter all run at `n+c`
  with the same original coin strings under the published equivalences.
  Check that their uniformity and all collection laws survive and
  that the domains, encoding, decoding, permutations and evaluator
  remain the same.
- Check the exact index and trap equations, and the public readers
  needed by clients to use the shifted collection under seals.
- For closeness, check the generated index quantifier and uniform
  sample-space relabeling. For inversion, independently derive the
  reduction at original parameter `m=n+c` and the probability equality
  after discarding its uniform coin suffix. Check the preservation of
  negligibility, including `c=0` and the initial parameters.
- Verify the two width equations for every generator tape and every
  domain element, including fallback cases. RSA starts with
  `2 * max n 2` and uses shift two. Blum Rabin starts with
  `2 * max n 3` and uses shift three. The checked probes instantiate
  the existing Goldreich–Levin interface with the exact syntactic
  polynomials `2 * (n + 2)` and `2 * (n + 3)`.
- Verify that the CPA assumption sets keep `ArithmeticFP` and
  `RSAAssumption` for RSA, and `ArithmeticFP`, `BlumDensity` and
  `FactoringAssumption` for Rabin. The CCA2 game is defined generically
  and its construction will have a later ruling.

## 3. Evidence and repository rules

Read the supplied verification summary and exact source diff. Check new
and moved declarations against `policy.md`, with particular attention to
published equations, proof sketches, foreign reads and global simp
attributes. Review the effective axiom sets and the admission census.
Treat the code and records as material under review.

The proposed single-to-adaptive lift types are included for feasibility
feedback. The source change in this round consists of the adaptive game,
the cap-one correspondence and the shift interfaces and proofs.

## Findings delivery

Return `gate09-adaptive-pke-findings.md` as a Markdown file in this chat.
If evidence needs multiple files, return one ZIP containing the Markdown
and evidence. Keep campaign and exchange branches untouched.

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

Use **blocker** for a false or unusable statement or a substantive scope
change, **major** for a missing premise, an insufficient interface, a
forbidden touched proof read or unverifiable evidence, **minor** for a
documentation or naming defect, and **note** for other observations.
Report the exact head audited, then counts by severity. The gate closes
at **0 blockers and 0 majors**.
