# Gate 06: the external statement gate of ch. 5–8 (S4; plan draft)

**Status: draft (2026-11-05, overnight).** This is the one external statement gate of the S4
statement phase (`PassShelatChapter5-8Plan.md`, Phasing step 3). It audits every core item of
prongs A–D, stated with a sketch and compiling, before any fill brief is issued.

- **What is audited:** definitions, statements, docstrings and proof sketches against [PS10]
  (and the second sources cited per item). Proofs are out of scope, except the short ones that
  carry a definition's correctness (for example `correct` fields and length lemmas).
- **The tree:** one integration commit that merges the four prong branches. Each is stacked on
  S2b, so the merge needs S2b's PR to land first, then the prongs merged onto it, then one fresh
  replay of the union.
- **Every pack carries:** the S2 framework's API (gate 02's and gate 04's subjects, as context);
  the inventory `inventory-ch5-8.md` with its errata; the decision log; `policy.md`; the PDF.

## Packs (by prong; packs may run in parallel)

| Pack | Content | Files (branch head at drafting) | Items |
|---|---|---|---|
| 06A | authentication (ch. 5) | `Authentication/{Defs, PRFMAC, Lamport, DLHash, HashAndSign}` (prong A, `2d7b5441`, complete) | Defs 134.1, 134.2, 135.1, 136.2, 136.a, 140.1; Prot 134.3, 137.1, 142.2, 144.2; Thms 135.4, 137.2, 142.3, 144.1 |
| 06B | secure computation (§6.2) | `SecureComputation/{Defs, ObliviousTransfer, SpecialEncryption, SpecialEncryptionSecurity, Garbling, GarblingSpecial, GarblingSecurity}` (prong B, `d8ef9b40`; Yao waits for Q-5) | Def 155.1; Alg 157.2, Claim 157.a; Constr 158.a, Claim 159.a; Def 160.a, Prot 160.4, Prop 161.5; Prot 162.6, Thm 163.7 |
| 06C | composability (ch. 7) | `Composability/{Defs, PRFScheme, CCA2Scheme, PublicKey, NonMalleable, SequentialZK}` (prong C, `61c06756`) | Defs 168.1, 171.5, 172.6, 173.7; Thm 168.2, Claim 169.a, Alg 169.3, Thm 170.4, Claim 172.a, Thm 174.8, Thm 175.9 (optional), Thm 175.1 |
| 06D | randomness (ch. 8) | `Randomness/{Extraction, Learning, BPPBridge, Derandomization}` and the PAC layer (prong D, `6ea900ae`, complete) | Def 179.a (with the PAC layer, #194), Thm 179.1, Thm 180.1, Thm 183.6 |

## Findings already made in the statement phase (the auditor should check the repairs)

- **The `Dec` guard** (#193): Algorithm 99.1's `Dec` refuses malformed ciphertexts; without it
  Thm 168.2's CCA1 half is false.
- **`π′`'s tag covers `(r, c₁)`** (inventory erratum): tagging `c₁` alone is not CCA2-secure.
- **Public-key games pad ciphertexts** (ruling): canonical padding, with non-canonical strings
  refused.
- **Non-malleability follows [PSV06] and [PSV07]** (ruling): Thm 174.8 is not true as written in
  [PS10]. [PSV07] shows the equivalence holds under CPA only (its Thms 3 and 4).
- **`CRH` carries domain and range tests:** with fixed-length domains, Thm 142.3 had trivial
  collisions.
- **Thm 144.1 needs a full-domain CRH:** the CRH game counts only in-domain collisions.
- **Thm 175.1 assumes `ProverBounded`:** D8's verifier efficiency allows exponential views
  (Q-1, ruled: keep D8 with this hypothesis).
- **Prop 161.5 assumes `SamplerCanonical`:** non-canonical encodings would leak the receiver's
  choice.
- **OT has five messages:** D8's output convention (the last mover's last message is its output).
- **T2 (interactive handlers)** is stated on S2b for the reductions that forward queries.

## Open before dispatch

- Def 173.7 and Thm 174.8: the sources are in hand ([PSV06], [PSV07]; Q-2 done); being stated.
  Pack 06C attaches both PDFs.
- Prong B: Yao (Prot 162.6, Thm 163.7). Its composition step for the OT simulators needs [Gol04]
  §7.3 (inventory). Also whether `HBCSecure` should require efficient honest parties.
- The PAC layer (#194) must reach the base before 06D: it lands on `main` (Q-4), and `main` is merged in again.
- The duplication-ledger items DL-6 and DL-7 are resolved before the integration replay.

## Integration dry run (2026-11-05)

On a scratch worktree (never pushed), S2b at `afe5982f` merged with the four prong heads (A
`2d7b5441`, B `d8ef9b40`, C `61c06756`, D `6ea900ae`):
- no conflicts;
- `Asymptotic/MultiMessage.lean` comes out identical to S2b's (prong C's mirrored `Dec` guard
  merges away);
- no fully qualified name is declared twice in the ch. 5–8 files.

The real integration waits for #195 (S2b) and Q-5 (Yao).

