# Uniformity audit: honest parties uniform, adversaries non-uniform (Codex, 2026-11-16)

**Requested by Seyoon (2026-11-16).** The intended convention is that honest parties, constructions and simulators
are **uniform PPT**, and that adversaries and distinguishers are **non-uniform PPT**. This audit checks every
cryptographic definition in TCSlib against that convention. It is a read-only audit, with no Lean runs.

## Background
- `Complexity.NUPPT` (`TCSlib/Complexity/Randomized/PPT.lean`) is a polynomial-time machine with per-length advice.
  `NUPPT.Uniform` means the advice is empty (`∀ n, A.advice n = []`), which is a PPT [PS10, Definition 23.4].
  `Complexity.PPT` is the uniform subtype.
- Deterministic algorithms are `PolyTimeComputable` functions. These are uniform by construction.
- Interactive strategies are uniform when `Strategy.Efficient` holds (`ZeroKnowledge/Interaction.lean:177`).
- **The maintainer's first scan.** Every scheme structure with `NUPPT` fields also has `_uniform` fields:
  `PublicKeyScheme`, `BitPublicKeyScheme`, `FixedLengthPKScheme`, `GroupPKScheme`, `PrivateKeyScheme`, `MAC`,
  `SignatureScheme`, `Collection`, `TrapdoorCollection`, `CRH` and `ExpGroupGen`. Further:
  - `MsgSampler.samp` (non-malleability) is non-uniform. This is intended, because the adversary chooses it.
  - `ZK` quantifies over uniform cheating verifiers (`V'.Efficient`), with an auxiliary input `z` of length at most
    `Lz`, and its simulators are uniform.
  - **`HBCSecure` (`SecureComputation/Defs.lean:~177`) has `∃ SA SB : NUPPT` with no uniformity requirement.** This
    is weaker than [Gol04, §7.2] and [PS10, §6.2].

  **Seyoon's ruling (2026-11-16):** audit now; fix `HBCSecure` in a statement PR after the open
  secure-computation PRs and sc-yao land.

## Scope
Cover all of `TCSlib/Cryptography/` and `TCSlib/Complexity/Randomized/` at the pinned records tip. For **every**
definition that quantifies over machines or strategies, or that bundles them, classify each machine-valued or
strategy-valued component. That includes security games, experiments, assumptions such as OWF, PRG, PRF, DDH, LWE
and SIS, protocols, simulators, extractors, samplers and reductions stated as definitions. Each component's role is
one of: **honest/construction**, **adversary**, **distinguisher**, **simulator**, **sampler/environment** or
**advice/auxiliary input**. For each component, record:
1. **Role and required uniformity:** what the convention requires, citing the source definition ([PS10], [Gol01],
   [Gol04], [AB09] or the cited paper) where the source specifies it.
2. **Actual uniformity:** what the Lean definition requires (`Uniform`, `Efficient`, `PolyTimeComputable`, or a bare
   `NUPPT`).
3. **Verdict:**
   - **OK.**
   - **WEAKER:** the definition is easier to satisfy than the source. For example, a non-uniform honest party or
     simulator under `∃`.
   - **STRONGER:** the definition is harder to satisfy than the source. For example, a uniform adversary under `∀`
     with no auxiliary input.
   - **EQUIVALENT-BY-AUX:** a uniform adversary that receives an unrestricted auxiliary input, which is equivalent
     to non-uniformity. State the length bound and whether it is adequate.
4. **For WEAKER or STRONGER:** a proposed repair, together with every downstream declaration whose statement or
   proof would be affected (consumers of the definition at the tip). Also check the open PRs #318, #319, #323, #324,
   #326 and #327 at their current heads.

Specifically confirm or refute the `HBCSecure` finding. For each existing proof that constructs `SA` or `SB`, at the
tip and in the open PRs, say whether the constructed simulator is already uniform or uses advice. sc-compose's step 3
uses worst-instance advice for a reduction; check whether that advice ever reaches a simulator. Also check that the
ZK auxiliary-input bound `Lz` is adequate, and whether any game gives its adversary less than the source intends,
for example no auxiliary input or no `1^n`.

## Output
Return `uniformity-audit-findings.md`: a table with one row per classified component (file:line, definition,
component, role, required, actual, verdict), then findings graded as in the gates (blocker, major, minor or note),
with proposed repairs and their downstream impact. Return a ZIP if you include evidence such as scripts or
extracted lists.
