# Common-exponent subexponential security implies negligible security

Status: two exact-header replacement drafts, not elaborated. No live files changed.
No Lean, lake, build, or Git commands were run for this task. Parent supplied source HEAD
`70b85f9ba83f27393d98fa5bf88505aea3d22a8d`; the snippets were checked against the live
working files, without independently resolving Git metadata.

## Deliverables

- `SubexpSimulationNegligible.lean.inc`: existing
  `SubexpSimSecureWith.simSecureWith` in `Simulation/Security.lean:87`.
- `SubexpSemiAdaptiveNegligible.lean.inc`: existing
  `SubexpSASimSecureWith.saSimSecureWith` in `SemiAdaptive/Security.lean:90`.

Both are term-only proofs with no helpers, new imports, new declarations, statement
changes, tactic blocks, admitted terms, or foreign definition unfolding. Maximum line
widths are 65 and 71 columns. A Python check asserted each theorem header exactly matches
its live theorem through `:=`, replacing only the existing `sorry` body.

## Actual search/read record

All repository-relative commands below ran in
`/Users/seyoonr/.codex/worktrees/tcslib-io-phfe/tcslib-exchange`.

1. Initially tried `rg` at obsolete `TCS/AdvancedEncryption/...` and
   `TCS/Foundations/...` paths; those paths do not exist. No contents were obtained.
2. Located the actual files with:

   ```sh
   rg --files | rg 'FunctionalEncryption/(Simulation|SemiAdaptive)/Security\.lean$|Foundations/Subexponential\.lean$|AGENTS\.md$'
   ```

3. Read both local proposition readers and existing admission headers with:

   ```sh
   rg -n -A 14 -B 6 'SubexpSimSecureWith\.simSecureWith|subexpSimSecureWith_iff|simSecureWith_iff' TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Simulation/Security.lean
   rg -n -A 14 -B 6 'SubexpSASimSecureWith\.saSimSecureWith|subexpSASimSecureWith_iff|saSimSecureWith_iff' TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/SemiAdaptive/Security.lean
   rg -n -A 9 -B 3 'theorem.*negligible|lemma.*negligible' TCSlib/Cryptography/Foundations/Subexponential.lean
   ```

4. Read headers, imports, and namespaces with `sed -n '1,80p'` on Simulation/Security,
   `sed -n '1,60p'` on SemiAdaptive/Security, and `sed -n '1,80p'` on
   Foundations/Subexponential.
5. Searched existing downstream short-form applications before considering helpers:

   ```sh
   rg -n 'Exists.elim .*subexp|SubexpSmall\.negligible .*\.1|\.negligible hc\.1|\.negligible hc' TCSlib/Cryptography/AdvancedEncryption TCSlib/Cryptography/Pairing
   ```

   No matching downstream examples were found. The existing shared theorem is sufficient;
   no helper was added.

## Dependencies and argument order

- `Simulation/Security.lean:70`: `subexpSimSecureWith_iff` exposes
  `exists c, 0 < c and forall A q, SubexpSmall c (...)`.
- `Simulation/Security.lean:52`: `simSecureWith_iff` packages
  `forall A q, Negligible (...)`.
- `SemiAdaptive/Security.lean:71`: `subexpSASimSecureWith_iff` exposes the analogous
  common-exponent condition for the exact existing `FE.toSAAdv` machine wrapper.
- `SemiAdaptive/Security.lean:51`: `saSimSecureWith_iff` packages the corresponding
  negligible-advantage condition, preserving the machine and total-call budget domain.
- `Foundations/Subexponential.lean:218`:
  `SubexpSmall.negligible (hSmall : SubexpSmall c mu) (hc : 0 < c) : Negligible mu`.
  Its actual namespace is `TCSlib.Cryptography`; Foundations is the file location.
- Core `Exists.elim` and conjunction projections only.

Each proof eliminates the common exponent, packages the local negligible-security reader,
then applies `SubexpSmall.negligible (hc.2 A q) hc.1`. The common exponent is kept before
all adversaries and budgets, and no quantitative weakening or new security claim occurs.
The existing imports already provide every dependency.

## Verification limits

Only textual header, width, and absence-of-admission/tactic checks were performed here.
Native elaboration and declaration/admission inventory refresh remain with the parent.
No false or unprovable statement was found in these two implications.
