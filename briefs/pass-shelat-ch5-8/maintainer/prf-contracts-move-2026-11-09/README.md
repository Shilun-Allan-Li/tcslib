# Asymptotic oracle and PRF contracts

Seyoon merged the permutation-to-PRG relocation #267 at `757f7fbaf80acd847feffb5d57f28322ce2d6beb`.
Its Lean sources and checker inputs match the verified head `fbed01a2bb841ab557396cebb2609cca3de8b06d`.

[PR #268](https://github.com/Shilun-Allan-Li/tcslib/pull/268) at `77e0232adeefdb0c7cf0abec14da6925bd8e1bcf` moves the oracle ensembles, next-query
adapter, indistinguishability, and PRF contract to
`Pseudorandom.Functions.Asymptotic.Defs`. The contract uses the finite
oracle model, the machine interface, and the negligible-advantage
definition. The generic `lazyDist` helper moves to `Functions.LazySampling`.
`Asymptotic.PRF` re-exports the contract and houses the GGM construction.

- All 30 affected modules are verified, including the library root and campaign
  Checks. The final replay checks 24 from source and transfers six from the
  earlier replay with identical source and dependency objects. It also verifies
  1,065 unaffected local objects and 3,810 external objects.
- The census pairs 184 declarations and maps 104 to new owners. The types,
  definition values and axiom sets match after normalizing private names and
  generated binder scopes. Lean checks the one private decoder lemma whose
  type uses a different generated matcher against its original type.
  The `lazyDist` generated equation resolves on demand with the original type.
  The existing `pairDecode_true_two` is published, and two new readers let the
  GGM proof use the oracle contract at the new boundary.
- Both oracle and GGM whole-file seals pass. The final sub-hybrid seal
  reproduces two baseline diagnostics from the repeated local irreducibility
  attributes. The earlier seal exposed two reductions of `lazyDist` in the
  sub-hybrid proofs. The published equation repairs both. The sealed control
  blocks direct reduction of `OracleEnsemble.Indist` and accepts its reader.
- The source and generated-equation scans find zero foreign-definition reads
  in the checked owners. Two old source-scan entries in `LazySampling` refer
  to the local `let g`. Their new line numbers and the inherited attribute
  diagnostics are recorded. [Ledger mapping](READS.json)
- Style checks add zero findings. The `OracleEnsemble.Indist` reader
  warning clears, and both pseudorandomness facades export the contract.

`prf-contracts-checks.zip` has SHA-256 `c34ebd50a9da72c2279d7d2b1f2f8e01f72ce82be992836b0b9c9a6f245e7f5d`.
[Verification hashes](VERIFICATION.json)

**Clear to merge — the compatibility imports, affected modules and seal comparison pass.**
