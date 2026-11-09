# Public-key scheme interfaces

Seyoon merged the [facade pilot #256](https://github.com/Shilun-Allan-Li/tcslib/pull/256)
at `f7b436779ac047f606a7fe85d23e5ab96f553925`. [PR #257](https://github.com/Shilun-Allan-Li/tcslib/pull/257) implements the second slice of the
[approved pilot](../cleanup-incremental-2026-11-09/final-r1/PKE-PILOT.md)
at `c8b779f58307e7e9ec0041f4dfdf24cf42b78f9e`.

`Encryption/PublicKey/Scheme.lean` owns `PublicKeyScheme` and
`BitPublicKeyScheme`. It imports `Asymptotic.Adversary` and carries the
original declarations, docstrings and correctness fields verbatim. The
facade imports it and the legacy module re-exports it. The remaining
commands in `Asymptotic/PublicKey.lean` match the base.

- The pinned one-module checks compile all 10 affected modules,
  including the library root and campaign Checks. The replay validates
  1,067 retained objects. Checks output matches the facade check.
- Both import probes pass. The census compares 373 declarations and
  rehomes 44 identities. Eight compiler-generated binder labels
  acquire the new module scope. All other compared type and definition
  data, reducibility, instance and matcher flags, and axiom dependencies
  match. The six existing `sorryAx` dependencies remain in the census.
- Five whole-file seals apply 7,569 requests.
  Two focused probes seal all six newly foreign generated definitions
  in the legacy owner and campaign Checks. Both pass. The explicit
  tactic scan and generated-equation collector find zero scoped reads.
  The thirteen sensitivity controls transfer from the identical checked
  `Authentication.DLHash` import closure. The generated-equation
  collector reruns its positive and published-reader controls.
- The nine inherited diagnostics match by source step, declaration
  identity, column and diagnostic text. The ledger IDs SEAL-0266 through
  SEAL-0274 retain their owner and shift 46 lines earlier.
  `READS.json` records both source ranges and the original evidence.
- The new module and facade pass both style checks. The legacy file's
  size finding falls from 1,070 to 1,024 lines, within its existing exception.

`VERIFICATION.json` binds the review to the checked source, receipts,
and archive. `scheme-checks.zip` contains the probes, logs and
relocation ledger. Its SHA-256 is `ad406139633014025c141b83475619e841db5e022572338724634b23cddcd6a2`.

**Clear to merge — the scheme interface relocation and compatibility imports pass.**
