# Pass–shelat cleanup and reorganization

Seyoon approved this order on November 8, 2026 PST and authorized the
incremental acceptance target for [PR #248](https://github.com/Shilun-Allan-Li/tcslib/pull/248)
once this plan is recorded on `cryptography/pass-shelat-ch2-4`. Seyoon reviews
and merges the Lean PRs. This ruling supersedes the requirement to close the
full inherited-read ledger before the #248 merge. The final cleanup still
closes that ledger on the reorganized source.

## 1. Land the checked cleanup increment

Reconcile the checked #248 head and its attributed worker commits with the
campaign base after the #232 merge. Take the delivered shared interfaces,
deduplication and proof repairs through the following acceptance checks.

- Verify the exact combined source. Compare the public declaration types,
  algorithms, attributes, admissions and actual axiom dependencies against
  the merged base and the approved cleanup exceptions. Preserve the #232
  statements and both verified probability-projection repairs.
- Compile the affected modules in dependency order and check `TCSlib` and
  the campaign `Checks` aggregate. Retain the exact source and object
  bindings and all check attempts.
- Apply the instance-aware Rule 10 seals with the approved exact notation
  exceptions. Cover the edited declarations, changed providers and
  consumers affected by a change of definition owner or operative import
  context. Check explicit unfolding and generated equation references as
  well as ordinary conversion. Use controls that test both the seal and
  the published-reader route.
- Compare with the merged base at the declaration and read level, including
  edits inside previously failing blocks. Repair a regression within scope
  or leave the affected change for the follow-up. A smaller set of failing
  declaration names alone cannot establish that all reads are inherited.
- Carry forward only witnessed inherited failures. Record the current and
  historical owner, actual declaration identity, source range, relevant
  provider, and evidence for each disposition. Preserve the original worker
  ledger and account for missing historical raw logs in the intake record.

Keep #248 draft until the regression check passes. The recorded owner and
worker scope still govern substantive provider proof changes and new machine
contracts. The three proposed `ClassNP/PolyTime` provider proof changes remain
separate scope decisions. [Checked intake and limits](fills/cleanup-part2/checkpoints/partial-r1/checked-repairs-r1/README.md)
· [Issued brief and original criteria](fills/cleanup-part2/issued-r1/brief.md)

The [incremental verification](maintainer/cleanup-incremental-2026-11-09/final-r1/README.md) records the exact #248 head and inherited-read dispositions.

## 2. Reorganize by primitive, starting with public-key encryption

The construction map can be designed against the current source. Start the
physical moves once the verified cleanup increment has landed. Use the
primitive as the reader's entry point and keep problem assumptions, shared
encodings and game machinery in reusable owner modules.

- Pilot `Encryption/PublicKey.lean` as the facade and construction map.
  Distinguish scheme interfaces, security games, the shared trapdoor route
  for RSA and Rabin, and the direct ElGamal route. Link each route's actual
  assumption set, algorithms, correctness and security results and open
  bridges. Link from the assumption side too.
- Give each coherent move a separate review. Preserve public names and
  types and supply compatibility imports for existing callers as needed.
  Check the changed import graph, exports and the definition boundaries
  introduced by the move. Map the ledger to its new declaration homes.
- Extend the pattern by dependency. Start with pseudorandomness and
  symmetric encryption, then authentication and hashing, then oblivious
  transfer, garbling and protocols. Agree on shared owners with the
  LWE/SIS campaign before moving common interfaces.

`Implications/PublicKey.lean` is the destination for short, proved
assumption-set-to-endpoint theorems. The selected endpoints are multi-message
IND-CPA and IND-CCA2 on a meaningful message space. CCA1 is an intermediate.
The RSA/Rabin width work, ElGamal's message and game transport, and the
oracle CPA proof and multi-message lifting are separate proof tasks.
[Implications design](implications/README.md)

## 3. Close the inherited seal ledger on the new layout

Regenerate the full inventory on the settled import graph. Resolve the
retained reads through the final owners' equation, field, case and machine
run contracts. Reconcile all historical observations and record what each
proof repair closes. Finish with the complete affected-module, root and
Checks replay, whole-file seals and controls, explicit and generated
reference review, and actual declaration and axiom census.

Gate 03 restaging follows its recorded prerequisites. The efficiency fill
uses the decoder interfaces after they land and the issue-time probes pass.
Any decision to dispatch it while cleanup dependencies remain open needs
the separate, scoped dependency ruling discussed with Seyoon.
