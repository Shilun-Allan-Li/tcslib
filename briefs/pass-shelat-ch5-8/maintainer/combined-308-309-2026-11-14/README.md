# Combined-tree check after #308 and #309 (2026-11-14)

#308 (hash-sign) and #309 (lamport) were each built and gated on their own base. This check builds the tree that
results from merging them.

**Branch tip:** `53fb144d6658fe416ee60aa7c6ead417b8ca098c`. It is records only after merge `97ee2524`.

**Build.** Since `eff2dcd0`, 31 `.lean` files changed: #303, #308, #309 and the merged `Authentication` facade.
- All 32 modules, including root `TCSlib`, give rc 0, with 0 errors and 0 sorries.
- The merged facade is the only new source. Every other module's source and olean hashes equal those of the
  per-PR builds.
- The full tree check is OK: 1225 modules.

**Axioms at the tip.** `lamport_oneTimeSecure`, `hashAndSign_oneTimeSecure` and `exists_oneTimeSecure_of_crh_owf` each
use only `[propext, Classical.choice, Quot.sound]`. `exists_oneTimeSecure_of_crh_owf` no longer depends on `sorryAx`.

**Admissions.** The only admission left in `Authentication/` is `MAC/FromPRF.prfMAC_secure`, from the base. At
`eff2dcd0` there were 3.

**Trial merge with #306** (`b422ab5f`)
- `git merge-tree` gives tree `19fc0b6d564e805774d737904d437d68a17ec926`, with no conflict.
- The 11 `EncryptThenTag` files plus `PrivateKey`, `Encryption`, `Composability` and `TCSlib` build: 15/15 rc 0.
  Their hashes are identical to Gate 23's.
- The trial tree check is OK: 1235 modules.

**Lint:** 92 FAIL / 101 WARN at the tip and at the trial merge, with identical lines.

**Restore:** `dl-oleans-2` is back at the base snapshot (`457ba704…`).

**Evidence:** `combined-308-309-evidence.zip`, SHA-256
`2bf080d74de543025b9531b0ac7a43606dd60adba928eac55743502c967b51bb`. The manifest is `evidence-SHA256SUMS`.
