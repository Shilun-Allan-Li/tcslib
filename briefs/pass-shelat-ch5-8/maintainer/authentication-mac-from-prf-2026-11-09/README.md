# PRF-MAC construction relocation

The campaign base `87e7671d125de6275d435f786feb699ec9b62a8d` includes Seyoon's merge of #277. Its Lean and checker
inputs match the verified MAC interface head `f2bc431a3834fcc864ec2ed9fc544a0574ff3102`.

[PR #278](https://github.com/Shilun-Allan-Li/tcslib/pull/278) at `c17739c2a4969233167501a2b97928b8d1f7cef0` moves the PRF-based MAC, its correctness proof,
and its security statement to `Authentication.MAC.FromPRF`. The declarations
and proof text move verbatim. The standalone module uses the MAC and PRF
contracts and reuses `runAt_coinKey` from the PRG-based encryption module.
`Authentication.PRFMAC` forwards the construction and retains its previous
import closure. The authentication facade keeps that import for its GGM,
PRG stretch and other transitive exports.

- All four affected modules and campaign Checks pass. The replay verified
  1,108 unchanged local objects and 3,810 external objects.
- The census matches all 17 declarations, including the correctness proof's
  elaborated references and the single admission dependency in `prfMAC_secure`.
  The legacy and standalone import probes agree.
- Both whole-file seals pass with the same unused `eq_self_iff_true` warning
  and the same admission warning. The standalone module needs
  1376 seal requests from the baseline's
  1902. The control blocks direct reduction
  of `prfMAC` and accepts its published message-length equation.
- The explicit and generated read scans and both style lints pass.

The cleanup ledger was compared against the relocated providers.
[Ledger comparison](READS.json)

`authentication-mac-from-prf-checks.zip` has SHA-256 `7d2002425feb43ec38063dabc673f783c4d1bfa1ab7b5c401bd2fcabbca61c2e`.
[Verification hashes](VERIFICATION.json)

**Clear to merge — the affected modules, both import paths and seals pass.**

Seyoon merged #278 at `96987c36b5fd72347a005edebce59367673603c3`. The Lean sources and checker inputs match the verified head.
