# Source review for PR #237

PR #236 merged into `cryptography/lwe-sis-constructions` at `d748845a18b575b65a61950598eb0b805d2a97c6`.
GitHub confirms that commit as the current central head. Its tree matches the
published #236 head `80a24e0c650206c8862f7dd5253811449b2a6701`. The merge preview with #237 at
`ff8345b1d2ac2f605d81cdf6c23216aadb918abb` succeeds and produces tree `7d148fc147d7859f4e0e790cbfac9af4e207acb1`.
The #237 Lean tree matches the audited proof freeze `690217cc1aaefe411158808a8b0797fd887a8abc`.

This review covers the 26 source-related declarations in the 62-declaration
construction core. It records source formulas, extracted subclaims and adaptations.
The remaining 36 declarations cover encoding, parameter bookkeeping and readers.
Names below are under `TCSlib.Cryptography`. Page numbers count from the start of
the frozen PDFs.

| Declarations | Source | Scope of the correspondence |
|---|---|---|
| `Hashing.SIS.hash`, `Hashing.SIS.collisionDifference`, `Hashing.SIS.collisionDifference_ne_zero`, `Hashing.SIS.cardinal_compression`, `Hashing.SIS.exists_collision` | Pei16 Equation (4.1.1) and the two binary-domain observations on PDF pp. 20–21 | The binary matrix map and counting argument supply the formula and pigeonhole subclaims. The difference and its nonzeroness are extracted from the source collision argument. |
| `Hashing.SIS.collisionDifference_sqNorm_le`, `Hashing.SIS.collisionDifference_isSolution`, `Hashing.SIS.exists_solution` | Pei16 binary collision and existence argument, PDF p. 21 | The squared-norm budget is explicit. The Lean proof bounds all binary differences by the full column count and uses that bound for each fixed matrix. |
| `Hashing.SIS.collisionProbability`, `Hashing.SIS.collisionProbability_le_successProbability` | Pei16 collision-to-SIS observation, PDF p. 21 | Lean compares finite experiments on the same matrix and finder coins. The quantitative event inclusion uses the column bound. |
| `Hashing.SIS.dyadic_cardinal_compression`, `Hashing.SIS.dyadic_exists_solution` | Pei16 binary-domain counting argument, PDF p. 21 | The dyadic profile is a local parameter choice. Its explicit dimensions give compression and a sufficiently large squared budget. |
| `Hashing.SIS.dyadic_sqNormBound_lt_modulus_sq`, `Hashing.SIS.dyadic_not_isSolution_of_modulus_dvd` | Pei16 observation after Equation (4.1.1), PDF p. 20 | The source excludes trivial modulus multiples with a radius bound. The Lean proof checks the squared inequality in the local profile and excludes every nonzero vector with all coordinates divisible by the modulus. |
| `LWE.BitEncoding.codepoint`, `LWE.BitEncoding.decode`, `LWE.BitEncoding.decode_codepoint_add` | Wu24 Definition 20.5 and correctness, PDF p. 83 | The zero and half-modulus codepoints come from the source formula. The formal decoder uses circular distance with false on ties and a strict separation bound valid for the chosen codepoints. |
| `Encryption.Symmetric.Regev.shift`, `Encryption.Symmetric.Regev.encrypt`, `Encryption.Symmetric.Regev.encryptDist`, `Encryption.Symmetric.Regev.encryptDist_eq_shift_sample` | Wu24 Definition 20.5, PDF p. 83, and Pei16 Definition 4.2.3, PDF p. 24 | The one-bit formula is batched with a common secret and actual finite error seeds. The same-seed sampler identity follows from the encryption formula and batch distribution. |
| `Encryption.Symmetric.Regev.decrypt`, `Encryption.Symmetric.Regev.decrypt_encrypt`, `Encryption.Symmetric.Regev.decrypt_encrypt_noise` | Wu24 Definition 20.5 and correctness, PDF p. 83 | Subtract the matrix-secret product and apply the formal bit decoder row by row. The proof assumes the stated integer support and separation bounds and covers every seed. |
| `Encryption.Symmetric.Regev.acceptProb_uniform_shift`, `Encryption.Symmetric.Regev.distAdv_encrypt_le` | Wu24 Lecture 21 security, PDF p. 85, and Pei16 Definition 4.2.3, PDF p. 24 | Uniform translation supplies the common ideal experiment. The batched same-coin comparisons and two-advantage triangle bound are local quantitative statements. |

## Proposed reference update

The [Pei16 excerpt](proposal-pr237/peikert2016-lattice-survey.md) retains both approved
#236 blocks. It adds the modulus-multiple observation at
`pdf-1a9802b66031-p020-b002` and the binary-domain argument at
`pdf-1a9802b66031-p021-b001`. The existing LWE batch definition on p. 24
supports the encryption sampler. Scoped Markdown SHA-256
`ebf435f1ce09b7b65947ea5a1d271a01168aecbe73c4b4d82b52502c3570f76b`.

The [Wu24 excerpt](proposal-pr237/wu2024-topics-cryptography.md) covers Definition 20.5
and its correctness discussion at `pdf-c0f87bf2e871-p083-b001`, and the
Lecture 21 ideal hybrid at `pdf-c0f87bf2e871-p085-b001`. Scoped Markdown
SHA-256 `4aab98cdaba30933eb4b9ae2e47a04ba2d43d08cab722cf9990168e36b416aed`. Original PDF SHA-256
`c0f87bf2e871180d62b2b27d38b916bce1a7b2228dbb68de72341597341d6d87` and archived raw extraction SHA-256
`345aad6425678069c5f1afbc328457c4c21c61e2019507a241e5e71376cf7814`. The PDF remains in the pinned exchange packet.

The correctness passage uses scaled rounding and a real-quarter bound.
The Lean theorem assumes strict separation for its nearest-codepoint rule.
The ideal hybrid passage uses a single sample. The common-secret batch and
quantitative bound have the separate support shown in the table. These
attributions do not approve automatic blueprint proof citations.

## Shared registry proposal

The target registry includes the approved Pei16 entry. This diff adds Wu24.
The before and proposed after SHA-256 values are
`747816a0571be024950d5cbdf48761515d50ffe48dc5232a95f39bc2e8eb4104` and
`a22d148b9b81a4fa03729286dee0357f6dda774391c169cb6e4da7df8ffb2fe5`.

```diff
--- a/blueprint/src/references/sources.json
+++ b/blueprint/src/references/sources.json
@@ -94,6 +94,12 @@
       "documents": [
         "vershynin-hdp-book"
       ]
+    },
+    "Wu24": {
+      "title": "D. Wu, CS395T Topics in Cryptography, Spring 2024 lecture notes, compilation last updated 30 April 2024.",
+      "documents": [
+        "wu2024-topics-cryptography"
+      ]
     }
   }
 }
```

The native fetch of the central commit failed DNS. A client fetch from
`tcslib-lwe-sis-phase1` supplies the exact commit for the integration. After
source approval, merge that target into #237's own worktree, attach the approved
reference records and run the 68-module landing checks. The present merge
preview uses the identical published #236 tree.

**Not yet clear to merge. The source attributions and registry change are
ready for approval, followed by integration and landing checks.**
