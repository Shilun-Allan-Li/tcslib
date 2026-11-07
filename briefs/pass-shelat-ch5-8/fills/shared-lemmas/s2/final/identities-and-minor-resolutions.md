# S2 delivery and landing identities

The immutable REPORT retains abbreviated worker identities. Full source identities below are recovered from format-patch metadata; the worker source Git objects were not independently authenticated. Exchange identities are independently resolved local Git objects.

| Patch | Worker source identity (metadata) |
|---|---|
| 0001-S2-milestone-2-prove-polyTimeComputable_rejectBlocks.patch | `144c99ea798e9d22d591e993dd749ac417075923` |
| 0002-S2-milestone-3-dl-a-and-dl-c-consume-H15-retire-dla_.patch | `5a6f802114dc5a44f9e515b73c06d5e3e0d80dca` |
| 0003-S2-milestone-4-RSA-unit-sampler-and-Rabin-generators.patch | `538b932d7f66c494ff3e9116a9541a4d617c02cc` |
| 0004-S2-final-proof-sketch-for-rsa_unitAcc_poly-style-lin.patch | `125a29633892daebde9fbad46a131d5b66febbb7` |

The landing branch is `cryptography/pass-shelat-reject-blocks-s2` at `d8c4cfed793f04062e7e79b78344e5b593ff3ddc`, in the reused completed Gate08 worktree. Its five commits (four delivered patches preserving authorship, then two comment-only minor fixes):

- `0a4f6b0583a60018d309f761e0428132ecc0b09a` S2 milestone 2: prove polyTimeComputable_rejectBlocksL (H15) via the repetition host
- `75edf4b11688a00f65c422dfe870d654f6afb823` S2 milestone 3: dl-a and dl-c consume H15; retire dla_ss*/dlc_ss* loops; refresh three sketches
- `09c6c531f05920044017f53045e5ab9cb1bffb4d` S2 milestone 4: RSA unit sampler and Rabin generators consume H15; retire rsa_us*/rabin_rb* loops; refresh three sketches
- `a2b706c3b69cf1e854b109b2d6d9e3ca4bb41406` S2 final: proof sketch for rsa_unitAcc_poly (style-lint finding)
- `d8c4cfed793f04062e7e79b78344e5b593ff3ddc` Correct H15 status and sampler-width prose after S2 review

The two comment-only corrections resolve the stale H15 module status and the sampler width typo. All code and public headers are unchanged by those corrections. The REPORT stays verbatim.
