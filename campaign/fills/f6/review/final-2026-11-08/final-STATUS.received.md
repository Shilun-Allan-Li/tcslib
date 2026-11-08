# fill-f6-final — receipt and status

* Zip: `fill-f6-final.zip` — SHA-256 `0f48e507b3a865b330c9a712adeab71e697bad9ba426e29a3172a24eeae70d10`, 1747430 bytes.
* Fill: F6 `Complexity.space_universal` (Claude, ruler-hosted suffix); owned file `TCSlib/Complexity/SpaceComplexity/Hierarchy.lean` only.
* Base `3023dc1408c3d216fc07a7cbba9ae30135b861ed`; branch `fill/f6-space-universal` head `6e98df4f7f86889b2c9eb3e9a05541cc772a56d4` (git bundle inside the zip).
* Status: **COMPLETE — target proved**, exact frozen statement, axioms `propext, Classical.choice, Quot.sound`; no new admission (census 22 → 21, the 21 inherited admissions unchanged).
* Checks: final 229-module sweep at the head 229/229 exit 0, 0 errors, 21 inherited `sorry` warnings; downstream pair PASS; freeze PASS (public/import/order/definitions frozen); seal of the 19 new declarations PASS with 72/72 paired controls (unsealed close, sealed fail); argument scan inspected; lints: no new finding; screens: base byte-identical to the issued baseline, head 1 new idiom-level pair (50%, for disposition); boundary probe PASS.
* Disclosures/requests: identity-embedding shared lemma request (E1), file size (E2), screen pair (E3), two derived `Fintype` instances not sealable by `[local irreducible]`, process deviations D1–D6. Details in `REPORT.md`.
