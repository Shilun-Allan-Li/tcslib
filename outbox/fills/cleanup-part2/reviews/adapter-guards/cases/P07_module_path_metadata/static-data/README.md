# PFR environment bootstrap supplement

This static supplement binds the exact source closure for PFR.Mathlib.Probability.UniformOn, PFR.Kullback and PFR.ForMathlib.Entropy.Basic. It does not execute a native/bootstrap/cache command or start a mathematical fill. The original 45 issue attachments remain byte-identical.

The exact closure is **31 PFR source modules**, in dependency order. No source import reaches LeanAPAP; its manifest-pinned package is recorded, but no blanket LeanAPAP build or alias is needed for these roots. All 31 sources match raw Git blobs at PFR e1095d58b7c6f10734988816f7764f2103b9bf29. The package/source/configuration fingerprints and import sites are recorded; no source files or trees were copied.

The source boundary contains **30 direct Mathlib roots**, with **14 extra roots** beyond the frozen 375, giving **389** in mathlib-full-union-roots.txt. No bare Mathlib root appears. The initial package-cache snapshot has 29/30 direct boundary objects present; the missing one is Mathlib.MeasureTheory.Measure.ProbabilityMeasure (already in the frozen original roots). Presence is not native freshness or ABI validation. No local source import or cycle is missing from this closure.

Use ordered-modules.json for module/source/blob/raw-hash mapping and graph.json for import edges. **bootstrap-order.txt**, rather than order.txt, contains the proposed unchanged-checker physical rel arguments `.lake/packages/PFR/PFR/<suffix>` in dependency order. The older order.txt is the logical PFR module-path list only.

## Revised static bootstrap design

Root's revised design uses no source alias. It invokes the unchanged checker with the physical package-relative rel path. A reviewed wrapper adds `--root=<clone>/.lake/packages/PFR` and exactly the four manifest-pinned PFR lakeOptions for those PFR invocations only:

- `-DautoImplicit=false`
- `-DrelaxedAutoImplicit=false`
- `-Dpp.unicode.fun=true`
- `-Dpp.proofs.withType=false`

All four are registered Boolean options in the pinned Lean sources. The unchanged checker does not read lakefile options itself. Other local-source checks must pass through the wrapper unchanged.

The checker writes `<tree>/.lake/packages/PFR/PFR/<suffix>.olean`; the planned same-tree object alias `<tree>/PFR -> .lake/packages/PFR/PFR` makes imports resolve precisely that object at `<tree>/PFR/<suffix>.olean`. physical-output-plan.json independently checks this relative mapping and the source realPath/module-root calculation for every one of the 31 modules. The alias has not been created by this agent. This is one source checkout and one olean tree, with no dependency/source copying, locator root or LEAN_PATH join.

The original source-alias-only idea is retained in source-alias-review.json as rejected/inapplicable. Pinned Lean/Shell.lean267–276 obtains the module name from moduleNameOfFileName unless setup supplies it; Lean/Util/Path.lean140–154 resolves source/root realPaths. Thus a source alias alone under the unchanged checker would have inferred a .lake/packages prefix. The revised explicit physical package root removes exactly that prefix. No unsafe reducibility or trust option is used.

wrapper-design-validation.json is a static design check, not a review of an unseen executable wrapper or a native result. Root must still verify the true imported PFR module/constant owner, fresh products, diagnostics and serial execution. An object merely being importable does not independently establish its owner identity.

MANIFEST.json preserves the first source-closure snapshot; DELIVERY-MANIFEST.json also binds the revised physical output and wrapper-design files. Neither includes its own hash. All raw/source/package fingerprints were checked read-only, and all frozen issue attachments were rehashed unchanged.

**Not yet clear to merge — environment bootstrap and native owner-identity verification remain with root.**
