# ReductionAdvantage Rule 10 reader repair

seq-zk-b repaired only the proof body of distAdv_phaseReduction. The public statement,
docstrings, imports, attributes, hypotheses and conclusion are unchanged byte for byte.
Old source SHA256: 1aa5423ff30b3a625ff3180cbc1665eb508fd9ec75f487f9bcf26ee8ba775035.
Final source SHA256: 88db28a4cee3d94851c7f9dee5d249ba808f49da292caa66e9e4a349098d4bd3.

The lead's canonical-coercion seal exposed two hidden-conversion dependencies in htake and
hdrop. The old simpa mixed equivalence application and coinLen rewrites; with foreign
coinsEquiv/blocks sealed, the goal retained the composed local equivalence. The repair
publishes a local he equation, destructs its typed product explicitly, and reads the
Equiv.trans/prodCongr/Prod.map applications before doing any scalar coin-length rewrite.
A separate hcut uses only PolyExpr.eval_mul/NUPPT.coinLen_eq. Each tape proof then rewrites
he and hcut and applies the existing exact take/drop_ofFn_coinsEquiv reader. No foreign
body is unfolded, no transport theorem is copied and no new definition/host is introduced.

Worker native01 retained one local product-shape error and two unused-simp warnings; its
exact source is retained. Explicitly destructing the pair resolves that issue. Worker
native02 passed with zero diagnostics, 2.28s, max RSS 2221834240 bytes. All checks used the
shared wrapper/tag/private olean tree. The worker ran no seals; lead owns revision6 matrix
rechecks and retains the canonical raw failures. A SHA-linked extract/reference to the
lead's failed raw log accompanies this evidence. Five earlier frozen manifests verify
unchanged; prior source snapshots and receipts remain intact.
