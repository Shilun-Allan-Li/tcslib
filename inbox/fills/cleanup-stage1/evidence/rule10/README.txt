cleanup-stage1 · Rule-10 evidence (driver ../tools/rule10_s1.sh)

base/  : the 17 changed owners at the check base 2081fe57 (tree 01cc6259), base snapshot oleans
head/  : the 17 owners and the 2 new modules at the check head caad0151 (tree 985dd312), swept oleans
Each: order/ (owners, queues), collect-runs/ (collector raw log: CLOSURE/ROOT/CAT rows),
seals/{A,B}/ and seals-coe/{A,B}/ (per owner: the instrumented probe source <label>.lean.txt and its
record <label>.json with requests, term rows and the source-to-probe line map; manifest.json),
controls-{strict,coe}/ (head only: probe sources and controls-plan.json), seal-runs/ (every raw log
mods/*.log and results.jsonl), seals-*.tsv (sealsum), ctlcheck-*.{json,log} (head), statements/
(touched.json spans used to attribute errors), scan/ (explicit-unfold scan), probe-sources/,
driver.out, mkseals-*.log, mkctl-*.log.
The driver's probe directories (S1R10B/, S1R10H/ in the clone) were byte-identical copies of the
recorded *.lean.txt probe sources and are not delivered twice.
base/scan-invalid-headsources/: a first base scan that read the head sources (invalid; see its README).
compare.md: base vs head per owner and variant; seal-table.md: the summary table of REPORT.md §8;
head/coe-attribution.txt: every strict-only error in a new declaration with its coercion attribution;
scan-compare.txt: base vs head explicit-unfold scan.
