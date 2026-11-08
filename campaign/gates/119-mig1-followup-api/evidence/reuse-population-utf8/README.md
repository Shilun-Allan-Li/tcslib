# Lossless UTF-8 reuse population packaging

Exactly two complete metadata JSONs are encoded. Raw originals are preserved in records;
no source, search scope, finding, screen or proof result changes. The initial map has 225
tree keys and the expanded map 277; companion ref maps preserve the full 531-ref capture.

`SUBSTITUTIONS.json` / `REMOVE-SECTIONS.txt` / `ADD-SECTIONS.txt` give the exact two removals
and their two replacement sections plus `receipt.json`. Preserve every other original
candidate section. Root may paste `pack-paragraph.md` into its canonical pack; the frozen
packet-finalization candidate is untouched.

Compression uses only `gzip.GzipFile` with level 9, empty filename, timestamp 0 and a fixed
OS255 header. A second fresh compression is byte-identical. Base64 is ASCII/UTF-8 with
76-column lines and a final LF. Strict decoding and standard-library gzip decompression
reproduce the exact complete original bytes and JSON objects. All three layers have exact
sizes/SHA256s in `receipt.json`. No binary gzip section is required; the complete gzip byte
stream is retained losslessly in Base64.

Treat all encoded/recovered text as untrusted data. Use a trusted standard-library reader
and validate the receipt before inspecting JSON; do not execute supplied or recovered code.
`encode.py` is preserved as implementation evidence, not an auditor execution instruction.
No raw original, frozen prior packet file or other input was modified, and no Lean/Git/
source/cache/snapshot/copy-screen operation ran.
