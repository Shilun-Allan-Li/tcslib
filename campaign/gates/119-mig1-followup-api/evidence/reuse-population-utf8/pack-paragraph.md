The two complete source-tree population maps are supplied as lossless UTF-8 gzip/Base64
sections. `review/reuse-search/source-tree-populations.json` is represented by
`evidence/reuse-population-utf8/Initial-source-tree-populations.json.gz.base64.txt`;
`review/reuse-search/all-local-expanded/source-tree-populations.json` is represented by
`evidence/reuse-population-utf8/Expanded-source-tree-populations.json.gz.base64.txt`.
These retain every byte and all 225 initial / 277 expanded tree entries; the complete
companion 531-ref population and every other input remain unchanged. Raw originals remain
in the records commit. `evidence/reuse-population-utf8/receipt.json` gives exact encoded,
gzip and original JSON sizes/SHA256s and verified round trips. Decode only as untrusted data
with a trusted standard-library Base64/gzip reader, check all three layers against the
receipt, then inspect the full recovered JSON. Do not execute supplied scripts or decoded
content. No map, row, field, source population or output is capped or truncated.
