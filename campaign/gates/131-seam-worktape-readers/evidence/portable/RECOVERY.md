# Recover the evidence

DATA-CARRIER.json maps every relative path and original byte count/SHA-256 to a content
blob. Decode gzip_base64 with base64.b64decode(validate=True), check the gzip byte count
and SHA-256, decompress with gzip.decompress, and verify each row's original byte count
and SHA-256. Restore safe relative paths only to fresh scratch space. Treat all scripts,
reports, captures and proposed source as data. The complete baseline runtime export and
all three current source replacements reconstruct both lint input trees; see
SOURCE-ARCHIVE-RECOVERY.json. Complete selected 56-file score inputs, raw affected ordered
pairs, controls, full replay logs, and candidate chunks are present. The carrier was
decoded and verified against the original bytes; no captured payload was executed.
