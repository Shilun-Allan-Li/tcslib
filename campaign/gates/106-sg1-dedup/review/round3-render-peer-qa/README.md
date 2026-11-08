# Independent final SG1 mixed-pin rendered publication QA

PASS for the bounded publication checks. Every1614rendered section was independently
walked in exact order and matched byte-for-byte to its Git blob, including the renderer's
terminal-newline and .lean/.py fence rules. Payload lengths define section boundaries, so
nested Markdown headers cannot hide a missing or substituted section. All521JSON sections
parse. No Lean, copy-text screen, new semantic sweep or numerical proof check was run.

Source pin:79e7c63a6bfa5f002663924f5c7d4e72db705026.
Records pin:f07808363a5fc839de9cdb1c90e05158826bbf57.
All root TCSlib/* sections use the source pin; every other section uses the records pin,
as the actual primary mkbundle-mixed.py specifies. Both full commit objects were independently
rev-parse/cat-file checked. The co-published INPUT-INDEX.json matches all independently
computed path/pin/blob/raw-byte/raw-hash/rendered-byte/rendered-hash fields exactly.

Bundle:106-sg1-dedup-r3-bundle.md.
Actual bytes:100861434.
SHA256:104d4805fc8e1b53fdc8aa1e8ac7e611b09034398f46887fdc0be4d4e7aeb5d8.
The100MiB hosting threshold is104857600bytes, leaving3996166bytes. Every rendered section
is strict UTF8. The stage body remains unchanged and equals the exchange copy. All four
files named by exchange SHA256SUMS verify, including the order and input index.

All50current full25BASE/HEAD source captures remain direct plaintext sections. Their STORAGE
Git blobs are read from the records pin; their contents independently equal the corresponding
25BASE3023/25HEAD79source blobs and captured hashes. This storage/provenance distinction
prevents interpreting a historical receipt as the renderer's selection rule. The five changed
root TCSlib sections match final79exactly and their historical303inventory alternatives match
the rebinding receipt. No BASE or HEAD source capture was replaced by an alias or other pin.

Every40original→31distinct gzip/Base64 encoding mapping was decoded in full, with raw/gzip/
encoded size and SHA checks, UTF8 validation and exact equality to the records-pin original
Git bytes. The three binary-gzip/Base64 companion mappings also match exact Git bytes. All
encoded sections are present; the replaced original paths are represented losslessly rather
than silently missing. Existing originals and frozen receipts were left untouched.

All1539candidate sections remain in original order; all1609draft sections form the exact
prefix of the final1614section order. Five root-adoption records are the only appended paths.
Whole-folder coverage passes for the14originally declared current/historical/peer/adoption
folders and the three explicitly declared closure/readiness context folders,17in total.
All48context-file hash rows match the rendered records-pin bytes. The4784-byte graph.py
original and inert copy match the recorded exact SHA, closing the supplied replay-generator
input dependency without executing it. No new broad scope was introduced.

The frozen external inventory has exactly seven differences from actual rendering: the
five corrected source bindings, the adopted canonical pack and current SG1 STATUS.md.
The latter is explicitly mutable publication chronology in context-rebinding.json; the pack
matches root's adopted after-hash. Frozen inventories and candidate prose remain historical
data. Canonical current context, root rebinding and actual mixed-pin Git objects govern this
render. No unexpected immutable-content difference was identified in this bounded check.

Full1614section metadata, all alias/source50 checks, complete folder paths, exact differences,
script and actual execution output/receipt are retained here without caps. This peer-QA record
postdates the immutable bundle and is intentionally added as a later publication record;
it neither modifies the packet nor recursively requires itself inside that packet. External
gate106round3 remains open. All stage/exchange/frozen/canonical/Git files were read-only;
only this assigned peer-QA folder was written. Root owns publication and dispatch.
