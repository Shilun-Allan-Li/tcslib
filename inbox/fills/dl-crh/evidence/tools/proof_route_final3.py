#!/usr/bin/env python3
"""Retain the historical route and write its source-line-correct final3 variant.

Use python3 -I. The mathematical route is unchanged; the final repair makes
dependent width transports explicit under both required seal modes.
"""
from pathlib import Path
import hashlib

source = Path("evidence/proof-route.md")
output = Path("evidence/proof-route-final3.md")
before = source.read_bytes()
text = before.decode()
old = "5a24269932a72f672104b18280609879dd992c82"
new = "fa33b9b8fa3a9b801a7db8857d7a2739c61c1e16"
assert old in text and new not in text
text = text.replace(old, new)
for original, final in ((532, 533), (548, 549), (579, 581), (629, 631), (656, 658), (708, 710),
                        (287, 290), (298, 301), (303, 306), (308, 311), (314, 317), (325, 328)):
    text = text.replace(":" + str(original), ":" + str(final))
anchor = "The statement of `Authentication.dlHash_crh` is preserved.\n"
assert anchor in text
text = text.replace(anchor, anchor + "\nThe final repair makes dependent width transports explicit: CRH fields are read\n"
    "before polynomial widths are normalized, and the padded-word width equality is\n"
    "transported with `congrArg` before applying the public encoded-vector reader.\n"
    "It changes proof elaboration under the required seals without adding declarations\n"
    "or changing the mathematical reduction.\n", 1)
output.write_text(text)
assert source.read_bytes() == before
print("PASS historical route unchanged", hashlib.sha256(before).hexdigest())
print("PASS fresh final3 route", hashlib.sha256(output.read_bytes()).hexdigest(), output)
