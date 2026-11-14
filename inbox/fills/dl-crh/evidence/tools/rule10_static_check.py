#!/usr/bin/env python3
"""Check evidence-tool assembly only; do not invoke Lean or Lake.

Retain the assembled bytes and input row so this static smoke check has no
omitted generated source. It is not a native seal/control result.
"""
import ast
import importlib.util
import json
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[2]
sys.dont_write_bytecode=True


def load(path,name):
    spec=importlib.util.spec_from_file_location(name,path)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module


for path in (ROOT/"evidence/tools").glob("rule10_*.py"):
    ast.parse(path.read_text())
P=load(Path(__file__).with_name("rule10_prepare.py"),"dl_crh_static_prepare")
S=load(Path(__file__).with_name("rule10_scan.py"),"dl_crh_static_scan")
bs,adapter=P.builders()
components=lambda name:[["str",part] for part in name.split(".")]
row=dict(spelling="Complexity.NUPPT.inArg",home="TCSlib.Complexity.Randomized.Closure",
         name_components=components("Complexity.NUPPT.inArg"),
         home_components=components("TCSlib.Complexity.Randomized.Closure"),
         instance=False,matcher=False,abbrev=False,collector_reducibility="semireducible")
raw=(ROOT/"TCSlib/Cryptography/Hashing/FromDiscreteLog/Coins.lean").read_bytes()
probe,insertions,line_map=bs.instrument(raw,bs.header(raw),"StaticPreparationOnly",[row])
recovered=probe
for record in reversed(insertions):
    a,n=record["probe_byte_offset"],record["byte_count"]
    recovered=recovered[:a]+recovered[a+n:]
assert recovered==raw
assert b"allowUnsafeReducibility" not in probe
assert b"G06-MASK" in probe and b"G06-COMPONENT" in probe
items,decls=S.declaration_context(raw.decode(),S.lexer()["inventory"](raw.decode()))
assert items and decls
out=ROOT/"evidence/probes/Rule10/static-assembly"
out.mkdir(parents=True,exist_ok=True)
(out/"owner-source.lean.txt").write_bytes(raw)
(out/"instrumented-source.lean.txt").write_bytes(probe)
P.save(out/"manifest.json",dict(status="STATIC_ASSEMBLY_ONLY_NO_LEAN_RUN",requested_rows=[row],
       owner_sha256=P.sha(raw),probe_sha256=P.sha(probe),original_bytes_recovered=True,
       no_unsafe_reducibility_option=True,insertions=insertions,source_to_probe_lines=line_map,
       explicit_inventory=items,declarations=decls))
print("PASS Python syntax, hardened instrumenter assembly, original-byte recovery and pure source inventory")
print("NOT RUN: Lean, Lake, native seals, native controls, proof validation")
