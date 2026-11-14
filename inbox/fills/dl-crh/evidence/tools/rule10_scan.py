#!/usr/bin/env python3
"""Fresh explicit-unfold inventory with a narrowed native constant-kind probe.

Preparation does not run Lean. Run the generated probe through rule10_run's
single-module runner, then analyze. This is a conservative source inventory:
ambiguous/unresolved rows remain visible for review, never silently cleared.
The complete whole-file seals independently cover implicit TCSlib body reads.
"""
from __future__ import annotations
import argparse
import ast
import bisect
import importlib.util
import json
from pathlib import Path
import re
import sys

ROOT=Path(__file__).resolve().parents[2]
PROBES=ROOT/"evidence/probes/Rule10"
sys.dont_write_bytecode=True


def module(path,name):
    spec=importlib.util.spec_from_file_location(name,path)
    result=importlib.util.module_from_spec(spec);spec.loader.exec_module(result);return result


P=module(Path(__file__).with_name("rule10_prepare.py"),"dl_crh_scan_prepare")
R=module(Path(__file__).with_name("rule10_run.py"),"dl_crh_scan_run")


def lexer():
    # Reuse only the inspected pure literal/comment masker and continuation-list
    # inventory definitions from the archived scanner; never execute its main.
    path=P.ARCH/"archived-gate10-tools/scan_explicit.py"
    tree=ast.parse(path.read_text())
    names={"blank","closing","list_start","inventory"}
    nodes=[node for node in tree.body if isinstance(node,ast.FunctionDef) and node.name in names
           or isinstance(node,ast.Assign) and any(isinstance(t,ast.Name) and t.id in {"TACTIC","HEADWORD"} for t in node.targets)]
    scope=dict(re=re,bisect=bisect,need=P.need)
    exec(compile(ast.Module(body=nodes,type_ignores=[]),str(path)+"::<pure inventory>","exec"),scope)
    return scope


def declaration_context(raw,items):
    code=lexer()["blank"](raw)
    lines=code.splitlines(keepends=True)
    namespace=[];stack=[];opens=[];declarations=[];contexts={};opening=False
    for number,line in enumerate(lines,1):
        if line.startswith("namespace "):
            stack.append((list(namespace),list(opens)))
            namespace+=line.split()[1].split(".")
        elif re.match(r"^(?:noncomputable\s+)?section(?:\s|$)",line):
            stack.append((list(namespace),list(opens)))
        elif re.match(r"^end(?:\s|$)",line) and stack:
            namespace,opens=stack.pop()
        if line.startswith("open "):
            tokens=line.split()[1:]
            if "in" not in tokens and "scoped" not in tokens:
                opens+=tokens;opening=True
        elif opening and line[:1].isspace() and line.strip() and not re.match(r"\s*(theorem|def|lemma|variable|set_option)\b",line):
            opens+=line.split()
        else:
            opening=False
        match=re.match(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec)\s+)*(theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|axiom)\s*([^\s:({\[]*)",line)
        if match:
            name=match[2] or "<anonymous-instance@"+str(number)+">"
            full=name[7:] if name.startswith("_root_.") else ".".join(namespace+[name])
            declarations.append(dict(name=full,kind=match[1],line=number,namespace=".".join(namespace)))
        contexts[number]=dict(namespace=".".join(namespace),opens=list(dict.fromkeys(opens)))
    for index,decl in enumerate(declarations):
        end=declarations[index+1]["line"]-1 if index+1<len(declarations) else len(lines)
        body="".join(lines[decl["line"]-1:end])
        decl["end"]=end
        decl["code_hash"]=P.sha(re.sub(r"\s+"," ",body).strip().encode())
        # Local binders are recorded conservatively, so their apparent global
        # suffix matches never become an unsupported native-resolution claim.
        locals_=set(re.findall(r"\b(?:let|have|set)\s+([\w']+)",body))
        locals_.update(re.findall(r"[({]\s*([\w']+)\s*(?::|[({])",body))
        for intro in re.findall(r"\b(?:intro|rintro)\s+([^\n;]+)",body):
            locals_.update(re.findall(r"[\w']+",intro))
        decl["local_names"]=sorted(locals_)
    result=[]
    for item in items:
        row=dict(item,**contexts[item["line"]])
        owners=[d for d in declarations if d["line"]<=item["line"]<=d["end"]]
        row.update(declaration=owners[-1]["name"] if owners else "<command/header>",
                   local_names=owners[-1]["local_names"] if owners else [])
        result.append(row)
    return result,declarations


def native_probe(owners,heads):
    lines=["import Lean"]+["import "+m for m in owners]+[
      "", "set_option maxHeartbeats 0","set_option maxRecDepth 65536","open Lean Elab Command", "",
      "def scanHeads : Array String := #["+", ".join(json.dumps(h,ensure_ascii=False) for h in sorted(heads))+"]",
      "def scanKind : ConstantInfo → String",
      '  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem" | .opaqueInfo _ => "opaque"',
      '  | .quotInfo _ => "quotient" | .inductInfo _ => "inductive" | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"',
      "run_cmd do", "  let env ← getEnv", "  let names := env.header.moduleNames", "  let mut count := 0",
      "  for (n, ci) in env.constants.toList do", "    let display := n.toString",
      "    let user := ((Lean.privateToUserName? n).getD n).toString",
      '    unless scanHeads.any (fun h => display == h || display.endsWith ("." ++ h) || user == h || user.endsWith ("." ++ h)) do continue',
      '    let home := match env.getModuleIdxFor? n with | some i => names[i.toNat]!.toString | none => "<builtin>"',
      '    IO.println ("SCAN-CAND " ++ (Json.mkObj [("name",toJson display),("user_name",toJson user),("home",toJson home),("kind",toJson (scanKind ci)),("private",toJson (Lean.privateToUserName? n).isSome)]).compress)',
      "    count := count + 1",'  IO.println s!"SCAN-COUNT {count}"', ""]
    return "\n".join(lines)


def prepare(edition,side):
    out=PROBES/edition
    state=json.loads((PROBES/"base-state.json" if side=="base" else out/"snapshot.json").read_text())
    tree=ROOT/state["root"] if side=="base" else ROOT
    R.verify_source_snapshot(state,tree)
    lex=lexer(); inventory=[];decls={};heads=set()
    base_decl={}
    if side=="final":
        for owner in P.BASE_OWNERS:
            raw=P.git(P.modpath(owner)).decode()
            _,ds=declaration_context(raw,lex["inventory"](raw))
            base_decl[owner]={d["name"]:d for d in ds}
    for owner in state["owners"]:
        path=P.modpath(owner);raw=(tree/path).read_text()
        rows,ds=declaration_context(raw,lex["inventory"](raw));decls[path]=ds
        own={d["name"]:d for d in ds}
        for row in rows:
            before=base_decl.get(owner,{}).get(row["declaration"])
            now=own.get(row["declaration"])
            status="BASE" if side=="base" else "NEW" if before is None else "SAME" if now and before["code_hash"]==now["code_hash"] else "CHANGED"
            row.update(module=owner,path=path,declaration_status=status)
            inventory.append(row);heads.add(row["head"])
            if "." in row["head"]: heads.add(row["head"].rsplit(".",1)[1])
    source=native_probe(state["owners"],heads).encode()
    rel=Path("evidence/probes/Rule10")/edition/("Scan"+side.title()+".lean")
    target=tree/rel;P.need(not target.exists(),"scan probe already exists")
    target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(source)
    copy=out/"scan-sources"/(side+".lean.txt");copy.parent.mkdir(parents=True,exist_ok=True);copy.write_bytes(source)
    P.save(out/(side+"-scan-plan.json"),dict(side=side,edition=edition,module=rel.with_suffix("").as_posix(),
        source_sha256=P.sha(source),delivered_source=str(copy.relative_to(ROOT)),items=inventory,declarations=decls,
        method="Fresh archived continuation-list lexer; native candidate kind/home table; conservative lexical resolution with unresolved rows retained."))
    print("Prepared",len(inventory),side,"explicit items and native candidate probe; no Lean invoked")


def run(edition,side):
    plan=json.loads((PROBES/edition/(side+"-scan-plan.json")).read_text())
    state=json.loads((PROBES/"base-state.json" if side=="base" else PROBES/edition/"snapshot.json").read_text())
    tree=ROOT/state["root"] if side=="base" else ROOT
    R.verify_source_snapshot(state,tree)
    if side=="base": R.verify_base_products(state)
    else: R.verify_final_products(state)
    P.need(R.sha(tree/(plan["module"]+".lean"))==plan["source_sha256"],"scan probe changed")
    result=R.run_one(plan["module"],side,"scan-"+side,edition)
    P.need(result["exit_code"]==0 and result["source_unchanged"],"native kind probe failed")
    analyze(edition,side,ROOT/result["log"])


def resolve(row,candidates):
    token=row["head"].removeprefix("_root_.")
    first=token.split(".",1)[0]
    if first in row["local_names"]:
        return "LOCAL_BINDER_OR_MEMBER",[]
    def exact(name):
        return [c for c in candidates if c["name"]==name or c["user_name"]==name
                and (not c["private"] or c["home"]==row["module"])]
    if row["head"].startswith("_root_."):
        found=exact(token);return ("RESOLVED" if len(found)==1 else "AMBIGUOUS" if found else "UNRESOLVED"),found
    namespace=row["namespace"].split(".") if row["namespace"] else []
    for length in range(len(namespace),-1,-1):
        found=exact(".".join(namespace[:length]+[token]))
        if found:return ("RESOLVED" if len(found)==1 else "AMBIGUOUS"),found
    found=[]
    for opened in row["opens"]:
        prefixes=[".".join(namespace[:i]+[opened]) for i in range(len(namespace),-1,-1)]
        for prefix in prefixes:
            for c in exact(prefix+"."+token):
                if c not in found:found.append(c)
    return ("RESOLVED" if len(found)==1 else "AMBIGUOUS" if found else "UNRESOLVED"),found


def analyze(edition,side,log):
    plan=json.loads((PROBES/edition/(side+"-scan-plan.json")).read_text())
    candidates=[];counts=[]
    for line in log.read_text().splitlines():
        if line.startswith("SCAN-CAND "):candidates.append(json.loads(line[10:]))
        elif line.startswith("SCAN-COUNT "):counts.append(int(line[11:]))
    P.need(len(counts)==1 and counts[0]==len(candidates),"incomplete native scan table")
    rows=[]
    for item in plan["items"]:
        status,found=resolve(item,candidates)
        defs=[c for c in found if c["kind"]=="def" and c["home"]!=item["module"]]
        rows.append(dict(item,resolution=status,candidates=found,foreign_definitions=defs))
    output=dict(side=side,edition=edition,status="INVENTORY_WITH_NATIVE_CANDIDATES_REQUIRES_REVIEW",
                native_log=str(log.relative_to(ROOT)),native_log_sha256=R.sha(log),native_candidates=candidates,
                items=rows,foreign_definition_items=[r for r in rows if r["foreign_definitions"]],
                unresolved_items=[r for r in rows if r["resolution"] in {"UNRESOLVED","AMBIGUOUS"}],
                limits=["Local-name/source namespace resolution is conservative lexical analysis, not replay of the original elaborator scope.",
                        "Every ambiguous/unresolved item is retained for manual disposition; no automatic clearance claim.",
                        "Native kind/home candidates include Mathlib/core definitions as well as TCSlib."])
    P.save(PROBES/edition/(side+"-explicit-scan.json"),output)
    print("Native-backed scan:",len(rows),"items;",len(output["foreign_definition_items"]),
          "foreign-definition candidate items;",len(output["unresolved_items"]),"unresolved/ambiguous retained")


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command",choices=("prepare","run","analyze"));parser.add_argument("--edition",required=True)
    parser.add_argument("--side",choices=("base","final"),required=True);parser.add_argument("--log",type=Path)
    args=parser.parse_args()
    if args.command=="prepare":prepare(args.edition,args.side)
    elif args.command=="run":run(args.edition,args.side)
    else:P.need(args.log is not None,"--log required");analyze(args.edition,args.side,args.log.resolve())


if __name__=="__main__":main()
