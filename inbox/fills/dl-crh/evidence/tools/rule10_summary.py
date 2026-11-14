#!/usr/bin/env python3
"""Summarize raw seals, paired controls, all-stored axioms and statement metadata.

This never invokes Lean. It verifies recorded raw-log/probe hashes and keeps
source failures separate from invalid harness runs. An explicit scan inventory
remains a manual-review input; this tool does not silently clear unresolved rows.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT=Path(__file__).resolve().parents[2]
PROBES=ROOT/"evidence/probes/Rule10"


def need(test,why):
    if not test:raise RuntimeError(why)


def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()


def read_jsonl(path):
    return [json.loads(line) for line in path.read_text().splitlines() if line.strip()] if path.exists() else []


def latest(rows,key):
    result={}
    for row in rows:
        k=row[key]
        if row.get("end",row.get("raw_log",""))>=result.get(k,{}).get("end",result.get(k,{}).get("raw_log","")):
            result[k]=row
    return result


def parse_census(path):
    rows={};counts=[]
    for line in path.read_text().splitlines():
        if line.startswith("C\t"):
            p=line.split("\t")
            need(len(p)==13,"bad census row width")
            key=(p[4],p[1]);need(key not in rows,"duplicate normalized stored-constant identity")
            axs=[] if p[12]=="[]" else [x.strip() for x in p[12].strip("[]").split(",")]
            rows[key]=dict(name=p[1],module=p[4],internal=p[2],private=p[3],kind=p[5],
                           type_hash=p[6],reducibility=p[7],abbrev=p[8],simp=p[9],instance=p[10],protected=p[11],axioms=axs)
        elif line.startswith("C-COUNT "):counts.append(int(line[8:]))
    need(len(counts)==1 and counts[0]==len(rows),"incomplete census output")
    return rows


def source_key(error):
    declaration=error.get("declaration", "<unmapped>")
    if declaration.startswith("<command@"):
        return "anonymous-command: "+re.sub(r"\s+"," ",error.get("heading",""))
    return declaration


def seals(edition,base_edition=None):
    results={};table=[];all_ok=True
    for side in ("base","final"):
        actual_edition=(base_edition or edition) if side=="base" else edition
        manifest=json.loads((PROBES/actual_edition/(side+"-seal-manifest.json")).read_text())
        done=latest(read_jsonl(ROOT/"evidence/logs/rule10"/actual_edition/("seals-"+side)/"results.jsonl"),"label")
        for entry in manifest["probes"]:
            row=done.get(entry["label"]);need(row is not None,"missing raw seal run: "+entry["label"])
            raw_log=ROOT/row["log"]
            need(sha(raw_log)==row["log_sha256"],"seal log hash differs")
            need(row["source_sha256"]==entry["probe_sha256"],"seal probe binding differs")
            request=json.loads((ROOT/entry["record"]).read_text())
            need(sha(ROOT/request["delivered_probe_source"])==entry["probe_sha256"],"delivered seal source differs")
            valid=row.get("harness_error") is None and row.get("actual_name_components_verified") and row.get("mask_verified") and row["source_unchanged"]
            source_errors=[e for e in row.get("failing_declarations",[]) if e["classification"]=="SOURCE"]
            unexpected=[e for e in row.get("failing_declarations",[]) if e["classification"]!="SOURCE"]
            # EOF metadata can have printed before a later native/output
            # failure. A nonzero native check without mapped source errors is
            # invalid evidence, and mapped errors must not accompany success.
            native_exit_consistent=(row["exit_code"]!=0 if source_errors else row["exit_code"]==0)
            lean_exit_statuses=[int(x) for x in re.findall(
                r"^FAIL\([^\n]*\): lean exited with status (\d+)$",raw_log.read_text(errors="replace"),re.M)]
            native_exit_consistent=native_exit_consistent and all(x==1 for x in lean_exit_statuses)
            valid=valid and not unexpected and native_exit_consistent
            all_ok=all_ok and valid
            fail=sorted({source_key(e) for e in source_errors})
            result=dict(side=side,evidence_edition=actual_edition,owner=entry["owner"],variant=entry["variant"],valid=bool(valid),
                        exit_code=row["exit_code"],failing_declarations=fail,errors=source_errors,
                        native_exit_consistent=bool(native_exit_consistent),lean_exit_statuses=lean_exit_statuses,
                        unexpected_errors=unexpected,harness_error=row.get("harness_error"),log=row["log"])
            results[(side,entry["owner"],entry["variant"])]=result;table.append(result)
    deltas=[]
    owners=sorted({owner for side,owner,variant in results if side=="final"})
    for owner in owners:
        for variant in ("A","B"):
            final=results[("final",owner,variant)];base=results.get(("base",owner,variant))
            before=set(base["failing_declarations"]) if base else set();after=set(final["failing_declarations"])
            deltas.append(dict(owner=owner,variant=variant,base_exists=base is not None,
                               new_failures=sorted(after-before),removed_failures=sorted(before-after),
                               inherited_failures=sorted(before&after)))
    return dict(all_harnesses_valid=bool(all_ok),table=table,deltas=deltas,
                new_failing_declarations=sum(len(d["new_failures"]) for d in deltas))


def controls(edition,base_edition=None):
    result={};all_pass=True
    for side in ("base","final"):
        actual_edition=(base_edition or edition) if side=="base" else edition
        plan=json.loads((PROBES/actual_edition/(side+"-controls-plan.json")).read_text())
        done=latest(read_jsonl(ROOT/"evidence/logs/rule10"/actual_edition/("controls-"+side)/"control-validation.jsonl"),"label")
        rows=[]
        for p in plan["probes"]:
            r=done.get(p["label"]);need(r is not None,"missing control validation: "+p["label"])
            need(sha(ROOT/r["raw_log"])==r["raw_log_sha256"],"control raw-log hash differs")
            need(sha(ROOT/p["delivered_source"])==p["source_sha256"],"delivered control source differs")
            all_pass=all_pass and r["passed"];rows.append(r)
        result[side]=rows
    return dict(all_pass=bool(all_pass),sides=result,
                evidence_editions=dict(base=base_edition or edition,final=edition))


def axioms(base_log,final_log):
    base=parse_census(base_log);final=parse_census(final_log)
    allowed={"propext","Classical.choice","Quot.sound"}
    target=("TCSlib.Cryptography.Hashing.FromDiscreteLog","TCSlib.Cryptography.Authentication.dlHash_crh")
    need(target in final,"target absent from final all-stored census")
    added=[];removed=[];changed=[];metadata_changes=[]
    for key,row in final.items():
        prior=base.get(key)
        if prior is None:added.append(row)
        else:
            fields=[field for field in ("kind","type_hash","reducibility","abbrev","simp","instance","protected") if prior[field]!=row[field]]
            if fields:metadata_changes.append(dict(module=key[0],name=key[1],fields=fields,before=prior,after=row))
            if prior["axioms"]!=row["axioms"]:changed.append(dict(module=key[0],name=key[1],before=prior["axioms"],after=row["axioms"]))
    for key,row in base.items():
        if key not in final:removed.append(row)
    nonstandard=[row for row in final.values() if set(row["axioms"])-allowed]
    new_nonstandard=[row for key,row in final.items() if set(row["axioms"])-allowed and
                     (key not in base or row["axioms"]!=base[key]["axioms"])]
    return dict(base_stored=len(base),final_stored=len(final),target_axioms=final[target]["axioms"],
                target_standard_only=not bool(set(final[target]["axioms"])-allowed),
                added=added,removed=removed,metadata_changes=metadata_changes,axiom_changes=changed,
                final_nonstandard=nonstandard,new_nonstandard=new_nonstandard,
                base_log=str(base_log.relative_to(ROOT)),base_log_sha256=sha(base_log),
                final_log=str(final_log.relative_to(ROOT)),final_log_sha256=sha(final_log))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--edition",required=True);parser.add_argument("--base-census-log",type=Path,required=True)
    parser.add_argument("--base-edition",help="Read original base evidence directly from this prior edition; never relabel raw runs")
    parser.add_argument("--final-census-log",type=Path,required=True)
    args=parser.parse_args();out=PROBES/args.edition
    base_edition=args.base_edition or args.edition
    reuse_reference=None
    if base_edition!=args.edition:
        reuse_path=out/"baseline-reuse.json"
        reuse=json.loads(reuse_path.read_text())
        need(reuse["status"]=="COMPLETE" and reuse["edition"]==args.edition and reuse["base_edition"]==base_edition and
             reuse["baseline_unchanged"] is True and reuse["raw_records_reused_without_relabeling"] is True,
             "cross-edition baseline reuse has not been verified")
        for item in reuse["original_evidence"]:
            need(sha(ROOT/item["path"])==item["sha256"],"reused original evidence changed: "+item["path"])
        base_state=json.loads((ROOT/reuse["base_state"]["path"]).read_text())
        need(sha(ROOT/reuse["base_state"]["path"])==reuse["base_state"]["sha256"] and
             base_state["source_hashes"]==reuse["source_hashes"],"reused base state changed")
        for path,digest in reuse["source_hashes"].items():
            need(sha(ROOT/base_state["snapshot_root"]/path)==sha(ROOT/base_state["root"]/path)==digest,
                 "reused baseline source changed: "+path)
        for item in reuse["runtime_object_verifications"]:
            need(sha(ROOT/item["runtime_olean_path"])==item["sha256"],"reused baseline object changed: "+item["module"])
        need(args.base_census_log.resolve()==(ROOT/reuse["base_census"]["path"]).resolve() and
             sha(args.base_census_log.resolve())==reuse["base_census"]["sha256"],"reused base census binding differs")
        reuse_reference=dict(path=str(reuse_path.relative_to(ROOT)),sha256=sha(reuse_path))
    s=seals(args.edition,base_edition);c=controls(args.edition,base_edition);a=axioms(args.base_census_log.resolve(),args.final_census_log.resolve())
    scan_paths={side:PROBES/(base_edition if side=="base" else args.edition)/(side+"-explicit-scan.json") for side in ("base","final")}
    scan={side:json.loads(path.read_text()) for side,path in scan_paths.items()}
    summary=dict(edition=args.edition,base_edition=base_edition,baseline_reuse=reuse_reference,seals=s,controls=c,axioms=a,
                 explicit_scan={side:dict(status=v["status"],items=len(v["items"]),
                     evidence_edition=base_edition if side=="base" else args.edition,
                     path=str(scan_paths[side].relative_to(ROOT)),sha256=sha(scan_paths[side]),
                     foreign_definition_items=len(v["foreign_definition_items"]),unresolved_items=len(v["unresolved_items"])) for side,v in scan.items()},
                 mechanical_checks_pass=s["all_harnesses_valid"] and s["new_failing_declarations"]==0 and c["all_pass"] and
                    a["target_standard_only"] and not a["new_nonstandard"] and not a["removed"] and not a["metadata_changes"],
                 final_clearance="NOT_ASSERTED: explicit scan dispositions and the issued full sweep/admission/lint/delivery checks require separate review")
    (out/"summary.json").write_text(json.dumps(summary,indent=2,ensure_ascii=False)+"\n")
    lines=["# dl-crh raw evidence summary","", "This is a mechanical evidence summary, not a proof-completion assertion.","",
           "| Side | Owner | Variant | Valid harness | Source failures |","|---|---|---|---|---|"]
    for row in s["table"]:lines.append(f"| {row['side']} | {row['owner']} | {row['variant']} | {row['valid']} | {len(row['failing_declarations'])} |")
    lines += ["",f"New failing declarations: {s['new_failing_declarations']}.",f"Paired controls all pass: {c['all_pass']}.",
              f"Base evidence edition: {base_edition}; fresh final evidence edition: {args.edition}. Original raw run identities are retained.",
              f"Target axioms: {a['target_axioms']}.",f"All stored constants: base {a['base_stored']}, final {a['final_stored']}.",
              "", "Every failing source declaration/command, every axiom/metadata delta, and scan limitation is retained in summary.json.",
              "Explicit-scan unresolved/ambiguous rows require dispositions; no automatic clearance is asserted."]
    (out/"summary.md").write_text("\n".join(lines)+"\n")
    print(json.dumps({"mechanical_checks_pass":summary["mechanical_checks_pass"],"new_seal_failures":s["new_failing_declarations"],
                      "controls_all_pass":c["all_pass"],"target_axioms":a["target_axioms"]}))


if __name__=="__main__":main()
