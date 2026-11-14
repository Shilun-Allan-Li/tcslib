#!/usr/bin/env python3
"""Prepare or serially run paired full-request-set sensitivity controls.

Use python3 -I. Preparation never invokes Lean. Running uses rule10_run's
one-module-at-a-time runner and the parent's launch/memory wrappers. A sealed
negative must produce exactly one diagnostic in its recorded source range;
unsealed counterparts and published-reader positives must produce no errors.
"""
from __future__ import annotations
import argparse
import importlib.util
import json
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[2]
PROBES=ROOT/"evidence/probes/Rule10"
sys.dont_write_bytecode=True


def load(path,name):
    spec=importlib.util.spec_from_file_location(name,path)
    module=importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    return module


P=load(Path(__file__).with_name("rule10_prepare.py"),"dl_crh_controls_prepare")
R=load(Path(__file__).with_name("rule10_run.py"),"dl_crh_controls_run")


# Each entry is a target definition, a body reading (negative if requested),
# and a reader/noninterference positive. These are evidence controls only.
# The matcher body and instance test follow the archived Gate06 controls.
CASES=[
 ("InArg","Complexity.NUPPT.inArg",
  "example (z : List Bool) : Complexity.NUPPT.inArg z = Complexity.pairSndD (Complexity.pairFstD (Complexity.pairFstD z)) := rfl\n",
  "example (z : List Bool) : Complexity.NUPPT.inArg z = Complexity.pairSndD (Complexity.pairFstD (Complexity.pairFstD z)) := Complexity.NUPPT.inArg_eq z\n",
  ("Complexity.NUPPT.inArg_eq","TCSlib.Complexity.Randomized.Closure"),False),
 ("AdvInput","Complexity.NUPPT.advInput",
  "example (n : ℕ) (y : List Bool) : Complexity.NUPPT.advInput n y = Turing.pairEncode (List.replicate n true) y := rfl\n",
  "example (n : ℕ) (y : List Bool) : Complexity.NUPPT.advInput n y = Turing.pairEncode (List.replicate n true) y := Complexity.NUPPT.advInput_eq n y\n",
  ("Complexity.NUPPT.advInput_eq","TCSlib.Complexity.Randomized.PPT"),False),
 ("Uexp","TCSlib.Cryptography.uexp",
  "example (f : Fin 3 → ℝ) : TCSlib.Cryptography.uexp f = (∑ a, f a) / Fintype.card (Fin 3) := rfl\n",
  "example (f : Fin 3 → ℝ) : TCSlib.Cryptography.uexp f = (∑ a, f a) / Fintype.card (Fin 3) := TCSlib.Cryptography.uexp_def f\n",
  ("TCSlib.Cryptography.uexp_def","TCSlib.Cryptography.Foundations.Probability"),False),
 ("PadFin","TCSlib.Cryptography.padFin",
  "example (l : ℕ) (w : List Bool) (j : Fin l) : TCSlib.Cryptography.padFin l w j = w.getD j false := rfl\n",
  "example (l : ℕ) (w : List Bool) (j : Fin l) : TCSlib.Cryptography.padFin l w j = w.getD j false := TCSlib.Cryptography.padFin_apply l w j\n",
  ("TCSlib.Cryptography.padFin_apply","TCSlib.Cryptography.Asymptotic.Adversary"),False),
 ("SplitBits","TCSlib.Cryptography.Authentication.splitBits",
  "example {a b : ℕ} (w : Fin (a+b) → Bool) (j : Fin a) : (TCSlib.Cryptography.Authentication.splitBits w).1 j = w (Fin.castAdd b j) := rfl\n",
  "example {a b : ℕ} (w : Fin (a+b) → Bool) (j : Fin a) : (TCSlib.Cryptography.Authentication.splitBits w).1 j = w (Fin.castAdd b j) := TCSlib.Cryptography.Authentication.splitBits_fst w j\n",
  ("TCSlib.Cryptography.Authentication.splitBits_fst","TCSlib.Cryptography.Authentication.Encoding"),False),
 ("Eval","Complexity.PolyExpr.eval",
  "example (n : ℕ) : (Complexity.PolyExpr.const 2).eval n = 2 := rfl\n",
  "example (n : ℕ) : (Complexity.PolyExpr.const 2).eval n = 2 := Complexity.PolyExpr.eval_const 2 n\n",
  ("Complexity.PolyExpr.eval_const","TCSlib.Complexity.Randomized.PolyExpr"),False),
 ("Matcher","Complexity.polyTimeComputable_iterateFind.match_1",
  "example (o : Option ℕ) (a : ℕ → List Bool) (b : List Bool) :\n    Complexity.polyTimeComputable_iterateFind.match_1 (fun _ => List Bool) o (fun i => a i) (fun _ => b) =\n      (match o with | some i => a i | none => b) := rfl\n",
  "example (n : ℕ) : n = n := rfl\n",None,False),
 ("Instance","Turing.instInhabitedCfg",
  "example : (default : Turing.Cfg 0 Bool Unit []) =\n    ⟨none, 0, (fun _ _ => none), (fun _ => 0), []⟩ := rfl\n",
  "example : (default : Turing.Cfg 0 Bool Unit []) = (default : Turing.Cfg 0 Bool Unit []) := rfl\n",
  None,False),
 ("ExpGenFun","TCSlib.Cryptography.Candidates.expGenFun",
  "example {V : List Bool → Prop} (G : TCSlib.Cryptography.Candidates.ExpGroupGen V) (z : List Bool) :\n    TCSlib.Cryptography.Candidates.expGenFun G z =\n      if G.n₀ ≤ (Complexity.NUPPT.inParam z).length then\n        Turing.pairEncode (G.gen.output (Complexity.NUPPT.layout (Complexity.NUPPT.inParam z) [] [] (Complexity.NUPPT.inCoins z))) []\n      else Turing.pairEncode TCSlib.Cryptography.Candidates.dlDefaultIndex [] := rfl\n",
  "example {V : List Bool → Prop} (G : TCSlib.Cryptography.Candidates.ExpGroupGen V) (z : List Bool) :\n    TCSlib.Cryptography.Candidates.expGenFun G z =\n      if G.n₀ ≤ (Complexity.NUPPT.inParam z).length then\n        Turing.pairEncode (G.gen.output (Complexity.NUPPT.layout (Complexity.NUPPT.inParam z) [] [] (Complexity.NUPPT.inCoins z))) []\n      else Turing.pairEncode TCSlib.Cryptography.Candidates.dlDefaultIndex [] := TCSlib.Cryptography.Candidates.expGenFun_eq G z\n",
  ("TCSlib.Cryptography.Candidates.expGenFun_eq","TCSlib.Cryptography.Candidates.DiscreteLog"),True),
 ("ExpSampleRaw","TCSlib.Cryptography.Candidates.expSampleRaw",
  "example (z : List Bool) : TCSlib.Cryptography.Candidates.expSampleRaw z =\n    TCSlib.Cryptography.Candidates.natToList (TCSlib.Cryptography.Candidates.dlW (Complexity.NUPPT.inArg z))\n      ((TCSlib.Cryptography.Candidates.sampleBelowL (TCSlib.Cryptography.Candidates.dlM (Complexity.NUPPT.inArg z))\n        (Nat.size (TCSlib.Cryptography.Candidates.dlM (Complexity.NUPPT.inArg z)))\n        (Complexity.NUPPT.inParam z).length (Complexity.NUPPT.inParam z).length (Complexity.NUPPT.inCoins z)).getD 0) := rfl\n",
  "example (z : List Bool) : TCSlib.Cryptography.Candidates.expSampleRaw z =\n    TCSlib.Cryptography.Candidates.natToList (TCSlib.Cryptography.Candidates.dlW (Complexity.NUPPT.inArg z))\n      ((TCSlib.Cryptography.Candidates.sampleBelowL (TCSlib.Cryptography.Candidates.dlM (Complexity.NUPPT.inArg z))\n        (Nat.size (TCSlib.Cryptography.Candidates.dlM (Complexity.NUPPT.inArg z)))\n        (Complexity.NUPPT.inParam z).length (Complexity.NUPPT.inParam z).length (Complexity.NUPPT.inCoins z)).getD 0) := TCSlib.Cryptography.Candidates.expSampleRaw_eq z\n",
  ("TCSlib.Cryptography.Candidates.expSampleRaw_eq","TCSlib.Cryptography.Candidates.DiscreteLog"),True),
]


def prepare(edition,side):
    directory=PROBES/edition
    manifest=json.loads((directory/(side+"-seal-manifest.json")).read_text())
    state=json.loads((PROBES/"base-state.json" if side=="base" else directory/"snapshot.json").read_text())
    tree=ROOT/state["root"] if side=="base" else ROOT
    builder,adapter=P.builders()
    old=P.ARCH/"archived-gate10-tools"
    ctl=P.load_tool(old/"build_controls.py","dl_crh_control_catalog")
    # Configure the standalone catalogue builder using the same reviewed
    # actual-Name payload adapter, without configuring builder twice.
    legacy=P.load_tool(old/"legacy_request_payload_adapter.py","dl_crh_control_legacy")
    original=ctl.catalog_command
    ctl.catalog_command=lambda b,l,rows,phase: adapter.augment(
        legacy.replace_request_build(original(b,l,rows,phase),rows,metadata=True),rows,l,"catalog-"+phase)
    plans=[]
    for entry in manifest["probes"]:
        seal=json.loads((ROOT/entry["record"]).read_text())
        have={r["spelling"] for r in seal["rows"]}
        selected=[case for case in CASES if (case[1] in have or
                    case[1]=="Complexity.PolyExpr.eval" and seal["variant"]=="A")
                  and not (side=="base" and case[5])]
        P.need(any(case[1] in have for case in selected),"no negative controls cover seal")
        ctl.READERS={case[4][0]:case[4][1] for case in selected if case[4]}
        for sealed in (False,True):
            label="DlCrhControl"+("S" if sealed else "U")+"_"+side+"_"+seal["variant"]+"_"+seal["owner"].replace(".","_")
            source=("import Lean\nimport "+seal["owner"]+"\n\nset_option maxHeartbeats 0\n"
                    "set_option autoImplicit false\nset_option relaxedAutoImplicit false\n\n").encode()
            source+=builder.seal_command(label,seal["rows"],end=False) if sealed else ctl.catalog_command(builder,label,seal["rows"],"unsealed")
            source+=b"namespace DlCrhControls\n\n"
            controls=[]
            for name,target,negative,positive,reader,_ in selected:
                for body,is_body in ((negative,True),(positive,False)):
                    first=source.count(b"\n")+1
                    source+=body.encode()+b"\n"
                    controls.append(dict(name=name+("Body" if is_body else "Reader"),target=target,
                         negative=is_body and target in have,
                         notation_exempt_body=is_body and target not in have,
                         start_line=first,end_line=first+body.count("\n")-1,
                         positive_kind="published-reader" if not is_body and reader else "noninterference" if not is_body else None))
            source+=b"end DlCrhControls\n\n"
            source+=builder.seal_command(label,seal["rows"],end=True) if sealed else ctl.catalog_command(builder,label,seal["rows"],"eof")
            rel=Path("evidence/probes/Rule10")/edition/"controls"/side/(label+".lean")
            target=tree/rel
            P.need(not target.exists(),"control source already exists")
            target.parent.mkdir(parents=True,exist_ok=True); target.write_bytes(source)
            copy=directory/"control-sources"/side/(label+".lean.txt")
            copy.parent.mkdir(parents=True,exist_ok=True); copy.write_bytes(source)
            plan=dict(label=label,side=side,variant=seal["variant"],owner=seal["owner"],sealed=sealed,
                      module=rel.with_suffix("").as_posix(),source_sha256=P.sha(source),
                      delivered_source=str(copy.relative_to(ROOT)),controls=controls,
                      expected_errors=[c["start_line"] for c in controls if c["negative"]] if sealed else [],
                      seal_record=entry["record"],rows=seal["rows"],
                      chunks=P.seal_chunks(label,seal["rows"]), chunk_size=P.CHUNK_SIZE,
                      harness_revision=P.HARNESS_REVISION,
                      attribute_installation="Lean.Attribute.add n `irreducible Lean.Syntax.missing .local")
            plans.append(plan)
    P.save(directory/(side+"-controls-plan.json"),dict(status="PREPARED_NOT_RUN",side=side,edition=edition,probes=plans))
    print("Prepared",len(plans),side,"control probes; sealed negatives:",sum(len(p["expected_errors"]) for p in plans))


def run(edition,side):
    plans=json.loads((PROBES/edition/(side+"-controls-plan.json")).read_text())["probes"]
    state=json.loads((PROBES/"base-state.json" if side=="base" else PROBES/edition/"snapshot.json").read_text())
    tree=ROOT/state["root"] if side=="base" else ROOT
    R.verify_source_snapshot(state,tree)
    if side=="base": R.verify_base_products(state)
    else: R.verify_final_products(state)
    _,adapter=P.builders()
    for plan in plans:
        source=tree/(plan["module"]+".lean")
        P.need(R.sha(source)==plan["source_sha256"],"control source changed")
        raw=R.run_one(plan["module"],side,"controls-"+side,edition)
        log=ROOT/raw["log"]; text=log.read_text(errors="replace")
        if plan["sealed"]:
            for chunk in plan["chunks"]:
                rows=plan["rows"][chunk["start"]:chunk["start"]+chunk["count"]]
                filtered="\n".join(line for line in text.splitlines()
                    if not ("G06-COMPONENT label=" in line or "G06-MASK label=" in line)
                    or "label="+chunk["label"]+" " in line)
                adapter.verify_component_log(filtered,chunk["label"],rows,("install","eof"))
                adapter.verify_mask_log(filtered,chunk["label"],rows,("install","eof"))
        else:
            adapter.verify_component_log(text,plan["label"],plan["rows"],("catalog-unsealed","catalog-eof"))
        unmatched=list(raw["errors"]); checks=[]
        for c in plan["controls"]:
            hits=[e for e in unmatched if c["start_line"] <= e["line"] <= c["end_line"]]
            expected=1 if plan["sealed"] and c["negative"] else 0
            ok=len(hits)==expected
            checks.append(dict(control=c["name"],target=c["target"],expected_errors=expected,
                               actual_errors=len(hits),passed=ok,errors=hits))
            unmatched=[e for e in unmatched if e not in hits]
        expected_total=len(plan["expected_errors"])
        passed=all(c["passed"] for c in checks) and not unmatched and raw["source_unchanged"] and (
            (raw["exit_code"]!=0 if expected_total else raw["exit_code"]==0))
        result=dict(label=plan["label"],side=side,variant=plan["variant"],owner=plan["owner"],
                    sealed=plan["sealed"],passed=passed,checks=checks,unexpected_errors=unmatched,
                    raw_log=raw["log"],raw_log_sha256=raw["log_sha256"])
        out=ROOT/"evidence/logs/rule10"/edition/("controls-"+side)/"control-validation.jsonl"
        with out.open("a") as handle: handle.write(json.dumps(result,ensure_ascii=False)+"\n")
        P.need(passed,"control sensitivity failed: "+plan["label"])
    print("PASS every paired control; each sealed negative failed exactly once")


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command",choices=("prepare","run")); parser.add_argument("--edition",required=True)
    parser.add_argument("--side",choices=("base","final"),required=True)
    args=parser.parse_args()
    (prepare if args.command=="prepare" else run)(args.edition,args.side)


if __name__=="__main__": main()
