r"""One harness for the whole dataset build: from Lean sources (+ reference texts) to
dataset/tcslib_theorems.jsonl.gz with every column populated -- incrementally.

The dataset is never rebuilt from nothing.  Every LLM product is cached per declaration
(statement prose under references/statements/, ratings and citations in the blueprint
.tex, proof notes under references/informalized/), the deterministic stages take
seconds, and the final `dataset` stage MERGES the build into the shipped dataset:
records the build contains are replaced or added, records of modules that are not
built (not imported from TCSlib.lean) are carried over unchanged, and only a
declaration that no longer exists under its name is dropped.  So the default run after
formalizing something new touches exactly the new and changed records, and
--only / --modules restrict every stage to a chosen set of records when the intent is
"fix these" rather than "update everything".

Stages, in order (each is idempotent and resumable; run a range with --from/--to or a
subset with --stages):

  graph        [no LLM]  `lake build` (only with --build) and scripts/build_dep_graph.py.
                         Reports Lean files newer than dep_graph.json, modules on disk that
                         the graph does not contain (not imported from TCSlib.lean, so never
                         built; their records are carried over, see `dataset`).
  references   [LLM]     Each --source TAG=PATH text (PDF or validated .md) is placed under
                         blueprint/src/references/, registered for its docstring TAG in
                         references/sources.json and, for a PDF, run through
                         `proofmatch extract` (OCR + model cleanup -> <name>.md).
  blueprint    [no LLM]  blueprint_enumerate -> blueprint_stub -> blueprint_assemble:
                         every documentable declaration gets a bound blueprint entry.
  statements   [LLM]     build_dataset --no-proof (pass 1) -> build_informal_statements
                         (handout-standard prose from the formal statement, rubric-gated,
                         definitions included) -> blueprint_restate --apply-only.
  difficulty   [LLM]     blueprint_difficulty_plan -> rate_difficulty -> blueprint_difficulty_apply.
  citations    [LLM]     pass 1 again (fresh prose) -> reference_coverage (which uncited
                         theorems cite which texts, and which texts are missing) ->
                         `proofmatch match` of each new reference document against the
                         dataset: \proofsource / \statementsource citations land in the
                         chapter .tex files.
  informalize  [LLM]     informalize_proofs: a prose account of every uncited, sorry-free
                         proof -> blueprint/src/references/informalized/<name>.md.  Refuses
                         to run while NEW theorems cite a text nobody attached (see
                         "Reference texts" below) unless --without-sources is given.
  dataset      [no LLM]  build_dataset (full, with flattened proofs) -> build_proof_notes
                         -> dataset_splice --merge into dataset/tcslib_theorems.jsonl + .gz.
  verify       [no LLM]  dataset_check --strict (schema, leaks, stubs, row loss, carried-over
                         rows, optional sampled Lean compile), dataset_hygiene,
                         statement_quality, blueprint_validate --strict.

Reference texts.  The builder does not search for sources.  A theorem is cited only when
the text it was formalized from has been ingested and matched; otherwise it receives an
informalized account of its Lean proof.  The contract is that whoever submits a
formalization attaches the text in the same change:

    python3 scripts/dataset_pipeline.py --source AB09=~/texts/arora-barak-ch09.pdf --yes

`AB09` is the [TAG] the new declarations' docstrings cite (policy.md §2).
`python3 scripts/sources.py` is the short form: `status` shows every text, tag and Lean
file with what it still needs; `add TAG=PATH` attaches and matches a text.  The
`citations` stage prints, per tag, how many uncited theorems cite it and whether a
document is registered for it; `informalize` stops when a new theorem's tag has no
text.  --without-sources acknowledges that and lets the proof notes be written.

Models and backends: every LLM stage runs on --model (default: $PROOFMATCH_MODEL, else
claude-opus-4-8 on the Claude Code CLI or gpt-5 on the Codex CLI) or its per-stage
override (--model-statements, ...).  The CLI that serves the model is inferred from the
model id (an OpenAI id runs on `codex exec`, anything else on `claude -p`) or forced with
--backend claude|codex; both run read-only, structured-output, in an empty directory
(proofmatch/agents.py).  Prose and judgement stages refuse a model below the opus / gpt-5
tier unless --allow-weak-models is given; see proofmatch/model_policy.py.
--check-env lists what this machine has of the toolchain (Python, Lean, the CLI, PDF tools).

Costs: every LLM stage first prints how much work is outstanding and asks before
spending (skip the question with --yes; --estimate stops after the report).  Each stage
caches its output per declaration, so an interrupted run resumes where it stopped.

Usage:
    python3 scripts/dataset_pipeline.py --estimate                      # what would run
    python3 scripts/dataset_pipeline.py --build --yes                   # update everything
    python3 scripts/dataset_pipeline.py --build --yes --source AB09=refs/arora-barak-ch09.pdf
    python3 scripts/dataset_pipeline.py --modules Complexity.Ch09 --yes # one module's records
    python3 scripts/dataset_pipeline.py --only TCSlib.Foo.bar --from statements --to dataset
    python3 scripts/dataset_pipeline.py --stages dataset,verify --lean-check 20
    python3 scripts/dataset_pipeline.py --model claude-fable-5-1 --stages statements
    python3 scripts/dataset_pipeline.py --backend codex --model gpt-5 --estimate
    python3 scripts/dataset_pipeline.py --check-env
"""

from __future__ import annotations

import argparse
import datetime as dt
import gzip
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

BASE = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(BASE))

from proofmatch.dataset_io import open_dataset, resolve_dataset  # noqa: E402
from proofmatch.model_policy import (  # noqa: E402
    BACKENDS, DEFAULT_MODELS, check_model, default_model, backend as resolve_backend,
)

SCRIPTS = BASE / "scripts"
DATASET = BASE / "dataset" / "tcslib_theorems.jsonl"
DATASET_GZ = BASE / "dataset" / "tcslib_theorems.jsonl.gz"
DEP_GRAPH = BASE / "dep_graph.json"
REFERENCES = BASE / "blueprint" / "src" / "references"
WORK_ROOT = BASE / ".proofmatch-work"
STATE_DIR = BASE / "dataset" / ".pipeline"
PASS1 = STATE_DIR / "pass1.jsonl"
BUILT = STATE_DIR / "built.jsonl"

STAGES = ["graph", "references", "blueprint", "statements", "difficulty",
          "citations", "informalize", "dataset", "verify"]
LLM_STAGES = {"references": "cleanup", "statements": "prose", "difficulty": "judgement",
              "citations": "judgement", "informalize": "prose"}


class StageFailed(RuntimeError):
    pass


# --------------------------------------------------------------------------- #
# Plumbing
# --------------------------------------------------------------------------- #
class Runner:
    def __init__(self, args):
        self.args = args
        self.state_path = STATE_DIR / "state.json"
        self.logs = STATE_DIR / "logs"
        STATE_DIR.mkdir(parents=True, exist_ok=True)
        self.logs.mkdir(parents=True, exist_ok=True)
        self.state = {}
        if self.state_path.exists():
            try:
                self.state = json.loads(self.state_path.read_text(encoding="utf-8"))
            except ValueError:
                self.state = {}
        self.env = dict(os.environ)
        self.env["PYTHONUNBUFFERED"] = "1"
        self.env["PROOFMATCH_MODEL"] = args.model
        self.env["PROOFMATCH_COMPARE_MODEL"] = args.model
        self.env["PROOFMATCH_BACKEND"] = args.backend
        # --source TAG=PATH pairs, parsed once.
        self.sources: list[tuple[str | None, Path]] = []
        for item in args.source:
            tag, path = (item.split("=", 1) if "=" in item and not item.startswith(("/", "~", "."))
                         else (None, item))
            self.sources.append((tag.strip() if tag else None, Path(path).expanduser()))

    @property
    def selected(self) -> bool:
        return bool(self.args.only or self.args.modules)

    def selection(self) -> list[str]:
        """argv restricting a stage script to the chosen records (every script accepts both)."""
        argv: list[str] = []
        if self.args.only:
            argv += ["--only", *self.args.only]
        if self.args.modules:
            argv += ["--modules", *self.args.modules]
        return argv

    def save(self) -> None:
        self.state_path.write_text(json.dumps(self.state, indent=2), encoding="utf-8")

    def mark(self, stage: str, status: str, **extra) -> None:
        self.state[stage] = dict(status=status, at=dt.datetime.now().isoformat(timespec="seconds"),
                                 **extra)
        self.save()

    def run(self, stage: str, cmd: list[str], *, check: bool = True, env: dict | None = None,
            log_name: str | None = None) -> int:
        """Run a child command, teeing its output to the stage log."""
        log = self.logs / f"{log_name or stage}.log"
        print(f"\n$ {' '.join(str(c) for c in cmd)}")
        if self.args.dry_run:
            return 0
        with open(log, "a", encoding="utf-8") as handle:
            handle.write(f"\n### {dt.datetime.now().isoformat(timespec='seconds')} $ "
                         f"{' '.join(str(c) for c in cmd)}\n")
            proc = subprocess.Popen(cmd, cwd=BASE, env=env or self.env,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            assert proc.stdout is not None
            for line in proc.stdout:
                sys.stdout.write(line)
                handle.write(line)
            rc = proc.wait()
        if check and rc != 0:
            raise StageFailed(f"{stage}: `{cmd[0]} {cmd[1] if len(cmd) > 1 else ''}` exited {rc} "
                              f"(log: {log.relative_to(BASE)})")
        return rc

    def py(self, stage: str, script: str, *argv: str, **kw) -> int:
        return self.run(stage, [sys.executable, str(SCRIPTS / script), *argv], **kw)

    def confirm(self, stage: str, what: str) -> bool:
        if self.args.estimate:
            print(f"  [estimate] {stage}: would {what}")
            return False
        if self.args.yes or self.args.dry_run or not sys.stdin.isatty():
            return True
        answer = input(f"  {stage}: {what}. Proceed? [y/N] ").strip().lower()
        return answer in ("y", "yes")

    def stage_model(self, stage: str) -> str:
        return getattr(self.args, f"model_{stage}", None) or self.args.model


def dataset_modules(path: Path) -> dict[str, int]:
    out: dict[str, int] = {}
    if not resolve_dataset(path).exists():
        return out
    with open_dataset(path) as handle:
        for line in handle:
            if line.strip():
                module = json.loads(line).get("source_module", "")
                out[module] = out.get(module, 0) + 1
    return out


def root_import_closure() -> set[str]:
    """Modules reachable from TCSlib.lean through TCSlib imports (what `lake build` builds)."""
    seen: set[str] = set()
    stack = ["TCSlib"]
    while stack:
        module = stack.pop()
        if module in seen:
            continue
        seen.add(module)
        rel = module[len("TCSlib."):] if module.startswith("TCSlib.") else ""
        path = BASE / "TCSlib.lean" if module == "TCSlib" else BASE / "TCSlib" / (rel.replace(".", "/") + ".lean")
        if not path.exists():
            continue
        for line in path.read_text(encoding="utf-8", errors="ignore").splitlines():
            if line.startswith("import TCSlib"):
                stack.append(line.split()[1])
    return seen


def module_matches(module: str, wanted) -> bool:
    """`TCSlib.A.B` matches `TCSlib.A.B`, `A.B`, `B` (dotted suffix) or `A` (an area prefix).
    Mirrors build_dataset.module_matches (not imported: scripts/proofmatch.py shadows the
    package once scripts/ is on sys.path)."""
    for w in wanted:
        w = w.strip()
        if not w:
            continue
        full = w if w.startswith("TCSlib.") else "TCSlib." + w
        if module == full or module.endswith("." + w) or module.startswith(full + "."):
            return True
    return False


def modules_of_names(names: list[str]) -> list[str]:
    """Modules of dep_graph.json that declare any of `names` (for the blueprint stage)."""
    if not DEP_GRAPH.exists():
        return []
    graph = json.load(open(DEP_GRAPH))["modules"]
    wanted = set(names)
    return sorted(m for m, md in graph.items() if wanted & set(md.get("declarations", {})))


# --------------------------------------------------------------------------- #
# Stages
# --------------------------------------------------------------------------- #
def stage_graph(r: Runner) -> None:
    if r.args.build:
        r.run("graph", ["lake", "build"], log_name="lake-build")
        r.py("graph", "build_dep_graph.py")
    if not DEP_GRAPH.exists():
        raise StageFailed("dep_graph.json is missing; run with --build (lake build + build_dep_graph.py)")
    graph_mtime = DEP_GRAPH.stat().st_mtime
    newer = [p for p in (BASE / "TCSlib").rglob("*.lean") if p.stat().st_mtime > graph_mtime]
    if newer:
        print(f"  WARNING: {len(newer)} Lean file(s) are newer than dep_graph.json "
              f"(e.g. {newer[0].relative_to(BASE)}); pass --build to refresh the graph")
    graph = json.load(open(DEP_GRAPH))["modules"]
    reachable = root_import_closure()
    on_disk = {"TCSlib." + str(p.relative_to(BASE / "TCSlib").with_suffix("")).replace("/", ".")
               for p in (BASE / "TCSlib").rglob("*.lean")}
    unbuilt = sorted(on_disk - set(graph))
    not_built = [m for m in unbuilt if m in reachable]
    unimported = [m for m in unbuilt if m not in reachable]
    stale = sorted(set(graph) - reachable)
    gone = sorted(set(graph) - on_disk)
    print(f"  dep_graph: {len(graph)} modules; {len(gone)} of them have no source file any more; "
          f"{len(stale)} are not reachable from TCSlib.lean (stale .ilean files)")
    if not_built:
        print(f"  {len(not_built)} module(s) are imported from TCSlib.lean but NOT in the graph: "
              f"the graph predates them.  Run with --build (lake build + build_dep_graph.py).")
        for m in not_built[:8]:
            print(f"      not built: {m}")
        if len(not_built) > 8:
            print(f"      ... and {len(not_built) - 8} more (see {r.logs / 'graph.log'})")
    if unimported:
        print(f"  {len(unimported)} module(s) on disk are NOT imported from TCSlib.lean, so no "
              f"build reaches them: add `import <module>` to TCSlib.lean, then --build.")
        for m in unimported[:8]:
            print(f"      not imported: {m}")
        if len(unimported) > 8:
            print(f"      ... and {len(unimported) - 8} more (see {r.logs / 'graph.log'})")
    if gone and not r.args.build:
        print(f"  WARNING: dep_graph.json predates a source reorganisation "
              f"(e.g. {gone[0]}); its records cannot be built -- pass --build")
    (r.logs / "graph.log").write_text(
        "imported from TCSlib.lean but not in graph (run --build):\n" + "\n".join(not_built)
        + "\n\nnot imported from TCSlib.lean (add the import, then --build):\n"
        + "\n".join(unimported)
        + "\n\nstale in graph:\n" + "\n".join(stale)
        + "\n\nin graph, no source file:\n" + "\n".join(gone) + "\n",
        encoding="utf-8")
    if r.args.modules:
        chosen = sorted(m for m in graph if module_matches(m, r.args.modules))
        absent = [m for m in unbuilt if module_matches(m, r.args.modules)]
        print(f"  --modules selects {len(chosen)} built module(s)"
              + (f"; {len(absent)} selected module(s) are NOT built: {', '.join(absent[:5])}"
                 if absent else ""))
        if not chosen:
            raise StageFailed("--modules selects no module of dep_graph.json; import the "
                              "module(s) from TCSlib.lean and rerun with --build")
    previous = dataset_modules(r.args.previous)
    carried = {m: n for m, n in previous.items() if m not in graph}
    if carried:
        rows = sum(carried.values())
        verb = "WILL BE DROPPED (--drop-unbuilt)" if r.args.drop_unbuilt else \
            "will be carried over unchanged (not regenerated; pass --drop-unbuilt to drop them)"
        print(f"  {rows} record(s) of the current dataset belong to {len(carried)} module(s) "
              f"absent from dep_graph.json and {verb}:")
        for m, n in sorted(carried.items(), key=lambda kv: -kv[1])[:20]:
            print(f"      {n:5d}  {m}")
        if len(carried) > 20:
            print(f"      ... and {len(carried) - 20} more modules")
        print("  (to regenerate them: import the modules from TCSlib.lean and rerun with --build)")
    r.mark("graph", "ok", modules=len(graph), not_built=len(not_built), unimported=len(unimported),
           gone=len(gone), carried_rows=sum(carried.values()))


def stage_references(r: Runner) -> list[Path]:
    """Place each --source under references/, register its tag, make sure a validated .md exists."""
    docs: list[Path] = []
    if not r.sources:
        print("  no --source given: nothing to ingest.")
        print("  NOTE: new theorems get citations only from a text attached with "
              "--source TAG=PATH (the TAG their docstrings cite, policy.md §2); without one "
              "they fall through to `informalize`, which writes a prose account of the Lean "
              "proof instead.  The `citations` stage lists which texts are missing.")
        r.mark("references", "ok", docs=[])
        return docs
    model = r.stage_model("references")
    verdict = check_model(model, LLM_STAGES["references"], allow_weak=r.args.allow_weak_models)
    if verdict.startswith("WARNING"):
        print(verdict)
    REFERENCES.mkdir(parents=True, exist_ok=True)
    env = dict(r.env, PROOFMATCH_MODEL=model, PROOFMATCH_COMPARE_MODEL=model)
    registrations: list[str] = []
    for tag, src in r.sources:
        src = src.resolve()
        if not src.exists():
            raise StageFailed(f"references: {src} does not exist")
        dest = REFERENCES / src.name
        if src.suffix.casefold() == ".md":
            if src.name.endswith(".raw.md"):
                raise StageFailed(f"references: give the validated .md or the PDF, not {src.name}")
            if dest.resolve() != src and not r.args.dry_run:
                shutil.copy2(src, dest)
            md = dest
        else:
            if dest.resolve() != src and not dest.exists() and not r.args.dry_run:
                shutil.copy2(src, dest)
            md = dest.with_suffix(".md")
            if md.exists():
                print(f"  {md.name} already validated; skipping extraction")
            elif r.confirm("references", f"OCR + model cleanup of {dest.name} on {model}"):
                cmd = [sys.executable, str(SCRIPTS / "proofmatch.py"), "extract", str(dest)]
                if r.args.max_cost:
                    cmd += ["--max-cost", str(r.args.max_cost)]
                r.run("references", cmd, env=env)
                if not md.exists() and not r.args.dry_run:
                    raise StageFailed(f"references: extraction produced no {md.name}")
        docs.append(md)
        if tag:
            registrations.append(f"{tag}={md.stem}")
        else:
            print(f"  WARNING: {src.name} was given without a tag (--source TAG=PATH); the "
                  f"coverage report cannot tie [TAG, ...] docstrings to it.  Register it later "
                  f"with: python3 scripts/reference_coverage.py --register TAG={md.stem}")
    if registrations:
        r.py("references", "reference_coverage.py", "--dataset", str(r.args.previous),
             *[a for reg in registrations for a in ("--register", reg)], check=False)
    r.mark("references", "ok", docs=[d.name for d in docs],
           tags=[t for t, _ in r.sources if t])
    return docs


def stage_blueprint(r: Runner) -> None:
    r.py("blueprint", "blueprint_enumerate.py")
    stub_argv: list[str] = []
    if r.args.modules:
        stub_argv += [a for m in r.args.modules for a in ("--module", m)]
    if r.args.only:
        stub_argv += ["--only", *r.args.only]
        for m in modules_of_names(r.args.only):
            stub_argv += ["--module", m]
    if r.args.estimate:
        # Stubs are blueprint edits (tracked .tex files); an estimate only counts them.
        r.py("blueprint", "blueprint_stub.py", *stub_argv, "--dry-run")
        print("  [estimate] blueprint: stub entries are not written; each one is a "
              "statement to write in `statements`")
        r.mark("blueprint", "estimated")
        return
    r.py("blueprint", "blueprint_stub.py", *stub_argv)
    r.py("blueprint", "blueprint_assemble.py")
    r.py("blueprint", "blueprint_validate.py", check=False)
    r.mark("blueprint", "ok")


def pass1(r: Runner, stage: str) -> None:
    r.py(stage, "build_dataset.py", "--no-proof", "--out", str(PASS1), *r.selection(),
         log_name=f"{stage}-pass1")


def stage_statements(r: Runner) -> None:
    model = r.stage_model("statements")
    pass1(r, "statements")
    common = ["--dataset", str(PASS1), "--model", model, "--jobs", str(r.args.jobs),
              "--definitions", "stubs", *r.selection()]
    if r.args.allow_weak_models:
        common.append("--allow-weak-models")
    # A builder change (imports, instances, context) alters every formal statement
    # without changing what it says; revalidate the prose cache against the previous
    # dataset(s) first so only statements whose mathematics changed are regenerated.
    history = [str(r.args.previous)]
    if resolve_dataset(DATASET).exists():
        history.append(str(DATASET))
    rekey = ["--rekey", *history] + ([] if r.args.regenerate_unknown else ["--trust-unknown"])
    r.py("statements", "build_informal_statements.py", *common, "--estimate", *rekey)
    if r.args.estimate:
        r.mark("statements", "estimated", model=model)
        return
    if r.confirm("statements", f"regenerate the outstanding informal statements on {model}"):
        extra = ["--limit", str(r.args.limit)] if r.args.limit else []
        rc = r.py("statements", "build_informal_statements.py", *common, *extra, check=False)
        if rc != 0:
            print("  WARNING: some statements failed to generate; cached ones are kept")
    r.py("statements", "blueprint_restate.py", "--apply-only")
    r.py("statements", "dataset_hygiene.py", "--strict", check=False)
    r.mark("statements", "ok", model=model)


def stage_difficulty(r: Runner) -> None:
    model = r.stage_model("difficulty")
    r.py("difficulty", "blueprint_difficulty_plan.py")
    common = ["--model", model, "--jobs", str(r.args.jobs), *r.selection()]
    if r.args.allow_weak_models:
        common.append("--allow-weak-models")
    r.py("difficulty", "rate_difficulty.py", *common, "--estimate")
    if r.args.estimate:
        r.mark("difficulty", "estimated", model=model)
        return
    if r.confirm("difficulty", f"rate the outstanding proofs on {model}"):
        extra = ["--limit", str(r.args.limit)] if r.args.limit else []
        rc = r.py("difficulty", "rate_difficulty.py", *common, *extra, check=False)
        if rc != 0:
            print("  WARNING: some ratings failed; the rest are applied")
    r.py("difficulty", "blueprint_difficulty_apply.py")
    r.mark("difficulty", "ok", model=model)


def reference_documents(r: Runner, new_docs: list[Path]) -> list[Path]:
    if r.args.cite_all:
        return sorted(p for p in REFERENCES.glob("*.md") if not p.name.endswith(".raw.md"))
    return new_docs


def already_matched(doc: Path) -> bool:
    try:
        from proofmatch.document import parse_validated_markdown
        run_id = parse_validated_markdown(doc).source_fingerprint[:12]
    except Exception:  # noqa: BLE001 - an unparsable doc is simply "not matched yet"
        return False
    return (WORK_ROOT / run_id / "chapter_review.json").exists()


def coverage(r: Runner, stage: str, *, strict: bool) -> int:
    """reference_coverage.py over the pass-1 build: which uncited theorems cite which texts."""
    argv = ["--dataset", str(PASS1), "--report", str(STATE_DIR / "coverage.json"), *r.selection()]
    if resolve_dataset(r.args.previous).exists():
        argv += ["--previous", str(r.args.previous)]
    tags = [t for t, _ in r.sources if t]
    if tags:
        argv += ["--attached", *tags]
    if strict:
        argv += ["--strict", "--only-new"]
    return r.py(stage, "reference_coverage.py", *argv, check=False, log_name=f"{stage}-coverage")


def stage_citations(r: Runner, new_docs: list[Path]) -> None:
    model = r.stage_model("citations")
    verdict = check_model(model, LLM_STAGES["citations"], allow_weak=r.args.allow_weak_models)
    if verdict.startswith("WARNING"):
        print(verdict)
    docs = reference_documents(r, new_docs)
    docs = [d for d in docs if r.args.rematch or not already_matched(d)]
    pass1(r, "citations")
    coverage(r, "citations", strict=False)
    if r.args.estimate:
        print(f"  [estimate] citations: would match {len(docs)} document(s): "
              f"{', '.join(d.name for d in docs) or 'none'}")
        r.mark("citations", "estimated", docs=[d.name for d in docs])
        return
    if not docs:
        print("  no reference documents to match (give --source TAG=PATH, or --cite-all / --rematch)")
        r.mark("citations", "ok", docs=[])
        return
    env = dict(r.env, PROOFMATCH_MODEL=model, PROOFMATCH_COMPARE_MODEL=model)
    done = []
    for doc in docs:
        cmd = [sys.executable, str(SCRIPTS / "proofmatch.py"), "match", str(doc), "--dataset", str(PASS1)]
        if r.args.max_cost:
            cmd += ["--max-cost", str(r.args.max_cost)]
        r.run("citations", cmd + ["--dry-run"], env=env, check=False)
        if r.confirm("citations", f"match {doc.name} against the dataset on {model}"):
            rc = r.run("citations", cmd, env=env, check=False)
            if rc != 0:
                print(f"  WARNING: match of {doc.name} exited {rc}; its review (if any) is in "
                      f"{WORK_ROOT.relative_to(BASE)}")
            else:
                done.append(doc.name)
    r.mark("citations", "ok", docs=done, model=model)


def stage_informalize(r: Runner) -> None:
    model = r.stage_model("informalize")
    if not PASS1.exists() or r.args.dry_run:
        pass1(r, "informalize")
    # The gate: a NEW theorem whose docstring cites a text nobody attached gets no proof
    # note until the text is attached (--source TAG=PATH) or the omission is acknowledged.
    if not r.args.without_sources and not r.args.estimate:
        if coverage(r, "informalize", strict=True) != 0 and not r.args.dry_run:
            raise StageFailed(
                "informalize: new theorems cite reference texts that are not attached.  "
                "Attach them (--source TAG=PATH, then rerun from `references`) so they get "
                "citations, or pass --without-sources to write informalized proof notes "
                "for them instead.  Details: dataset/.pipeline/coverage.json")
    common = ["--dataset", str(PASS1), "--model", model, "--jobs", str(r.args.jobs), *r.selection()]
    if r.args.allow_weak_models:
        common.append("--allow-weak-models")
    r.py("informalize", "informalize_proofs.py", *common, "--estimate")
    if r.args.estimate:
        r.mark("informalize", "estimated", model=model)
        return
    if r.confirm("informalize", f"write proof notes for the outstanding uncited proofs on {model}"):
        extra = ["--limit", str(r.args.limit)] if r.args.limit else []
        rc = r.py("informalize", "informalize_proofs.py", *common, *extra, check=False)
        if rc != 0:
            print("  WARNING: some notes failed to generate; the rest are kept")
    r.mark("informalize", "ok", model=model)


def stage_dataset(r: Runner) -> None:
    """Build the selected (or all built) records and merge them into the shipped dataset."""
    r.py("dataset", "build_dataset.py", "--out", str(BUILT), *r.selection())
    r.py("dataset", "build_proof_notes.py", "--dataset", str(BUILT))
    argv = [str(BUILT), "--merge", "--dataset", str(DATASET),
            "--report", str(STATE_DIR / "merge.json")]
    if r.selected:
        argv.append("--selected")
    if r.args.drop_unbuilt:
        argv.append("--drop-unbuilt")
    if r.args.estimate:
        print("  [estimate] dataset: merge reported below, nothing written")
        argv.append("--dry-run")
    r.py("dataset", "dataset_splice.py", *argv)
    r.mark("dataset", "estimated" if r.args.estimate else "ok", selected=r.selected)


def stage_verify(r: Runner) -> None:
    argv = ["--dataset", str(DATASET), "--strict", "--report", str(STATE_DIR / "check.json")]
    if resolve_dataset(r.args.previous).exists():
        argv += ["--previous", str(r.args.previous)]
    if r.args.drop_unbuilt:
        argv.append("--allow-row-loss")
    if r.args.lean_check:
        argv += ["--lean-check", str(r.args.lean_check)]
    rc_check = r.py("verify", "dataset_check.py", *argv, check=False)
    r.py("verify", "dataset_hygiene.py", "--dataset", str(DATASET), check=False)
    r.py("verify", "statement_quality.py", "--dataset", str(DATASET), check=False)
    # Labels of declarations in unbuilt modules are expected while their records are
    # carried over; only with --drop-unbuilt are they genuinely stale.
    bp_argv = ["--strict"] + ([] if r.args.drop_unbuilt else ["--allow-orphans"])
    rc_bp = r.py("verify", "blueprint_validate.py", *bp_argv, check=False)
    status = "ok" if rc_check == 0 and rc_bp == 0 else "failed"
    r.mark("verify", status, dataset_check=rc_check, blueprint_validate=rc_bp)
    if status != "ok":
        raise StageFailed("verify: dataset_check or blueprint_validate reported hard failures "
                          f"(see {STATE_DIR.relative_to(BASE)}/check.json and logs/verify.log)")


# --------------------------------------------------------------------------- #
# Environment check
# --------------------------------------------------------------------------- #
def _version(cmd: list[str]) -> str | None:
    try:
        out = subprocess.run(cmd, capture_output=True, text=True, timeout=60)
    except (OSError, subprocess.TimeoutExpired):
        return None
    if out.returncode != 0:
        return None
    text = (out.stdout or out.stderr).strip().splitlines()
    return text[0][:60] if text else "ok"


def check_env(args) -> int:
    """What this machine has of what the pipeline needs; exit 1 when a required piece is missing."""
    rows: list[tuple[str, bool, str | None, str]] = []   # (what, required, found, how to get it)
    py_ok = sys.version_info >= (3, 10)
    rows.append(("python >= 3.10", True, sys.version.split()[0] if py_ok else None,
                 "install Python 3.10 or newer"))
    cli = {"claude": ("claude", "Claude Code CLI: npm install -g @anthropic-ai/claude-code, "
                                "then `claude` once to log in"),
           "codex": ("codex", "OpenAI Codex CLI: npm install -g @openai/codex, then "
                              "`codex login`")}[args.backend]
    rows.append((f"{cli[0]} CLI (--backend {args.backend}, model {args.model})", True,
                 _version([cli[0], "--version"]) if shutil.which(cli[0]) else None, cli[1]))
    other = "codex" if args.backend == "claude" else "claude"
    rows.append((f"{other} CLI (the other backend)", False,
                 _version([other, "--version"]) if shutil.which(other) else None,
                 "optional; --backend " + other))
    rows.append(("lean (toolchain of lean-toolchain, via elan)", True,
                 _version(["lean", "--version"]) if shutil.which("lean") else None,
                 "https://github.com/leanprover/elan; the project pins " +
                 (BASE / "lean-toolchain").read_text().strip()
                 if (BASE / "lean-toolchain").exists() else "install elan"))
    rows.append(("lake (graph stage --build, verify --lean-check)", True,
                 _version(["lake", "--version"]) if shutil.which("lake") else None,
                 "comes with the Lean toolchain"))
    oleans = BASE / ".lake" / "build" / "lib" / "lean" / "TCSlib"
    n_ilean = len(list(oleans.rglob("*.ilean"))) if oleans.exists() else 0
    rows.append((".lake build artifacts (the dependency graph is read from .ilean files)", True,
                 f"{n_ilean} .ilean files" if n_ilean else None,
                 "run `lake build` once (or the pipeline with --build)"))
    rows.append(("dep_graph.json", True,
                 dt.datetime.fromtimestamp(DEP_GRAPH.stat().st_mtime).strftime("%Y-%m-%d")
                 if DEP_GRAPH.exists() else None, "pipeline --build regenerates it"))
    rows.append(("pdf2txt.py (references stage, PDF sources only)", False,
                 _version(["pdf2txt.py", "--version"]) if shutil.which("pdf2txt.py") else None,
                 "pip install pdfminer.six (a Markdown source needs neither PDF tool)"))
    rows.append(("gs / Ghostscript (references stage, page images for ambiguous OCR)", False,
                 _version(["gs", "--version"]) if shutil.which("gs") else None,
                 "brew install ghostscript / apt install ghostscript"))
    rows.append(("dataset/tcslib_theorems.jsonl(.gz)", True,
                 "present" if resolve_dataset(DATASET).exists() else None,
                 "git checkout of the dataset"))
    missing_required = False
    print(f"environment for the dataset pipeline ({BASE})")
    for what, required, found, how in rows:
        status = "ok     " if found else ("MISSING" if required else "absent ")
        print(f"  {status}  {what}: {found or '-'}")
        if not found:
            print(f"           -> {how}")
        missing_required |= required and not found
    if missing_required:
        print("\nsome required pieces are missing; the pipeline cannot run yet")
        return 1
    print("\nall required pieces are present; next: python3 scripts/dataset_pipeline.py --estimate")
    return 0


# --------------------------------------------------------------------------- #
# Driver
# --------------------------------------------------------------------------- #
def selected_stages(args) -> list[str]:
    if args.stages:
        wanted = [s.strip() for s in args.stages.split(",") if s.strip()]
        bad = [s for s in wanted if s not in STAGES]
        if bad:
            raise SystemExit(f"unknown stage(s): {bad}; choose from {STAGES}")
        return [s for s in STAGES if s in wanted]
    lo = STAGES.index(args.from_stage) if args.from_stage else 0
    hi = STAGES.index(args.to_stage) if args.to_stage else len(STAGES) - 1
    return STAGES[lo: hi + 1]


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--stages", help="comma-separated subset of: " + ",".join(STAGES))
    ap.add_argument("--from", dest="from_stage", choices=STAGES)
    ap.add_argument("--to", dest="to_stage", choices=STAGES)
    ap.add_argument("--source", action="append", default=[], metavar="TAG=PATH",
                    help="a reference text (PDF or validated .md) the new statements come "
                         "from, with the [TAG] their docstrings cite; repeatable. Ingested "
                         "and registered in `references`, matched in `citations`.")
    ap.add_argument("--without-sources", action="store_true",
                    help="informalize: write proof notes for new theorems even though their "
                         "docstrings cite a text that is not attached")
    ap.add_argument("--only", nargs="+", metavar="NAME",
                    help="restrict every stage to these theorems (fully-qualified Lean names); "
                         "the dataset stage then replaces just these records")
    ap.add_argument("--modules", nargs="+", metavar="MODULE",
                    help="restrict every stage to these modules (`TCSlib.A.B`, the suffix "
                         "`A.B`, or an area such as `Complexity`)")
    ap.add_argument("--cite-all", action="store_true",
                    help="citations: match every reference document, not just --source ones")
    ap.add_argument("--rematch", action="store_true",
                    help="citations: match documents that already have a run")
    ap.add_argument("--build", action="store_true",
                    help="graph: run `lake build` and rebuild dep_graph.json first")
    ap.add_argument("--backend", choices=("auto", *BACKENDS), default="auto",
                    help="which CLI runs the LLM stages: claude (Claude Code), codex (OpenAI "
                         "Codex), or auto = inferred from the model id (default)")
    ap.add_argument("--model", default=None,
                    help="model for every LLM stage (default: $PROOFMATCH_MODEL, else "
                         + ", ".join(f"{m} on {b}" for b, m in DEFAULT_MODELS.items()) + ")")
    for stage in LLM_STAGES:
        ap.add_argument(f"--model-{stage}", dest=f"model_{stage}", metavar="MODEL",
                        help=f"model for the {stage} stage only")
    ap.add_argument("--allow-weak-models", action="store_true",
                    help="waive the per-stage model floor (proofmatch/model_policy.py)")
    ap.add_argument("--regenerate-unknown", action="store_true",
                    help="statements: regenerate cached prose whose cache key matches no "
                         "known build instead of trusting it")
    ap.add_argument("--jobs", type=int, default=4, help="concurrent model calls per stage")
    ap.add_argument("--limit", type=int, help="cap each LLM stage at this many items (pilot)")
    ap.add_argument("--max-cost", type=str, help="proofmatch --max-cost for references/citations")
    ap.add_argument("--previous", type=Path, default=None,
                    help="dataset to compare against for row loss and new records (default: "
                         "a copy of the current dataset taken when the run starts)")
    ap.add_argument("--drop-unbuilt", action="store_true",
                    help="dataset: drop records whose module is not in dep_graph.json instead "
                         "of carrying them over unchanged")
    ap.add_argument("--lean-check", type=int, default=0, metavar="N",
                    help="verify: compile N sampled formal statements")
    ap.add_argument("--yes", action="store_true", help="do not ask before spending")
    ap.add_argument("--estimate", action="store_true",
                    help="run the no-LLM stages (the dataset merge as a dry run) and only "
                         "report what the LLM stages would do")
    ap.add_argument("--dry-run", action="store_true", help="print the commands, run nothing")
    ap.add_argument("--check-env", action="store_true",
                    help="check the toolchain this machine needs (Python, Lean, the model CLI, "
                         "PDF tools) and exit")
    args = ap.parse_args()

    args.model = args.model or default_model(None if args.backend == "auto" else args.backend)
    args.backend = resolve_backend(args.model, None if args.backend == "auto" else args.backend)
    if args.check_env:
        return check_env(args)

    stages = selected_stages(args)
    print(f"dataset pipeline: {' -> '.join(stages)}")
    if args.only or args.modules:
        print("selection: " + " ".join((["--only", *args.only] if args.only else [])
                                       + (["--modules", *args.modules] if args.modules else [])))
    print(f"model: {args.model} via the {args.backend} CLI" + "".join(
        f"; {s}: {getattr(args, f'model_{s}')}" for s in LLM_STAGES if getattr(args, f"model_{s}")))
    for stage, kind in LLM_STAGES.items():
        if stage in stages:
            model = getattr(args, f"model_{stage}") or args.model
            verdict = check_model(model, kind, allow_weak=args.allow_weak_models)
            if verdict.startswith("WARNING"):
                print(verdict)

    r = Runner(args)
    # Snapshot the dataset the run starts from (taken when a run begins at `graph`, or
    # when no snapshot exists yet): the baseline for "new record", row loss and rekeying.
    if args.previous is None:
        snapshot = STATE_DIR / "previous.jsonl.gz"
        current = resolve_dataset(DATASET)
        if current.exists() and not args.dry_run and (stages[0] == "graph" or not snapshot.exists()):
            if current.suffix == ".gz":
                shutil.copy2(current, snapshot)
            else:
                with open(current, "rb") as src, gzip.open(snapshot, "wb") as dst:
                    shutil.copyfileobj(src, dst)
        args.previous = STATE_DIR / "previous.jsonl"   # resolve_dataset() finds the .gz

    new_docs: list[Path] = []
    try:
        for stage in stages:
            print(f"\n=== {stage} ===")
            r.mark(stage, "running")
            if stage == "graph":
                stage_graph(r)
            elif stage == "references":
                new_docs = stage_references(r)
            elif stage == "blueprint":
                stage_blueprint(r)
            elif stage == "statements":
                stage_statements(r)
            elif stage == "difficulty":
                stage_difficulty(r)
            elif stage == "citations":
                if not new_docs and r.sources:
                    new_docs = [REFERENCES / p.with_suffix(".md").name for _, p in r.sources]
                stage_citations(r, new_docs)
            elif stage == "informalize":
                stage_informalize(r)
            elif stage == "dataset":
                stage_dataset(r)
            elif stage == "verify":
                stage_verify(r)
    except StageFailed as error:
        r.mark(stage, "failed", error=str(error))
        print(f"\nFAILED: {error}")
        print(f"state: {r.state_path.relative_to(BASE)}; resume with --from {stage}")
        return 1
    print(f"\ndone: {' -> '.join(stages)}  (state: {r.state_path.relative_to(BASE)})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
