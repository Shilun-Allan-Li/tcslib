"""Publish only PR #239 and this proof audit's owned exchange inputs; never merge."""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
REPO = "Shilun-Allan-Li/tcslib"
REMOTE = "https://github.com/" + REPO + ".git"
TOPIC = "cryptography/lwe-sis-dyadic-arithmetic"
CENTRAL = "cryptography/lwe-sis-constructions"
EXCHANGE = "exchange/pass-shelat-ch5-8"
SOURCE = (HERE / "evidence/source-pin.txt").read_text().strip()


def git(checkout, *args, capture=True):
    result = subprocess.run(["git", "-C", str(checkout), *args],
                            capture_output=capture, text=True, check=True)
    return result.stdout.strip() if capture else ""


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--worker", choices=["codex", "claude"])
    parser.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    assert args.check_only or args.worker, "Select Codex or Claude freshly for this proof audit."
    record = json.loads((HERE / "review-publication.json").read_text())
    publisher = Path(record["publisher_checkout"])
    assert publisher.name == "tcslib-exchange-lwe-sis-publish" and (publisher / ".git").is_dir()
    assert Path(git(ROOT, "rev-parse", "--show-toplevel")) == ROOT
    assert git(ROOT, "branch", "--show-current") == TOPIC
    assert not git(ROOT, "status", "--porcelain"), "Own PR checkout must be clean."
    assert git(ROOT, "remote", "get-url", "--push", "--all", "origin") == REMOTE
    assert record["source_pin"] == SOURCE
    if record["selected_worker"] is not None and args.worker:
        assert args.worker == record["selected_worker"], "Respect this job's recorded reviewer choice."
    assert not git(ROOT, "diff", "--name-only", SOURCE, "HEAD", "--",
                   "TCSlib", "TCSlib.lean", "lean-toolchain", "lake-manifest.json")
    for row in record["source_files"]:
        assert hashlib.sha256((ROOT / row["path"]).read_bytes()).hexdigest() == row["sha256"]

    def check_exchange():
        assert git(publisher, "branch", "--show-current") == record["publisher_branch"]
        assert not git(publisher, "status", "--porcelain"), "Private publisher must be clean."
        assert git(publisher, "remote", "get-url", "--push", "--all", "origin") == REMOTE
        for row in record["files"]:
            assert row["path"].startswith("lwe-sis-constructions/")
            assert hashlib.sha256((publisher / row["path"]).read_bytes()).hexdigest() == row["sha256"]

    check_exchange()
    if args.check_only:
        print(f"Clean own draft and private publisher; {len(record['source_files'])} frozen sources and {len(record['files'])} payload hashes pass.")
        return

    def gh(*values):
        return subprocess.check_output(["gh", *values], cwd=ROOT, text=True).strip()

    pr = json.loads(gh("pr", "view", "239", "--repo", REPO, "--json",
                       "headRefName,baseRefName,state,isDraft"))
    assert pr["headRefName"] == TOPIC and pr["baseRefName"] == CENTRAL
    assert pr["state"] == "OPEN" and pr["isDraft"], "Inspect a closed or non-draft PR first."
    head = git(ROOT, "rev-parse", "HEAD")
    git(ROOT, "push", "--no-follow-tags", "origin", head + ":refs/heads/" + TOPIC, capture=False)
    gh("pr", "edit", "239", "--repo", REPO,
       "--title", "Prove dyadic scalar arithmetic for cryptographic encodings",
       "--body-file", str(HERE / "PR_BODY.md"))
    git(publisher, "-c", "rebase.autoStash=false", "pull", "--rebase", "origin", EXCHANGE,
        capture=False)
    check_exchange()
    pending = git(publisher, "diff", "--name-only", "--no-renames", "FETCH_HEAD", "HEAD").splitlines()
    assert all(p.startswith("lwe-sis-constructions/") for p in pending), pending
    git(publisher, "push", "--no-follow-tags", "origin", "HEAD:refs/heads/" + EXCHANGE,
        capture=False)
    pin = git(publisher, "rev-parse", "HEAD")
    print("\nPR #239 updated; exchange commit: " + pin)
    print("Paste into a fresh " + args.worker.capitalize() + " auditor chat:\n")
    print("Audit the LWE/SIS dyadic scalar arithmetic proofs, round 1, in " + REPO + ".")
    print("Read " + EXCHANGE + " at exact commit " + pin + ".")
    print("Read README.md, lwe-sis-constructions/README.md, then " + record["gate_path"] + "/README.md.")
    print("Verify SHA256SUMS and both revision-qualified BUNDLE-FILES indexes; follow the first-section pack.")
    print("Statement freeze: " + record["statement_freeze"] + "; filled Lean/root: " + SOURCE + ".")
    print("Bundled records: " + record["records_pin"] + ".")
    print("Bundle SHA-256: " + record["bundle_sha256"] + "; sections: " + str(record["sections"]) + ".")
    print("Review all 12 filled proofs, 18 unchanged declarations, the complete owned inventory and sixteen backing contracts.")
    print("PR #239 targets " + CENTRAL + ". Return lwe-sis-dyadic-arithmetic-proofs-findings.md as Markdown in chat.")
    print("Do not edit, fill, dispatch workers, push or merge.")
    print("\nOnly the own draft and owned exchange inputs were pushed; the user dispatches. No branch was merged.")


if __name__ == "__main__":
    try:
        main()
    except subprocess.CalledProcessError as error:
        raise SystemExit("Publication stopped after exit " + str(error.returncode)
                         + "; inspect the error. No force or merge was attempted.") from None
