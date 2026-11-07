# Actual invocations and reproducibility

Every shell invocation sourced:

```sh
source /Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/env.sh
set -e
```

Source insertion and probe preparation used `python3 -I` with `prepare_source.py` and
`prepare_checks.py`. The latter reads the existing trusted source parser and extracts only
the balanced `split_header` function; it does not execute the earlier review driver. No
delivered producer script was executed.

The complete snapshot-copy command and removed own-overlay output link are recorded in
`context.json`. `run.py` then invoked each of these once, in this order, through the managed
wrappers whose exact argument arrays are retained in the corresponding request receipts:

```sh
python3 -I campaign/gates/119-mig1-followup-api/review/first-entry/run.py Actual-module
python3 -I campaign/gates/119-mig1-followup-api/review/first-entry/run.py Finite-newsection-sealed
python3 -I campaign/gates/119-mig1-followup-api/review/first-entry/run.py Metadata
python3 -I campaign/gates/119-mig1-followup-api/review/first-entry/run.py Controls-unsealed
python3 -I campaign/gates/119-mig1-followup-api/review/first-entry/run.py Controls-sealed
```

The first run compiled the actual isolated source into the private complete overlay. Each
subsequent run copied its fully reviewed inert input to a unique `/private/tmp` file and
used the plain managed wrapper without compiled outputs. The four last run consoles were
also redirected to `*-console.txt`; `.out` files are the authoritative unmodified native
stdout/stderr payloads. Each receipt records its input hash, elapsed time, exit status,
diagnostic counts, actual command array and output hash.

After those runs, offline reconciliation used:

```sh
python3 -I campaign/gates/119-mig1-followup-api/review/first-entry/verify.py
```

The runner deliberately refuses to overwrite any existing attempt's log or receipt. New
attempts must use new names. Do not rerun `prepare_source.py` on the already edited source.
