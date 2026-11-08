The actual replay was launched from a shell that first sourced the approved scratch env.sh, with escalation solely for shared lock access:

bash /Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/api/slotrun.sh python3 -I /private/tmp/ab34-fe-live1-final-validation/evidence/scripts/run_replay.py

The generated-mkreplay-NOT-EXECUTED.sh file is data only. Its network fetch would mutate Git. The executed Python driver preserves its read-only source/ref/blob/predecessor/list prechecks, uses whole cp -cR, invokes the exact scripts/lean_check_tree.sh under nice10 inside one shared slot, and retains each module's complete stdout/stderr separately. The approved helper writes only fresh .oleans into the independent complete clone. It calls Lean with -j4. The driver has no source/Git/canonical-record mutation. Lock reclamation/release is the approved slotrun helper's standard behavior.

A default-permission attempt to read process telemetry was denied by the operating-system sandbox before ps executed. The subsequent explicit read-only elevated sample succeeds and records the actual Lean PID, -j4 argv, nice10, driver ancestry, and its shared slot PID. This failed optional telemetry read did not affect compilation.
