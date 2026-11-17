#!/usr/bin/env bash
# rule10_all.sh (bb1-sim, lead): the head series' phases, then (once tree B's rebuild has finished) the base series'.
E=/home/user/exch/s/inbox/fills/bb1-sim/evidence; DRV=$E/tools/drivers/rule10_bb1sim.sh
bash $DRV head touched collect pretest seals scan
until grep -q '"done"' $E/build/base-tree/results.jsonl 2>/dev/null; do sleep 30; done
bash $DRV base touched collect baseseals
echo "ALL DONE $(date -u +%FT%TZ)"
