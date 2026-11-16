set -u
D=/home/user/exchange/inbox/fills/gsw-security
export PATH=$HOME/.elan/bin:$PATH
cd /home/user/fill
until grep -qE "^ALL 147 OK|^STOP" $D/evidence/checkpoint1/sweep.log; do sleep 5; done
grep -qE "^STOP" $D/evidence/checkpoint1/sweep.log && { echo "SWEEP STOPPED"; exit 1; }
python3 -I $D/evidence/tools/run_seals.py probes/seals/cp1-base
python3 -I $D/evidence/tools/run_seals.py probes/seals/cp1
python3 -I $D/evidence/tools/run_seals.py probes/controls/cp1
python3 -I $D/evidence/tools/check_module.py --maxerrors0 probes/axioms/cp1/Axioms $D/evidence/checkpoint1/axioms.log
echo QUEUE-DONE
