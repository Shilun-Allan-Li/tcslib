set -u
D=/home/user/exchange/inbox/fills/gsw-security
O=/home/user/exchange/outbox/fills/gsw-security
export PATH=$HOME/.elan/bin:$PATH
cd /home/user/fill
mkdir -p $D/evidence/final
for m in TCSlib/Cryptography/Hashing/SIS/Columns TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Security; do
  python3 -I $D/evidence/tools/check_module.py $m $D/evidence/final/owned/$(echo $m | tr / _).log
done
python3 -I $D/evidence/tools/run_list.py $O/order.txt $D/evidence/final/sweep $D/evidence/final/sweep.log
tail -1 $D/evidence/final/sweep.log
python3 -I $D/evidence/tools/run_seals.py probes/seals/final-base
python3 -I $D/evidence/tools/run_seals.py probes/seals/final
python3 -I $D/evidence/tools/check_module.py --maxerrors0 probes/axioms/final/Axioms $D/evidence/final/axioms.log
python3 -I $D/evidence/tools/run_seals.py probes/controls/final
echo QUEUE-DONE
