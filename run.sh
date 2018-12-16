#!/usr/bin/env bash
source ./venv/bin/activate
cd ./src/
#python -m run --program-size=2 --synthesizer=deepcoder --logfile=deepcoder_2.log
python -m run --program-size=2 --synthesizer=neo --logfile=neo_2.log
python -m run --program-size=2 --synthesizer=neo_a --logfile=neoA_2.log
python -m run --program-size=2 --synthesizer=neo_ah --logfile=neoAH_2.log
#python -m run --program-size=3 --synthesizer=deepcoder --logfile=deepcoder_3.log
#python -m run --program-size=3 --synthesizer=neo --logfile=neo_3.log
#python -m run --program-size=3 --synthesizer=neo_a --logfile=neoA_3.log
#python -m run --program-size=3 --synthesizer=neo_ah --logfile=neoAH_3.log
#python -m run --program-size=4 --synthesizer=deepcoder --logfile=deepcoder_4.log
#python -m run --program-size=4 --synthesizer=neo --logfile=neo_4.log
#python -m run --program-size=4 --synthesizer=neo_a --logfile=neoA_4.log
#python -m run --program-size=4 --synthesizer=neo_ah --logfile=neoAH_4.log