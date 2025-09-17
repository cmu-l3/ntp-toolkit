#!/usr/bin/bash

#SBATCH --partition=cpu
#SBATCH --cpus-per-task=128
#SBATCH --mem=256G
#SBATCH --time=48:00:00
#SBATCH --output=logs/extract.out
#SBATCH --error=logs/extract.out

source /home/thomaszh/.bashrc
cd /home/thomaszh/ntp-toolkit-hammer
conda activate lm

MAX_WORKERS=16 # set according to your RAM capacity
CONFIG=configs/config_mathlib_full.json
rm -rf Examples/mathlib
python scripts/extract_repos.py --config $CONFIG --cwd "`pwd`" --imports --max-workers $MAX_WORKERS
python scripts/extract_repos.py --config $CONFIG --cwd "`pwd`" --declarations --skip_setup --max-workers $MAX_WORKERS
python scripts/extract_repos.py --config $CONFIG --cwd "`pwd`" --training_data_with_premises --skip_setup --max-workers $MAX_WORKERS
python scripts/extract_repos.py --config $CONFIG --cwd "`pwd`" --full_proof_training_data --skip_setup --max-workers $MAX_WORKERS  # this one is not necessary; only used for e.g. proof length analysis in paper
python scripts/extract_repos.py --config $CONFIG --cwd "`pwd`" --add_imports --skip_setup --max-workers $MAX_WORKERS
lake exe update_hammer_blacklist > Examples/mathlib/HammerBlacklist.jsonl
python scripts/get_config_revision.py --config $CONFIG > Examples/mathlib/revision

OUTPUT_DIR=/data/user_data/thomaszh

rm -rf $OUTPUT_DIR/mathlib
cp -r Examples/mathlib $OUTPUT_DIR
