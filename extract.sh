#!/usr/bin/bash

# The following lines beginning with "# SBATCH" are automatically parsed if this script is run via sbatch 
#SBATCH --partition=cpu
#SBATCH --cpus-per-task=128
#SBATCH --mem=512G
#SBATCH --time=48:00:00
#SBATCH --output=logs/extract.out
#SBATCH --error=logs/extract.out

source /home/jclune/.bashrc
cd /home/jclune/LeanPremise/ntp-toolkit
conda activate lm

MAX_WORKERS=128 # set according to your RAM capacity
CONFIG=configs/config_mathlib_full.json
rm -rf Examples/mathlib
stdbuf -o0 python scripts/extract_repos.py --config $CONFIG --cwd "`pwd`" --imports --max-workers $MAX_WORKERS
stdbuf -o0 python scripts/extract_repos.py --config $CONFIG --cwd "`pwd`" --declarations --skip_setup --max-workers $MAX_WORKERS
stdbuf -o0 python scripts/extract_repos.py --config $CONFIG --cwd "`pwd`" --training_data_with_premises --skip_setup --max-workers $MAX_WORKERS
stdbuf -o0 python scripts/extract_repos.py --config $CONFIG --cwd "`pwd`" --full_proof_training_data --skip_setup --max-workers $MAX_WORKERS  # this one is not necessary; only used for e.g. proof length analysis in paper
stdbuf -o0 python scripts/extract_repos.py --config $CONFIG --cwd "`pwd`" --add_imports --skip_setup --max-workers $MAX_WORKERS
lake exe update_hammer_blacklist > Examples/mathlib/HammerBlacklist.jsonl
stdbuf -o0 python scripts/get_config_revision.py --config $CONFIG > Examples/mathlib/revision

OUTPUT_DIR=/data/user_data/jclune/mathlib
mkdir -p $OUTPUT_DIR
rm -rf $OUTPUT_DIR
cp -r Examples/mathlib $OUTPUT_DIR
