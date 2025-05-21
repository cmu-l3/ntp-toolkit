#!/usr/bin/bash

#SBATCH --cpus-per-task=16
#SBATCH --mem=128G
#SBATCH --time=48:00:00
#SBATCH --output=logs/extract.out
#SBATCH --error=logs/extract.out

source /home/thomaszh/.bashrc
cd /home/thomaszh/ntp-toolkit
conda activate lm

MW=16

lake exe cache get
lake build
rm -rf Examples/Mathlib
python scripts/extract_repos.py --config configs/config_mathlib_full.json --cwd "`pwd`" --imports --skip_setup --max-workers $MW
python scripts/extract_repos.py --config configs/config_mathlib_full.json --cwd "`pwd`" --declarations --skip_setup --max-workers $MW
python scripts/extract_repos.py --config configs/config_mathlib_full.json --cwd "`pwd`" --training_data_with_premises --skip_setup --max-workers $MW
python scripts/extract_repos.py --config configs/config_mathlib_full.json --cwd "`pwd`" --full_proof_training_data --skip_setup --max-workers $MW
python scripts/extract_repos.py --config configs/config_mathlib_full.json --cwd "`pwd`" --add_imports --skip_setup --max-workers $MW
lake exe update_hammer_blacklist > Examples/Mathlib/HammerBlacklist.jsonl

OUTPUT_DIR=/data/user_data/thomaszh

rm -rf $OUTPUT_DIR/Mathlib
cp -r Examples/Mathlib $OUTPUT_DIR/
