import glob
import os
import argparse
import subprocess
import json
import tiktoken
import time
from pathlib import Path
from tqdm import tqdm
from concurrent.futures import ProcessPoolExecutor, as_completed


TACTIC_JSONL_DIRS = {
    'training_data': 'TacticPrediction',
}

FULL_PROOF_JSONL_DIRS = {
    'full_proof_training_data': 'FullProof',
}

SRC_DIRS = {
    'split_rw': 'SplitRw',
}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--pipeline-output-base-dir', nargs='+', type=str, default=['Examples/Mathlib'])
    parser.add_argument('--blacklist', nargs='*', type=str, default=['equational_theories.Generated'])
    parser.add_argument('--out-json', type=str, default=None)
    args = parser.parse_args()

    enc = tiktoken.encoding_for_model("gpt-4")

    stats = {}

    for k, v in SRC_DIRS.items():
        print(v)
        files = [
            f for base_dir in args.pipeline_output_base_dir for f in glob.glob(os.path.join(base_dir, v, '*.lean'))
            if not any(Path(f).name.startswith(b) for b in args.blacklist)
        ]
        stats['%s_files' % v] = len(files)

        num_lines = 0
        num_tokens = 0

        for f in tqdm(files, total=len(files)):
            with open(f, 'r') as f:
                text = f.read()
                tokens = len(enc.encode(text))
                num_tokens += tokens
                num_lines += len(text.split('\n'))
        stats['%s_lines' % v] = num_lines
        stats['%s_tokens' % v] = num_tokens

    for k, v in TACTIC_JSONL_DIRS.items():
        print(v)
        files = [
            f for base_dir in args.pipeline_output_base_dir for f in glob.glob(os.path.join(base_dir, v, '*.jsonl'))
            if not any(Path(f).name.startswith(b) for b in args.blacklist)
        ]
        stats['%s_files' % v] = len(files)

        num_tactics = 0
        for f in tqdm(files, total=len(files)):
            with open(f, 'r') as f:
                for line in f:
                    num_tactics += 1
        stats['%s_tactics' % v] = num_tactics

    for k, v in FULL_PROOF_JSONL_DIRS.items():
        print(v)
        files = [
            f for base_dir in args.pipeline_output_base_dir for f in glob.glob(os.path.join(base_dir, v, '*.jsonl'))
            if not any(Path(f).name.startswith(b) for b in args.blacklist)
        ]

        num_theorems = 0
        for f in tqdm(files, total=len(files)):
            with open(f, 'r') as f:
                for line in f:
                    num_theorems += 1
        stats['%s_theorems' % v] = num_theorems

    for k, v in stats.items():
        print(k, v, sep='\t')

    if args.out_json is not None:
        with open(args.out_json, 'w') as f:
            json.dump(stats, f)
