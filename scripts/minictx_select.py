"""Select theorems that go into miniCTX from a raw minictx.jsonl file.

Currently this generates miniCTX-v2/valid and miniCTX-v2/test from miniCTX-v2/raw in the current directory.
(The raw data being output from ntp-toolkit)."""

import argparse
import json
import subprocess
import tqdm
import random

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='Convert data from a miniCTX repository to a random test+valid set.')
    parser.add_argument('repo', type=str, nargs='+', help='Name of repo (e.g. PFR)')
    parser.add_argument('--size', type=int, default=50, help='Size of valid and test set')
    parser.add_argument('--cutoff_date', type=str, default="2024-11-28", help='Earliest theorem possible (YYYY-MM-DD)')

    args = parser.parse_args()

    for repo in args.repo:

        print(f"=== {repo} ===")

        minictx_raw_file = f"miniCTX-v2/raw/{repo}.jsonl"

        with open(minictx_raw_file, 'r') as file:
            minictx_raw_data = [json.loads(line) for line in file]

        print(f"Before filtering, {len(minictx_raw_data)=}")

        # filter raw to only theorems
        minictx_raw_data = [
            d for d in minictx_raw_data
            if "lemma " in d["theoremStatement"] or "theorem " in d["theoremStatement"]
        ]

        # filter to only theorems with sorryless proof
        minictx_raw_data = [
            d for d in minictx_raw_data
            if d["proofMetadata"]["hasProof"]
        ]

        minictx_raw_data = [
            d for d in minictx_raw_data
            if d["theoremCreated"]["date"] is not None and d["theoremCreated"]["date"] > args.cutoff_date
        ]

        print(f"After filtering, {len(minictx_raw_data)=}")
        if len(minictx_raw_data) < args.size * 2:
            print(f"Warning: not enough data for extracting splits, wanted at least 2 * {args.size}, got {len(minictx_raw_data)}")
            print(f"         Proceeding by extracting only {len(minictx_raw_data) // 2} for each of test/valid")
            size = len(minictx_raw_data) // 2
        else:
            size = args.size

        random.seed(0)
        test_valid_data = random.sample(minictx_raw_data, size * 2)
        test_data = test_valid_data[:size]
        valid_data = test_valid_data[size:]

        with open(f"miniCTX-v2/valid/{repo}.jsonl", "w") as f:
            for d in valid_data:
                json.dump(d, f)
                f.write('\n')
        with open(f"miniCTX-v2/test/{repo}.jsonl", "w") as f:
            for d in test_data:
                json.dump(d, f)
                f.write('\n')
