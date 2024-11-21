# Convert outputs from extract_repos to miniCTX format

import argparse
import glob
import json
import os
import subprocess
import re


def get_theorem_commit(theorem_name: str, repo_path):
    try:
        git_log_command = [
            "git", "log", "--reverse", "--pretty=format:%H %ad", "--date=short", "-S", theorem_name
        ]
        result = subprocess.run(git_log_command, cwd=repo_path, capture_output=True, text=True, check=True)

        if not result.stdout:
            # Theorem not found; try removing top-level name segment and searching again
            if "." in theorem_name:
                return get_theorem_commit(theorem_name.split(".", 1)[1], repo_path)
            else:
                return (None, None)
        first_commit_info = result.stdout.splitlines()[0]
        commit_hash, commit_date = first_commit_info.split(" ", 1)
        return commit_hash.strip() , commit_date.strip()
    except Exception as e:
        print(f"Error finding commit for {theorem_name}: {e}")
        return (None, None)


def get_file_commit(file_path, repo_path):
    file_path = file_path.removeprefix(repo_path)

    try:
        git_log_command = [
            "git", "log", "--reverse", "--pretty=format:%H %ad", "--date=short", file_path
        ]
        result = subprocess.run(git_log_command, cwd=repo_path, capture_output=True, text=True, check=True)

        if not result.stdout:
            print(f"File {file_path} not found")
            return (None, None)
        first_commit_info = result.stdout.splitlines()[0]
        commit_hash, commit_date = first_commit_info.split(" ", 1)
        return commit_hash.strip() , commit_date.strip()
    except Exception as e:
        print(f"Error finding commit for {file_path}: {e}")
        return (None, None)

parser = argparse.ArgumentParser()
parser.add_argument(
    'input_dir', type=str,
    help='Input directory containing output from extract_repos.py (e.g. Examples/Mathlib)'
)
parser.add_argument(
    'out_file', type=argparse.FileType('w'),
    help='Output in miniCTX format as .jsonl'
)
args = parser.parse_args()


repo_premises = set()
for filename in glob.glob(os.path.join(args.input_dir, 'Premises/*.jsonl')):
    with open(filename) as file:
        for line in file:
            data = json.loads(line)
            repo_premises.add(data['name'])

theorems = []
for filename in glob.glob(os.path.join(args.input_dir, 'FullProof/*.jsonl')):
    premises_map = {}
    premises_filename = filename.replace('FullProof', 'Premises', 1)
    with open(premises_filename) as premises_file:
        for line in premises_file:
            data = json.loads(line)
            premises_map[data['name']] = data
    with open(filename) as file:
        for i, line in enumerate(file):
            data = json.loads(line)
            context = data['srcUpToDecl']
            name = data['declName']
            proof = data['proof']

            if name in premises_map:
                premise_info = premises_map[name]
                has_in_file_dependency = any(d['name'] in premises_map for d in premise_info['dependents'])
                has_repo_dependency = any(d['name'] in repo_premises for d in premise_info['dependents'])
                num_repo_dependencies = sum(d['name'] in repo_premises for d in premise_info['dependents'])
                num_in_file_dependencies = sum(d['name'] in premises_map for d in premise_info['dependents'])
                num_dependencies = len(premise_info['dependents'])
                imported_modules = premise_info['importedModules']
            else:
                # not available (because of some probably fixable error)
                has_in_file_dependency = None
                has_repo_dependency = None
                imported_modules = None
                num_repo_dependencies = None
                num_in_file_dependencies = None
                num_dependencies = None

            file_path = data['file']
            # file_dir = os.path.dirname(file_path)  # a subdirectory in the repo
            repo_path_match = re.search(r"^(\./)*\.lake/packages/[^/]+/", file_path)
            if not repo_path_match:
                raise ValueError(f"Unrecognized repository path in {file_path}")
            repo_path = repo_path_match.group(0)
            file_commit, file_date = get_file_commit(file_path, repo_path)
            theorem_commit, theorem_date = get_theorem_commit(name, repo_path)
            file_path_pretty = re.sub(r"(\./)*\.lake/packages/", "", file_path)

            theorems.append({
                'srcContext': context,
                'theoremStatement': data['decl'],
                'theoremName': name,

                'fileCreated': {"commit": file_commit, "date": file_date},
                'theoremCreated': {"commit": theorem_commit, "date": theorem_date},
                'file': file_path_pretty,
                'module': data['module'],
                'jsonFile': os.path.basename(filename),

                'positionMetadata': {
                    'lineInFile': 1 + context.count('\n'),
                    'tokenPositionInFile': len(context),
                    # The JSONL is collected in order (see full_proof_training_data)
                    'theoremPositionInFile': i,
                },
                'dependencyMetadata': {
                    'inFilePremises': has_in_file_dependency,
                    'numInFilePremises': num_in_file_dependencies,
                    'repositoryPremises': has_repo_dependency,
                    'numRepositoryPremises': num_repo_dependencies,
                    'numPremises': num_dependencies,
                    'importedModules': imported_modules,
                },
                'proofMetadata': {
                    'hasProof': 'sorry' not in proof,
                    'proof': proof,
                    'proofType': 'tactic' if proof.startswith(':= by') else 'term',
                    'proofLengthLines': proof.count('\n'),
                    'proofLengthTokens': len(proof),
                }
            })

for theorem in theorems:
    args.out_file.write(json.dumps(theorem))
    args.out_file.write('\n')
args.out_file.close()
