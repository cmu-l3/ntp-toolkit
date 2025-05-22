import json
import os
import argparse
import subprocess
import time
from pathlib import Path
from tqdm import tqdm
from concurrent.futures import ProcessPoolExecutor, as_completed


DIR_NAMES = {
    'training_data': 'TacticPrediction',
    'state_comments': 'StateComments',
    'full_proof_training_data': 'FullProof',
    'full_proof_training_data_states': 'FullProofWithStates',
    'premises': 'Premises',
    'training_data_with_premises': 'TrainingDataWithPremises',
    'add_imports': 'WithImports',
    'imports': 'Imports',
    'declarations': 'Declarations'
}

def _get_stem(input_module, input_file_mode):
    if input_file_mode:
        stem = Path(input_module).stem
    else:
        stem = input_module
    return stem

def _run_cmd(cmd, cwd, input_file, output_file):
    if isinstance(input_file, str):
        input_file = [input_file]
    with open(output_file, 'w') as f:
        subprocess.run(
            ['lake', 'exe', cmd, *input_file],
            cwd=cwd,
            check=True,
            stdout=f
        )

def _extract_module(input_module, input_file_mode, output_base_dir, cwd, training_data, full_proof_training_data,
                    premises, state_comments, full_proof_training_data_states, training_data_with_premises, add_imports,
                    declarations, imports):
    # Tactic prediction
    if training_data:
        _run_cmd(
            cmd='training_data',
            cwd=cwd,
            input_file=input_module,
            output_file=os.path.join(
                output_base_dir,
                DIR_NAMES['training_data'],
                _get_stem(input_module, input_file_mode) + '.jsonl'
            )
        )

    # Full proof generation
    if full_proof_training_data:
        _run_cmd(
            cmd='full_proof_training_data',
            cwd=cwd,
            input_file=input_module,
            output_file=os.path.join(
                output_base_dir,
                DIR_NAMES['full_proof_training_data'],
                _get_stem(input_module, input_file_mode) + '.jsonl'
            )
        )

    # Premise analysis
    if premises:
        _run_cmd(
            cmd='premises',
            cwd=cwd,
            input_file=input_module,
            output_file=os.path.join(
                output_base_dir,
                DIR_NAMES['premises'],
                _get_stem(input_module, input_file_mode) + '.jsonl'
            )
        )

    # State comments
    if state_comments:
        state_comments_output_file = os.path.join(
            output_base_dir,
            DIR_NAMES['state_comments'],
            _get_stem(input_module, input_file_mode) + '.lean'
        )
        _run_cmd(
            cmd='state_comments',
            cwd=cwd,
            input_file=input_module,
            output_file=state_comments_output_file
        )

    # Full proof generation with state comments
    if full_proof_training_data_states:
        _run_cmd(
            cmd='full_proof_training_data',
            cwd=cwd,
            input_file=state_comments_output_file,
            output_file=os.path.join(
                output_base_dir,
                DIR_NAMES['full_proof_training_data_states'],
                _get_stem(input_module, input_file_mode) + '.jsonl'
            )
        )

    # Same as Tactic Prediction but with additional fields documenting premises used
    if training_data_with_premises:
        _run_cmd(
            cmd='training_data_with_premises',
            cwd=cwd,
            input_file=input_module,
            output_file=os.path.join(
                output_base_dir,
                DIR_NAMES['training_data_with_premises'],
                _get_stem(input_module, input_file_mode) + '.jsonl'
            )
        )

    # Reproduces source code with additional specified imports
    if add_imports:
        _run_cmd(
            cmd='add_imports',
            cwd=cwd,
            input_file=input_module,
            output_file=os.path.join(
                output_base_dir,
                DIR_NAMES['add_imports'],
                _get_stem(input_module, input_file_mode) + '.lean'
            )
        )

    if declarations:
        _run_cmd(
            cmd='declarations',
            cwd=cwd,
            input_file=input_module,
            output_file=os.path.join(
                output_base_dir,
                DIR_NAMES['declarations'],
                _get_stem(input_module, input_file_mode) + '.jsonl'
            )
        )

    if imports:
        _run_cmd(
            cmd='imports',
            cwd=cwd,
            input_file=input_module,
            output_file=os.path.join(
                output_base_dir,
                DIR_NAMES['imports'],
                _get_stem(input_module, input_file_mode) + '.jsonl'
            )
        )

    print(input_module)
    return 1


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--output-base-dir', default='Examples/Mathlib')
    parser.add_argument('--cwd', default='/Users/wellecks/projects/ntptutorial/partI_nextstep/ntp_lean/llm-training-data')
    parser.add_argument(
        '--import-module',
        nargs='+',
        help='Base module name(s) as entry point to a project (e.g., Mathlib, PrimeNumberTheoremAnd)'
    )
    parser.add_argument(
        '--max-workers',
        default=None,
        type=int,
        help="maximum number of processes; defaults to number of processors"
    )
    parser.add_argument(
        '--training_data',
        action='store_true'
    )
    parser.add_argument(
        '--full_proof_training_data',
        action='store_true'
    )
    parser.add_argument(
        '--premises',
        action='store_true'
    )
    parser.add_argument(
        '--state_comments',
        action='store_true'
    )
    parser.add_argument(
        '--full_proof_training_data_states',
        action='store_true'
    )
    parser.add_argument(
        '--training_data_with_premises',
        action='store_true'
    )
    parser.add_argument(
        '--add_imports',
        action='store_true'
    )
    parser.add_argument(
        '--declarations',
        action='store_true'
    )
    parser.add_argument(
        '--imports',
        action='store_true'
    )
    args = parser.parse_args()

    if ((not args.training_data) and (not args.full_proof_training_data) and (not args.premises) and (not args.state_comments)
        and (not args.full_proof_training_data_states) and (not args.training_data_with_premises) and (not args.add_imports)
        and (not args.declarations) and (not args.imports)):
        raise AssertionError('''At least one of the following flags must be set: [--training_data, --full_proof_training_data,
                             --premises, --state_comments, --full_proof_training_data_states, --training_data_with_premises,
                             --add_imports, --declarations, --imports]''')

    Path(args.output_base_dir).mkdir(parents=True, exist_ok=True)
    for name in DIR_NAMES.values():
        Path(os.path.join(args.output_base_dir, name)).mkdir(parents=True, exist_ok=True)

    print("Building...")
    subprocess.run(['lake', 'build', 'all_modules'], check=True)
    subprocess.run(['lake', 'build', 'training_data'], check=True)
    subprocess.run(['lake', 'build', 'full_proof_training_data'], check=True)
    subprocess.run(['lake', 'build', 'premises'], check=True)
    subprocess.run(['lake', 'build', 'training_data_with_premises'], check=True)
    subprocess.run(['lake', 'build', 'add_imports'], check=True)
    subprocess.run(['lake', 'build', 'declarations'], check=True)
    subprocess.run(['lake', 'build', 'imports'], check=True)

    # Extract all modules in the project
    input_modules_file = os.path.join(
        args.output_base_dir,
        'Modules.jsonl'
    )
    _run_cmd(
        cmd='all_modules',
        cwd=args.cwd,
        input_file=args.import_module,
        output_file=input_modules_file
    )
    input_modules = []
    with open(input_modules_file, 'r') as f:
        for line in f:
            input_modules.append(json.loads(line)['name'])

    completed = []
    start = time.time()
    with ProcessPoolExecutor(args.max_workers) as executor:
        futures = [
            executor.submit(
                _extract_module,
                input_module=input_module,
                input_file_mode=False,
                output_base_dir=args.output_base_dir,
                cwd=args.cwd,
                training_data=args.training_data,
                full_proof_training_data=args.full_proof_training_data,
                premises=args.premises,
                state_comments=args.state_comments,
                full_proof_training_data_states=args.full_proof_training_data_states,
                training_data_with_premises=args.training_data_with_premises,
                add_imports=args.add_imports,
                declarations=args.declarations,
                imports=args.imports
            )
            for input_module in input_modules
        ]
        for future in tqdm(as_completed(futures), total=len(futures)):
            completed.append(future.result())

            if (len(completed)+1) % 10 == 0:
                end = time.time()
                print("Elapsed %.2f" % (round(end - start, 2)))
                print("Avg/file %.3f" % (round((end - start)/len(completed), 3)))

    end = time.time()
    print("Elapsed %.2f" % (round(end - start, 2)))

    subprocess.run(
        ['python', 'scripts/data_stats.py', '--pipeline-output-base-dir', args.output_base_dir],
        cwd=args.cwd,
        check=True
    )

    if args.premises and args.full_proof_training_data:
        subprocess.run(
            ['python', 'scripts/convert_minictx.py', args.output_base_dir, os.path.join(args.output_base_dir, 'minictx.jsonl')],
            cwd=args.cwd,
            check=True
        )
