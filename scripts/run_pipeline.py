import glob
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
}

def _get_stem(input_module, input_file_mode):
    if input_file_mode:
        stem = Path(input_module).stem
    else:
        stem = input_module
    return stem

def _run_cmd(cmd, cwd, input_file, output_file):
    with open(output_file, 'w') as f:
        subprocess.run(
            ['lake', 'exe', cmd, input_file],
            cwd=cwd,
            check=True,
            stdout=f
        )

def _extract_module(input_module, input_file_mode, output_base_dir, cwd, training_data, full_proof_training_data,
                    premises, state_comments, full_proof_training_data_states, training_data_with_premises):
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

    print(input_module)
    return 1


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--output-base-dir', default='Examples/Mathlib')
    parser.add_argument('--cwd', default='/Users/wellecks/projects/ntptutorial/partI_nextstep/ntp_lean/llm-training-data')
    parser.add_argument(
        '--input-file', 
        default=None, 
        help='input file in the Examples folder'
    )
    parser.add_argument(
        '--import-file', 
        help='Runs the pipeline on all modules imported in the given lean file.',
        default='.lake/packages/mathlib/Mathlib.lean'
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
    args = parser.parse_args()
    
    if ((not args.training_data) and (not args.full_proof_training_data) and (not args.premises) and (not args.state_comments)
        and (not args.full_proof_training_data_states) and (not args.training_data_with_premises)):
        raise AssertionError('''At least one of the following flags must be set: [--training_data, --full_proof_training_data, 
                             --premises, --state_comments, --full_proof_training_data_states, --training_data_with_premises]''')

    Path(args.output_base_dir).mkdir(parents=True, exist_ok=True)
    for name in DIR_NAMES.values():
        Path(os.path.join(args.output_base_dir, name)).mkdir(parents=True, exist_ok=True)

    print("Building...")
    subprocess.run(['lake', 'build', 'training_data'], check=True)
    subprocess.run(['lake', 'build', 'full_proof_training_data'], check=True)
    subprocess.run(['lake', 'build', 'premises'], check=True)
    subprocess.run(['lake', 'build', 'training_data_with_premises'], check=True)

    input_modules = []
    if args.input_file is not None:
        input_modules.extend(
            glob.glob(args.input_file)
        )
    elif args.import_file is not None:
        with open(args.import_file) as f:
            for line in f.readlines():
                if 'import ' in line:
                    chunks = line.split('import ')
                    module = chunks[1].strip()
                    input_modules.append(module)
    else:
        raise AssertionError('one of --input-file or --import-file must be set')

    completed = []
    start = time.time()
    with ProcessPoolExecutor(args.max_workers) as executor:
        input_file_mode = args.input_file is not None
        futures = [
            executor.submit(
                _extract_module,
                input_module=input_module,
                input_file_mode=input_file_mode,
                output_base_dir=args.output_base_dir,
                cwd=args.cwd,
                training_data=args.training_data,
                full_proof_training_data=args.full_proof_training_data,
                premises=args.premises,
                state_comments=args.state_comments,
                full_proof_training_data_states=args.full_proof_training_data_states,
                training_data_with_premises=args.training_data_with_premises,
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

    subprocess.run(
        ['python', 'scripts/convert_minictx.py', args.output_base_dir, os.path.join(args.output_base_dir, 'minictx.jsonl')],
        cwd=args.cwd,
        check=True
    )
