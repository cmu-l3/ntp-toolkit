from typing import Optional
from dataclasses import dataclass
import json
import os
import argparse
import subprocess
import time
from pathlib import Path
from tqdm import tqdm
from concurrent.futures import ProcessPoolExecutor, as_completed


# Information about each task
@dataclass
class Task:
    # Task name, as provided by the user flags
    name: str
    # Output directory name
    output_dir: str
    # Output extension, usually .jsonl
    output_file_extension: str
    # The name of the command for `lake exe command`
    command: str
    # If requires an input file that is the output of some other task
    input_file_from_task: Optional[str] = None

TASKS = [
    Task('training_data', 'TacticPrediction', '.jsonl', 'training_data'),
    Task('state_comments', 'StateComments', '.lean', 'state_comments'),
    Task('full_proof_training_data', 'FullProof', '.jsonl', 'full_proof_training_data'),
    Task('full_proof_training_data_states', 'FullProofWithStates', '.jsonl', 'full_proof_training_data', input_file_from_task='state_comments'),
    Task('training_data', 'TacticPrediction', '.jsonl', 'training_data'),
    Task('training_data', 'TacticPrediction', '.jsonl', 'training_data'),
    Task('premises', 'Premises', '.jsonl', 'premises'),
    Task('training_data_with_premises', 'TrainingDataWithPremises', '.jsonl', 'training_data_with_premises'),
    Task('imports', 'Imports', '.jsonl', 'imports'),
    Task('declarations', 'Declarations', '.jsonl', 'declarations'),
]
TASK_NAME_TO_TASK = {task.name: task for task in TASKS}


def _run_cmd(cmd, cwd, inputs, output_file):
    if isinstance(inputs, str):
        inputs = [inputs]
    with open(output_file, 'w') as f:
        subprocess.run(
            ['lake', 'exe', cmd, *inputs],
            cwd=cwd,
            check=True,
            stdout=f
        )

def _extract_module(input_module: str, output_base_dir: str, cwd: str, tasks: list[Task], skip_existing: bool):
    for task in tasks:
        output_file = os.path.join(
            output_base_dir,
            task.output_dir,
            input_module + task.output_file_extension
        )
        if skip_existing and os.path.exists(output_file):
            continue
        if task.input_file_from_task is not None:
            # For full_proof_training_data, it takes the output .lean files from state_comments as input module
            input_task = TASK_NAME_TO_TASK[task.input_file_from_task]
            input_module = '.'.join([
                output_base_dir.replace(os.path.sep, '.'),
                input_task.output_dir,
                input_module,
            ])
        _run_cmd(
            cmd=task.command,
            cwd=cwd,
            inputs=input_module,
            output_file=output_file
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
        '--task',
        choices=[task.name for task in TASKS],
        nargs='+',
        help='Choice of script(s) to run on (e.g. training_data)'
    )
    parser.add_argument(
        '--name',
        default=None,
        type=str,
        help="package name"
    )
    parser.add_argument('--skip_existing', action="store_true", help="If specified, existing outputs will not be overwritten")
    args = parser.parse_args()
    tasks = [task for task in TASKS if task.name in args.task]

    Path(args.output_base_dir).mkdir(parents=True, exist_ok=True)
    for task in tasks:
        Path(os.path.join(args.output_base_dir, task.output_dir)).mkdir(parents=True, exist_ok=True)

    print("Building...")
    subprocess.run(['lake', 'build', 'all_modules'], check=True)
    for task in tasks:
        subprocess.run(['lake', 'build', task.command], check=True)

    # Extract all modules in the project
    input_modules_file = os.path.join(
        args.output_base_dir,
        'Modules.jsonl'
    )
    _run_cmd(
        cmd='all_modules',
        cwd=args.cwd,
        inputs=args.import_module,
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
                output_base_dir=args.output_base_dir,
                cwd=args.cwd,
                tasks=tasks,
                skip_existing=args.skip_existing,
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
        ['python', 'scripts/data_stats.py', '--pipeline-output-base-dir', args.output_base_dir, '--out-json', os.path.join(args.output_base_dir, 'stats.json')],
        cwd=args.cwd,
        check=True
    )

    if 'premises' in args.task and 'full_proof_training_data' in args.task:
        subprocess.run(
            ['python', 'scripts/convert_minictx.py', args.output_base_dir, os.path.join(args.output_base_dir, 'minictx.jsonl')],
            cwd=args.cwd,
            check=True
        )
