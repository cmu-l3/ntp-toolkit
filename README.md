# ntp-toolkit

The neural theorem proving toolkit transforms Lean repositories into datasets for training and evaluating machine learning models.

<img width="900" alt="ntp-toolkit" src="https://github.com/user-attachments/assets/61441106-722c-4187-a505-c0d438760582">


The toolkit is originally a fork of Kim Morrison's [lean-training-data](https://github.com/semorrison/lean-training-data) and developed in [miniCTX](https://cmu-l3.github.io/minictx/).



## Running extraction
To run the full pipeline on all repositories in a config file in the `configs` directory:
```
python scripts/extract_repos.py --cwd {filepath_of_this_repo} --config {filepath_of_config_file} [flags to indicate which processes to run]
```

The flags that can be set to indicate which processes to run are:
- `--training_data`: This outputs to the `TacticPrediction` directory
- `--full_proof_training_data`: This outputs to the `FullProof` directory
- `--premises`: This outputs to the `Premises` directory
- `--state_comments`: This outputs to the `StateComments` directory
- `--full_proof_training_data_states`: This outputs to the `FullProofWithStates` directory
- `--training_data_with_premises`: This outputs to the `TrainingDataWithPremises` directory
- `--add_imports`: This rewrites Lean files to the `WithImports` directory (and is a prerequisite for performing hammer evaluations)
- `--declarations`: This outputs to the `Declarations` directory
- `--imports`: This outputs import JSON information to the `Imports` directory

At least one of the above flags must be set in order for the script to run (but there should be no issue with setting multiple or even all of the above flags)

On a Macbook Pro (M3 Max, 14 CPU) it takes around 2 hours to run the extractions on mathlib.


To run a tool individually, use `lake exe <tool>`. \
The `run_pipeline.py` script uses Python to call tools in this way and organize the resulting files.



#### Extraction tools:
### `training_data`

This produces a `.jsonl` file where each line is an example of the following form:
```json
{
   "state": "{tactic state}",
   "nextTactic" : "{pretty-printed next tactic}",
   "srcUpToTactic" : "{source code in the file up to the tactic invocation}",
   "declUpToTactic" : "{source code in the declaration up to the tactic invocation}",
   "decl": "{declaration without proof (e.g., statement of a theorem)}",
   "declId": "{unique identifier of the declaration}"
}
```

### `full_proof_training_data`

This produces a `.jsonl` file where each line is an example of the following form:
```json
{
   "srcUpToDecl":"{source code in the file up to the declaration}",
   "decl": "{declaration without proof (e.g., statement of a theorem)}",
   "declId": "{unique identifier of the declaration}",
   "proof":"{proof}"
}
```

### `state_comments`

This produces Lean source files with proof states interleaved as comments after each tactic.

### `premises`

This produces premises used by each constant in a module.

### `declarations`

This produces information that pretty-prints each declaration in a module. The resulting format is
```json
{
   "name": "pow_two",
   "kind": "theorem",
   "args": ["{M : Type u_2}", "[Monoid M]", "(a : M)"],
   "type": "a ^ 2 = a * a",
   "doc": "Note that most of the lemmas about powers of two refer to it as `sq`.",
   "decl": "/-- Note that most of the lemmas about powers of two refer to it as `sq`. -/\ntheorem pow_two {M : Type u_2} [Monoid M] (a : M) : a ^ 2 = a * a",
   "line": 810,
   "column": 0
}
```

### `imports`
This outputs the imports of each module (both transitively imported modules and directly imported modules). The resulting format is
```json
{
   "name": "{imported module name}",
   "isDirect": "{whether it is explicitly imported by the module (otherwise it is transitively imported)}"
}
```

### `training_data_with_premises`

This produces a `.jsonl` file where each line contains all of the information in `training_data` plus the fields `nextTacticHammerRecommendation` and `declHammerRecommendation` (the former gives a hammer recommendation based solely on the next tactic and the latter gives a hammer recommendation based on the proof of the entire theorem).

### Adding new extraction tasks
You can add a new extraction task, by:
1. Add a relevant flag to `scripts/extract_repos.py`. Also change the `_lakefile` method accordingly, and add the flag to `flags`.
2. Then add an entry in `TASKS` to `scripts/run_pipeline.py`

## Running instruction tuning data generation
After extraction, you can generate various forms of (prompt, completion) examples for fine-tuning language models.

To do so, run:
```
python scripts/instruction_tuning.py --prompt context_state_tactic
```
See `python scripts/instruction_tuning.py -h` for other options for `--prompt` or other settings.

The prompt includes a natural language description of the task, commonly referred to as an "instruction" (hence the name instruction tuning data).

## Other setup docs from `lean-training-data`

You may find these useful during setup.

* Install [`elan`](https://github.com/leanprover/elan) by running

```shell
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```
* Run `lake exe cache get` (this downloads precompiled binaries for `Mathlib`).
* Run `lake build`
* Run `lake exe <tool>`, where `<tool>` is one of the programs documented below.


## Projects

Projects that use or build upon `ntp-toolkit`:
- [miniCTX: Neural Theorem Proving with (Long-)Contexts](https://cmu-l3.github.io/minictx/)
- [ImProver: Agent-Based Automated Proof Optimization](https://arxiv.org/abs/2410.04753)

Submit a PR to add your project or paper here!


## Citation

The toolkit is originally a fork of Kim Morrison's [lean-training-data](https://github.com/semorrison/lean-training-data):

```bibtex
@misc{lean-training-data,
  author = {Kim Morrison},
  title = {lean-training-data},
  year = {2023},
  publisher = {GitHub},
  journal = {GitHub repository},
  howpublished = {\url{https://github.com/semorrison/lean-training-data}},
}
```

The `ntp-toolkit` was initially developed in [miniCTX](https://cmu-l3.github.io/minictx/):
```bibtex
@misc{hu2024minictxneuraltheoremproving,
      title={miniCTX: Neural Theorem Proving with (Long-)Contexts},
      author={Jiewen Hu and Thomas Zhu and Sean Welleck},
      year={2024},
      eprint={2408.03350},
      archivePrefix={arXiv},
      primaryClass={cs.AI},
      url={https://arxiv.org/abs/2408.03350},
}
```
