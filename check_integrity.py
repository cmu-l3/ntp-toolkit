import os
import json

def is_jsonl_well_formed(file_path):
    """Check if a JSONL file is well-formed."""
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            for line_number, line in enumerate(f, start=1):
                line = line.strip()
                if line:  # Skip empty lines
                    json.loads(line)
        return True
    except json.JSONDecodeError as e:
        print(f"Error in file {file_path} on line {line_number}: {e}")
        return False
    except Exception as e:
        print(f"Encountered error {e}")
        return False

def check_jsonl_files(directory):
    """Check all JSONL files under a directory."""
    check_files_exist(directory)
    for root, _, files in os.walk(directory):
        for file in sorted(files):
            if file.endswith('.jsonl'):
                file_path = os.path.join(root, file)
                if is_jsonl_well_formed(file_path):
                    pass
                    # print(f"{file_path} is well-formed.")
                else:
                    print(f"{file_path} is NOT well-formed.")

def check_files_exist(directory):
    with open(os.path.join(directory, "Modules.jsonl")) as f:
        modules = [json.loads(l)["name"] for l in f]
    for subdir in os.listdir(directory):
        if subdir not in ["TrainingDataWithPremises", "Declarations", "Imports"]:
            continue
        dir = os.path.join(directory, subdir)
        files = os.listdir(dir)
        for m in modules:
            if f"{m}.jsonl" not in files:
                print(f"{m} not in {dir}")

if __name__ == "__main__":
    print("About to begin check_integrity.py")
    for examples_dir in ["Examples/mathlib", "/data/user_data/jclune/mathlib"]:
        if os.path.exists(examples_dir):
            check_jsonl_files(examples_dir)
        else:
            print(f"Directory {examples_dir} does not exist.")
    print("Finished checking integrity")
