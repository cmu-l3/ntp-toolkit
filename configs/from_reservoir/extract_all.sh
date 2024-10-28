# usage: sh extract_all.sh --training_data --full_proof_training_data [... additional flags]

# cd "$(dirname "$0")"
# python fetch_reservoir_index.py
# rm -rf reservoir-index

cd "$(dirname "$0")/../.."
for file in configs/from_reservoir/configs/*.json; do
    if [ -f "$file" ]; then
        echo "Processing $file"
        if python scripts/lean_version_supported.py "$file"; then
            python scripts/extract_repos.py --cwd "`pwd`" --config $file --skip_existing $@
        else
            echo "Lean version not supported for $file"
        fi
    fi
done
