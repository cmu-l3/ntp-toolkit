"""
Converts lean_reservoir.json to config.json format for ntp-toolkit.
"""

import json
import os

import pandas as pd

if __name__ == "__main__":
    reservoir_json_file = "lean_reservoir.json"
    reservoir_dataframe = pd.read_json(reservoir_json_file)
    output_dir = "configs"
    os.makedirs(output_dir, exist_ok=True)
    for index, row in reservoir_dataframe.iterrows():
        config = {
            "repo": row["repositoryURL"],
            "commit": row["commitVersion"],
            "lean": f"leanprover/lean4:{row['leanVersion']}",
            "name": row["packageName"],
            # note: we only extract one (main) import
            "imports": [row["importName"]],
        }
        import re
        safe_title = re.sub(r'[^a-zA-Z0-9_\-]', '--', row['reservoirTitle'])
        output_file = os.path.join(output_dir, f"{safe_title}.json")
        with open(output_file, "w") as f:
            json.dump(config, f, indent=4)
