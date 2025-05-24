import json

data_path = "test.jsonl"

with open(data_path) as f:
    theorems = [json.loads(l) for l in f]

for theorem in theorems:
    name = theorem["declName"]
    tactics = theorem["tactics"]
    # Determine declaration
    for tactic in tactics:
        if tactic["decl"]:
            decl = tactic["decl"]
            break
    else:
        continue

    state_signatures = [
        state_signature
        for tactic in tactics
        for state_signature in tactic["statesAsSignatures"]
    ]

    haves = []
    i = 1
    # The natural order of haves is reverse of the order of tactic states
    for state_signature in state_signatures[::-1]:
        have = state_signature.replace("extracted", f"have h{i}", 1)
        haves.append("  " + have + " := by sorry")
        i += 1

    print(decl + ":= by")
    for have in haves:
        print(have)
    print("  sorry")
    print()
