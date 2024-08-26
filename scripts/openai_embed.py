import json
import os

import tiktoken
from openai import OpenAI
import numpy as np
import tqdm


BATCH_SIZE = 32
EMBEDDING_SIZE = 3072

def prettify_declaration(declaration: dict) -> str:
    kind = declaration["kind"]
    name = declaration["name"]
    args = declaration["args"]
    type = declaration["type"]
    doc = declaration["doc"]
    prettified = f"{kind} {name} {' '.join(args)} : {type}"
    if doc is not None:
        prettified = f"/-- {doc.strip()} -/\n" + prettified
    return prettified

def get_embeddings(texts, model="text-embedding-3-large"):
    assert len(texts) <= 8191
    return np.array([
        response.embedding
        for response in client.embeddings.create(input=texts, model=model).data
    ], dtype=np.float32)

def chunk(s: list, chunk_size: int):
    for i in tqdm.trange(0, len(s), chunk_size):
        yield s[i : i + chunk_size]

def num_tokens(text: str, encoding_name: str = "cl100k_base"):
    encoding = tiktoken.get_encoding(encoding_name)
    return len(encoding.encode(text))

declarations = []
declarations_dir = "Examples/Mathlib/Declarations"
for json_file in sorted(os.listdir(declarations_dir)):
   if json_file.endswith(".jsonl"):
        with open(os.path.join(declarations_dir, json_file)) as f:
            for line in f:
                declarations.append(json.loads(line))

print(f"Embedding {len(declarations)} declarations")

# names = []
# embeddings = np.zeros((0, EMBEDDING_SIZE))

for d in declarations:
    # if this fails, consider trimming the doc?
    assert num_tokens(prettify_declaration(d)) <= 8191

client = OpenAI()

os.makedirs("embeddings", exist_ok=True)

for i, batch_declarations in enumerate(chunk(declarations, BATCH_SIZE)):
    save_file = f"embeddings/batch_{i}.npz"
    if os.path.isfile(save_file):
        continue
    batch_names = [d["name"] for d in batch_declarations]
    batch_embeddings = get_embeddings([prettify_declaration(d) for d in batch_declarations])
    # names.extend(batch_names)
    # embeddings = np.concatenate([embeddings, batch_embeddings], axis=0)
    np.savez(save_file, names=batch_names, embeddings=batch_embeddings)

if not os.path.isfile("embeddings/embeddings.npz"):
    print("Collating results")
    names = []
    embeddings = np.zeros((len(declarations), EMBEDDING_SIZE), dtype=np.float32)
    for i, _ in enumerate(chunk(declarations, BATCH_SIZE)):
        save_file = f"embeddings/batch_{i}.npz"
        batch = np.load(save_file)
        names.extend(batch["names"])
        embeddings[i * BATCH_SIZE : (i + 1) * BATCH_SIZE] = batch["embeddings"]
    np.savez("embeddings/embeddings.npz", names=names, embeddings=embeddings)

print(f"Saved to embeddings/embeddings.npz")

def retrieve(text, topk=5):
    text_embedding = get_embeddings([text])[0]
    scores = embeddings @ text_embedding
    topk_indices = scores.argsort()[-topk:][::-1]
    topk_scores = scores[topk_indices]
    topk_names = [names[i] for i in topk_indices]
    return list(zip(topk_scores, topk_names))
