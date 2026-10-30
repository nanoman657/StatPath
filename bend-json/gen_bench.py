# Writes bench.json (~1 MB): an array of records mixing every JSON type,
# non-ASCII text, escapes, big integers and small fractions.
#   python3 gen_bench.py && bend bench.bend bench.json
import json, random

random.seed(7)
items = []
while len(items) % 200 or len(json.dumps(items)) <= 1_000_000:
    i = len(items)
    items.append({"id": i, "name": f"user_{i} é ☃", "score": round(random.uniform(-1000, 1000), 3),
                  "big": random.randint(10**20, 10**25), "ratio": random.random() / 1e5,
                  "active": i % 3 == 0, "tags": ["alpha", "beta", "gamma"][: i % 4],
                  "nested": {"x": [1, 2, 3, i], "y": None, "z": {"deep": [True, False]}},
                  "text": "line one\nline \"two\"\t\\ end"})
with open("bench.json", "w", encoding="utf-8") as f:
    f.write(json.dumps(items, ensure_ascii=False))
