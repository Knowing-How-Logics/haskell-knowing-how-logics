import csv
import sys
from collections import defaultdict

path = sys.argv[1] if len(sys.argv) > 1 else "benchmarks/results/raw/quick.csv"
rows = list(csv.DictReader(open(path, newline="")))
by_logic = defaultdict(list)
for row in rows:
    by_logic[row["logic"]].append(float(row["time_ms"]))

for logic, times in sorted(by_logic.items()):
    avg = sum(times) / len(times)
    print(f"{logic:14s} cases={len(times):3d} avg_time_ms={avg:.3f} max_time_ms={max(times):.3f}")
