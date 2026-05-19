import csv
import sys
from collections import defaultdict
from pathlib import Path

import matplotlib.pyplot as plt


path = sys.argv[1] if len(sys.argv) > 1 else "benchmarks/results/raw/quick.csv"

with open(path, newline="") as f:
    rows = list(csv.DictReader(f))


def as_bool(value):
    return str(value).strip().lower() == "true"


def as_float(value):
    try:
        return float(value)
    except Exception:
        return 0.0


def as_int(value):
    try:
        return int(float(value))
    except Exception:
        return None


def row_name(row):
    return row.get("name", "unknown")


def runtime(row):
    return as_float(row.get("time_ms", "0"))


def ensure_plot_dir():
    outdir = Path("benchmarks/results/plots")
    outdir.mkdir(parents=True, exist_ok=True)
    return outdir


by_logic = defaultdict(list)
for row in rows:
    by_logic[row["logic"]].append(row)

print(f"file={path}")
print(f"total_cases={len(rows)}")
print()

summary_rows = []

for logic, logic_rows in sorted(by_logic.items()):
    times = [runtime(row) for row in logic_rows]

    passed = sum(1 for row in logic_rows if as_bool(row.get("passed", "")))
    stable = sum(1 for row in logic_rows if as_bool(row.get("stable", "")))
    expected_true = sum(1 for row in logic_rows if as_bool(row.get("expected", "")))
    expected_false = len(logic_rows) - expected_true

    avg = sum(times) / len(times)
    max_time = max(times)
    slowest = max(logic_rows, key=runtime)

    summary_rows.append(
        {
            "logic": logic,
            "cases": len(logic_rows),
            "passed": passed,
            "stable": stable,
            "expected_true": expected_true,
            "expected_false": expected_false,
            "avg_time_ms": avg,
            "max_time_ms": max_time,
            "slowest": row_name(slowest),
            "slowest_time_ms": runtime(slowest),
        }
    )

    print(
        f"{logic:14s} "
        f"cases={len(logic_rows):3d} "
        f"passed={passed:3d}/{len(logic_rows):3d} "
        f"stable={stable:3d}/{len(logic_rows):3d} "
        f"true={expected_true:3d} "
        f"false={expected_false:3d} "
        f"avg_time_ms={avg:.3f} "
        f"max_time_ms={max_time:.3f}"
    )
    print(
        f"{'':14s} "
        f"slowest={row_name(slowest)} "
        f"time_ms={runtime(slowest):.3f}"
    )

failed_rows = [row for row in rows if not as_bool(row.get("passed", ""))]
unstable_rows = [row for row in rows if not as_bool(row.get("stable", ""))]

if failed_rows:
    print()
    print("FAILED CASES")
    for row in failed_rows:
        print(
            row_name(row),
            "logic=" + row.get("logic", "unknown"),
            "expected=" + row.get("expected", ""),
            "result=" + row.get("result", ""),
            "time_ms=" + row.get("time_ms", ""),
        )

if unstable_rows:
    print()
    print("UNSTABLE CASES")
    for row in unstable_rows:
        print(
            row_name(row),
            "logic=" + row.get("logic", "unknown"),
            "stable=" + row.get("stable", ""),
        )


outdir = ensure_plot_dir()

# Write a compact CSV summary.
summary_path = outdir / "summary.csv"
with open(summary_path, "w", newline="") as f:
    fieldnames = [
        "logic",
        "cases",
        "passed",
        "stable",
        "expected_true",
        "expected_false",
        "avg_time_ms",
        "max_time_ms",
        "slowest",
        "slowest_time_ms",
    ]
    writer = csv.DictWriter(f, fieldnames=fieldnames)
    writer.writeheader()
    for row in summary_rows:
        writer.writerow(row)

# Plot 1: average runtime by logic.
labels = [row["logic"] for row in summary_rows]
avg_times = [row["avg_time_ms"] for row in summary_rows]

plt.figure(figsize=(8, 5))
plt.bar(labels, avg_times)
plt.ylabel("Average runtime (ms)")
plt.xlabel("Logic")
plt.title("Average Runtime by Logic")
plt.xticks(rotation=25, ha="right")
plt.tight_layout()
plt.savefig(outdir / "runtime_by_logic.png", dpi=200)
plt.close()

# Plot 2: maximum runtime by logic.
max_times = [row["max_time_ms"] for row in summary_rows]

plt.figure(figsize=(8, 5))
plt.bar(labels, max_times)
plt.ylabel("Maximum runtime (ms)")
plt.xlabel("Logic")
plt.title("Maximum Runtime by Logic")
plt.xticks(rotation=25, ha="right")
plt.tight_layout()
plt.savefig(outdir / "max_runtime_by_logic.png", dpi=200)
plt.close()

# Plot 3: pass/stable summary by logic.
passed_counts = [row["passed"] for row in summary_rows]
case_counts = [row["cases"] for row in summary_rows]
failed_counts = [case_counts[i] - passed_counts[i] for i in range(len(labels))]

plt.figure(figsize=(8, 5))
plt.bar(labels, passed_counts, label="passed")
plt.bar(labels, failed_counts, bottom=passed_counts, label="failed")
plt.ylabel("Number of cases")
plt.xlabel("Logic")
plt.title("Passed vs Failed Cases")
plt.xticks(rotation=25, ha="right")
plt.legend()
plt.tight_layout()
plt.savefig(outdir / "passed_failed_by_logic.png", dpi=200)
plt.close()

# Plot 4: BasicKH runtime by number of states, if available.
basic_rows = [row for row in rows if row.get("logic") == "basic"]
points = []
for row in basic_rows:
    states = as_int(row.get("states", ""))
    if states is not None:
        points.append((states, runtime(row), row_name(row)))

if points:
    grouped = defaultdict(list)
    for states, time_ms, _ in points:
        grouped[states].append(time_ms)

    xs = sorted(grouped)
    ys = [sum(grouped[x]) / len(grouped[x]) for x in xs]

    plt.figure(figsize=(8, 5))
    plt.plot(xs, ys, marker="o")
    plt.ylabel("Average runtime (ms)")
    plt.xlabel("Number of states")
    plt.title("BasicKH Runtime by Number of States")
    plt.tight_layout()
    plt.savefig(outdir / "basic_runtime_by_states.png", dpi=200)
    plt.close()

# Plot 5: runtime scatter by case.
sorted_rows = sorted(rows, key=runtime, reverse=True)
top_rows = sorted_rows[:20]

plt.figure(figsize=(10, 6))
plt.barh([row_name(row) for row in reversed(top_rows)], [runtime(row) for row in reversed(top_rows)])
plt.xlabel("Runtime (ms)")
plt.title("Top 20 Slowest Benchmark Cases")
plt.tight_layout()
plt.savefig(outdir / "top_slowest_cases.png", dpi=200)
plt.close()

print()
print(f"summary written to {summary_path}")
print(f"plots written to {outdir}")
print("generated:")
print(f"- {outdir / 'runtime_by_logic.png'}")
print(f"- {outdir / 'max_runtime_by_logic.png'}")
print(f"- {outdir / 'passed_failed_by_logic.png'}")
print(f"- {outdir / 'basic_runtime_by_states.png'}")
print(f"- {outdir / 'top_slowest_cases.png'}")