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


def row_name(row):
    return row.get("name", "unknown")


def runtime(row):
    return as_float(row.get("time_ms", "0"))


def ensure_plot_dir():
    outdir = Path("benchmarks/results/plots")
    outdir.mkdir(parents=True, exist_ok=True)
    return outdir


def group_by(rows_, key):
    grouped = defaultdict(list)
    for row in rows_:
        grouped[key(row)].append(row)
    return grouped


def is_rescue_row(row):
    text = " ".join(
        [
            row.get("name", ""),
            row.get("family", ""),
            row.get("purpose", ""),
            row.get("parameter_value", ""),
        ]
    ).lower()
    return "rescue" in text


def correctness_key(row):
    expected = as_bool(row.get("expected", ""))
    result = as_bool(row.get("result", ""))

    if expected and result:
        return "TT"
    if expected and not result:
        return "TF"
    if (not expected) and result:
        return "FT"
    return "FF"


def correctness_label(key):
    return {
        "TT": "expected True / result True",
        "TF": "expected True / result False",
        "FT": "expected False / result True",
        "FF": "expected False / result False",
    }[key]


def write_csv(path_, fieldnames, data_rows):
    with open(path_, "w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        for row in data_rows:
            writer.writerow({field: row.get(field, "") for field in fieldnames})


def plot_correctness_overall(rows_, outdir):
    keys = ["TT", "TF", "FT", "FF"]
    values = [
        sum(1 for row in rows_ if correctness_key(row) == key)
        for key in keys
    ]

    plt.figure(figsize=(8, 5))
    plt.bar([correctness_label(key) for key in keys], values)
    plt.ylabel("Number of cases")
    plt.xlabel("Expected / actual result")
    plt.title("Overall Correctness: Expected vs Actual Result")
    plt.xticks(rotation=25, ha="right")
    plt.tight_layout()
    plt.savefig(outdir / "correctness_overall.png", dpi=200)
    plt.close()


def plot_correctness_by_logic(rows_, outdir):
    by_logic = group_by(rows_, lambda row: row.get("logic", "unknown"))
    logic_labels = sorted(by_logic)

    passed = []
    failed = []

    for logic in logic_labels:
        logic_rows = by_logic[logic]
        pass_count = sum(
            1
            for row in logic_rows
            if correctness_key(row) in ("TT", "FF")
        )
        passed.append(pass_count)
        failed.append(len(logic_rows) - pass_count)

    plt.figure(figsize=(8, 5))
    plt.bar(logic_labels, passed, label="passed")
    plt.bar(logic_labels, failed, bottom=passed, label="failed")
    plt.ylabel("Number of cases")
    plt.xlabel("Logic")
    plt.title("Correctness by Logic")
    plt.xticks(rotation=25, ha="right")
    plt.legend()
    plt.tight_layout()
    plt.savefig(outdir / "correctness_by_logic.png", dpi=200)
    plt.close()


def plot_positive_negative_coverage(rows_, outdir):
    by_logic = group_by(rows_, lambda row: row.get("logic", "unknown"))
    logic_labels = sorted(by_logic)

    positive = []
    negative = []

    for logic in logic_labels:
        logic_rows = by_logic[logic]
        pos = sum(1 for row in logic_rows if as_bool(row.get("expected", "")))
        positive.append(pos)
        negative.append(len(logic_rows) - pos)

    plt.figure(figsize=(8, 5))
    plt.bar(logic_labels, positive, label="expected True")
    plt.bar(logic_labels, negative, bottom=positive, label="expected False")
    plt.ylabel("Number of cases")
    plt.xlabel("Logic")
    plt.title("Positive and Negative Test Coverage by Logic")
    plt.xticks(rotation=25, ha="right")
    plt.legend()
    plt.tight_layout()
    plt.savefig(outdir / "positive_negative_coverage_by_logic.png", dpi=200)
    plt.close()


def plot_witness_found_positive(rows_, outdir):
    positive_rows = [row for row in rows_ if as_bool(row.get("expected", ""))]
    by_logic = group_by(positive_rows, lambda row: row.get("logic", "unknown"))
    logic_labels = sorted(by_logic)

    found = []
    missing = []

    for logic in logic_labels:
        logic_rows = by_logic[logic]
        found_count = sum(
            1 for row in logic_rows
            if as_bool(row.get("witness_found", ""))
        )
        found.append(found_count)
        missing.append(len(logic_rows) - found_count)

    plt.figure(figsize=(8, 5))
    plt.bar(logic_labels, found, label="witness found")
    plt.bar(logic_labels, missing, bottom=found, label="missing")
    plt.ylabel("Number of expected-true cases")
    plt.xlabel("Logic")
    plt.title("Witness Found on Expected-True Cases")
    plt.xticks(rotation=25, ha="right")
    plt.legend()
    plt.tight_layout()
    plt.savefig(outdir / "witness_found_positive_cases_by_logic.png", dpi=200)
    plt.close()


def plot_runtime_by_logic(rows_, outdir):
    by_logic = group_by(rows_, lambda row: row.get("logic", "unknown"))
    logic_labels = sorted(by_logic)

    avg_times = [
        sum(runtime(row) for row in by_logic[logic]) / len(by_logic[logic])
        for logic in logic_labels
    ]

    max_times = [
        max(runtime(row) for row in by_logic[logic])
        for logic in logic_labels
    ]

    plt.figure(figsize=(8, 5))
    plt.bar(logic_labels, avg_times)
    plt.ylabel("Average runtime (ms)")
    plt.xlabel("Logic")
    plt.title("Average Runtime by Logic")
    plt.xticks(rotation=25, ha="right")
    plt.tight_layout()
    plt.savefig(outdir / "runtime_by_logic.png", dpi=200)
    plt.close()

    plt.figure(figsize=(8, 5))
    plt.bar(logic_labels, max_times)
    plt.ylabel("Maximum runtime (ms)")
    plt.xlabel("Logic")
    plt.title("Maximum Runtime by Logic")
    plt.xticks(rotation=25, ha="right")
    plt.tight_layout()
    plt.savefig(outdir / "max_runtime_by_logic.png", dpi=200)
    plt.close()


def plot_top_slowest(rows_, outdir):
    top_rows = sorted(rows_, key=runtime, reverse=True)[:20]

    plt.figure(figsize=(10, 6))
    plt.barh(
        [row_name(row) for row in reversed(top_rows)],
        [runtime(row) for row in reversed(top_rows)],
    )
    plt.xlabel("Runtime (ms)")
    plt.title("Top 20 Slowest Benchmark Cases")
    plt.tight_layout()
    plt.savefig(outdir / "top_slowest_cases.png", dpi=200)
    plt.close()


def plot_rescue_coverage(rescue_rows, outdir):
    by_logic = group_by(rescue_rows, lambda row: row.get("logic", "unknown"))
    logic_labels = sorted(by_logic)

    positive = []
    negative = []

    for logic in logic_labels:
        logic_rows = by_logic[logic]
        pos = sum(1 for row in logic_rows if as_bool(row.get("expected", "")))
        positive.append(pos)
        negative.append(len(logic_rows) - pos)

    plt.figure(figsize=(8, 5))
    plt.bar(logic_labels, positive, label="expected True")
    plt.bar(logic_labels, negative, bottom=positive, label="expected False")
    plt.ylabel("Number of rescue cases")
    plt.xlabel("Logic")
    plt.title("Rescue Coverage: Positive and Negative Cases")
    plt.xticks(rotation=25, ha="right")
    plt.legend()
    plt.tight_layout()
    plt.savefig(outdir / "rescue_positive_negative_coverage.png", dpi=200)
    plt.close()


def plot_rescue_runtime_by_logic(rescue_rows, outdir):
    by_logic = group_by(rescue_rows, lambda row: row.get("logic", "unknown"))
    logic_labels = sorted(by_logic)

    avg_times = [
        sum(runtime(row) for row in by_logic[logic]) / len(by_logic[logic])
        for logic in logic_labels
    ]

    plt.figure(figsize=(8, 5))
    plt.bar(logic_labels, avg_times)
    plt.ylabel("Average runtime (ms)")
    plt.xlabel("Logic")
    plt.title("Rescue Runtime by Logic")
    plt.xticks(rotation=25, ha="right")
    plt.tight_layout()
    plt.savefig(outdir / "rescue_runtime_by_logic.png", dpi=200)
    plt.close()


outdir = ensure_plot_dir()

by_logic = group_by(rows, lambda row: row.get("logic", "unknown"))
logic_labels = sorted(by_logic)

print(f"file={path}")
print(f"total_cases={len(rows)}")
print()

summary_rows = []

for logic in logic_labels:
    logic_rows = by_logic[logic]
    times = [runtime(row) for row in logic_rows]

    tt = sum(1 for row in logic_rows if correctness_key(row) == "TT")
    tf = sum(1 for row in logic_rows if correctness_key(row) == "TF")
    ft = sum(1 for row in logic_rows if correctness_key(row) == "FT")
    ff = sum(1 for row in logic_rows if correctness_key(row) == "FF")

    passed = tt + ff
    failed = tf + ft
    stable = sum(1 for row in logic_rows if as_bool(row.get("stable", "")))
    slowest = max(logic_rows, key=runtime)

    summary_rows.append(
        {
            "logic": logic,
            "cases": len(logic_rows),
            "expected_true_result_true": tt,
            "expected_true_result_false": tf,
            "expected_false_result_true": ft,
            "expected_false_result_false": ff,
            "passed": passed,
            "failed": failed,
            "stable": stable,
            "unstable": len(logic_rows) - stable,
            "avg_time_ms": sum(times) / len(times),
            "max_time_ms": max(times),
            "slowest": row_name(slowest),
            "slowest_time_ms": runtime(slowest),
        }
    )

    print(
        f"{logic:14s} "
        f"cases={len(logic_rows):3d} "
        f"TT={tt:3d} "
        f"TF={tf:3d} "
        f"FT={ft:3d} "
        f"FF={ff:3d} "
        f"passed={passed:3d}/{len(logic_rows):3d} "
        f"avg_time_ms={sum(times) / len(times):.3f} "
        f"max_time_ms={max(times):.3f}"
    )
    print(
        f"{'':14s} "
        f"slowest={row_name(slowest)} "
        f"time_ms={runtime(slowest):.3f}"
    )


summary_path = outdir / "summary.csv"
summary_fields = [
    "logic",
    "cases",
    "expected_true_result_true",
    "expected_true_result_false",
    "expected_false_result_true",
    "expected_false_result_false",
    "passed",
    "failed",
    "stable",
    "unstable",
    "avg_time_ms",
    "max_time_ms",
    "slowest",
    "slowest_time_ms",
]

with open(summary_path, "w", newline="") as f:
    writer = csv.DictWriter(f, fieldnames=summary_fields)
    writer.writeheader()
    for row in summary_rows:
        writer.writerow(row)


family_groups = group_by(
    rows,
    lambda row: (row.get("logic", "unknown"), row.get("family", "unknown")),
)

family_summary_rows = []

for (logic, family), family_rows in sorted(family_groups.items()):
    tt = sum(1 for row in family_rows if correctness_key(row) == "TT")
    tf = sum(1 for row in family_rows if correctness_key(row) == "TF")
    ft = sum(1 for row in family_rows if correctness_key(row) == "FT")
    ff = sum(1 for row in family_rows if correctness_key(row) == "FF")
    times = [runtime(row) for row in family_rows]
    slowest = max(family_rows, key=runtime)

    family_summary_rows.append(
        {
            "logic": logic,
            "family": family,
            "cases": len(family_rows),
            "expected_true_result_true": tt,
            "expected_true_result_false": tf,
            "expected_false_result_true": ft,
            "expected_false_result_false": ff,
            "passed": tt + ff,
            "failed": tf + ft,
            "avg_time_ms": sum(times) / len(times),
            "max_time_ms": max(times),
            "slowest": row_name(slowest),
            "slowest_time_ms": runtime(slowest),
        }
    )

family_summary_path = outdir / "family_summary.csv"
family_fields = [
    "logic",
    "family",
    "cases",
    "expected_true_result_true",
    "expected_true_result_false",
    "expected_false_result_true",
    "expected_false_result_false",
    "passed",
    "failed",
    "avg_time_ms",
    "max_time_ms",
    "slowest",
    "slowest_time_ms",
]

with open(family_summary_path, "w", newline="") as f:
    writer = csv.DictWriter(f, fieldnames=family_fields)
    writer.writeheader()
    for row in family_summary_rows:
        writer.writerow(row)


plot_correctness_overall(rows, outdir)
plot_correctness_by_logic(rows, outdir)
plot_positive_negative_coverage(rows, outdir)
plot_witness_found_positive(rows, outdir)
plot_runtime_by_logic(rows, outdir)
plot_top_slowest(rows, outdir)


rescue_rows = [row for row in rows if is_rescue_row(row)]
rescue_summary_path = outdir / "rescue_summary.csv"

if rescue_rows:
    rescue_fields = [
        "name",
        "logic",
        "family",
        "expected",
        "result",
        "passed",
        "stable",
        "ordinary_reachable",
        "ordinary_all_pre_reachable",
        "witness_found",
        "witness_size",
        "expected_witness_size",
        "witness_size_passed",
        "budget_dimension",
        "time_ms",
    ]

    write_csv(
        rescue_summary_path,
        rescue_fields,
        sorted(rescue_rows, key=lambda r: (r.get("logic", ""), row_name(r))),
    )

    plot_rescue_coverage(rescue_rows, outdir)
    plot_rescue_runtime_by_logic(rescue_rows, outdir)


print()
print(f"summary written to {summary_path}")
print(f"family summary written to {family_summary_path}")
if rescue_rows:
    print(f"rescue summary written to {rescue_summary_path}")
print(f"plots written to {outdir}")
print("generated:")
print(f"- {outdir / 'correctness_overall.png'}")
print(f"- {outdir / 'correctness_by_logic.png'}")
print(f"- {outdir / 'positive_negative_coverage_by_logic.png'}")
print(f"- {outdir / 'witness_found_positive_cases_by_logic.png'}")
print(f"- {outdir / 'runtime_by_logic.png'}")
print(f"- {outdir / 'max_runtime_by_logic.png'}")
print(f"- {outdir / 'top_slowest_cases.png'}")
if rescue_rows:
    print(f"- {outdir / 'rescue_positive_negative_coverage.png'}")
    print(f"- {outdir / 'rescue_runtime_by_logic.png'}")
    print(f"- {rescue_summary_path}")