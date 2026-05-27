import csv
import sys
from collections import defaultdict
from pathlib import Path

import matplotlib.pyplot as plt


CSV_PATH = sys.argv[1] if len(sys.argv) > 1 else "benchmarks/results/raw/quick.csv"
OUTDIR = Path("benchmarks/results/plots")


MAIN_PARAMETERS = {
    "basic": {
        "states",
        "actions",
        "path_length",
        "width",
        "pre_states",
    },
    "intermediate": {
        "states",
        "depth",
        "width",
        "pre_states",
    },
    "regular": {
        "states",
        "path_length",
        "width",
        "depth",
        "automata_count",
        "class_size",
    },
    "budget": {
        "states",
        "budget_dimension",
    },
}

PARAMETER_ALIASES = {
    "automata": "automata_count",
    "budget_dim": "budget_dimension",
    "branching_width": "width",
    "language_depth": "depth",
    "automata_states": "automaton_states",
}

IGNORED_PARAMETERS = {
    "",
    "NA",
    "semantic-case",
    "case-study",
    "formula_depth",
    "cost_per_step",
    "budget",
    "second_budget",
    "automaton_states",
    "agents",
}


def read_rows(path):
    with open(path, newline="") as f:
        return list(csv.DictReader(f))


def as_bool(value):
    return str(value).strip().lower() == "true"


def as_float(value):
    try:
        return float(value)
    except Exception:
        return 0.0


def numeric_value(value):
    try:
        return float(value)
    except Exception:
        return None


def row_name(row):
    return row.get("name", "unknown")


def runtime(row):
    return as_float(row.get("time_ms", "0"))


def canonical_parameter(parameter):
    return PARAMETER_ALIASES.get(parameter, parameter)


def group_by(rows, key):
    grouped = defaultdict(list)
    for row in rows:
        grouped[key(row)].append(row)
    return grouped


def ensure_plot_dir():
    OUTDIR.mkdir(parents=True, exist_ok=True)
    return OUTDIR


def write_csv(path, fieldnames, rows):
    with open(path, "w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            writer.writerow({field: row.get(field, "") for field in fieldnames})


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


def safe_name(text):
    return (
        text.replace("/", "_")
        .replace(" ", "_")
        .replace("-", "_")
        .replace("__", "_")
    )


def family_label(family):
    return family.replace("_", "-")


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


def collect_main_scaling_series(rows):
    series = []

    grouped = group_by(
        rows,
        lambda row: (
            row.get("logic", "unknown"),
            canonical_parameter(row.get("primary_parameter", "")),
            row.get("family", "unknown"),
        ),
    )

    for (logic, parameter, family), group_rows in sorted(grouped.items()):
        if parameter in IGNORED_PARAMETERS:
            continue
        if parameter not in MAIN_PARAMETERS.get(logic, set()):
            continue

        by_value = group_by(group_rows, lambda row: row.get("parameter_value", ""))
        points = []

        for value, value_rows in by_value.items():
            x = numeric_value(value)
            if x is None:
                continue

            avg_runtime = sum(runtime(row) for row in value_rows) / len(value_rows)
            points.append((x, avg_runtime, len(value_rows)))

        points.sort(key=lambda item: item[0])

        if len(points) >= 2:
            series.append(
                {
                    "logic": logic,
                    "parameter": parameter,
                    "family": family,
                    "points": points,
                }
            )

    return series


def write_series_csv(series, path):
    rows = []
    for item in series:
        for x, y, n in item["points"]:
            rows.append(
                {
                    "logic": item["logic"],
                    "parameter": item["parameter"],
                    "family": item["family"],
                    "parameter_value": x,
                    "avg_time_ms": y,
                    "cases": n,
                }
            )

    fields = [
        "logic",
        "parameter",
        "family",
        "parameter_value",
        "avg_time_ms",
        "cases",
    ]
    write_csv(path, fields, rows)


def plot_overall_correctness(rows, outdir):
    keys = ["TT", "TF", "FT", "FF"]
    values = [sum(1 for row in rows if correctness_key(row) == key) for key in keys]

    plt.figure(figsize=(8, 5))
    plt.bar([correctness_label(key) for key in keys], values)
    plt.ylabel("Number of cases")
    plt.xlabel("Expected / actual result")
    plt.title("Overall correctness")
    plt.xticks(rotation=25, ha="right")
    plt.tight_layout()

    outpath = outdir / "correctness_overall.png"
    plt.savefig(outpath, dpi=200)
    plt.close()
    return outpath


def plot_correctness_by_logic(rows, outdir):
    by_logic = group_by(rows, lambda row: row.get("logic", "unknown"))
    logic_labels = sorted(by_logic)

    passed = []
    failed = []

    for logic in logic_labels:
        logic_rows = by_logic[logic]
        passed_count = sum(1 for row in logic_rows if correctness_key(row) in ("TT", "FF"))
        passed.append(passed_count)
        failed.append(len(logic_rows) - passed_count)

    plt.figure(figsize=(8, 5))
    plt.bar(logic_labels, passed, label="passed")
    plt.bar(logic_labels, failed, bottom=passed, label="failed")
    plt.ylabel("Number of cases")
    plt.xlabel("Logic")
    plt.title("Correctness by logic")
    plt.xticks(rotation=25, ha="right")
    plt.legend()
    plt.tight_layout()

    outpath = outdir / "correctness_by_logic.png"
    plt.savefig(outpath, dpi=200)
    plt.close()
    return outpath


def plot_coverage_by_logic(rows, outdir):
    by_logic = group_by(rows, lambda row: row.get("logic", "unknown"))
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
    plt.title("Positive/negative coverage by logic")
    plt.xticks(rotation=25, ha="right")
    plt.legend()
    plt.tight_layout()

    outpath = outdir / "positive_negative_coverage_by_logic.png"
    plt.savefig(outpath, dpi=200)
    plt.close()
    return outpath


def plot_runtime_by_logic(rows, outdir):
    by_logic = group_by(rows, lambda row: row.get("logic", "unknown"))
    logic_labels = sorted(by_logic)

    avg_times = [
        sum(runtime(row) for row in by_logic[logic]) / len(by_logic[logic])
        for logic in logic_labels
    ]

    max_times = [
        max(runtime(row) for row in by_logic[logic])
        for logic in logic_labels
    ]

    paths = []

    plt.figure(figsize=(8, 5))
    plt.bar(logic_labels, avg_times)
    plt.ylabel("Average runtime (ms)")
    plt.xlabel("Logic")
    plt.title("Average runtime by logic")
    plt.xticks(rotation=25, ha="right")
    plt.tight_layout()

    outpath = outdir / "runtime_by_logic.png"
    plt.savefig(outpath, dpi=200)
    plt.close()
    paths.append(outpath)

    plt.figure(figsize=(8, 5))
    plt.bar(logic_labels, max_times)
    plt.ylabel("Maximum runtime (ms)")
    plt.xlabel("Logic")
    plt.title("Maximum runtime by logic")
    plt.xticks(rotation=25, ha="right")
    plt.tight_layout()

    outpath = outdir / "max_runtime_by_logic.png"
    plt.savefig(outpath, dpi=200)
    plt.close()
    paths.append(outpath)

    return paths


def plot_top_slowest(rows, outdir):
    top_rows = sorted(rows, key=runtime, reverse=True)[:20]

    plt.figure(figsize=(10, 6))
    plt.barh(
        [row_name(row) for row in reversed(top_rows)],
        [runtime(row) for row in reversed(top_rows)],
    )
    plt.xlabel("Runtime (ms)")
    plt.title("Top 20 slowest benchmark cases")
    plt.tight_layout()

    outpath = outdir / "top_slowest_cases.png"
    plt.savefig(outpath, dpi=200)
    plt.close()
    return outpath


def plot_main_scaling(series, outdir):
    paths = []
    by_logic_parameter = group_by(
        series,
        lambda item: (item["logic"], item["parameter"]),
    )

    for (logic, parameter), items in sorted(by_logic_parameter.items()):
        plt.figure(figsize=(9, 5))

        for item in items:
            xs = [x for x, _, _ in item["points"]]
            ys = [y for _, y, _ in item["points"]]
            plt.plot(xs, ys, marker="o", label=family_label(item["family"]))

        plt.xlabel(parameter)
        plt.ylabel("Average runtime (ms)")
        plt.title(f"{logic}: runtime by {parameter}")
        plt.legend(fontsize=8)
        plt.tight_layout()

        outpath = outdir / f"main_runtime_{logic}_by_{safe_name(parameter)}.png"
        plt.savefig(outpath, dpi=200)
        plt.close()
        paths.append(outpath)

    return paths


def normalize_points(points):
    xs = [x for x, _, _ in points]
    lo = min(xs)
    hi = max(xs)

    if hi == lo:
        return [(0.0, y) for _, y, _ in points]

    return [((x - lo) / (hi - lo), y) for x, y, _ in points]


def plot_main_parameter_comparison(main_series, outdir):
    paths = []
    by_logic = group_by(main_series, lambda item: item["logic"])

    for logic, items in sorted(by_logic.items()):
        by_parameter = group_by(items, lambda item: item["parameter"])

        plt.figure(figsize=(10, 6))
        plotted = False

        for parameter in sorted(by_parameter):
            value_rows = []

            for item in by_parameter[parameter]:
                value_rows.extend([(x, y, n) for x, y, n in item["points"]])

            by_value = defaultdict(list)
            for x, y, _ in value_rows:
                by_value[x].append(y)

            points = sorted(
                (x, sum(ys) / len(ys), len(ys))
                for x, ys in by_value.items()
            )

            if len(points) < 2:
                continue

            normalized = normalize_points(points)
            xs = [x for x, _ in normalized]
            ys = [y for _, y in normalized]
            plt.plot(xs, ys, marker="o", label=parameter)
            plotted = True

        if not plotted:
            plt.close()
            continue

        plt.xlabel("Normalized parameter value")
        plt.ylabel("Average runtime (ms)")
        plt.title(f"{logic}: main scaling parameters")
        plt.legend(fontsize=8)
        plt.tight_layout()

        outpath = outdir / f"main_runtime_{logic}_parameter_comparison.png"
        plt.savefig(outpath, dpi=200)
        plt.close()
        paths.append(outpath)

    return paths


def write_summary(rows, outdir):
    by_logic = group_by(rows, lambda row: row.get("logic", "unknown"))
    summary_rows = []

    print(f"file={CSV_PATH}")
    print(f"total_cases={len(rows)}")
    print()

    for logic in sorted(by_logic):
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
            f"avg_time_ms={sum(times) / len(times):.6f} "
            f"max_time_ms={max(times):.6f}"
        )
        print(
            f"{'':14s} "
            f"slowest={row_name(slowest)} "
            f"time_ms={runtime(slowest):.6f}"
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
    write_csv(summary_path, summary_fields, summary_rows)

    return summary_path


def write_family_summary(rows, outdir):
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
    write_csv(family_summary_path, family_fields, family_summary_rows)

    return family_summary_path


def write_rescue_summary(rows, outdir):
    rescue_rows = [row for row in rows if is_rescue_row(row)]
    if not rescue_rows:
        return None

    rescue_summary_path = outdir / "rescue_summary.csv"
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

    return rescue_summary_path


def main():
    rows = read_rows(CSV_PATH)
    outdir = ensure_plot_dir()

    summary_path = write_summary(rows, outdir)
    family_summary_path = write_family_summary(rows, outdir)
    rescue_summary_path = write_rescue_summary(rows, outdir)

    generated = []
    generated.append(plot_overall_correctness(rows, outdir))
    generated.append(plot_correctness_by_logic(rows, outdir))
    generated.append(plot_coverage_by_logic(rows, outdir))
    generated.extend(plot_runtime_by_logic(rows, outdir))
    generated.append(plot_top_slowest(rows, outdir))

    main_series = collect_main_scaling_series(rows)

    main_csv = outdir / "main_scaling_series.csv"
    write_series_csv(main_series, main_csv)

    main_plots = plot_main_scaling(main_series, outdir)
    comparison_plots = plot_main_parameter_comparison(main_series, outdir)

    print()
    print(f"summary written to {summary_path}")
    print(f"family summary written to {family_summary_path}")
    if rescue_summary_path:
        print(f"rescue summary written to {rescue_summary_path}")
    print(f"main scaling series written to {main_csv}")
    print(f"plots written to {outdir}")
    print()
    print("generated core plots:")
    for path in generated:
        print(f"- {path}")

    print()
    print("generated main scaling plots:")
    for path in main_plots:
        print(f"- {path}")

    print()
    print("generated main comparison plots:")
    for path in comparison_plots:
        print(f"- {path}")


if __name__ == "__main__":
    main()
