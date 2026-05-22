# KHora Benchmarks

This directory contains the benchmark suite for **KHora**, a Haskell model checker for knowing-how logics.

The benchmarks are designed to test both correctness and scalability of the implemented model-checking algorithms. They cover four parts of the project:

1. `basic`: benchmarks for the basic knowing-how logic `L_Kh`;
2. `regular`: benchmarks for regular-plan knowing-how with uncertainty;
3. `intermediate`: benchmarks for knowing-how with intermediate-state constraints;
4. `budget`: benchmarks for regular-plan knowing-how with scalar and vector budget constraints.

The benchmark suite is not only a timing experiment. It also checks that the expected semantic result is obtained, that repeated measurements are stable, and that important negative cases are genuine semantic separators rather than merely unreachable examples.

---

## Directory structure

The benchmark code is organised as follows.

```text
benchmarks/
  app/
    Main.hs

  src/
    Bench/
      Common.hs
      Basic.hs
      Regular.hs
      Intermediate.hs
      Budget.hs

  check/
    CheckAll.hs
    CheckBasic.hs
    CheckRegular.hs
    CheckIntermediate.hs
    CheckBudget.hs

  results/
    raw/
      quick.csv
      full.csv
```

The main benchmark runner is `benchmarks/app/Main.hs`.

The four benchmark suites are implemented in:

```text
benchmarks/src/Bench/Basic.hs
benchmarks/src/Bench/Regular.hs
benchmarks/src/Bench/Intermediate.hs
benchmarks/src/Bench/Budget.hs
```

The shared benchmark infrastructure is implemented in:

```text
benchmarks/src/Bench/Common.hs
```

The consistency checkers are implemented in:

```text
benchmarks/check/CheckAll.hs
benchmarks/check/CheckBasic.hs
benchmarks/check/CheckRegular.hs
benchmarks/check/CheckIntermediate.hs
benchmarks/check/CheckBudget.hs
```

---

## What the benchmark runner does

The benchmark runner collects benchmark cases from the four suites:

```text
basic
intermediate
regular
budget
```

Each case records:

- the name of the benchmark case;
- the logic being tested;
- the benchmark family;
- whether the expected semantic result is `True` or `False`;
- model-size information;
- formula-size information;
- witness information, when relevant;
- timing information.

The runner then writes the result to a CSV file.

By default, the output path is:

```text
benchmarks/results/raw/quick.csv
```

for quick mode, and:

```text
benchmarks/results/raw/full.csv
```

for full mode.

---

## Running the benchmarks

### Run all benchmarks in quick mode

```bash
stack run khora-bench -- --quick
```

This writes:

```text
benchmarks/results/raw/quick.csv
```

Quick mode is useful for checking that the benchmark suite still runs after code changes.

---

### Run all benchmarks in full mode

```bash
stack run khora-bench -- --full
```

This writes:

```text
benchmarks/results/raw/full.csv
```

Full mode is the main mode to use before reporting benchmark results.

---

### Run one logic suite

You can run only one logic by using `--suite`.

```bash
stack run khora-bench -- --full --suite basic
```

```bash
stack run khora-bench -- --full --suite intermediate
```

```bash
stack run khora-bench -- --full --suite regular
```

```bash
stack run khora-bench -- --full --suite budget
```

---

### Run one benchmark family

The `--suite` argument can also be a family name.

For example:

```bash
stack run khora-bench -- --full --suite line-positive
```

```bash
stack run khora-bench -- --full --suite formula-depth-positive
```

```bash
stack run khora-bench -- --full --suite trap-reachable-negative
```

```bash
stack run khora-bench -- --full --suite vector-tightness
```

This is useful when developing or debugging one group of benchmarks.

---

### Write the result to a custom file

```bash
stack run khora-bench -- --full --suite regular --out benchmarks/results/raw/regular-full.csv
```

The directory is created automatically if it does not already exist.

---

## Benchmark modes

There are two modes.

### Quick mode

Quick mode uses smaller parameter ranges and fewer samples.

It is intended for development.

```bash
stack run khora-bench -- --quick
```

### Full mode

Full mode uses larger parameter ranges and more samples.

It is intended for final benchmark reporting.

```bash
stack run khora-bench -- --full
```

The timing infrastructure repeats each benchmark case several times and records the median per-iteration time. It also checks whether repeated runs produce the same semantic result.

---

## CSV output format

The output CSV has the following columns.

```text
name,
logic,
family,
mode,
expected,
result,
passed,
stable,
samples,
total_iterations,
min_iterations,
max_iterations,
states,
actions,
transitions,
propositions,
agents,
automata,
automaton_states,
budget_dimension,
formula_size,
purpose,
primary_parameter,
parameter_value,
pre_states,
goal_states,
ordinary_reachable,
ordinary_all_pre_reachable,
witness_found,
witness_size,
expected_witness_size,
witness_size_passed,
time_ms,
min_time_ms,
max_time_ms
```

The most important columns are:

| Column | Meaning |
|---|---|
| `name` | Unique name of the benchmark case. |
| `logic` | One of `basic`, `intermediate`, `regular`, or `budget`. |
| `family` | The benchmark family. This is used for grouped experiments. |
| `mode` | Either `quick` or `full`. |
| `expected` | Expected semantic truth value, when known. |
| `result` | Actual result returned by the model checker. |
| `passed` | Whether `result` agrees with `expected`. |
| `stable` | Whether repeated measurements returned the same outcome. |
| `states` | Number of LTS states. |
| `actions` | Number of actions. |
| `transitions` | Number of transitions. |
| `propositions` | Number of atomic propositions. |
| `agents` | Number of agents, if relevant. |
| `automata` | Number of available automata or plan classes, if relevant. |
| `automaton_states` | Number of automaton states, if relevant. |
| `budget_dimension` | Budget dimension, used by vector-budget benchmarks. |
| `formula_size` | Size of the tested formula. |
| `purpose` | Human-readable description of what the case tests. |
| `primary_parameter` | Main parameter varied by the benchmark. |
| `parameter_value` | Value of the main parameter. |
| `pre_states` | Number of states satisfying the precondition. |
| `goal_states` | Number of states satisfying the goal condition. |
| `ordinary_reachable` | Whether the goal is reachable by ordinary reachability. |
| `ordinary_all_pre_reachable` | Whether all precondition states can ordinarily reach the goal. |
| `witness_found` | Whether the checker found a witnessing plan or automaton. |
| `witness_size` | Size of the witness, when relevant. |
| `expected_witness_size` | Expected witness size, when specified. |
| `witness_size_passed` | Whether the witness size agrees with the expected size. |
| `time_ms` | Median per-iteration running time in milliseconds. |
| `min_time_ms` | Minimum per-iteration running time. |
| `max_time_ms` | Maximum per-iteration running time. |

Missing values are written as:

```text
NA
```

---

## Checking benchmark results

After running benchmarks, use the checker programs to validate the produced CSV file.

### Check all benchmark results

```bash
stack run khora-check-all -- benchmarks/results/raw/full.csv
```

If no path is given, the checker uses:

```text
benchmarks/results/raw/full.csv
```

So the following also works:

```bash
stack run khora-check-all
```

The all-in-one checker verifies that:

- all four logics are present;
- all benchmark rows passed;
- all benchmark rows are stable;
- purpose and parameter fields are present;
- witness-size checks pass where expected witness sizes are provided;
- all required benchmark families are present;
- there are genuine reachability-separator cases;
- vector-budget rows record their budget dimension.

---

### Check only the basic benchmarks

```bash
stack run khora-check-basic -- benchmarks/results/raw/full.csv
```

This checks the rows with:

```text
logic=basic
```

It verifies:

- all basic benchmark rows passed;
- all basic benchmark rows are stable;
- witness-size checks pass where expected witness sizes are provided;
- purpose and parameter fields are present;
- intended reachability separators are ordinary-reachable;
- the multi-start negative case behaves as expected.

---

### Check only the regular benchmarks

```bash
stack run khora-check-regular -- benchmarks/results/raw/full.csv
```

This checks the rows with:

```text
logic=regular
```

It verifies:

- all regular benchmark rows passed;
- all regular benchmark rows are stable;
- purpose and parameter fields are present;
- witness-size checks pass where expected witness sizes are provided;
- all required regular benchmark families are present;
- manual positive and negative cases behave as expected;
- reachability-separator cases are genuine;
- awareness cases behave as expected;
- mixed-class cases behave as expected;
- regular-language width and depth cases behave as expected;
- automaton-only cases behave as expected;
- different agents may have different knowing-how abilities in the same model;
- formula-depth cases behave as expected.

---

### Check only the intermediate benchmarks

```bash
stack run khora-check-intermediate -- benchmarks/results/raw/full.csv
```

This checks the rows with:

```text
logic=intermediate
```

It verifies:

- all intermediate benchmark rows passed;
- all intermediate benchmark rows are stable;
- purpose and parameter fields are present;
- witness-size checks pass where expected witness sizes are provided;
- all required intermediate benchmark families are present;
- manual positive and negative cases behave as expected;
- reachability-separator cases are genuine;
- intermediate-constraint negative cases are not merely unreachable;
- multi-start unsafe cases behave as expected;
- formula-depth cases behave as expected.

---

### Check only the budget benchmarks

```bash
stack run khora-check-budget -- benchmarks/results/raw/full.csv
```

This checks the rows with:

```text
logic=budget
```

It verifies:

- all budget benchmark rows passed;
- all budget benchmark rows are stable;
- purpose and parameter fields are present;
- witness-size checks pass where expected witness sizes are provided;
- all required budget benchmark families are present;
- scalar-budget negative cases behave as expected;
- vector-budget rows record their budget dimension;
- vector-budget negative cases behave as expected;
- formula-depth cases behave as expected.

---

## Recommended workflow

For normal development, use:

```bash
stack run khora-bench -- --quick
```

Then, if the quick run succeeds, run the full benchmark suite:

```bash
stack run khora-bench -- --full
```

Finally, check the full CSV:

```bash
stack run khora-check-all -- benchmarks/results/raw/full.csv
```

A complete final benchmark run is therefore:

```bash
stack run khora-bench -- --full
stack run khora-check-all -- benchmarks/results/raw/full.csv
```

For debugging one suite, use:

```bash
stack run khora-bench -- --full --suite regular --out benchmarks/results/raw/regular-full.csv
stack run khora-check-regular -- benchmarks/results/raw/regular-full.csv
```

For debugging one family, use:

```bash
stack run khora-bench -- --full --suite formula-depth-positive --out benchmarks/results/raw/formula-depth.csv
```

---

## Benchmark suites

## 1. Basic knowing-how benchmarks

The `basic` suite tests the basic knowing-how model checker.

The basic formula has the form:

```text
Kh(pre, goal)
```

Intuitively, it asks whether there is a plan that guarantees reaching a goal state from every state satisfying the precondition.

The basic suite contains:

### Manual semantic cases

These are small hand-written cases testing important semantic corners:

```text
manual-empty-plan
manual-vacuous-precondition
manual-reliable-plan
manual-nondet-success
manual-multistart-success
manual-trap-failure
manual-dead-end-failure
```

They test cases such as:

- empty plans;
- vacuous preconditions;
- reliable deterministic plans;
- nondeterministic but safe plans;
- multi-start preconditions;
- traps;
- dead ends.

### Case studies

```text
robot-corridor-safe-plan
robot-corridor-risky-only
robot-corridor-multistart
```

These are small robot-navigation examples. They are useful because they are easy to explain in a paper or presentation.

### Generated parameter sweeps

```text
line-positive
line-broken-negative
branching-depth-safe-positive
branching-depth-trap-negative
branching-width-safe-positive
branching-width-trap-negative
multi-start-all-good
multi-start-one-bad
action-count-good-last
action-count-no-good
path-length-good-last
path-length-no-good
trap-reachable-negative
formula-depth-positive
```

These families vary parameters such as:

- number of states;
- branching depth;
- branching width;
- number of precondition states;
- number of actions;
- path length;
- formula depth.

The negative cases are important because many of them are still ordinarily reachable. This shows that the benchmark is testing strong executability and guaranteed success, not just graph reachability.

---

## 2. Regular-plan knowing-how benchmarks

The `regular` suite tests knowing-how with regular plans and uncertainty over plan classes.

The regular-plan setting is stricter than ordinary reachability. A plan class is good only when all plans represented by the relevant automaton class are strongly executable and guarantee the goal.

The regular suite contains:

### Manual semantic cases

```text
manual-empty-plan
manual-vacuous-precondition
manual-single-good-class
manual-good-bad-class
manual-not-strongly-executable
manual-unaware-good-action
manual-agent-difference
```

These test:

- empty plans;
- vacuous preconditions;
- a single good regular plan class;
- a class mixing good and bad plans;
- failure of strong executability;
- the difference between the existence of a good action in the LTS and the agent being aware of it;
- different agents having different available plan classes in the same model.

### Case studies

```text
baking-good-method
baking-confused-methods
robot-aware-safe
robot-unaware-safe
```

These cases are intended to make the regular-plan semantics intuitive:

- in the baking examples, the agent may or may not distinguish an adequate method from a bad method;
- in the robot examples, the safe action may exist, but the agent may be unaware of it.

### Generated parameter sweeps

```text
line-positive
line-broken-negative
automaton-only-size-positive
automaton-only-size-negative
class-count-good-last
class-count-no-good
all-good-mixed-class-positive
mixed-class-negative
regular-language-width-positive
regular-language-width-negative
regular-language-depth-positive
regular-language-depth-negative
awareness-positive
basic-capable-unaware-negative
multi-agent-one-knows
multi-agent-last-fails
formula-depth-positive
```

These families vary:

- LTS size;
- automaton size;
- number of available automata;
- size of a plan class;
- width of a regular language;
- depth of a regular language;
- awareness size;
- number of agents;
- formula depth.

The most important negative families are those where the goal is reachable in the underlying LTS, but the agent still does not know how because of uncertainty, unawareness, or unsafe plans inside the same regular class.

---

## 3. Intermediate-constraint benchmarks

The `intermediate` suite tests knowing-how with an intermediate-state constraint.

The formula has the form:

```text
Khm(pre, mid, goal)
```

Intuitively, it asks whether there is a plan that guarantees reaching the goal from every precondition state while keeping all strict intermediate states inside the `mid` condition.

The intermediate suite contains:

### Manual semantic cases

```text
manual-empty-plan
manual-vacuous-precondition
manual-safe-plan
manual-unsafe-middle-failure
manual-nondet-safe-success
manual-nondet-unsafe-failure
manual-multistart-success
manual-multistart-one-bad
manual-dead-end-failure
```

These test:

- empty plans;
- vacuous preconditions;
- safe intermediate states;
- unsafe intermediate states;
- nondeterministic safe and unsafe branches;
- multiple precondition states;
- dead ends.

### Case studies

```text
robot-safe-corridor
robot-unsafe-corridor
robot-risky-branch
```

These are robot-navigation examples where reaching the goal is not enough. The route must also remain safe before the goal is reached.

### Generated parameter sweeps

```text
corridor-positive
corridor-unsafe-middle
corridor-broken
branching-depth-safe
branching-depth-unsafe
branching-width-safe
branching-width-unsafe
multi-start-all-good
multi-start-one-unsafe
action-count-safe-last
action-count-no-safe
path-length-safe-last
path-length-unsafe
formula-depth-positive
```

These families vary:

- corridor length;
- branching depth;
- branching width;
- number of precondition states;
- number of actions;
- path length;
- formula depth.

The important negative cases are those where the goal is ordinarily reachable, but every candidate plan violates the intermediate constraint.

---

## 4. Budget benchmarks

The `budget` suite tests regular-plan knowing-how with budget constraints.

There are two kinds of budget benchmarks:

1. scalar-budget benchmarks;
2. vector-budget benchmarks.

In scalar-budget benchmarks, a plan must fit within one numerical budget.

In vector-budget benchmarks, a plan must fit every component of a resource vector. For example, a robot route may have both time cost and energy cost.

The budget suite contains:

### Manual semantic cases

```text
manual-empty-plan
manual-vacuous-precondition
manual-within-budget
manual-over-budget
manual-unaware-cheap-action
vector-manual-within-budget
vector-manual-first-dim-failure
vector-manual-second-dim-failure
```

These test:

- empty plans;
- vacuous preconditions;
- plans exactly within budget;
- plans over budget;
- cheap actions that exist in the LTS but are not available to the agent;
- vector-budget success;
- failure in the first resource dimension;
- failure in the second resource dimension.

### Case studies

```text
delivery-cheap-route
delivery-expensive-only
robot-time-energy-positive
robot-time-energy-negative
```

These examples are intended to be easy to explain:

- in the delivery examples, the destination may be reachable only by an expensive route;
- in the robot examples, a route may fit the time budget but fail the energy budget.

### Generated parameter sweeps

```text
line-positive
line-over-budget
threshold
cost-per-step-positive
cost-per-step-negative
class-count-good-last
class-count-no-good
vector-line-positive
vector-line-over-budget
vector-dimension-positive
vector-dimension-negative
vector-tightness
formula-depth-positive
```

These families vary:

- number of states;
- budget threshold;
- cost per step;
- number of available plan classes;
- vector-budget path length;
- vector dimension;
- budget tightness;
- formula depth.

The vector-budget cases are important because they test that the checker treats each budget dimension separately. A plan should fail if it exceeds any one dimension, even if it fits all the others.

---

## How to interpret the results

A benchmark row is successful when:

```text
passed=True
stable=True
```

This means:

1. the result agrees with the expected semantic value;
2. repeated measurements returned the same outcome.

For positive cases, usually:

```text
expected=True
result=True
witness_found=True
```

For negative cases, usually:

```text
expected=False
result=False
witness_found=False
```

A negative case is especially useful when:

```text
ordinary_reachable=True
expected=False
result=False
```

This means the goal is reachable in the ordinary graph sense, but the knowing-how formula is still false. These cases demonstrate that the benchmark is testing the intended knowing-how semantics rather than simple reachability.

For vector-budget cases, the column:

```text
budget_dimension
```

should not be `NA`.

---

## Adding a new benchmark case

To add a new benchmark case, add it to the relevant suite:

```text
benchmarks/src/Bench/Basic.hs
benchmarks/src/Bench/Regular.hs
benchmarks/src/Bench/Intermediate.hs
benchmarks/src/Bench/Budget.hs
```

Each benchmark case should have:

- a unique `name`;
- a `family`;
- an expected result;
- a clear purpose string;
- a primary parameter name;
- a parameter value;
- an expected witness size if the witness size is part of the test;
- a model;
- a formula or formula components.

For example, a benchmark case should conceptually contain information like:

```text
name = "basic-line-positive-32"
logic = "basic"
family = "line-positive"
expected = True
purpose = "Linear positive baseline: increasing states also increases the required witness length."
primary_parameter = "states"
parameter_value = "32"
expected_witness_size = Just 31
```

After adding a new benchmark family, also update the corresponding checker:

```text
benchmarks/check/CheckBasic.hs
benchmarks/check/CheckRegular.hs
benchmarks/check/CheckIntermediate.hs
benchmarks/check/CheckBudget.hs
benchmarks/check/CheckAll.hs
```

This is important. Otherwise the new family may run, but the checker will not verify that it is required.

---

## Adding a new benchmark family

When adding a new family, follow this checklist.

### 1. Add the generator

Add a new function in the relevant benchmark file, for example:

```haskell
newFamilyBenchmarks :: BenchMode -> [BenchCase]
newFamilyBenchmarks mode =
  [ -- benchmark cases here
  ]
```

### 2. Include it in `generatedBenchmarks`

For example:

```haskell
generatedBenchmarks :: BenchMode -> [BenchCase]
generatedBenchmarks mode =
  concat
    [ existingFamily1 mode
    , existingFamily2 mode
    , newFamilyBenchmarks mode
    ]
```

### 3. Give every row a clear family name

Use a stable family name such as:

```text
new-family-positive
new-family-negative
```

Do not use only the full benchmark name as the family. The family name is used by `--suite`.

### 4. Add the family to the checker

For example, in the relevant checker:

```haskell
checkRequiredFamilies rows =
  checkRequiredFamilies rows "basic"
    [ "manual-empty-plan"
    , "line-positive"
    , "new-family-positive"
    ]
```

Also add more specific checks if the family is meant to test a special semantic property.

### 5. Run the relevant suite

```bash
stack run khora-bench -- --quick --suite new-family-positive
```

Then run the checker:

```bash
stack run khora-check-all -- benchmarks/results/raw/quick.csv
```

---

## Notes for reporting benchmark results

When reporting the benchmark results in a paper, thesis, or README, it is better not to report every individual row. Instead, group the results by:

```text
logic
family
primary_parameter
parameter_value
time_ms
```

The most useful columns for tables are usually:

```text
logic
family
primary_parameter
parameter_value
states
actions
transitions
automata
automaton_states
budget_dimension
formula_size
result
witness_size
time_ms
```

For correctness discussion, the most useful columns are:

```text
logic
family
expected
result
passed
stable
ordinary_reachable
witness_found
witness_size_passed
```

For scalability discussion, the most useful columns are:

```text
logic
family
primary_parameter
parameter_value
states
transitions
automata
automaton_states
formula_size
time_ms
```

---

## Minimal reproducible commands

To reproduce the full benchmark CSV:

```bash
stack run khora-bench -- --full --out benchmarks/results/raw/full.csv
```

To validate the full benchmark CSV:

```bash
stack run khora-check-all -- benchmarks/results/raw/full.csv
```

To reproduce only the budget benchmarks:

```bash
stack run khora-bench -- --full --suite budget --out benchmarks/results/raw/budget-full.csv
stack run khora-check-budget -- benchmarks/results/raw/budget-full.csv
```

To reproduce only the regular-plan benchmarks:

```bash
stack run khora-bench -- --full --suite regular --out benchmarks/results/raw/regular-full.csv
stack run khora-check-regular -- benchmarks/results/raw/regular-full.csv
```

To reproduce only the basic benchmarks:

```bash
stack run khora-bench -- --full --suite basic --out benchmarks/results/raw/basic-full.csv
stack run khora-check-basic -- benchmarks/results/raw/basic-full.csv
```

To reproduce only the intermediate-constraint benchmarks:

```bash
stack run khora-bench -- --full --suite intermediate --out benchmarks/results/raw/intermediate-full.csv
stack run khora-check-intermediate -- benchmarks/results/raw/intermediate-full.csv
```

---

## Summary

The benchmark suite is meant to support three claims.

First, the implemented model checkers return the expected semantic results on hand-written corner cases.

Second, the negative cases are not trivial failures of reachability. Many of them are ordinary-reachable but fail because of the stronger knowing-how requirements, such as strong executability, uncertainty over regular plan classes, intermediate-state constraints, or budget constraints.

Third, the generated families give controlled scalability tests by varying one main parameter at a time, such as number of states, branching width, automaton size, number of plan classes, formula depth, or budget dimension.