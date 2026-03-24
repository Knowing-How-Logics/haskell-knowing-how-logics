# Model Checking for Knowing-How Logics

This project implements model-checking procedures in Haskell for two knowing-how logics:

- the basic single-agent logic **$\mathcal{L}_{Kh}$**
- the uncertainty-based multi-agent logic **$reg\text{-}\mathcal{L}^U_{Kh}$**

In addition to the model checkers, the project includes parsers, random model generation, and a test suite using QuickCheck and HSpec.

---

## Implemented Logics

### 1. Single-Agent Logic: $\mathcal{L}_{Kh}$

The first logic is the basic knowing-how logic **$\mathcal{L}_{Kh}$**, following  Wang (2015), with the semantics reformulated in Areces et al. (2021).

Models are given as labelled transition systems ($\text{LTS}$).
A formula of the form `Kh(ψ, φ)` means that there exists a plan `σ` such that, for every state satisfying `ψ`, the plan `σ` is strongly executable and all states reachable by executing `σ` satisfy `φ`. Since the semantic clause quantifies over all states satisfying the precondition, the `Kh` modality is global in the model.

This part of the project includes:

- a Haskell representation of the syntax and semantics of $\mathcal{L}_{Kh}$
- an explicit model checker with bounded plan length
- a parser for formulas of  $\mathcal{L}_{Kh}$
- random generation of $\text{LTS}$ models and formulas for testing
- QuickCheck-based validation of semantic and implementation-level properties

---

### 2. Multi-Agent Logic: $reg\text{-}\mathcal{L}^U_{Kh}$

The second logic is the multi-agent extension **$reg\text{-}\mathcal{L}^U_{Kh}$**, which follows the algorithms described in Demri and Fervari (2023).

Models are given as uncertainty-based labelled transition systems ($\text{reg-LTS}^U$), where each agent is associated with a set of finite automata representing indistinguishable plans.
A formula `Kh_i(ψ, φ)` holds iff there exists an automaton in the agent’s uncertainty set such that every plan accepted by the automaton is strongly executable from every `ψ`-state, and all resulting states satisfy `φ`.

Model checking is carried out via a product digraph construction and a reachability analysis procedure.

This part of the project includes:

- a Haskell representation of $\text{reg-LTS}^U$ models and finite automata
- an implementation of the model-checking procedure based on product graphs and reachability
- a parser for multi-agent formulas
- random generation of models, automata, and formulas
- QuickCheck-based validation of semantic and algorithmic properties

---

## Installation

### Requirements



- Stack
- LaTeX (`latexmk`) for compiling the report
  

---

### Setup

```bash
git clone https://github.com/rensdoodeman/haskell-knowing-how-logics.git
cd haskell-knowing-how-logics
stack build
```

---

### How to run?

Run the full test suite:

```bash
stack test
```

Start an interactive GHCi session:

```bash
stack ghci
```

## Quick Start Examples

### Single-Agent Logic

Generate a random $\text{LTS}$ and model-check a formula:

```haskell
m <- generate (generateLTS 5 3 2)

-- Using the parser
evalForm (m, 1) "KH p1 p2"

-- Alternatively, using the internal representation
isTrue (m, 1) (KH (P 1) (P 2))
```

This checks whether there exists a plan that is strongly executable from every state satisfying `p1`, and guarantees `p2` at every resulting state.

Formulas can also be generated randomly:

```haskell
f <- generate (arbitrary :: Gen Form)
isTrue (m, 1) f
```

This evaluates a randomly generated formula in the given model.

---

### Multi-Agent Logic

Generate a random $\text{reg-LTS}^U$ model and model-check a formula:

```haskell
m <- generate (generateRegLTSU 5 3 2 2)

-- Using the parser
evalRegForm (m, 1) "KH1 p1 p2"

-- Alternatively, using the internal representation
isTrueReg (m, 1) (KHI 1 (Prop 1) (Prop 2))
```

This checks whether agent 1 has an available automaton such that every accepted plan is strongly executable from every `p1`-state and guarantees `p2`.

Formulas can also be generated randomly:

```haskell
f <- generate (generateRegForm 2 5)
isTrueReg (m, 1) f
```

This evaluates a randomly generated multi-agent formula, where the first parameter specifies the number of agents and the second controls the formula size.

---

## Formula Input Format

The project provides parsers for both the single-agent language $\mathcal{L}_{Kh}$ and the multi-agent language $reg\text{-}\mathcal{L}^U_{Kh}$.

---
### Single-Agent Parser 
---

| Input form | Meaning | Parsed as |
|-----------|---------|-----------|
| `p1`, `p2`, ... | propositional variable | `P 1`, `P 2`, ... |
| `P1`, `P2`, ... | propositional variable | `P 1`, `P 2`, ... |
| `T` | truth constant | `T` |
| `!φ` | negation | `Neg φ` |
| `φ ^ ψ` | conjunction | `Conj φ ψ` |
| `φ v ψ` | disjunction (abbreviation) | `Neg (Conj (Neg φ) (Neg ψ))` |
| `φ V ψ` | disjunction (abbreviation) | `Neg (Conj (Neg φ) (Neg ψ))` |
| `φ -> ψ` | implication (abbreviation) | `Neg (Conj φ (Neg ψ))` |
| `KH φ ψ` | knowing-how formula | `KH φ ψ` |
| `(φ)` | parentheses for grouping | `φ` |

---
### Multi-Agent Parser 
---

| Input form | Meaning | Parsed as |
|-----------|---------|-----------|
| `p1`, `p2`, ... | propositional variable | `Prop 1`, `Prop 2`, ... |
| `P1`, `P2`, ... | propositional variable | `Prop 1`, `Prop 2`, ... |
| `!φ` | negation | `Not φ` |
| `φ v ψ` | disjunction | `Disj φ ψ` |
| `φ V ψ` | disjunction | `Disj φ ψ` |
| `φ -> ψ` | implication (abbreviation) | `Disj (Not φ) ψ` |
| `φ ^ ψ` | conjunction (abbreviation) | `Not (Disj (Not φ) (Not ψ))` |
| `KH1 φ ψ` | knowing-how for agent 1 | `KHI 1 φ ψ` |
| `KH2 φ ψ` | knowing-how for agent 2 | `KHI 2 φ ψ` |
| `KH 1 φ ψ` | alternative syntax | `KHI 1 φ ψ` |
| `(φ)` | parentheses for grouping | `φ` |



---

### Notes

- In both parsers, `p1` and `P1` are equivalent.
- Some connectives are implemented as abbreviations:
  - `->` and `v` in the single-agent parser
  - `->` and `^` in the multi-agent parser
- `KH` is used in the single-agent language, while `KH i` (or `KHi`) is used in the multi-agent language to indicate the agent index.
- Spaces are flexible: for example, both `KH1 p1 p2` and `KH 1 p1 p2` are accepted.

---

## Makefile Utilities

For convenience, the repository provides a Makefile to automate common tasks:

- **Build the project**

```bash
make build
```

This runs `stack build` to compile the Haskell code.

---

- **Run the main executable**

```bash
make run
```

This builds the project and runs the executable `myprogram`.

---

- **Run the test suite**

```bash
make test
```

This runs all test suites with coverage enabled.

---

- **Compile the report**

```bash
make
```

or

```bash
make report.pdf
```

This compiles the LaTeX report using `latexmk`.

---

- **Clean generated files**

```bash
make clean
```

This removes Stack build artifacts and auxiliary LaTeX files.


---

## References

The implementation of the logics and model-checking procedures in this project is based on the following works:

- Wang, Y. (2015). *A Logic of Knowing How*. In *Logical Reasoning and Interaction (LORI'15)*, LNCS 9394, pp. 392–405. Springer.
- Areces, C., Fervari, R., Saravia, A. R., & Velázquez-Quesada, F. R. (2021). *Uncertainty-Based Semantics for Multi-Agent Knowing How Logics*. In *TARK 2021*, EPTCS 335, pp. 23–37.
- Demri, S., & Fervari, R. (2023). *Model-Checking for Ability-Based Logics with Constrained Plans*. In *AAAI-23*, Vol. 37(5), pp. 6305–6312.

For the complete bibliography used in the report, see `references.bib`.