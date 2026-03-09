# Knowing-how Logics

## Syntax

### Propositional
* `Prop` = set of propositional letters.

### Agents 
* `Agt` = set of agents.

### Kh modality
* `Kh_i` = Kh w.r.t. agent `i` from `Agt`.

### Actions
* `Act` = set of actions.

### Plans
* `Act*` = set of all finite sequences of actions, namely, set of plans.

## Model
`M = <S, (R_a), (U_i), V>`

### States
* `S` = set of all states.

### Automata
* `U_i` = set of Automata w.r.t. agent `i`.

* `A = (Q, Act, delta, I, F)`

```
Q = set of automaton states.

delta = transition relation.

I = initial states.

F = accepting states.
```

#### Special automaton used in model checking:

* `A_(a,b) = (Q, Act, delta, I, F)` where
```
Q = S.

(t -a-> t') in delta <=> t R_a t'

I = {a}.

F = {b}.
```

* `L(A)` = language of automata.

### Valuation
* `V` = valuation function.

### Relations

* `R_a` = relation w.r.t. action `a`.

* `R_sigma` = relation w.r.t. plan `sigma`.

* `R_sigma (u)` = set of states that are reachable from state `u` via plan `sigma`

* `R_pi (u)` = union of `R_sigma (u)` w.r.t. `sigma`, where `sigma` is in `pi`.

* `R_pi (X)` = union of `R_pi (u)` w.r.t. `u`, where `u` is in `X` and `X` is a subset of `S`.

* `SE(sigma)` = set of all states that plan `sigma` is strongly executable.

* `SE(pi)` = intersection of `SE(sigma)` w.r.t. `sigma`, where `sigma` is in `pi`.

## Semantics

* `eval` = satisfaction.

* `[phi]` = set of states where `phi` holds.

## Model Checking

```
for each automaton A in U_i:
    check condition (1)
    check condition (2)
```

### Condition 1

#### reachability

#### product graph

### Condition 2

#### reachability

#### product graph