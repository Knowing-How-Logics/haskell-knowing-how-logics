# KHora: A Model Checker for Knowing-How Logics
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.19316699.svg)](https://doi.org/10.5281/zenodo.19316699)

KHora is a model checking tool for knowing-how logics, written in Haskell. It currently supports:

- the basic knowing-how logic $\mathcal{L}_{Kh}$;
- the knowing-how logic with intermediate constraints $\mathcal{L}_{Khm}$;
- the uncertainty-based knowing-how logic with regularity constraints $reg\text{-}\mathcal{L}^U_{Kh}$;
- the budget extension of $\mathit{reg}\text{-}\mathcal{L}^U_{Kh}$.

For further details, see the relevant sections of `KHora.pdf`. **WORK IN PROGRESS!!**

## Installation

### Requirements

To build and run KHora, you will need:

- [Stack](https://docs.haskellstack.org/)
- a recent GHC version supported by Stack
- a TeX distribution with `latexmk` if you want to compile the report (optional)

### Setup

```bash
git clone https://github.com/Knowing-How-Logics/haskell-knowing-how-logics.git
cd haskell-knowing-how-logics
stack build
```
### How to use?
build + clean up + run benchmark + verify data + plot
```shell
make dev
```

## References

- Wang, Y. (2015). *A Logic of Knowing How*. In *Logic, Rationality, and Interaction: 5th International Workshop, LORI 2015*, LNCS 9394, pp. 392–405. Springer.
- Areces, C., Fervari, R., Saravia, A. R., & Velázquez-Quesada, F. R. (2021). *Uncertainty-Based Semantics for Multi-Agent Knowing How Logics*. In *Proceedings of the 18th Conference on Theoretical Aspects of Rationality and Knowledge (TARK 2021)*, EPTCS 335, pp. 23–37.
- Demri, S., & Fervari, R. (2023). *Model-Checking for Ability-Based Logics with Constrained Plans*. In *Proceedings of the 37th AAAI Conference on Artificial Intelligence*, Vol. 37, No. 5, pp. 6305–6312.
- Wang, Y. 2018b. A logic of goal-directed knowing how. Synthese, 195(10): 4419–4439.
