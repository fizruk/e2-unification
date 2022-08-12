# e2-unification

[![Haddock](https://shields.io/badge/Haddock-documentation-informational)](https://fizruk.github.io/e2-unification/haddock/index.html)
[![CI status](https://github.com/fizruk/e2-unification/actions/workflows/haskell.yml/badge.svg)](https://github.com/fizruk/e2-unification/actions/workflows/haskell.yml)

Simple E-unification for second-order syntax.

## About

This is an experimental project, attempting to implement a generic unification procedure in presence of second-order equalities a la Fiore [1]. The idea is to make it powerful enough to get higher-order unification "for free" for a given language provided its 2nd-order syntax description and rewrite rules, and then use it for type inference for dependent type theories. A more obscure version of this approach has been implemented in an experimental [rzk](https://github.com/fizruk/rzk) proof assistant and described in [2]. Implementation here corresponds more with the [version presented at UNIF-2022 workshop](https://easychair.org/smart-program/FLoC2022/UNIF-2022-08-12.html#session:62460) [3].

This is active work-in-progress and may contain bugs and performance issues.

## Development

The project is developed with both Stack and Nix (for GHCJS version).

### Building with GHC

For quick local development and testing it is recommended to work with a GHC version, using [Stack tool](https://docs.haskellstack.org/en/stable/README/). Clone this project and simply run `stack build`:

```sh
git clone git@github.com:fizruk/simple-topes.git
cd simple-topes
stack build
```

# References

[1] Marcelo P. Fiore, Ola Mahmoud (2013). _Second-Order Algebraic Theories._ CoRR, [abs/1308.5409](http://arxiv.org/abs/1308.5409)

[2] N. Kudasov. _Functional Pearl: Dependent type inference via free higher-order unification._ [abs/2204.05653](https://arxiv.org/abs/2204.05653)

[3] N. Kudasov. _Higher-order unification from E-unification with second-order equations and parametrised metavariables._ UNIF-2022 https://easychair.org/smart-program/FLoC2022/UNIF-2022-08-12.html#session:62460
