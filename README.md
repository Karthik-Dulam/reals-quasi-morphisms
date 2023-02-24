# Reals using Quasi-Morphisms [WIP]
[![ci](https://github.com/Karthik-Dulam/reals-quasi-morphisms/actions/workflows/build.yaml/badge.svg?event=push)](https://github.com/Karthik-Dulam/reals-quasi-morphisms/actions/workflows/build.yaml)

Reals defined using quasi-morphisms formalized in Lean

## Introduction
This project is an attempt to formalize the construction of the reals using quasi-morphisms
from `ℤ` to itself. We first construct the type `AlmostHom ℤ` consisting of functions from
`ℤ` to itself which respect addition up to a constant error bound and show that this is a
commutative group under addition. Next we define the subgroup consisting of bounded functions
and form the quotient group, which we call `QuasiHom ℤ`. Finally, we define multiplication on
`QuasiHom ℤ` by function composition and an ordering and show that it is a complete ordered
field [WIP].

## Plan
Here, `G` is an additive commutative group.

+ [ ] Construct `QuasiHom G` and show that `QuasiHom ℤ` is a complete ordered field
  - [X] Define `QuasiHom G`
    * [X] Define `AlmostHom G`
    * [X] Construct instance of `AddCommGroup (AlmostHom G)` using pointwise addition
    * [X] Define the subgroup of bounded functions
    * [X] Define `QuasiHom G` as the quotient of `AlmostHom G` by the subgroup
  - [ ] Field structure of `QuasiHom ℤ` using composition as multiplication
    * [X] Define multiplication of type `QuasiHom ℤ →+ QuasiHom G →+ QuasiHom G` by lifting composition
    * [ ] Construct inverse of a non-zero `QuasiHom` (and prove that it is inverse)
    * [ ] Construct instance of `Field (QuasiHom ℤ)`
  - [ ] Order structure of `QuasiHom ℤ`
    * [X] Define a predicate `NonNeg` on `QuasiHom ℤ`
    * [ ] Construct instance of `LinearOrderedAddCommGroup (QuasiHom ℤ)` using the predicate, via `TotalPositiveCone`
  - [ ] Construct instance of `ConditionallyCompleteLinearOrder (QuasiHom ℤ)`
  - [ ] Construct instance of `LinearOrderedField (QuasiHom ℤ)`
+ [ ] (optional) Show that `QuasiHom G` is a `QuasiHom ℤ`-vector space
  - [ ] Construct instance of `Module (QuasiHom ℤ) (QuasiHom G)`

    This should follow straightforwardly from `QuasiHom ℤ →+ QuasiHom G →+ QuasiHom G`.
+ [ ] (optional) Relate `QuasiHom ℤ` to other algebraic structures
  - [ ] Embed `ℚ` (as an ordered field) in `QuasiHom ℤ`
  - [ ] Define unique isomorphism from `QuasiHom ℤ` to any other complete ordered field
+ [ ] (optional) Show `QuasiHom ℤ` is Cauchy-complete (perhaps as a uniform space?)
+ [ ] (optional) Generalise codomain from `ℤ` (perhaps to a `LinearOrderedRing`?)

## References & Clarifications
+ Primarily [this exposition](http://web.science.mq.edu.au/~street/EffR.pdf) by James Douglas et al

  Remark: our naming convention is slightly different from this: we call the functions
  `ℤ → ℤ` which are almost additive almost-homomorphisms (`AlmostHom`) and the elements of
  the quotient of `AlmostHom` by the bounded functions quasi-morphisms (`QuasiHom`), whereas
  the paper calls the functions themselves quasi-morphisms.
