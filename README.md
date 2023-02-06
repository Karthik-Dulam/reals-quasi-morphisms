# Reals using Quasi-Morphisms [WIP]

[![ci](https://github.com/Karthik-Dulam/reals-quasi-morphisms/actions/workflows/build.yaml/badge.svg?event=push)](https://github.com/Karthik-Dulam/reals-quasi-morphisms/actions/workflows/build.yaml)

Reals defined using Quasi-Morphisms formalized in Lean

## Introduction 

This project is an attempt to formalize the construction of the reals using 
QuasiMorphisms from `ℤ` to itself. We first Construct the type of AlmostHomomorphisms,
then show that this has a commutative group structure, identify the subgroup formed by
bounded AlmostHomomorphisms and then quotient by this subgroup to get the type of Reals.

We then define a product on QuasiMorphisms by showing that the composition respects the 
equivalence relation. Using this product we show that this forms a field [WIP].
We need to find a suitable order on this type and show that this forms an ordered field, 
and finally prove completeness.


## Plan 

  + [ ] Construct a Complete Ordered Field using QuasiMorphisms
      - [X] Define Quasi-Morphisms
          * [X] AlmostHoms
          * [X] BoundedHoms
          * [X] AlmostHoms additive group
          * [X] Quotient AlmostHoms / BoundedHoms
      - [ ] Show QMs form a Field 
          * [X] Composition on AlmostHoms
          * [X] "Lift" it to Quotient
          * [ ] Construct inverses
          * [ ] Misc Properties (Some of these follow from comp on Quasi-Morphisms)
      - [ ] Ordered Field
          * [ ] Define a suitalbe total order on QuasiMorphisms
          * [ ] Prove that this forms an Ordered Field
      - [ ] Prove Completeness
    
## References & Clarifications

We have followed [this exposition](http://web.science.mq.edu.au/~street/EffR.pdf) by James Douglas et al, but 
the naming convention is slightly different: We call the functions : `ℤ → ℤ` which 
are almost homomorphisms, `AlmostHoms` and the bounded functions among them, `BoundedHoms`.
We call the quotient of `AlmostHoms` by `BoundedHoms` as `QuasiMorphisms`.
