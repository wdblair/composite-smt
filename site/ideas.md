---
title: Preliminary Ideas
layout: default
---

# {{ page.title}}

Here we give a short overview of the capabilities and performance differences
we've seen from documentation and papers. This is meant as a scratchpad for
potential investigation.

### Capabilities

#### Non Linear Arithmetic

Yices does not support non-linear arithmetic. Formulas of the following form

    (define y::nat)
    (assert (not (>= (* y y) y)))    ; prove negation unsatisfiable
    (check)

cause Yices to fail. In this case, unknown is not returned, Yices actually fails saying
nonlinaer arithmetic is unsupported. This error will appear whenever it encounters
a sub-formula (* x y) where neither terms are constant.

In contrast, Z3 4.0 has a non-linear arithmetic solver, but it is not yet integrated
with the other theories (arrays, bitvectors, etc.). Therefore, Z3 should be able to handle
non-linear arithmetic if it is the only theory used in the formula. Of course, non-linear arithmetic is
undecidable, so there will be some formulas it can't handle. In Z3's language we can prove the above
example satisfiable.

    (declare-const x Int)
    (assert (>= (* x x) x))
    (check-sat)
    sat

#### Subtypes

Yices supports subtypes, which is described as a set of elements of some type. We can, for example, 
define the set of even natural numbers as

    (define even::(subtype (n::int) ( and ( >= n 0) ( = (mod n 2) 0 ))))

Z3 lacks direct support for subtypes. Subtypes are used to make functions, records, and tuples 
_dependent_; the type of one component may depend on the types of previous components. We are not 
sure if Z3 supports dependent types, although it seems unlikely. Adding support for sub-types may
not be particularly useful.

In our perspective, dependent types do not add to the capability of an SMT solver; a solver using a dependent
language cannot solve more first order formulas than a solver without such types.

#### Bit Vectors

bit-vector functions such as bvshl, bvlshr, bvudiv, bvurem are not supported in Yices. This means most 
of the benchmarks in QF_UFBV will not run in Yices.

### Performance

#### Nested if-then-else Statements

Slides from a talk given by Bruno Dutertre \[[1]\] specify nested if-then-else formulas as an area
where Yices 2.0 works very well. A formula like the following

    (>= (ite c t1 t2) u)

Can be handled by "lifting" the if expression out which gives

    (ite c (>= t1 u) (>= t2 u))

While this risks exponential blow-up, Dutertre notes that lifting works well in practice. A set
of SMT benchmarks from NEC that reason about program constraints verify huge formulas of nested
conditionals. Dutertre attributes Yices' success in this area to lifting.

A quick run of Yices, Yices2, and Z3 on the mentioned benchmark verified Dutertre's claim. Yices 2.0 
went through the medium sized set (364 examples) in a minute and half. Z3 took over 13 minutes while 
Yices 1.0 took about an hour.

#### Bitvectors

In the same talk Dutertre mentions Bitvectors as an example of a problem that has easy solutions
given the right simplifications. The standard technique reduces constraints on bit vectors to 
propositional formulas (bit-blasting). Z3 does the same thing, so the difference in performance
for such formulas may be slight. We should investigate this on the QF_BV and QF_AUBV benchmarks.

### References

1. [Challenging Problems for Yices][1]: Duterte, Deduction at Scale Seminar 2011

[1]: http://www.mpi-inf.mpg.de/departments/rg1/conferences/deduction10/slides/bruno-dutertre.pdf