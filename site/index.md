---
title: Will Blair and Nikka Ghalili
layout: default
---

# Integrating Z3 and Yices 
## CS 512 Project

### Members

* Nikka Chalili - nikka999@bu.edu
* Will Blair - wdblair@bu.edu

### Project Description

The goal of our project is to combine two SMT solvers into a more powerful composite
solver. For this project, more powerful is defined as being able to validate a set of formulas that neither
of the individual solvers could validate on its own. We will restrict this set to first order logic formulas
involving integers and bit vectors.


The two SMT solvers we will use are Z3 and Yices from Microsoft Research and SRI International, respectively.
Both can handle a wide domain of input including real numbers, integers, fixed-size bit vectors, arrays, and 
user-defined recursive data types. In addition to determining satisfiability, Z3 can also provide a solution 
to a formula \[[1]\], but that may be outside the scope of the project. Yices supports all of the theories in 
SMT-Comp as of 2006.

### Schedule

* #### Mid March
Become familiar with how to use both SMT solvers for basic formulas. Explore the usefulness of each
solver and put together a preliminary set of formulas each can handle well.
* #### Late March
Complete a good draft of the two sets of formulas each solver can handle, as well as those outside the reach
of each solver.
* #### Early April
Define precisely the set of formula our integrated solver will be able to handle. Begin work on the interface.

### Meetings

* #### 2/21/13
Outlined some common features of Z3 and Yices. Decided that we'll each get some experience
with a solver and start finding formula especially suited for it.  Yices is assigned to Will and Z3 to Nikka.

* #### 3/19/13
Met with Andrei and discussed the scope of the project. Got ideas about strategy for examining
the solvers' efficiency and capabilities. He mentioned not to focus too much on parsing.

* #### 3/22/13
Discussed our initial findings. Decided to measure Yices' and Z3's performance on some standard
benchmarks. We'll evaluate both on QF_LIA, QF_UFLIA, and AUFLIA (to see what each supports for as
far as quantifiers).

* #### 3/30/13
Compared our results from the basic performance tests. We noticed Yices would time out on some
formulas in QF_LIA when Z3 could handle them without a problem. Decided for Will to explore what
reasonable timeout yields the most formulas that can be solved by both solvers. Nikka will investigate
how more efficient (if at all) each solver is for a particular logic.

* #### 4/7/13
Compared our findings for each solver's capabilities. We started outlining our intuition for each
experiment and looked forward to what the result of this project should be. Given the performance
and capability results we have, we are going to implement a baseline SMT solver that just runs both
solvers in parallel and answers based on whichever solver finishes first. This is simple to implement
and will gives us a good comparison to the composite solver we want to implement that decides the best
solver to run based on the characteristics of the input formula.

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

#### Bit Vectors

bit-vector functions such as bvshl, bvlshr, bvudiv, bvurem are not supported in Yices. This means most 
of the benchmarks in QF_UFBV are unsupported in Yices.

### Performance

#### Nested if-then-else Statements

Slides from a talk given by Bruno Dutertre \[[2]\] specify nested if-then-else formulas as an area
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

This section highlights web pages or papers we have referenced or have found helpful.

1. [Towards Lightweight Integration of SMT Solvers][1]: Lapets, Mirzaei 2012

2. [Challenging Problems for Yices][2]: Duterte, Deduction at Scale Seminar 2011

[1]: http://www.cs.bu.edu/techreports/pdf/2012-017-smt-integration.pdf
[2]: http://www.mpi-inf.mpg.de/departments/rg1/conferences/deduction10/slides/bruno-dutertre.pdf
