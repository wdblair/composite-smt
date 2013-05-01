---
title: Measuring the Power of a Solver
layout: default
---

# {{ page.title }}

### Introduction

Yices currently comes in two versions. Version 1 is a stable release that 
previously won the SMT competition in the mid to late 2000s. Its feature set is 
comparable to Z3, but the preliminary experiments we ran demonstrate that
it isn't very competitive with the latest version of Z3.

In this section we outline how we went about determining the power of an SMT
solver, and then demonstrate the lack of interesting differences between Yices 1.0
and Z3. For these reasons, we decided to use Yices 2.0 instead. These experiments
were also run to get a better idea of which solver is appropriate for each logic 
since the subject is not heavily discussed in the documentation. Many sources simply
outline what the solver can and cannot do. Given the overlap of features between
Z3 and Yices, this isn't very helpful.

### Defining Capability

If we define power as the set of logics from which each solver can handle a 
reasonable number of formulas, we would have a droll comparison.
Both Yices 1 and Z3 support the standard set of quantifier free logics as well 
as those involving quantifiers and Z3 offers some support for non-linear 
polynomial arithmetic. We claim that the practical power of a solver is tied to
its efficiency.

An SMT solver will only answer "I don't know" if the formula given matches its known
unknowns, or it surpasses a timeout. For example, if I give Yices a formula that
contains non-linear arithmetic, it will fail in the parsing step. On the other hand,
if I give it a formula that tries to prove an inductive fact on the set of natural 
numbers, it will run forever in an infinite loop.

    (declare-datatypes () ((Nat zero (succ (pred Nat)))))
    (declare-fun p (Nat) Bool)
    (assert (p zero))
    (assert (forall ((x Nat)) (implies (p (pred x)) (p x))))
    (assert (not (forall ((x Nat)) (p x))))
    (check-sat)

Given the above, the obvious parameter that controls an SMT solver's power is the
timeout we give it. We can also modify the tactics it will employ during
solving _link_to_strategy_paper_, but that is outside the scope of our project. If
one solver can solve more formulas within a much smaller timeout than
another, we can say such a solver is more powerful. Whenever we compare the capabilities
of two solvers, we will use the following experiment.

## Experiments

There are many benchmark suites to choose from and some logics consist of a
enormous amount of tests. At the beginning of the project, we were unsure of how
long we should expect a solver to finish a test. Some examples are proven on the
order of milliseconds whereas some take hours. This made running the solver over the 
entire suite unfeasible. In order to avoid the land mines that take ten minutes or 
more for both solvers, we decided to run each solver on a random sample of each logic.
We first run both solvers with our lowest timeout over each benchmark in the sample.
If one solver decides a benchmark within the timeout and the other doesn't we 
designate it the winner, otherwise we note both as finishing it. For any benchmarks
that neither solver proved, we repeat this process for the next timeout for the unsolved
benchmarks. If neither solver can prove a benchmark in any of the timeouts, we mark it
as unknown.

The experiments we ran between Yices 1.0 and Z3 were the same as described in the
capability experiments. The following are the results obtained for some common
logics. For each logic, we selected a random sample of at least 5% of the total
tests. We exclude logics that were explicitely unsupported by a solver.

### Results

![Yices][1]

### Conclusions

Based on our results, there isn't much compelling evidence to use Yices 
1.0. It is true that both solvers can handle _most_ formulas in a short
time, but there is little that Yices can do that Z3 cannot. Of course,
integer difference logic and linear real arithmetic appear to be exceptions to this rule, 
but we argue in the next section where Yices 1.0 excels, Yices 2.0 excels more.

Another compelling reason not to use Yices 1 is the fact that Z3 beats it
to the punch on roughly 30% of our QF_BV sample. Given that quantifier
free formulas over bit vectors is the largest benchmark and arguably one
of the most important, we would like to use two solvers that are competitive 
in deciding it.

[1]: img/solvers/yices.svg
