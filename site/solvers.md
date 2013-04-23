---
title: Choice of Solvers
layout: default
---

# {{ page.title }}

### Introduction

Yices currently comes in two versions. Version 1 is a stable release that 
previously won the SMT competition in the mid 2000's. Its feature set is 
comparable to Z3, but the preliminary experiments we ran demonstrate that 
it isn't very competitive with the latest version of Z3. For these reasons,
we chose the new prototype of yices, version 2. Version 2 lacks many features,
such as quantifiers, but in our comparison it provides a good speed up over Z3
in some cases.

Our project then intends to combine the full-featured Z3 solver with the lighter
Yices 2.0. Exploring just how much of a speed up we can get based on the choice
of solver will be the focus of the project. The results presented here compare
the power of Yices 1.0 to Z3.

## Experiments

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
integer difference logic and linear real arithmetic appear to be exceptions to this rule, but we argue in the next section where Yices 1.0 excels, Yices 2.0 excels more.

Another compelling reason not to use Yices 1 is the fact that Z3 beats it
to the punch on roughly 30% of our QF_BV sample. Given that quantifier
free formulas over bit vectors is the largest benchmark suite available,
we would like to use two solvers that are competitive in deciding it.

##### Notes

One feature it has that is absent in Yices 2.0 and Z3 is the ability 
to find maximally satisifying models for formulas, but this may be outside 
the scope for our project.

[1]: img/solvers/yices.svg
