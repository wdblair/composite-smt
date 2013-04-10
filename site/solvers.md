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

![QF_AX][6]
![QF_AUFBV][1]
![QF_BV][8]
![QF_LIA][2]
![QF_LRA][4]
![QF_UFLRA][9]
![AUFLIA][10]
![AUFLIRA][11]
![QF_UFIDL][5]


### Conclusions

Based on our results, there isn't much compelling evidence to use Yices 1.0. One
feature it has that is absent in Yices 2.0 and Z3 is the ability to find maximally
satisifying models for formulas, but this may be outside the scope for our project.

[1]: img/solvers/qf_aufbv.svg
[2]: img/solvers/qf_lia.svg
[3]: img/solvers/qf_auflia.svg
[4]: img/solvers/qf_lra.svg
[5]: img/solvers/qf_ufidl.svg
[6]: img/solvers/qf_ax.svg
[7]: img/solvers/qf_uflia.svg
[8]: img/solvers/qf_bv.svg
[9]: img/solvers/qf_uflra.svg
[10]: img/solvers/auflia.svg
[11]: img/solvers/auflira.svg