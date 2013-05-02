---
title: Performance Breakdown
layout: default
---

# {{ page.title }}

From our capabilities results we see that both Yices and Z3 can solve most benchmarks within
a second. Clearly, anything Yices can do, Z3 can also do. In terms of what formulas can be decided
by Z3 and Yices, both are on an even footing. Our capability results suggestthat 

We would like to explore whether there is any significant performance difference between Yices and 
Z3 within the 1 second time frame. The motivation is to find logics and formulas that are susceptible 
to optimization with Yices 2.

### Results

### Analysis

### Next Step

We have now outlined a couple of candidate logics for optimization. The next question is what kind
of interface can we develop to use both Z3 and Yices? Unfortunately, SMT-LIB 1.2 is a deprecated 
language, and most of the SMT community has moved on to SMT-LIB 2.0, but no such interface for Yices 2.0
exists. In addition, there are not many examples of Yices 2's redesigned C API.

A fully functional SMT-LIB 2 parser was written by one of MathSat's authors with a moduler interface 
to integrating external solvers. In order to make Yices 2 more accessible, we'd like to use this parser
so that Yices 2 can solve the same format as Z3.