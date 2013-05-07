---
title: Capabilities of Z3 and Yices
layout: default
---

# {{ page.title }}

This experiment sought to determine what logics from the SMT benchmarks (if any)) are better solved by yices 2 or z3. We use the same experiment and 
evaluation

### Results

![Results][1]

### Analysis
Yices 2.0 performs better than Z3 in a number of logics, but most are 
solved within a second. In our report, we investigate the which is better
within this one second window and discover a few places where Yices 2.0
does consistently beat Z3.

[1]: img/power/power.svg