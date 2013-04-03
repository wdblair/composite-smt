Power of SMT Solvers
====================
(This puts the rough, in rough draft) These experiments try to determine what logics from the SMT benchmarks (if any) are
better solved by yices or z3.

Intuition
=========

Both Yices and SMT are reasonably powerful SMT solvers. Given enough time, we think
either of these solvers will eventually solve a formula from the SMT benchmarks; there
are few formulas where either solver will just give up and say "I don't know". For yices,
formulas involving quantifiers and non-linear arithmetic will cause it to give up.

Internally, a solver only answers unknown if it times out. If a solver's power is
determined by how many formulas it can determine are sat or unsat, then power must be
tied to efficiency. These experiments will explore the upper bound of an "ideal" timeout
where a composite solver could answer all of the formulas found in the SMT-Comp benchmark
suite. We hope to show neither Yices nor Z3 could do this with the same timeout.

These results could also serve as an ideal baseline for the composite solver we hope to 
build.

Experiment
===========

The biggest time sink for benchmarking SMT solvers occurs when a solver encounters
a formula it won't be able to solve within timeout. If the other solver
could have solved it in a shorter amount of time, we at least waste the timeout
period. The heart of this experiment is to determine if one solver can solve one set
of logic much faster than the other. Note, we are not interested in _how_ much faster.
That is being determined in our performance benchmark.

The simplest parameter for controlling the "power" of a solver is the timeout. Starting
from a few seconds and moving upwards in our experiments, we hope to find out which solver
is better suited to each logic. Note, the ideal timeout may also depend on the logic at
hand. One example is that our preliminary investigation showed Z3 smoking Yices on quantifier
free linear integer arithmetic, yet both struggled in certain quantifier free formulas involving
bit vectors.

All benchmarks are run on elf.bu.edu.

The goal of this experiment is to find an ideal timeout for each logic where we may solve a reasonably
large set of that logic in the benchmarks. We are vague using the term reasonably, since we're unsure of
the decision landscape for each solver yet. We'll arrive at a definition as the timeout becomes less
reasonable.

### Description
For each timeout t, run following steps on each file within a logic.

1. Run z3 and yices on the file with a hard timeout T.
2. If both time out, answer "unknown".
3. If both answer, answer "known".
4. If only one solver s finishes, answer s, where s is the solver's name.

If any answer unknown, do the above just on the unknown files
with the next timeout t'. If most answer known, reduce the timeout.

There's a lot of benchmarks to go through. The logics QF_BV and QF_AUBV, for example,
have roughly 46000 benchmarks to go through. Given we only have about 43,200
minutes until the project is due, taking a random sample is our best bet. 

### Results

N/A

