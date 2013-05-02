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
Define precisely the set of formula our integrated solver will be able to handle. Begin work on the composite solver.

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
solvers in parallel and answers based on whichever solver finishes first. This is simple to
implement and will gives us a good comparison to the composite solver we want to implement that
decides the best solver to run based on the characteristics of the input formula.

* #### 4/23/13
Went over the initial baseline SMT solver we developed. Decided that once an SMT solver finishes,
the program should terminate the other solver and return the result. Went over our current graphs and
talked about how to present our results with respect to efficiency. Outlined a good direction for our final
deliverable; an SMT solver as feature rich as Z3 but as quick as Yices 2.

### References

This section highlights web pages or papers we have referenced or have found helpful.

1. [Towards Lightweight Integration of SMT Solvers][1]: Lapets, Mirzaei 2012

[1]: http://www.cs.bu.edu/techreports/pdf/2012-017-smt-integration.pdf
