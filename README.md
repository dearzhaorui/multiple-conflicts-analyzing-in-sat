
Modified CaDiCaL SAT Solver For Evaluation of Multiple Conflicts Analyzing
===============================================================================

This repository contains all sources used in the paper "Analyzing Multiple Conflicts in SAT: An Experimental Evaluation". They are all built on top of [CaDiCaL 1.5.2](https://github.com/arminbiere/cadical.git).

The goal of this version is to experimentally evaluate how many different conflicting clauses occur, the contribution based on lemmas' quanlity(e.g. LBD) to the solving process for each of them and exploring the best solving strategy. 

The `output` directory contains four sub-folders with all output files of each SAT solver (the CaDiCal and two modified versions for multiple conflicts analyzing) tested on 400 Main Track benchmarks in SAT Competition 2022 in 5 seeds(1,2,3,4,5). The experiments have been done in a cluster with 10 nodes of type Dell PowerEdge R240 with Intel Xeon E-2124. Every solver on a node is set to have 4 cores and 15GB of memory available. The time limit is 5000 seconds.
