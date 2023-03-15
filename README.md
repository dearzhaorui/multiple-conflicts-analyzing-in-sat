
Modified CaDiCaL SAT Solver For Evaluation of Multiple Conflicts Analyzing
===============================================================================

This repository is an modified version for an experiment evaluation of multiple conflicts analyzing, originally from [CaDiCaL 1.5.2](https://github.com/arminbiere/cadical.git).

The goal of this version is to experimentally evaluate how many different conflicting clauses occur, the contribution based on lemmas' quanlity(e.g. LBD) to the solving process for each of them and exploring the best solving strategy.

Go to each folder for more details about building information. 

The `output` directory contains four sub-folders with all output files of each SAT solver (the CaDiCal and two modified versions for multiple conflicts analyzing) tested on 400 Main Track benchmarks in SAT Competition 2022 in 5 seeds(e.g. 1,2,3,4,5). 
The experiments with a time limit 5000 seconds have been done in a cluster with 10 nodes. Every solver on a node is set to hava 4 cores and 15GB of memory available.
