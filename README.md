#MAXSAT-Ising

This package contains the generalized Ising model ground
state solver. There are three subpackages - "ising", which is the solver
iself, "ccls", which is a MAX-SAT solver optimized for spin-glass problems,
and "ccls_lb", which is a modified version of the ccls solver optimized for
this particular use case. These packages are based on the AkMAXSAT code, as
well as the CCLS2014 code.


A detailed description of the algorithm and benchmarks are available in 
Huang et al, "Finding and proving the exact ground state of a generalized
Ising model by convex optimization and MAXSAT" PRB (2016) 
([preprint](https://arxiv.org/abs/1604.06722))


Authors:
+ Ising solver implementation: Wenxuan Huang, Daniil Kitchaev
+ MAXSAT solvers: Chuan Luo (CCLS, CCLS\_to\_akmaxsat), Adrian Kuegel (akmaxsat)


Contact: Wenxuan Huang (key01027ATmit.edu), Daniil Kitchaev (dkitchATmit.edu)


If you use this code in your work, please cite Huang et al, "Finding and
proving the exact ground state of a generalized Ising model by convex
optimization and MAXSAT" PRB (2016) -
([preprint](https://arxiv.org/abs/1604.06722))

Prerequisites
-------------------------------------------------------------------------------
This package is tested using GCC 4.8.2, Gurobi 6.5.2 and 6.0.2, and Boost 1.57.


Installation
-------------------------------------------------------------------------------
1. Set the Gurobi INCLUDE and LIB directories in the build.sh script. Make sure
	a recent version of Boost is installed, including the regex module.
2. Run the build.sh script

!! A note on compilers: Gurobi does not support GCC 5 at the time of writing, 
so all compilation must be done with GCC 4.8 or earlier. Note that on recent
versions of Ubuntu, this requires rebuilding Boost with GCC 4.8, as the
defaults available have been updated to GCC 5.


Execution
-------------------------------------------------------------------------------
The bin directory contains a number of executables - these must at all times
be located in the same directory, so if you move them, they must all be moved
together. The main executable is "ising", while the others are needed for
intermediate steps in the solver.
Thus, to run the code, copy the entire contents of the bin/ directory to the
directory where you have the J_config.in and J_in.in files:

```bash
    cp <ising root>/bin/* <run_dir>/

```
And run the main executable:

```bash
    cd <run_dir>/
    ./ising
```


Input
-------------------------------------------------------------------------------
The "ising" executable assumes the presence of two files in its directory -
"J_in.in", which contains the cluster expansion ECI's, and "J_config.in",
which contains the setup for the solver execution. See the documentation
below and provided examples for the format of these files.


###ECIs (J_in.in)
The first line of this file is

```
Constant <E0>
```
where <E0> gives the baseline energy of the system per lattice site in the case
that all correlations are zero.

The following sets of blocks, separated by a blank line, are formatted as
```
Cluster <N>
<i0>,<j0>,<k0>,<p0>,<t0> <i1>,<j1>,<k1>,<p1>,<t1> <i2>,<j2>,<k2>,<p2>,<t2> ...
J=<ECI>
```
where:
+ `<N>` is the index of cluster, starting with 1
+ `<i0>,<j0>,<k0>,<p0>,<t0>` give the set of sites belowing to the cluster.
  Specifically, (i,j,k) specify unit cell translations of the site in question,
  p gives the index of the site within this unit cell, and t specifies the
  specie index occupying this site. Once again, note that i,j,k,p,t all begin
  at 1 rather than 0 as the 0-clusters are arbitary reference states.
+ `<ECI>` gives the ECI (energy) associated with the cluster

### Configuration (J_config.in)
+ NSITES: Maximum number of sites in a unit cell to consider (default=50)
+ NLOOPS: Number of lower bound optimization loops (default=4)
+ LABEL: Label for the calculation (default=IS0)
+ PREC: Numerical precision for the ECI's (default 1e-6)
+ MODE_JPLUSMINUS:
    + 0 - ECI's and correlations in 0/1 form (default) for site occupancy
    + 1 - ECI's and correlations in -1/+1 form for site occupancy
+ MODE_SOLVER:
    + 0 - Exact solution
    + 1 - Pseudo-optimization without proof (default)
    + 2 - Pseudo-optimization with proof
+ MODE_VERBOSITY:
    + 0 - Silent
    + 1 - Input and output to stdout (default)
    + 2 - General calculation defaults to stdout
    + 3 - Every little detail to stdout

Examples:
------------------------------------------------------------------------------
Two examples are provided. The first is a simple square lattice with a
repulsive nearest-neighbor term, attractive next-nearest neighbor term,
and slightly repulsive next-nearest-neighbor triplet.

The second example is analogous to the cluster expansion provided for the
Li-graphite system in [Persson et al, PRB 82, 125416 (2010)](http://journals.aps.org/prb/abstract/10.1103/PhysRevB.82.125416).
 It is a 2D cluster expansion on a triangular lattice, with pair terms only.
