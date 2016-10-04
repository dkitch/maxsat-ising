/* This module defines the general Ising solver procedure and provides
 * an interface for calling the solver with a defined Hamiltonian, in the
 * form of a set of ECI's, and a constraint on the maximum size of the
 * desired solution.
 *
 * Author: Wenxuan Huang
 * Maintainer: Wenxuan Huang, Daniil Kitchaev
 * Date: 15 March, 2015
 *
 * Copyright: Wenxuan Huang (C) 2014, All rights reserved.
 */

#ifndef SOLVER_H
#define SOLVER_H

#include <iostream>
#include <sstream>
#include <fstream>
#include <streambuf>
#include <string>
#include <vector>
#include <map>
#include <set>
#include "gurobi_c++.h"
#include "boost/tuple/tuple.hpp"
#include "boost/tuple/tuple_comparison.hpp"
#include "boost/tuple/tuple_io.hpp"
#include <boost/lexical_cast.hpp>
#include "periodicfunction.h"
#include "lowerbound.h"
#include "tools.h"

using namespace std;
using namespace ::boost::tuples;
using namespace ::boost;

void run_solver(int max_sites,
                map< set< tuple<int,int,int,int,int> >, double> &J,
                map< set< tuple<int,int,int,int,int> >, double> &lowerboundclustertype,
                map< set< tuple<int,int,int,int,int> >, double> &upperboundclustertype,
                map< tuple<int,int,int,int>, int> &cellrepresentation,
                double &lower_bound,
                double &exact_lower_bound,
                double &upper_bound,
                map< tuple<int,int,int,int>, int> &unitcell,
                tuple <int,int,int,int,int,int> &periodicity,
                map< set< tuple<int,int,int,int,int> >, double> &J_for_proof,
                std::string id,
                double prec = 1000000.0,
                int num_loops = 4,
                bool basic_exact_mode = false,
                bool pseudo_mode = true,
                bool pseudo_mode_with_proof = false,
                bool verbose = true,
                bool very_verbose = false,
                bool obscenely_verbose = false);

void corecode(map<int, int> component,
              int xrange, int yrange, int zrange,
              int Ncomp,
              int loopnumber,
              map<set<tuple<int,int,int,int,int> >, double> &J,
              map<set<tuple<int,int,int,int,int> >, double> &lowerboundclustertype,
              map<set<tuple<int,int,int,int,int> >, double> &upperboundclustertype,
              map<tuple<int,int,int,int>,int> &cellrepresentation,
              double &lower_bound, double &upper_bound,
              map<tuple<int,int,int,int>,int> &unitcell,
              tuple<int,int,int,int,int,int> &periodicity,
              map<set<tuple<int,int,int,int,int> >, double> &J_for_proof,
              std::string id,
              bool pseudo_mode,
              bool pseudo_mode_with_proof,
              bool basic_exact_mode,
              bool very_verbose,
              bool obscenely_verbose);

void calculate_range_from_J(map<set<tuple<int,int,int,int,int> >, double> &J,
                                                 int &xrange, int &yrange, int &zrange,
                                                 map<int, int> &component);
#endif
