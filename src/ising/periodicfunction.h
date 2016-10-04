/* This module defines the upper bound (periodic) solver for the generalized Ising model.
 *
 * Author: Wenxuan Huang
 * Maintainer: Wenxuan Huang, Daniil Kitchaev
 * Date: 15 March, 2015
 *
 * Copyright: Wenxuan Huang (C) 2014, All rights reserved.
 */

#ifndef PERIODICFUNCTION_H
#define PERIODICFUNCTION_H

#include <iostream>
#include <fstream>
#include <sstream>
#include <string>
#include <stdlib.h>
#include <map>
#include <set>
#include <vector>
#include <algorithm>
#include "gurobi_c++.h"
#include <boost/lexical_cast.hpp>
#include "boost/tuple/tuple.hpp"
#include "boost/tuple/tuple_comparison.hpp"
#include "boost/tuple/tuple_io.hpp"
#include <boost/lexical_cast.hpp>
#include "tools.h"

using namespace std;
using namespace ::boost::tuples;
using namespace ::boost;

void periodic(int a0, int a1, int a2, int a3, int a4, int a5,
              map<set<tuple<int,int,int,int,int> >, double> &J,
              int xrange, int yrange, int zrange,
              map<int,int> componentnumber,
              map<tuple<int,int,int,int>,int> &spin,
              double &averageenergy,
              map< tuple<int,int,int,int,int,int>, map<set<tuple<int,int,int,int,int> >, double> > &clustertypeperiodic,
              double min_so_far,
              std::string id,
              bool stop_at_first_iteration,
              bool stop_when_upperbound_smaller_than_predicted_lower_bound,
              bool stop_till_exact_result,
              bool obscenely_verbose);

#endif



