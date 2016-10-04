/* This module defines the lower bound solver for the generalized Ising model.
 *
 * Author: Wenxuan Huang
 * Maintainer: Wenxuan Huang, Daniil Kitchaev
 * Date: 15 March, 2015
 *
 */

#ifndef LOWERBOUND_H
#define LOWERBOUND_H

#include <iostream>
#include <sstream>
#include <string>
#include <map>
#include <set>
#include <vector>
#include <algorithm>
#include "gurobi_c++.h"
#include "boost/tuple/tuple.hpp"
#include "boost/tuple/tuple_comparison.hpp"
#include "boost/tuple/tuple_io.hpp"
#include <boost/lexical_cast.hpp>
#include "tools.h"

using namespace std;
using namespace ::boost::tuples;
using namespace ::boost;

void get_lowerbound(int a0,int a1,int a2,int a3,int a4,int a5,
                 map<set<tuple<int,int,int,int,int> >, double> &J,
                 int xrange,int yrange,int zrange,
                 map<int,int> componentnumber,
                 map<tuple<int,int,int,int>,int> &spin,
                 double &averageenergy,
                 map<tuple<int,int,int,int,int,int>, map<set<tuple<int,int,int,int,int> >, double> > &clustertypeperiodic,
                 map<set<tuple<int,int,int,int,int> >, double> &J_for_proof,
                 std::string id,
                 bool pseudo_mode,
                 bool pseudo_mode_with_proof,
                 bool basic_exact_mode,
                 bool obscenely_verbose);

void get_lowerbound_sub(int a0,int a1,int a2,int a3,int a4,int a5,
                    map<set<tuple<int,int,int,int,int> >, double> &J,
                    int xrange,int yrange,int zrange,
                    map<int,int> componentnumber,
                    map<tuple<int,int,int,int>,int> &spin,
                    double &averageenergy,
                    map<tuple<int,int,int,int,int,int>, map<set<tuple<int,int,int,int,int> >, double> > &clustertypeperiodic,
                    double LB_so_far,
                    std::string id,
                    bool stop_at_first_iteration,
                    bool stop_when_upperbound_smaller_than_predicted_lower_bound,
                    bool stop_till_exact_result,
                    bool obscenely_verbose);

#endif

