/* This module defines overall interface to the generalized Ising solver.
 * See the README for the meaning of input flags, input files, and installation
 *
 * Author: Wenxuan Huang
 * Maintainer: Wenxuan Huang, Daniil Kitchaev
 * Date: 15 March, 2015
 *
 * Copyright: Wenxuan Huang (C) 2014, All rights reserved.
 */

#include <iostream>
#include <fstream>
#include <sstream>
#include <streambuf>
#include <string>
#include <stdio.h>
#include <vector>
#include <set>
#include <map>
#include "gurobi_c++.h"
#include "boost/tuple/tuple.hpp"
#include "boost/tuple/tuple_comparison.hpp"
#include "boost/tuple/tuple_io.hpp"
#include <boost/lexical_cast.hpp>
#include "solver.h"

using namespace std;
using namespace ::boost::tuples;
using namespace ::boost;

void read_from_file(std::string &id,
                     int &max_sites,
                     map< set<tuple<int,int,int,int,int> >, double> &J,
                     double &prec,
                     int &num_loops,
                     bool &translation_algorithm,
                     bool &basic_exact_mode,
                     bool &pseudo_mode,
                     bool &pseudo_mode_with_proof,
                     bool &verbose,
                     bool &very_verbose,
                     bool &obscenely_verbose);

int main (void) {
    std::string id="IS0";
    int max_sites = 50;
    int num_loops = 4;
    double prec = 0.00001;
    bool translation_algorithm = false;
    bool basic_exact_mode = false;
    bool pseudo_mode = true;
    bool pseudo_mode_with_proof = false;
    bool verbose = true;
    bool very_verbose = false;
    bool obscenely_verbose = false;

    double lower_bound, upper_bound, exact_lowerbound;

    map< set<tuple<int,int,int,int,int> >, double> J, lowerboundclustertype, upperboundclustertype, J_for_proof;
    map< tuple<int,int,int,int>,int> unitcell;
    tuple<int,int,int,int,int,int> periodicity;
    map< tuple<int,int,int,int>, int> cellrepresentation;

    read_from_file(id, max_sites, J, prec, num_loops, translation_algorithm,
                   basic_exact_mode, pseudo_mode, pseudo_mode_with_proof,
                   verbose, very_verbose, obscenely_verbose);

    run_solver(max_sites, J,
               lowerboundclustertype, upperboundclustertype, cellrepresentation,
               lower_bound, upper_bound, exact_lowerbound, unitcell, periodicity,
               J_for_proof,
               id,
               prec, num_loops,
               basic_exact_mode, pseudo_mode, pseudo_mode_with_proof,
               verbose, very_verbose, obscenely_verbose);

    return 0;
}

void read_from_file(std::string &id,
                     int &max_sites,
                     map< set<tuple<int,int,int,int,int> >, double> &J,
                     double &prec,
                     int &num_loops,
                     bool &translation_algorithm,
                     bool &basic_exact_mode,
                     bool &pseudo_mode,
                     bool &pseudo_mode_with_proof,
                     bool &verbose,
                     bool &very_verbose,
                     bool &obscenely_verbose) {
	map< set<tuple<int,int,int,int,int> >, double> J_negative1_positive1;
	set< tuple<int,int,int,int,int> >setoftupletemp;
	double constant_term = 0;
	int solver_mode = 1;
	int verbosity = 1;

	std::ifstream t2("J_config.in");
	std::stringstream buffer2;
	buffer2 << t2.rdbuf();
	string J_config_file=buffer2.str();

	vector<string> J_config_line;
	split_is(J_config_file, '\n', J_config_line);
	for (vector<string>::iterator it=J_config_line.begin(); it!=J_config_line.end(); it++) {
		vector<string> J_config_line_segment;
		string temp=*it;
		split_is(temp, ' ', J_config_line_segment);
		vector<string>::iterator segment_iterator=J_config_line_segment.begin();
		string first_segment=*segment_iterator;
		vector<string> equal_left_right;
		split_is(first_segment, '=', equal_left_right);
		vector<string>::iterator equal_iterator=equal_left_right.begin();
		string equal_left=*equal_iterator;
		equal_iterator++;
		string equal_right=*equal_iterator;

		if (equal_left=="NSITES") {
			max_sites=lexical_cast<int>(equal_right) ;
		}else if (equal_left=="NLOOPS") {
			num_loops=lexical_cast<int>(equal_right) ;
		}else if (equal_left=="LABEL") {
			id=equal_right;
		}else if (equal_left=="PREC") {
			prec=lexical_cast<double>(equal_right) ;
		}else if (equal_left=="MODE_JPLUSMINUS") {
			translation_algorithm=lexical_cast<bool>(equal_right) ;
		}else if (equal_left=="MODE_SOLVER") {
			solver_mode=lexical_cast<int>(equal_right) ;
		}else if (equal_left=="MODE_VERBOSITY") {
			verbosity = lexical_cast<int>(equal_right) ;
		}
	}

	if (solver_mode == 0) {
		basic_exact_mode = true;
		pseudo_mode = false;
		pseudo_mode = false;
	}else if (solver_mode == 1) {
		basic_exact_mode = false;
		pseudo_mode = true;
		pseudo_mode_with_proof = false;
	}else if (solver_mode == 2) {
		basic_exact_mode = false;
		pseudo_mode = true;
		pseudo_mode_with_proof = true;
	}else{
		cout << "Invalid solver mode given. Exiting." << endl;
		exit(1);
	}

	if (verbosity == 0) {
		verbose = false;
		very_verbose = false;
		obscenely_verbose = false;
	}else if (verbosity == 1) {
		verbose = true;
		very_verbose = false;
		obscenely_verbose = false;
	}else if (verbosity == 2) {
		verbose = true;
		very_verbose = true;
		obscenely_verbose = false;
	}else if (verbosity == 3) {
		verbose = true;
		very_verbose = true;
		obscenely_verbose = true;
	}else {
		cout << "Invalid verbosity mode given. Exiting." << endl;
		exit(1);
	}

	std::ifstream t1("J_in.in");
	std::stringstream buffer1;
	buffer1 << t1.rdbuf();
	string J_in_file=buffer1.str();

	vector<string> J_in_line;
	split_is(J_in_file, '\n', J_in_line);
	int line_format_indicator=0;
	for (vector<string>::iterator it=J_in_line.begin(); it!=J_in_line.end(); it++){
		string this_line=*it;
		if (it==J_in_line.begin()){
			vector<string> segment;
			split_is(this_line, ' ', segment);
			vector<string>::iterator segment_iterator=segment.begin();
			string temp_segment=*segment_iterator;
			if (temp_segment=="Constant"){
				segment_iterator++;
				constant_term=lexical_cast<double>(*segment_iterator);
			}
		}else{
			if (line_format_indicator==0) {
				vector<string> segment;
				split_is(this_line, ' ', segment);
				vector<string>::iterator segment_iterator=segment.begin();
				string temp_segment=*segment_iterator;
				if (temp_segment=="Cluster") {
					line_format_indicator=1;
				}
			}else if (line_format_indicator==1){
				setoftupletemp.clear();
				vector<string> segment;
				split_is(this_line, ' ', segment);

				for (vector<string>::iterator it2=segment.begin(); it2!=segment.end(); it2++) {
					string this_segment=*it2;
					vector<string> number_vector;
					split_is(this_segment, ',', number_vector);
					int l1,l2,l3,l4,l5;
					l1=lexical_cast<int>(number_vector[0]);
					l2=lexical_cast<int>(number_vector[1]);
					l3=lexical_cast<int>(number_vector[2]);
					l4=lexical_cast<int>(number_vector[3]);
					l5=lexical_cast<int>(number_vector[4]);
					setoftupletemp.insert(make_tuple(l1,l2,l3,l4,l5));
				}

				line_format_indicator=2;
			}else if (line_format_indicator==2) {
				vector<string> segment;
				split_is(this_line, '=', segment);

				if (translation_algorithm){
					J_negative1_positive1[setoftupletemp]=lexical_cast<double>(segment[1]);
				}else{
					J[setoftupletemp]=lexical_cast<double>(segment[1]);
				}

				line_format_indicator=0;
			}
		}
	}

	if(translation_algorithm){
		convertJ_neg1_pos1toJ(J_negative1_positive1, J, constant_term);
	}
}
