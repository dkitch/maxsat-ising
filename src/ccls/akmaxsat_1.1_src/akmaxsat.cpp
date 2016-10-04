/*
   <akmaxsat: a (partial) (weighted) MAX-SAT solver>
    Copyright (C) 2010 Adrian Kuegel

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/

#include <string.h>
#include <limits.h>
#include <string>
#include <iostream>
#include <cstdio>
#include <algorithm>
#include <fstream>
#include <assert.h>
#include <time.h>
#include <stdlib.h>
#include "cnf_formula.hpp"
using namespace std;

//! \file akmaxsat.cpp Documentation of the maxsat solver

#ifdef RBFS
void rbfs(CNF_Formula<long long> &cf) {
	int *variable_stack = new int[cf.getNVars()];
	int *todo = new int[cf.getNVars()];
	ULL *f = new ULL[cf.getNVars()+1];
	ULL *F = new ULL[cf.getNVars()+1];
	ULL *f2 = new ULL[cf.getNVars()+1];
	ULL *F2 = new ULL[cf.getNVars()+1];
	ULL *b = new ULL[cf.getNVars()+1];
	int *pos = new int[cf.getNVars() + 1];
	int *variables = new int[cf.getNVars()];
	int variable_stack_len = 0;
	b[0] = MAXWEIGHT;
	F[0] = f[0] = cf.bestMinusLowerBound();
	int L, p;
	int branch_cnt = 0, propagate_cnt = 0;
	long double besthvalue;
	bool found;
	vector< pair<long long, int_c> > tv;
	for (int i=1; i<=cf.getNVars(); ++i) {
		double hv1 = cf.getBinaryLength(i)*2+cf.getUnitLength(i)+cf.getLength(i);
		double hv2 = cf.getBinaryLength(-i)*2+cf.getUnitLength(-i)+cf.getLength(-i);
		tv.push_back(make_pair(hv1*hv1+min(hv1, hv2), i));
	}
	sort(tv.begin(), tv.end());
	int sign = 0;
	int ind;
	int nvariables = cf.getNVars();
	for (int i=0; i<nvariables; ++i) {
		variables[i] = tv[i].second;
		pos[tv[i].second] = i;
	}
	int *pit = variables + nvariables - 1;
	do {
	//	printf("%d %llu %llu %llu\n", variable_stack_len, f[variable_stack_len], F[variable_stack_len], b[variable_stack_len]);
		if (f[variable_stack_len] > b[variable_stack_len]) {
			F[variable_stack_len] = f[variable_stack_len];
			goto goback;
		}
		if (variable_stack_len == cf.getNVars())
			break;
#ifdef PROP_LIST
		L = cf.propagateLiteral();
		if (L != 0) {
			if (!cf.assignLiteral(L))
				goto goback;
			++propagate_cnt;
			variable_stack[variable_stack_len] = abs(L);
			todo[variable_stack_len++] = 0;
			F[variable_stack_len] = f[variable_stack_len] = cf.bestMinusLowerBound();
			b[variable_stack_len] = b[variable_stack_len-1];
			if (f[variable_stack_len-1] < F[variable_stack_len-1] && F[variable_stack_len-1] > F[variable_stack_len])
				F[variable_stack_len] = F[variable_stack_len-1];
			p = pos[abs(L)];
			assert(p >= 0);
			if (p != nvariables-1) {
				variables[p] = variables[nvariables-1];
				pos[variables[p]] = p;
			}
			--nvariables;
			continue;
		}
#endif
		found = false;
		if (nvariables < 5000)
			pit = variables + nvariables-1;
		if (pit >= variables + nvariables)
			pit = variables + nvariables-1;
		for (; pit>=variables; --pit) {
			long long lneg = cf.getLength(-*pit);
			long long lpos = cf.getLength(*pit);
			// check if -i can be discarded
			if (cf.getUnitLength(*pit) >= lneg) {
				if (!cf.assignLiteral(*pit))
					goto goback;
				assert(pos[*pit] == pit - variables);
				++propagate_cnt;
				variable_stack[variable_stack_len] = *pit;
				*pit = variables[nvariables-1];
				pos[*pit] = pit - variables;
				--nvariables;
				todo[variable_stack_len++] = 0;
				b[variable_stack_len] = b[variable_stack_len-1];
				F[variable_stack_len] = f[variable_stack_len] = cf.bestMinusLowerBound();
				if (f[variable_stack_len-1] < F[variable_stack_len-1] && F[variable_stack_len-1] > F[variable_stack_len])
					F[variable_stack_len] = F[variable_stack_len-1];
				found = true;
				break;
			}
			// check if +i can be discarded
			else if (cf.getUnitLength(-*pit) >= lpos) {
				if (!cf.assignLiteral(-*pit))
					goto goback;
				assert(pos[*pit] == pit - variables);
				++propagate_cnt;
				variable_stack[variable_stack_len] = *pit;
				*pit = variables[nvariables-1];
				pos[*pit] = pit - variables;
				--nvariables;
				todo[variable_stack_len++] = 0;
				b[variable_stack_len] = b[variable_stack_len-1];
				F[variable_stack_len] = f[variable_stack_len] = cf.bestMinusLowerBound();
				if (f[variable_stack_len-1] < F[variable_stack_len-1] && F[variable_stack_len-1] > F[variable_stack_len])
					F[variable_stack_len] = F[variable_stack_len-1];
				found = true;
				break;
			}
		}
		if (found)
			continue;
		ind = 0;
		if (nvariables >= 3000) {
			ind = variables[nvariables-1];
			if (cf.getW_lb(ind) + cf.getUnitLength(ind) + cf.getBinaryLength(ind) > cf.getW_lb(-ind)+cf.getUnitLength(-ind)+cf.getBinaryLength(-ind))
				sign = 1;
			else
				sign = -1;
		}
		else {
			besthvalue = -1;
			assert(nvariables > 0);
			for (int *it=variables+nvariables-1; it>=variables; --it) {
				assert(pos[*it] == it - variables);
				long long lneg = cf.getLength(-*it);
				long long lpos = cf.getLength(*it);
				long double hv1 = cf.getW_lb(*it) + cf.getBinaryLength(*it) + lpos;
				assert(hv1 >= 0);
				long double hv2 = cf.getW_lb(-*it) + cf.getBinaryLength(-*it) + lneg;
				assert(hv2 >= 0);
				if (hv1 * hv2 + min(lpos, lneg) >= besthvalue) {
					besthvalue = hv1 * hv2 + min(lpos, lneg);
					ind = *it;
			//		if (lneg > lpos)
					if (hv2 > hv1)
						sign = -1;
					else
						sign = 1;
				}
			}
		}
		assert(ind != 0);
		todo[variable_stack_len] = sign * ind;
		variable_stack[variable_stack_len++] = ind;
		cf.assignLiteral(-sign * ind);
		F2[variable_stack_len] = f2[variable_stack_len] = cf.bestMinusLowerBound();
		if (F[variable_stack_len-1] > f[variable_stack_len-1] && F[variable_stack_len-1] > F2[variable_stack_len])
			F2[variable_stack_len] = F[variable_stack_len-1];
		cf.unassignLiteral();
		cf.assignLiteral(sign * ind);
		F[variable_stack_len] = f[variable_stack_len] = cf.bestMinusLowerBound();
		if (F[variable_stack_len-1] > f[variable_stack_len-1] && F[variable_stack_len-1] > F[variable_stack_len])
			F[variable_stack_len] = F[variable_stack_len-1];
		if (F2[variable_stack_len] < F[variable_stack_len]) {
			todo[variable_stack_len-1] *= -1;
			swap(F2[variable_stack_len], F[variable_stack_len]);
			swap(f2[variable_stack_len], f[variable_stack_len]);
			cf.unassignLiteral();
			cf.assignLiteral(-sign * ind);
			ULL temp = cf.bestMinusLowerBound();
			if (temp > f[variable_stack_len]) {
				if (temp > f2[variable_stack_len])
					temp = f2[variable_stack_len];
				f[variable_stack_len] = temp;
				if (temp > F[variable_stack_len]) {
					F[variable_stack_len] = temp;
					if (F[variable_stack_len-1] > f[variable_stack_len-1] && F[variable_stack_len-1] > F[variable_stack_len])
						F[variable_stack_len] = F[variable_stack_len-1];
				}
			}
		}
		b[variable_stack_len] = min(b[variable_stack_len-1], F2[variable_stack_len]);
		++branch_cnt;
		p = pos[ind];
		assert(p >= 0);
		variables[p] = variables[nvariables-1];
		pos[variables[p]] = p;
		--nvariables;
		continue;
goback:
		while(variable_stack_len) {
			cf.unassignLiteral();
			if (todo[variable_stack_len-1]) {
				if (F[variable_stack_len] > F2[variable_stack_len]) {
					swap(F[variable_stack_len], F2[variable_stack_len]);
					swap(f[variable_stack_len], f2[variable_stack_len]);
					if (F[variable_stack_len] <= b[variable_stack_len-1]) {
						todo[variable_stack_len-1] *= -1;
						b[variable_stack_len] = min(b[variable_stack_len-1], F2[variable_stack_len]);
						cf.assignLiteral(todo[variable_stack_len-1]);
						ULL temp = cf.bestMinusLowerBound();
						if (temp > f[variable_stack_len]) {
							if (temp > f2[variable_stack_len])
								temp = f2[variable_stack_len];
							f[variable_stack_len] = temp;
							if (temp > F[variable_stack_len]) {
								F[variable_stack_len] = temp;
								if (F[variable_stack_len-1] > f[variable_stack_len-1] && F[variable_stack_len-1] > F[variable_stack_len])
									F[variable_stack_len] = F[variable_stack_len-1];
							}
						}
						break;
					}
				}
				else
					assert(F[variable_stack_len] > b[variable_stack_len-1]);
			}
			assert(F[variable_stack_len] > b[variable_stack_len]);
			assert(F[variable_stack_len] >= F[variable_stack_len-1]);
			F[variable_stack_len-1] = F[variable_stack_len];
			--variable_stack_len;
			pos[variable_stack[variable_stack_len]] = nvariables;
			variables[nvariables++] = variable_stack[variable_stack_len];
		}
	}while(variable_stack_len);
	printf("c %d branches %d propagates\n", branch_cnt, propagate_cnt);
	delete [] variable_stack;
	delete [] todo;
	delete [] F2;
	delete [] F;
	delete [] f2;
	delete [] f;
	delete [] b;
	delete [] variables;
	delete [] pos;
}

#else

void fast_backtrack(CNF_Formula<long long> &cf) {
	int *variable_stack = new int[cf.getNVars()];
	int *todo = new int[cf.getNVars()];
	int *pos = new int[cf.getNVars() + 1];
	int *variables = new int[cf.getNVars()];
	int variable_stack_len = 0;
	int L, p;
	int branch_cnt = 0, propagate_cnt = 0;
	long double besthvalue;
	bool found;
	bool do_lb_calc = false;//cf.getNVars() <= 200 || (cf.getBestCost() < cf.getHardWeight());
	bool firstlb = true;
	vector< pair<long long, int_c> > tv;
	for (int i=1; i<=cf.getNVars(); ++i) {
		double hv1 = cf.getBinaryLength(i)*2+cf.getUnitLength(i)+cf.getLength(i);
		double hv2 = cf.getBinaryLength(-i)*2+cf.getUnitLength(-i)+cf.getLength(-i);
		tv.push_back(make_pair(hv1*hv1+min(hv1, hv2), i));
	}
	sort(tv.begin(), tv.end());
	int sign = 0;
	int ind;
	int nvariables = cf.getNVars();
	for (int i=0; i<nvariables; ++i) {
		variables[i] = tv[i].second;
		pos[tv[i].second] = i;
	}
	int *pit = variables + nvariables - 1;
	do {
		if (variable_stack_len == cf.getNVars()) {
			do_lb_calc = true;
			goto goback;
		}
#ifdef PROP_LIST
		L = cf.propagateLiteral();
		if (L != 0) {
			if (!cf.assignLiteral(L))
				goto goback;
			++propagate_cnt;
			variable_stack[variable_stack_len] = abs(L);
			todo[variable_stack_len++] = 0;
			p = pos[abs(L)];
			assert(p >= 0);
			if (p != nvariables-1) {
				variables[p] = variables[nvariables-1];
				pos[variables[p]] = p;
			}
			--nvariables;
			continue;
		}
#endif
		firstlb = false;
		if (!cf.bestMinusLowerBound())
			goto goback;
#ifdef PROP_LIST
		L = cf.propagateLiteral();
		if (L != 0) {
			if (!cf.assignLiteral(L))
				goto goback;
			++propagate_cnt;
			variable_stack[variable_stack_len] = abs(L);
			todo[variable_stack_len++] = 0;
			p = pos[abs(L)];
			assert(p >= 0);
			if (p != nvariables-1) {
				variables[p] = variables[nvariables-1];
				pos[variables[p]] = p;
			}
			--nvariables;
			continue;
		}
#endif
		found = false;
		if (nvariables < 5000)
			pit = variables + nvariables-1;
		if (pit >= variables + nvariables)
			pit = variables + nvariables-1;
		for (; pit>=variables; --pit) {
			long long lneg = cf.getLength(-*pit);
			long long lpos = cf.getLength(*pit);
			// check if -i can be discarded
			if (cf.getUnitLength(*pit) >= lneg) {
				if (!cf.assignLiteral(*pit))
					goto goback;
				assert(pos[*pit] == pit - variables);
				++propagate_cnt;
				variable_stack[variable_stack_len] = *pit;
				*pit = variables[nvariables-1];
				pos[*pit] = pit - variables;
				--nvariables;
				todo[variable_stack_len++] = 0;
				found = true;
				break;
			}
			// check if +i can be discarded
			else if (cf.getUnitLength(-*pit) >= lpos) {
				if (!cf.assignLiteral(-*pit))
					goto goback;
				assert(pos[*pit] == pit - variables);
				++propagate_cnt;
				variable_stack[variable_stack_len] = *pit;
				*pit = variables[nvariables-1];
				pos[*pit] = pit - variables;
				--nvariables;
				todo[variable_stack_len++] = 0;
				found = true;
				break;
			}
		}
		if (found)
			continue;
		ind = 0;
		if (nvariables >= 3000) {
			ind = variables[nvariables-1];
			if (cf.getW_lb(ind) + cf.getUnitLength(ind) + cf.getBinaryLength(ind) > cf.getW_lb(-ind)+cf.getUnitLength(-ind)+cf.getBinaryLength(-ind))
				sign = 1;
			else
				sign = -1;
		}
		else {
			besthvalue = -1;
			assert(nvariables > 0);
			for (int *it=variables+nvariables-1; it>=variables; --it) {
				assert(pos[*it] == it - variables);
				long long lneg = cf.getLength(-*it);
				long long lpos = cf.getLength(*it);
				long double hv1 = cf.getW_lb(*it) + cf.getBinaryLength(*it) + lpos;
				assert(hv1 >= 0);
				long double hv2 = cf.getW_lb(-*it) + cf.getBinaryLength(-*it) + lneg;
				assert(hv2 >= 0);
				if (hv1 * hv2 + min(lpos, lneg) >= besthvalue) {
					besthvalue = hv1 * hv2 + min(lpos, lneg);
					ind = *it;
			//		if (lneg > lpos)
					// todo: check what happens if we choose randomly the first 3 variables
					/*
					if (variable_stack_len <= 2) {
						if (rand() < RAND_MAX/2)
							sign = 1;
						else
							sign = -1;
					}
					else {
					*/
						if (hv2 > hv1)
							sign = -1;
						else
							sign = 1;
				//	}
				}
			}
		}
		assert(ind != 0);
		todo[variable_stack_len] = -sign * ind;
		if (!cf.assignLiteral(ind * sign)) {
			if (!cf.assignLiteral(ind * -sign))
				goto goback;
			todo[variable_stack_len] = 0;
		}
		++branch_cnt;
//		if (branch_cnt % 10000 == 0)
//			printf("c sofar %d branches\n", branch_cnt);
		variable_stack[variable_stack_len++] = ind;
		p = pos[ind];
		assert(p >= 0);
		variables[p] = variables[nvariables-1];
		pos[variables[p]] = p;
		--nvariables;
		continue;
goback:
		while(variable_stack_len) {
			--variable_stack_len;
			cf.unassignLiteral();
			if (todo[variable_stack_len])
				if (cf.assignLiteral(todo[variable_stack_len])) {
					todo[variable_stack_len++] = 0;
					break;
				}
			pos[variable_stack[variable_stack_len]] = nvariables;
			variables[nvariables++] = variable_stack[variable_stack_len];
		}
	}while(variable_stack_len);
	printf("c %d branches %d propagates\n", branch_cnt, propagate_cnt);
	delete [] variable_stack;
	delete [] todo;
	delete [] variables;
	delete [] pos;
}

#endif

int main(int argc, char **argv) {
	srand(time(0));
	if (argc < 2) {
		printf("usage: %s <cnf-file> [upper bound file]\n", argv[0]);
		return 1;
	}
	ifstream istr(argv[1]);
	CNF_Formula<long long> cf(istr);
#ifdef FORCE_LS
	char command[1000];
	char folder[1000];
	char file[1000];
	char *p = argv[1];
	while(strchr(p, '/') != NULL)
		p = strchr(p, '/') + 1;
	sprintf(folder, "/tmp/akmaxsat %d %s/", getpid(), p);
	sprintf(command, "mkdir \"%s\"", folder);
	system(command);
	sprintf(file, "%s%s", folder,p);
	if (cf.isWeighted())
		sprintf(command, "./ubcsat -alg irots -w -seed 0 -runs 10 -cutoff %d -r bestsol -r out /dev/null -inst %s > \"%s\"", min(100*cf.getNVars(), 100000), argv[1], file);
	else
		sprintf(command, "./ubcsat -alg irots -seed 0 -runs 10 -cutoff %d -r bestsol -r out /dev/null -inst %s > \"%s\"", min(100*cf.getNVars(), 100000), argv[1], file);
	system(command);
	ifstream istr2(file);
#else	
	if (argc > 2) {
		ifstream istr2(argv[2]);
#endif
		ULL bestCost = cf.getHardWeight();
		string s;
		istr2 >> s;
#ifndef FORCE_LS
		if (s == "#") {
#endif
			getline(istr2, s);
			ULL t;
			string best;
			for (int i=0; i<10; ++i) {
				istr2 >> s >> s >> t;
				if (t < bestCost) {
					istr2 >> best;
					bestCost = (ULL)t;
				}
				else
					istr2 >> s;
			}
			if (best.size() > 0) {
				char *bestA = new char[best.size() + 1];
				for (int i=0; i<(int)best.size(); ++i)
					if (best[i] == '0')
						bestA[i + 1] = -1;
					else
						bestA[i + 1] = 1;
				cf.saveBest(bestCost, bestA);
				delete [] bestA;
			}
#ifndef FORCE_LS
		}
		else {
			while(s != "Solution")
				istr2 >> s;
			ULL t;
			istr2 >> s >> t;
			while(istr2 >> s && s != "v");
			if (t < bestCost) {
				bestCost = (ULL)t;
				char *bestA = new char[cf.getNVars() + 1];
				for (int i=1; i<=cf.getNVars(); ++i) {
					int t;
					istr2 >> t;
					assert(t == i || t == -i);
					bestA[i] = (t > 0? 1 : -1);
				}
				cf.saveBest(bestCost, bestA);
				delete [] bestA;
			}
		}
#endif
		cout << "c initialized bestCost to " << bestCost << endl;
		cout << "o " << bestCost << endl;
#ifdef FORCE_LS
		remove(file);
		remove(folder);
    
#else
	}
#endif

	if (argc > 2) //luo
	{ //luo
		string my_result_file = argv[2]; //luo
		string my_command = "rm -f " + my_result_file; //luo
		system(my_command.c_str()); //luo
		sscanf(argv[3],"%llu",&first_lower_bound_threshold); //luo
		printf("c first_lower_bound_threshold = %llu\n", first_lower_bound_threshold); //luo
	} //luo

#ifdef RBFS
	rbfs(cf);
#else
	fast_backtrack(cf);
#endif
	cf.printSolution();
	return 0;
}
