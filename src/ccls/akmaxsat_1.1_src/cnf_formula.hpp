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

#ifndef CNF_FORMULA_HPP_INCLUDE

#define CNF_FORMULA_HPP_INCLUDE

#include "clauses.hpp"
#include "restore_list.hpp"
#include <cstdio>
#include <cmath>
#include <vector>
#include <set>
#include <utility>
using namespace std;

unsigned long long first_lower_bound_threshold;
int first_checked=0;

//! The class CNF_Formula maintains the states of the CNF_Formula during backtracking
template<class TL> class CNF_Formula {
	// private variables
	//! clause number to indicate a unit clause
	const static int UNIT_CLAUSE = 1;
#ifdef FUIP
	vector<int> bla;
	vector<int> *tadj;
	int succ_cnt_fuip, total_cnt_fuip;
	int *Q2;
	char *visit2;
	int *ref_cnt;
#endif
#ifdef STATS
	int *explored;
	long long *sum_cost;
#endif
	//! all clauses of the CNF formula
	Clauses all_clauses;
	//! boolean flag which indicates if the given formula has weighted clauses or default weight 1
	bool isWcnf;
	//! number of Variables in the formula
	int nVars;
	//! contains a list of pointers to clauses in which literal i occurs
	vector<int> *appears;
	//! contains a list of clauses implying unit literal i
	vector<int> *unit_implication_list;
	//! contains the current size of each appears vector
	int *appears_len;
	//! contains the values assigned to the variables
	char *assigned_values;
	//! contains the best values assigned to the variables
	char *bestA;
	//! number of assigned literals
	int n_assigned;
	//! stack of assigned literals
	int *assigned_literals;
	//! timestamp
	long long timestamp;
	//! timestamps when appears array was last traversed
	long long *appears_traversed;
	//! weight of unit clauses which contain literal i
	TL *W_unit;
	//! weight of binary clauses which contain literal i
	TL *W_binary;
	//! weight of clauses of length > 2 which contain literal i
	TL *W_large;
	//! sum of clause weights of clauses containing literal i contained in inconsistent subformulas detected in lower bound calculation
	TL *W_lb;
	//! saved weight of unit clauses with literal i
	TL *W_unit_save;
	//! cost of current partial assignment
	ULL *cost;
	//! best cost of a complete assignment
	ULL bestCost;
	//! difference between current cost and bestCost
	ULL needed_for_skip;
	//! list of clauses which need to be reinserted
	restore_list rlist;
	//! stores data for each literal (depends on function)
	int *literal_data;
	//! stores the clause id of clauses which contain the variables (a, b) at position a * nVars + b
	int *ternary_clause_data;
	//! stores the literals in the order in which they should be selected for propagation
	pair<TL, int> *literal_order;
	//! length of literal_order list
	int l;
	//! stores a stack of processed variables during lower bound calculation with unit propagation
	int *vars;
	//! stores the number of variables on the vars stack
	int vars_top;
	//! stores a list of clauses processed during lower bound computation
	vector<int> take_back;
	//! stores a list of variables processed during lower bound computation
	vector<int> which;
	//! stores a list of clauses of cycle structures
	vector<int> cycle_clauses;
	//! queue of variables used in the function detectConflict
	int *Q;
	//! head of queue
	int head;
	//! tail of queue
	int tail;
	//! old tail of queue
	int oldtail;
	//! hard clause weight (for partial maxsat)
	ULL hard;
	//! maximum input variable
	int maxVn;
	//! maps a variable in compacted variable numbering to the original variables
	int *mapping;
	//! number of an original variable in the compacted variable numbering
	int *maps_to;
	//! total number of generalized unit propagations performed
	int total_gup;
	//! number of generalized unit propagations which produced a lower bound >= bestCost
	int succ_gup;
#ifdef PROP_LIST
	//! stack which contains literals which can be propagated
	int *propagation_stack;
	//! number of literals which can be propagated
	int propagation_stack_size;
	//! position of literal i on the propagation stack
	int *onstack;
#endif
	//! list of clauses which were changed during lower bound calculation
	vector<int> changed;
	// height transform
	vector<double> psi;
	vector<int> *ptr;

	// private functions
	//! Normalize the clause array and determine if it is a tautology
	inline bool normalize_clause_array(vector<int_c> &clause) const {
		sort(clause.begin(), clause.end());
		int len = 0;
		int last = 0;
		for (int i=0; i<(int)clause.size(); ++i) {
			if (clause[i] != last) {
				clause[len++] = clause[i];
				last = clause[i];
			}
			// check if the clause is a tautology (it contains clause[i] and -clause[i])
			if (binary_search(clause.begin()+i, clause.end(), -clause[i]))
				return false;
		}
		clause.resize(len);
		return true;
	}
	//! delete clauses which are fulfilled by setting literal L to true
	inline void deleteFulfilled(int L) {
#ifdef DEBUG
		cout << "delete fulfilled" << endl;
#endif
		assert(!assigned_values[abs(L)]);
		vector<int> &appears2 = appears[L];
		assert(appears_len[L] == (int)appears2.size());
		for (int i=appears2.size()-1; i>=0; --i) {
			int &it = appears2[i];
			// remove clauses which already have a delete flag
			if (all_clauses.getDeleteFlag(it)) {
				if (all_clauses.getSpecialFlag(it))
					all_clauses.decreaseCounter(it);
				it = appears2.back();
				appears2.pop_back();
			}
			else {
				// set the delete flag
				all_clauses.addDeleteFlag2Clause(it);
				assert(all_clauses.getLength(it) > 1);
				// update W_binary
				if (all_clauses.getLength(it) == 2) {
					const int_c *literals = all_clauses.getLiterals(it);
					assert(literals[0] == L || literals[1] == L);
					W_binary[literals[0]] -= all_clauses.getWeight(it);
					W_binary[literals[1]] -= all_clauses.getWeight(it);
#ifdef PROP_LIST
/*
   					// the following lines can be used to find a propagation variable - usually it does not improve speed
					int i = 0;
					if (literals[0] == L)
						i = 1;
					if (onstack[-literals[i]] < 0 && getLength(literals[i]) <= W_unit[-literals[i]]) {
						onstack[-literals[i]] = propagation_stack_size;
						propagation_stack[propagation_stack_size++] = -literals[i];
					}
*/
#endif
				}
				// update W_large
				else {
					const int_c *literals = all_clauses.getLiterals(it);
					ULL w = all_clauses.getWeight(it);
#ifndef NDEBUG
					bool found = false;
#endif
					for (int i=all_clauses.getLength(it)-1; i>=0; --i) {
						W_large[literals[i]] -= w;
#ifndef NDEBUG
						if (literals[i] == L)
							found = true;
#endif
#ifdef PROP_LIST
/*
   						// the following lines can be used to find a propagation variable - usually it does not improve speed
						if (literals[i] != L && onstack[-literals[i]] < 0 && getLength(literals[i]) <= W_unit[-literals[i]]) {
							onstack[-literals[i]] = propagation_stack_size;
							propagation_stack[propagation_stack_size++] = -literals[i];
						}
*/
#endif
					}
					assert(found);
				}
			}
		}
		appears_len[L] = (int)appears2.size();
		// set new time stamp for the appears array
		appears_traversed[L] = timestamp++;
	}
	//! set a to min(a + b, bestCost)
	inline void saveAddition(ULL &a, TL b) const {
		if (a + b < bestCost)
			a = a + (ULL)b;
		else
			a = bestCost;
	}
	//! set a to min(a + b, bestCost)
	inline void saveAddition(ULL &a, ULL b) const {
		if (a + b < bestCost)
			a = a + (ULL)b;
		else
			a = bestCost;
	}
	//! set a to max(a - b, 0)
	inline void saveSubtraction(ULL &a, TL b) const {
		if ((TL)a >= b)
			a = a - (ULL)b;
		else
			a = 0;
	}
	//! set a to max(a - b, 0)
	inline void saveSubtraction(ULL &a, ULL b) const {
		if (a >= b)
			a = a - b;
		else
			a = 0;
	}
	//! remove literal L from clauses in the formula
	inline ULL removeLiteral(int L) {
		assert(L >= -nVars && L <= nVars && L != 0);
#ifdef DEBUG
		cout << "trying to remove literal " << L << endl;
#endif
		assert(W_unit_save[L] == W_unit[L]);
		int l;
		assert((int)appears[L].size() == appears_len[L]);
		appears_traversed[L] = timestamp++;
		vector<int> &appears2 = appears[L];
		for (int i=appears2.size()-1; i>=0; --i) {
			int &it = appears2[i];
			// remove clause with delete flags
			if (all_clauses.getDeleteFlag(it)) {
				if (all_clauses.getSpecialFlag(it))
					all_clauses.decreaseCounter(it);
				it = appears2.back();
				appears2.pop_back();
			}
			else {
				// remove the literal from the clause
				all_clauses.decreaseLength(it);
				l = all_clauses.getLength(it);
				// update W_binary and W_large
				if (l == 2) {
					const int_c *literals = all_clauses.getLiterals(it);
					ULL w = all_clauses.getWeight(it);
					W_binary[literals[0]] += w;
					W_binary[literals[1]] += w;
					W_large[literals[0]] -= w;
					W_large[literals[1]] -= w;
					W_large[L] -= w;
				}
				// update W_unit and W_binary
				else if (l == 1) {
					int literal = *all_clauses.getLiterals(it);
					W_binary[literal] -= all_clauses.getWeight(it);
					W_binary[L] -= all_clauses.getWeight(it);
					W_unit[literal] += all_clauses.getWeight(it);
					W_unit_save[literal] += all_clauses.getWeight(it);
					// unary resolution of literal, -literal may become possible
					unary_resolution(literal);
					assert(!assigned_values[abs(literal)]);
#ifdef PROP_LIST
					// check if literal can be propagated
					if (onstack[literal] < 0 && W_unit[literal] + (TL)cost[n_assigned] >= (TL)bestCost) {
						onstack[literal] = propagation_stack_size;
						propagation_stack[propagation_stack_size++] = literal;
					}
#endif
					// set delete flag for unit clauses
					all_clauses.addDeleteFlag2Clause(it);
				}
			}
		}
		appears_len[L] = (int)appears[L].size();
#ifndef NDEBUG
		for (vector<int>::const_iterator it=appears[L].begin(); it < appears[L].end(); ++it)
			assert(all_clauses.getDeleteFlag(*it) == false || all_clauses.getLength(*it) == 1);
#endif
		return W_unit[L] > (TL)MAXWEIGHT? MAXWEIGHT : (ULL)W_unit[L];
	}
	//! propagate literal -L, set L to false
	inline int propagateLiteral(int L) {
		assert(vars_top >= 0 && L == -vars[vars_top]);
		assert(L >= -nVars && L <= nVars && L != 0);
		assert(!assigned_values[abs(L)]);
#ifdef DEBUG
		printf("propagating %d\n", L);
#endif
		all_clauses.assignVariable(L);
		vector<int> &appears2 = appears[L];
#ifndef NDEBUG
		for (vector<int>::reverse_iterator it=appears2.rbegin(); it<appears2.rbegin()+((int)appears2.size()-appears_len[L]); ++it)
			assert(all_clauses.getDeleteFlag(*it) == true);
#endif
		for (vector<int>::reverse_iterator it=appears2.rbegin() + ((int)appears2.size() - appears_len[L]); it<appears2.rend(); ++it) {
			if (all_clauses.getDeleteFlag(*it)) {
				// in this case, it may be a clause to be deleted, or one which was used in an inconsistent subformula to increase the lower bound
				// we can't distinguish this, so we just move the clause pointer to the end of the list
				// note that we do not need to consider such clauses again when looking for inconsistent subformulas until lower bound calculation has ended and the delete flag gets removed
				--appears_len[L];
				swap(*it, appears2[appears_len[L]]);
			}
			else {
				all_clauses.decreaseLength(*it);
				// check if clause becomes a unit clause
				if (all_clauses.getLength(*it) == 1) {
					const int_c *literals = all_clauses.getLiterals(*it);
					// put literal in the queue
					if (literal_data[*literals] <= 0) {
						Q[tail++] = *literals;
						assert(tail <= 2 * nVars);
						literal_data[*literals] = *it;
					}
				}
			}
		}
		// check if L could be propagated, too -> conflict!
		if (literal_data[L] > 0) {
			assert(literal_data[L] != UNIT_CLAUSE && !all_clauses.getDeleteFlag(literal_data[L]));
			return literal_data[L];
		}
		// if there is a unit literal L, it conflicts with propagating -L
		if (W_unit[L] > 0)
			return literal_data[L] = UNIT_CLAUSE;
		return 0;
	}
	//! add literal L back to clauses where it was removed
	inline void addLiteral(int L) {
		vector<int> &appears2 = appears[L];
		assert((int)appears2.size() == appears_len[L]);
		for (vector<int>::reverse_iterator it=appears2.rbegin(); it<appears2.rend(); ++it) {
			assert(all_clauses.getLength(*it) == 1 || !all_clauses.getDeleteFlag(*it));
			// check if clause was a unit clause
			if (all_clauses.getLength(*it) == 1) {
				int literal = *all_clauses.getLiterals(*it);
				assert(literal != L);
				// now we need to remove the delete flag
				assert(all_clauses.getDeleteFlag(*it));
				all_clauses.removeDeleteFlagFromClause(*it);
				// adjust weights
				W_binary[literal] += all_clauses.getWeight(*it);
				W_binary[L] += all_clauses.getWeight(*it);
				W_unit[literal] -= all_clauses.getWeight(*it);
				W_unit_save[literal] -= all_clauses.getWeight(*it);
#ifdef PROP_LIST
/*
   				// the following lines remove a literal from the propagation stack in case it cannot be propagated anymore
				// usually it is no speedup to do this
				if (onstack[literal] >= 0 && getUnitLength(literal) < getLength(-literal) && W_unit[literal] + (TL)cost[n_assigned + 1] < (TL)bestCost) {
					int pos = onstack[literal];
					if (pos != propagation_stack_size-1) {
						propagation_stack[pos] = propagation_stack[propagation_stack_size-1];
						onstack[propagation_stack[pos]] = pos;
					}
					onstack[literal] = -1;
					--propagation_stack_size;
				}
*/
#endif
				// check if the clause needs to be inserted into the appears list
				// this is the case if the appears list of literal was traversed after L was assigned false (which happened with time stamp appears_traversed[L]
				if (appears_traversed[literal] > appears_traversed[L]) {
					appears[literal].push_back(*it);
					++appears_len[literal];
				}
			}
			// update W_binary and W_large
			else if (all_clauses.getLength(*it) == 2) {
				const int_c *literals = all_clauses.getLiterals(*it);
				ULL w = all_clauses.getWeight(*it);
				W_binary[literals[0]] -= w;
				W_binary[literals[1]] -= w;
				W_large[literals[0]] += w;
				W_large[literals[1]] += w;
				W_large[L] += w;
			}
			// increase the length of the clause (literal L will be added back to the clause)
			all_clauses.increaseLength(*it);
		}
		// unassign literal L
		all_clauses.unassignVariable(L);
	}
	//! undo propagation of literal L
	inline void undoPropagateLiteral(int L) {
		vector<int> &appears2 = appears[L];
		for (vector<int>::const_iterator it=appears2.begin(); it<appears2.begin() + appears_len[L]; ++it) {
			assert(!all_clauses.getDeleteFlag(*it));
			all_clauses.increaseLength(*it);
		}
		all_clauses.unassignVariable(L);
	}

	//! add literal L to clauses where it was removed if there is a conflict
	inline int addLiteralConflict(int L) {
		vector<int> &appears2 = appears[L];
		// count how many clauses in the inconsistent subformula depend on propagating L
		int propagated = 0;
#ifdef FUIP
		bla.clear();
#endif
		for (vector<int>::const_iterator it=appears2.begin(); it<appears2.begin() + appears_len[L]; ++it) {
			assert(!all_clauses.getDeleteFlag(*it));
			// if clause has a marker flag, it belongs to inconsistent subformula
			if (all_clauses.getMarker(*it)) {
#ifdef FUIP
				bla.push_back(*it);
#endif
				++propagated;
			}
			all_clauses.increaseLength(*it);
		}
		all_clauses.unassignVariable(L);
		if (!propagated)
			return W_unit[L] > 0;
		return propagated;
	}
	
	//! apply resolution to pairs of binary clause (x_i, x_j) (x_i, -x_j) or ternary clauses (x_i, x_j, x_k) (x_i, x_j, -x_k)
	inline TL binary_ternary_resolution(int L) {
		int_c nC[2];
		TL cnt = 0;
		int other1, other2, id;
		const int_c *literals;
		// store in literal_data[i] the clause consisting of literals L and i
		// store in ternary_clause_data[(L1+nVars)*(2*nVars+1)+L2+nVars] the clause consisting of literals L, L1 and L2
		for (int i=appears[L].size()-1; i>=0; --i) {
			int &it = appears[L][i];
			if (all_clauses.getDeleteFlag(it)) {
				// remove clause pointers which should be deleted
				if (all_clauses.getSpecialFlag(it))
					all_clauses.decreaseCounter(it);
				it = appears[L].back();
				appears[L].pop_back();
			}
			else {
				assert(all_clauses.getWeight(it) > 0);
				assert(!all_clauses.getSpecialFlag(it));
				all_clauses.saveWeight(it);
				if (all_clauses.getLength(it) == 2) {
					literals = all_clauses.getLiterals(it);
					other1 = (literals[0] == L? literals[1] : literals[0]);
					// check if there was an identical binary clause
					if (literal_data[other1] > 0) {
						assert(literal_data[other1] != it);
						ULL w = all_clauses.getWeight(it);
						assert(all_clauses.getWeight(literal_data[other1]) > 0);
						// add weight of clause to previous same clause
						all_clauses.addWeight(literal_data[other1], w);
						all_clauses.subtractWeight(it, w, true);
						rlist.addEntry(it);
						rlist.commit(timestamp++, w, false);
					}
					else {
						assert(all_clauses.getWeight(it) > 0);
						literal_data[other1] = it;
					}
				}
				else if (ternary_clause_data != NULL && all_clauses.getLength(it) == 3) {
					literals = all_clauses.getLiterals(it);
					other1 = other2 = 0;
					// determine the other two literals other1 and other2 which appear together with literal L in the clause
					for (int i=0; i<3; ++i)
						if (literals[i] != L) {
							if (!other1)
								other1 = literals[i];
							else
								other2 = literals[i];
						}
					if (other1 > other2)
						swap(other1,  other2);
					// calculate a unique id for a clause containing literal L and literal other1 and literal other2
					id = (other1 + nVars) * (nVars * 2 + 1) + other2 + nVars;
					// check if we can merge the clause
					if (ternary_clause_data[id] > 0) {
						assert(ternary_clause_data[id] != it);
						ULL w = all_clauses.getWeight(it);
						assert(all_clauses.getWeight(ternary_clause_data[id]) > 0);
						all_clauses.addWeight(ternary_clause_data[id], w);
						all_clauses.subtractWeight(it, w, true);
						rlist.addEntry(it);
						rlist.commit(timestamp++, w, false);
					}
					else {
						assert(all_clauses.getWeight(it) > 0);
						ternary_clause_data[id] = it;
					}
				}
			}
		}
		// now do the resolution using literal_data and ternary_clause_data arrays
		for (int i=appears[L].size()-1; i>=0; --i) {
			int &it = appears[L][i];
			assert(!all_clauses.getSpecialFlag(it));
			if (all_clauses.getDeleteFlag(it)) {
				// in this case it can only be a clause which was deleted because it is the same as another clause, and its weight was added to the other clause
				// we only need to delete the clause pointer
				it = appears[L].back();
				appears[L].pop_back();
			}
			else {
				if (all_clauses.getLength(it) == 2) {
					literals = all_clauses.getLiterals(it);
					other1 = (literals[0] == L)? literals[1] : literals[0];
					if (literal_data[other1] != it) {
						assert(all_clauses.getWeight(it) == all_clauses.getSavedWeight(it));
						continue;
					}
					literal_data[other1] = 0;
					ULL w = all_clauses.getWeight(it);
					// check if we changed the weight of the clause
					if (all_clauses.getSavedWeight(it) != w) {
						assert(all_clauses.getSavedWeight(it) < w);
						rlist.addEntry(it);
						rlist.commit(timestamp++, w - all_clauses.getSavedWeight(it), true);
						all_clauses.saveWeight(it);
					}
					// check if there is also a clause consisting of L and -other1 -> resolution of (L, other1) with (L, -other1)
					if (literal_data[-other1] > 0) {
						int c = literal_data[-other1];
						literal_data[-other1] = 0;
						ULL w2 = all_clauses.getWeight(c);
						// check if we changed the weight
						if (all_clauses.getSavedWeight(c) != w2) {
							assert(all_clauses.getSavedWeight(c) < w2);
							rlist.addEntry(c);
							rlist.commit(timestamp++, w2 - all_clauses.getSavedWeight(c), true);
							all_clauses.saveWeight(c);
						}
						ULL wmin = min(w, w2);
						assert(wmin > 0);
						all_clauses.subtractWeight(c, wmin, true);
						all_clauses.subtractWeight(it, wmin, true);
						W_binary[other1] -= wmin;
						W_binary[-other1] -= wmin;
						W_binary[L] -= wmin;
						W_binary[L] -= wmin;
						rlist.addEntry(c);
						rlist.addEntry(it);
						rlist.commit(timestamp++, wmin, false);
						cnt += wmin;
						if (w == wmin) {
							// if the complete weight of the clause was subtracted, the clause pointer can be deleted
							it = appears[L].back();
							appears[L].pop_back();
							continue;
						}
					}
				}
				else if (ternary_clause_data != NULL && all_clauses.getLength(it) == 3) {
					literals = all_clauses.getLiterals(it);
					other1 = other2 = 0;
					// determine the other two literals other1 and other2 which appear together with literal L in the clause
					for (int i=0; i<3; ++i)
						if (literals[i] != L) {
							if (!other1)
								other1 = literals[i];
							else
								other2 = literals[i];
						}
					if (other1 > other2)
						swap(other1,  other2);
					id = (other1 + nVars) * (nVars * 2 + 1) + other2 + nVars;
					if (ternary_clause_data[id] <= 0)
						continue;
					assert(ternary_clause_data[id] == it);
					ternary_clause_data[id] = 0;
					ULL w = all_clauses.getWeight(it);
					// check if we changed the weight
					if (all_clauses.getSavedWeight(it) != w) {
						assert(all_clauses.getSavedWeight(it) < w);
						rlist.addEntry(it);
						rlist.commit(timestamp++, w - all_clauses.getSavedWeight(it), true);
						all_clauses.saveWeight(it);
					}
					// first negate other1
					int other3 = -other1, other4 = other2;
					if (other3 > other4)
						swap(other3, other4);
					id = (other3 + nVars) * (nVars * 2 + 1) + other4 + nVars;
					// check if there exists a clause (L, -other1, other2)
					// -> resolution with (L, other1, other2) possible
					if (ternary_clause_data[id] > 0) {
						int c = ternary_clause_data[id];
						ULL w2 = all_clauses.getWeight(c);
						if (all_clauses.getSavedWeight(c) != w2) {
							assert(all_clauses.getSavedWeight(c) < w2);
							rlist.addEntry(c);
							rlist.commit(timestamp++, w2 - all_clauses.getSavedWeight(c), true);
							all_clauses.saveWeight(c);
						}
						ULL wmin = min(w, w2);
						assert(wmin > 0);
						if (wmin == w2)
							ternary_clause_data[id] = 0;
						all_clauses.subtractWeight(c, wmin, true);
						all_clauses.subtractWeight(it, wmin, true);
						rlist.addEntry(c);
						rlist.addEntry(it);
						rlist.commit(timestamp++, wmin, false);
						// adjust weights
						W_binary[L] += wmin;
						W_binary[other2] += wmin;
						W_large[L] -= wmin;
						W_large[L] -= wmin;
						W_large[other2] -= wmin;
						W_large[other2] -= wmin;
						W_large[other1] -= wmin;
						W_large[-other1] -= wmin;
						if (literal_data[other2] > 0) {
							assert(all_clauses.getWeight(literal_data[other2]) > 0);
							all_clauses.addWeight(literal_data[other2], wmin);
						}
						else {
							nC[0] = L;
							nC[1] = other2;
							c = all_clauses.addClause(nC, 2, wmin);
							take_back.push_back(c);
							appears[other2].push_back(c);
							++appears_len[other2];
							rlist.addEntry(c);
							rlist.commit(timestamp++, wmin, true);
						}
						// if clause weight has become zero, the clause pointer can be deleted
						if (w == wmin) {
							it = appears[L].back();
							appears[L].pop_back();
							continue;
						}
						w -= wmin;
					}
					// then negate other2
					other3 = other1;
					other4 = -other2;
					if (other3 > other4)
						swap(other3, other4);
					id = (other3 + nVars) * (nVars * 2 + 1) + other4 + nVars;
					// check if there exists a clause (L, other1, -other2)
					// -> resolution with (L, other1, other2) possible
					if (ternary_clause_data[id] > 0) {
						int c = ternary_clause_data[id];
						ULL w2 = all_clauses.getWeight(c);
						if (all_clauses.getSavedWeight(c) != w2) {
							assert(all_clauses.getSavedWeight(c) < w2);
							rlist.addEntry(c);
							rlist.commit(timestamp++, w2 - all_clauses.getSavedWeight(c), true);
							all_clauses.saveWeight(c);
						}
						ULL wmin = min(w, w2);
						assert(wmin > 0);
						if (wmin == w2)
							ternary_clause_data[id] = 0;
						all_clauses.subtractWeight(c, wmin, true);
						all_clauses.subtractWeight(it, wmin, true);
						// adjust weights
						W_binary[L] += wmin;
						W_binary[other1] += wmin;
						W_large[L] -= wmin;
						W_large[L] -= wmin;
						W_large[other1] -= wmin;
						W_large[other1] -= wmin;
						W_large[other2] -= wmin;
						W_large[-other2] -= wmin;
						rlist.addEntry(c);
						rlist.addEntry(it);
						rlist.commit(timestamp++, wmin, false);
						if (literal_data[other1] > 0) {
							assert(all_clauses.getWeight(literal_data[other1]) > 0);
							all_clauses.addWeight(literal_data[other1], wmin);
						}
						else {
							nC[0] = L;
							nC[1] = other1;
							c = all_clauses.addClause(nC, 2, wmin);
							take_back.push_back(c);
							appears[other1].push_back(c);
							++appears_len[other1];
							rlist.addEntry(c);
							rlist.commit(timestamp++, wmin, true);
						}
						// if weight of the clause has become zero, the clause pointer can be deleted
						if (w == wmin) {
							it = appears[L].back();
							appears[L].pop_back();
							continue;
						}
					}
				}
			}
		}
		// take_back contains the binary clauses created by resolution of ternary clauses
		if (!take_back.empty()) {
			appears[L].insert(appears[L].end(), take_back.begin(), take_back.end());
			take_back.clear();
		}
		appears_len[L] = (int)appears[L].size();
		appears_traversed[L] = timestamp++;
#ifndef NDEBUG
		for (vector<int>::const_iterator it=appears[L].begin(); it!=appears[L].end(); ++it)
			assert(all_clauses.getDeleteFlag(*it) == false);
#endif
		assert(!assigned_values[abs(L)]);
		return cnt;
	}
	//! insert clause c into the appears list of L
	inline void do_insert(int L, int c) {
		appears[L].push_back(c);
		assert((int)appears[L].size() > appears_len[L]);
		swap(appears[L].back(), appears[L][appears_len[L]]);
		++appears_len[L];
	}
	//! remove inconsistent subformula (possibly use inference rules for transformation)
	void resolveConflict() {
		#ifdef DEBUG
		cout << "resolveConflict" << endl;
#endif
		int t, pos = -1, other = 0;
		// first extract inconsistent subformula -> stored in take_back
		assert(take_back.empty());
		assert(vars_top >= 0);
		assert(literal_data[-vars[vars_top]] > 0);
		// add the conflict clause to the inconsistent subformula and mark it
		take_back.push_back(literal_data[-vars[vars_top]]);
		literal_data[-vars[vars_top]] = 0;
		if (take_back.back() != UNIT_CLAUSE)
			all_clauses.addMarker2Clause(take_back.back());
		else
			take_back.back() = -vars[vars_top] - nVars;
		assert(which.empty());
		// pos2 is either -1 or indicates that we may shorten the inconsistent subformula by taking only the first "pos2" entries and adding a unit literal "var"
		int pos2 = -1, pcnt = 0, var, maxt = 1;
		ULL minweight = MAXWEIGHT;
		// process the propagation stack in reverse order
		for (int *it=vars + vars_top; it >= vars; --it) {
#ifdef DEBUG
			if (literal_data[*it] == 0)
				for (int i=0; i<=vars_top; ++i)
					printf("vars[%d] = %d\n", i, vars[i]);
#endif
			assert(literal_data[*it] > 0);
			// check if literal -*it occurred in marked clauses (i. e. *it needs to be propagated to yield the conflict clause)
			if ((t = addLiteralConflict(-*it))) {
				// add literal to the list of literals which need to be propagated to yield the conflict clause
				which.push_back(*it);
				if (t > maxt)
					maxt = t;
				if (t == 2) {
					// this means that the literal -*it occured in two marked clauses
					// this may be the "starting point" of a cycle structure
					// save the position
					if (take_back.size() == 3)
						pos = 3;
					// save the literal
					other = *it;
				}
				// if -*it occurs in more than one marked clause, we may not shorten the inconsistent subformula after this point
				if (t > 1)
					pos2 = -1;
				if (literal_data[*it] != UNIT_CLAUSE) {
					// check if there exists a unit literal which could be used for propagation instead of the current clause
					if (W_unit[*it] > 0 && pos2 < 0 && take_back.size() > 2) {
						pos2 = take_back.size();
						pcnt = 0;
						var = *it - nVars;
					}
					if (all_clauses.getWeight(literal_data[*it]) < minweight)
						minweight = all_clauses.getWeight(literal_data[*it]);
					assert(!all_clauses.getMarker(literal_data[*it]));
					// mark the clause and add it to the list of clauses of the inconsistent subformula
					all_clauses.addMarker2Clause(literal_data[*it]);
					take_back.push_back(literal_data[*it]);
				}
				else {
					if (W_unit[*it] < (TL)minweight)
						minweight = W_unit[*it];
					// represent a unit literal by *it - nVars
					// it holds -nVars <= *it <= nVars, thus *it - nVars <= 0 < UNIT_CLAUSE
					take_back.push_back(*it - nVars);
					// if we encounter another used unit literal, we cannot shorten the inconsistent subformula beyond that
					if (pos2 >= 0) {
						++pcnt;
						if (pcnt > 1)
							pos2 = -1;
					}
				}
			}
			literal_data[*it] = 0;
		}
		// check if inconsistent subformula can be shortened
		if (pos2 >= 2 && pos2+1<(int)take_back.size() && W_unit[var+nVars] >= (TL)minweight) {
			int cnt = -1;
			while((int)take_back.size() > pos2) {
				++cnt;
				if (take_back.back() > UNIT_CLAUSE)
					all_clauses.removeMarkerFromClause(take_back.back());
				take_back.pop_back();
			}
			assert(var <= 0 && cnt >= 0);
			which.resize(which.size()-cnt);
			take_back.push_back(var);
		}
		vars_top = -1;
		int first_large_clause = -1;
		int cnt = 0;
		minweight = MAXWEIGHT;
		// determine the minimum weight of a clause belonging to the inconsistent subformula
		// also determine the position of the first clause with more than two literals
		for (vector<int>::const_iterator it=take_back.begin(); it!=take_back.end(); ++it)
			if (*it > UNIT_CLAUSE) {
				minweight = min(minweight, all_clauses.getWeight(*it));
				assert(all_clauses.getLength(*it) > 1);
				if (first_large_clause < 0 && all_clauses.getLength(*it) > 2)
					first_large_clause = distance((vector<int>::const_iterator)take_back.begin(), it);
			}
			else {
				if (W_unit[*it + nVars] < (TL)minweight)
					minweight = (ULL)W_unit[*it + nVars];
				++cnt;
			}
		// remove the markers from the clauses and subtract the weight from unit clauses
		for (vector<int>::const_iterator it=take_back.begin(); it!=take_back.end(); ++it) {
			if (*it <= 0) {
				W_unit[*it + nVars] -= minweight;
				assert(W_unit[*it + nVars] >= 0);
			}
			else
				all_clauses.removeMarkerFromClause(*it);
		}
		assert(take_back.back() <= 0);
		if (first_large_clause >= 0) {
			which.clear();
			// check if we can use cycle resolution
			if (first_large_clause > 2 && take_back.size() > 3) {
				int c[3] = {take_back[0], take_back[1], take_back[2]};
				// check that the first three clauses are binary clauses
				if (c[0] > UNIT_CLAUSE && all_clauses.getLength(c[0]) == 2 && c[1] > UNIT_CLAUSE && all_clauses.getLength(c[1]) == 2 && c[2] > UNIT_CLAUSE && all_clauses.getLength(c[2]) == 2) {
					int other = which[2];
					const int_c *literals1 = all_clauses.getLiterals(c[0]);
					const int_c *literals2 = all_clauses.getLiterals(c[1]);
					// the conflict clause should not contain -other
					const int_c *literals3 = all_clauses.getLiterals(c[2]);
					// first find common literals in literals2 and literals3
					int i1 = -1, i2;
					if (literals2[0] == literals3[0])
						i1 = i2 = 0;
					else if (literals2[0] == literals3[1]) {
						i1 = 0;
						i2 = 1;
					}
					else if (literals2[1] == literals3[0]) {
						i1 = 1;
						i2 = 0;
					}
					else if (literals2[1] == literals3[1])
						i1 = i2 = 1;
					if (i1 >= 0 && ((literals1[0] == -literals2[1-i1] && literals1[1] == -literals3[1-i2]) || (literals1[0] == -literals3[1-i2] && literals1[1] == -literals2[1-i1]))) {
						assert(literals1[0] != -other && literals1[1] != -other);
						assert(literals2[i1] == -other);
						other = literals2[i1];
						assert(pos == 3);
						// do cycle resolution
						if (process_cycle_clauses(c[0], c[1], c[2], literals2[i1], literals1[0], literals1[1])) {
							// in the special case of unit propagation, we do not need to include the newly generated ternary clauses in the inconsistent subformula
							take_back.pop_back();
							take_back.pop_back();
							// remove the binary clauses which were used in the resolution
							take_back.erase(take_back.begin(), take_back.begin() + 3);
							assert(W_unit[other] >= minweight);
							W_unit[other] -= minweight;
							unary_resolution(other);
							cycle_clauses.clear();
						}
					}
					else
						assert(pos != 3);
				}
			}
			// remove inconsistent subformula
			for (vector<int>::const_iterator it=take_back.begin(); it!=take_back.end(); ++it)
				if (*it > 0) {
					assert(!all_clauses.getDeleteFlag(*it));
					if (all_clauses.getLength(*it) == 2) {
						const int *literals = all_clauses.getLiterals(*it);
						W_binary[literals[0]] -= minweight;
						W_binary[literals[1]] -= minweight;
					}
					else {
						const int *literals = all_clauses.getLiterals(*it);
						for (int j=all_clauses.getLength(*it)-1; j>=0; --j)
							W_large[literals[j]] -= minweight;
					}
					changed.push_back(*it);
					all_clauses.subtractWeight(*it, minweight);
				}
			take_back.clear();
			saveSubtraction(needed_for_skip, minweight);
			return;
		}
		// check if we can apply a transformation
		if (cnt == 2) {
			// it is a chain of binary clauses
			int_c nC[2];
			bool added = false;
			for (vector<int>::const_iterator it=take_back.begin(); it < take_back.end(); ++it)
				if (*it > UNIT_CLAUSE) {
					all_clauses.subtractWeight(*it, minweight, true);
					assert(all_clauses.getLength(*it) == 2);
					const int_c *literals = all_clauses.getLiterals(*it);
					W_binary[literals[0]] -= minweight;
					W_binary[literals[1]] -= minweight;
					W_binary[-literals[0]] += minweight;
					W_binary[-literals[1]] += minweight;
					nC[0] = -literals[0];
					nC[1] = -literals[1];
					int c = all_clauses.addClause(nC, 2, minweight);
					do_insert(nC[0], c);
					do_insert(nC[1], c);
					rlist.addEntry(c);
					added = true;
				}
				else {
					W_unit_save[*it + nVars] -= minweight;
					assert(*it == take_back[0] || *it == take_back.back());
				}
			if (added)
				rlist.commit(timestamp++, minweight, true);
			saveAddition(cost[n_assigned], minweight);
			saveSubtraction(needed_for_skip, minweight);
			for (vector<int>::const_iterator it=take_back.begin(); it!=take_back.end(); ++it)
				rlist.addEntry(*it);
			rlist.commit(timestamp++, minweight, false);
			minweight = 0;
		}
		else if (pos == 3) {
			assert(cnt == 1 && take_back.size() >= 3);
			// cycle resolution can be applied
			int_c nC[3];
			const int_c *literals;
			assert(cnt == 1);
			literals = all_clauses.getLiterals(take_back[0]);
			assert(literals[0] != other && literals[1] != other && literals[0] != -other && literals[1] != -other);
			ULL mw = min(all_clauses.getWeight(take_back[0]), min(all_clauses.getWeight(take_back[1]), all_clauses.getWeight(take_back[2])));
			assert(mw >= minweight);
			if (mw > minweight) {
				W_unit[-other] += mw - minweight;
				W_unit_save[-other] += mw - minweight;
				rlist.addEntry(-other - nVars);
				rlist.commit(timestamp++, mw - minweight, true);
			}
			literals = all_clauses.getLiterals(take_back[0]);
			assert(literals[0] != other && literals[1] != other);
			nC[0] = other;
			nC[1] = literals[0];
			nC[2] = literals[1];
			W_binary[-other] -= mw;
			W_binary[-other] -= mw;
			W_binary[literals[0]] -= mw;
			W_binary[-literals[0]] -= mw;
			W_binary[literals[1]] -= mw;
			W_binary[-literals[1]] -= mw;
			W_large[nC[0]] += mw;
			W_large[nC[1]] += mw;
			W_large[nC[2]] += mw;
			int c = all_clauses.addClause(nC, 3, mw);
			do_insert(nC[0], c);
			do_insert(nC[1], c);
			do_insert(nC[2], c);
			rlist.addEntry(c);
			nC[0] *= -1;
			nC[1] *= -1;
			nC[2] *= -1;
			W_large[nC[0]] += mw;
			W_large[nC[1]] += mw;
			W_large[nC[2]] += mw;
			c = all_clauses.addClause(nC, 3, mw);
			do_insert(nC[0], c);
			do_insert(nC[1], c);
			do_insert(nC[2], c);
			rlist.addEntry(c);
			if (mw > minweight)
				rlist.commit(timestamp++, mw, true);
			bool added = false;
			for (vector<int>::const_iterator it=take_back.begin()+3; it+1<take_back.end(); ++it) {
				const int *literals = all_clauses.getLiterals(*it);
				nC[0] = -literals[0];
				nC[1] = -literals[1];
				W_binary[nC[0]] += minweight;
				W_binary[nC[1]] += minweight;
				W_binary[literals[0]] -= minweight;
				W_binary[literals[1]] -= minweight;
				int c = all_clauses.addClause(nC, 2, minweight);
				do_insert(nC[0], c);
				do_insert(nC[1], c);
				rlist.addEntry(c);
				added = true;
			}
			assert(take_back.back() <= UNIT_CLAUSE);
			if (mw == minweight || added)
				rlist.commit(timestamp++, minweight, true);
			W_unit_save[take_back.back() + nVars] -= minweight;
			if (mw > minweight) {
				assert(take_back.size() > 3);
				all_clauses.subtractWeight(take_back[0], mw, true);
				all_clauses.subtractWeight(take_back[1], mw, true);
				all_clauses.subtractWeight(take_back[2], mw, true);
				rlist.addEntry(take_back[0]);
				rlist.addEntry(take_back[1]);
				rlist.addEntry(take_back[2]);
				rlist.commit(timestamp++, mw, false);
				for (vector<int>::const_iterator it=take_back.begin() + 3; it!=take_back.end(); ++it) {
					rlist.addEntry(*it);
					if (*it > 0)
						all_clauses.subtractWeight(*it, minweight, true);
					// otherwise it was already subtracted
					else
						assert(*it == take_back.back());
				}
			}
			else {
				for (vector<int>::const_iterator it=take_back.begin(); it!=take_back.end(); ++it) {
					rlist.addEntry(*it);
					if (*it > 0)
						all_clauses.subtractWeight(*it, minweight, true);
					// otherwise it was already subtracted
					else
						assert(*it == take_back.back());
				}
			}
			rlist.commit(timestamp++, minweight, false);
			saveAddition(cost[n_assigned], minweight);
			saveSubtraction(needed_for_skip, minweight);
			minweight = 0;
			unary_resolution(other);
#ifdef PROP_LIST
			if (onstack[-other] < 0 && W_unit[-other] + (TL)cost[n_assigned] >= (TL)bestCost) {
				onstack[-other] = propagation_stack_size;
				propagation_stack[propagation_stack_size++] = -other;
			}
#endif
		}
		/*
		// the following lines can be used to do Max-SAT resolution yielding an empty clause
		else if (take_back.size() <= 5) {
			bool added = false;
			int len = take_back[0] > UNIT_CLAUSE?all_clauses.getLength(take_back[0]):1;
			int maxlen = 100, maxlen2 = 100, len2;
			if (len > maxlen)
				maxlen = len;
			int *nclause = new int[maxlen];
			int *nclause2 = new int[maxlen2];
			const int *literals;
			if (len == 1)
				nclause[0] = take_back[0]+nVars;
			else
				memcpy(nclause, all_clauses.getLiterals(take_back[0]), len*sizeof(int));
			vector<int>::const_iterator it, it2;
			// now do resolution
			for (it=which.begin(), it2=take_back.begin()+1; it!=which.end(); ++it,++it2) {
				assert(len > 0);
				len2 = *it2 > UNIT_CLAUSE?all_clauses.getLength(*it2) : 1;
				if (len2 > maxlen2) {
					maxlen2 *= 2;
					while(len2 > maxlen2)
						maxlen2 *= 2;
					delete [] nclause2;
					nclause2 = new int[maxlen2];
				}
				if (len2 == 1) {
					assert(*it2 <= UNIT_CLAUSE);
					nclause2[0] = *it2 + nVars;
				}
				else {
					literals = all_clauses.getLiterals(*it2);
					memcpy(nclause2, literals, len2 * sizeof(int));
				}
				// move literal *it to the end
#ifndef NDEBUG
				bool found = false;
#endif
				for (int i=0; i<len; ++i)
					if (nclause[i] == -*it) {
						swap(nclause[len-1], nclause[i]);
#ifndef NDEBUG
						found = true;
#endif
						break;
					}
#ifndef NDEBUG
#ifdef DEBUG
				if (!found) {
					printf("looking for literal %d\n",-*it);
					for (int i=0; i<len; ++i)
						printf("%d ", nclause[i]);
					puts("");
				}
#endif
				assert(found);
				found = false;
#endif
				for (int i=0; i<len2; ++i)
					if (nclause2[i] == *it) {
						swap(nclause2[len2-1], nclause2[i]);
#ifndef NDEBUG
						found = true;
#endif
						break;
					}
#ifndef NDEBUG
#ifdef DEBUG
				if (!found) {
					printf("looking for literal %d\n",*it);
					for (int i=0; i<len2; ++i)
						printf("%d ", nclause2[i]);
					puts("");
				}
#endif
				assert(found);
#endif
				--len;
				--len2;
				// determine common literals
				sort(nclause, nclause+len);
#ifndef NDEBUG
				for (int i=1; i<len; ++i)
					assert(nclause[i] != nclause[i-1]);
#endif
				sort(nclause2, nclause2+len2);
				assert(nclause[len] == -nclause2[len2]);
				int l = len-1;
				for (int i=len-1, j=len2-1; i>=0 && j>=0; ) {
					if (nclause[i] == nclause2[j]) {
						swap(nclause[l--], nclause[i--]);
						nclause2[j--] = nclause2[--len2];
					}
					else if (nclause[i] < nclause2[j])
						--j;
					else
						--i;
				}
				if (len + len2 + 1 > maxlen) {
					maxlen *= 2;
					while(len + len2 + 1 > maxlen)
						maxlen *= 2;
					int *temp = new int[maxlen];
					memcpy(temp, nclause, sizeof(int) * len);
					swap(nclause, temp);
					delete [] temp;
				}
				// add compensation clauses
				if (len2 > 0) {
					memcpy(nclause+len+1, nclause2, len2*sizeof(int));
					assert(nclause[len] == -*it);
					for (int i=len+1; i<=len+len2; ++i) {
						nclause[i] = -nclause[i];
						if (i > len+1)
							nclause[i-1] = -nclause[i-1];
						int c = all_clauses.addClause(nclause, i+1, minweight);
						for (int j=0; j<=i; ++j) {
							if (i+1 == 2)
								W_binary[nclause[j]] += minweight;
							else
								W_large[nclause[j]] += minweight;
							do_insert(nclause[j], c);
						}
						rlist.addEntry(c);
						added = true;
					}
					nclause[len + len2] = -nclause[len + len2];
#ifndef NDEBUG
					for (int i=0; i<len2; ++i)
						assert(nclause[len+i+1] == nclause2[i]);
#endif
				}
				nclause[len] = -nclause[len];
				assert(nclause[len] == *it);
				for (int i=l; i>=0; --i) {
					nclause[i] = -nclause[i];
					if (i < l)
						nclause[i+1] = -nclause[i+1];
					int c = all_clauses.addClause(nclause+i, len+len2+1-i, minweight);
					for (int j=i; j<=len+len2; ++j) {
						if (len+len2+1-i == 2)
							W_binary[nclause[j]] += minweight;
						else
							W_large[nclause[j]] += minweight;
						do_insert(nclause[j], c);
					}
					rlist.addEntry(c);
					added = true;
				}
				if (l >= 0)
					nclause[0] = -nclause[0];
				nclause[len] = nclause[len+len2];
				len += len2;
			}
			assert(it == which.end() && it2 == take_back.end());
#ifdef DEBUG
			if (len > 0) {
				printf("len = %d\n", len);
				for (int i=0; i<len; ++i)
					printf("%d ", nclause[i]);
				puts("");
			}
#endif
			assert(len == 0);
			delete [] nclause;
			delete [] nclause2;
			which.clear();
			assert(minweight > 0);
			if (added)
				rlist.commit(timestamp++, minweight, true);
			saveAddition(cost[n_assigned], minweight);
			saveSubtraction(needed_for_skip, minweight);
			for (vector<int>::const_iterator it=take_back.begin(); it!=take_back.end(); ++it) {
				rlist.addEntry(*it);
				if (*it > 0) {
					if (all_clauses.getLength(*it) == 2) {
						const int *literals = all_clauses.getLiterals(*it);
						W_binary[literals[0]] -= minweight;
						W_binary[literals[1]] -= minweight;
					}
					else {
						const int *literals = all_clauses.getLiterals(*it);
						for (int j=all_clauses.getLength(*it)-1; j>=0; --j)
							W_large[literals[j]] -= minweight;
					}
					all_clauses.subtractWeight(*it, minweight, true);
				}
				else {
					assert(W_unit[*it + nVars] >= 0);
					W_unit_save[*it + nVars] -= minweight;
				}
			}
			rlist.commit(timestamp++, minweight, false);
			take_back.clear();
			return;
		}
		*/
		else {
			// no transformation, just remove inconsistent subformula
			for (vector<int>::const_iterator it=take_back.begin(); it!=take_back.end(); ++it)
				if (*it > 0) {
					if (all_clauses.getLength(*it) == 2) {
						const int *literals = all_clauses.getLiterals(*it);
						W_binary[literals[0]] -= minweight;
						W_binary[literals[1]] -= minweight;
					}
					else {
						const int *literals = all_clauses.getLiterals(*it);
						for (int j=all_clauses.getLength(*it)-1; j>=0; --j)
							W_large[literals[j]] -= minweight;
					}
					changed.push_back(*it);
					all_clauses.subtractWeight(*it, minweight);
				}
		}
		which.clear();
		take_back.clear();
		saveSubtraction(needed_for_skip, minweight);
	}
	//! restore the clauses changed by the lowerbound function
	void restoreClauses(int L) {
#ifdef DEBUG
		cout << "restoreClauses" << endl;
#endif
		int length;
		long long deletion_time;
		ULL minweight;
		bool sign;
		const int *rclauses;
		// get the clauses which need to be changed back to their previous state
		while( (rclauses = rlist.retrieve(appears_traversed[L], length, deletion_time, minweight, sign)) != NULL) {
			while(length > 0) {
				--length;
				int clause_id = rclauses[length];
				if (clause_id <= 0) {
					// in that case, we have a unit clause with a unit literal clause_id + nVars
					clause_id += nVars;
					assert(!assigned_values[abs(clause_id)]);
					assert(W_unit[clause_id] == W_unit_save[clause_id]);
					if (sign) {
						W_unit[clause_id] -= minweight;
						W_unit_save[clause_id] -= minweight;
						assert(W_unit_save[clause_id] >= 0);
					}
					else {
						W_unit[clause_id] += minweight;
						W_unit_save[clause_id] += minweight;
					}
					continue;
				}
				assert(!all_clauses.getSpecialFlag(clause_id));
				bool wasDeleted = all_clauses.getDeleteFlag(clause_id);
				if (sign)
					all_clauses.subtractWeight(clause_id, minweight, true);
				else
					all_clauses.addWeight(clause_id, minweight, true);
				// adjust the weights W_binary or W_total, respectively
				if (all_clauses.getLength(clause_id) == 2) {
					const int_c *literals = all_clauses.getLiterals(clause_id);
					if (sign) {
						W_binary[literals[0]] -= minweight;
						W_binary[literals[1]] -= minweight;
					}
					else {
						W_binary[literals[0]] += minweight;
						W_binary[literals[1]] += minweight;
					}
				}
				else if (all_clauses.getLength(clause_id) >= 3) {
					const int_c *literals = all_clauses.getLiterals(clause_id);
					for (int i=all_clauses.getLength(clause_id)-1; i>=0; --i)
						if (sign)
							W_large[literals[i]] -= minweight;
						else
							W_large[literals[i]] += minweight;
				}
				if (all_clauses.getDeleteFlag(clause_id)) {
					assert(!wasDeleted);
					// in that case the clause can be permanently deleted
#ifndef NDEBUG
					const int_c *literals = all_clauses.getLiterals(clause_id);
					for (int i=all_clauses.getLength(clause_id)-1; i>=0; --i) {
						int cnt = 0;
						for (vector<int>::const_iterator it=appears[literals[i]].begin(); it!=appears[literals[i]].end(); ++it)
							if (*it == clause_id)
								++cnt;
						assert(cnt == 1);
					}
					for (int i=-nVars; i<=nVars; ++i) {
						bool valid = (i != 0);
						for (int j=all_clauses.getLength(clause_id)-1; j>=0; --j)
							if (literals[j] == i)
								valid = false;
						if (!valid)
							continue;
						for (vector<int>::const_iterator it=appears[i].begin(); it!=appears[i].end(); ++it)
							assert(*it != clause_id);
					}
#endif
					// call the prepareDelete function which stores the number of active references to the clause
					all_clauses.prepareDelete(clause_id);
					assert(all_clauses.getWeight(clause_id) == all_clauses.getSavedWeight(clause_id) && all_clauses.getSpecialFlag(clause_id) && all_clauses.getDeleteFlag(clause_id));
					continue;
				}
				if (!wasDeleted)
					continue;
				int l = all_clauses.getLength(clause_id);
				assert(l > 1);
				const int_c *literals = all_clauses.getLiterals(clause_id);
				// reinsert clause pointers into the appears lists where needed
				for (int i=0; i<l; ++i) {
#ifndef NDEBUG
					bool found = false;
					for (vector<int>::const_iterator it=appears[literals[i]].begin(); it!=appears[literals[i]].end(); ++it)
						if (*it == clause_id) {
							found = true;
							break;
						}
#endif
					assert(appears_len[literals[i]] == (int)appears[literals[i]].size());
					if (appears_traversed[literals[i]] > deletion_time) {
#ifndef NDEBUG
						if (found) cout << "here with " << literals[i] << " " << all_clauses.getLength(clause_id) << " " << appears_traversed[literals[i]] << " " << deletion_time << endl;
						assert(!found);
#endif
						appears[literals[i]].push_back(clause_id);
						++appears_len[literals[i]];
					}
#ifndef NDEBUG
					else {
						if (!found) cout << "here2 " << all_clauses.getLength(clause_id) << " " << appears_traversed[literals[i]] << " " << deletion_time << endl;
						assert(found);
					}
#endif
				}
			}
		}
	}
	// process clauses (l1 l2) (l1 l3) (-l2 -l3) which imply -l1
	inline bool process_cycle_clauses(int c1, int c2, int c3, int l1, int l2, int l3) {
		int_c nC[3];
		if (l1 == l2 || l1 == l3 || l2 == -l3)
			return false;
		assert(l1 != l2 && l1 != -l2 && l1 != l3 && l1 != -l3 && l2 != l3 && l2 != -l3);
		assert(all_clauses.getLength(c1) == 2 && all_clauses.getLength(c2) == 2 && all_clauses.getLength(c3) == 2);
		if (!all_clauses.getDeleteFlag(c1) && !all_clauses.getDeleteFlag(c2) && !all_clauses.getDeleteFlag(c3)) {
			ULL minweight = min(all_clauses.getWeight(c1), min(all_clauses.getWeight(c2), all_clauses.getWeight(c3)));
			assert(minweight > 0);
			// save the clause pointers to clauses involved in the cycle resolution
			cycle_clauses.push_back(c1);
			cycle_clauses.push_back(c2);
			cycle_clauses.push_back(c3);
			// save the information in the restore list
			rlist.addEntry(c1);
			all_clauses.subtractWeight(c1, minweight, true);
			rlist.addEntry(c2);
			all_clauses.subtractWeight(c2, minweight, true);
			rlist.addEntry(c3);
			all_clauses.subtractWeight(c3, minweight, true);
			rlist.commit(timestamp++, minweight, false);
			assert(l1 >= -nVars && l1 <= nVars && l1 != 0 && !assigned_values[abs(l1)]);
			W_unit[l1] += minweight;
			W_unit_save[l1] += minweight;
#ifdef PROP_LIST
			// check if the literal l1 can be propagated
			if (onstack[l1] < 0 && W_unit[l1] + (TL)cost[n_assigned] >= (TL)bestCost) {
				onstack[l1] = propagation_stack_size;
				propagation_stack[propagation_stack_size++] = l1;
			}
#endif
			rlist.addEntry(l1 - nVars);
			// add compensation clauses (-l1, l2, l3) and (l1, -l2, -l3)
			// also update the weights according to the new clauses
			nC[0] = -l1;
			nC[1] = l2;
			nC[2] = l3;
			W_binary[-nC[0]] -= minweight;
			W_binary[-nC[0]] -= minweight;
			W_binary[nC[1]] -= minweight;
			W_binary[-nC[1]] -= minweight;
			W_binary[nC[2]] -= minweight;
			W_binary[-nC[2]] -= minweight;
			W_large[nC[0]] += minweight;
			W_large[nC[1]] += minweight;
			W_large[nC[2]] += minweight;
			int c = all_clauses.addClause(nC, 3, minweight);
			take_back.push_back(c);
			do_insert(nC[0], c);
			do_insert(nC[1], c);
			do_insert(nC[2], c);
			rlist.addEntry(c);
			nC[0] = -nC[0];
			nC[1] = -nC[1];
			nC[2] = -nC[2];
			W_large[nC[0]] += minweight;
			W_large[nC[1]] += minweight;
			W_large[nC[2]] += minweight;
			c = all_clauses.addClause(nC, 3, minweight);
			take_back.push_back(c);
			do_insert(nC[0], c);
			do_insert(nC[1], c);
			do_insert(nC[2], c);
			rlist.addEntry(c);
			rlist.commit(timestamp++, minweight, true);
			return true;
		}
		return false;
	}
	//! sort the appears list by weight of the clauses
	void do_sort(int i) {
		vector< pair<ULL, int> > temp;
		temp.reserve(appears[i].size());
		for (vector<int>::const_iterator it=appears[i].begin(); it!=appears[i].end(); ++it)
			temp.push_back(make_pair(all_clauses.getWeight(*it), *it));
		sort(temp.begin(), temp.end());
		vector<int>::iterator it2=appears[i].begin();
		for (vector< pair<ULL, int> >::iterator it=temp.begin(); it!=temp.end(); ++it)
			*it2++ = it->second;
	}
	//! check if literal L is a failed literal
	inline bool detectFailedLiteral(int L) {
#ifdef DEBUG
		cout << "detectFailedLiteral L = " << L << endl;
#endif
		// propagated literal L
		vars[++vars_top] = L;
		assert(literal_data[L] <= 0);
		literal_data[L] = UNIT_CLAUSE;
		if (propagateLiteral(-L))
			return true;
		// continue propagation to see if propagating L results in a conflict
		// -> L is a failed literal
		while(head != tail) {
			int nexti = Q[head++];
			assert(nexti != 0);
			assert(head < 2 * nVars);
			assert(literal_data[nexti] > 0);
			vars[++vars_top] = nexti;
			if (propagateLiteral(-nexti)) {
				// clear the queue
				while(head != tail) {
					if (Q[head] != -nexti)
						literal_data[Q[head]] = 0;
					++head;
				}
				return true;
			}
			assert(literal_data[-nexti] <= 0);
		}
		return false;
	}
	//! resolution of clauses L and -L
	void unary_resolution(int L) {
		// this should usually be executed only once
		while(W_unit[L] > 0 && W_unit[-L] > 0) {
			ULL s;
			if (W_unit[-L] < W_unit[L])
				s = (W_unit[-L] > (TL)MAXWEIGHT? MAXWEIGHT : (ULL)W_unit[-L]);
			else
				s = (W_unit[L] > (TL)MAXWEIGHT? MAXWEIGHT : (ULL)W_unit[L]);
			W_unit[L] -= s;
			W_unit[-L] -= s;
			W_unit_save[L] -= s;
			W_unit_save[-L] -= s;
			saveAddition(cost[n_assigned], s);
			saveSubtraction(needed_for_skip, s);
			rlist.addEntry(-L - nVars);
			rlist.addEntry(L - nVars);
			rlist.commit(timestamp++, s, false);
		}
	}
	//! check if there is a conflict using generalized unit propagation
	bool detectConflictFl(bool &fl, int &iv, int &iv2) {
#ifdef DEBUG
		cout << "detectConflictFl" << endl;
#endif
		head = tail = 0;
		int L, fL;
		fl = false;
		assert(vars_top == -1);
		int minii = l-1, minv = l-1;
		while(1) {
			bool found = false;
			// look for a literal in a unit clause
			// start at position iv2
			for (int ii=0,tiv=iv2; !found && ii<l; ++ii) {
				int i = literal_order[tiv].second;
		//		if (++tiv == l)
		//			tiv = 0;
				if (--tiv < 0)
					tiv = l-1;
				if (!W_unit[i])
					i = -i;
				minv = ii;
				if (W_unit[i] > 0 && literal_data[i] <= 0) {
					Q[tail++] = i;
					literal_data[i] = UNIT_CLAUSE;
					found = true;
					break;
				}
			}
			// uncomment the following two lines if only unit propagation and failed literal detection should be used
#ifdef NO_GUP
			if (!found && fl)
				break;
#endif
			if (!found) {
				int save_head = head;
				int save_vars_top = vars_top;
				// look for a failed literal
				// start at position iv
				for (int ii=0, tiv=iv; !found && ii<l; ++ii) {
					int i = literal_order[tiv].second;
					if (--tiv < 0)
						tiv = l-1;
					assert(i != 0);
					if (W_binary[-i] > W_binary[i] || (W_binary[-i] == W_binary[i] && W_large[-i] > W_large[i]))
						i = -i;
					assert(!assigned_values[abs(i)]);
					minii = ii;
					if (literal_data[i] > 0 || literal_data[-i] > 0)
						continue;
					if (detectFailedLiteral(i)) {
						L = resolveFailedLiteral(save_vars_top);
						head = save_head;
						tail = head + 1;
						Q[head] = -L;
						assert(literal_data[-L] <= 0);
						literal_data[-L] = UNIT_CLAUSE;
						found = true;
						fl = true;
						fL = L;
						break;
					}
					assert(head == tail);
					head = tail = save_head;
					for (int *it=vars + vars_top; it > vars + save_vars_top; --it) {
						undoPropagateLiteral(-*it);
						literal_data[*it] = 0;
					}
					vars_top = save_vars_top;
				}
				if (!found)
					break;
			}
			// if we are here we have at least one literal to be propagated
			assert(tail <= 2 * nVars);
			oldtail = head;
			// propagate in breadth-first search order
			while(head != tail) {
				// for unit propagation, move a unit literal towards the front which yields an immediate conflict
				// first check that the literal at the front of the queue does not yield an immediate conflict
				if (!fl && W_unit[-Q[head]] == 0 && literal_data[-Q[head]] <= 0) {
					for (int i=head+1; i<tail; ++i)
						if (W_unit[-Q[i]] > 0) {
							swap(Q[head], Q[i]);
							break;
						}
				}
				assert(oldtail == head);
				oldtail = tail;
				while(head != oldtail) {
					L = Q[head++];
					assert(literal_data[L]);
					assert(!assigned_values[abs(L)]);
					vars[++vars_top] = L;
					if (propagateLiteral(-L)) {
						// this means a conflict was found
						// reset the literal_data array to 0 at positions still in the queue
						while(head != tail) {
							if (Q[head] != -L)
								literal_data[Q[head]] = 0;
							++head;
						}
						iv -= (1+minii);
						if (iv < 0)
							iv += l;
						iv2 += minv+1;
						if (iv2 >= l)
							iv2 -= l;
						return true;
					}
				}
			}
		}
		assert(vars_top == -1 || literal_data[-vars[vars_top]] <= 0);
		assert(head == tail);
		// if we are here this means no conflict was found
		// undo the propagations
		for (int *it=vars + vars_top; it >= vars; --it) {
			undoPropagateLiteral(-*it);
			literal_data[*it] = 0;
		}
		for (int *it=vars; it<=vars+vars_top; ++it) {
			// check if we can apply cycle resolution
			if (unit_implication_list[-*it].size() >= 3) {
				int c1 = unit_implication_list[-*it][0];
				if (c1 <= UNIT_CLAUSE || all_clauses.getDeleteFlag(c1)) {
					unit_implication_list[-*it].clear();
					continue;
				}
				int c2 = unit_implication_list[-*it][1];
				if (c2 <= UNIT_CLAUSE || all_clauses.getDeleteFlag(c2)) {
					unit_implication_list[-*it].clear();
					continue;
				}
				int c3 = unit_implication_list[-*it][2];
				if (c3 <= UNIT_CLAUSE || all_clauses.getDeleteFlag(c3)) {
					unit_implication_list[-*it].clear();
					continue;
				}
				if (all_clauses.getLength(c1) == 2 && all_clauses.getLength(c2) == 2 && all_clauses.getLength(c3) == 2) {
					const int_c *literals1 = all_clauses.getLiterals(c1);
					const int_c *literals2 = all_clauses.getLiterals(c2);
					const int_c *literals3 = all_clauses.getLiterals(c3);
					// first find common literals in literals2 and literals3
					int i1 = -1, i2;
					if (literals2[0] == literals3[0])
						i1 = i2 = 0;
					else if (literals2[0] == literals3[1]) {
						i1 = 0;
						i2 = 1;
					}
					else if (literals2[1] == literals3[0]) {
						i1 = 1;
						i2 = 0;
					}
					else if (literals2[1] == literals3[1])
						i1 = i2 = 1;
					if (i1 >= 0 && ((literals1[0] == -literals2[1-i1] && literals1[1] == -literals3[1-i2]) || (literals1[0] == -literals3[1-i2] && literals1[1] == -literals2[1-i1]))) {
#ifdef DEBUG
						const int *literals = all_clauses.getLiterals(c1);
						printf("(%d %d) ", literals[0], literals[1]);
						literals = all_clauses.getLiterals(c2);
						printf("(%d %d) ", literals[0], literals[1]);
						literals = all_clauses.getLiterals(c3);
						printf("(%d %d) -> %d +-(%d %d %d)\n", literals[0], literals[1], literals2[i1], -literals2[i1], literals1[0], literals1[1]);
#endif
						int other = literals2[i1];
						if (process_cycle_clauses(c1, c2, c3, literals2[i1], literals1[0], literals1[1]))
							unary_resolution(other);
					}
				}
			}
			unit_implication_list[-*it].clear();
		}
		cycle_clauses.clear();
		take_back.clear();
		vars_top = -1;
		return false;
	}
	//! resolve the conflict and extract inconsistent subformula
	void resolveConflictFl() {
#ifdef DEBUG
		cout << "resolveConflictFl" << endl;
#endif
		assert(vars_top >= 0);
		assert(literal_data[-vars[vars_top]] > 0);
		assert(take_back.empty());
		// add the conflict clause to the inconsistent subformula to be constructed
		take_back.push_back(literal_data[-vars[vars_top]]);
		literal_data[-vars[vars_top]] = 0;
		int t, pos = 0;
		int_c c[3];
		// set the marker to indicate it belongs to the inconsistent subformula
		if (take_back.back() != UNIT_CLAUSE) {
			all_clauses.addMarker2Clause(take_back.back());
			c[pos++] = take_back.back();
		}
		else {
			pos = -1;
			take_back.back() = -vars[vars_top] - nVars;
			assert(W_unit[-vars[vars_top]] > 0);
		}
		assert(which.empty());
		// go through the propagation stack in reverse order
		// undo propagations, thereby checking if the clause was needed for deriving the conflict clause
		for (int *it=vars + vars_top; it >= vars; --it) {
#ifdef DEBUG
			printf("cur = %d implication_list.size() = %d\n", *it, (int)unit_implication_list[-*it].size());
			if (literal_data[*it] == 0)
				for (int i=0; i<=vars_top; ++i)
					printf("vars[%d] = %d %d\n", i, vars[i], (int)unit_implication_list[-vars[i]].size());
#endif
			assert(literal_data[*it] > 0);
			if ((t = addLiteralConflict(-*it))) {
				// t indicates the number of marked clauses which include literal -*it
				// this means that t > 0 implies the current clause is needed to derive the conflict clause
				if (literal_data[*it] != UNIT_CLAUSE) {
					assert(!all_clauses.getMarker(literal_data[*it]));
					all_clauses.addMarker2Clause(literal_data[*it]);
					take_back.push_back(literal_data[*it]);
					// collect the first three clauses to check for cycle resolution
					if (pos >= 0 && pos < 3)
						c[pos++] = take_back.back();
				}
				else if (W_unit[*it] > 0) {
					if (pos < 3)
						pos = -1;
					take_back.push_back(*it - nVars);
				}
				else {
					if (pos < 3)
						pos = -1;
					assert(!unit_implication_list[-*it].empty());
					which.push_back(-*it);
					for (vector<int>::const_iterator it2=unit_implication_list[-*it].begin(); it2!=unit_implication_list[-*it].end(); ++it2) {
						assert(*it2 > UNIT_CLAUSE && !all_clauses.getDeleteFlag(*it2));
						if (!all_clauses.getMarker(*it2)) {
							all_clauses.addMarker2Clause(*it2);
							take_back.push_back(*it2);
						}
					}
				}
			}
			literal_data[*it] = 0;
		}
		ULL minw = bestCost;
		for (vector<int>::const_iterator it=take_back.begin(); it!=take_back.end(); ++it)
			if (*it <= 0) {
				if (W_unit[*it + nVars] < (TL)minw)
					minw = (ULL)W_unit[*it + nVars];
				literal_data[*it + nVars] = 1;
			}
			else {
				assert(!all_clauses.getDeleteFlag(*it));
				minw = min(minw, all_clauses.getWeight(*it));
				all_clauses.removeMarkerFromClause(*it);
			}
		assert(minw > 0);
		// process unit implication lists belonging to the inconsistent subformula and look for clauses forming a cycle
		for (vector<int>::const_reverse_iterator it=which.rbegin(); it!=which.rend(); ++it) {
			if (unit_implication_list[*it].size() >= 3) {
				// check if the three clauses form a cycle
				int c1 = unit_implication_list[*it][0];
				if (c1 <= UNIT_CLAUSE || find(cycle_clauses.begin(), cycle_clauses.end(), c1)!=cycle_clauses.end()) {
					unit_implication_list[*it].clear();
					continue;
				}
				int c2 = unit_implication_list[*it][1];
				if (c2 <= UNIT_CLAUSE || find(cycle_clauses.begin(), cycle_clauses.end(), c2)!=cycle_clauses.end()) {
					unit_implication_list[*it].clear();
					continue;
				}
				int c3 = unit_implication_list[*it][2];
				if (c3 <= UNIT_CLAUSE || find(cycle_clauses.begin(), cycle_clauses.end(), c3)!=cycle_clauses.end()) {
					unit_implication_list[*it].clear();
					continue;
				}
				if (all_clauses.getLength(c1) == 2 && all_clauses.getLength(c2) == 2 && all_clauses.getLength(c3) == 2) {
					const int_c *literals1 = all_clauses.getLiterals(c1);
					const int_c *literals2 = all_clauses.getLiterals(c2);
					const int_c *literals3 = all_clauses.getLiterals(c3);
					// first find common literals in literals2 and literals3
					int i1 = -1, i2;
					if (literals2[0] == literals3[0])
						i1 = i2 = 0;
					else if (literals2[0] == literals3[1]) {
						i1 = 0;
						i2 = 1;
					}
					else if (literals2[1] == literals3[0]) {
						i1 = 1;
						i2 = 0;
					}
					else if (literals2[1] == literals3[1])
						i1 = i2 = 1;
					if (i1 >= 0 && ((literals1[0] == -literals2[1-i1] && literals1[1] == -literals3[1-i2]) || (literals1[0] == -literals3[1-i2] && literals1[1] == -literals2[1-i1]))) {
						int other = literals2[i1];
						// do cycle resolution
						if (process_cycle_clauses(c1, c2, c3, literals2[i1], literals1[0], literals1[1])) {
							assert(W_unit[other] >= minw);
							literal_data[other] = 0;
							W_unit[other] -= minw;
							unary_resolution(other);
						}
					}
				}
			}
			unit_implication_list[*it].clear();
		}
		sort(cycle_clauses.begin(), cycle_clauses.end());
		// check if we can use cycle resolution
		if (pos == 3 && all_clauses.getLength(c[0]) == 2 && all_clauses.getLength(c[1]) == 2 && all_clauses.getLength(c[2]) == 2 && !binary_search(cycle_clauses.begin(), cycle_clauses.end(), c[0]) && !binary_search(cycle_clauses.begin(), cycle_clauses.end(), c[1]) && !binary_search(cycle_clauses.begin(), cycle_clauses.end(), c[2]))  {
			const int_c *literals1 = all_clauses.getLiterals(c[0]);
			const int_c *literals2 = all_clauses.getLiterals(c[1]);
			const int_c *literals3 = all_clauses.getLiterals(c[2]);
			// first find common literals in literals2 and literals3
			int i1 = -1, i2;
			if (literals2[0] == literals3[0])
				i1 = i2 = 0;
			else if (literals2[0] == literals3[1]) {
				i1 = 0;
				i2 = 1;
			}
			else if (literals2[1] == literals3[0]) {
				i1 = 1;
				i2 = 0;
			}
			else if (literals2[1] == literals3[1])
				i1 = i2 = 1;
			if (i1 >= 0 && ((literals1[0] == -literals2[1-i1] && literals1[1] == -literals3[1-i2]) || (literals1[0] == -literals3[1-i2] && literals1[1] == -literals2[1-i1]))) {
				int other = literals2[i1];
				// do cycle resolution
				if (process_cycle_clauses(c[0], c[1], c[2], literals2[i1], literals1[0], literals1[1])) {
					assert(W_unit[other] >= minw);
					literal_data[other] = 0;
					W_unit[other] -= minw;
					unary_resolution(other);
				}
			}
		}
		sort(cycle_clauses.begin(), cycle_clauses.end());
		which.clear();
		// subtract minw from all clauses belonging to the inconsistent subformula
		for (vector<int>::const_iterator it=take_back.begin(); it!=take_back.end(); ++it)
			if (*it <= 0) {
				if (literal_data[*it + nVars] == 1) {
					assert(W_unit[*it + nVars] >= minw);
					W_unit[*it + nVars] -= minw;
					literal_data[*it + nVars] = 0;
				}
			}
			else if (!binary_search(cycle_clauses.begin(), cycle_clauses.end(), *it)) {
				if (all_clauses.getWeight(*it) >= bestCost)
					continue;
				assert(all_clauses.getWeight(*it) >= minw);
				changed.push_back(*it);
				all_clauses.subtractWeight(*it, minw);
				if (all_clauses.getLength(*it) == 2) {
					const int *literals = all_clauses.getLiterals(*it);
					W_binary[literals[0]] -= minw;
					W_binary[literals[1]] -= minw;
				}
				else {
					const int *literals = all_clauses.getLiterals(*it);
					for (int i=all_clauses.getLength(*it)-1; i>=0; --i)
						W_large[literals[i]] -= minw;
				}
			}
		// now process all remaining unit implication lists and look for clauses forming a cycle
		for (int *it=vars+vars_top; it>=vars; --it) {
			// check if we can use cycle resolution
			if (unit_implication_list[-*it].size() >= 3) {
				int c1 = unit_implication_list[-*it][0];
				if (c1 <= UNIT_CLAUSE || all_clauses.getDeleteFlag(c1)) {
					unit_implication_list[-*it].clear();
					continue;
				}
				int c2 = unit_implication_list[-*it][1];
				if (c2 <= UNIT_CLAUSE || all_clauses.getDeleteFlag(c2)) {
					unit_implication_list[-*it].clear();
					continue;
				}
				int c3 = unit_implication_list[-*it][2];
				if (c3 <= UNIT_CLAUSE || all_clauses.getDeleteFlag(c3)) {
					unit_implication_list[-*it].clear();
					continue;
				}
				if (all_clauses.getLength(c1) == 2 && all_clauses.getLength(c2) == 2 && all_clauses.getLength(c3) == 2) {
					const int_c *literals1 = all_clauses.getLiterals(c1);
					const int_c *literals2 = all_clauses.getLiterals(c2);
					const int_c *literals3 = all_clauses.getLiterals(c3);
					// first find common literals in literals2 and literals3
					int i1 = -1, i2;
					if (literals2[0] == literals3[0])
						i1 = i2 = 0;
					else if (literals2[0] == literals3[1]) {
						i1 = 0;
						i2 = 1;
					}
					else if (literals2[1] == literals3[0]) {
						i1 = 1;
						i2 = 0;
					}
					else if (literals2[1] == literals3[1])
						i1 = i2 = 1;
					if (i1 >= 0 && ((literals1[0] == -literals2[1-i1] && literals1[1] == -literals3[1-i2]) || (literals1[0] == -literals3[1-i2] && literals1[1] == -literals2[1-i1]))) {
#ifdef DEBUG
						const int *literals = all_clauses.getLiterals(c1);
						printf("(%d %d) ", literals[0], literals[1]);
						literals = all_clauses.getLiterals(c2);
						printf("(%d %d) ", literals[0], literals[1]);
						literals = all_clauses.getLiterals(c3);
						printf("(%d %d) -> %d +-(%d %d %d)\n", literals[0], literals[1], literals2[i1], -literals2[i1], literals1[0], literals1[1]);
#endif
						int other = literals2[i1];
						if (process_cycle_clauses(c1, c2, c3, literals2[i1], literals1[0], literals1[1]))
							unary_resolution(other);
					}
				}
			}
			unit_implication_list[-*it].clear();
		}
		cycle_clauses.clear();
		take_back.clear();
		vars_top = -1;
		saveSubtraction(needed_for_skip, minw);
	}
	//! extract clauses which are in conflict with the failed literal
	int resolveFailedLiteral(int save_vars_top) {
#ifdef DEBUG
		cout << "resolveFailedLiteral" << endl;
#endif
		assert(vars_top > save_vars_top);
		assert(literal_data[-vars[vars_top]] > 0);
		assert(which.empty());
		which.push_back(literal_data[-vars[vars_top]]);
#ifndef NDEBUG
		for (int *it=vars; it<=vars+vars_top; ++it)
			assert(*it != -vars[vars_top]);
#endif
		literal_data[-vars[vars_top]] = 0;
		assert(which.back() != UNIT_CLAUSE);
		all_clauses.addMarker2Clause(which.back());
		int t, var = 0, pos = 0;
		vector<int> vars2;
#ifdef FUIP
		int pos2 = 0;
		ref_cnt[0] = 0;
#endif
		// process propagation stack in reverse order
		for (int *it=vars + vars_top; it > vars + save_vars_top; --it) {
#ifdef DEBUG
			if (literal_data[*it] == 0)
				for (int i=0; i<=vars_top; ++i)
					printf("vars[%d] = %d\n", i, vars[i]);
#endif
			assert(literal_data[*it] > 0);
			if ((t = addLiteralConflict(-*it))) {
				if (t > 1) {
					pos = which.size();
					var = *it;
				}
#ifdef FUIP
				vars2.push_back(*it);
				int cur = which.size();
				ref_cnt[cur] = 0;
				for (vector<int>::const_iterator it2=bla.begin(); it2!=bla.end(); ++it2) {
					int t = distance(which.begin(), find(which.begin(), which.end(), *it2));
					tadj[cur].push_back(t);
					++ref_cnt[t];
				}
#endif
				which.push_back(literal_data[*it]);
				assert(it == vars+save_vars_top+1 || literal_data[*it] != UNIT_CLAUSE);
				if (literal_data[*it] != UNIT_CLAUSE) {
					assert(!all_clauses.getMarker(literal_data[*it]));
					all_clauses.addMarker2Clause(literal_data[*it]);
				}
				else
					which.back() = *it - nVars;
			}
			literal_data[*it] = 0;
		}
#ifdef FUIP
		int l2 = 0;
		for (int i=0; i<(int)which.size(); ++i) {
			if (ref_cnt[i] == 0) Q2[l2++] = i;
			visit2[i] = 0;
		}
		int work_cnt = 0;
		for (int i=0; i<l2; ++i) {
			int cur = Q2[i];
			if (l2-i == 1 && !work_cnt && cur)
				pos2 = cur;
			for (vector<int>::const_iterator it=tadj[cur].begin(); it!=tadj[cur].end(); ++it) {
				if (!visit2[*it]) {
					++work_cnt;
					visit2[*it] = 1;
				}
				if (--ref_cnt[*it] == 0) {
					Q2[l2++] = *it;
					--work_cnt;
				}
			}
			tadj[cur].clear();
		}
		if (pos < (int)which.size()-1)
			++total_cnt_fuip;
		if (pos < pos2)
			fprintf(stderr, "error: here with pos = %d, pos2 = %d\n", pos, pos2);
		else if (pos > pos2) {
			++succ_cnt_fuip;
		}
#endif
		// no FUIP - uncomment next line
#ifdef NO_FUIP
		pos = which.size()-1;
#endif
		assert(var != 0);
		assert(head == tail);
		vars_top = save_vars_top;
		assert(which.back() < UNIT_CLAUSE);
		assert(unit_implication_list[var].empty());
		for (vector<int>::const_iterator it=which.begin(); it+1 < which.end(); ++it)  {
			assert(*it > UNIT_CLAUSE && all_clauses.getLength(*it) > 1 && all_clauses.getWeight(*it) > 0);
			all_clauses.removeMarkerFromClause(*it);
		}
		which.resize(pos);
		unit_implication_list[var] = which;
		which.clear();
		return var;
	}
	double clause_height(int start, int skip, int satisfied) {
		double wa = (double)psi[start++];
		int len = (int)psi[start++] * 2;
		double potential = 0;
		for (int i=0; i<len; i+=2) {
			if (start + i == skip)
				continue;
			if (psi[start + i] <= psi[start + i + 1]) {
				potential += psi[start + i];
				satisfied = 1;
			}
			else
				potential += psi[start + i + 1];
		}
		if (satisfied)
			return wa - potential;
		double difference = 1e34;
		for (int i=0; i<len; i+=2) {
			if (start + i == skip)
				continue;
			double tdiff = fabs(psi[start + i] - psi[start + i + 1]);
			if (tdiff < difference)
				difference = tdiff;
		}
		if (wa > difference)
			return wa - potential - difference;
		return -potential;
	}
	//! generalized unit propagation to find inconsistent subformulas
	void generalized_unit_propagation() {
		l = 0;
		for (int i=1; i<=nVars; ++i) {
			if (!assigned_values[i]) {
				literal_order[l].second = i;
				literal_order[l].first = (W_binary[i] + W_large[i]) * (W_binary[-i] + W_large[-i]);
				++l;
			}
		}
		sort(literal_order, literal_order + l);
		bool fl;
		int iv = l-1, iv2 = l/2;
		while(needed_for_skip > 0) {
			if (!detectConflictFl(fl, iv, iv2))
				break;
			// check if failed literals were used; if not, transformation rules can possibly be applied
			fl?resolveConflictFl():resolveConflict();
		}
		++total_gup;
		if (!needed_for_skip) {
			++succ_gup;
			return;
		}
#ifdef CALC_MH
		reverse(literal_order, literal_order+l);
		psi.clear();
		for (int ii=0; ii<l; ++ii) {
			int i = literal_order[ii].second;
			ptr[i].clear();
		}
		int c = 0, c2 = 0;
		for (int ii=0; ii<l; ++ii) {
			int i = literal_order[ii].second;
			if (W_unit[i] > 0) {
				++c;
				++c2;
				ptr[i].push_back(psi.size()+2);
				ptr[i].push_back(psi.size());
				psi.push_back(W_unit[i]);
				psi.push_back(1);
				psi.push_back(0);
				psi.push_back(0);
			}
			if (W_unit[-i] > 0) {
				++c;
				++c2;
				ptr[i].push_back(psi.size()+3);
				ptr[i].push_back(psi.size());
				psi.push_back(W_unit[-i]);
				psi.push_back(1);
				psi.push_back(0);
				psi.push_back(0);
			}
			for (vector<int>::iterator it=appears[i].begin(); it!=appears[i].end(); ++it) {
				if (all_clauses.getDeleteFlag(*it))
					continue;
				++c;
				const int_c *literals = all_clauses.getLiterals(*it);
				if (*literals != i)
					continue;
				++c2;
				int start = psi.size();
				psi.push_back(all_clauses.getWeight(*it));
				psi.push_back(all_clauses.getLength(*it));
				for (int j=all_clauses.getLength(*it)-1; j>=0; --j) {
					int ii = abs(literals[j]);
					ptr[ii].push_back(psi.size() + (literals[j] < 0));
					ptr[ii].push_back(start);
					psi.push_back(0);
					psi.push_back(0);
				}
			}
			for (vector<int>::iterator it=appears[-i].begin(); it!=appears[-i].end(); ++it) {
				if (all_clauses.getDeleteFlag(*it))
					continue;
				++c;
				const int_c *literals = all_clauses.getLiterals(*it);
				if (*literals != -i)
					continue;
				++c2;
				int start = psi.size();
				psi.push_back(all_clauses.getWeight(*it));
				psi.push_back(all_clauses.getLength(*it));
				for (int j=all_clauses.getLength(*it)-1; j>=0; --j) {
					int ii = abs(literals[j]);
					ptr[ii].push_back(psi.size() + (literals[j] < 0));
					ptr[ii].push_back(start);
					psi.push_back(0);
					psi.push_back(0);
				}
			}
		}
		if ((c+c2)*2 != (int)psi.size())
			printf("%d %d\n", (c+c2)*2, (int)psi.size());
		bool stop = false;
		vector<double> old;
		int iter = 0;
		double maxdiff;
		while(!stop && (iter++<100 || (!n_assigned && iter++<1000))) {
			stop = true;
			maxdiff = 1e-6;
			for (int ii=0; ii<l; ++ii) {
				int i = literal_order[ii].second;
				double m1 = 0, m2 = 0;
				old.clear();
				for (vector<int>::iterator it=ptr[i].begin(); it!=ptr[i].end(); ++it) {
					int isneg = (*it & 1);
					int p = *it++ - isneg;
					old.push_back(psi[p]);
					old.push_back(psi[p + 1]);
					psi[p] = clause_height(*it, p, 1);
					psi[p + 1] = clause_height(*it, p, 0);
					if (isneg) {
						m1 += psi[p + 1];
						m2 += psi[p];
					}
					else {
						m1 += psi[p];
						m2 += psi[p + 1];
					}
				}
				m1 /= (ptr[i].size()/2);
				m2 /= (ptr[i].size()/2);
				vector<double>::iterator it2 = old.begin();
				double sum1 =  0, sum2 = 0;
				for (vector<int>::iterator it=ptr[i].begin(); it!=ptr[i].end(); ++it) {
					int isneg = (*it & 1);
					int p = *it++ - isneg;
					if (isneg) {
						psi[p+1] -= m1;
						psi[p] -= m2;
						sum1 += psi[p+1];
						sum2 += psi[p];
					}
					else {
						psi[p] -= m1;
						psi[p + 1] -= m2;
						sum1 += psi[p];
						sum2 += psi[p+1];
					}
					if (fabs(psi[p] - *it2) > maxdiff) {
						maxdiff = fabs(psi[p]- *it2);
						stop = false;
					}
					++it2;
					if (fabs(psi[p + 1] - *it2) > maxdiff) {
						maxdiff = fabs(psi[p + 1] - *it2);
						stop = false;
					}
					++it2;
				}
				if (fabs(sum1) > 1e-7 || fabs(sum2) > 1e-7) {
					printf("%lf %lf\n", sum1, sum2);
					exit(1);
				}
			}
		}
		double lb = 0;
		for (int i=0; i<(int)psi.size();) {
			lb += psi[i] - clause_height(i, -1, 0);
			i += psi[i+1] * 2 + 2;
		}
		lb = ceil(lb - 1e-9);
		if (lb >= needed_for_skip) {
		//	printf("success in depth %d\n", n_assigned);
			needed_for_skip = 0;
			return;
		}
		if (n_assigned == 0)
			printf("%lf iter=%d maxdiff=%lf\n", lb, iter, maxdiff);
		needed_for_skip -= (long long)lb;
#endif
#ifndef NDEBUG
		for (int i=1; i<=nVars; ++i)
			assert(literal_data[i] == 0 && literal_data[-i] == 0);
#endif
	}

	// public functions
public:
	//! CNF_Formula constructor
	/*! \param istr the input stream from which the formula can be read
	 */
	CNF_Formula(istream &istr) {
		total_gup = succ_gup = 0;
		string line;
		int nClauses, t = 0;
		char type[100];
		// parse the input file
		while(getline(istr, line)) {
			// look for the parameter line
			if (line[0] == 'p' && line[1] == ' ') {
				t = sscanf(line.c_str(), "p %s %d %d %llu", type, &maxVn, &nClauses, &hard);
				if (t >= 3)
					break;
			}
		}
		if (t < 3)
			fprintf(stderr, "Parse error: did not find the parameter line\n");
		assert(t >= 3);
		if (t == 3 || !hard)
			hard = MAXWEIGHT;
		// check if the formula contains weighted clauses or not
		if (!strcmp(type, "wcnf"))
			isWcnf = true;
		else {
			assert(!strcmp(type, "cnf"));
			isWcnf = false;
		}
		vector<int> lengths, literals;
		vector<ULL> weights;
		maps_to = new int[maxVn + 1];
		memset(maps_to, -1, sizeof(int) * (maxVn + 1));
		nVars = 0;
		int var;
		// read the clauses and construct the formula data structures
		for (int i=0; i<nClauses; ++i) {
			vector<int> clause;
			ULL weight = 1;
			if (isWcnf) {
				// read the weight
				istr >> weight;
				assert(weight > 0 && weight <= MAXWEIGHT);
			}
			// read the literals in the clause
			while(istr >> var && var)
				clause.push_back(var);
			// now remove duplicate literals, and check if the clause is a tautology
			if (normalize_clause_array(clause)) {
				// if it is not a tautology, store the clause data
				for (vector<int_c>::iterator it=clause.begin(); it!=clause.end(); ++it) {
					int sign = 1;
					int var = *it;
					if (var < 0) {
						var = -var;
						sign = -1;
					}
					// remap the variables to values between 1 and nVars
					if (maps_to[var] < 0) {
						++nVars;
						maps_to[var] = nVars;
					}
					// first, all literals from all clauses are put into the literals vector
					literals.push_back(maps_to[var] * sign);
				}
				// store the number of literals in the current clause
				lengths.push_back((int)clause.size());
				// store the weight of the clause
				weights.push_back(weight);
			}
			// in this case the clause is a tautology and can be ignored
			else {
				--i;
				--nClauses;
			}
		}
		if (nVars != maxVn)
			printf("c Number of variables occuring in the formula: %d max variable = %d -> remapping\n", nVars, maxVn);
		// store in mapping the original variable number of each new variable
		mapping = new int[nVars + 1];
#ifdef STATS
		explored = new int[nVars + 1];
		sum_cost = new long long[nVars + 1];
		memset(explored, 0, sizeof(int) * (nVars+1));
		memset(sum_cost, 0, sizeof(long long) * (nVars + 1));
#endif
		for (int i=1; i<=maxVn; ++i) {
			if (maps_to[i] < 0)
				continue;
			assert(maps_to[i] > 0 && maps_to[i] <= nVars);
			mapping[maps_to[i]] = i;
		}
		vars_top = -1;
#ifdef FUIP
		tadj = new vector<int>[2*nVars];
		succ_cnt_fuip = total_cnt_fuip = 0;
		ref_cnt = new int[2*nVars];
		Q2 = new int[2*nVars];
		visit2 = new char[2*nVars];
#endif
		ptr = new vector<int>[2 * nVars + 1];
		vars = new int[2 * nVars];
		Q = new int[2 * nVars];
		cost = new ULL[nVars + 1];
		cost[0] = 0;
#ifdef PROP_LIST
		propagation_stack = new int[nVars * 2];
		propagation_stack_size = 0;
		onstack = new int[nVars * 2 + 1];
		memset(onstack, -1, sizeof(int) * (2 * nVars + 1));
		onstack += nVars;
#endif
		W_unit = new TL[2 * nVars + 1];
		W_binary = new TL[2 * nVars + 1];
		W_large = new TL[2 * nVars + 1];
		W_lb = new TL[2 * nVars + 1];
		W_unit_save = new TL[2 * nVars + 1];
		memset(W_unit, 0, sizeof(TL) * (2 * nVars + 1));
		memset(W_binary, 0, sizeof(TL) * (2 * nVars + 1));
		memset(W_large, 0, sizeof(TL) * (2 * nVars + 1));
		memset(W_unit_save, 0, sizeof(TL) * (2 * nVars + 1));
		literal_data = new int[2 * nVars + 1];
		ternary_clause_data = (nVars > 5000? NULL : new int[(2 * nVars + 1) * (2 * nVars + 1)]);
		literal_order = new pair<TL, int> [2 * nVars];
		memset(literal_data, 0, sizeof(int) * (2 * nVars + 1));
		appears = new vector<int>[2 * nVars + 1];
		unit_implication_list = new vector<int>[2 * nVars + 1];
		appears_len = new int[2 * nVars + 1];
		memset(appears_len, 0, sizeof(int) * (2 * nVars + 1));
		appears_len += nVars;
		appears_traversed = new long long[2 * nVars + 1];
		memset(appears_traversed, -1, sizeof(long long) * (2 * nVars + 1));
		if (ternary_clause_data != NULL)
			memset(ternary_clause_data, 0, sizeof(int) * (2 * nVars + 1) * (2 * nVars + 1));
		assigned_values = new char[nVars + 1];
		bestA = new char[nVars + 1];
		memset(assigned_values, 0, sizeof(char)* (nVars + 1));
		memset(bestA, 0, sizeof(char) * (nVars + 1));
		assigned_literals = new int[nVars + 1];
		// since we want to index with values in the range [-nVars, nVars], add +nVars to the pointers
		W_unit += nVars;
		W_binary += nVars;
		W_large += nVars;
		W_unit_save += nVars;
		W_lb += nVars;
		appears += nVars;
		unit_implication_list += nVars;
		appears_traversed += nVars;
		literal_data += nVars;
		n_assigned = 0;
		timestamp = 0;
		assert(nClauses == (int)lengths.size());
		assert(nClauses == (int)weights.size());
		// initialize additional variables of the clauses data structure
		all_clauses.init(nVars);
		vector<int_c>::iterator it=literals.begin();
		// construct the formula data structures
		for (int i=0; i<nClauses; ++i) {
			ULL weight = weights[i];
			int len = lengths[i];
			if (len == 1) {
				W_unit[*it] += weight;
				W_unit_save[*it] += weight;
				++it;
				continue;
			}
			int_c *clause_array = new int_c[len];
			for (int j=0; j<len; ++j) {
				assert(it < literals.end());
				clause_array[j] = *it++;
			}
			// add the clause to the data structure maintaining all clauses
			int clause_id = all_clauses.addClause(clause_array, len, weight);
			assert(clause_id > UNIT_CLAUSE);
			assert(all_clauses.getLength(clause_id) == len);
			// add clause pointers to the appears array
			for (int j=0; j<len; ++j) {
				if (len == 2)
					W_binary[clause_array[j]] += weight;
				else if (len > 2)
					W_large[clause_array[j]] += weight;
				++appears_len[clause_array[j]];
				appears[clause_array[j]].push_back(clause_id);
			}
			delete [] clause_array;
		}
		bestCost = hard;
		assert(it >= literals.end());
		for (int i=1; i<=nVars; ++i) {
			do_sort(i);
			do_sort(-i);
		}
	}
	//! get the weight of clauses containing i used in inconsistent subformulas
	/*! \param i the literal for which the weight should be returned
	 */
	inline TL getW_lb(int i) const {
		return W_lb[i];
	}
	//! get number of variables
	inline int getNVars() const {
		return nVars;
	}
	//! get the type of the instance
	inline bool isWeighted() const {
		return isWcnf;
	}
	//! print the optimal solution in the maxsat evaluation format
	inline void printSolution() const {
		printf("c total generalized unit propagation = %d, success = %.2lf%%\n", total_gup, 100.0*succ_gup/total_gup);
#ifdef STATS
		printf("c number of nodes expanded per level:\n");
		for (int i=1; i<=nVars; ++i) {
			if (explored[i] > 0)
				printf("c depth %d: %d %lld\n", i, explored[i], sum_cost[i]/explored[i]);
		}
#endif
		if (bestCost == hard) {
			puts("s UNSATISFIABLE");
			return;
		}
		// we assume here that printSolution is only called at the end
		puts("s OPTIMUM FOUND");
		printf("c Optimal Solution = %llu\nv", bestCost);
		int j = 0;
		set<int> used;
		for (int i=1; i<=nVars; ++i)
			used.insert(mapping[i]);
		for (int i=1; i<=maxVn; ++i)
			// if variable i did not occur in the formula, assign it to true
			if (used.find(i) == used.end())
				printf(" %d", i);
			// otherwise take sign from the best assignment found (bestA)
			else {
				++j;
				assert(j <= nVars);
				printf(" %d", (int)bestA[j] * mapping[j]);
			}
		assert(j == nVars);
		putchar('\n');
	}
	//! get number of clauses of literal L
	/*! \param L literal to which the number of clauses should be returned
	 */
	inline TL getLength(int L) const {
		assert(!assigned_values[abs(L)]);
#ifndef NDEBUG
		TL sum = 0;
		for (vector<int>::const_iterator it=appears[L].begin(); it!=appears[L].end(); ++it)
			if (all_clauses.getDeleteFlag(*it) == false && all_clauses.getLength(*it) > 1)
				sum += all_clauses.getWeight(*it);
		assert(sum == W_binary[L] + W_large[L]);
#endif
		return W_large[L] + W_binary[L] + W_unit[L];
	}
	//! get number of unit clauses involving literal L
	/*! \param L literal L
	 */
	inline TL getUnitLength(int L) const {
		assert(W_unit[L] >= 0);
		return W_unit[L];
	}
	//! get number of binary clauses involving literal L
	/*! \param L literal L
	 */
	inline TL getBinaryLength(int L) const {
#ifndef NDEBUG
		TL sum = 0;
		for (vector<int>::const_iterator it=appears[L].begin(); it!=appears[L].end(); ++it)
			if (!all_clauses.getDeleteFlag(*it) && all_clauses.getLength(*it) == 2)
				sum += all_clauses.getWeight(*it);
		assert(W_binary[L] == sum);
#endif
		return W_binary[L];
	}
	//! check if an assignment of L exceeds bestCost
	/*! \param L the literal to be checked
	 *  \returns true iff assignment of L leads to costs < bestCost
	 */
	inline bool assignmentPossible(int L) const {
		return (TL)cost[n_assigned] + W_unit[-L] < (TL)bestCost;
	}
	//! assign literal L the value true
	/*! \param L literal to be assigned
	 *  \returns true iff assignment does not lead to costs >= bestCost
	 */
	inline bool assignLiteral(int L) {
		if (!assignmentPossible(L))
			return false;
#ifdef DEBUG
		cout << "assign literal " << L << endl;
#endif
		assert(-nVars <= L && L <= nVars && L != 0 && assigned_values[abs(L)] == 0);
		assert(W_unit[-L] == W_unit_save[-L]);
		cost[n_assigned+1] = cost[n_assigned] + (ULL)W_unit[-L];
		deleteFulfilled(L);
		// remove literal -L from clauses
		assigned_values[abs(L)] = L > 0? 1 : -1;
		assigned_literals[n_assigned++] = L;
		all_clauses.assignVariable(-L);
		removeLiteral(-L);
#ifdef STATS
		++explored[n_assigned];
		sum_cost[n_assigned] += cost[n_assigned];
		if (n_assigned == nVars) {
			int mexpl = 0;
			for (int i=1; i<=nVars; ++i) {
				if (explored[i] >= explored[mexpl])
					mexpl = i;
				/*
				if (explored[i] > 0)
					printf("c depth %d: %d %llu\n", i, explored[i], sum_cost[i]/explored[i]);
				*/
			}
			printf("c maximum explored in depth %d\n", mexpl);
	//		for (int i=1; i<=nVars; ++i)
	//			sum_cost[i] = explored[i] = 0;
		}
#endif
		// is it a complete assignment?
		if (n_assigned == nVars) {
			memcpy(bestA, assigned_values, sizeof(char) * (nVars + 1));
			bestCost = cost[n_assigned];
			printf("o %llu\n", bestCost);
			// for debugging reasons one may print intermediate solutions
	//		printSolution();
			fflush(stdout);
		}
		return true;
	}

	//! unassign literal V
	/*! \param L literal which is reset
	 */
	void unassignLiteral() {
		assert(n_assigned > 0);
		int L = assigned_literals[n_assigned-1];
#ifdef DEBUG
		cout << "unassign literal " << L << endl;
#endif
		restoreClauses(L);
		--n_assigned;
		assigned_values[abs(L)] = 0;
		assert(appears_len[L] == (int)appears[L].size());
		// add literal -L back to clauses
		addLiteral(-L);
		// remove delete flag from clauses which become unfulfilled
		for (vector<int>::const_iterator it=appears[L].begin(); it!=appears[L].end(); ++it) {
			int l = all_clauses.getLength(*it);
			if (l == 1) {
				assert(!all_clauses.getDeleteFlag(*it));
				continue;
			}
			assert(l > 1);
			assert(all_clauses.getDeleteFlag(*it));
			assert(!all_clauses.getSpecialFlag(*it));
			const int_c *literals = all_clauses.getLiterals(*it);
			assert(all_clauses.getWeight(*it) > 0);
			if (l == 2) {
				W_binary[literals[0]] += all_clauses.getWeight(*it);
				W_binary[literals[1]] += all_clauses.getWeight(*it);
			}
			else if (l >= 3) {
				ULL w = all_clauses.getWeight(*it);
				for (int i=0; i<l; ++i)
					W_large[literals[i]] += w;
			}
			all_clauses.removeDeleteFlagFromClause(*it);
			// check if we need to reinsert it into appears lists
			for (int i=0; i<l; ++i) {
				if (literals[i] == L)
					continue;
#ifdef DEBUG
				if (assigned_values[abs(literals[i])]) {
					for (int j=0; j<l; ++j)
						printf("%d(%d) ", literals[j], assigned_values[abs(literals[j])]);
					printf("L = %d\n", L);
				}
#endif
				assert(!assigned_values[abs(literals[i])]);
#ifndef NDEBUG
				bool found = false;
				for (vector<int>::const_iterator it2=appears[literals[i]].begin(); it2!=appears[literals[i]].end(); ++it2)
					if (*it2 == *it) {
						found = true;
						break;
					}
#endif
				assert(appears_len[literals[i]] == (int)appears[literals[i]].size());
				if (appears_traversed[literals[i]] > appears_traversed[L]) {
#ifndef NDEBUG
					if (found) printf("%d %llu %lld %lld\n", l, all_clauses.getWeight(*it), appears_traversed[literals[i]], appears_traversed[L]);
					assert(!found);
#endif
					appears[literals[i]].push_back(*it);
					++appears_len[literals[i]];
				}
#ifndef NDEBUG
				else
					assert(found);
#endif
			}
		}
	}
	//! compute lower bound (plus inference rules)
	/*! \returns true iff lower bound plus current cost exceeds the best solution
	 *  \remark cost may be increased resulting from formula transformations with inference rules
	 */
	ULL bestMinusLowerBound() {
#ifdef RBFS
		if (n_assigned == nVars)
			return cost[n_assigned];
		needed_for_skip = MAXWEIGHT - cost[n_assigned];
#else
		needed_for_skip = bestCost - cost[n_assigned];
#endif
		changed.clear();
		assert(n_assigned < nVars);
		if (!needed_for_skip)
			return 0;
		++timestamp;
#ifdef DEBUG
		cout << "compute lower bound" << endl;
#endif
#ifndef NDEBUG
		for (int i=1; i<=nVars; ++i)
			if (!assigned_values[i])
				assert(literal_data[i] <= 0 && literal_data[-i] <= 0);
#endif
		// binary resolution of clauses (i, x) and (-i, x)
		// ternary resolution of clauses (i, x, y) (-i, x, y)
		for (int i=1; i<=nVars; ++i) {
			if (assigned_values[i])
				continue;
			W_lb[i] = W_lb[-i] = 0;
			assert(W_unit[i] == W_unit_save[i]);
	//		if (n_assigned <= nVars/3) {
				W_unit[i] += binary_ternary_resolution(i);
#ifdef PROP_LIST
				// check if the literal i can be propagated
				if (onstack[i] < 0 && W_unit[i] + (TL)cost[n_assigned] >= (TL)bestCost) {
					onstack[i] = propagation_stack_size;
					propagation_stack[propagation_stack_size++] = i;
				}
#endif
				assert(W_unit[-i] == W_unit_save[-i]);
				W_unit[-i] += binary_ternary_resolution(-i);
#ifdef PROP_LIST
				// check if the literal -i can be propagated
				if (onstack[-i] < 0 && W_unit[i] + (TL)cost[n_assigned] >= (TL)bestCost) {
					onstack[-i] = propagation_stack_size;
					propagation_stack[propagation_stack_size++] = -i;
				}
#endif
	//		}
		}
		// now save information to be able to restore the old clause data
	//	if (n_assigned <= nVars/3)
			for (int i=1; i<=nVars && needed_for_skip > 0; ++i) {
				if (assigned_values[i])
					continue;
				TL mw = min(W_unit[i], W_unit[-i]);
				TL t1 = W_unit[i] - W_unit_save[i];
				TL t2 = W_unit[-i] - W_unit_save[-i];
				if (mw > 0) {
					saveAddition(cost[n_assigned], mw);
					saveSubtraction(needed_for_skip, mw);
					W_unit[i] -= mw;
					W_unit[-i] -= mw;
				}
				TL diff;
				if (mw != t1) {
					bool sign = false;
					if (mw > t1)
						diff = mw - t1;
					else {
						diff = t1 - mw;
						sign = true;
					}
					while(diff > 0) {
						TL t = min(diff, (TL)MAXWEIGHT);
						diff -= t;
						rlist.addEntry(i - nVars);
						rlist.commit(timestamp++, (ULL)t, sign);
					}
				}
				if (mw != t2) {
					bool sign = false;
					if (mw > t2)
						diff = mw - t2;
					else {
						diff = t2 - mw;
						sign = true;
					}
					while(diff > 0) {
						TL t = min(diff, (TL)MAXWEIGHT);
						diff -= t;
						rlist.addEntry(-i - nVars);
						rlist.commit(timestamp++, (ULL)t, sign);
					}
				}
				W_unit_save[i] = W_unit[i];
				W_unit_save[-i] = W_unit[-i];
			}
		// now use generalized unit propagation to increase the lower bound
		if (needed_for_skip > 0)
			generalized_unit_propagation();
		// go through all changed clauses and reset their weights which were possibly changed by the generalized unit propagation
		ULL diff;
		for (vector<int>::const_iterator it=changed.begin(); it!=changed.end(); ++it) {
			if ((diff = all_clauses.getSavedWeight(*it)-all_clauses.getWeight(*it)) == 0)
				continue;
			const int_c *literals = all_clauses.getLiterals(*it);
			assert(*literals >= -nVars && *literals <= nVars && *literals != 0);
			// reset weight
			assert(diff > 0);
			if (all_clauses.getLength(*it) == 2) {
				W_binary[literals[0]] += diff;
				W_binary[literals[1]] += diff;
				W_lb[literals[0]] += diff;
				W_lb[literals[1]] += diff;
			}
			else {
				for (int j=all_clauses.getLength(*it)-1; j>=0; --j) {
					W_large[literals[j]] += diff;
					W_lb[literals[j]] += diff;
				}
			}
			all_clauses.resetWeight(*it);
			assert(!all_clauses.getDeleteFlag(*it));
		}
		ULL ret = needed_for_skip;
		for (int i=1; i<=nVars; ++i) {
			if (assigned_values[i])
				continue;
#ifndef NDEBUG
			for (vector<int>::const_iterator it=appears[i].begin(); it!=appears[i].end(); ++it)
				assert(all_clauses.getSavedWeight(*it) == all_clauses.getWeight(*it));
			for (vector<int>::const_iterator it=appears[-i].begin(); it!=appears[-i].end(); ++it)
				assert(all_clauses.getSavedWeight(*it) == all_clauses.getWeight(*it));
#endif
			if (appears_len[i] < (int)appears[i].size()) {
				reverse(appears[i].begin() + appears_len[i], appears[i].end());
				appears_len[i] = appears[i].size();
			}
			if (appears_len[-i] < (int)appears[-i].size()) {
				reverse(appears[-i].begin() + appears_len[-i], appears[-i].end());
				appears_len[-i] = appears[-i].size();
			}
			W_lb[i] += W_unit_save[i] - W_unit[i];
			W_lb[-i] += W_unit_save[-i] - W_unit[-i];
			W_unit[i] = W_unit_save[i];
			assert(W_unit[i] >= 0);
			W_unit[-i] = W_unit_save[-i];
			assert(W_unit[-i] >= 0);
			// it may be possible that we still can do unary resolution here
			unary_resolution(i);
		}
		if (n_assigned == 0)
			printf("c first lower bound: %llu\n", (unsigned long long)(bestCost - ret));
		
		//edited by luo
		if(first_checked == 0)
		{
			first_checked = 1;
			unsigned long long first_lower_bound = (unsigned long long)(bestCost - ret);
			if(first_lower_bound>first_lower_bound_threshold)
			{
				printf("c the first_lower_bound %llu is greater than the first_lower_bound_threshold %llu, terminate!\n", first_lower_bound, first_lower_bound_threshold);
                printSolution();
				exit(-1);
			}
		}
		//
		
        //edited by Wenxuan
        {
            unsigned long long first_lower_bound = (unsigned long long)(bestCost - ret);
            if(first_lower_bound>first_lower_bound_threshold)
            {
                printf("c we arrive at lower bound %llu which is greater than the lower_bound_threshold %llu, terminate!\n", first_lower_bound, first_lower_bound_threshold);
                printSolution();
                exit(-1);
            }
        }
        //
        
#ifdef RBFS
		return MAXWEIGHT - ret;
#endif
		return ret;
	}
	//! CNF_Formula destructor
	~CNF_Formula() {
#ifdef DEBUG
		printf("c finished with timestamp %lld\n", timestamp);
#endif
#ifdef FUIP
		printf("c fuip statistics: %.2lf%% cases had improvements\n", (100.0*succ_cnt_fuip)/total_cnt_fuip);
		delete [] tadj;
		delete [] visit2;
		delete [] Q2;
		delete [] ref_cnt;
#endif
#ifdef STATS
		delete [] sum_cost;
		delete [] explored;
#endif
		// subtract nVars to get to the beginning of the arrays
		W_unit -= nVars;
		W_binary -= nVars;
		W_large -= nVars;
		W_unit_save -= nVars;
		appears -= nVars;
		unit_implication_list -= nVars;
		appears_traversed -= nVars;
		literal_data -= nVars;
		W_lb -= nVars;
		appears_len -= nVars;
		// delete all arrays
		delete [] appears_len;
		delete [] vars;
		delete [] Q;
		delete [] literal_order;
		delete [] literal_data;
		delete [] ternary_clause_data;
		delete [] assigned_values;
		delete [] W_binary;
		delete [] W_large;
		delete [] W_unit_save;
		delete [] appears_traversed;
		delete [] appears;
		delete [] unit_implication_list;
		delete [] assigned_literals;
		delete [] W_unit;
		delete [] mapping;
		delete [] maps_to;
		delete [] bestA;
		delete [] W_lb;
		delete [] cost;
#ifdef PROP_LIST
		onstack -= nVars;
		delete [] onstack;
		delete [] propagation_stack;
#endif
	}
	inline ULL getHardWeight() const {
		return hard;
	}
	//! return the best cost of a complete assignment found so far
	inline ULL getBestCost() const {
		return bestCost;
	}
	//! initialize the best assignment to the assignment of besta
	inline void saveBest(ULL best, char *besta) {
		assert(best <= bestCost);
		bestCost = best;
		for (int i=1; i<=maxVn; ++i)
			if (maps_to[i] > 0)
				bestA[maps_to[i]] = besta[i];
	}
#ifdef PROP_LIST
	//! check if a literal can be propagated because there is a hard unit clause
	inline int propagateLiteral() {
		int L;
		// check the literals on the propagation stack if they can still be propagated
		while(propagation_stack_size > 0) {
			// remove the top literal
			L = propagation_stack[propagation_stack_size-1];
			--propagation_stack_size;
			onstack[L] = -1;
			if ((TL)W_unit[L] + (TL)cost[n_assigned] >= (TL)bestCost/* || getLength(-L) <= W_unit[L]*/) {
				assert(!assigned_values[abs(L)]);
				return L;
			}
		}
		return 0;
	}
#endif
};

#endif
