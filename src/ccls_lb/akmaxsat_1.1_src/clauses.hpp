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

#ifndef CLAUSES_HPP_INCLUDE
#define CLAUSES_HPP_INCLUDE

#include <algorithm>
#include <string.h>
#include <iostream>
#include <assert.h>
using namespace std;

typedef int int_c;
typedef unsigned long long ULL;

extern ULL MAXWEIGHT;

/*! \file clauses.hpp Documentation of class Clauses
 */
//! The class Clauses is a data structure which stores and maintains a list of clauses efficiently
class Clauses {
	// private member variable
	//! clauses contains clauses in the format \<length\> <traversal id> \<literal 1\> ... \<literal length\>
	int_c *clauses;
	//! capacity of the array clauses - a power of 2
	int capacity;
	//! capacity of the array headsFreeList - log2(capacity)
	int logcapacity; 
	//! pointers to the first free block of size 2^i
	int *headsFreeList;
	//! stores which literals are currently assigned to false
	bool *assigned;
	//! number of variables
	int nVars;
	//! bit which indicates deletion of the clause
	const static int DELETED = 1<<30;
	//! bit which indicates a marker
	const static int MARKED = 1<<29;
	//! bit which indicates that the clause is special
	const static int SPECIAL = 1<<28;
	//! bit which indicates that a clause was changed since it was last traversed
	const static int CHANGED = 1<<27;
	//! maximum length of a clause
	const static int MAXLEN = (1<<27)-1;

	// private functions
	//! doubles the amount of memory available to store clauses
	void doubleStorage();
	//! add a free memory block of size 2^list_id to the list of empty blocks
	inline void addFreeBlock(int pos, int list_id) {
		clauses[pos] = headsFreeList[list_id];
		headsFreeList[list_id] = pos;
	}
	//! remove the first block of size 2^list_id from the list of empty blocks
	inline void popFreeBlock(int list_id) {
		assert(headsFreeList[list_id] > 0);
		headsFreeList[list_id] = clauses[headsFreeList[list_id]];
	}
	//! add special flag to clause
	/*! \param clause_id The id of the clause to which a special flag should be added
	 */
	inline void addSpecialFlag2Clause(int clause_id) {
		assert(clause_id > 0 && clause_id < capacity && clauses[clause_id] > 0 && (clauses[clause_id] & SPECIAL) == 0);
		clauses[clause_id] |= SPECIAL;
	}

	//public functions
public:
	//! Clauses constructor
	Clauses();
	//! initialize the number of variables and the assigned array
	void init(int n) {
		assert(assigned == NULL);
		nVars = n;
		assigned = new bool[2 * nVars + 1];
		memset(assigned, false, (2 * nVars + 1)*sizeof(bool));
		assigned += nVars;
	}
	//! Add a clause to the list of clauses.
	/*! \param literals specifies the literals of the clause
	 *  \param length gives the length of the clause
	 *  \param weight gives the weight of the clause
	 *  \returns returns the clause id
	 */
	inline int addClause(int_c *literals, int length, ULL weight) {
#ifdef DEBUG
		for (int i=0; i<length; ++i)
			printf("%d ", literals[i]);
		puts("");
#endif
		assert(literals != NULL && length >= 0 && length <= MAXLEN);
		// find a free block for storing the new clause
		int pos = 0, k;
		length += 5;
		for (k=2; k<logcapacity; ++k)
			if ((1<<k) >= length) {
				pos = headsFreeList[k];
				if (pos)
					break;
			}
		// increase storage as long as no large enough block was found
		while(!pos) {
			doubleStorage();
			// after doubling storage, the biggest available block has size 2^(logcapacity-2)
			if ((1 << (logcapacity - 2)) >= length) {
				pos = headsFreeList[logcapacity - 2];
				assert(pos);
				k = logcapacity - 2;
				break;
			}
		}
#ifdef DEBUG
		cout << "k = " << k << " pos = " << pos << endl;
#endif
		popFreeBlock(k);
		// now split the block until its size is the smallest power of 2 >= length
		while(k > 0 && (1<<(k-1)) >= length) {
			--k;
			addFreeBlock(pos + (1<<k), k);
		}
		length -= 5;
#ifdef DEBUG
		cout << "now k = " << k << endl;
		for (int i=0; i<length; ++i) {
			cout << literals[i] << " ";
			cout.flush();
		}
		cout << endl;
#endif
		clauses[pos] = length;
		*((ULL*)&clauses[pos+1]) = *((ULL*)&clauses[pos+3]) = weight;
		memcpy(clauses+pos+5, literals, sizeof(int_c) * length);
#ifdef DEBUG
		cout << "memcpy done" << endl;
#endif
		return pos;
	}
	//! lit is assigned to false
	/*! \param lit is the literal which is assigned false
	 */
	inline void assignVariable(int lit) {
		assigned[lit] = true;
	}
	//! assignment of lit is taken back
	/*! \param lit is the literal which was assigned false and becomes unassigned
	 */
	inline void unassignVariable(int lit) {
		assigned[lit] = false;
	}
	//! decrease the length of a clause because of an assignment
	/*! \param clause_id is the id of the clause whose length is decreased
	 */
	inline void decreaseLength(int clause_id) {
		clauses[clause_id] = (clauses[clause_id] | CHANGED) - 1;
	}
	//! increase the length of a clause because of an assignment
	/*! \param clause_id is the id of the clause whose length is increased
	 */
	inline void increaseLength(int clause_id) {
		clauses[clause_id] = (clauses[clause_id] | CHANGED) + 1;
	}
	//! Delete clause clause_id.
	/*! \param clause_id The id of the clause to be deleted.
	 */
	inline void deleteClause(int clause_id) {
		assert(clause_id > 0 && clause_id < capacity && (clauses[clause_id] & DELETED) == DELETED && (clauses[clause_id] & SPECIAL) == SPECIAL);
		int k = 2, w = getLength(clause_id) + 5;
		while((1<<k) < w)
			++k;
		addFreeBlock(clause_id, k);
	}
	//! prepare a clause for deletion
	/*! \param clause_id The id of the clause.
	 *  \remark add a reference counter
	 */
	inline void prepareDelete(int clause_id) {
		assert(clause_id > 0 && clause_id < capacity);
		assert(clauses[clause_id + 1] == 0);
		addSpecialFlag2Clause(clause_id);
		clauses[clause_id + 5] = getLength(clause_id);
	}
	//! decrease reference counter
	/*! \param clause_id The id of the clause.
	 */
	inline void decreaseCounter(int clause_id) {
		assert(clause_id > 0 && clause_id < capacity && (clauses[clause_id] & DELETED) == DELETED && (clauses[clause_id] & SPECIAL) == SPECIAL);
		if (--clauses[clause_id+5] == 0)
			deleteClause(clause_id);
	}
	//! Add a delete flag to a clause.
	/*! \param clause_id The id of the clause to be flagged
	 */
	inline void addDeleteFlag2Clause(int clause_id) {
		assert(clause_id > 0 && clause_id < capacity && (clauses[clause_id] & DELETED) == 0);
		clauses[clause_id] |= DELETED;
	}
	//! mark the clause.
	/*! \param clause_id The id of the clause to be marked
	 */
	inline void addMarker2Clause(int clause_id) {
		assert(clause_id > 0 && clause_id < capacity && clauses[clause_id] > 0 && (clauses[clause_id] & MARKED) == 0);
		clauses[clause_id] |= MARKED;
	}
	//! remove the special flag from a clause
	/*! \param clause_id The id of the clause
	 */
	inline void removeSpecialFlagFromClause(int clause_id) {
		assert(clause_id > 0 && clause_id < capacity && clauses[clause_id] > 0 && (clauses[clause_id] & SPECIAL));
		clauses[clause_id] ^= SPECIAL;
	}
	//! Remove marker from a clause.
	/*! \param clause_id The id of the clause.
	 */
	inline void removeMarkerFromClause(int clause_id) {
		assert(clause_id > 0 && clause_id < capacity && clauses[clause_id] > 0 && (clauses[clause_id] & MARKED));
		clauses[clause_id] ^= MARKED;
	}
	//! Remove a delete flag from a clause.
	/*! \param clause_id The id of the clause.
	 */
	inline void removeDeleteFlagFromClause(int clause_id) {
		assert(clause_id > 0 && clause_id < capacity && (clauses[clause_id] & DELETED));
		clauses[clause_id] ^= DELETED;
	}
	//! Get the delete flag of a clause.
	/*! \param clause_id The id of the clause
	 *  \returns true if clause is marked as deleted, false otherwise
	 */
	inline bool getDeleteFlag(int clause_id) const {
#ifdef DEBUG
		if (clauses[clause_id] == 0)
			printf("clause_id = %d\n", clause_id);
#endif
		assert(clause_id > 0 && clause_id < capacity && clauses[clause_id] != 0);
		return clauses[clause_id] & DELETED;
	}
	//! Get the marker of a clause.
	/*! \param clause_id The id of the clause
	 *  \returns true if clause is marked, false otherwise
	 */
	inline bool getMarker(int clause_id) const {
		assert(clause_id > 0 && clause_id < capacity && clauses[clause_id] != 0);
		return clauses[clause_id] & MARKED;
	}
	//! Get the special flag of a clause.
	/*! \param clause_id The id of the clause
	 *  \returns true if clause is flagged as special, false otherwise
	 */
	inline bool getSpecialFlag(int clause_id) const {
		assert(clause_id > 0 && clause_id < capacity && clauses[clause_id] != 0);
		return clauses[clause_id] & SPECIAL;
	}
	//! Get a list of literals of a clause.
	/*! \param clause_id The id of the clause.
	 */
	inline const int_c *getLiterals(int clause_id) const {
		assert(clause_id > 0 && clause_id < capacity);
		// check if clause length has changed
		if (clauses[clause_id]&CHANGED) {
			// move the unassigned literals to the front
			clauses[clause_id] ^= CHANGED;
			int needed = getLength(clause_id);
			int *sptr = clauses + clause_id + 5;
			while(needed && !assigned[*sptr]) {
				++sptr;
				--needed;
			}
			if (!needed)
				return clauses + clause_id + 5;
			int *ptr = sptr + 1;
			int c = needed;
			while(needed) {
				if (!assigned[*ptr++])
					--needed;
			}
			--ptr;
			while(c--) {
				swap(*sptr, *ptr);
				if (!c) break;
				--ptr;
				while(assigned[*ptr])
					--ptr;
				++sptr;
				while(c && !assigned[*sptr]) {
					--c;
					++sptr;
				}
			}
		}
		return clauses + clause_id + 5;
	}
	//! get the length of a clause.
	/*! \param clause_id The id of the clause.
	 *  \returns the length of the clause
	 */
	inline int getLength(int clause_id) const {
		assert(clause_id > 0 && clause_id < capacity && clauses[clause_id] != 0);
		return clauses[clause_id]&MAXLEN;
	}
	//! get the weight of a clause.
	/*! \param clause_id The id of the clause.
	 *  \returns the weight of the clause
	 */
	inline ULL getWeight(int clause_id) const {
		assert(clause_id > 0 && clause_id < capacity);
		return *((ULL*)&clauses[clause_id+1]);
	}
	//! get the saved weight of a clause.
	/*! \param clause_id The id of the clause.
	 *  \returns the weight of the clause
	 */
	inline ULL getSavedWeight(int clause_id) const {
		assert(clause_id > 0 && clause_id < capacity && getLength(clause_id) > 0);
		return *((ULL*)&clauses[clause_id+3]);
	}
	//! reset the weight of a clause to the saved weight.
	/*! \param clause_id The id of the clause.
	 */
	inline void resetWeight(int clause_id) {
		assert(clause_id > 0 && clause_id < capacity && getLength(clause_id) > 0);
		assert(!getSpecialFlag(clause_id));
		if (getWeight(clause_id) == getSavedWeight(clause_id))
			return;
		assert(getWeight(clause_id) < getSavedWeight(clause_id));
		*((ULL*)&clauses[clause_id + 1]) = *((ULL*)&clauses[clause_id + 3]);
		assert(getWeight(clause_id) > 0);
		clauses[clause_id] &= ~DELETED;
	}
	//! save the current weight of a clause.
	/*! \param clause_id The id of the clause.
	 *  \remark saves a copy of the current weight
	 */
	inline void saveWeight(int clause_id) {
		assert(clause_id > 0 && clause_id < capacity && getLength(clause_id) > 0);
		*((ULL*)&clauses[clause_id+3]) = *((ULL*)&clauses[clause_id+1]);
	}	
	//! increase the weight of a clause.
	/*! \param clause_id The id of the clause.
	 *  \param w The weight to be added (w != 0).
	 */
	inline void addWeight(int clause_id, ULL w, bool change_saved = false) {
		assert(clause_id > 0 && clause_id < capacity && w != 0);
		assert(!getSpecialFlag(clause_id));
		if (getWeight(clause_id) == 0) {
			assert(getDeleteFlag(clause_id) && w > 0);
			removeDeleteFlagFromClause(clause_id);
		}
		assert(w <= MAXWEIGHT - getWeight(clause_id));
		*((ULL*)&clauses[clause_id + 1]) += w;
		if (change_saved)
			*((ULL*)&clauses[clause_id + 3]) += w;
	}
	//! decrease the weight of a clause.
	/*! \param clause_id The id of the clause.
	 *  \param w The weight to be subtracted (w != 0).
	 */
	inline void subtractWeight(int clause_id, ULL w, bool change_saved = false) {
		assert(clause_id > 0 && clause_id < capacity && w != 0 && !getDeleteFlag(clause_id));
		assert(!getSpecialFlag(clause_id));
		*((ULL*)&clauses[clause_id + 1]) -= w;
		if (change_saved) {
			assert(getSavedWeight(clause_id) >= w);
			*((ULL*)&clauses[clause_id + 3]) -= w;
		}
		if (getWeight(clause_id) == 0)
			addDeleteFlag2Clause(clause_id);
	}
	~Clauses();
};

#endif
