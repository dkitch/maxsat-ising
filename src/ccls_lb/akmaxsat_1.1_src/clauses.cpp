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

#include "clauses.hpp"

ULL MAXWEIGHT = (1ULL<<63) - 1;

//! doubles the amount of memory available to store clauses
void Clauses::doubleStorage() {
	capacity <<= 1;
	++logcapacity;
	int_c *clauses2 = new int_c[capacity];
	assert(clauses2 != NULL);
	memcpy(clauses2, clauses, sizeof(int_c) * capacity/2);
	delete [] clauses;
	clauses = clauses2;
	int *headsFreeList2 = new int[logcapacity];
	assert(headsFreeList2 != NULL);
	memcpy(headsFreeList2, headsFreeList, sizeof(int) * (logcapacity-1));
	delete [] headsFreeList;
	headsFreeList = headsFreeList2;
	assert(headsFreeList[logcapacity-2] == 0);
	// add the new storage block to the buddy memory management
	headsFreeList[logcapacity-2] = capacity/2;
	headsFreeList[logcapacity-1] = 0;
	clauses[capacity/2] = 0;
}

//! Clauses constructor
Clauses::Clauses() {
	assigned = NULL;
	logcapacity = 16;
	capacity = 1<<logcapacity;
	clauses = new int_c[capacity];
	headsFreeList = new int[logcapacity];
	for (int i=0; i+1<logcapacity; ++i) {
		headsFreeList[i] = 1<<i;
		clauses[1<<i] = 0;
	}
	headsFreeList[logcapacity-1] = 0;
}

//! Clauses destructor
Clauses::~Clauses() {
	delete [] clauses;
	assert(assigned != NULL);
	assigned -= nVars;
	delete [] assigned;
	delete [] headsFreeList;
}
