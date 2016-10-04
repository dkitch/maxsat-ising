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

#ifndef RESTORE_LIST_HPP_INCLUDE

#define RESTORE_LIST_HPP_INCLUDE

#include "clauses.hpp"

/*! \file restore_list.hpp Documentation of class restore_list
 */

//! the class restore_list maintains a list of clauses which need to be restored when backtracking
class restore_list {
private:
	//! data contains data entries of the following form: pointer to clause c1, c2, ..., ck, weight, k, time_stamp
	int *data;
	//! pos points to one element after the last entry in data
	int *pos;
	//! end contains a pointer to the last allocated position in data
	int *end;
	//! size is the number of allocated positions in data
	int size;
	//! added counts the number of clauses added so far to the current data entry
	int added;
	//! doubles the amount of position available in the data array
	void increase_data();
public:
	//! constructor of class restore_list
	restore_list();
	//! destructor of class restore_list
	~restore_list();
	//! add clause to current data entry
	/*! \param clause_id is the id of the clause to be added
	 */
	inline void addEntry(int clause_id) {
		if (pos == end)
			increase_data();
		*pos++ = clause_id;
		++added;
	}
	//! retrieve a data entry
	/*! \param timestamp we restore only clauses which were deleted after time timestamp
	    \param length is set to the number of clauses belonging to the data entry
		\param deletion_time is the timestamp of the time when the deletion happened
		\param weight is the weight which should be added to the clauses belonging to this data entry
		\param sign indicates if we need to subtract or add the weight
		\returns NULL if no more data entry with timestamp > timestamp is available, otherwise a pointer to the first clause of the data entry is returned
	 */
	inline const int *retrieve(long long timestamp, int &length, long long &deletion_time, ULL &weight, bool &sign) {
		assert(added == 0);
		if (pos == data)
			return NULL;
		assert(pos >= data + 5);
		deletion_time = *((ULL*)(pos-2));
		if (deletion_time > timestamp) {
			length = *(pos-3);
			if (length & (1<<30)) {
				length ^= 1<<30;
				sign = true;
			}
			else
				sign = false;
			weight = *((ULL*)(pos-5));
			pos -= (5 + length);
			return pos;
		}
		return NULL;
	}
	//! commit a data entry
	/*! \param timestamp the time of the deletion
	    \param weight the weight which was subtracted or added to the clauses
		\param sign indicates if the weight was added or subtracted
	 */
	inline void commit(long long timestamp, ULL weight, bool sign) {
		assert(added > 0);
		if (pos + 5 > end)
			increase_data();
		*((ULL *)pos) = weight;
		pos += 2;
		if (sign)
			added |= 1 << 30;
		*pos++ = added;
		added = 0;
		*((ULL *)pos) = timestamp;
		pos += 2;
	}
};

#endif
