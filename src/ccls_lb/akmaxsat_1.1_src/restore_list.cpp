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

#include <assert.h>
#include <string.h>
#include "restore_list.hpp"

//! constructor of class restore_list
restore_list::restore_list() {
	size = 10000;
	pos = data = new int[size];
	end = data + size;
	added = 0;
}

//! destructor of the class restore_list
restore_list::~restore_list() {
	delete [] data;
}

//! doubles the amount of available positions in data
void restore_list::increase_data() {
	size *= 2;
	int *data_new = new int[size];
	memcpy(data_new, data, sizeof(int) * size / 2);
	pos = data_new + (pos - data);
	delete [] data;
	data = data_new;
	end = data + size;
}
