/* This module defines a number of auxilary tools for the generalized Ising solver.
 *
 * Author: Wenxuan Huang
 * Maintainer: Wenxuan Huang, Daniil Kitchaev
 * Date: 15 March, 2015
 *
 */

#ifndef TOOLS_H
#define TOOLS_H

#include <iostream>
#include <fstream>
#include <string>
#include <vector>
#include <map>
#include <set>
#include <sstream>
#include <cerrno>
#include "boost/tuple/tuple.hpp"
#include "boost/tuple/tuple_comparison.hpp"
#include "boost/tuple/tuple_io.hpp"
#include "boost/lexical_cast.hpp"
#include "boost/regex.hpp"
#include "boost/algorithm/string/regex.hpp"

using namespace std;
using namespace ::boost::tuples;
using namespace ::boost;

inline int floor_int_division(int a, int b) { return int(floor(double(a)/double(b))); }

inline double round(double d) { return floor(d + 0.5); }

inline int positive_modulo(int i, int n) { return (i % n + n) % n; }

void matchnumber(map<tuple<int,int,int,int,int,int>, double >& dictionary,double number,set<tuple<int,int,int,int,int,int> > &list);

long long myPow(long long x, long long p);

template <typename Iterator>
bool next_combination(const Iterator first, Iterator k, const Iterator last) {
    /* Credits: Thomas Draper */
    if ((first == last) || (first == k) || (last == k)) {
        return false;
	}
    Iterator itr1 = first;
    Iterator itr2 = last;
    ++itr1;
    if (last == itr1) {
        return false;
	}
    itr1 = last;
    --itr1;
    itr1 = k;
    --itr2;
    while (first != itr1) {
        if (*--itr1 < *itr2) {
            Iterator j = k;
            while (!(*itr1 < *j)) ++j;
            std::iter_swap(itr1,j);
            ++itr1;
            ++j;
            itr2 = k;
            std::rotate(itr1,j,last);
            while (last != j) {
                ++j;
                ++itr2;
            }
            std::rotate(k,itr2,last);
            return true;
        }
    }
    std::rotate(first,k,last);
    return false;
}

template <typename type1>
void convertJ_neg1_pos1toJ(map<set<type1>,double> &J_negative1_positive1, map<set<type1>,double> &J,double &constant_term) {
    for (typename map<set<type1>,double>::iterator it1=J_negative1_positive1.begin(); it1!=J_negative1_positive1.end(); it1++) {
        set<type1> tuple_set=it1->first;
        vector<type1> tuple_vector;

        for (typename set<type1>::iterator it=tuple_set.begin();it!=tuple_set.end();it++) {
            tuple_vector.push_back(*it);
        }

        double value=it1->second;
        int size_of_set=tuple_set.size();
        for (size_t k=size_of_set; k>0.1; k--) {
            int k_int=k;
            do {
                set<type1> subset;
                for(typename vector<type1>::iterator it2=tuple_vector.begin(); it2!=tuple_vector.begin()+k;it2++) {
                    subset.insert(*it2);
                }
                J[subset]+=value*myPow(2,k_int)*myPow(-1,size_of_set-k_int);
            }
            while(next_combination(tuple_vector.begin(),tuple_vector.begin() + k,tuple_vector.end()));
        }
        constant_term+=value*myPow(-1,size_of_set);
    }
}

template<typename type1>
void findminmax(map<type1, double > &dictionary,double &min,double &max ) {
    min=1e100;
    max=-1e100;
    for (typename map<type1, double >::iterator ait=dictionary.begin(); ait!=dictionary.end(); ait++) {
        if (ait->second<min) {
            min=ait->second;
        }
        if (ait->second>max) {
            max=ait->second;
		}
    }
}

template<typename type1, typename type2>
void printmap(map<type1,type2>&thismap) {
    cout<<"\n";
    for(typename map<type1,type2>::iterator it = thismap.begin(); it != thismap.end(); ++it) {
        cout<<(*it).first<<":"<<(*it).second<<endl;
    }
}

template<typename type1,typename type2,typename type3>
void printmapofmap(map<type1,map<type2,type3> >&thismap) {
    for(typename map<type1,map<type2,type3> >::iterator it = thismap.begin(); it != thismap.end(); ++it) {
        cout<<(*it).first<<":"<<endl;
        printmap((*it).second);
    }
}

template<typename type1>
void printvector(type1 &thisvector) {
    for(typename type1::iterator it = thisvector.begin(); it != thisvector.end(); ++it) {
        cout<<(*it)<<", ";
    }
}

template<typename type1>
void printvectorofvector(type1 &thisvector) {
    for(typename type1::iterator it = thisvector.begin(); it != thisvector.end(); ++it) {
        cout<<"\n";
        printvector(*it);
    }
}

template<typename type1>
void printvectorofmap(type1 &thisvector) {
    for(typename type1::iterator it = thisvector.begin(); it != thisvector.end(); ++it) {
        cout<<"\n ";
        printmap(*it);
    }
}

template<typename type1,typename vectortype>
void printmapofvector(map<type1,vectortype>&thismap) {
    cout<<"\n";
    for(typename map<type1,vectortype >::iterator it = thismap.begin(); it != thismap.end(); ++it) {
        cout<<(*it).first<<": ";
        printvector((*it).second);
        cout<<"\n";
    }
}

template<typename type1,typename type2>
void printmapfromsets(map<type1,type2>&thismap) {
    cout<<"\n";
    for(typename map<type1,type2>::iterator it = thismap.begin(); it != thismap.end(); ++it){
		printvector((*it).first);
        cout<<": ";
        cout<<(*it).second;
        cout<<"\n";
    }
}

template<typename type1,typename type2,typename type3>
void getkeystoset(map<type1,type2> &thismap, set<type1> &thisset) {
    for(typename map<type1,type2>::iterator it = thismap.begin(); it != thismap.end(); ++it) {
        thisset.insert(*(it).first);
    }
}

template<typename type1,typename type2,typename type3>
void getkeystovector(map<type1,type2> &thismap, vector<type1> &thisset) {
    for(typename map<type1,type2>::iterator it = thismap.begin(); it != thismap.end(); ++it) {
        thisset.push_back(*(it).first);
    }
}

template<int k>
int getimax(map<tuple<int,int>,int> & spin) {
    vector<int> thisvector;
    for(typename map<tuple<int,int>,int>::iterator it = spin.begin(); it != spin.end(); ++it) {
        thisvector.push_back((*it).first.get<k>());
    }
    vector<int>::iterator it=max_element(thisvector.begin(), thisvector.end());
    return *it;
}

template<int k>
int getimax(map<tuple<int,int,int,int>,int> & spin) {
    vector<int> thisvector;
    for(typename map<tuple<int,int,int,int>,int>::iterator it = spin.begin(); it != spin.end(); ++it) {
        thisvector.push_back((*it).first.get<k>());
    }
    vector<int>::iterator it=max_element(thisvector.begin(), thisvector.end());
    return *it;
}

template<int k>
int getimin(map<tuple<int,int>,int> & spin) {
    vector<int> thisvector;
    for(typename map<tuple<int,int>,int>::iterator it = spin.begin(); it != spin.end(); ++it) {
        thisvector.push_back((*it).first.get<k>());
    }
    vector<int>::iterator it=min_element(thisvector.begin(), thisvector.end());
    return *it;
}

template<int k>
int getimin(map<tuple<int,int,int,int>,int> & spin) {
    vector<int> thisvector;
    for(typename map<tuple<int,int,int,int>,int>::iterator it = spin.begin(); it != spin.end(); ++it) {
        thisvector.push_back((*it).first.get<k>());
    }
    vector<int>::iterator it=min_element(thisvector.begin(), thisvector.end());
    return *it;
}

std::string exec(std::string command);

std::string get_file_contents(const char *filename);

void split_is(const std::string &s, char delim, std::vector<std::string> &elems);

void split_is(const std::string &s, std::string delim_regex, std::vector<std::string> &elems);

std::string to_string_is(int n);

std::string to_string_is(double d);

int stoi_is(std::string s);

double stod_is(std::string s);

void convertspintostring(map<tuple<int,int,int,int>,int>& spin, string &spinstring);

void printblock(map<tuple<int,int,int,int>,int> &thisblock);

void printblocklist(vector<map<tuple<int,int,int,int>,int> > &thisblocklist);
#endif
