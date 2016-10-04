#include "tools.h"

using namespace std;
using namespace ::boost::tuples;
using namespace ::boost;

void matchnumber(map<tuple<int,int,int,int,int,int>, double >& dictionary,double number,set<tuple<int,int,int,int,int,int> > &list){
    list.clear();
    for (map<tuple<int,int,int,int,int,int>, double >::iterator ait=dictionary.begin(); ait!=dictionary.end(); ait++) {
        if (ait->second<=number+1e-5 && ait->second>=number-1e-5) {
            list.insert(ait->first);
        }
    }
}

long long myPow(long long x, long long p){
    if (p == 0) return 1;
    if (p == 1) return x;

    long tmp = myPow(x, p/2);
    if (p%2 == 0) return tmp * tmp;
    else return x * tmp * tmp;
}

std::string exec(std::string command) {
	// As with any exec, use with extreme care
    const char* cmd = command.c_str();
    FILE* pipe = popen(cmd, "r");
    if (!pipe) return "ERROR";
    char buffer[256];
    std::string result = "";
    while(!feof(pipe)) {
    	if(fgets(buffer, 256, pipe) != NULL) {
    		result += buffer;
		}
    }
    pclose(pipe);
    return result;
}

// Thanks to insanecoding.blogspot.com for this function
std::string get_file_contents(const char *filename){
	std::ifstream in(filename, std::ios::in | std::ios::binary);
	if (in) {
		std::string contents;
		in.seekg(0, std::ios::end);
		contents.resize(in.tellg());
		in.seekg(0, std::ios::beg);
		in.read(&contents[0], contents.size());
		in.close();
		return(contents);
	}
	throw(errno);
}

void split_is(const std::string &s, char delim, std::vector<std::string> &elems) {
    std::stringstream ss(s);
    std::string item;
    while (std::getline(ss, item, delim)) {
        if(item.length() > 0) {
            elems.push_back(item);
		}
    }
}

void split_is(const std::string &s, string delim_regex, std::vector<std::string> &elems) {
    // Terribly slow and inefficient, sorry. Should probably fix this at some point
    boost::algorithm::split_regex(elems, s, regex(delim_regex));
    std::vector<std::string> non_zero_elems;
    for(uint e = 0; e < elems.size(); e++) {
        if (elems[e].length() > 0) {
            non_zero_elems.push_back(elems[e]);
        }
    }
    elems = non_zero_elems;
}

std::string to_string_is(int n) {
    std::string str = boost::lexical_cast<std::string>(n);
    return str;
}

std::string to_string_is(double d) {
    std::string str = boost::lexical_cast<std::string>(d);
    return str;
}

int stoi_is(std::string s) {
    return boost::lexical_cast<int>(s);
}

double stod_is(std::string s) {
    return boost::lexical_cast<double>(s);
}

void convertspintostring(map<tuple<int,int,int,int>,int>& spin, string &spinstring) {
    set<tuple<int,int,int,int> > keylist;
    int imax = getimax<0>(spin);
    int jmax = getimax<1>(spin);
    int zmax = getimax<2>(spin);
    int location_max = getimax<3>(spin);
    int location_min = getimin<3>(spin);
    spinstring = "";
    for (int z = zmax; z > 0; z--) {
        spinstring += "\n";
        for (int j = jmax; j > 0; j--) {
            spinstring = spinstring + "\n";
            for (int i = 1; i < imax + 1; i++) {
                spinstring += "(";
                for (int location = location_min; location < location_max + 1; location++) {
                    if (spin.count(make_tuple(i, j, z, location)) == 1){
                        spinstring = spinstring + " " + lexical_cast<string>(spin[(make_tuple(i, j, z, location))]);
                    }else{
                        spinstring = spinstring + " " + "x";
                    }
                }
                spinstring += ")";
            }
        }
    }
}

void printblock(map<tuple<int,int,int,int>,int> &thisblock) {
    string tempstring3;
    convertspintostring(thisblock, tempstring3);
    cout << tempstring3 << "\n";
}

void printblocklist(vector<map<tuple<int,int,int,int>,int> > &thisblocklist) {
    for(vector<map<tuple<int,int,int,int>,int> >::iterator it=thisblocklist.begin();it!=thisblocklist.end();it++ ){
        cout << "\n-----";
        printblock(*it);
    }
}
