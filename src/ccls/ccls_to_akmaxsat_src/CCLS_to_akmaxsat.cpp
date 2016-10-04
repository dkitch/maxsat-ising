#include <iostream>
#include <string>
#include <sstream>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>

using namespace std;

int main(int argc, char **argv)
{
	printf("c This is the CCLS_to_akmaxsat solver, Version: MAXSAT EVALUATION 2014 (2014.03.28)\n");
	printf("c Many thanks to the akmaxsat team!\n");

	if(argc!=3)
	{
		printf("c Usage: %s <instance> <first_lower_bound_threshold>\n", argv[0]);
		return -1;
	}

	int my_pid = getpid();
	int my_time = time(0);
	string my_pid_str;
	string my_time_str;
	string my_instance;
	string my_result_file;
	string my_command;
	stringstream my_sstream;
	
	my_sstream.clear();
	my_sstream.str("");
	my_sstream<<my_pid;
	my_sstream>>my_pid_str;
	my_sstream.clear();
	my_sstream.str("");
	my_sstream<<my_time;
	my_sstream>>my_time_str;
	
	my_instance = argv[1];
	my_instance = "\"" + my_instance + "\"";
	my_result_file = "ccls_res_" + my_pid_str + "_" + my_time_str;
	my_command = "./CCLS2014 " + my_instance + " 1 10 > ./" + my_result_file;
	
	cout<<"c "<<my_command<<endl;
	printf("c start CCLS\n");
	system(my_command.c_str());
	printf("c stop CCLS\n");
	
	string terminating_gap_str = argv[2];
	my_command = "./akmaxsat " + my_instance + " ./" + my_result_file + " " + terminating_gap_str;
	cout<<"c "<<my_command<<endl;
	printf("c start akmaxsat\n");
	system(my_command.c_str());
	printf("c stop akmaxsat\n");
	
	return 0;
}
