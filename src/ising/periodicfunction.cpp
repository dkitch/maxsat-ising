#include "periodicfunction.h"

using namespace std;
using namespace ::boost::tuples;
using namespace ::boost;

void periodic(int a0, int a1, int a2, int a3, int a4, int a5,
              map<set<tuple<int,int,int,int,int> >, double> &J,
              int x_range, int y_range, int z_range,
              map<int,int> componentnumber,
              map<tuple<int,int,int,int>,int> &spin,
              double &averageenergy,
              map< tuple<int,int,int,int,int,int>, map<set<tuple<int,int,int,int,int> >, double> > &clustertypeperiodic,
              double min_so_far,
              std::string id,
              bool stop_at_first_iteration,
              bool stop_when_upperbound_smaller_than_predicted_lower_bound,
              bool stop_till_exact_result,
              bool obscenely_verbose) {
    if (obscenely_verbose) {
        cout << "Calculating periodic UB with a0 = " << a0;
        cout << ", a1 = " << a1;
        cout << ", a2 = " << a2;
        cout << ", a3 = " << a3;
        cout << ", a4 = " << a4;
        cout << ", a5 = " << a5 << endl;
    }

    set< set<tuple<int,int,int,int,int> > > nonzerolist;
    map<set<tuple<int,int,int,int,int> >, long long> J_integral;

    long long softer_count_variable = 1;
    map<tuple<int,int,int,int,int>, long long> softer_variable_encode;
    map<long long,tuple<int,int,int,int,int> > softer_variable_decode;
    map<set<long long>, long long> softer_maxsat_model;
    set<set<long long> > softer_maxsat_model_hard;
    long long softer_max_element = 1e18;
    map<long long, int> soft_result;
    long long overall_constant = 0;

    for(map<set<tuple<int,int,int,int,int> >, double>::iterator it = J.begin(); it != J.end(); it++){
        nonzerolist.insert(it->first);
        J_integral[it->first]=round(it->second);
    }

    for (int i = 1; i < a0 + 1; i++) {
        for (int j = 1; j < a2 + 1; j++) {
            for (int k = 1; k < a5 + 1; k++) {
                for (map<int, int>::iterator cit = componentnumber.begin(); cit!=componentnumber.end(); cit++) {
                    int position = cit->first;
                    int element_count = cit->second;
                    for (int z = 0; z < element_count; z++) {
                        if (z > 0.1) {
                            softer_variable_encode[make_tuple(i, j, k, position, z)] = softer_count_variable;
                            softer_variable_decode[softer_count_variable] = make_tuple(i, j, k, position, z);
                            softer_count_variable++;
                        }
                    }
                }
            }
        }
    }

    for (int i = 1; i < a0 + x_range; i++) {
        for (int j = 1; j < a2 + y_range; j++) {
            for (int k = 1; k < a5 + z_range; k++) {
                for (map<int, int>::iterator cit=componentnumber.begin(); cit!=componentnumber.end(); cit++) {
                    int position = cit->first;
                    int element_count = cit->second;
                    for (int mu = 0; mu < element_count; mu++) {
                        if (mu > 0.1) {
                            int i0 = positive_modulo(((i-1)-floor_int_division(j-1-(k-1)/a5*a4,a2)*a1-(k-1)/a5*a3), a0) + 1;
                            int j0 = positive_modulo(((j-1)-(k-1)/a5*a4), a2) + 1;
                            int k0 = (k-1) % a5 + 1;
                            softer_variable_encode[make_tuple(i, j, k, position, mu)] =
                                softer_variable_encode[make_tuple(i0, j0, k0, position, mu)];
                        }
                    }
                }
            }
        }
    }

    for (int i = 1; i < a0 + 1; i++) {
        for (int j = 1; j < a2 + 1; j++) {
            for (int k = 1; k < a5 + 1; k++) {
                for (map<int, int>::iterator cit = componentnumber.begin(); cit != componentnumber.end(); cit++) {
                    int position = cit->first;
                    int element_count = cit->second;
                    for (int temp5 = 0; temp5 < element_count - 1; temp5++) {
                        for (int temp6 = temp5 + 1; temp6 < element_count; temp6++) {
                            set<long long> set_temp;
                            if (temp5 > 0.1) {
                                set<long long> softer_set_temp;
                                softer_set_temp.insert(-softer_variable_encode[make_tuple(i, j, k, position, temp5)]);
                                softer_set_temp.insert(-softer_variable_encode[make_tuple(i, j, k, position, temp6)]);
                                softer_maxsat_model_hard.insert(softer_set_temp);
                            }
                        }
                    }
                }
            }
        }
    }

    for (int i = 1; i < a0 + 1;i++) {
        for (int j = 1; j < a2 + 1; j++) {
            for (int k = 1; k < a5 + 1; k++) {
                for(set< set<tuple<int,int,int,int,int> > >::iterator itv = nonzerolist.begin();
                                                                    itv != nonzerolist.end(); ++itv) {
                    tuple<int,int,int,int,int> first, second;
                    set<tuple<int,int,int,int,int> >::iterator itera1 = (*itv).begin();
                    set<tuple<int,int,int,int,int> > tuple_set = *itv;
                    if (J_integral[tuple_set] > 0.1 ) {
                        set<long long> set_of_terms;
                        set<long long> softer_set_of_terms;
                        for(set<tuple<int,int,int,int,int> >::iterator itv1 = tuple_set.begin();
                                                                        itv1 != tuple_set.end(); itv1++) {
                            tuple<int,int,int,int,int> tuple_here = *itv1;
                            int x0 = tuple_here.get<0>();
                            int y0 = tuple_here.get<1>();
                            int z0 = tuple_here.get<2>();
                            int position = tuple_here.get<3>();
                            int mu = tuple_here.get<4>();
                            softer_set_of_terms.insert(-softer_variable_encode[make_tuple(x0 + i - 1,
                                                                                          y0 + j - 1,
                                                                                          z0 + k - 1,
                                                                                          position, mu)]);
                        }
                        softer_maxsat_model[softer_set_of_terms] += J_integral[tuple_set];
                    }

                    if (J_integral[tuple_set] < -0.1) {
                        for(set<tuple<int,int,int,int,int> >::iterator itv1 = tuple_set.begin();
                                                                    itv1 != tuple_set.end(); itv1++) {
                            set<long long> set_of_terms;
                            set<long long> softer_set_of_terms;
                            tuple<int,int,int,int,int> tuple_here = *itv1;
                            int x0 = tuple_here.get<0>();
                            int y0 = tuple_here.get<1>();
                            int z0 = tuple_here.get<2>();
                            int position = tuple_here.get<3>();
                            int mu = tuple_here.get<4>();
                            softer_set_of_terms.insert(softer_variable_encode[make_tuple(x0 + i - 1,
                                                                                         y0 + j - 1,
                                                                                         z0 + k - 1,
                                                                                         position, mu)]);
                            itv1++;
                            for (set<tuple<int,int,int,int,int> >::iterator itv2 = itv1;
                                                                                itv2 != tuple_set.end(); itv2++) {
                                tuple<int,int,int,int,int> tuple_here = *itv2;
                                int x0 = tuple_here.get<0>();
                                int y0 = tuple_here.get<1>();
                                int z0 = tuple_here.get<2>();
                                int position = tuple_here.get<3>();
                                int mu = tuple_here.get<4>();
                                softer_set_of_terms.insert(-softer_variable_encode[make_tuple(x0 + i - 1,
                                                                                              y0 + j - 1,
                                                                                              z0 + k - 1,
                                                                                              position, mu)]);
                            }
                            itv1--;
                            softer_maxsat_model[softer_set_of_terms] -= J_integral[tuple_set];
                        }
                        overall_constant -= J_integral[tuple_set];
                    }
                }
            }
        }
    }

    ofstream softer_input;
    string softer_filename = id + "_" + to_string_is(a0) + "." + to_string_is(a2) + "." + to_string_is(a5);
    softer_filename += "_softer_periodic.wcnf";
    softer_input.open(softer_filename.c_str());
    softer_input << "p wcnf " << softer_variable_decode.size() <<
                    " " << softer_maxsat_model.size() + softer_maxsat_model_hard.size() <<
                    " " << softer_max_element;

    for (map<set<long long>, long long>::iterator it1 = softer_maxsat_model.begin();
                                                    it1 != softer_maxsat_model.end(); it1++) {
        set<long long> the_set = it1->first;
        softer_input << "\n" << (it1->second);
        for (set<long long>::iterator it2 = the_set.begin(); it2 != the_set.end(); it2++) {
            softer_input << " " << (*it2);
        }
        softer_input << " 0";
    }
    for (set<set<long long> >::iterator it1 = softer_maxsat_model_hard.begin();
                                            it1 != softer_maxsat_model_hard.end(); it1++) {
        set<long long> the_set = *it1;
        softer_input << "\n" << softer_max_element;
        for (set<long long>::iterator it2 = the_set.begin(); it2 != the_set.end(); it2++) {
            softer_input << " " << *it2;
        }
        softer_input << " 0";
    }
    softer_input.close();

    long long criteria = overall_constant + round(min_so_far*a0*a2*a5) + 100;
    if (stop_at_first_iteration) {
        criteria = 0;
    }else if (stop_when_upperbound_smaller_than_predicted_lower_bound) {
        criteria = overall_constant + round(min_so_far*a0*a2*a5) + 100;
    }else if (stop_till_exact_result) {
        criteria = 1e18;
    }

    string criteria_string = lexical_cast<string>(criteria);
    string result_now = exec("./CCLS_to_akmaxsat " + softer_filename + " " + criteria_string);
    std::remove(softer_filename.c_str());

    vector<string> result_pieces;
    split_is(result_now, '\n', result_pieces);
    string s_line;
    vector<string> v_line;

    for (vector<string>::iterator it = result_pieces.begin(); it != result_pieces.end(); it++) {
        string temp_string = *it;
        vector<string> temp_segment;
        split_is(temp_string, ' ', temp_segment);
        string first_segment = *temp_segment.begin();
        if (first_segment == "s") {
            s_line = temp_string;
        }
        if (first_segment == "v") {
            v_line.push_back(temp_string);
            for (vector<string>::iterator it1 = temp_segment.begin(); it1 != temp_segment.end(); it1++) {
                if (it1 != temp_segment.begin()) {
                    long long number_now = boost::lexical_cast<long long>(*it1);
                    if (number_now < -0.1) {
                        soft_result[-number_now] = 0;
                    }else if (number_now > 0.1) {
                        soft_result[number_now] = 1;
                    }
                }
            }
        }
    }

    map<tuple<int, int,int,int,int>, int> s_result;
    for (map<long long, int>::iterator it = soft_result.begin(); it != soft_result.end(); it++) {
        s_result[softer_variable_decode[it->first]] = it->second;
    }

    for (int i = 1; i < a0 + x_range; i++) {
        for (int j = 1; j < a2 + y_range; j++) {
            for (int k = 1; k < a5 + z_range; k++) {
                for (map<int, int>::iterator cit = componentnumber.begin();
                                                            cit != componentnumber.end(); cit++) {
                    int position = cit->first;
                    int element_count = cit->second;
                    for (int mu = 0; mu < element_count; mu++) {
                        int i0 = positive_modulo(((i-1)-floor_int_division(j-1-(k-1)/a5*a4,a2)*a1-(k-1)/a5*a3), a0) + 1;
                        int j0 = positive_modulo(((j-1)-(k-1)/a5*a4), a2) + 1;
                        int k0 = (k-1) % a5 + 1;
                        if (s_result[make_tuple(i0, j0, k0, position, mu)] == 1){
                            spin[make_tuple(i, j, k, position)] = mu;
                            break;
                        }
                        spin[make_tuple(i, j, k, position)] = 0;
                    }
                }
            }
        }
    }

    if (obscenely_verbose){
        cout << "\nUB block is: ";
        printblock(spin);
        cout << endl;
    }

    for (set< set<tuple<int,int,int,int,int> > >::iterator it = nonzerolist.begin();
                                                                it != nonzerolist.end(); it++){
        set<tuple<int,int,int,int,int> > thisset = *it;
        clustertypeperiodic[make_tuple(a0, a1, a2, a3, a4, a5)][*it] = 0;
        for (int i = 1; i < a0 + 1; i++) {
            for (int j = 1; j < a2 + 1;j++) {
                for (int k = 1; k < a5 + 1; k++) {
                    int all_matched_indicator = 0;
                    for (set<tuple<int,int,int,int,int> >::iterator it1 = thisset.begin();
                                                                        it1 != thisset.end(); it1++){
                        tuple<int,int,int,int,int> temp_tuple = *it1;
                        int x = temp_tuple.get<0>();
                        int y = temp_tuple.get<1>();
                        int z = temp_tuple.get<2>();
                        int position = temp_tuple.get<3>();
                        int var = temp_tuple.get<4>();
                        if (spin[make_tuple(i + x - 1, j + y - 1, k + z - 1, position)] != var) {
                            break;
                        }
                        it1++;
                        if (it1 == thisset.end()) {
                            all_matched_indicator = 1;
                            break;
                        }
                        it1--;
                    }

                    if (all_matched_indicator == 1) {
                        clustertypeperiodic[make_tuple(a0, a1, a2, a3, a4, a5)][*it] += 1.0/(a0*a2*a5);
                    }
                }
            }
        }
    }

    if (obscenely_verbose) {
        cout << "UB configuration: ";
        printmapfromsets(clustertypeperiodic[make_tuple(a0,a1,a2,a3,a4,a5)]);
        cout << endl;
    }

    map<set<tuple<int,int,int,int,int> >, double> cluster_type_here = clustertypeperiodic[make_tuple(a0,a1,a2,a3,a4,a5)];
    averageenergy=0;
    for (map<set<tuple<int,int,int,int,int> >, double>::iterator it = cluster_type_here.begin();
                                                                it != cluster_type_here.end(); it++) {
        averageenergy += J[it->first]*it->second;
    }

    if (soft_result.empty()) {
        averageenergy = 1e10;
    }

    if (obscenely_verbose) {
        cout << "\nPeriodic UB average energy: " << averageenergy;
        cout << endl;
    }
}





