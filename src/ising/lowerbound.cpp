#include "lowerbound.h"

using namespace std;
using namespace ::boost::tuples;
using namespace ::boost;

void get_lowerbound(int a0, int a1, int a2, int a3, int a4, int a5,
                    map<set<tuple<int,int,int,int,int> >, double> &J,
                    int x_range, int y_range, int z_range,
                    map<int,int> componentnumber,
                    map<tuple<int,int,int,int>,int> &spin,
                    double &lower_bound,
                    map<tuple<int,int,int,int,int,int>, map<set<tuple<int,int,int,int,int> >, double> > &clustertypeperiodic,
                    map<set<tuple<int,int,int,int,int> >, double> &J_for_proof,
                    std::string id,
                    bool pseudo_mode,
                    bool pseudo_mode_with_proof,
                    bool basic_exact_mode,
                    bool obscenely_verbose) {
    if (!((basic_exact_mode && !pseudo_mode && !pseudo_mode_with_proof) ||
           (!basic_exact_mode && pseudo_mode && pseudo_mode_with_proof) ||
           (!basic_exact_mode && pseudo_mode && !pseudo_mode_with_proof))){
        cout << "Invalid choice of solver mode! Exiting." << endl;
        exit(1);
    }

    if (obscenely_verbose){
        cout << "---------------------- Computing lower bound ---------------------" << endl;
    }

    // Define optimization range (based on loopnumber and dimensionality)
    x_range += a0-1;
    y_range += a2-1;
    z_range += a5-1;

    // Set up Gurobi optimizer
    GRBEnv env = GRBEnv();
    GRBEnv env_quadratic = GRBEnv();
    GRBModel m = GRBModel(env);
    GRBModel m_quadratic = GRBModel(env_quadratic);
    if (!obscenely_verbose){
        m.getEnv().set(GRB_IntParam_OutputFlag, 0);
        m_quadratic.getEnv().set(GRB_IntParam_OutputFlag, 0);
    }
    GRBVar mu = m.addVar(-1e18, 1e18, 1, GRB_CONTINUOUS);
    GRBVar mu_quadratic = m_quadratic.addVar(-1e15, 1e15, 1, GRB_CONTINUOUS);
    m.update();
    m_quadratic.update();
    m.set(GRB_IntAttr_ModelSense,-1);
    m_quadratic.set(GRB_IntAttr_ModelSense,-1);

    long long equivalent_sets_count = 0;
    map<long long, set<set<tuple<int,int,int,int,int> > > > index_to_equivalent_sets;
    map<set<set<tuple<int,int,int,int,int> > >,long long> revert_index_to_equivalent_sets;
    map<long long, double> value_of_equivalent_sets;
    double max_value_of_J = 0;

    for (map<set<tuple<int,int,int,int,int> >, double>::iterator it1 = J.begin(); it1 != J.end(); it1++) {
        set<tuple<int,int,int,int,int> > prototype_set=it1->first;
        double value = it1->second;

        // Set some limits on x, y, z range
        int x_max = -1e5;
        int x_min = 1e5;
        int y_max = -1e5;
        int y_min = 1e5;
        int z_max = -1e5;
        int z_min = 1e5;
        for (set<tuple<int,int,int,int,int> >::iterator it2=prototype_set.begin(); it2!=prototype_set.end(); it2++) {
            tuple<int,int,int,int,int> tuple_element=*it2;
            int x_position=tuple_element.get<0>();
            int y_position=tuple_element.get<1>();
            int z_position=tuple_element.get<2>();
            if (x_min > x_position) { x_min = x_position; }
            if (x_max < x_position) { x_max = x_position; }
            if (y_min > y_position) { y_min = y_position; }
            if (y_max < y_position) { y_max = y_position; }
            if (z_min > z_position) { z_min = z_position; }
            if (z_max < z_position) { z_max = z_position; }
        }

        // Find equivalent sets of ECIs
        set<set<tuple<int,int,int,int,int> > > set_of_equivalent;
        for (int translation_z = 1-z_min; translation_z <= z_range-z_max; translation_z++) {
            for (int translation_y = 1-y_min; translation_y <= y_range-y_max; translation_y++) {
                for (int translation_x = 1-x_min; translation_x <= x_range-x_max; translation_x++) {
                    set<tuple<int,int,int,int,int> > temp_equivalent_set;

                    for (set<tuple<int,int,int,int,int> >::iterator it2=prototype_set.begin(); it2!=prototype_set.end(); it2++) {
                        tuple<int,int,int,int,int> tuple_element=*it2;
                        tuple<int,int,int,int,int> new_tuple=make_tuple(tuple_element.get<0>() +
                                                                        translation_x,tuple_element.get<1>() +
                                                                        translation_y,tuple_element.get<2>() +
                                                                        translation_z,tuple_element.get<3>(),
                                                                        tuple_element.get<4>());
                        temp_equivalent_set.insert(new_tuple);
                    }
                    set_of_equivalent.insert(temp_equivalent_set);
                }
            }
        }

        if (revert_index_to_equivalent_sets.count(set_of_equivalent) == 0) {
            index_to_equivalent_sets[equivalent_sets_count] = set_of_equivalent;
            revert_index_to_equivalent_sets[set_of_equivalent] = equivalent_sets_count;
            value_of_equivalent_sets[equivalent_sets_count] = value;
            equivalent_sets_count++;
        } else {
            long long number = revert_index_to_equivalent_sets[set_of_equivalent];
            value_of_equivalent_sets[number] += value;
        }
    }

    for (map<long long, double>::iterator it1 = value_of_equivalent_sets.begin(); it1 != value_of_equivalent_sets.end(); it1++) {
        if (max_value_of_J < abs(it1->second)) { max_value_of_J = abs(it1->second); }
    }

    map<tuple<long long,long long>, set<tuple<int,int,int,int,int> > > index_to_subcluster;
    map<set<tuple<int,int,int,int,int> >, tuple<long long,long long> > revert_index_to_subcluster;
    map<tuple<long long,long long>, double> subcluster_value;
    map<tuple<long long,long long>, GRBVar> subcluster_variable,subcluster_variable_quadratic;
    map<long long,long long> prenum_to_subnum; //Last one does not count

    for (map<long long, set<set<tuple<int,int,int,int,int> > > >::iterator it1 = index_to_equivalent_sets.begin(); it1 != index_to_equivalent_sets.end(); it1++) {
        long long sub_number = 0;
        long long pre_number = it1->first;
        set<set<tuple<int,int,int,int,int> > > equivalent_set_here = it1->second;
        for (set<set<tuple<int,int,int,int,int> > >::iterator it2=equivalent_set_here.begin(); it2 != equivalent_set_here.end(); it2++) {
            set<tuple<int,int,int,int,int> > subset_here = *it2;
            index_to_subcluster[make_tuple(pre_number,sub_number)] = subset_here;
            revert_index_to_subcluster[subset_here]=make_tuple(pre_number, sub_number);
            subcluster_variable[make_tuple(pre_number,sub_number)] = m.addVar(-max_value_of_J, max_value_of_J, 0, GRB_CONTINUOUS);
            subcluster_variable_quadratic[make_tuple(pre_number,sub_number)] = m_quadratic.addVar(-max_value_of_J, max_value_of_J,0, GRB_CONTINUOUS);
            sub_number++;
        }
        prenum_to_subnum[pre_number]=sub_number;
    }

    m.update();
    m_quadratic.update();
    for (long long prenumber = 0; prenumber < equivalent_sets_count; prenumber++) {
        GRBLinExpr sum = 0;
        GRBLinExpr sum_quadratic = 0;
        for (long long subnumber = 0; subnumber < prenum_to_subnum[prenumber]; subnumber++) {
            sum += subcluster_variable[make_tuple(prenumber,subnumber)];
            sum_quadratic += subcluster_variable_quadratic[make_tuple(prenumber,subnumber)];
        }
        m.addConstr(sum == value_of_equivalent_sets[prenumber]);
        m_quadratic.addConstr(sum_quadratic == value_of_equivalent_sets[prenumber]);
    }

    map<set<tuple<int,int,int,int,int> >, double> J_input;
    double proximal_factor=1e-8;
    GRBQuadExpr quadratic_objective = mu_quadratic;
    for (long long  prenumber = 0; prenumber < equivalent_sets_count; prenumber++) {
        for (long long subnumber = 0; subnumber < prenum_to_subnum[prenumber]; subnumber++) {
            double prefactor = proximal_factor;
            quadratic_objective += (-1)*prefactor*subcluster_variable_quadratic[make_tuple(prenumber,subnumber)]*
                                                  subcluster_variable_quadratic[make_tuple(prenumber,subnumber)];

        }
    }

    m_quadratic.setObjective(quadratic_objective);
    double lowerbound_memory=-1e20;
    map<set<tuple<int,int,int,int,int> >, double> J_input_best_memory;

    GRBConstr lambda_constraint;
    for (long long infinite_loop = 0; infinite_loop < 500000; infinite_loop++) {
        m_quadratic.optimize();
        J_input.clear();
        for (map<tuple<long long,long long>, GRBVar>::iterator it1 = subcluster_variable_quadratic.begin(); it1 != subcluster_variable_quadratic.end(); it1++) {

            tuple<long long,long long> tuple_here = it1->first;
            GRBVar variable_here=it1->second;
            try {
                J_input[index_to_subcluster[tuple_here]] = variable_here.get(GRB_DoubleAttr_X);
            } catch (GRBException a) {
                lower_bound = lowerbound_memory;
                J_for_proof = J_input_best_memory;
                if (obscenely_verbose){
                    cout << "LB - Loop #" << infinite_loop <<": Either a numerical error occurred or found tightest LB: " << lower_bound << endl;
                    cout << "J_for_proof: ";
                    printmapfromsets(J_for_proof);
                    cout << "\n" << endl;
                }
                return;
            }
        }

        if (pseudo_mode) {
            get_lowerbound_sub(1, 0, 1, 0, 0, 1,
                               J_input,
                               x_range, y_range, z_range, componentnumber,
                               spin, lower_bound,
                               clustertypeperiodic, lowerbound_memory, id,
                               true, false, false,
                               obscenely_verbose);
        }else if (basic_exact_mode) {
            get_lowerbound_sub(1, 0, 1, 0, 0, 1,
                               J_input,
                               x_range, y_range, z_range, componentnumber,
                               spin, lower_bound,
                               clustertypeperiodic, lowerbound_memory, id,
                               false, true, false,
                               obscenely_verbose);
        }

        map<set<tuple<int,int,int,int,int> >, double> cluster_type_now = clustertypeperiodic[make_tuple(1,0,1,0,0,1)];

        if (lowerbound_memory <= lower_bound) {
            lowerbound_memory = lower_bound;
            J_input_best_memory = J_input;
            J_for_proof = J_input_best_memory;
        }

        GRBLinExpr subcluster_sum = 0;
        for (map<set<tuple<int,int,int,int,int> >, double>::iterator it1 = cluster_type_now.begin(); it1 != cluster_type_now.end(); it1++) {
            subcluster_sum += subcluster_variable[revert_index_to_subcluster[it1->first]]*it1->second;
        }
        m.addConstr(mu <= subcluster_sum);


        GRBLinExpr sum1_quadratic = 0;
        for (map<set<tuple<int,int,int,int,int> >, double>::iterator it1 = cluster_type_now.begin(); it1 != cluster_type_now.end(); it1++) {
            sum1_quadratic += subcluster_variable_quadratic[revert_index_to_subcluster[it1->first]]*it1->second;
        }
        m_quadratic.addConstr(mu_quadratic <= sum1_quadratic);

        m.optimize();
        double upperbound_of_lowerbound = m.get(GRB_DoubleAttr_ObjVal);

        if (infinite_loop >= 1) {
            m_quadratic.remove(lambda_constraint);
        }
        lambda_constraint = m_quadratic.addConstr(mu_quadratic >= 0.5*lowerbound_memory + 0.5*upperbound_of_lowerbound);

        quadratic_objective = 0;
        for (long long  prenumber = 0; prenumber<equivalent_sets_count; prenumber++) {
            for (long long subnumber = 0; subnumber<prenum_to_subnum[prenumber]; subnumber++) {

                quadratic_objective -= (subcluster_variable_quadratic[make_tuple(prenumber,subnumber)] -
                                         J_input_best_memory[index_to_subcluster[make_tuple(prenumber,subnumber)]]) *
                                       (subcluster_variable_quadratic[make_tuple(prenumber,subnumber)] -
                                         J_input_best_memory[index_to_subcluster[make_tuple(prenumber,subnumber)]]);

                subcluster_variable_quadratic[make_tuple(prenumber,subnumber)].set(GRB_DoubleAttr_Start,
                                                                                   J_input_best_memory[index_to_subcluster[make_tuple(prenumber,subnumber)]]);
            }
        }
        m_quadratic.setObjective(quadratic_objective);

        if (obscenely_verbose){
            cout << "\nLB - Loop #" << infinite_loop << endl;
            cout << "\tBound of LB: " << upperbound_of_lowerbound << endl;
            cout << "\tCurrent LB: " << lower_bound << endl;
            cout << "\tBest LB: " << lowerbound_memory<< endl;
            cout << "\tProximity factor:" << proximal_factor << endl;
            cout << "\n" << endl;
        }

        if (lower_bound + 0.1 > upperbound_of_lowerbound) {
            J_for_proof = J_input_best_memory;
            lower_bound = lowerbound_memory;
            if (obscenely_verbose){
                cout << "LB - Loop #" << infinite_loop << ": Found tightest lower bound: " << lower_bound << endl;
                cout << "J_for_proof:";
                printmapfromsets(J_for_proof);
                cout << "\n" << endl;
            }
            break;
        }
    }
}

void get_lowerbound_sub(int a0, int a1, int a2, int a3, int a4, int a5,
                    map<set<tuple<int,int,int,int,int> >, double> &J,
                    int x_range, int y_range, int z_range, map<int,int> componentnumber,
                    map<tuple<int,int,int,int>,int> &spin,
                    double &lower_bound,
                    map<tuple<int,int,int,int,int,int>, map<set<tuple<int,int,int,int,int> >, double> > &clustertypeperiodic,
                    double LB_so_far,
                    std::string id,
                    bool stop_at_first_iteration,
                    bool stop_when_upperbound_smaller_than_predicted_lower_bound,
                    bool stop_till_exact_result,
                    bool obscenely_verbose) {
    if (obscenely_verbose) {
        cout << "\nCalculating LB with a0 = " << a0;
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
        J_integral[it->first] = round(it->second);
    }

    for (int i = 1; i < a0 + x_range; i++) {
        for(int j = 1; j < a2 + y_range; j++) {
            for (int k = 1; k < a5 + z_range; k++) {
                for (map<int, int>::iterator cit = componentnumber.begin(); cit != componentnumber.end(); cit++) {
                    int position = cit->first;
                    int element_count = cit->second;
                    for (int z = 0; z < element_count; z++) {
                        if (z > 0.1) {
                            softer_variable_encode[make_tuple(i,j,k,position,z)] = softer_count_variable;
                            softer_variable_decode[softer_count_variable] = make_tuple(i,j,k,position,z);
                            softer_count_variable++;
                        }
                    }
                }
            }
        }
    }

    for (int i = 1; i < a0 + x_range; i++) {
        for (int j = 1; j < y_range; j++) {
            for (int k = 1; k < a5 + z_range; k++) {
                for (map<int, int>::iterator cit = componentnumber.begin(); cit != componentnumber.end(); cit++) {
                    int position = cit->first;
                    int element_count = cit->second;
                    for (int mu = 0; mu < element_count; mu++) {
                        if (mu > 0.1) {
                            set<long long> set_temp_1;
                            set_temp_1.insert(-softer_variable_encode[make_tuple(i, j, k, position, mu)]);
                            set_temp_1.insert(softer_variable_encode[make_tuple((i + a1 - 1) % a0 + 1,
                                                                                  a2 + j, k, position, mu)]);
                            set_temp_1.clear();
                            set_temp_1.insert(softer_variable_encode[make_tuple(i, j, k, position, mu)]);
                            set_temp_1.insert(-softer_variable_encode[make_tuple((i + a1 - 1) % a0 + 1,
                                                                                  a2 + j, k, position, mu)]);
                        }
                    }
                }
            }
        }
    }

    for (int j = 1; j < a2 + y_range; j++) {
        for (int i = 1; i < x_range; i++) {
            for (int k = 1; k < a5 + z_range; k++) {
                for (map<int, int>::iterator cit = componentnumber.begin(); cit != componentnumber.end(); cit++) {
                    int position = cit->first;
                    int element_count = cit->second;
                    for (int mu = 0; mu < element_count; mu++) {
                        if (mu > 0.1) {
                            set<long long> set_temp_1;
                            set_temp_1.insert(-softer_variable_encode[make_tuple(i, j, k, position, mu)]);
                            set_temp_1.insert(softer_variable_encode[make_tuple(i + a0, j, k, position, mu)]);

                            set_temp_1.clear();
                            set_temp_1.insert(softer_variable_encode[make_tuple(i, j, k, position, mu)]);
                            set_temp_1.insert(-softer_variable_encode[make_tuple(i + a0, j, k, position, mu)]);
                        }
                    }
                }
            }
        }
    }

    for (int i = 1; i < a0 + x_range; i++){
        for (int j = 1; j < a2 + y_range; j++){
            for (int k = 1; k < z_range; k++) {
                for (map<int, int>::iterator cit = componentnumber.begin(); cit != componentnumber.end(); cit++) {
                    int position = cit->first;
                    int element_count = cit->second;
                    for (int mu = 0; mu < element_count; mu++) {
                        if (mu > 0.1) {
                            set<long long> set_temp_1;
                            set_temp_1.insert(-softer_variable_encode[make_tuple(i, j, k, position, mu)]);
                            set_temp_1.insert(softer_variable_encode[make_tuple((i + a3 - 1) % a0 + 1,
                                                                                (j - 1 + a4) % a2 + 1,
                                                                                k + a5, position, mu)]);
                            set_temp_1.clear();
                            set_temp_1.insert(softer_variable_encode[make_tuple(i, j, k, position, mu)]);
                            set_temp_1.insert(-softer_variable_encode[make_tuple((i + a3 - 1) % a0 + 1,
                                                                                 (j - 1 + a4) % a2 + 1,
                                                                                 k + a5, position, mu)]);
                        }
                    }
                }
            }
        }
    }

    for (int i = 1; i < a0 + x_range; i++) {
        for (int j = 1; j < a2 + y_range; j++) {
            for (int k = 1; k < a5 + z_range; k++) {
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

    for (int i = 1; i < a0 + 1; i++) {
        for (int j = 1; j < a2 + 1; j++) {
            for (int k = 1; k < a5 + 1; k++) {
                for(set< set<tuple<int,int,int,int,int> > >::iterator itv = nonzerolist.begin();
                                                                itv != nonzerolist.end(); ++itv){
                    tuple<int,int,int,int,int> first, second;
                    set<tuple<int,int,int,int,int> > tuple_set = *itv;
                    if (J_integral[tuple_set] > 0.1) {
                        set<long long> set_of_terms;
                        set<long long> softer_set_of_terms;
                        for(set< tuple<int,int,int,int,int> >::iterator itv1 = tuple_set.begin();
                                                                    itv1 != tuple_set.end(); itv1++){
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
                                                                    itv1 != tuple_set.end(); itv1++){
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
                            softer_maxsat_model[softer_set_of_terms]-=J_integral[tuple_set];
                        }
                        overall_constant -= J_integral[tuple_set];
                    }
                }
            }
        }
    }

    // Construct input file for MAXSAT optimizer
    ofstream softer_input;
    string softer_filename=id + "_" + to_string_is(a0) + "." + to_string_is(a2) + "." + to_string_is(a5);
    softer_filename += "_softer_lowerbound.wcnf";
    softer_input.open(softer_filename.c_str());
    softer_input << "p wcnf " << softer_variable_encode.size() << " "
                  << softer_maxsat_model.size() + softer_maxsat_model_hard.size() << " " << softer_max_element;

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

    long long criteria = overall_constant + round(LB_so_far * a0 * a2 * a5) - 100;
    if (stop_when_upperbound_smaller_than_predicted_lower_bound) {
        criteria = overall_constant + round(LB_so_far * a0 * a2 * a5) - 100;
    }
    if (criteria < 0) { criteria = 0; }
    if (stop_at_first_iteration) { criteria = 1e18; }
    if (stop_till_exact_result) { criteria = 0; }

    string criteria_string = lexical_cast<string>(criteria);
    string result_now = exec("./CCLS_to_akmaxsat_LB " + softer_filename + " " + criteria_string);
    std::remove(softer_filename.c_str());

    vector<string> result_pieces;
    split_is(result_now, '\n', result_pieces);
    string s_line;
    vector<string> v_line;

    //long long o_value;
    for (vector<string>::iterator it=result_pieces.begin(); it != result_pieces.end(); it++) {
        string temp_string = *it;
        vector<string> temp_segment;
        split_is(temp_string, ' ', temp_segment);
        string first_segment = *temp_segment.begin();
        if (first_segment == "s") {
            s_line = temp_string;
        }
        //if (first_segment=="o") {
            //vector<string>::iterator it1=temp_segment.begin();
            //o_value=boost::lexical_cast<long long>(*(++it1));
        //}
        if (first_segment == "v") {
            v_line.push_back(temp_string);
            for (vector<string>::iterator it1 = temp_segment.begin(); it1 != temp_segment.end(); it1++) {
                if (it1!=temp_segment.begin()) {
                    long long number_now = boost::lexical_cast<long long>(*it1);
                    if (number_now < -0.1) {
                        soft_result[-number_now] = 0;
                    }
                    else if (number_now > 0.1){
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

    for (int i = 1; i < a0 + x_range; i++){
        for (int j = 1; j < a2 + y_range; j++) {
            for (int k = 1; k < a5 + z_range; k++) {
                for (map<int, int>::iterator cit = componentnumber.begin();
                                                            cit != componentnumber.end(); cit++) {
                    int position = cit->first;
                    int element_count = cit->second;
                    for (int mu = 0; mu < element_count; mu++) {
                        if (s_result[make_tuple(i, j, k, position, mu)] == 1) {
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
        cout << "\nBlock result is: ";
        printblock(spin);
        cout << endl;
    }

    for (set< set<tuple<int,int,int,int,int> > >::iterator it = nonzerolist.begin();
                                                            it != nonzerolist.end(); it++) {
        set<tuple<int,int,int,int,int> > thisset = *it;
        clustertypeperiodic[make_tuple(a0,a1,a2,a3,a4,a5)][*it] = 0;
        for (int i = 1; i < a0 + 1; i++) {
            for (int j = 1; j < a2 + 1; j++) {
                for (int k = 1; k < a5 + 1; k++) {
                    int all_matched_indicator = 0;
                    for (set<tuple<int,int,int,int,int> >::iterator it1 = thisset.begin();
                                                                    it1 != thisset.end(); it1++) {
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
                        clustertypeperiodic[make_tuple(a0, a1, a2, a3, a4, a5)][*it] += 1.0/(a0 * a2 * a5);
                    }
                }
            }
        }
    }

    map<set<tuple<int,int,int,int,int> >, double> cluster_type_here =
                                            clustertypeperiodic[make_tuple(a0, a1, a2, a3, a4, a5)];
    lower_bound = 0;
    for (map<set<tuple<int,int,int,int,int> >, double>::iterator it = cluster_type_here.begin();
                                                                it != cluster_type_here.end(); it++) {
        lower_bound += J[it->first]*it->second;
    }

    if (obscenely_verbose){
        cout << "\n(" << id <<") LB average energy: " << lower_bound << endl;;
    }
}
