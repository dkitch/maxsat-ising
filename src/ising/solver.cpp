#include "solver.h"

using namespace std;
using namespace ::boost::tuples;
using namespace ::boost;

void run_solver(int max_sites,
                map< set< tuple<int,int,int,int,int> >, double> &J,
                map< set< tuple<int,int,int,int,int> >, double> &lowerboundclustertype,
                map< set< tuple<int,int,int,int,int> >, double> &upperboundclustertype,
                map< tuple<int,int,int,int>, int> &cellrepresentation,
                double &lower_bound,
                double &exact_lower_bound,
                double &upper_bound,
                map< tuple<int,int,int,int>, int> &unitcell,
                tuple<int,int,int,int,int,int> &periodicity,
                map< set< tuple<int,int,int,int,int> >, double> &J_for_proof,
                std::string id,
                double prec,
                int num_loops,
                bool basic_exact_mode,
                bool pseudo_mode,
                bool pseudo_mode_with_proof,
                bool verbose,
                bool very_verbose,
                bool obscenely_verbose) {
    if (!((basic_exact_mode && !pseudo_mode && !pseudo_mode_with_proof) ||
           (!basic_exact_mode && pseudo_mode && pseudo_mode_with_proof) ||
           (!basic_exact_mode && pseudo_mode && !pseudo_mode_with_proof))){
        cout << "Invalid choice of solver mode! Exiting." << endl;
        exit(1);
    }

    // If verbose, print back basic input
    if (verbose){
        cout << "(" << id <<") %%%%%%%%%%%%%%%%%%%% Solver %%%%%%%%%%%%%%%%%%%%%" << endl;
        cout << "(" << id <<") -------------------- Input ----------------------" << endl;
        if(basic_exact_mode){
            cout << "Basic exact mode" << endl;
        }else if (pseudo_mode && !pseudo_mode_with_proof){
            cout << "Pseudo mode (no proof)" << endl;
        }else if (pseudo_mode && pseudo_mode_with_proof){
            cout << "Pseudo mode (with proof)" << endl;
        }
        cout << "Precision: " << prec << endl;
        cout << "(" << id <<") J: " << endl;
        printmapfromsets(J);
        cout << "(" << id <<") Solver: " << endl;
        cout << "(" << id <<") -------------------------------------------------" << endl;
    }

    // Convert J to integers
    map< set< tuple<int,int,int,int,int> >, double> Ji;
    map< set< tuple<int,int,int,int,int> >, double>::iterator Jit;
    for (Jit = J.begin(); Jit != J.end(); ++Jit){
        Ji[Jit->first] = (double)((long long)(Jit->second / prec));
    }

    // Calculate basic block size and dimension (in species)
    map<int,int> components;
    int x_range, y_range, z_range;
    calculate_range_from_J(Ji, x_range, y_range, z_range, components);

    // Solve optimization problem
    if(verbose){
        cout << "(" << id <<") Solving optimization problem ..." << endl;
    }
    corecode(components, x_range, y_range, z_range, max_sites, num_loops,
             Ji,
             lowerboundclustertype, upperboundclustertype, cellrepresentation,
             lower_bound, upper_bound, unitcell, periodicity, J_for_proof,
             id, pseudo_mode, pseudo_mode_with_proof, basic_exact_mode,
             very_verbose, obscenely_verbose);

    // If necessary, prove lower bound convergence
    if (pseudo_mode_with_proof){
        if(verbose){
            cout << "(" << id <<") Proving correctness ..." << endl;
            cout << "(" << id <<") J for proof: " << endl;
            printmapfromsets(J_for_proof);
        }
        calculate_range_from_J(J_for_proof, x_range, y_range, z_range, components);
        map< tuple<int, int, int, int>, int> tempspin;
        map< tuple<int, int, int, int, int, int>,
             map<set<tuple<int, int, int, int, int> >, double> > temp_clustertype_periodic;
        double temp_LB_so_far = lower_bound;
        get_lowerbound_sub(x_range, 0, y_range, 0, 0, z_range,
                           J_for_proof,
                           x_range, y_range, z_range, components,
                           tempspin,
                           exact_lower_bound,
                           temp_clustertype_periodic,
                           temp_LB_so_far, id,
                           false, false, true, obscenely_verbose);
    }

    upper_bound = upper_bound * prec;
    lower_bound = lower_bound * prec;
    exact_lower_bound = exact_lower_bound * prec;

    // Output results
    if (verbose){
        cout << "(" << id <<") ------------------- Results --------------------" << endl;
        if(basic_exact_mode){
            cout << "(" << id <<") UB: " << upper_bound << "; LB: " << lower_bound << endl;
        }else if(!pseudo_mode_with_proof){
            cout << "(" << id <<") UB: " << upper_bound << "; Pseudo-LB: " << lower_bound << endl;
        }else{
            cout << "(" << id <<") UB: " << upper_bound << "; Pseudo-LB: " << lower_bound << "; Exact-LB: " << exact_lower_bound << endl;
        }
        cout << "(" << id <<") Correlations: ";
        printmapfromsets(upperboundclustertype);
        cout << "\n(" << id <<") Unit cell: ";
        printblock(unitcell);
        cout << "\n(" << id <<") Periodicity: " << periodicity << endl;
        cout << "(" << id <<") --------------------- Done --------------------\n" << endl;
    }
}

void corecode(map<int, int> component,
              int x_range, int y_range, int z_range,
              int max_sites,
              int loopnumber,
              map<set<tuple<int,int,int,int,int> >, double> &J,
              map<set<tuple<int,int,int,int,int> >, double> &lowerboundclustertype,
              map<set<tuple<int,int,int,int,int> >, double> &upperboundclustertype,
              map<tuple<int,int,int,int>,int> &cellrepresentation,
              double &lower_bound, double &upper_bound,
              map<tuple<int,int,int,int>,int> &unitcell,
              tuple<int,int,int,int,int,int> &periodicity,
              map<set<tuple<int,int,int,int,int> >, double> &J_for_proof,
              std::string id,
              bool pseudo_mode,
              bool pseudo_mode_with_proof,
              bool basic_exact_mode,
              bool very_verbose,
              bool obscenely_verbose) {
    map<tuple<int,int,int,int,int,int>, map<tuple<int,int,int,int>,int> > spin_periodic, spin_lowerbound;
    map<tuple<int,int,int,int,int,int>, double > energy_periodic,energy_lowerbound;

    int dimension;
    double lowerbound_from_compat = -1e18;
    double min_bound = -1e18, max_bound = 0;
    set<tuple<int,int,int,int,int,int> >  min_list, max_list;

    int a0, a1, a2, a3, a4, a5;
    set<tuple<int,int,int,int,int,int> > setoftupletemp;
    map<tuple<int,int,int,int,int,int>, map<set<tuple<int,int,int,int,int> >, double> > clustertype_periodic;
    map<tuple<int,int,int,int,int,int>, map<set<tuple<int,int,int,int,int> >, double> > clustertype_lowerbound;

    if (!((basic_exact_mode && !pseudo_mode && !pseudo_mode_with_proof) ||
           (!basic_exact_mode && pseudo_mode && pseudo_mode_with_proof) ||
           (!basic_exact_mode && pseudo_mode && !pseudo_mode_with_proof))){
        cout << "Invalid choice of solver mode! Exiting." << endl;
        exit(1);
    }

    // Identify dimensionality of the problem
    if (z_range == 1 && y_range == 1) {
        dimension = 1;
        if (very_verbose) { cout << "1D algorithm activated" << endl; }
    }else if (z_range == 1){
        dimension = 2;
        if (very_verbose) { cout << "2D algorithm activated" << endl; }
    }else{
        dimension = 3;
        if (very_verbose) { cout << "3D algorithm activated" << endl; }
    }

    // Obtain lower bound estimate on the energy
    if (loopnumber > 0){
        if (dimension == 1) {
            a0=loopnumber;
            a1=0;
            a2=1;
            a3=0;
            a4=0;
            a5=1;
        }else if (dimension == 2) {
            a0=loopnumber;
            a1=0;
            a2=loopnumber;
            a3=0;
            a4=0;
            a5=1;
        }else if (dimension == 3) {
            a0=loopnumber;
            a1=0;
            a2=loopnumber;
            a3=0;
            a4=0;
            a5=loopnumber;
        }

		// Attempt to solve lower bound problem
        get_lowerbound(a0, a1, a2, a3, a4, a5, J, x_range, y_range, z_range,
                   component, spin_lowerbound[make_tuple(a0,a1,a2,a3,a4,a5)],
                   energy_lowerbound[make_tuple(a0,a1,a2,a3,a4,a5)],
                   clustertype_lowerbound, J_for_proof, id,
                   pseudo_mode, pseudo_mode_with_proof, basic_exact_mode,
                   obscenely_verbose);

        findminmax(energy_lowerbound, min_bound, max_bound);
        matchnumber(energy_lowerbound, max_bound, max_list);
        lowerbound_from_compat=max_bound;

        if(very_verbose){
            cout << "******************************************************************************" << endl;
            cout << "LB: " << endl;
            printmap(energy_lowerbound);

            cout << "LB solution: " << endl;
            for (set<tuple<int,int,int,int,int,int> >::iterator ait=max_list.begin(); ait!=max_list.end(); ait++){
                tuple<int,int,int,int,int,int> a;
                a=*ait;
                cout << "\n" << a;
                printblock(spin_lowerbound[a]);
            }

            cout << "\nLB maximum is: " << max_bound << endl;
            cout << "LB maximum list: ";
            printvector(max_list);
            cout << "\nAbsolute LB: " << lowerbound_from_compat << endl;
        }
    }

    // Obtain upper bound estimate on the energy
    if (max_sites > 0){
        for (int alpha=1; alpha < max_sites+1; alpha++){
            double dump1;
            findminmax(energy_periodic, min_bound, dump1);
            matchnumber(energy_periodic, min_bound, min_list);

            if (min_bound <= lowerbound_from_compat+1) { break; }

            if (dimension == 1) {
                a0=alpha;
                a1=0;
                a2=1;
                a3=0;
                a4=0;
                a5=1;

                if (pseudo_mode) {
                    periodic(a0,a1,a2, a3,a4,a5,
                             J,
                             x_range,y_range,z_range, component,
                             spin_periodic[make_tuple(a0,a1,a2,a3,a4,a5)],
                             energy_periodic[make_tuple(a0,a1,a2,a3,a4,a5)],
                             clustertype_periodic, min_bound, id,
                             true, false, false,
                             obscenely_verbose);

                }else if (basic_exact_mode){
                    periodic(a0,a1,a2, a3,a4,a5,
                             J,
                             x_range,y_range,z_range, component,
                             spin_periodic[make_tuple(a0,a1,a2,a3,a4,a5)],
                             energy_periodic[make_tuple(a0,a1,a2,a3,a4,a5)],
                             clustertype_periodic, min_bound, id,
                             false, true, false,
                             obscenely_verbose);
                }

                double dump1;
                findminmax(energy_periodic, min_bound, dump1);
                matchnumber(energy_periodic, min_bound, min_list);

                if (very_verbose){
                    cout << "\nUB: " << min_bound << ", LB: " << lowerbound_from_compat << "; Periodicity: ";
                    printvector(min_list);
                    cout << endl;
                }
            }else if (dimension == 2) {
                a3=0;
                a4=0;
                a5=1;
                for (int a2 = 1; a2 < alpha+1; a2++){
                    if (alpha % a2 == 0) {
                        a0 = alpha/a2;
                        for (int a1=0; a1<a0; a1++) {
                            if (pseudo_mode) {
                                periodic(a0, a1, a2, a3, a4, a5,
                                         J, x_range, y_range, z_range, component,
                                         spin_periodic[make_tuple(a0,a1,a2,a3,a4,a5)],
                                         energy_periodic[make_tuple(a0,a1,a2,a3,a4,a5)],
                                         clustertype_periodic, min_bound, id,
                                         true, false, false,
                                         obscenely_verbose);

                            }else if (basic_exact_mode){
                                periodic(a0, a1, a2, a3, a4, a5,
                                         J, x_range, y_range, z_range, component,
                                         spin_periodic[make_tuple(a0,a1,a2,a3,a4,a5)],
                                         energy_periodic[make_tuple(a0,a1,a2,a3,a4,a5)],
                                         clustertype_periodic, min_bound, id,
                                         false, true, false,
                                         obscenely_verbose);
                            }

                            double dump1;
                            findminmax(energy_periodic, min_bound, dump1);
                            matchnumber(energy_periodic, min_bound, min_list);

                            if (very_verbose){
                                cout << "\nUB: " << min_bound << ", LB: " << lowerbound_from_compat << "; Periodicity: ";
                                printvector(min_list);
                                cout << endl;
                            }

                        }
                    }
                }


            }else if (dimension == 3){
                for (int beta = 1; beta < alpha + 1; beta++) {
                    if (alpha % beta == 0) {
                        a0 = alpha/beta;
                        for (int gamma = 1; gamma < beta+1; gamma++){
                            if (beta % gamma == 0) {
                                a2 = beta/gamma;
                                a5 = gamma;
                                for (a4 = 0; a4 < a2; a4++) {
                                    for (a3 = 0; a3 < a0; a3++) {
                                        for (a1 = 0; a1 < a0; a1++) {
                                            if (pseudo_mode) {
                                                periodic(a0, a1, a2, a3, a4, a5,
                                                         J, x_range, y_range, z_range, component,
                                                         spin_periodic[make_tuple(a0,a1,a2,a3,a4,a5)],
                                                         energy_periodic[make_tuple(a0,a1,a2,a3,a4,a5)],
                                                         clustertype_periodic, min_bound, id,
                                                         true, false, false,
                                                         obscenely_verbose);
                                            }
                                            else if (basic_exact_mode){
                                                periodic(a0, a1, a2, a3, a4, a5,
                                                         J, x_range, y_range, z_range, component,
                                                         spin_periodic[make_tuple(a0,a1,a2,a3,a4,a5)],
                                                         energy_periodic[make_tuple(a0,a1,a2,a3,a4,a5)],
                                                         clustertype_periodic, min_bound, id,
                                                         false, true, false,
                                                         obscenely_verbose);
                                            }

                                            double dump1;
                                            findminmax(energy_periodic, min_bound, dump1);
                                            matchnumber(energy_periodic, min_bound, min_list);

                                            if (very_verbose){
                                                cout << "\nUB: " << min_bound << ", LB: " << lowerbound_from_compat << "; Periodicity: ";
                                                printvector(min_list);
                                                cout << endl;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        double dump1;
        findminmax(energy_periodic, min_bound, dump1);
        matchnumber(energy_periodic, min_bound, min_list);

        if (very_verbose){
            cout << "******************************************************************************" << endl;
            cout << "UB: " << endl;
            printmap(energy_lowerbound);

            if (loopnumber > 0){
                cout << "LB solution: " << endl;
                for (set<tuple<int,int,int,int,int,int> >::iterator ait=max_list.begin(); ait!=max_list.end(); ait++){
                    tuple<int,int,int,int,int,int> a;
                    a = *ait;
                    cout << "\n" << a;
                    printblock(spin_lowerbound[a]);
                }
            }

            cout << "UB solution: " << endl;
            for (set<tuple<int,int,int,int,int,int> >::iterator ait=min_list.begin(); ait!=min_list.end(); ait++){
                tuple<int,int,int,int,int,int> a;
                a = *ait;
                cout << "\n" << a;
                printblock(spin_periodic[a]);
            }

            cout << "\nUB minimum is: " << min_bound << endl;
            cout << "\nAbsolute LB: " << lowerbound_from_compat << endl;
            cout << "UB minimum list: ";
            printvector(min_list);
            cout << "LB maximum list: ";
            printvector(max_list);
            cout << endl;
        }
    }

    // Output final results
    lower_bound = lowerbound_from_compat;
    upper_bound = min_bound;

    lowerboundclustertype = clustertype_lowerbound[*(max_list.begin())];
    upperboundclustertype = clustertype_periodic[*(min_list.begin())];

    periodicity = *(min_list.begin());
    unitcell = spin_periodic[periodicity];
}


void calculate_range_from_J(map<set<tuple<int,int,int,int,int> >, double> &J,
                                                int &x_range,int &y_range,int &z_range,
                                                map<int, int>&component) {
    int xmax=0;
    int ymax=0;
    int zmax=0;
    for (map<set<tuple<int,int,int,int,int> >, double>::iterator it=J.begin(); it!=J.end(); it++) {
        set<tuple<int,int,int,int,int> > tuple_set_temp=it->first;
        for (set<tuple<int,int,int,int,int> >::iterator itv=tuple_set_temp.begin(); itv!=tuple_set_temp.end(); itv++) {
            if (xmax<(*itv).get<0>()) {
                xmax=(*itv).get<0>();
            }
            if (ymax<(*itv).get<1>()) {
                ymax=(*itv).get<1>();
            }
            if (zmax<(*itv).get<2>()) {
                zmax=(*itv).get<2>();
            }

            int location=(*itv).get<3>();
            int elementtype=(*itv).get<4>();

            if (component.count(location)==0) {
                component[location]=elementtype+1;
            }
            else if (component[location]<elementtype+1)
            {
                component[location]=elementtype+1;
            }
        }
    }
    x_range=xmax;
    y_range=ymax;
    z_range=zmax;
}
