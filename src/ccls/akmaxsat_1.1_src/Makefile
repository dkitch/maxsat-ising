#FLAG = -O3 -static -Wall -ansi -fomit-frame-pointer -funroll-loops -DNDEBUG #-DFORCE_LS #-DRBFS #-DFORCE_LS # -DFUIP
FLAG = -O3 -Wall -ansi -fomit-frame-pointer -funroll-loops -DNDEBUG #-DFORCE_LS #-DRBFS #-DFORCE_LS # -DFUIP


akmaxsat: akmaxsat.cpp restore_list.o cnf_formula.hpp clauses.o
	g++ $(FLAG) akmaxsat.cpp -o akmaxsat restore_list.o clauses.o

clauses.o: clauses.cpp clauses.hpp
	g++ $(FLAG) clauses.cpp -c -o clauses.o

restore_list.o: restore_list.cpp restore_list.hpp
	g++ $(FLAG) restore_list.cpp -c -o restore_list.o

clean:
	rm *.o
	rm akmaxsat
