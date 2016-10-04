WORKDIR = `pwd`

CXX = g++
LD = g++

INC = -I$(ISING_GUROBI_INC) 
CFLAGS = -Wall -m64 -g -fPIE -fexceptions -frounding-math -O3
LIB = -L$(ISING_GUROBI_LIB) -lgurobi_c++ -lgurobi65 -lboost_regex

BINDIR = bin
OBJDIR = obj
OUT_FINAL = $(BINDIR)/ising

OBJ = $(OBJDIR)/main.o $(OBJDIR)/solver.o $(OBJDIR)/periodicfunction.o $(OBJDIR)/tools.o $(OBJDIR)/lowerbound.o

all: prepare build

prepare:
	test -d bin || mkdir -p bin
	test -d $(OBJDIR) || mkdir -p $(OBJDIR)

build: $(OBJ)
	$(LD) -o $(OUT_FINAL) $(OBJ) $(LDFLAGS) $(LIB)

$(OBJDIR)/main.o: main.cpp
	$(CXX) $(CFLAGS) $(INC) -c main.cpp -o $(OBJDIR)/main.o

$(OBJDIR)/solver.o: solver.cpp
	$(CXX) $(CFLAGS) $(INC) -c solver.cpp -o $(OBJDIR)/solver.o

$(OBJDIR)/periodicfunction.o: periodicfunction.cpp
	$(CXX) $(CFLAGS) $(INC) -c periodicfunction.cpp -o $(OBJDIR)/periodicfunction.o

$(OBJDIR)/tools.o: tools.cpp
	$(CXX) $(CFLAGS) $(INC) -c tools.cpp -o $(OBJDIR)/tools.o

$(OBJDIR)/lowerbound.o: lowerbound.cpp
	$(CXX) $(CFLAGS) $(INC) -c lowerbound.cpp -o $(OBJDIR)/lowerbound.o

clean:
	rm -rf $(OBJDIR)
	rm -rf $(BINDIR)
