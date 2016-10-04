CFLAGS = -O3 -m64
#CFLAGS = -m64 -O3 -static -fno-strict-aliasing -funroll-all-loops -fexpensive-optimizations -Wall 
TARGET = CCLS2014

all: ${TARGET} clean

${TARGET}: basic.h main.cpp
	g++ ${CFLAGS} main.cpp -o ${TARGET}

clean:
	rm -f *~

cleanup:
	rm -f ${TARGET}
	rm -f *~
