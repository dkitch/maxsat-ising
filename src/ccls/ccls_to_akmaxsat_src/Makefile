CFLAGS = -O3 -m64
#CFLAGS = -m64 -O3 -static -fno-strict-aliasing -funroll-all-loops -fexpensive-optimizations -Wall 
TARGET = CCLS_to_akmaxsat

all: ${TARGET} clean

${TARGET}: ${TARGET}.cpp
	g++ ${CFLAGS} ${TARGET}.cpp -o ${TARGET}

clean:
	rm -f *~

cleanup:
	rm -f ${TARGET}
	rm -f *~
