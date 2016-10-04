CFLAGS = -O3 -m64
#CFLAGS = -m64 -O3 -static -fno-strict-aliasing -funroll-all-loops -fexpensive-optimizations -Wall 
TARGET = CCLS_to_akmaxsat
TARGET_out = CCLS_to_akmaxsat_LB
all: ${TARGET} clean

${TARGET}: ${TARGET}.cpp
	g++ ${CFLAGS} ${TARGET}.cpp -o ${TARGET_out}

clean:
	rm -f *~

cleanup:
	rm -f ${TARGET}
	rm -f *~
