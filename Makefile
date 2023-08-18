.PHONY : all test clean

all : test

test :
	$(info ************  TEST TODO ************)

clean : 
	rm -rf out/ *.log instrumented/* .stack-work/ _cache/
