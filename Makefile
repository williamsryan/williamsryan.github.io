.PHONY : all test clean

all : watch

watch :
	stack build
	stack exec site watch

test :
	$(info ************  TEST TODO ************)

clean : 
	rm -rf out/ *.log instrumented/* .stack-work/ _cache/
