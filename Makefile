st-exact: main.cpp CBGfinder.cpp CBGfinder.h
	g++ -O3 -std=c++11 main.cpp CBGfinder.cpp -o st-exact
clean:
	rm -f *.o st-exact
