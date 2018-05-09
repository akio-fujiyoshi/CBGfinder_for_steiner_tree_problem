# CBGfinder_for_steiner_tree_problem
This is a variation of CBGfinder specialized in the Steiner tree problem for PACE 2018 competition.

### Algorithm
The algorithm is based on the graphset-subgraph matching method of CBGfinder.
CBGfinder is a software for given graphs to find subgraphs (any subgraphs, spanning subgraphs or induced subgraphs) accepted by an automaton.

For speed-up, the reduce method of Bodlaender et. al. was implemented.

### Compile
Type "make" or "g++ -o st-exact -O3 -std=c++11 main.cpp CBGfinder.cpp".

### Run
Type "./st-exact -s 4321 < input_graph.gr > output.txt".
