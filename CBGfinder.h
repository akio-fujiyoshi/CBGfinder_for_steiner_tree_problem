/*
    CBGfinder for Steiner Tree Problem version 1.3

    Copyright (C) 2018 Akio Fujiyoshi, Department of Computer and 
    Information Sciences, Ibaraki University. All rights reserved.

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/

#define MAX_W 7 //This valuse must be less than the size of child ID (cid).
#define MAX_TW 200
#define MAX_RULE 100
#define MAX_LR 100
#define ATMARK -2
#define ASTERISK -3
#define INITIAL_STATE 1
#define REPETITION_TW 0 //0 for graphs of too big TW

//#define _MESSAGE
//#define _MONITOR
//#define _TRACE

#define _STEINER_TREE_OPTIMIZATION
//#define _TIMELIMIT 300 //(second)

#ifdef _TIMELIMIT
extern clock_t start_all;
#endif

typedef unsigned int eid; //edge ID
typedef unsigned int vid; //vertex ID
typedef unsigned char rid; //rule ID
typedef unsigned char cid; //child ID
typedef unsigned char nalr; //number of application of limited rules
typedef long long weight_type; //weight

struct Mode {
	bool span;
	bool ind;
	bool dis;
	bool min;
	bool order_read;
	bool order_save;
};

//Data structures
struct vertex_type {
	int label;
	weight_type weight;
};

struct edge_type {
	int tail;
	int head;
	int label;
	weight_type weight;
};

extern char *order_filename;
extern vid *elimination_order;
extern int random_seed;

extern struct vertex_type *vertex;
extern struct edge_type *edge;
extern vid num_vertex;
extern eid num_edge;

int find_CBG(Mode exe_mode, struct vertex_type *v, int num_vertex, struct edge_type *e, int num_edge, int *result_edge, int *result_edge_num, weight_type *result_weight);
int load_automaton(char *automaton_filename);
int state(char *s);
int sigma(char *s);
int delta(char *s);
void output_result(void);
