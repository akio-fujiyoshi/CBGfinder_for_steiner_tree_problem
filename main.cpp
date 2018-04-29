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

#ifdef _DEBUG
#define _CRTDBG_MAP_ALLOC
#include <stdlib.h>
#include <crtdbg.h>
#ifndef DBG_NEW 
#define DBG_NEW new ( _NORMAL_BLOCK , __FILE__ , __LINE__ ) 
#define new DBG_NEW 
#endif 
#endif

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <time.h>
#include <signal.h>
#include <string>
#include <iostream>
#include <fstream>
#include <algorithm>
#include <map>
#include <set>
#include <stack>
#include <climits>

#ifdef __linux__
#include <sys/types.h>
#include <unistd.h>
#endif

#include "CBGfinder.h"

using namespace std;

struct vertex_type *vertex;
struct edge_type *edge;
vid num_vertex;
eid num_edge;
vid num_terminal;

vid *elimination_order=NULL;
int random_seed=0;
weight_type total_weight;

weight_type estimated_weight;
set<eid> *estimated_edge;

clock_t start_all;

void out_of_memory() {
#ifdef _MESSAGE
	fprintf(stderr, "\nOut of Memory!\n");
	printf("Out of Memory!\n");
	printf("Approxmated-Edges:%d\n", estimated_edge->size());
	printf("Approxmated-Weight:%.2f\n\n", (double) estimated_weight);
#endif
	output_result();
	exit(0);
}

void signal_handler(int signal) {
	if (signal==SIGTERM || signal==SIGINT) {
#ifdef _MESSAGE
		fprintf(stderr, "\nSIGTERM received!\n");
		printf("SIGTERM received!\n");
		printf("Approxmated-Edges:%d\n", estimated_edge->size());
		printf("Approxmated-Weight:%.2f\n\n", (double) estimated_weight);
		clock_t end_all=clock();
		printf("Duration:%.3f\n\n", ((double) (end_all-start_all))/CLOCKS_PER_SEC);
#endif
		output_result();
		exit(0);
	}
}

void output_result(void) {
#ifndef _MESSAGE
	printf("VALUE %lld\n", (long long) estimated_weight);
	for (set<eid>::iterator i=estimated_edge->begin(); i!=estimated_edge->end(); ++i) {
		if (*i%2!=0) {
			printf("%d %d\n", edge[*i].head, edge[*i].tail);
		}
		else {
			printf("%d %d\n", edge[*i-1].head, edge[*i-1].tail);
		}
	}
#endif
}

bool operator<(const edge_type &lhs, const edge_type &rhs) {
	if (lhs.weight!=rhs.weight) return lhs.weight<rhs.weight;
	if (lhs.tail!=rhs.tail) return lhs.tail<rhs.tail;
	if (lhs.head!=rhs.head) return lhs.head<rhs.head;
	return lhs.label<rhs.label;
}

weight_type approx_st(struct vertex_type *v, vid num_vertex, struct edge_type *e, eid num_edge) {
	set<vid> v_set;
	map<edge_type, eid> e_set;
	set<vid> t_set;
	set<vid> **v_child=new set<vid>*[num_vertex+1];
	set<eid> **e_child=new set<eid>*[num_vertex+1];
	vid *v_parent=new vid[num_vertex+1];
	eid *e_parent=new eid[num_vertex+1];
	weight_type result_weight=0;

	//Initialize the adjacency sets of the vertexs.
	for (int i=1; i<=num_vertex; i++) {
		v_child[i]=new set<vid>;
		e_child[i]=new set<eid>;

		if (v[i].weight!=0) t_set.insert(i);
	}
	for (int i=1; i<=num_edge; i++) {
		e_child[e[i].tail]->insert(i);
	}

	vid cv=*t_set.begin();
	v_set.insert(cv);
	t_set.erase(cv);
	for (set<eid>::iterator i=e_child[cv]->begin(); i!=e_child[cv]->end(); ++i) {
		e_set[e[*i]]=*i;
	}

	//Constract a minimum spanning tree by Prim's method.
	while (t_set.size()>0 && e_set.size()>0) {
		edge_type ce=e_set.begin()->first;
		eid ce_id=e_set.begin()->second;
		e_set.erase(ce);

		cv=ce.head;

		//Check if adding the edge "ce" cause a cycle.
		if (v_set.count(cv)!=0) continue;

		v_set.insert(cv);
		v_child[ce.tail]->insert(ce.head);
		v_parent[ce.head]=ce.tail;
		e_parent[ce.head]=ce_id;

		if (t_set.count(cv)!=0) t_set.erase(cv);

		for (set<eid>::iterator i=e_child[cv]->begin(); i!=e_child[cv]->end(); ++i) {
			e_set[e[*i]]=*i;
		}

		estimated_edge->insert(ce_id);
		result_weight+=ce.weight;
	}
	if (t_set.size()>0) {
		fprintf(stderr, "\nNo Steiner Tree!\n");
		exit(1);
	}

	//Delete nonterminal leaves.
	for (set<vid>::iterator i=v_set.begin(); i!=v_set.end(); ++i) {
		vid cv=*i;

		while (v_child[cv]->size()==0 && v[cv].weight==0) {
			//Check if the vertex "cv" has been removed.
			if (v_child[v_parent[cv]]->count(cv)==0) break;

			v_child[v_parent[cv]]->erase(cv);

			estimated_edge->erase(e_parent[cv]);
			result_weight-=e[e_parent[cv]].weight;

			cv=v_parent[cv];
		}
	}

	//Release memory.
	for (int i=1; i<=num_vertex; i++) {
		delete v_child[i];
		delete e_child[i];
	}
	delete[] e_parent;
	delete[] v_parent;
	delete[] v_child;
	delete[] e_child;
	
	return result_weight;
}

int tree_size(set<vid> *b_adj, set<eid> *bag, vid parent, vid child) {
	if (b_adj[child].size()==1) return 1; //bag[child].size();

	int size=1; //bag[child].size();
	for (set<vid>::iterator i=b_adj[child].begin(); i!=b_adj[child].end(); ++i) {
		if (*i!=parent) {
			size+=tree_size(b_adj, bag, child, *i);
		}
	}
	return size;
}

int main(int argc, char *argv[]) {
	FILE *fin=NULL;
	char s[1024], s1[1024], s2[1024], s3[1024], *ptr;

	int num_rule;
	weight_type weight;
	int result;
	int *result_edge;
	int result_edge_num;
	char *automaton_filename=NULL;

	//set_new_handler(out_of_memory);
	//signal(SIGTERM, signal_handler);
	//signal(SIGINT, signal_handler);

	start_all = clock();

	Mode mode;
	mode.span=false;
	mode.ind=false;
	mode.dis=false;
	mode.min=true;
	mode.order_read=false;
	mode.order_save=false;

	int pos;
	for (pos=1; pos<argc-1; pos++) {
		if (strcmp(argv[pos], "-a")==0) {
			pos++;
			automaton_filename=argv[pos];
		}
		else if (strcmp(argv[pos], "-s")==0) {
			pos++;
			random_seed=atoi(argv[pos]);
		}
		else if (strcmp(argv[pos], "-spanning")==0) {
			mode.span=true;
		}
		else if (strcmp(argv[pos], "-not_induced")==0) {
			mode.ind=true;
		}
		else if (strcmp(argv[pos], "-minimum")==0) {
			mode.min=false;
		}
		else if (strcmp(argv[pos], "-connected")==0) {
			mode.dis=true;
		}
		else {
			printf("Usage: st-exact [-s random_seed] [-a automaton_filename] [-spanning] [-not_induced] [-connected] [-minimum] input_filename\n");
			exit(1);
		}
	}

	num_rule=load_automaton(automaton_filename);

	if (pos==argc-1) {
		fin=fopen(argv[argc-1], "r");
		if (fin==NULL) {
			fprintf(stderr, "Error: Cannot open the input file (%s).", argv[argc-1]);
			exit(1);
		}
	}
	else {
		fin=stdin;
	}

	ptr=fgets(s, 1024, fin);
	while (ptr!=NULL && strncmp(s, "SECTION Graph", 13)!=0 && strncmp(s, "Section Graph", 13)!=0) {
		ptr=fgets(s, 1024, fin);
	}

	if (s==NULL) {
		fprintf(stderr, "Error: \"SECTION Graph\" not found.");
		exit(1);
	}

	fgets(s, 1024, fin); // "Nodes XXX"
	sscanf(s, "Nodes %s", s1);
	num_vertex=atoi(s1);
	vertex=new struct vertex_type[num_vertex+1]; 

#ifdef _MESSAGE
	printf("Nodes:%d\n", num_vertex);
#endif

	for (int i=1; i<=num_vertex; i++) {
		vertex[i].label=0;
		vertex[i].weight=0;
	}

	fgets(s, 1024, fin); // "Edges XXX"
	sscanf(s, "Edges %s", s1);
	num_edge=atoi(s1)*2;
	edge=new struct edge_type[num_edge+1];

	total_weight=0;
	for (int i=1; i<=num_edge; i+=2) {
		fgets(s, 1024, fin); // "E XXX XXX XXX"
		sscanf(s, "E %s %s %s", s1, s2, s3);

		int v1=atoi(s1);
		int v2=atoi(s2);
		int w=atoi(s3);

		//Skip self-loops.
		if (v1==v2) {
			num_edge-=2;
			i-=2;
			continue;
		}

		if (v1<=0 || v2 <=0 || w<0) {
			fprintf(stderr, "Error: Edge Data (%s).", s);
			exit(1);
		}

		edge[i].head=edge[i+1].tail=v1;
		edge[i].tail=edge[i+1].head=v2;
		edge[i].weight=edge[i+1].weight=w;
		edge[i].label=edge[i+1].label=0;
		total_weight+=w;
	}

#ifdef _MESSAGE
	printf("Edges:%d\n", num_edge/2);
	printf("Total-Weight:%.2f\n", (double) total_weight);
#endif

	ptr=fgets(s, 1024, fin);
	while (ptr!=NULL && strncmp(s, "SECTION Terminals", 17)!=0 && strncmp(s, "Section Terminals", 17)!=0) {
		ptr=fgets(s, 1024, fin);
	}

	if (ptr==NULL) {
		fprintf(stderr, "Error: \"SECTION Terminals\" not found.");
		exit(1);
	}

	fgets(s, 1024, fin); // "Terminals XXX"
	sscanf(s, "Terminals %s", s1);
	num_terminal=atoi(s1);

#ifdef _MESSAGE
	printf("Terminals:%d\n", num_terminal);
	printf("Total-Weight*Terminals:%.2f\n", (double) total_weight*num_terminal);
#endif

	for (int i=0; i<num_terminal; i++) {
		fgets(s, 1024, fin); // "T XXX"
		sscanf(s, "T %s", s1);

		int t=atoi(s1);

		if (t<=0 || t>num_vertex) {
			fprintf(stderr, "Error: Terminal Data (%s).", s);
			exit(1);
		}

		vertex[t].weight=-total_weight;
	}

	ptr=fgets(s, 1024, fin);
	while (ptr!=NULL && strncmp(s, "SECTION Tree Decomposition", 26)!=0) {
		ptr=fgets(s, 1024, fin);
	}

	if (ptr!=NULL) {
		fgets(s, 1024, fin); // "s td XXX XXX XXX"
		if (s[0]!='s') fgets(s, 1024, fin); // "c We do not guarantee that this tree decomposition has minimum width."
		sscanf(s, "s td %s %s %s", s1, s2, s3);
		int num_bag=atoi(s1);
		int bag_size=atoi(s2);
#ifdef _MESSAGE
		printf("Num-Bag:%d\tBag-Size:%d\n", num_bag, bag_size);
#endif

		set<vid> b_set;
		set<vid> *bag=new set<vid>[num_bag+1];
		set<vid> *b_adj=new set<vid>[num_bag+1];

		for (int i=1; i<=num_bag; i++) {
			b_set.insert(i);

			fgets(s, 1024, fin); // "b BAG_NUMBER XXX XXX XXX ..."
			strtok(s, " "); // "b"
			ptr=strtok(NULL, " "); // "BAG_NUMBER"
			int bag_number=atoi(ptr);
			while(ptr!=NULL) {
				ptr=strtok(NULL, " "); // "XXX"
				if (ptr!=NULL) {
					int b=atoi(ptr);

					if (b<=0) {
						fprintf(stderr, "Error: Tree Decomposition Data (%s).", s);
						exit(1);
					}

					bag[bag_number].insert(b);
				}
			}
		}

		ptr=fgets(s, 1024, fin);
		while (ptr!=NULL && strncmp(s, "END", 3)!=0) {
			sscanf(s, "%s %s", s1, s2);

			int b1=atoi(s1);
			int b2=atoi(s2);

			if (b1<=0 || b2<=0) {
				fprintf(stderr, "Error: Tree Decomposition Data (%s).", s);
				exit(1);
			}

			b_adj[b1].insert(b2);
			b_adj[b2].insert(b1);

			ptr=fgets(s, 1024, fin);
		}
		if (ptr==NULL) {
			fprintf(stderr, "Error: Tree Decomposition Data (%s).", s);
			exit(1);
		}

		//From here, we make an elimination ordering.
		elimination_order=new vid[num_vertex];
		int pos=0;

		//Find the farthest leaf bag from the center for the first bag to remove.
		vid first_b=1;
		vid depth_max=0;
		stack<pair<vid, vid>> b_stack;
		pair<vid, vid> p;
		p.first=1;
		p.second=1;
		b_stack.push(p);
		bool *b_done=new bool[num_bag+1];
		for (int i=1; i<=num_bag; i++) b_done[i]=false;
		while(!b_stack.empty()) {
			p=b_stack.top();
			b_stack.pop();
			b_done[p.first]=true;
			if (b_adj[p.first].size()==1 && depth_max<p.second) {
				first_b=p.first;
				depth_max=p.second;
			}
			vid b=p.first;
			vid depth=p.second;
			for (set<vid>::iterator i=b_adj[b].begin(); i!=b_adj[b].end(); ++i) {
				if (!b_done[*i]) {
					p.first=*i;
					p.second=depth+1;
					b_stack.push(p);
				}
			}
		}

		vid b=first_b;
#ifdef _MONITOR
		printf("[%d:%d]", b, depth_max);
#endif
		while (b_set.size()>0) {
			if (b_adj[b].size()!=0) {
				vid parent=*b_adj[b].begin();
				for (set<vid>::iterator i=bag[b].begin(); i!=bag[b].end(); ++i) {
					if (bag[parent].count(*i)==0) {
						elimination_order[pos++]=*i;
					}
				}
			}
			else {
				for (set<vid>::iterator i=bag[b].begin(); i!=bag[b].end(); ++i) {
					elimination_order[pos++]=*i;
				}
			}

			//Erase the bag b, and renew the adjacency sets of the remaining bags.
			for (set<vid>::iterator i=b_adj[b].begin(); i!=b_adj[b].end(); ++i) {
				b_adj[*i].erase(b);
			}

			b_set.erase(b);

			//Decide a bag to remove next.
			if (b_set.size()>0) {
				vid parent_b=b;
				vid next_b=*b_adj[b].begin();
				vid depth=1;
				while (b_adj[next_b].size()>1) {
					depth++;
					int min_size=INT_MAX;
					vid min_b;
					for (set<vid>::iterator i=b_adj[next_b].begin(); i!=b_adj[next_b].end(); ++i) {
						if (*i!=parent_b) {
							int size=tree_size(b_adj, bag, next_b, *i);
							if (size<min_size) {
								min_size=size;
								min_b=*i;
							}
						}
					}
					parent_b=next_b;
					next_b=min_b;
				}

				b=next_b;
#ifdef _MONITOR
				if (b!=0) printf("[%d:%d]", b, depth);
#endif
			}
		}
#ifdef _MONITOR
		printf("\n");
#endif

		delete[] b_done;
		delete[] bag;
		delete[] b_adj;
	}

	fclose(fin);

	estimated_edge=new set<eid>;
	estimated_weight=approx_st(vertex, num_vertex, edge, num_edge);
#ifdef _MESSAGE
	printf("Estimated-Edges:%d\n", estimated_edge->size());
	printf("Estimated-Weight:%.2f\n", (double) estimated_weight);
#endif

	result_edge=new int[num_edge/2+1];
	result=find_CBG(mode, vertex, num_vertex, edge, num_edge, result_edge, &result_edge_num, &weight);
	if (result!=1) {
#ifdef _MESSAGE
		printf("Not Accepted!\n");
		clock_t end_all=clock();
		printf("Duration:%.3f\n\n", ((double) (end_all-start_all))/CLOCKS_PER_SEC);
		exit(0);
#endif
		//output_result();
		for(;;);
		exit(1);
	}
#ifdef _MESSAGE
	printf("Result-Edges:%d\n", result_edge_num);
#ifndef _STEINER_TREE_OPTIMIZATION
	printf("Result-Weight:%.2f\n", (double) weight+num_terminal*total_weight);
#else
	printf("Result-Weight:%.2f\n", (double) weight);
#endif
#endif

#ifndef _MESSAGE
#ifndef _STEINER_TREE
	printf("VALUE %lld\n", (long long) weight+num_terminal*total_weight);
#else
	printf("VALUE %lld\n", (long long) weight);
#endif
	for (int i=0; i<result_edge_num; i++) {
		if (result_edge[i]%2!=0) {
			printf("%d %d\n", edge[result_edge[i]].head, edge[result_edge[i]].tail);
		}
		else {
			printf("%d %d\n", edge[result_edge[i]-1].head, edge[result_edge[i]-1].tail);
		}
	}
#endif

	delete estimated_edge;
	delete[] vertex;
	delete[] edge;
	delete[] result_edge;	

#ifdef _MESSAGE
	clock_t end_all=clock();
	printf("Duration:%.3f\n", ((double) (end_all-start_all))/CLOCKS_PER_SEC);
#ifdef __linux__
	char command[1024];
	sprintf(command, "grep VmPeak /proc/%d/status", getpid());
	system(command);
#else
	printf("\n");
#endif
#endif

#ifdef _DEBUG
	_CrtDumpMemoryLeaks();
#endif

	return 0;
}
