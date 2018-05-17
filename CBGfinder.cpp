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

#include <stdio.h>
#include <string.h>
#include <time.h>
#include <set>
#include <vector>
#include <string>
#include <iostream>
#include <fstream>
#include <algorithm>
#include <new>
#include <random>
#include <bitset>
#include <map>
#include <unordered_set>

#include "CBGfinder.h"

using namespace std;

#ifdef _MONITOR
static int subgraph_count=0;
static int subgraph_max=0;
static int subgraph_total=0;
#endif

#ifdef _STEINER_TREE_OPTIMIZATION
extern weight_type estimated_weight;
extern set<eid> *estimated_edge;
#endif

//Data structures
struct rule_instance {
	int state_l;
	int state_r[MAX_W];
	int sigma;
	int delta[MAX_W];
	unsigned int width;
	unsigned int width2;
};

struct subCBGface {
	vid vertex;
	rid rule;
	cid x;
	vid parent;
};

//Global variables
static char state_table[100][80];
static char sigma_table[100][80];
static char delta_table[100][80];
static int size_state=0;
static int size_sigma=0;
static int size_delta=0;

static rule_instance rule[MAX_RULE];
static int num_rule;

static int num_lr=0;
static rid limited_rules[MAX_LR];
static unsigned char max_apply[MAX_LR];
static unsigned char min_apply[MAX_LR];

static Mode mode;
static bool accept;
char *order_filename;

#ifdef _STEINER_TREE_OPTIMIZATION
extern vid num_terminal;
#endif

//Data structures
class subCBG {
public:
	unsigned char size_face;
	struct subCBGface *face;
	nalr *num_apply;
#ifndef _STEINER_TREE_OPTIMIZATION
	weight_type weight;
#else
	unsigned int weight;
#endif
	bitset<32> *edge_selection;

	subCBG() {
	}

	~subCBG() {
		delete[] face;
		delete[] num_apply;
		delete[] edge_selection;
#ifdef _MONITOR
		subgraph_count--;
#endif
	}
};

struct ordered_vertex {
	vid vertex;
	int priority;
};

struct subCBGmap {
	set<vid> *unused_v_set;
	unordered_set<subCBG> *sg_set;
};

struct hyperedge {
	set<vid> *v_set;
	set<subCBGmap> *sgmap_set;
	bool initial;
	eid num_edge;
	eid *edge;
#ifdef _STEINER_TREE_OPTIMIZATION
	vid num_terminal;
#endif
};

//Supporting functions
namespace std {
	template <>
	struct hash<subCBG> {
		size_t operator()(const subCBG &sg) const {
			size_t hv=0;
			hv = hv*1009+sg.size_face;
			for (int i=0; i!=sg.size_face; i++) {
				hv = hv*1009+sg.face[i].parent;
				hv = hv*1009+sg.face[i].vertex;
#ifndef _STEINER_TREE_OPTIMIZATION
				hv = hv*1009+sg.face[i].rule;
				hv = hv*1009+sg.face[i].x;
			}
			for (int i=0; i<num_lr; i++) {
				hv = hv*1009+sg.num_apply[i];
#endif
			}

			return hv;
		}
	};
}

bool operator<(const subCBGmap &lhs, const subCBGmap &rhs) {
	if (lhs.unused_v_set->size() < rhs.unused_v_set->size()) return true;
	if (lhs.unused_v_set->size() > rhs.unused_v_set->size()) return false;
	for (set<vid>::iterator i=lhs.unused_v_set->begin(), j=rhs.unused_v_set->begin(); i!=lhs.unused_v_set->end(); ++i, ++j) {
		if (*i < *j) return true;
		if (*i > *j) return false;
	}
	return false;
}

bool operator<(const hyperedge &lhs, const hyperedge &rhs) {
	if (lhs.v_set->size() < rhs.v_set->size()) return true;
	if (lhs.v_set->size() > rhs.v_set->size()) return false;
	for (set<vid>::iterator i=lhs.v_set->begin(), j=rhs.v_set->begin(); i!=lhs.v_set->end(); ++i, ++j) {
		if (*i < *j) return true;
		if (*i > *j) return false;
	}
	return false;
}

bool operator==(const subCBG &lhs, const subCBG &rhs) {
	for (int i=0; i<lhs.size_face; i++) {
		if (lhs.face[i].parent != rhs.face[i].parent) return false;
#ifndef _STEINER_TREE_OPTIMIZATION
		if (lhs.face[i].rule != rhs.face[i].rule) return false;
		if (lhs.face[i].x != rhs.face[i].x) return false;
	}
	for (int i=0; i<num_lr; i++) {
		if (lhs.num_apply[i] != rhs.num_apply[i]) return false;
#endif
	}
	return true;
}

bool operator<(const subCBG &lhs, const subCBG &rhs) {
	if (lhs.size_face < rhs.size_face) return true;
	if (lhs.size_face > rhs.size_face) return false;
	for (int i=0; i<lhs.size_face; i++) {
		if (lhs.face[i].vertex < rhs.face[i].vertex) return true;
		if (lhs.face[i].vertex > rhs.face[i].vertex) return false;
		if (lhs.face[i].parent < rhs.face[i].parent) return true;
		if (lhs.face[i].parent > rhs.face[i].parent) return false;
#ifndef _STEINER_TREE_OPTIMIZATION
		if (lhs.face[i].rule < rhs.face[i].rule) return true;
		if (lhs.face[i].rule > rhs.face[i].rule) return false;
		if (lhs.face[i].x < rhs.face[i].x) return true;
		if (lhs.face[i].x > rhs.face[i].x) return false;
	}
	for (int i=0; i<num_lr; i++) {
		if (lhs.num_apply[i] < rhs.num_apply[i]) return true;
		if (lhs.num_apply[i] > rhs.num_apply[i]) return false;
#endif
	}
	return false;
}

bool operator<(const ordered_vertex &lhs, const ordered_vertex &rhs) {
	if (lhs.priority!=rhs.priority) return lhs.priority<rhs.priority;
	return lhs.vertex<rhs.vertex;
}

bool compPair(const pair<size_t, unsigned int> &lhs, pair<size_t, unsigned int> &rhs) {
	return lhs.second<rhs.second;
}

inline void merge(nalr *num_apply, nalr *num_apply1, nalr *num_apply2) {
	for (int i=0; i<num_lr; i++) {
		num_apply[i] = num_apply1[i]+num_apply2[i];
	}
}

//Submain functions
void add_subCBG(set<subCBGmap>::iterator i_map, subCBGface *face, unsigned char size_face, bitset<32> *edge_selection1, eid num_edge1, bitset<32> *edge_selection2, eid num_edge2, weight_type weight, nalr *num_apply) {
	static subCBGmap sg_map;
	static subCBG sg;

#ifdef _MONITOR
	subgraph_count++;
	subgraph_total++;
	if (subgraph_count>subgraph_max) subgraph_max=subgraph_count;
#endif

	eid num_edge=num_edge1+num_edge2;
	
	sg.size_face=size_face;
	if (size_face>0) sg.face=new subCBGface[size_face]; 
	sg.edge_selection=NULL;
	sg.weight=weight;
	sg.num_apply=new nalr[num_lr];

	for (int i=0; i<size_face; i++) {
		sg.face[i]=face[i];
	}

	if (num_apply!=NULL) {
		for (int i=0; i<num_lr; i++) {
			sg.num_apply[i]=num_apply[i];
		}
	}
	else {
		for (int i=0; i<num_lr; i++) {
			sg.num_apply[i]=0;
		}
	}

	//Check if a subgraph with the same face exists.
	unordered_set<subCBG>::iterator i_sg=i_map->sg_set->find(sg);
	if (i_sg==i_map->sg_set->end()) { //new subgraph
#ifdef _TRACE
		for (int j=0; j<sg.size_face; j++) {
			if (sg.face[j].parent==sg.face[j].vertex) {
				printf("[v%d,r%d(%d)]", sg.face[j].vertex, sg.face[j].rule, sg.face[j].x);
			}
			else if (sg.face[j].parent==0) {
				printf("root<-[v%d,r%d(%d)]", sg.face[j].vertex, sg.face[j].rule, sg.face[j].x);
			}
			else {
				printf("v%d<-[v%d,r%d(%d)]", sg.face[j].parent, sg.face[j].vertex, sg.face[j].rule, sg.face[j].x);
			}
		}
		printf("(%.2f)", (double) sg.weight);
#endif
		//Set the edge selection of a subgraph.
		sg.edge_selection=new bitset<32>[num_edge/32+2];
		if (edge_selection1!=NULL) {
			for (eid i=0; i<num_edge1/32+1; i++) {
				sg.edge_selection[i]=edge_selection1[i];
			}
		}
		else {
			for (eid i=0; i<num_edge1/32+1; i++) {
				sg.edge_selection[i]=0;
			}
		}
		int remainder=num_edge1%32;
		if (edge_selection2!=NULL) {
			sg.edge_selection[num_edge1/32]=sg.edge_selection[num_edge1/32]|(edge_selection2[0])<<remainder;
			sg.edge_selection[num_edge1/32+1]=edge_selection2[0]>>(32-remainder);
			for (eid i=num_edge1/32+1, j=1; i<num_edge/32+1; i++, j++) {
				sg.edge_selection[i]=sg.edge_selection[i]|(edge_selection2[j]<<remainder);
				sg.edge_selection[i+1]=edge_selection2[j]>>(32-remainder);
			}
		}
		else {
			for (eid i=num_edge1/32+1; i<num_edge/32+1; i++) {
				sg.edge_selection[i]=0;
			}
		}

		i_map->sg_set->insert(sg);
	}
	else { //already exists
#ifdef _TRACE
		printf("x ");
		for (int j=0; j<sg.size_face; j++) {
			if (sg.face[j].parent==sg.face[j].vertex) {
				printf("[v%d,r%d(%d)]", sg.face[j].vertex, sg.face[j].rule, sg.face[j].x);
			}
			else if (sg.face[j].parent==0) {
				printf("root<-[v%d,r%d(%d)]", sg.face[j].vertex, sg.face[j].rule, sg.face[j].x);
			}
			else {
				printf("v%d<-[v%d,r%d(%d)]", sg.face[j].parent, sg.face[j].vertex, sg.face[j].rule, sg.face[j].x);
			}
		}
#endif
		if (!mode.min && i_sg->weight<weight || mode.min && i_sg->weight>weight) {
#ifdef _TRACE
			printf("(%.2f->%.2f)", (double) i_sg->weight, (double) sg.weight);
#endif
			//Set the edge selection of a subgraph.
			sg.edge_selection=new bitset<32>[num_edge/32+2];
			if (edge_selection1!=NULL) {
				for (eid i=0; i<num_edge1/32+1; i++) {
					sg.edge_selection[i]=edge_selection1[i];
				}
			}
			else {
				for (eid i=0; i<num_edge1/32+1; i++) {
					sg.edge_selection[i]=0;
				}
			}
			int remainder=num_edge1%32;
			if (edge_selection2!=NULL) {
				sg.edge_selection[num_edge1/32]=sg.edge_selection[num_edge1/32]|(edge_selection2[0])<<remainder;
				sg.edge_selection[num_edge1/32+1]=edge_selection2[0]>>(32-remainder);
				for (eid i=num_edge1/32+1, j=1; i<num_edge/32+1; i++, j++) {
					sg.edge_selection[i]=sg.edge_selection[i]|(edge_selection2[j]<<remainder);
					sg.edge_selection[i+1]=edge_selection2[j]>>(32-remainder);
				}
			}
			else {
				for (eid i=num_edge1/32+1; i<num_edge/32+1; i++) {
					sg.edge_selection[i]=0;
				}
			}

			i_map->sg_set->erase(i_sg);
			i_map->sg_set->insert(sg);
		}
		else {
#ifdef _MONITOR
			subgraph_count--;
#endif
#ifdef _TRACE
			printf("(x %.2f)", (double) sg.weight);
#endif
			delete[] sg.num_apply;
			delete[] sg.face;
		}
	}

	sg.edge_selection=NULL;
	sg.num_apply=NULL;
	sg.face=NULL;
}

void contract_and_add_subCBG(hyperedge *he, vid v, set<vid> *unused_v_set, set<subCBGmap>::iterator i_map, subCBGface *face, unsigned char size_face, bitset<32> *edge_selection1, eid num_edge1, bitset<32> *edge_selection2, eid num_edge2, weight_type weight, nalr *num_apply) {
	//Find the terminal corresponding to the vertex v.
	int p=0;
	while (p<size_face) {
		if (face[p].vertex==v) break;
		++p;
	}

	//If no terminal is corresponding to v,
	if (p==size_face) {
		//and the mode is not spanning, then keep it.
		if (!mode.span) {
#ifdef _TRACE
			printf("Contraction (Keep a face-unchanged subCBG): ");
#endif
			unused_v_set->erase(v);
			add_subCBG(i_map, face, size_face, edge_selection1, num_edge1, edge_selection2, num_edge2, weight, num_apply);
			return;
		}
		//and the mode is spanning, then skip it.
		else {
			return;
		}
	}

	//Check if the size of v_set of he will be zero.
	bool size_will_be_zero=false;
	if (he->v_set->size()==1) {
		size_will_be_zero=true;
	}
	else if (!mode.span && size_face==1 && face[p].vertex==v) {
		size_will_be_zero=true;
	}
	else if (mode.ind && !mode.dis && face[p].rule!=0) {
		bool find=false;
		for (int q=0; q<size_face; q++) {
			if (p==q) continue;
			if (face[q].rule!=0 || face[q].rule==0 && face[q].parent!=0) {
				find=true;
				break;
			}
		}
		if (!find) size_will_be_zero=true;
	}

	//If the size of v_set of he will be zero, then contract it.
	if (size_will_be_zero) {
#ifdef _STEINER_TREE_OPTIMIZATION
		//Check if all terminals are in the subgraph.
		if (he->num_terminal<num_terminal && !(v!=0 && vertex[v].weight!=0 && he->num_terminal>=num_terminal-1)) {
			return;
		}
#endif

		if (face[p].x==(1<<rule[face[p].rule].width)-1 && (face[p].parent!=face[p].vertex || rule[face[p].rule].state_l==INITIAL_STATE)) {
			//Check the number of applications of limited rules.
			int k;
			for (k=0; k<num_lr; k++) {
				int num;

				if (face[p].rule==limited_rules[k]) {
					num=num_apply[k]+1;
				}
				else {
					num=num_apply[k];
				}

				if (num>max_apply[k]) break;
				if (num<min_apply[k]) break;
			}
			if (k<num_lr) return;
				
			//A successful subgraph is obtained.
			if (face[p].rule!=0) accept=true;

			static subCBGface new_face[MAX_TW+1];
			int new_size_face=0;
			for (int q=0; q<size_face; q++) {
				if (p==q) continue;

				new_face[new_size_face].vertex=face[q].vertex;
				new_face[new_size_face].parent=0; //This is to avoid creating disconneted subCBG. (Only for "mode.ind && !mode.dis")
				new_face[new_size_face].rule=face[q].rule;
				new_face[new_size_face].x=face[q].x;
				new_size_face++;
			}

			nalr new_num_apply[MAX_LR];
			for (k=0; k<num_lr; k++) {
				if (limited_rules[k]==face[p].rule) new_num_apply[k]=num_apply[k]+1;
				else new_num_apply[k]=num_apply[k];
			}

#ifdef _TRACE
			if (face[p].parent==face[p].vertex) {
				printf("Contraction [v%d,r%d(%d)]: ", face[p].vertex, face[p].rule, face[p].x);
			}
			else if (face[p].parent==0) {
				printf("Contraction root<-[v%d,r%d(%d)]: ", face[p].vertex, face[p].rule, face[p].x);
			}
			else {
				printf("Contraction v%d<-[v%d,r%d(%d)]: ", face[p].parent, face[p].vertex, face[p].rule, face[p].x);
			}
#endif
#ifndef _STEINER_TREE_OPTIMIZATION
			if (face[p].rule!=0) weight+=vertex[v].weight;
#endif
			add_subCBG(i_map, new_face, new_size_face, edge_selection1, num_edge1, edge_selection2, num_edge2, weight, new_num_apply);

			return;
		}
		else {
			return;
		}
	}

	//There are more than 2 terminals.

#ifndef _STEINER_TREE_OPTIMIZATION
	//If the mode is not disconnected, p is connected to the fixed root, and any other terminal is not connected to the fixed root, then skip it.
	if (!mode.dis && face[p].parent==0) {
		bool connect=false;
		for (int q=0; q<size_face; q++) {
			if (p==q) continue;
			if (face[q].parent==0) {
				connect=true;
				break;
			}
		}
		if (!connect) return;
	}

	//Check the existance of the fixed root.
	bool root=false;
	for (int j=0; j<size_face; j++) {
		if (face[j].parent==0) {
			root=true;
			break;
		}
	}

	//If p will be the new fixed root,
	if (face[p].parent==face[p].vertex) {
		//If the rhs of the rule does not have the initial state, then skip it.
		if (rule[face[p].rule].state_l!=INITIAL_STATE) return;

		//If the mode is not disconnected,
		if (!mode.dis && face[p].rule!=0) {
			//If the fixed root has already existed, then skip it. (p cannot be another fixed root.)
			if (root) return;

			//If p does not have any children, then skip it. (p cannot be the root of an isolated subgraph.)
			bool connect=false;
			for (int q=0; q<size_face; q++) {
				if (p==q) continue;
				if (face[q].parent==v) {
					connect=true;
					break;
				}
			}
			if (!connect) return;
		}
	}
#else
	if (unused_v_set->count(v)==0 && !(he->num_terminal>=num_terminal && he->v_set->size()-unused_v_set->size()==1) && !(v!=0 && vertex[v].weight!=0 && he->num_terminal>=num_terminal-1 && he->v_set->size()-unused_v_set->size()==1)) {
		//Check if p is connected to another terminal. 
		bool find_child=false;
		for (int q=p+1; q<size_face; q++) {
			if (face[q].parent==face[p].vertex) {
				find_child=true;
				break;
			}
		}
		if (face[p].parent==face[p].vertex && !find_child) return;
	}
#endif

	//Check if the rule will be statisfied.
	if (face[p].x!=(1<<rule[face[p].rule].width)-1) return;

	//Contract a subCBG with the vertex v.
	static subCBGface new_face[MAX_TW+1];
	int new_size_face=0;
#ifdef _STEINER_TREE_OPTIMIZATION
	int new_parent=0;
#endif
	for (int q=0; q<size_face; q++) {
		if (p==q) continue;

		new_face[new_size_face].vertex=face[q].vertex;
		new_face[new_size_face].rule=face[q].rule;
		new_face[new_size_face].x=face[q].x;
		if (face[q].parent==v) {
#ifndef _STEINER_TREE_OPTIMIZATION
			new_face[new_size_face].parent=0;
#else
			if (new_parent==0) {
				new_parent=face[q].vertex;
			}
			new_face[new_size_face].parent=new_parent;
#endif
		}
		else {
			new_face[new_size_face].parent=face[q].parent;
		}

		new_size_face++;
	}

	nalr new_num_apply[MAX_LR];
	int k;
	for (k=0; k<num_lr; k++) {
		if (limited_rules[k]==face[p].rule) new_num_apply[k]=num_apply[k]+1;
		else new_num_apply[k]=num_apply[k];
	}

#ifdef _TRACE
	if (face[p].parent==face[p].vertex) {
		printf("Contraction [v%d,r%d(%d)]: ", face[p].vertex, face[p].rule, face[p].x);
	}
	else if (face[p].parent==0) {
		printf("Contraction root<-[v%d,r%d(%d)]: ", face[p].vertex, face[p].rule, face[p].x);
	}
	else {
		printf("Contraction v%d<-[v%d,r%d(%d)]: ", face[p].parent, face[p].vertex, face[p].rule, face[p].x);
	}
#endif
#ifndef _STEINER_TREE_OPTIMIZATION
	if (face[p].rule!=0) weight+=vertex[v].weight;
#endif
	
	add_subCBG(i_map, new_face, new_size_face, edge_selection1, num_edge1, edge_selection2, num_edge2, weight, new_num_apply);

	return;
}

#ifdef _STEINER_TREE_OPTIMIZATION
void rank_reduction(hyperedge *he, vid contracting_vertex) {
#ifndef _DEBUG
	static vector<bool> left_right(num_vertex+1);
#else
	vector<bool> left_right(num_vertex+1);
#endif

	for (set<subCBGmap>::iterator i_map=he->sgmap_set->begin(); i_map!=he->sgmap_set->end(); ++i_map) {
		set<vid> v_set(*he->v_set);
		v_set.erase(contracting_vertex);
		for (set<vid>::iterator i=i_map->unused_v_set->begin(); i!=i_map->unused_v_set->end(); ++i) {
			v_set.erase(*i);
		}
		size_t num_cuts=pow(2, v_set.size()-1);

		//Check if num_cuts is more than 2.
		if (num_cuts<2) continue;

		int8_t **matrix= new int8_t*[i_map->sg_set->size()];
		for (int i=0; i<i_map->sg_set->size(); i++) {
			matrix[i]=new int8_t[num_cuts];
		}

		//Get the order of subgraphs.
		vector<pair<size_t, unsigned int>> order(i_map->sg_set->size());
		vector<size_t> r_order(i_map->sg_set->size());
		size_t sg_pos=0;
		for (unordered_set<subCBG>::iterator i_sg=i_map->sg_set->begin(); i_sg!=i_map->sg_set->end(); ++i_sg, sg_pos++) {
			order[sg_pos].first=sg_pos;
			order[sg_pos].second=i_sg->weight;
		}
		sort(order.begin(), order.end(), compPair);
		for (int i=0; i<i_map->sg_set->size(); i++) {
			r_order[order[i].first]=i;
		}

		//Construct a cut matrix.
		sg_pos=0;
		for (unordered_set<subCBG>::iterator i_sg=i_map->sg_set->begin(); i_sg!=i_map->sg_set->end(); ++i_sg, sg_pos++) {
			size_t cut_pos=0;
			for (size_t cut=1; cut<num_cuts*2; cut+=2, cut_pos++) {
				//Set each vertex left or right.
				bitset<32> cut_bits=cut;
				int j=0;
				for (set<vid>::iterator i=v_set.begin(); i!=v_set.end(); ++i, j++) {
					left_right[*i]=cut_bits.test(j);
				}

				//Check if sg is a refinement of cut.
				bool refinement=true;
				for (uint8_t i=0; i<i_sg->size_face; i++) {
					if (left_right[i_sg->face[i].parent]!=left_right[i_sg->face[i].vertex]) {
						refinement=false;
						break;
					}
				}

				if (refinement) matrix[r_order[sg_pos]][cut_pos]=1;
				else matrix[r_order[sg_pos]][cut_pos]=0;
			}
		}

		//Keep track of columns that are to be processed.
		vector<size_t> swipePositions;
		for (size_t i=0; i<num_cuts; i++){
			swipePositions.push_back(i);
		}

		set<size_t> sg_base;
		size_t i=0;
		while (i<i_map->sg_set->size() && swipePositions.size()>0){
			bool hasOne=false;
			size_t swipePosition=-1;
			size_t j=0;
			while(j<num_cuts && !hasOne){
				if (matrix[i][j]==1){
					hasOne=true;
					swipePosition=j;
				}
				j++;
			}
			if (hasOne){
				sg_base.insert(order[i].first);
				for (int k =i+1; k<i_map->sg_set->size(); k++){
					if (matrix[k][swipePosition]==1){
						for (j=0; j<swipePositions.size(); j++){
							size_t column=swipePositions[j];
							int8_t oldValue=matrix[k][column];
							int8_t swipeValue=matrix[i][column];
							int8_t newValue=(oldValue+swipeValue)%2;
							matrix[k][column]=newValue;

						}
					}
				}
			}
			if (swipePosition!=-1) swipePositions.erase(find(swipePositions.begin(), swipePositions.end(), swipePosition));
			i++;
		}

		//Release memory.
		for (int i=0; i<i_map->sg_set->size(); i++) {
			delete[] matrix[i];
		}
		delete[] matrix;

#ifdef _TRACE
		printf("Rank-Reduction: %d->%d\n", i_map->sg_set->size(), sg_base.size());
#else
#ifdef _MONITOR
		printf("[%d->%d]", i_map->sg_set->size(), sg_base.size());
#endif
#endif
		subCBG *sg_array=new subCBG[sg_base.size()];
		size_t j=0, j_pos=0;
		for (unordered_set<subCBG>::iterator i=i_map->sg_set->begin(); i!=i_map->sg_set->end(); ++i, j++) {
			if (sg_base.count(j)==0) continue;

			sg_array[j_pos].size_face=i->size_face;
			sg_array[j_pos].face=new subCBGface[i->size_face];
			for (int k=0; k<i->size_face; k++) {
				sg_array[j_pos].face[k]=i->face[k];
			}
			sg_array[j_pos].num_apply=new nalr[num_lr];
			for (int k=0; k<num_lr; k++) {
				sg_array[j_pos].num_apply[k]=i->num_apply[k];
			}
			sg_array[j_pos].weight=i->weight;
			sg_array[j_pos].edge_selection=new bitset<32>[he->num_edge/32+2];
			for (eid k=0; k<he->num_edge/32+1; k++) {
				sg_array[j_pos].edge_selection[k]=i->edge_selection[k];
			}

			j_pos++;
		}

		i_map->sg_set->clear();
		for (int i=0; i<j_pos; i++) {
			i_map->sg_set->insert(sg_array[i]);
		}

		//Release memory.
		for (size_t i=0; i<sg_base.size(); i++) {
			sg_array[i].face=NULL;
			sg_array[i].num_apply=NULL;
			sg_array[i].edge_selection=NULL;
		}
		delete[] sg_array;
	}
}
#endif

void HE_combine(hyperedge *he1, hyperedge *he2, vid contracting_vertex) {
	hyperedge he;
#ifndef _DEBUG	
	static vector<int> parent(num_vertex+1);
	static set<vid> empty_v_set;
#else
	vector<int> parent(num_vertex+1);
	set<vid> empty_v_set;
#endif

	he.v_set=new set<vid>;
	for (set<vid>::iterator i=he1->v_set->begin(); i!=he1->v_set->end(); ++i) {
		he.v_set->insert(*i);
	}
	for (set<vid>::iterator i=he2->v_set->begin(); i!=he2->v_set->end(); ++i) {
		he.v_set->insert(*i);
	}

	he.num_edge=he1->num_edge+he2->num_edge;
	he.edge=new eid[he.num_edge];
	for (eid i=0; i<he1->num_edge; i++) {
		he.edge[i]=he1->edge[i];
	}
	for (eid i=0; i<he2->num_edge; i++) {
		he.edge[i+he1->num_edge]=he2->edge[i];
	}

	he.sgmap_set=new set<subCBGmap>;
#ifdef _STEINER_TREE_OPTIMIZATION
	he.num_terminal=he1->num_terminal+he2->num_terminal;
#endif

	//Calculate the intersection, the relative complements of *he1->v_set and *he2->v_set.
	vector<vid> v_set_common;
	vector<vid> v_set_1only;
	vector<vid> v_set_2only;
	set_intersection(he1->v_set->begin(), he1->v_set->end(), he2->v_set->begin(), he2->v_set->end(), back_inserter(v_set_common));
	set_difference(he1->v_set->begin(), he1->v_set->end(), he2->v_set->begin(), he2->v_set->end(), back_inserter(v_set_1only));
	set_difference(he2->v_set->begin(), he2->v_set->end(), he1->v_set->begin(), he1->v_set->end(), back_inserter(v_set_2only));

	//If the size of both he1 and he2 are zero, then combine them unconditionally. This case happens when the input graph is not connected.
	if (he1->v_set->size()==0 && he2->v_set->size()==0) {
		bitset<32> *edge_selection1=NULL, *edge_selection2=NULL;
		weight_type weight1=0, weight2=0;
		for (set<subCBGmap>::iterator i_map=he1->sgmap_set->begin(); i_map!=he1->sgmap_set->end(); ++i_map) {
			for (unordered_set<subCBG>::iterator i=i_map->sg_set->begin(); i!=i_map->sg_set->end(); ++i) {
				if (edge_selection1==NULL) {
					edge_selection1=i->edge_selection;
					weight1=i->weight;
				}
				else if (!mode.min && i->weight>weight1 || mode.min && i->weight<weight1) {
					edge_selection1=i->edge_selection;
					weight1=i->weight;
				}
			}
		}
		for (set<subCBGmap>::iterator i_map=he2->sgmap_set->begin(); i_map!=he2->sgmap_set->end(); ++i_map) {
			for (unordered_set<subCBG>::iterator i=i_map->sg_set->begin(); i!=i_map->sg_set->end(); ++i) {
				if (edge_selection2==NULL) {
					edge_selection2=i->edge_selection;
					weight2=i->weight;
				}
				else if (!mode.min && i->weight>weight2 || mode.min && i->weight<weight2) {
					edge_selection2=i->edge_selection;
					weight2=i->weight;
				}
			}
		}

		//Find subCBGmap in he.
		subCBGmap sg_map;
		sg_map.unused_v_set=&empty_v_set;
		set<subCBGmap>::iterator i_map=he.sgmap_set->find(sg_map);
		if (i_map==he.sgmap_set->end()) {
			sg_map.unused_v_set=new set<vid>;
			sg_map.sg_set=new unordered_set<subCBG>;
			he.sgmap_set->insert(sg_map);

			i_map=he.sgmap_set->find(sg_map);
		}

		if (contracting_vertex==0) add_subCBG(i_map, NULL, 0, edge_selection1, he1->num_edge, edge_selection2, he2->num_edge, weight1+weight2, NULL);
		else contract_and_add_subCBG(&he, contracting_vertex, &empty_v_set, i_map, NULL, 0, edge_selection1, he1->num_edge, edge_selection2, he2->num_edge, weight1+weight2, NULL);

		//Release memory.
		for (set<subCBGmap>::iterator i_map=he1->sgmap_set->begin(); i_map!=he1->sgmap_set->end(); ++i_map) {
			delete i_map->unused_v_set;
			delete i_map->sg_set;
		}
		for (set<subCBGmap>::iterator i_map=he2->sgmap_set->begin(); i_map!=he2->sgmap_set->end(); ++i_map) {
			delete i_map->unused_v_set;
			delete i_map->sg_set;
		}
		delete he1->sgmap_set;
		delete he1->v_set;
		delete[] he1->edge;
		delete he2->sgmap_set;
		delete he2->v_set;
		delete[] he2->edge;
		
		he1->sgmap_set=he.sgmap_set;
		he1->v_set=he.v_set;
		he1->num_edge=he.num_edge;
		he1->edge=he.edge;
		he1->initial=he2->initial;

		return;
	}

	//If the size of he1 is zero, then then combine he1 and he2 unconditionally. This time, he1 is a newly created edge. 
	if (he1->v_set->size()==0) {
		for (set<subCBGmap>::iterator i_map2=he2->sgmap_set->begin(); i_map2!=he2->sgmap_set->end(); ++i_map2) {
			for (unordered_set<subCBG>::iterator i=i_map2->sg_set->begin(); i!=i_map2->sg_set->end(); ++i) {
				//Find subCBGmap in he.
				subCBGmap sg_map;
				set<vid> unused_v_set(*i_map2->unused_v_set);
				bool erase_unused=false;
				if (unused_v_set.count(contracting_vertex)!=0) {
					erase_unused=true;
					unused_v_set.erase(contracting_vertex);
				}
				sg_map.unused_v_set=&unused_v_set;
				set<subCBGmap>::iterator i_map=he.sgmap_set->find(sg_map);
				if (i_map==he.sgmap_set->end()) {
					sg_map.unused_v_set=new set<vid>(unused_v_set);
					sg_map.sg_set=new unordered_set<subCBG>;
					he.sgmap_set->insert(sg_map);

					i_map=he.sgmap_set->find(sg_map);
				}
				if (erase_unused) unused_v_set.insert(contracting_vertex);

				if (contracting_vertex==0) add_subCBG(i_map, i->face, i->size_face, NULL, he1->num_edge, i->edge_selection, he2->num_edge, i->weight, i->num_apply);
				else contract_and_add_subCBG(&he, contracting_vertex, i_map2->unused_v_set, i_map, i->face, i->size_face, NULL, he1->num_edge, i->edge_selection, he2->num_edge, i->weight, i->num_apply);
#ifdef _TRACE
				printf(" <=he1_first ");
				for (int k=0; k<i->size_face; k++) {
					if (i->face[k].parent==i->face[k].vertex) {
						printf("[v%d,r%d(%d)]", i->face[k].vertex, i->face[k].rule, i->face[k].x);
					}
					else if (i->face[k].parent==0) {
						printf("root<-[v%d,r%d(%d)]", i->face[k].vertex, i->face[k].rule, i->face[k].x);
					}
					else {
						printf("v%d<-[v%d,r%d(%d)]", i->face[k].parent, i->face[k].vertex, i->face[k].rule, i->face[k].x);
					}
				}
				printf("\n");
#endif
			}
		}

		//Release memory.
		for (set<subCBGmap>::iterator i_map=he1->sgmap_set->begin(); i_map!=he1->sgmap_set->end(); ++i_map) {
			delete i_map->unused_v_set;
			delete i_map->sg_set;
		}
		for (set<subCBGmap>::iterator i_map=he2->sgmap_set->begin(); i_map!=he2->sgmap_set->end(); ++i_map) {
			delete i_map->unused_v_set;
			delete i_map->sg_set;
		}
		delete he1->sgmap_set;
		delete he1->v_set;
		delete[] he1->edge;
		delete he2->sgmap_set;
		delete he2->v_set;
		delete[] he2->edge;
		
		he1->sgmap_set=he.sgmap_set;
		he1->v_set=he.v_set;
		he1->num_edge=he.num_edge;
		he1->edge=he.edge;
		he1->initial=he2->initial;

		return;
	}

#ifndef _STEINER_TREE_OPTIMIZATION
	//If the mode is neither spanning nor induced, then add copy of them to he unconditionally.
	if (!mode.span && !mode.ind) {
		for (set<subCBGmap>::iterator i_map1=he1->sgmap_set->begin(); i_map1!=he1->sgmap_set->end(); ++i_map1) {
			set<vid> unused_v_set(*i_map1->unused_v_set);
			subCBGmap sg_map;
			for (vector<vid>::iterator i=v_set_2only.begin(); i!=v_set_2only.end(); ++i) {
				unused_v_set.insert(*i);
			}

			//Find subCBGmap in he.
			bool erase_unused=false;
			if (unused_v_set.count(contracting_vertex)!=0) {
				erase_unused=true;
				unused_v_set.erase(contracting_vertex);
			}
			sg_map.unused_v_set=&unused_v_set;
			set<subCBGmap>::iterator i_map=he.sgmap_set->find(sg_map);
			if (i_map==he.sgmap_set->end()) {
				sg_map.unused_v_set=new set<vid>(unused_v_set);
				sg_map.sg_set=new unordered_set<subCBG>;
				he.sgmap_set->insert(sg_map);

				i_map=he.sgmap_set->find(sg_map);
			}
			if (erase_unused) unused_v_set.insert(contracting_vertex);

			for (unordered_set<subCBG>::iterator i=i_map1->sg_set->begin(); i!=i_map1->sg_set->end(); ++i) {
				if (contracting_vertex==0) add_subCBG(i_map, i->face, i->size_face, i->edge_selection, he1->num_edge, NULL, he2->num_edge, i->weight, i->num_apply);
				else contract_and_add_subCBG(&he, contracting_vertex, &unused_v_set, i_map, i->face, i->size_face, i->edge_selection, he1->num_edge, NULL, he2->num_edge, i->weight, i->num_apply);

#ifdef _TRACE
				printf(" <=he1_only ");
				for (int k=0; k<i->size_face; k++) {
					if (i->face[k].parent==i->face[k].vertex) {
						printf("[v%d,r%d(%d)]", i->face[k].vertex, i->face[k].rule, i->face[k].x);
					}
					else if (i->face[k].parent==0) {
						printf("root<-[v%d,r%d(%d)]", i->face[k].vertex, i->face[k].rule, i->face[k].x);
					}
					else {
						printf("v%d<-[v%d,r%d(%d)]", i->face[k].parent, i->face[k].vertex, i->face[k].rule, i->face[k].x);
					}
				}
				printf("\n");
#endif
			}
		}
		for (set<subCBGmap>::iterator i_map2=he2->sgmap_set->begin(); i_map2!=he2->sgmap_set->end(); ++i_map2) {
			set<vid> unused_v_set(*i_map2->unused_v_set);
			subCBGmap sg_map;
			for (vector<vid>::iterator i=v_set_1only.begin(); i!=v_set_1only.end(); ++i) {
				unused_v_set.insert(*i);
			}

			//Find subCBGmap in he.
			bool erase_unused=false;
			if (unused_v_set.count(contracting_vertex)!=0) {
				erase_unused=true;
				unused_v_set.erase(contracting_vertex);
			}
			sg_map.unused_v_set=&unused_v_set;
			set<subCBGmap>::iterator i_map=he.sgmap_set->find(sg_map);
			if (i_map==he.sgmap_set->end()) {
				sg_map.unused_v_set=new set<vid>(unused_v_set);
				sg_map.sg_set=new unordered_set<subCBG>;
				he.sgmap_set->insert(sg_map);

				i_map=he.sgmap_set->find(sg_map);
			}
			if (erase_unused) unused_v_set.insert(contracting_vertex);

			for (unordered_set<subCBG>::iterator i=i_map2->sg_set->begin(); i!=i_map2->sg_set->end(); ++i) {
				if (contracting_vertex==0) add_subCBG(i_map, i->face, i->size_face, NULL, he1->num_edge, i->edge_selection, he2->num_edge, i->weight, i->num_apply);
				else contract_and_add_subCBG(&he, contracting_vertex, &unused_v_set, i_map, i->face, i->size_face, NULL, he1->num_edge, i->edge_selection, he2->num_edge, i->weight, i->num_apply);

#ifdef _TRACE
				printf(" <=he2_only ");
				for (int k=0; k<i->size_face; k++) {
					if (i->face[k].parent==i->face[k].vertex) {
						printf("[v%d,r%d(%d)]", i->face[k].vertex, i->face[k].rule, i->face[k].x);
					}
					else if (i->face[k].parent==0) {
						printf("root<-[v%d,r%d(%d)]", i->face[k].vertex, i->face[k].rule, i->face[k].x);
					}
					else {
						printf("v%d<-[v%d,r%d(%d)]", i->face[k].parent, i->face[k].vertex, i->face[k].rule, i->face[k].x);
					}
				}
				printf("\n");
#endif
			}
		}
	}
#endif

	//Combine subCBGmaps in he1 and he2
	for (set<subCBGmap>::iterator i_map1=he1->sgmap_set->begin(); i_map1!=he1->sgmap_set->end(); ++i_map1) {
		for (size_t ptn=0; ptn<pow(2, v_set_2only.size()); ptn++) {
			set<vid> unused_v_set;
			subCBGmap sg_map;

			//Find subCBGmap in he2. 
			sg_map.unused_v_set=&unused_v_set;
			for (size_t j=0; j<v_set_common.size(); j++) {
				if (i_map1->unused_v_set->count(v_set_common[j])!=0) {
					unused_v_set.insert(v_set_common[j]);
				}
			}
			bitset<32> ptn_bits=ptn;
			for (int j=0; j<v_set_2only.size(); j++) {
				if (ptn_bits.test(j)) {
					unused_v_set.insert(v_set_2only[j]);
				}
			}
			set<subCBGmap>::iterator i_map2=he2->sgmap_set->find(sg_map);
			if (i_map2==he2->sgmap_set->end()) continue;

			//Obtain unused_v_set and used_v_set.
			for (size_t j=0; j<v_set_1only.size(); j++) {
				if (i_map1->unused_v_set->count(v_set_1only[j])!=0) {
					unused_v_set.insert(v_set_1only[j]);
				}
			}
			set<vid> used_v_set(*he.v_set);
			for (set<vid>::iterator i=unused_v_set.begin(); i!=unused_v_set.end(); ++i) {
				used_v_set.erase(*i);
			}

			//Find subCBGmap in he.
			bool erase_unused=false;
			if (unused_v_set.count(contracting_vertex)!=0) {
				erase_unused=true;
				unused_v_set.erase(contracting_vertex);
			}
			sg_map.unused_v_set=&unused_v_set;
			set<subCBGmap>::iterator i_map=he.sgmap_set->find(sg_map);
			if (i_map==he.sgmap_set->end()) {
				sg_map.unused_v_set=new set<vid>(unused_v_set);
				sg_map.sg_set=new unordered_set<subCBG>;
				he.sgmap_set->insert(sg_map);

				i_map=he.sgmap_set->find(sg_map);
			}
			if (erase_unused) unused_v_set.insert(contracting_vertex);

			//Combine subCBGs in i_map1 and i_map2.
			for (unordered_set<subCBG>::iterator i=i_map1->sg_set->begin(); i!=i_map1->sg_set->end(); ++i) {
#ifndef _STEINER_TREE_OPTIMIZATION
				if (!mode.dis && i->size_face==0) continue;
#endif

				for (unordered_set<subCBG>::iterator j=i_map2->sg_set->begin(); j!=i_map2->sg_set->end(); ++j) {
#ifndef _STEINER_TREE_OPTIMIZATION
					if (!mode.dis && j->size_face==0) continue;
#endif

#ifdef _STEINER_TREE_OPTIMIZATION
					//Check if the weight will be too big.
					if (i->weight+j->weight > estimated_weight) continue;
#endif

#ifdef _TIMELIMIT
					clock_t time_now=clock();
					if ((time_now-start_all)/CLOCKS_PER_SEC>=_TIMELIMIT) {
#ifdef _MESSAGE
						fprintf(stderr, "\nTime Over!\n");
						printf("Time Over!\n");
#ifdef _STEINER_TREE
						printf("Approxmated-Edges:%d\n", estimated_edge->size());
						printf("Approxmated-Weight:%.2f\n", (double) estimated_weight);
#endif
						printf("Duration:%.3f\n\n", ((double) (time_now-start_all))/CLOCKS_PER_SEC);
#endif
						output_result();
						exit(0);
					}
#endif

#ifndef _STEINER_TREE_OPTIMIZATION
					//Find the fixed root of each subCBG.
					bool root1=false;
					for (int k=0; k<i->size_face; k++) {
						if (i->face[k].parent==0) {
							root1=true;
							break;
						}
					}
					bool root2=false;
					for (int k=0; k<j->size_face; k++) {
						if (j->face[k].parent==0) {
							root2=true;
							break;
						}
					}

					//If the mode is not disconnected, and both subCBGs have a fixed root, then skip.
					if (!mode.dis && root1 && root2) {
						continue;
					}

					//Merge the number of applications of limited rules.
					nalr inner_num_apply[MAX_LR];
					nalr total_num_apply[MAX_LR];
					merge(inner_num_apply, i->num_apply, j->num_apply);
					merge(total_num_apply, i->num_apply, j->num_apply);
#endif

					//Check the feasibility of combination of subCBGs.
					bool combine=true;
					int p=0;
					int q=0;
					set<vid>::iterator r=used_v_set.begin();
					while (r!=used_v_set.end()) {
						if (p<i->size_face && q<j->size_face && *r==i->face[p].vertex && *r==j->face[q].vertex) {
#ifndef _STEINER_TREE_OPTIMIZATION
							if (i->face[p].rule!=j->face[q].rule || (i->face[p].x&j->face[q].x)!=0 || (i->face[p].parent!=i->face[p].vertex && j->face[q].parent!=j->face[q].vertex)) {
							//if (i->face[p].rule!=j->face[q].rule) { //|| (i->face[p].parent!=i->face[p].vertex && j->face[q].parent!=j->face[q].vertex)) {
								//The feasibility is negative.
								combine=false;
								break;
							}

							//Check the number of applications of the limited rules.
							int k;
							for (k=0; k<num_lr; k++) if (limited_rules[k]==i->face[p].rule) break;
							if (k<num_lr) total_num_apply[k]++;
#endif

							if (i->face[p].parent==i->face[p].vertex) {
								parent[*r]=j->face[q].parent;
							}
#ifndef _STEINER_TREE_OPTIMIZATION
							else {
								parent[*r]=i->face[p].parent;
							}
#else
							else if (j->face[q].parent==j->face[q].vertex) {
								parent[*r]=i->face[p].parent;
							}
							else {
								vid pa_i=i->face[p].parent;
								vid pa_j=j->face[q].parent;

								while (pa_i!=0 && pa_i!=parent[pa_i]) {
									pa_i=parent[pa_i];
								}
								while (pa_j!=0 && pa_j!=parent[pa_j]) {
									pa_j=parent[pa_j];
								}

								if (pa_i<pa_j) {
									parent[*r]=pa_i;
									parent[pa_j]=pa_i;
								}
								else {
									parent[*r]=pa_j;
									parent[pa_i]=pa_j;
								}
							}
#endif
							++p; ++q; ++r;
						}
						else if (p<i->size_face && *r==i->face[p].vertex) {
#ifndef _STEINER_TREE_OPTIMIZATION
							//Check the number of applications of the limited rules.
							int k;
							for (k=0; k<num_lr; k++) if (limited_rules[k]==i->face[p].rule) break;
							if (k<num_lr) total_num_apply[k]++;
#endif

							parent[*r]=i->face[p].parent;
							++p; ++r;
						}
						else if (q<j->size_face && *r==j->face[q].vertex) {
#ifndef _STEINER_TREE_OPTIMIZATION
							//Check the number of applications of the limited rules.
							int k;
							for (k=0; k<num_lr; k++) if (limited_rules[k]==j->face[q].rule) break;
							if (k<num_lr) total_num_apply[k]++;
#endif

							parent[*r]=j->face[q].parent;
							++q; ++r;
						}
						else {
							parent[*r]=0;
							++r;
						}
					}
					if (!combine) continue;

#ifndef _STEINER_TREE_OPTIMIZATION
					//Check the number of applications of limited rules.
					int k;
					for (k=0; k<num_lr; k++) {
						if (total_num_apply[k]>max_apply[k]) break;
					}
					if (k<num_lr) {
						continue;
					}
#else
					int k;
#endif

					//Find the parent of each terminal.
					combine=true;
					parent[0]=0;
					for (r=used_v_set.begin(); r!=used_v_set.end(); ++r) {
						vid pa=parent[*r];
				
						//Check if r is a root or has an inner root.
						if (pa==0 || pa==*r) continue;

						k=used_v_set.size();
						while (k>0 && pa!=0 && pa!=parent[pa]) {
							pa=parent[pa];
							k--;
						}
						if (k<=0) {
							//Find a cycle.
							combine=false;
							break;
						}
				
						vid next=parent[*r];
						parent[*r]=pa;
						while (next!=0 && next!=parent[next]) {
							next=parent[next];
							parent[next]=pa;
						}
					}
					if (!combine) continue;

					//Combine subCBGs.
					static subCBGface face[MAX_TW+1];
					int size_face=0;
					p=0;
					q=0;
					r=used_v_set.begin();
					while (r!=used_v_set.end()) {
						face[size_face].vertex=*r;
						face[size_face].parent=parent[*r];
						if (p<i->size_face && q<j->size_face && *r==i->face[p].vertex && *r==j->face[q].vertex) {
							face[size_face].rule=i->face[p].rule;
#ifndef _STEINER_TREE_OPTIMIZATION
							face[size_face].x=i->face[p].x|j->face[q].x;
#endif
							++p; ++q; ++r;
						}
						else if (p<i->size_face && *r==i->face[p].vertex) {
							face[size_face].rule=i->face[p].rule;
							face[size_face].x=i->face[p].x;
							++p; ++r;
						}
						else if (q<j->size_face && *r==j->face[q].vertex) {
							face[size_face].rule=j->face[q].rule;
							face[size_face].x=j->face[q].x;
							++q; ++r;
						}
						else {
							++r;
							continue;
						}

						size_face++;
					}

#ifndef _STEINER_TREE_OPTIMIZATION
					if (contracting_vertex==0) add_subCBG(i_map, face, size_face, i->edge_selection, he1->num_edge, j->edge_selection, he2->num_edge, i->weight+j->weight, inner_num_apply);
					else contract_and_add_subCBG(&he, contracting_vertex, &unused_v_set, i_map, face, size_face, i->edge_selection, he1->num_edge, j->edge_selection, he2->num_edge, i->weight+j->weight, inner_num_apply);
#else
					if (contracting_vertex==0) add_subCBG(i_map, face, size_face, i->edge_selection, he1->num_edge, j->edge_selection, he2->num_edge, i->weight+j->weight, i->num_apply);
					else contract_and_add_subCBG(&he, contracting_vertex, &unused_v_set, i_map, face, size_face, i->edge_selection, he1->num_edge, j->edge_selection, he2->num_edge, i->weight+j->weight, i->num_apply);
#endif

#ifdef _TRACE
					printf(" <= ");
					for (int k=0; k<i->size_face; k++) {
						if (i->face[k].parent==i->face[k].vertex) {
							printf("[v%d,r%d(%d)]", i->face[k].vertex, i->face[k].rule, i->face[k].x);
						}
						else if (i->face[k].parent==0) {
							printf("root<-[v%d,r%d(%d)]", i->face[k].vertex, i->face[k].rule, i->face[k].x);
						}
						else {
							printf("v%d<-[v%d,r%d(%d)]", i->face[k].parent, i->face[k].vertex, i->face[k].rule, i->face[k].x);
						}
					}
					printf(" + ");
					for (int k=0; k<j->size_face; k++) {
						if (j->face[k].parent==j->face[k].vertex) {
							printf("[v%d,r%d(%d)]", j->face[k].vertex, j->face[k].rule, j->face[k].x);
						}
						else if (j->face[k].parent==0) {
							printf("root<-[v%d,r%d(%d)]", j->face[k].vertex, j->face[k].rule, j->face[k].x);
						}
						else {
							printf("v%d<-[v%d,r%d(%d)]", j->face[k].parent, j->face[k].vertex, j->face[k].rule, j->face[k].x);
						}
					}
					printf("\n");
#endif
				}
			}
		}
	}

#ifdef _STEINER_TREE_OPTIMIZATION
	if (he.v_set->size()<32) rank_reduction(&he, contracting_vertex);
#endif

	//Release memory.
	for (set<subCBGmap>::iterator i=he1->sgmap_set->begin(); i!=he1->sgmap_set->end(); ++i) {
		delete i->unused_v_set;
		delete i->sg_set;
	}
	for (set<subCBGmap>::iterator i=he2->sgmap_set->begin(); i!=he2->sgmap_set->end(); ++i) {
		delete i->unused_v_set;
		delete i->sg_set;
	}
	delete he1->sgmap_set;
	delete he1->v_set;
	delete[] he1->edge;
	delete he2->sgmap_set;
	delete he2->v_set;
	delete[] he2->edge;

	he1->sgmap_set=he.sgmap_set;
	he1->v_set=he.v_set;
	he1->num_edge=he.num_edge;
	he1->edge=he.edge;
	he1->initial=false;

	return;
}

int check_tw(vid *temp_order, int *priority, int num_vertex, struct edge_type *e, int num_edge) {
	set<ordered_vertex> v_set;
	set<vid> **v_adj=new set<vid>*[num_vertex+1];
	int tw_max=0;

	//Initialize the adjacency sets of the vertexs.
	for (int i=1; i<=num_vertex; i++) {
		v_adj[i]=new set<vid>;
	}
	for (int i=1; i<=num_edge; i++) {
		v_adj[e[i].head]->insert(e[i].tail);
		v_adj[e[i].tail]->insert(e[i].head);
	}

	if (temp_order==NULL) {
		for (int i=0; i<num_vertex; i++) {
			//Determine a vertex to remove.
			vid v=elimination_order[i];

			int tw=v_adj[v]->size();
			if (tw_max<tw) tw_max=tw;

			//Erase the vertex v, and renew the adjacency sets of the remaining vertexs.
			for (set<vid>::iterator j=v_adj[v]->begin(); j!=v_adj[v]->end(); ++j) {
				v_adj[*j]->erase(v);
				for (set<vid>::iterator k=v_adj[v]->begin(); k!=v_adj[v]->end(); ++k) {
					if (*j==*k) continue;
					v_adj[*j]->insert(*k);
				}
			}
			v_adj[v]->clear();

			tw=0;
		}

		//Release memory.
		for (int i=1; i<=num_vertex; i++) {
			delete v_adj[i];
		}
		delete[] v_adj;

		return tw_max;
	}

	//Initialize a priority set of the vertexs.
	for (int i=1; i<=num_vertex; i++) {
		ordered_vertex ov;

		ov.vertex=i;
		ov.priority=priority[i];
		v_set.insert(ov);
	}

	int *act=new int[num_vertex+1];
	for (int i=0; i<num_vertex+1; i++) act[i]=0;
	set<vid> act_vertex;

	int pos=0;
	for (bool change=true; change;) {
		change=false;

		int tw=0;
		while (v_set.size()>0) {
			//Determine a vertex to remove.
			ordered_vertex ov;
			vid v=0;
			int act_max=0;
			for (set<ordered_vertex>::iterator i=v_set.begin(); i!=v_set.end(); ++i) {
				//Check if a vertex with the minimum degree.
				if (v_adj[i->vertex]->size()<=tw) {
					if (v==0) {
						ov=*i;
						v=i->vertex;

						act_max=act[i->vertex];
					}
					else {
						if (act[i->vertex]>act_max) {
							ov=*i;
							v=i->vertex;

							act_max=act[i->vertex];
						}
					}
				}
			}
			if (v==0) {
				tw++;
				if (tw_max<tw) tw_max=tw;
				continue;
			}

			temp_order[pos++]=v;

			for (set<vid>::iterator j=v_adj[v]->begin(); j!=v_adj[v]->end(); ++j) {
				act[*j]--;
				if (act_vertex.count(*j)==0) {
					for (set<vid>::iterator k=v_adj[*j]->begin(); k!=v_adj[*j]->end(); ++k) {
						act[*k]++;
					}
				}
				act_vertex.insert(*j);
			}


			//Erase the vertex v, and renew the adjacency sets of the remaining vertexs.
			for (set<vid>::iterator j=v_adj[v]->begin(); j!=v_adj[v]->end(); ++j) {
				v_adj[*j]->erase(v);
				for (set<vid>::iterator k=v_adj[v]->begin(); k!=v_adj[v]->end(); ++k) {
					if (*j==*k) continue;
					v_adj[*j]->insert(*k);
				}
			}
			v_adj[v]->clear();
			v_set.erase(ov);
			act_vertex.erase(v);

			tw=0;
			change=true;
		}
	}

	//Release memory.
	for (int i=1; i<=num_vertex; i++) {
		delete v_adj[i];
	}
	delete[] v_adj;
	delete[] act;

	return tw_max;
}

//The main function
int find_CBG(Mode exe_mode, struct vertex_type *input_vertex, int input_num_vertex, struct edge_type *input_edge, int input_num_edge, int *result_edge, int *result_edge_num, weight_type *result_weight) {
	set<vid> **v_adj;
	set<vid> v_set;
	set<hyperedge> he_set;
	set<hyperedge> **v_he;
	map<vid, hyperedge*> *temp_he;
	int tw;
	FILE *fout;

	num_vertex=input_num_vertex;
	vertex=input_vertex;
	num_edge=input_num_edge;
	edge=input_edge;

	//Allocate memory.
	v_adj=new set<vid>*[num_vertex+1];
	v_he=new set<hyperedge>*[num_vertex+1];
	temp_he=new map<vid, hyperedge*>[num_vertex+1];

	mode=exe_mode;
	accept=false;
	*result_edge_num=0;

	if (mode.order_read) {
		ifstream fin(order_filename);
		if (fin.fail()) {
			fprintf(stderr, "Error: \"%s\" cannot be opened!", order_filename);
			exit(1);
		}

		elimination_order=new vid[num_vertex];
		for (vid i=0; i<num_vertex; i++) {
			fin>>elimination_order[i];
		}

		tw = check_tw(NULL, NULL, num_vertex, edge, num_edge);
	}
	else if (elimination_order!=NULL) {
		tw = check_tw(NULL, NULL, num_vertex, edge, num_edge);
	}
	else {
		elimination_order=new vid[num_vertex];
		int *priority=new int[num_vertex+1];
		vid *temp_order=new vid[num_vertex];

		for (vid i=1; i<=num_vertex; i++) {
			priority[i]=0;
		}
		tw = check_tw(temp_order, priority, num_vertex, edge, num_edge);

		for (vid i=0; i<num_vertex; i++) {
			elimination_order[i]=temp_order[i];
		}

		if (tw>3) {
			int best_tw=tw;

#ifdef _MONITOR
			printf("%d ", tw);
#endif
			mt19937 mt(4321+37);
			for (int i=0; i<REPETITION_TW; i++) {
				for (int j=1; j<=num_vertex; j++) {
					priority[j]=mt();
				}

				tw = check_tw(temp_order, priority, num_vertex, edge, num_edge);

				if (tw<best_tw) {
					best_tw=tw;

					for (vid i=0; i<num_vertex; i++) {
						elimination_order[i]=temp_order[i];
					}
				}
#ifdef _MONITOR
				printf("%d ",tw);
#endif
			}
#ifdef _MONITOR
			printf("\nbest:%d\n", best_tw);
#endif
			tw=best_tw;
		}

		if (mode.order_save) { 
			fout=fopen("order.txt", "w");
			for (vid i=0; i<num_vertex; i++) {
				fprintf(fout, "%d ", elimination_order[i]);
			}
			fclose(fout);
		}

		delete[] priority;
		delete[] temp_order;
	}

#ifdef _TRACE
	printf("TW<=%d\n", tw);
#else
#ifdef _MONITOR
	printf("Tree-Width:%d\n", tw);
#else
#ifdef _MESSAGE
	printf("Tree-Width:%d\n", tw);
#endif
#endif
#endif

	if (tw>MAX_TW) {
		return 2;
	}

	//Initialize the adjacency sets of the vertexs.
	for (vid i=1; i<=num_vertex; i++) {
		v_adj[i]=new set<vid>;
		v_set.insert(i);
	}
	for (eid i=1; i<=num_edge; i++) {
		v_adj[edge[i].head]->insert(edge[i].tail);
		v_adj[edge[i].tail]->insert(edge[i].head);
	}
	
	//Initialize the hyper edges.
#ifdef _TRACE
	printf("Initialize:\n");
#endif
	for (vid i=1; i<=num_vertex; i++) {
		v_he[i]=new set<hyperedge>;
	}

#ifndef _DEBUG	
	static set<vid> empty_v_set;
#else
	set<vid> empty_v_set;
#endif
	for (eid i=1; i<=num_edge; i++) {
		int v1, v2;
		v1=edge[i].tail;
		v2=edge[i].head;

#ifdef _STEINER_TREE_OPTIMIZATION
		if (v1>v2) continue; //Consider only one direction.
#endif

		hyperedge *he;
		if (v1<v2) {
			if (temp_he[v1][v2]==NULL) {
				he=new hyperedge;
				he->v_set=new set<vid>;
				he->v_set->insert(v1);
				he->v_set->insert(v2);
				he->sgmap_set=new set<subCBGmap>;
				he->num_edge=1;
				he->edge=new eid[1];
				he->edge[0]=i;
				he->initial=true;
#ifdef _STEINER_TREE_OPTIMIZATION
				he->num_terminal=0;
#endif
				temp_he[v1][v2]=he;
			}
			else {
				he=temp_he[v1][v2];
			}
		}
		else {
			if (temp_he[v2][v1]==NULL) {
				he=new hyperedge;
				he->v_set=new set<vid>;
				he->v_set->insert(v1);
				he->v_set->insert(v2);
				he->sgmap_set=new set<subCBGmap>;
				he->num_edge=1;
				he->edge=new eid[1];
				he->edge[0]=i;
				he->initial=true;
#ifdef _STEINER_TREE_OPTIMIZATION
				he->num_terminal=0;
#endif
				temp_he[v2][v1]=he;
			}
			else {
				he=temp_he[v2][v1];
			}
		}

		//v1(parent)-n->v2(child)
		for (int k=1; k<=num_rule; k++) {
			for (int l=1; l<=num_rule; l++) {
				for (unsigned int n=0; n<rule[k].width; n++) {
					if (rule[k].sigma==vertex[v1].label && rule[l].sigma==vertex[v2].label && rule[k].state_r[n]==rule[l].state_l && rule[k].delta[n]==edge[i].label) {
						if ((rule[k].state_l==INITIAL_STATE && rule[k].width>v_adj[v1]->size()) || (rule[k].state_l!=INITIAL_STATE && rule[k].width+1>v_adj[v1]->size()) || (rule[l].state_l==INITIAL_STATE && rule[l].width>v_adj[v2]->size()) || (rule[l].state_l!=INITIAL_STATE && rule[l].width+1>v_adj[v2]->size())) continue;
						static subCBGface face[2];
						if (v1<v2) {
							face[0].vertex=v1;
							face[1].vertex=v2;
							face[0].parent=v1;
							face[1].parent=v1;
							face[0].rule=k;
							face[1].rule=l;
							face[0].x=1<<n;
							face[1].x=0;
						}
						else {
							face[1].vertex=v1;
							face[0].vertex=v2;
							face[1].parent=v1;
							face[0].parent=v1;
							face[1].rule=k;
							face[0].rule=l;
							face[1].x=1<<n;
							face[0].x=0;
						}

						//Find subCBGmap in he.
						subCBGmap sg_map;
						sg_map.unused_v_set=&empty_v_set;
						set<subCBGmap>::iterator i_map=he->sgmap_set->find(sg_map);
						if (i_map==he->sgmap_set->end()) {
							sg_map.unused_v_set=new set<vid>;
							sg_map.sg_set=new unordered_set<subCBG>;
							he->sgmap_set->insert(sg_map);

							i_map=he->sgmap_set->find(sg_map);
						}

						static bitset<32> edge_selection[1];
						edge_selection[0]=1;

						add_subCBG(i_map, face, 2, edge_selection, 1, NULL, 0, edge[i].weight, NULL);
#ifdef _TRACE
						printf("\n");
#endif
					}
				}
			}
		}

		//v1(parent)-n->@:q<-o-v2(parent)
		for (int k=1; k<=num_rule; k++) {
			for (int l=1; l<=num_rule; l++) {
				for (unsigned int n=0; n<rule[k].width; n++) {
					for (unsigned int o=0; o<rule[l].width; o++) {
						if (rule[k].sigma==vertex[v1].label && rule[l].sigma==vertex[v2].label && rule[k].state_r[n]==rule[l].state_r[o] && rule[k].delta[n]==edge[i].label && rule[l].delta[o]==ATMARK) {
							if ((rule[k].state_l==INITIAL_STATE && rule[k].width>v_adj[v1]->size()) || (rule[k].state_l!=INITIAL_STATE && rule[k].width+1>v_adj[v1]->size()) || (rule[l].state_l==INITIAL_STATE && rule[l].width>v_adj[v2]->size()) || (rule[l].state_l!=INITIAL_STATE && rule[l].width+1>v_adj[v2]->size())) continue;
							static subCBGface face[2];
							if (v1<v2) {
								face[0].vertex=v1;
								face[1].vertex=v2;
								face[0].parent=v1;
								face[1].parent=v2;
								face[0].rule=k;
								face[1].rule=l;
								face[0].x=1<<n;
								face[1].x=1<<o;
							}
							else {
								face[1].vertex=v1;
								face[0].vertex=v2;
								face[1].parent=v1;
								face[0].parent=v2;
								face[1].rule=k;
								face[0].rule=l;
								face[1].x=1<<n;
								face[0].x=1<<o;
							}

							//Find subCBGmap in he.
							subCBGmap sg_map;
							sg_map.unused_v_set=&empty_v_set;
							set<subCBGmap>::iterator i_map=he->sgmap_set->find(sg_map);
							if (i_map==he->sgmap_set->end()) {
								sg_map.unused_v_set=new set<vid>;
								sg_map.sg_set=new unordered_set<subCBG>;
								he->sgmap_set->insert(sg_map);

								i_map=he->sgmap_set->find(sg_map);
							}

							static bitset<32> edge_selection[1];
							edge_selection[0]=1;

							add_subCBG(i_map, face, 2, edge_selection, 1, NULL, 0, edge[i].weight, NULL);
#ifdef _TRACE
							printf("\n");
#endif
						}
					}
				}
			}
		}

		//v1(parent)-*->v2(child)
		for (int k=1; k<=num_rule; k++) {
			for (int l=1; l<=num_rule; l++) {
				for (unsigned int n=rule[k].width; n<rule[k].width+rule[k].width2; n++) {
					if (rule[k].sigma==vertex[v1].label && rule[l].sigma==vertex[v2].label && rule[k].state_r[n]==rule[l].state_l && rule[k].delta[n]==edge[i].label) {
						static subCBGface face[2];
						if (v1<v2) {
							face[0].vertex=v1;
							face[1].vertex=v2;
							face[0].parent=v1;
							face[1].parent=v1;
							face[0].rule=k;
							face[1].rule=l;
							face[0].x=0;
							face[1].x=0;
						}
						else {
							face[1].vertex=v1;
							face[0].vertex=v2;
							face[1].parent=v1;
							face[0].parent=v1;
							face[1].rule=k;
							face[0].rule=l;
							face[1].x=0;
							face[0].x=0;
						}

						//Find subCBGmap in he.
						subCBGmap sg_map;
						sg_map.unused_v_set=&empty_v_set;
						set<subCBGmap>::iterator i_map=he->sgmap_set->find(sg_map);
						if (i_map==he->sgmap_set->end()) {
							sg_map.unused_v_set=new set<vid>;
							sg_map.sg_set=new unordered_set<subCBG>;
							he->sgmap_set->insert(sg_map);

							i_map=he->sgmap_set->find(sg_map);
						}

						static bitset<32> edge_selection[1];
						edge_selection[0]=1;

						add_subCBG(i_map, face, 2, edge_selection, 1, NULL, 0, edge[i].weight, NULL);
#ifdef _TRACE
						printf("\n");
#endif
					}
				}
			}
		}

		//For stuffing, if the mode is not induced, then
		if (!mode.ind) {
			for (int k=1; k<=num_rule; k++) {
				for (int l=1; l<=num_rule; l++) {
					if (rule[k].sigma==vertex[v1].label && rule[l].sigma==vertex[v2].label) {
						if ((rule[k].state_l==INITIAL_STATE && rule[k].width>v_adj[v1]->size()) || (rule[k].state_l!=INITIAL_STATE && rule[k].width+1>v_adj[v1]->size()) || (rule[l].state_l==INITIAL_STATE && rule[l].width>v_adj[v2]->size()) || (rule[l].state_l!=INITIAL_STATE && rule[l].width+1>v_adj[v2]->size())) continue;
						static subCBGface face[2];
						if (v1<v2) {
							face[0].vertex=v1;
							face[1].vertex=v2;
							face[0].parent=v1;
							face[1].parent=v2;
							face[0].rule=k;
							face[1].rule=l;
							face[0].x=0;
							face[1].x=0;
						}
						else {
							face[1].vertex=v1;
							face[0].vertex=v2;
							face[1].parent=v1;
							face[0].parent=v2;
							face[1].rule=k;
							face[0].rule=l;
							face[1].x=0;
							face[0].x=0;
						}

						//Find subCBGmap in he.
						subCBGmap sg_map;
						sg_map.unused_v_set=&empty_v_set;
						set<subCBGmap>::iterator i_map=he->sgmap_set->find(sg_map);
						if (i_map==he->sgmap_set->end()) {
							sg_map.unused_v_set=new set<vid>;
							sg_map.sg_set=new unordered_set<subCBG>;
							he->sgmap_set->insert(sg_map);

							i_map=he->sgmap_set->find(sg_map);
						}

						static bitset<32> edge_selection[1];
						edge_selection[0]=0;

						add_subCBG(i_map, face, 2, edge_selection, 1, NULL, 0, 0, NULL);
#ifdef _TRACE
						printf("\n");
#endif
					}
				}
			}
		}

		//For stuffing, if the mode is not spanning, then
		if (!mode.span) {
#ifdef _STEINER_TREE_OPTIMIZATION
			if (vertex[v1].weight==0 && vertex[v2].weight==0) {
				static bitset<32> edge_selection[1];
				edge_selection[0]=0;

				//Find subCBGmap in he.
				set<vid> unused_v_set;
				unused_v_set.insert(v1);
				unused_v_set.insert(v2);
				subCBGmap sg_map;
				sg_map.unused_v_set=&unused_v_set;
				set<subCBGmap>::iterator i_map=he->sgmap_set->find(sg_map);
				if (i_map==he->sgmap_set->end()) {
					sg_map.unused_v_set=new set<vid>(unused_v_set);
					sg_map.sg_set=new unordered_set<subCBG>;
					he->sgmap_set->insert(sg_map);

					i_map=he->sgmap_set->find(sg_map);
				}

				add_subCBG(i_map, NULL, 0, edge_selection, 1, NULL, 0, 0, NULL);
#ifdef _TRACE
				printf("\n");
#endif
			}
#endif

			static subCBGface face[1];
			for (int k=1; k<=num_rule; k++) {
				if (rule[k].sigma==vertex[v1].label && rule[k].width<=v_adj[v1]->size()) {
#ifdef _STEINER_TREE_OPTIMIZATION
					if (vertex[v2].weight==0) {
#endif
					face[0].vertex=v1;
					face[0].parent=v1;
					face[0].rule=k;
					face[0].x=0;

					//Find subCBGmap in he.
					set<vid> unused_v_set;
					unused_v_set.insert(v2);
					subCBGmap sg_map;
					sg_map.unused_v_set=&unused_v_set;
					set<subCBGmap>::iterator i_map=he->sgmap_set->find(sg_map);
					if (i_map==he->sgmap_set->end()) {
						sg_map.unused_v_set=new set<vid>(unused_v_set);
						sg_map.sg_set=new unordered_set<subCBG>;
						he->sgmap_set->insert(sg_map);

						i_map=he->sgmap_set->find(sg_map);
					}

					static bitset<32> edge_selection[1];
					edge_selection[0]=0;

					add_subCBG(i_map, face, 1, edge_selection, 1, NULL, 0, 0, NULL);
#ifdef _TRACE
					printf("\n");
#endif
#ifdef _STEINER_TREE_OPTIMIZATION
					}
#endif
				}
				if (rule[k].sigma==vertex[v2].label && rule[k].width<=v_adj[v2]->size()) {
#ifdef _STEINER_TREE_OPTIMIZATION
					if (vertex[v1].weight==0) {
#endif
					face[0].vertex=v2;
					face[0].parent=v2;
					face[0].rule=k;
					face[0].x=0;

					//Find subCBGmap in he.
					set<vid> unused_v_set;
					unused_v_set.insert(v1);
					subCBGmap sg_map;
					sg_map.unused_v_set=&unused_v_set;
					set<subCBGmap>::iterator i_map=he->sgmap_set->find(sg_map);
					if (i_map==he->sgmap_set->end()) {
						sg_map.unused_v_set=new set<vid>(unused_v_set);
						sg_map.sg_set=new unordered_set<subCBG>;
						he->sgmap_set->insert(sg_map);

						i_map=he->sgmap_set->find(sg_map);
					}

					static bitset<32> edge_selection[1];
					edge_selection[0]=0;

					add_subCBG(i_map, face, 1, edge_selection, 1, NULL, 0, 0, NULL);
#ifdef _TRACE
					printf("\n");
#endif
#ifdef _STEINER_TREE_OPTIMIZATION
					}
#endif
				}
			}
		}
	}

	//Set he_set and v_he.
	for (int i=1; i<num_vertex; i++) {
		for (map<vid, hyperedge*>::iterator j=temp_he[i].begin(); j!=temp_he[i].end(); ++j) {
			he_set.insert(*(j->second));
			v_he[i]->insert(*(j->second));
			v_he[j->first]->insert(*(j->second));
			delete j->second;
		}
	}

	//Release memory.
	delete[] temp_he;

#if defined(_MONITOR) || defined(_MESSAGE)
	int num_remaining=num_vertex;
#endif
	for (int i=0; i<num_vertex; i++) {
		//Determine a vertex to remove.
		vid v=elimination_order[i];

		if (v_set.count(v)==0) {
			fprintf(stderr, "Error: Elimination Order is Wrong!");
			exit(1);
		}
		else {
			v_set.erase(v);
		}

#ifdef _TRACE
		printf("\nRemove: v%d (degree=%d)\nCombine: ", v, v_adj[v]->size());
		for (set<hyperedge>::iterator j=v_he[v]->begin(); j!=v_he[v]->end(); ++j) {
			printf("{");
			for (set<vid>::iterator k=j->v_set->begin(); k!=j->v_set->end(); ++k) {
				if (k!=j->v_set->begin()) printf(",");
				printf("v%d", *k);
			}
			printf("}");
		}
		printf("\n");
#else
#ifdef _MONITOR
		printf("\nRemove: v%d (%d/%d)(degree=%d)", v, num_remaining--, num_vertex, v_adj[v]->size());
#else
#ifdef _MESSAGE
		fprintf(stderr, "Remove: v%d (%d/%d)(degree=%d)                    \r", v, num_remaining--, num_vertex, v_adj[v]->size());
		fflush(stderr);
#endif
#endif
#endif

		//Constract a new hypeyedge he_new for {v}+v_adj[v].
		hyperedge he_new;
		he_new.sgmap_set=new set<subCBGmap>;
		he_new.v_set=new set<vid>;
		he_new.num_edge=0;
		he_new.edge=NULL;
#ifdef _STEINER_TREE_OPTIMIZATION
		he_new.num_terminal=0;
#endif
		int count=v_he[v]->size();
		for (set<hyperedge>::iterator j=v_he[v]->begin(); j!=v_he[v]->end(); ++j, count--) {
#ifdef _TRACE
			printf("<= {");
			for (set<vid>::iterator k=j->v_set->begin(); k!=j->v_set->end(); ++k) {
				if (k!=j->v_set->begin()) printf(",");
				printf("v%d", *k);
			}
			printf("}\n");
#endif
			hyperedge he;
			he.sgmap_set=j->sgmap_set;
			he.v_set=j->v_set;
			he.num_edge=j->num_edge;
			he.edge=j->edge;
			he.initial=j->initial;
#ifdef _STEINER_TREE_OPTIMIZATION
			he.num_terminal=j->num_terminal;
#endif

			//Erase the hyperedge j and all links to it.
			he_set.erase(*j);
			for (set<vid>::iterator k=j->v_set->begin(); k!=j->v_set->end(); ++k) {
				if (*k==v) continue;
				v_he[*k]->erase(*j);
			}

			if (count>1) {
#ifdef _TRACE
#else
#ifdef _MONITOR
				if (he_new.v_set->size()!=0) printf("(%d,%d)-", he.v_set->size(), he.sgmap_set->size());
#endif
#endif
				HE_combine(&he_new, &he, 0);
#ifdef _STEINER_TREE_OPTIMIZATION
				he_new.num_terminal=he_new.num_terminal+he.num_terminal;
#endif
#ifdef _TRACE
#else
#ifdef _MONITOR
				printf("(%d,%d)", he_new.v_set->size(), he_new.sgmap_set->size());
#endif
#endif
			}
			else {
#ifdef _TRACE
#else
#ifdef _MONITOR
				printf("(%d,%d)->", he.v_set->size(), he.sgmap_set->size());
#endif
#endif
				HE_combine(&he_new, &he, v);
#ifdef _STEINER_TREE_OPTIMIZATION
				he_new.num_terminal=he_new.num_terminal+he.num_terminal;
				if (vertex[v].weight!=0) he_new.num_terminal++;
#endif

				//Remove the vertex v from the hyperedge he_new.
				he_new.v_set->erase(v);
				he_new.initial=false;
#ifdef _TRACE
#else
#ifdef _MONITOR
				printf("(%d,%d)", he_new.v_set->size(), he_new.sgmap_set->size());
#endif
#endif
			}
		}
		v_he[v]->clear();
					
		//Add the hyperedge he_new to he_set.
		pair<set<hyperedge>::iterator, bool> r=he_set.insert(he_new);
		if (r.second) {
			//he_new could be newly added.
			for (set<vid>::iterator j=v_adj[v]->begin(); j!=v_adj[v]->end(); ++j) {
				v_he[*j]->insert(he_new);
			}
		}
		else {
#ifdef _TRACE
			printf("Merge:\n");
#endif
			//he_new needs to be combined to an existing hyperedge.
			hyperedge he;
			he.sgmap_set=r.first->sgmap_set;
			he.v_set=r.first->v_set;
			he.num_edge=r.first->num_edge;
			he.edge=r.first->edge;
			he.initial=r.first->initial;
#ifdef _STEINER_TREE_OPTIMIZATION
			he.num_terminal=r.first->num_terminal;
#endif

			he_set.erase(he_new);
			for (set<vid>::iterator j=v_adj[v]->begin(); j!=v_adj[v]->end(); ++j) {
				v_he[*j]->erase(he_new);
			}

#ifdef _TRACE
#else
#ifdef _MONITOR
			printf("(%d,%d)=>", he.v_set->size(), he.sgmap_set->size());
#endif
#endif
			HE_combine(&he_new, &he, 0);
#ifdef _STEINER_TREE_OPTIMIZATION
			he_new.num_terminal=he_new.num_terminal+he.num_terminal;
#endif
#ifdef _TRACE
#else
#ifdef _MONITOR
			printf("(%d,%d)", he_new.v_set->size(), he_new.sgmap_set->size());
#endif
#endif

			he_set.insert(he_new);
			for (set<vid>::iterator j=v_adj[v]->begin(); j!=v_adj[v]->end(); ++j) {
				v_he[*j]->insert(he_new);
			}
		}

		//Erase the vertex v, and renew the adjacency sets of the remaining vertexs.
		for (set<vid>::iterator j=v_adj[v]->begin(); j!=v_adj[v]->end(); ++j) {
			v_adj[*j]->erase(v);
			for (set<vid>::iterator k=v_adj[v]->begin(); k!=v_adj[v]->end(); ++k) {
				if (*j==*k) continue;
				v_adj[*j]->insert(*k);
			}
		}
	}

	delete[] elimination_order;

	*result_edge_num=0;
	*result_weight=(weight_type) 0.0;
	weight_type weight=0;

	//Obtain the result.
	if (accept) {
		for (set<hyperedge>::iterator i=he_set.begin(); i!=he_set.end(); ++i) {
			bitset<32> *edge_selection=NULL;
			for (set<subCBGmap>::iterator i_map=i->sgmap_set->begin(); i_map!=i->sgmap_set->end(); ++i_map) {
				for (unordered_set<subCBG>::iterator j=i_map->sg_set->begin(); j!=i_map->sg_set->end(); ++j) {
					if (edge_selection==NULL) {
						edge_selection=j->edge_selection;
						weight=j->weight;
					}
					else if (!mode.min && j->weight>weight || mode.min && j->weight<weight) {
						edge_selection=j->edge_selection;
						weight=j->weight;
					}
				}
			}
			if (edge_selection!=NULL) {
				for (eid j=0; j<i->num_edge; j++) {
					if (edge_selection[j/32].test(j%32)) {
						result_edge[*result_edge_num]=i->edge[j];
						*result_edge_num=*result_edge_num+1;
					}
				}
			}
		}
		sort(result_edge, result_edge+(*result_edge_num));
		*result_weight=weight;
	}

	//Release the adjacency sets.
	for (int i=1; i<=num_vertex; i++) {
		delete v_adj[i];
		delete v_he[i];
	}
	delete[] v_adj;
	delete[] v_he;

	//Release the hyperedges.
	for (set<hyperedge>::iterator i=he_set.begin(); i!=he_set.end(); ++i) {
		for (set<subCBGmap>::iterator i_map=i->sgmap_set->begin(); i_map!=i->sgmap_set->end(); ++i_map) {
			delete i_map->unused_v_set;
			delete i_map->sg_set;
		}
		delete i->sgmap_set;
		delete i->v_set;
		delete[] i->edge;
	}

#ifdef _MONITOR
	printf("\n\nSubgraphMax:%d\nSubgraphTotal:%d\n", subgraph_max, subgraph_total);
#else
#ifdef _MESSAGE
	fprintf(stderr, "\n");
#endif
#endif

	if (accept) return 1;
	else return 0;
}

//Supporting functions for loading an automaton
int state(char *s) {
	int i;
	
	for (i=0; i<size_state; i++) {
		if (strcmp(state_table[i], s)==0) {
			return i+1;
		}
	}
	return 0;
}

int sigma(char *s) {
	int i;
	
	for (i=0; i<size_sigma; i++) {
		if (strcmp(sigma_table[i], s)==0) {
			return i+1;
		}
	}
	return 0;
}

int delta(char *s) {
	int i;
	
	for (i=0; i<size_delta; i++) {
		if (strcmp(delta_table[i], s)==0) {
			return i+1;
		}
	}
	return 0;
}

//The main function for loading an automaton
int load_automaton(char *automaton_filename) {
	FILE *fin;
	int i, j, k;
	char s[160], na[160];

	rule[0].state_l=INITIAL_STATE;
	rule[0].sigma=0;
	rule[0].width=0;
	rule[0].width2=0;
	
	if (automaton_filename==NULL) {
		rule[1].state_l=INITIAL_STATE;
		rule[1].sigma=0;
		rule[1].width=0;
		rule[1].width2=1;
		rule[1].state_r[0]=INITIAL_STATE;
		rule[1].delta[0]=0;

		num_rule=1;
		return 1;
	}

	fin=fopen(automaton_filename, "r");
	if (fin==NULL) {
		fprintf(stderr, "Error: \"%s\" cannot be opened!", automaton_filename);
		exit(1);
	}
	
	fgets(s, 160, fin);
	i=0; j=0; k=0;
	while (s[i]!='\0') {
		if (s[i]==',' || s[i]=='\n') {
			state_table[j][k]='\0';
			i++; j++; k=0;
			continue;
		}
		state_table[j][k]=s[i];
		i++; k++;
	}
	size_state=j;
	
	fgets(s, 160, fin);
	i=0; j=0; k=0;
	while (s[i]!='\0') {
		if (s[i]==',' || s[i]=='\n') {
			sigma_table[j][k]='\0';
			i++; j++; k=0;
			continue;
		}
		sigma_table[j][k]=s[i];
		i++; k++;
	}
	size_sigma=j;
	
	fgets(s, 160, fin);
	i=0; j=0; k=0;
	while (s[i]!='\0') {
		if (s[i]==',' || s[i]=='\n') {
			delta_table[j][k]='\0';
			i++; j++; k=0;
			continue;
		}
		delta_table[j][k]=s[i];
		i++; k++;
	}
	size_delta=j;
	
	num_rule=0;
	while (fgets(s, 160, fin)!=NULL) {
		i=0; j=0;
		
		rule[num_rule+1].state_l=-1;
		while (s[i]!='\0') {
			if (s[i]=='(') {
				na[j]='\0';
				rule[num_rule+1].state_l=state(na);
				if (rule[num_rule+1].state_l==0) {
					fprintf(stderr, "Error: automatonに未登録の状態があります。");
					exit(1);
				}
				i++; j=0;
				break;
			}
			na[j]=s[i];
			i++; j++;
		}
		if (rule[num_rule+1].state_l==-1) {
			printf("ERROR_state_l(%d):%s\n", i, s);
			exit(1);
		}
		
		rule[num_rule+1].sigma=-1;
		while (s[i]!='\0') {
			if (s[i]=='(' || s[i]==')') {
				na[j]='\0';
				rule[num_rule+1].sigma=sigma(na);
				j=0;
				break;
			}
			na[j]=s[i];
			i++; j++;
		}
		if (rule[num_rule+1].sigma==-1) {
			printf("ERROR_sigma(%d):%s\n", i, s);
			exit(1);
		}
		
		k=0;
		rule[num_rule+1].width2=0;
		if (s[i]=='(') {
			i++;
			while (s[i]!='\0') {
				if (s[i]==',' || s[i]==')') {
					na[j]='\0';
					if (na[0]=='@') {
						rule[num_rule+1].delta[k]=ATMARK;
					} else if (na[0]=='*') {
						rule[num_rule+1].delta[k]=delta(&(na[1]));
						rule[num_rule+1].width2++;
					} else {
						rule[num_rule+1].delta[k]=delta(na);
					}
					if (s[i]==',') {
						i++; j=0; k++;
						continue;
					}
					else {
						i++; j=0; k++;
						break;
					}
				}
				na[j]=s[i];
				i++; j++;
			}
		}
		if (s[i]==')') i++;
		else {
			printf("ERROR1_close(%d):%s\n", i, s);
			exit(1);
		}
		rule[num_rule+1].width=k-rule[num_rule+1].width2;
		
		while (s[i]!='\0') {
			if (isspace(s[i])) {
				i++;
				continue;
			}
			if (strncmp(&s[i], "->", 2)==0) {
				i+=2;
				break;
			}
			else {
				printf("ERROR2_arrow(%d):%s\n", i, s);
				exit(1);
			}
		}
		
		while (s[i]!='\0') {
			if (isspace(s[i])) {
				i++;
				continue;
			}
			break;
		}
		
		while (s[i]!='\0') {
			if (s[i]=='(' || s[i]=='\n' || s[i]=='[') {
				na[j]='\0';
				if (rule[num_rule+1].sigma!=sigma(na)) {
					printf("ERROR3_sigma(%d):%s\n", i, s);
					exit(1);
				}
				j=0;
				break;
			}
			na[j]=s[i];
			i++; j++;
		}
		
		if (rule[num_rule+1].width+rule[num_rule+1].width2>0) {
			if (s[i]!='(') {
				printf("ERROR4_open(%d):%s\n", i, s);
				exit(1);
			}
			else i++;
		}
		
		for (k=0; k<rule[num_rule+1].width+rule[num_rule+1].width2; k++) {
			while (s[i]!='\0') {
				if (s[i]=='(') {
					na[j]='\0';
					rule[num_rule+1].state_r[k]=state(na);
					i++; j=0;
					break;
				}
				na[j]=s[i];
				i++; j++;
			}
			
			while (s[i]!='\0') {
				if (s[i]==')') {
					na[j]='\0';
					if (rule[num_rule+1].delta[k]!=delta(na) && !(rule[num_rule+1].delta[k]==ATMARK) || rule[num_rule+1].delta[k]==ATMARK && na[0]!='@') {
						printf("ERROR6_delta(%d):%s\n", i, s);
						exit(1);
					}
					i++; j=0;
					break;
				}
				na[j]=s[i];
				i++; j++;
			}
			
			if (k == rule[num_rule+1].width+rule[num_rule+1].width2-1) {
				if (s[i]!=')') {
					printf("ERROR7_close(%d):%s\n", i, s);
					exit(1);
				}
				else i++;
			}
			else {
				if (s[i]!=',') {
					printf("ERROR8_comma(%d):%s\n", i, s);
					exit(1);
				}
				else i++;
			}
		}
		
		while (s[i]!='\0') {
			if (isspace(s[i])) {
				i++;
				continue;
			}
			break;
		}

		if (s[i]=='[') {
			limited_rules[num_lr]=num_rule+1;
			i++;

			while (s[i]!='\0') {
				if (s[i]==',') {
					na[j]='\0';
					min_apply[num_lr]=atoi(na);
					i++; j=0;
					break;
				}
				na[j]=s[i];
				i++; j++;
			}

			while (s[i]!='\0') {
				if (s[i]==']') {
					na[j]='\0';
					max_apply[num_lr]=atoi(na);
					i++; j=0;
					break;
				}
				na[j]=s[i];
				i++; j++;
			}

			if (s[i]=='\0') {
				printf("ERROR10_apply(%d):%s\n", i, s);
				exit(1);
			}

			num_lr++;
		}
			
		while (s[i]!='\0') {
			if (isspace(s[i])) {
				i++;
				continue;
			}
			break;
		}

		if (s[i]!='\0') {
			printf("ERROR9_eol(%d):%s\n", i, s);
			exit(1);
		}
		
		num_rule++;
	}
	
	fclose(fin);
	
	return num_rule;
}
