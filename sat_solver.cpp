/*

SAT SOLVER

Authors :
Ayush Kumar

Created on 10/26/18

*/
#include <iostream>
#include <cstdlib>
#include <cmath>
#include <vector>
#include <fstream>
#include <cassert>
#include <string>
#include <sstream>
#include <ctime>
#include <set>
#include <list>

using namespace std;
typedef unsigned int uint;

#define tr(container, it) \
for(auto it = container.begin(); it != container.end(); it++)

int N_PROPS, N_CLAUSES, CNT;
vector<int> LITERALS, FREQ;
bool SAT = true;

clock_t time_p=clock();
void ayush194()
{
    time_p=clock()-time_p;
    cerr<<"Time Taken : "<<(float)(time_p)/CLOCKS_PER_SEC<<"\n";
}

inline void settrue(int x) {assert(abs(x) <= N_PROPS); LITERALS[abs(x)] = (x > 0 ? 1 : 0);}
inline void setfalse(int x) {assert(abs(x) <= N_PROPS); LITERALS[abs(x)] = (x > 0 ? 0 : 1);}
inline void unset(int x) {assert(abs(x) <= N_PROPS); LITERALS[abs(x)] = -1;}
inline bool checktrue(int x) {assert(abs(x) <= N_PROPS); return LITERALS[abs(x)] == (x > 0 ? 1 : 0);}
inline bool checkfalse(int x) {assert(abs(x) <= N_PROPS); return LITERALS[abs(x)] == (x > 0 ? 0 : 1);}
inline bool checkunset(int x) {assert(abs(x) <= N_PROPS); return LITERALS[abs(x)] == -1;}
inline int getvalue(int x) {assert(abs(x) <= N_PROPS); return LITERALS[abs(x)];}

bool cmpclause(pair<set<int>, bool>& x, pair<set<int>, bool>& y) {
	set<int>& a = x.first, b = y.first;
	int freq_a = 0, freq_b = 0;
	for(set<int>::iterator it = a.begin(); it != a.end(); it++) {
		freq_a += FREQ[abs(*it)];
	}
	for(set<int>::iterator it = b.begin(); it != b.end(); it++) {
		freq_b += FREQ[abs(*it)];
	}
	return freq_a > freq_b;
}

int mysize(vector<pair<set<int>, bool> >& a, int sz) {
	for(int i = sz-1; i >= 0; i--) {
		if (a[i].second) {return i+1;}
	}
	return 0;
}

class Data {
public:
	Data() {}
	//first int is the index in LITERALS array, and second int is the value
	vector<pair<int, int> > literals;
	//stores index of removed clause
	vector<int> removedcl;
	//first int is index, second is the literal removed
	vector<pair<int, int> > shrunkcl;
	void backtrack(vector<pair<set<int>, bool> >& f) {
		for(auto& x : literals) {
			LITERALS[x.first] = x.second;
		}
		for(int x : removedcl) {
			f[x].second = true;
		}
		for(auto& x : shrunkcl) {
			f[x.first].first.insert(x.second);
		}
	}
};

bool solveSAT(vector<pair<set<int>, bool> >& f, int sz) {
	//counts number of recursive calls to this function
	CNT++;
	//cout << CNT << endl;
/*
	auto test1 = f;
	auto test2 = LITERALS;
*/
	//uses Semantic Tableaux as a decision procedure for solving the SAT problem
	if (sz == 0) {return true;}
	//f[sz-1] should be the last element of the vector such that f[sz-1].second is true
/*
	assert(sz == mysize(f, f.size()));
	assert(f[sz-1].second);
	for(uint i = 0; i < f.size(); i++) {
		//all sets should have size > 0 
		assert(f[i].first.size() > 0);
	}
*/
	Data bt;
	bool unitcl = true;
	while (unitcl) {
		//iterate and find all unit clauses and set the literals to true
		for(uint i = 0; i < sz; i++) {
			if (!f[i].second) {continue;}
//			assert(f[i].first.size() > 0);
			if (f[i].first.size() == 1) {
				//unit clause
				int x = *(f[i].first.begin());
				if (checkfalse(x)) {
					//contradictory literal found
					bt.backtrack(f);
	
//					assert(test1 == f); assert(test2 == LITERALS);

					return false;
				}
				if (checkunset(x)) {
					//store in backtrack
					bt.literals.push_back(make_pair(abs(x), getvalue(x)));
					settrue(x);
				}
				bt.removedcl.push_back(i);
				f[i].second = false;
				if (i == sz - 1) {sz = mysize(f, sz);}
			}
		}
		if (sz == 0) {return true;}
		unitcl = false;
		//Based on the value of literals, remove/shrink some clauses
		bool flag = true;
		for(uint i = 0; i < sz; i++) {
			if (!f[i].second) {continue;}
			vector<int> to_remove;
			//this clause will either be fully removed or shrunk
			bool remove_flag = false;
			tr(f[i].first, it) {
				if (checktrue(*it)) {
					//remove this clause;
					remove_flag = true; break;
				} else if (checkfalse(*it)) {
					//shrink this clause
					to_remove.push_back(*it);
				}
			}
			if (remove_flag) {
				f[i].second = false;
				if (i == sz - 1) {sz = mysize(f, sz);}
				//store in backtrack
				bt.removedcl.push_back(i);
			} else {
				for(uint j = 0; j < to_remove.size(); j++) {
					f[i].first.erase(to_remove[j]);
					//store in backtrack
					bt.shrunkcl.push_back(make_pair(i, to_remove[j]));
				}
				//note that this clause may now have become a unit or even a 0 clause
				if (f[i].first.size() == 0) {
					//this clause cannot become true
					flag = false; break;
				}
				if (f[i].first.size() == 1) {unitcl = true;}
			}
		}
		if (!flag) {
			bt.backtrack(f);

//			assert(test1 == f); assert(test2 == LITERALS);

			return false;
		}
		if (sz == 0) {return true;}
		//due to shrinking some clauses may have again become unit clauses
	}	
/*
	assert(sz == mysize(f, f.size()));
	for(uint i = 0; i < sz; i++) {
		assert(f[i].first.size() > 0);
		if(!f[i].second) {continue;}
		assert(f[i].first.size() > 1);
		tr(f[i].first, it) {
			//all literals must be unset
			assert(checkunset(*it));
		}
	}
*/
	//note that after all the above operations, all the literals
	//left in the clauses are unset. Also there are no unit clauses present
	//also note that the size cannot be 0
	//also it is guaranteed that f[sz-1].second is true
/*
	assert(sz != 0);
	assert(f[sz-1].second);
*/
	set<int>& last = f[sz-1].first;
	int x = *(last.begin());

	//either x should be set T or F. Two branches of the tree
	//T
//	assert(checkunset(x));
	bt.literals.push_back(make_pair(abs(x), getvalue(x)));

	settrue(x);
	f[sz-1].second = false;
	bt.removedcl.push_back(sz-1);
	sz = mysize(f, sz);

	bool flag = solveSAT(f, sz);
	if (flag) {return true;}
	
	//1st branch returned false, partial backtrack
	sz = bt.removedcl.back() + 1;
	bt.removedcl.pop_back();
//	assert(!f[sz-1].second);
	f[sz-1].second = true;

	//investigate the other branch
	//F
	setfalse(x);
	f[sz-1].first.erase(x);
	bt.shrunkcl.push_back(make_pair(sz-1, x));

	flag = solveSAT(f, sz);
	if (flag) {return true;}
	bt.backtrack(f);
	
//	assert(test1 == f); assert(test2 == LITERALS);

	return false;
}

int main(int argc, char* argv[]) {
	if (argc != 3) {
		cout << "Usage : ./a.out filename_in filename_out" << endl;
		return 0;
	}
	string filename_in = argv[1];
	string filename_out = argv[2];
	//take input from file in cnf form
	ifstream sat_file;
	sat_file.exceptions(std::ios::failbit);
	try {sat_file.open(filename_in);}
	catch (const std::ios_base::failure& e) {
		cout << "Unable to open file!" << endl;
		return 0;		
	}
	//there is another way out using vector<pair<set<int>, flag> >, when an element
	//is to be erased, simply set the flag to be false. During iteration, skip false flag elements
	//During backtracking simply set the flag to be on
	vector<pair<set<int>, bool> > clauses;
	bool unitcl = false;
	while (true) {
		string line;
		getline(sat_file, line, '\n');
		if (line.empty()) {break;}
		stringstream ss(line);
		string word_1; ss >> word_1;
		if (word_1 == "c") {
			//ignore comment
			continue;
		} else if (word_1 == "p") {
			string word_2, word_3, word_4;
			ss >> word_2 >> word_3 >> word_4;
			try {
				if (word_2 != "cnf") {throw 20;}
				N_PROPS = stoi(word_3);
				N_CLAUSES = stoi(word_4);
			}
			catch (const std::invalid_argument& e) {
				cout << "Input file not in DIMACS representation!\nNumber of Propositions/Clauses is missing!" << endl;
				return 0;
			} catch (int e) {
				if (e == 20) {
					cout << "Input file not in DIMACS representation!\n'cnf' keyword is missing!" << endl;
					return 0;
				}
			}
			LITERALS.resize(N_PROPS+1, -1);
			FREQ.resize(N_PROPS+1, 0);
			//fill(LITERALS.begin(), LITERALS.end(), -1);
		} else if (!word_1.empty() && word_1 != "0") {
			//this line must be a clause or a literal;
			set<int> tmp;
			//vector<int> tmp;
			try {
				tmp.insert(stoi(word_1));
				while(true) {
					string word; ss >> word;
					if (word == "0" || word.empty()) {break;}
					int num = stoi(word);
					tmp.insert(num);
					FREQ[abs(num)]++;
				}
			} catch (const std::invalid_argument& e) {
				cout << "Input file not in DIMACS representation!\nError in Clause!";
			}
			if (tmp.size() == 1) {unitcl = true;}
			clauses.push_back(make_pair(tmp, true));
			/*
			if (tmp.size() == 1) {
				int top = *(tmp.begin());
				if (checkfalse(top)) {
					SAT = false;
					break;
				} else {settrue(top);}
			}
			else {clauses.push_back(make_pair(tmp, true));}
			*/
		}
	}

	while (unitcl) {
		for(uint i = 0; i < clauses.size(); i++) {
			if (clauses[i].first.size() == 1) {
				//unit clause
				int top = *(clauses[i].first.begin());
				if (checkfalse(top)) {SAT = false; break;}
				settrue(top);
				clauses.erase(clauses.begin() + i);
				i--;
			}
		}
		if (!SAT) {break;}
		unitcl = false;
		for(uint i = 0; i < clauses.size(); i++) {
			vector<int> to_remove;
			bool break_flag = false;
			tr(clauses[i].first, it2) {
				if (checktrue(*it2)) {
					//this clause is already true, no need for this clause
					clauses.erase(clauses.begin() + i);
					i--; break_flag = true; break;
				} else if (checkfalse(*it2)) {
					//this literal doesn't make the clause true, so shrink this clause
					to_remove.push_back(*it2);
				}
			}
			if (break_flag) {continue;}
			for(uint j = 0; j < to_remove.size(); j++) {
				clauses[i].first.erase(to_remove[j]);
			}
			if (clauses[i].first.size() == 1) {unitcl = true;}
			if (clauses[i].first.size() == 0) {SAT = false; break;}
		} 
	}

	FILE* satsol_file = fopen(filename_out.c_str(), "w");
	if (!SAT) {
		cout << "UNSAT" << endl;
		fprintf(satsol_file, "UNSAT");
		return 0;
	}
/*	
	tr(clauses, it1) {
		assert(it1->first.size() > 1);
		tr(it1->first, it2) {
			assert(getvalue(*it2) == -1);
		}
	}
*/	
	//heuristic 1
	//sort the clauses by their frequency value
	//sort(clauses.begin(), clauses.end(), cmpclause);
	
	SAT = solveSAT(clauses, clauses.size());
	if (!SAT) {
		cout << "UNSAT" << endl;
		fprintf(satsol_file, "UNSAT");
	}
	else {
		cout << "SAT" << endl;
		fprintf(satsol_file, "SAT\n");
		for(uint i = 1; i < LITERALS.size(); i++) {
			int val = LITERALS[i] == 0 ? -i : i;
			cout << val << ' ';
			fprintf(satsol_file, "%d ", val);
		}
		cout << 0 << endl;
		fprintf(satsol_file, "0\n");
	}
	fclose(satsol_file);
	cout << "Steps Required : " << CNT << endl;
	ayush194();
	return 0;
}