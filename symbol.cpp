#include<bits/stdc++.h>
#include<map>
using namespace std;

struct Entry{
    string name;
    string type;
    string value;
    int lineno;
    Entry(string n,string t,string v,int ln):name(n),type(t),value(v),lineno(ln) {}
};
void printV(string name, vector<Entry*> vec){
    int n= vec.size();
    for(int i=0;i<n;i++){
        cout<<name <<"  "<<vec[i]->type<<"  "<<vec[i]->value<<"  "<<vec[i]->lineno<<endl;
    }
}

class symboltable{
public:
    vector<Entry*> symbols;
    unordered_map<string,Entry*> table;
};


class scope{
public:
    string name;
    int lineno;
    vector<scope*> childs;
    unordered_map<string,scope*> table;
    struct symboltable* smt;
    scope* parent ;
    scope(string n,int lin ): name(n),lineno(lin){
        smt=new symboltable();
    }
};

