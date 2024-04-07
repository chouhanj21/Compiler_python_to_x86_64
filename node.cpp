#include<bits/stdc++.h>
using namespace std;





class Node {
     static int nodecount;
     public:
     int count;
     string  type ="";
     string value;
     vector<string> tac;
     string addr;
     vector<Node*> childs;
     Node(const char * Value){
          count= nodecount++;
          value = Value;
     }
   
};

