%{  
    #include<bits/stdc++.h>
    #include<fstream>
    using namespace std;
    #include "node.cpp"
    #include "symbol.cpp"
    #define YYDEBUG 1

    int yylex (void);
    void yyerror (const char *s);
    extern stack<int> indent;
    int node_count=0;
    extern char* yytext;
    extern int current_indent;
    extern int yylineno;
    int Node::nodecount=0;
    struct Node* head=NULL;
    void printtable(struct scope* global_scope);
    struct scope* global_scope=new scope(".head",0);


    // void print(struct Node* head);
    int tnum=0;
    string addrup(){
        string id=  "t"+to_string(tnum);
        tnum++;
        return id;
    }
    int labelnum=0;
    string newlabel(){
        string id=  "l"+to_string(labelnum);
        labelnum++;
        return id;
    }
    void print3ac(  Node* a){
        ofstream file("threeac.txt");
        for(auto x:a->tac){
            file<<"        "<<x<<endl;
        }
        file.close();
    }
    
    void print_string(ofstream& dotfile, string s){
        int len = s.length();
        for(int i=0; i<len; i++){
            if(s[i] == '\"'){
                dotfile << "\\\"";
            }
            else if(s[i] == '\''){
                dotfile << "\\\'";
            }
            else if(s[i] == '\\'){
                dotfile<<"\\\\";
            }
            else{
                dotfile<<s[i];
            }
        }
        return;
    }
    void printnodes(ofstream& dotfile, struct Node* head) {
        if(head->type!=""){
            if(head->type == "STRING"){
                dotfile << "node" << head->count << " [label=\"" << "String" <<" ( "; 
                print_string(dotfile, head->value);
                dotfile <<")\"]" << endl;
            }
            else{
                dotfile << "node" << head->count << " [label=\"" << head->type <<" ( " << head->value<<" ) \"]" << endl;
            }
        }
        else{
            dotfile << "node" << head->count << " [label=\"" << head->value<<"\"]" << endl;
        }

        for (auto child : head->childs) {
            printnodes(dotfile, child);
        }
        return ;
    }

    void printedges(ofstream& dotfile, struct Node* head) {

        for (auto child : head->childs) {
            dotfile<<"node"<<head->count<<"->"<<"node"<<child->count<<endl;
            printedges(dotfile, child);
        }
        return ;
    }


%}
%union{
    struct Node * node;

}

%token <node>NEWLINE NAME NUMBER STRING INDENT DEDENT
%token <node>ADD_ASSIGN "+="
%token <node>SUB_ASSIGN "-="
%token <node>MUL_ASSIGN "*="

%token <node>XOR_ASSIGN "^="
%token <node>LEFT_ASSIGN "<<="
%token <node>RIGHT_ASSIGN ">>="
%token <node>POW_ASSIGN "**="

%token <node>PASS "pass"
%token <node>DEF "def"

%token <node>ARROW "->"
%token <node>BREAK "break"
%token <node>CONTINUE "continue"
%token <node>RETURN "return"
%token <node>IF "if"
%token <node>WHILE "while"
%token <node>IN "in"
%token <node>FOR "for"

%token <node>CLASS "class"
%token <node>NONE "None"
%token <node>TRUE "True"
%token <node>FALSE "False"
%token <node>ELIF "elif"

%token <node>ELSE "else"

%token <node>DIV_ASSIGN "/="
%token <node>REM_ASSIGN "%="
%token <node>AND_ASSIGN "&="
%token <node>OR_ASSIGN "|="
%token <node>OR "or"
%token <node>AND "and"
%token <node>NOT "not"

%token <node>LEFT_OP "<<"
%token <node>RIGHT_OP ">>"
%token <node>IS_EQUAL "=="
%token <node>NOT_EQUAL "!="
%token <node>GEQ ">="
%token <node>LEQ "<="
%token <node>NEQ "<>"
%token <node>COLON_ASSIGN ":="
%token <node>CONCAT "//"
%token <node>POW "**"
%token <node>DOTS "..."
%token <node> ',' '(' ')' ':' '.' '[' ']' '~' '-' '+' '%' '/' '*' '&' '^' '|' '>' '<' '='

%start input

%type<node>  stmts stmt simple_stmt compound_stmt expr_stmt pass_stmt flow_stmt
%type<node> expr testlist test_type
%type<node> augassign comma_argument_star 
%type<node>  test 

%type<node> break_stmt continue_stmt return_stmt 
%type<node> if_stmt while_stmt for_stmt classdef
%type<node> elif_test_colon_suite_star suite  or_test 
%type<node> and_test  not_test comparison 
%type<node> comp_op shift_expr 
%type<node> arith_expr  term 
%type<node> factor add_or_sub_or_tilde power atom_expr atom trailer_star
%type<node> trailer 
%type<node> testlist_comp test_or comma_test_or_star
%type<node>  small_stmt left_or_right
%type<node> parameters typedargslist tfpdef arglist 
%type<node>  xor_expr funcdef argument and_expr string_star mul_or_div_or_rem_or_concat add_or_sub



%%

input: stmts {head =$1;}| 
stmts: stmts stmt {
    $$=new Node("stmts");
    $$->childs.push_back($1);
    $$->childs.push_back($2);
    for(auto x:$1->tac) $$->tac.push_back(x);
    for(auto x:$2->tac) $$->tac.push_back(x);
}
    | stmt 
stmt: simple_stmt 
    | compound_stmt
    |NEWLINE
simple_stmt: small_stmt ';' simple_stmt {$$=new Node(";");
    $$->childs.push_back($1);
    $$->childs.push_back($3);
    for(auto x:$1->tac) $$->tac.push_back(x);
    for(auto x:$3->tac) $$->tac.push_back(x);
    }
    | small_stmt ';' NEWLINE {
    $$=$1;
    }
    | small_stmt NEWLINE {
    $$=$1;
    }

small_stmt: expr_stmt
    | pass_stmt 
    | flow_stmt 
/* global_scope->smt->symbols.push_back(new Entry($1->value,$2->type,$2->value,yylineno-1)); */
expr_stmt: NAME ':'test_type{
    $$=new Node("expr_stmt");
    $$->childs.push_back($1);
    $$->childs.push_back($3);
    for(auto x:$3->tac) $$->tac.push_back(x);
    $$->tac.push_back( "push param "+$1->value+" = "+$3->value+"()" );
    global_scope->smt->symbols.push_back(new Entry($1->value,$3->type,$3->value,yylineno-1));
    }
    | testlist
|NAME ':' test_type '='test{
    $$= new Node("expr_smt");
    $$->childs.push_back($1);
    $$->childs.push_back($5);
    for(auto x:$5->tac) $$->tac.push_back(x);
    $$->tac.push_back($1->value+" = "+$5->addr);
    global_scope->smt->symbols.push_back(new Entry($1->value,$3->type,$3->value,yylineno-1));
}
|test augassign test{
   
    $$=new Node("augassign");
    $$->childs.push_back($1);
    $$->childs.push_back($3);
    for(auto x:$1->tac) $$->tac.push_back(x);
    for(auto x:$2->tac) $$->tac.push_back(x);
    for(auto x:$3->tac) $$->tac.push_back(x);
    $$->tac.push_back($1->value+" = "+$1->value+$2->value+$3->addr);

}
|test '=' test {
    global_scope->smt->symbols.push_back(new Entry($1->value,$1->type,$3->value,yylineno-1));
    for(auto x:$1->tac) $$->tac.push_back(x);
    for(auto x:$3->tac) $$->tac.push_back(x);
    $$->tac.push_back($1->value+" = "+$3->addr);

}

testlist: test ',' testlist{
    $$=$2;
    $$->childs.push_back($1);
    $$->childs.push_back($3);
    for(auto x:$1->tac) $$->tac.push_back(x);
    for(auto x:$3->tac) $$->tac.push_back(x);
}
    | test ','{$$=$1;}
    | test  {$$=$1;}
test_type: NAME | NONE | NAME '[' NAME ']' 
augassign: "+=" {$$->value="+";}
    | "-="      {$$->value="-";}
    | "*="      {$$->value="*";}
    | "/="      {$$->value="/";}
    | "%="      {$$->value="%";}
    | "&="      {$$->value="&";}
    | "|="      {$$->value="|";}
    | "^="      {$$->value="^";}
    |"<<="      {$$->value="<<";}
    | ">>="     {$$->value=">>";}
    | "**="     {$$->value="**";}

pass_stmt: "pass"
flow_stmt: break_stmt
    | continue_stmt
    | return_stmt 
break_stmt: "break"
continue_stmt: "continue"
return_stmt: "return" testlist {
    $$=new Node("return");
    $$->childs.push_back($2);
    for(auto x:$2->tac) $$->tac.push_back(x);
    $$->tac.push_back("return " +$2->value);
}
    | "return" {$$->tac.push_back("return");}
compound_stmt:funcdef
    |if_stmt 
    | while_stmt 
    | for_stmt 
    | classdef  
if_stmt: "if" test ':' suite elif_test_colon_suite_star "else" ':' suite{
    $$=new Node("if_block");
    $$->childs.push_back($2);
    $$->childs.push_back($4);
    $$->childs.push_back($5);
    $$->childs.push_back($8);
    string l1=newlabel();
    string l2=newlabel();
    for(auto x:$2->tac) $$->tac.push_back(x);
    $$->tac.push_back("if "+$2->addr+" goto "+l1);
    $$->tac.push_back("goto "+l2);
    $$->tac.push_back(l1+": ");
    for(auto x:$4->tac) $$->tac.push_back(x);
    for(auto x:$5->tac) $$->tac.push_back(x);
    $$->tac.push_back(l2+": ");
    for(auto x:$8->tac) $$->tac.push_back(x);
}
    | "if" test ':' suite elif_test_colon_suite_star {
            
    $$=new Node("if_block");
    $$->childs.push_back($2);
    $$->childs.push_back($4);
    string l1=newlabel();
    string l2=newlabel();
    for(auto x:$2->tac) $$->tac.push_back(x);
    $$->tac.push_back("if "+$2->addr+" goto "+l1);
    $$->tac.push_back("goto "+l2);
    $$->tac.push_back(l1+": ");
    for(auto x:$4->tac) $$->tac.push_back(x);
   
    $$->tac.push_back(l2+": ");
    for(auto x:$5->tac) $$->tac.push_back(x);
    
    }
    | "if" test ':' suite "else" ':' suite{
    $$=new Node("if_block");
    $$->childs.push_back($2);
    $$->childs.push_back($4);
    $$->childs.push_back($7);
    string l1=newlabel();
    string l2=newlabel();
    for(auto x:$2->tac) $$->tac.push_back(x);
    $$->tac.push_back("if "+ $2->addr+" goto "+l1);
    $$->tac.push_back("goto " + l2);
    $$->tac.push_back(l1 + ": ");
    for(auto x:$4->tac) $$->tac.push_back(x);
    $$->tac.push_back(l2 + ": ");
    for(auto x:$7->tac) $$->tac.push_back(x);
    }
    | "if" test ':' suite{
    $$=new Node("if_block");
    $$->childs.push_back($2);
    $$->childs.push_back($4);
    string l1=newlabel();
    string l2=newlabel();
    for(auto x:$2->tac) $$->tac.push_back(x);
    $$->tac.push_back("if "+$2->addr+" goto "+l1);
    $$->tac.push_back("goto "+l2);
    $$->tac.push_back(l1+": ");
    for(auto x:$4->tac) $$->tac.push_back(x);
    




    
    }
while_stmt: "while" test ':' suite{
        $$=new Node("while_block");
        $$->childs.push_back($1);
        $$->childs.push_back($3);
        string l1=newlabel();
        string l2=newlabel();
        for(auto x:$2->tac) $$->tac.push_back(x);
        $$->tac.push_back("while "+$2->addr+" goto "+l1);
        $$->tac.push_back("goto "+l2);
        $$->tac.push_back(l1+": ");
        for(auto x:$4->tac) $$->tac.push_back(x);
        
    }
for_stmt: "for" NAME "in" NAME '(' atom ')' ':' suite{
        $$=new Node("for_block");
        $$->childs.push_back($2);
        $$->childs.push_back($4);
        $$->childs.push_back($6);
        string l1=newlabel();
        string l2=newlabel();
        string t1=addrup();
        $$->tac.push_back($2->value+" =  0");
        for(auto x:$7->tac) $$->tac.push_back(x);
        $$->tac.push_back("if " + $2->value+" <= "+$6->value+" goto "+l1);
        $$->tac.push_back("goto "+l2);
        $$->tac.push_back(l1+": ");
        for(auto x:$9->tac) $$->tac.push_back(x);
        $$->tac.push_back($2->value+" = "+$2->value+" + 1");
        
    }
    |"for" NAME "in" NAME '(' atom ',' atom ')' ':' suite{
        $$=new Node("for_block");
        $$->childs.push_back($2);
        $$->childs.push_back($4);
        $$->childs.push_back($6);
        string l1=newlabel();
        string l2=newlabel();
        string t1=addrup();
        $$->tac.push_back($2->value+" = "+$6->value);
        for(auto x:$7->tac) $$->tac.push_back(x);
        $$->tac.push_back("if " + $2->value+" <= "+$8->value+" goto "+l1);
        $$->tac.push_back("goto "+l2);
        $$->tac.push_back(l1+": ");
        for(auto x:$11->tac) $$->tac.push_back(x);
        $$->tac.push_back($2->value+" = "+$2->value+" + 1");
        

    
    }

elif_test_colon_suite_star: elif_test_colon_suite_star "elif" test ':' suite {
        $$=new Node("elif_block");
        $$->childs.push_back($1);
        $$->childs.push_back($3);
        $$->childs.push_back($5);
        string l1=newlabel();
        string l2=newlabel();
        for(auto x:$1->tac) $$->tac.push_back(x);
        for(auto x:$3->tac) $$->tac.push_back(x);
        $$->tac.push_back("else if "+$3->addr+" goto "+l1);
        $$->tac.push_back("goto "+l2);
        $$->tac.push_back(l1+": ");
        for(auto x:$5->tac) $$->tac.push_back(x);
    }

    | "elif" test ':' suite{
        $$=new Node("elif_block");
        $$->childs.push_back($2);
        $$->childs.push_back($4);
        string l1=newlabel();
        string l2=newlabel();
        for(auto x:$2->tac) $$->tac.push_back(x);
        $$->tac.push_back("else if "+$2->addr+" goto "+l1);
        $$->tac.push_back("goto "+l2);
        $$->tac.push_back(l1+": ");
        for(auto x:$4->tac) $$->tac.push_back(x);
        
        
    }
suite: simple_stmt 
    | NEWLINE INDENT stmts DEDENT{$$=$3;}
test: or_test "if" or_test "else" test{
    $$=new Node("test");
    $$->childs.push_back($1);
    $$->childs.push_back($3);
    $$->childs.push_back($5);
}
    | or_test 
or_test: or_test "or" and_test {
    $$=new Node("or_test");
    $$->childs.push_back($1);
    $$->childs.push_back($2);
    for(auto x:$1->tac) $$->tac.push_back(x);
    for(auto x:$3->tac) $$->tac.push_back(x);
    $$->addr=addrup();
    $$->tac.push_back($$->addr+" = "+$1->addr + " "+$2->value+ " "+$3->addr );
}
    | and_test





and_test: and_test "and" not_test{
    $$=new Node("and_test");
    $$->childs.push_back($1);
    $$->childs.push_back($2);
    for(auto x:$1->tac) $$->tac.push_back(x);
    for(auto x:$3->tac) $$->tac.push_back(x);
    $$->addr=addrup();
    $$->tac.push_back($$->addr+" = "+$1->addr + " "+$2->value+ " "+$3->addr );
    
}
    | not_test{
        $$=$1;
    }





not_test: "not" not_test {$$=new Node("not");
    $$->childs.push_back($2);
    for(auto x:$2->tac) $$->tac.push_back(x);
    $$->addr=addrup();
    $$->tac.push_back($$->addr+" = "+$1->value+ " "+$2->addr );

}
    | comparison{
        $$=$1;
    }



comparison: expr comp_op  comparison{
    $$=new Node("comparison");
    $$->childs.push_back($1);
    $$->childs.push_back($2);
    for(auto x:$1->tac) $$->tac.push_back(x);
    for(auto x:$3->tac) $$->tac.push_back(x);
    $$->addr=addrup();
    $$->tac.push_back($$->addr+" = "+$1->addr + $2->value + $3->addr );
}
    | expr

comp_op: '<'
    |'>'
    |"=="
    |">="
    |"<="
    |"<>"
    |"!="


expr: xor_expr '|' expr{$$=new Node("expr");
            $$->childs.push_back($1);
            $$->childs.push_back($2);
            for(auto x:$1->tac) $$->tac.push_back(x);
            for(auto x:$3->tac) $$->tac.push_back(x);
            $$->addr=addrup();
            $$->tac.push_back($$->addr+" = "+$1->addr + $2->value + $3->addr );
}
    | xor_expr
xor_expr: and_expr '^' xor_expr{
    $$=new Node("xor_expr");
    $$->childs.push_back($1);
    $$->childs.push_back($2);
    for(auto x:$1->tac) $$->tac.push_back(x);
    for(auto x:$3->tac) $$->tac.push_back(x);
    $$->addr=addrup();
    $$->tac.push_back($$->addr+" = "+$1->addr + $2->value + $3->addr );
                

}
    | and_expr
and_expr: shift_expr  '&' and_expr {
    $$=$2;
    $$->childs.push_back($1);
    $$->childs.push_back($2);
    for(auto x:$1->tac) $$->tac.push_back(x);
    for(auto x:$3->tac) $$->tac.push_back(x);
    $$->addr=addrup();
    $$->tac.push_back($$->addr+" = "+$1->addr + $2->value + $3->addr );
}
    | shift_expr
shift_expr: arith_expr left_or_right shift_expr{
    $$=new Node("shift_expr");
    $$->childs.push_back($1);
    $$->childs.push_back($2);
    for(auto x:$1->tac) $$->tac.push_back(x);
    for(auto x:$3->tac) $$->tac.push_back(x);
    $$->addr=addrup();
    $$->tac.push_back($$->addr+" = "+$1->addr + $2->value + $3->addr );
}
    | arith_expr
left_or_right:"<<" 
    | ">>"
arith_expr: arith_expr add_or_sub term{$$=new Node("arith_expr");
                                        $$=$2;
                                        $$->childs.push_back($1);
                                        $$->childs.push_back($3);
                                        for(auto x:$1->tac) $$->tac.push_back(x);
                                        for(auto x:$3->tac) $$->tac.push_back(x);
                                        $$->addr=addrup();
                                        $$->tac.push_back($$->addr+" = "+$1->addr + $2->value + $3->addr );
            }
    | term

add_or_sub:'+'
    |'-'
term: term mul_or_div_or_rem_or_concat factor{
    $$=new Node("term");
    $$->childs.push_back($1);
    $$->childs.push_back($2);
    for(auto x:$1->tac) $$->tac.push_back(x);
    for(auto x:$3->tac) $$->tac.push_back(x);
    $$->addr=addrup();
    $$->tac.push_back($$->addr+" = "+$1->addr + $2->value + $3->addr );
}
    | factor

mul_or_div_or_rem_or_concat:'*'
    |'/'
    |'%'
    |"//"
factor: add_or_sub_or_tilde factor {
    $$=new Node("factor");
    $$->childs.push_back($1);
    $$->childs.push_back($2);
    for(auto x:$1->tac) $$->tac.push_back(x);
    for(auto x:$2->tac) $$->tac.push_back(x);
    $$->addr=addrup();
    $$->tac.push_back($$->addr+" = "+$1->value + $2->addr );
}
    | power
add_or_sub_or_tilde:'+'
    |'-'
    |'~'
power: atom_expr "**" factor{
    $$=new Node("**");
    $$->childs.push_back($1);
    $$->childs.push_back($3);
    for(auto x:$1->tac) $$->tac.push_back(x);
    for(auto x:$3->tac) $$->tac.push_back(x);
    $$->addr=addrup();
    $$->tac.push_back($$->addr+" = "+$1->addr + $2->value + $3->addr );
}
    | atom_expr{
        $$=$1;
    }
atom_expr: atom trailer_star{
    $$=new Node("atom_expr");
    $$->childs.push_back($1);
    $$->childs.push_back($2);
    for(auto x:$1->tac) $$->tac.push_back(x);
    for(auto x:$2->tac) $$->tac.push_back(x);
}
    | atom{$$=$1;}
trailer_star: trailer_star trailer{
    $$=new Node("trailer_star");
    $$->childs.push_back($1);
    $$->childs.push_back($2);
    for(auto x:$1->tac) $$->tac.push_back(x);
    for(auto x:$2->tac) $$->tac.push_back(x);
}
    | trailer{$$=$1;}
atom: '(' testlist_comp ')'{$$=$2;}
    | '[' testlist_comp ']'{$$=$2;}
    | '(' ')'{$$=new Node("()");}
    | '[' ']'{$$=new Node("[]");}
    | NAME{$$->addr=$1->value;}
    | NUMBER{
        $$->addr = addrup();
        $$->tac.push_back($$->addr + " = " + $1->value);

    }
    | string_star
    | "..."
    | "None"
    | "True"
    | "False"
string_star: string_star STRING{$$=$1;}
    | STRING
testlist_comp: test_or comma_test_or_star ','{
    $$=new Node(",");
    $$->childs.push_back($1);
    $$->childs.push_back($2);
}
    | test_or comma_test_or_star{
        $$=new Node("testlist_comp");
        $$->childs.push_back($1);
        $$->childs.push_back($2);
    }
    | test_or ','{$$=$1;}
    | test_or 
comma_test_or_star: comma_test_or_star ',' test_or{
    $$=new Node(",");
    $$->childs.push_back($1);
    $$->childs.push_back($3);
    for(auto x:$1->tac) $$->tac.push_back(x);
    for(auto x:$3->tac) $$->tac.push_back(x);
    $$->addr=addrup();
    $$->tac.push_back($$->addr+" = "+$1->addr + $2->value + $3->addr );
}
    | ',' test_or {$$=$2;}
test_or:test
trailer: '(' arglist ')' {$$=$2;}
    | '(' ')'
    | '[' test ']'{$$=$2;}
    | '.' NAME 



funcdef: "def" NAME parameters "->" test ':' {struct scope* temp=new scope($2->value,yylineno);
                                                temp->parent=global_scope;
                                                global_scope->childs.push_back(temp);
                                                global_scope=temp;
                                             } suite {
    $$=new Node("funcdef");
    $$->childs.push_back($2);
    $$->childs.push_back($3);
    $$->childs.push_back($5);
    $$->childs.push_back($8);
    // mytable.insert($2->value,$5->value,$5->type,yylineno-1);
    global_scope =global_scope->parent;
    $$->tac.push_back($2->value+":");
    $$->tac.push_back("beginfunc");
    for(auto x:$3->tac) $$->tac.push_back(x);
    for(auto x:$5->tac) $$->tac.push_back(x);
    for(auto x:$8->tac) $$->tac.push_back(x);
    $$->tac.push_back("endfunc");


}

parameters: '(' typedargslist ')' {
    $$=new Node("parameters");
    $$->childs.push_back($2);                          
    for(auto x:$2->tac) $$->tac.push_back(x);                                                            
}
    | '(' ')' {
    $$=new Node("()");
    }
typedargslist: tfpdef ',' typedargslist {
    $$=new Node(",");
    $$->childs.push_back($1);
    $$->childs.push_back($3);
    for(auto x:$1->tac) $$->tac.push_back(x);
    for(auto x:$3->tac) $$->tac.push_back(x);

}

    | tfpdef
tfpdef: NAME ':' test_type {
    $$=new Node("tfpdef");
    $$->childs.push_back($1);
    $$->childs.push_back($3);
    global_scope->smt->symbols.push_back(new Entry($1->value,$3->type,$3->value,yylineno-1));
    for(auto x:$3->tac) $$->tac.push_back(x);
    $$->tac.push_back($1->value+" =  popparam");
    
   // mytable.insert($1->value,$3->type,$3->value,yylineno-1);
}
    | NAME {
        $$->tac.push_back($1->value+" =  popparam");
    }

classdef: "class" NAME '(' arglist ')' ':' suite {
    $$=new Node("classdef");
    $$->childs.push_back($2);
    $$->childs.push_back($4);
    $$->childs.push_back($7);
}
    | "class" NAME '(' ')' ':' suite {
        $$=new Node("classdef");
        $$->childs.push_back($1);
        $$->childs.push_back($5);
    }
    | "class" NAME ':' suite {
        $$=new Node("classdef");
        $$->childs.push_back($1);
        $$->childs.push_back($3);
    }
arglist: argument comma_argument_star ','{
    $$=new Node(",");
    $$->childs.push_back($1);
    $$->childs.push_back($2);
    
}
    | argument comma_argument_star{
        $$=new Node("classdef");
        $$->childs.push_back($1);
        $$->childs.push_back($2);
    }
    | argument ','{$$=$1;}
    | argument 
comma_argument_star: comma_argument_star ',' argument{
    $$=new Node(",");
    $$->childs.push_back($1);
    $$->childs.push_back($3);
}
    | ',' argument{$$=$2;}
argument: test
    | test ":=" test{
        $$=new Node(":=");
        $$->childs.push_back($1);
        $$->childs.push_back($3);
    }
    | test '=' test{
        $$=new Node("=");
        $$->childs.push_back($1);
        $$->childs.push_back($3);
    }

%%

int main(void){
    yydebug=1;
    indent.push(0);
    yyparse();
    ofstream outfile("graph.dot");
    if (!outfile.is_open()) {
        cerr << "Error opening file for writing." << endl;
        return 1;
    }

  
    outfile << "digraph G {" << endl;

    printnodes(outfile, head);
    printedges(outfile, head);
    outfile << "}" << endl;
    cout<<endl;
    // mytable.print();
    outfile.close();
    printtable(global_scope);
    print3ac(head);
   
}

void yyerror (const char *s) {
    cout << s << endl;
}


void printtable(struct scope* global_scope){
    ofstream file("symbol.txt");

    if (global_scope){
        file<<global_scope->name<<endl;
        for(auto a:global_scope->smt->symbols){
            file <<"       " << a->name<<"  "<<a->type<<"  "<<a->value<<"  "<<a->lineno<<endl;
        }
        for(auto a:global_scope->childs){
            printtable(a);
        }
    }else{
        return;
    }
   
     file.close();
 }


