%option noyywrap
%option yylineno
%{
    #include<bits/stdc++.h>
    #include"node.cpp"
    #include "parser.tab.h"
    using namespace std;
    extern long long int line_number;
    std::stack<int> indent;
    int dedent=0;
    int ind=0;
    int newline=0;
    int a=0;
    
%}
bininteger   [0][bB]([_]?[0-1])+
octinteger   [0][oO]([_]?[0-7])+
hexinteger   [0][xX]([_]?[0-9a-fA-F])+
decinteger [0]|[0]([_]?[0])+|[1-9]([_]?[0-9])*
integer      {bininteger}|{octinteger}|{hexinteger}|{decinteger}
digitpart [0-9]([_]?[0-9])*
fraction [.]{digitpart}
exponent      [eE][+-]?{digitpart}
pointfloat    ({digitpart}?){fraction}|{digitpart}[.]
exponentfloat ({digitpart}|{pointfloat}){exponent}
floatnumber   {pointfloat}|{exponentfloat}
number {integer}|{floatnumber}
%s final
%% 

  {
        if(ind){
            ind=0;
            return INDENT;
        }
        if(dedent>0){
            dedent--;
            return DEDENT;
        }
    }
^[ ]+("#"[^\n]*)?$ {}
^[ ]+ {return INDENT;}
\n[ ]*/\n {}
\n[ ]* { 
        int ct=yyleng-1;
        BEGIN(final);
        
        if(ct%2==1) {
            cout << "indentation error" << endl;
            exit(-1);
        }
        else if(ct > indent.top()){
            indent.push(ct);
            ind=1;
           
        }
        else if(ct < indent.top()){
            while(ct!=indent.top()){
                dedent++;
                if(indent.top()==0){
                    cout << "indentation error" << endl;
                }
                indent.pop();
            }
        }
        return NEWLINE;
    }
^. {
    unput(*yytext);
    BEGIN(final);
    while(indent.top()!=0){
        dedent++;
        indent.pop();
    }
}

 
<final>True { yylval.node=new Node(yytext);yylval.node->type = "KeyWORD";return TRUE;}
<final>False {yylval.node=new Node(yytext);yylval.node->type = "KeyWORD";return FALSE;}
<final>none {   yylval.node=new Node(yytext);yylval.node->type = "KeyWORD"; return NONE;}
<final>pass { yylval.node=new Node(yytext);yylval.node->type = "KeyWORD";   return PASS;}
<final>continue { yylval.node=new Node(yytext);yylval.node->type = "KeyWORD";return CONTINUE;}
<final>for { yylval.node=new Node(yytext);yylval.node->type = "KeyWORD";return FOR;}
<final>if { yylval.node=new Node(yytext);yylval.node->type = "KeyWORD";return IF;}
<final>elif { yylval.node=new Node(yytext);yylval.node->type = "KeyWORD";return ELIF;}
<final>else { yylval.node=new Node(yytext);yylval.node->type = "KeyWORD"; return ELSE;}
<final>break { yylval.node=new Node(yytext);yylval.node->type = "KeyWORD";  return BREAK;}
<final>return { yylval.node=new Node(yytext);yylval.node->type = "KeyWORD";return RETURN;}
<final>class { yylval.node=new Node(yytext);yylval.node->type = "KeyWORD"; return CLASS;}
<final>while { 
    yylval.node=new Node(yytext);yylval.node->type = "KeyWORD";   
    return WHILE;}
<final>in {
    yylval.node=new Node(yytext);yylval.node->type = "KeyWORD";    
    return IN;}

<final>and {   
    yylval.node=new Node(yytext);yylval.node->type = "KeyWORD";
    return AND;
}
<final>def {    
    yylval.node=new Node(yytext);yylval.node->type = "KeyWORD";
    return DEF;
}
<final>not { yylval.node=new Node(yytext);
            yylval.node->type = "operator";
            return NOT;}

<final>or { yylval.node=new Node(yytext);yylval.node->type = "operator"; 
    return OR;}
<final>[a-zA-Z_][a-zA-Z0-9_]* {
    yylval.node=new Node(yytext);yylval.node->type = "KeyWORD";
    return NAME;
}
<final>{number} {
    yylval.node=new Node(yytext);yylval.node->type = "NUMBER";
  
    return NUMBER;
}



<final>"+" {
    yylval.node=new Node(yytext);yylval.node->type = "operator";
    return '+';
}
<final>"-" {
    yylval.node=new Node(yytext);yylval.node->type = "operator";
    return '-';
}
<final>"*" {
    yylval.node=new Node(yytext);yylval.node->type = "operator";
    return '*';
}
<final>"/" {
    yylval.node=new Node(yytext);yylval.node->type = "operator";
    return '/';
}

<final>"//" {
    yylval.node=new Node(yytext);yylval.node->type = "operator";
    return CONCAT;
}

<final>"%" {
    yylval.node=new Node(yytext);yylval.node->type = "operator";
    
    return '%';
}

<final>"**" {
    yylval.node=new Node(yytext);yylval.node->type = "operator";
    
    return POW;
}
 




<final>"=" {
    yylval.node=new Node(yytext);yylval.node->type = "operator";
    return '=';
}
<final>"+=" {
    yylval.node=new Node(yytext);yylval.node->type = "operator";
    return ADD_ASSIGN;
}
<final>"-=" {
    yylval.node=new Node(yytext);yylval.node->type = "operator";
    return SUB_ASSIGN;
}
<final>"*=" {
   yylval.node=new Node(yytext);yylval.node->type = "operator";
    return  MUL_ASSIGN;
}
<final>"/=" {
   yylval.node=new Node(yytext);yylval.node->type = "operator";
    return DIV_ASSIGN;
}
<final>"%=" {
    yylval.node=new Node(yytext);yylval.node->type = "operator";
    return REM_ASSIGN;
}
<final>"**=" {
    yylval.node=new Node(yytext);yylval.node->type = "operator";
    return POW_ASSIGN;
}
<final>"&=" {
    yylval.node=new Node(yytext);yylval.node->type = "operator";
    return AND_ASSIGN;
}
<final>"|=" {
    yylval.node=new Node(yytext);yylval.node->type = "operator";
    return OR_ASSIGN;
}
<final>"^=" {
   yylval.node=new Node(yytext);yylval.node->type = "operator";
    return XOR_ASSIGN;
}

<final>"<<=" {
    yylval.node=new Node(yytext);yylval.node->type = "operator";
    return LEFT_ASSIGN;
}
<final>">>=" {
   yylval.node=new Node(yytext);yylval.node->type = "operator";
    return RIGHT_ASSIGN;
}



<final>">" {
   yylval.node=new Node(yytext);yylval.node->type = "operator";
    return '>';
    }
<final>"<" {
    yylval.node=new Node(yytext);yylval.node->type = "operator";
    return '<';
}
<final>"==" {
    yylval.node=new Node(yytext);yylval.node->type = "operator";
    return IS_EQUAL;
}
<final>">=" {
    yylval.node=new Node(yytext);yylval.node->type = "operator";
    return GEQ;
}
<final>"<=" {
    yylval.node=new Node(yytext);yylval.node->type = "operator";
    return LEQ;
}
<final>"!=" {
   yylval.node=new Node(yytext);yylval.node->type = "operator";
    return NOT_EQUAL;
}



<final>"&" {
    yylval.node=new Node(yytext);yylval.node->type = "operator";
    return '&';
}
<final>"|" {
    yylval.node=new Node(yytext);yylval.node->type = "operator";
    return '|';
}
<final>"^" {
    yylval.node=new Node(yytext);yylval.node->type = "operator";
    return '^';
}
<final>"~" {
   yylval.node=new Node(yytext);yylval.node->type = "operator";
    return '~';
}

<final>"<<" {
    yylval.node=new Node(yytext);yylval.node->type = "operator";
    return LEFT_OP;
}
<final>">>" {
   yylval.node=new Node(yytext);yylval.node->type = "operator";
    return RIGHT_OP;
}



<final>":" {
    yylval.node=new Node(yytext);yylval.node->type = "DELIMETER";
    return ':';
}
<final>"->" {
    yylval.node=new Node(yytext);yylval.node->type = "DELIMETER";
    return ARROW;
}


<final>"[" {
    yylval.node=new Node(yytext);yylval.node->type = "DELIMETER";
    return '[';
}
<final>"]" {
    yylval.node=new Node(yytext);yylval.node->type = "DELIMETER";
  
    return ']';
}
<final>"(" {
    yylval.node=new Node(yytext);yylval.node->type = "DELIMETER";
    return '(';
}
<final>")" {
    yylval.node=new Node(yytext);yylval.node->type = "DELIMETER";
    return ')';
}


<final>"." {
    yylval.node=new Node(yytext);yylval.node->type = "DELIMETER";
        return '.';
}

<final>"," { yylval.node=new Node(yytext);yylval.node->type = "DELIMETER";
        return ','; }

<final>"{" {
    yylval.node=new Node(yytext);yylval.node->type = "DELIMETER";
        return  '{';
}

<final>"}" {
    yylval.node=new Node(yytext);yylval.node->type = "DELIMETER";
        return '}';
}

<final>";" {
    yylval.node=new Node(yytext);yylval.node->type = "DELIMETER";
        return ';';
}

<final>[\"][^\"]*[\"]|[\'][^\']*[\'] {
   
   yylval.node=new Node(yytext);yylval.node->type = "STRING";
            return STRING;
}

<final>[ \t\r\f] {}

<final>. {printf("error! unrecognised input character :%s, skipping\n", yytext); exit(-1);}


%%
