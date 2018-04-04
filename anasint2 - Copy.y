/****************************************************/
/* File: anasint2.y                                 */
/* The C- Yacc/Bison specification file             */
/*                                                  */
/* Lucas Vecchete                                   */
/****************************************************/
%{
#define YYPARSER /* distinguishes Yacc output from other code files */
#include <iostream>
#include <fstream>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <string>
#include <math.h>

#define YYDEBUG 1
#define productionFeedBack 0
#define NodeCreationFeedBack 0 

#define AssemblerFeedBack 0
#define ShowCodeGenErrors 0
#define instructionsOnTerminal 0
#define memAllocFeedback 0

#define ShowSemanticalErrors 1
#define TabGenFeedBack 0

FILE* listing; /* listing output text file */

/*******************************************************/
/********** Árvore de Análise Sintática ****************/
/*******************************************************/


static int indentNo = 0;
#define YYSTYPE TreeNode *
#define INDENT indentNo+=4
#define UNINDENT indentNo-=4
#define MAXCHILDREN 3

typedef enum {StmtK,ExpK} NodeKind;//NodeKind é um tipo que é usado no campo "nodekind" do treeNode, Smtk significa que é um nó (If,While, Assign, Return) ExpK significa que é um nó (Operação,Numero,ID,Declaracao de Funcao,MemVarK)
typedef enum {IfK,WhileK,AssignK,ReturnK} StmtKind;//Tipos de StmtKind, if, while, assign, return
typedef enum {OpK,NumK,IdK,DeclTypeK,MemVarK} ExpKind;//Tipos de ExpKind Operação, Numero, ID, Tipo de declaracao, 
/* ExpType is used for type checking */
typedef enum {Void,Integer} ExpType;
typedef enum {Call,FuncDecl,VarDecl,Var,VectorDecl,VectorPos, FuncAttrVar, FuncAttrVector} IDType;

typedef struct treeNode
   { struct treeNode * child[MAXCHILDREN];//maximo de filhos do no
     struct treeNode * sibling;//ponteiro para o no irmao
     int lineno;
	 int codeGen;
     NodeKind nodekind;
     union { StmtKind stmt; ExpKind exp;} kind;
     union { int op;
             int val;
             char * name; } attr;//tipo de atributo do no se eh nome, um token ou valor
    ExpType type; /* for type checking of exps */ //preenche so quando DeclType
	IDType id_type;
	char * scope;
	int scope_number;
   } TreeNode;

static char * savedName; /* for use in assignments */
static int savedLineNo;  /* ditto */
static int savedVal;  /* ditto */
static char * savedFunction = "Global";

TreeNode * savedTree = NULL;// Declaração da árvore

TreeNode * newExpNode(ExpKind kind);
TreeNode * newStmtNode(StmtKind kind);
void printTree(TreeNode * tree);
void printToken(int token, const char* tokenString );

/************************************************************************/
/************* Tabela de Símbolos e Analisador Semântico ****************/
/************************************************************************/

#define hash_size 211

int semantical_error = 0;

typedef struct symbol{
	char *ID;
	IDType id_type;
	char *data_type;
	int index;
	char *scope;
	int lines[50];
	int top;
	int mem_add; //memLoc
	int size;
	int im_add;	// lineLocAssembly
	TreeNode *node;
	struct symbol *nxt;
} Symbol;

typedef struct {
  Symbol *begin;
}SymList;

SymList HashVec[hash_size];

int hash_calc(char *nameID);

/************************************************************************/
/******************* Gerador de Codigo Intermediario ********************/
/************************************************************************/



/**************************************************************/

std::string strExp;

using namespace std;

extern "C"
{
	ofstream writeTree;
	int yylex();
	int yyparse();
	void abrirArq();
	char ids[30];
	char *copyString(char * s);
	void printSyntaxTree();
	void printTable();
	void SymTabGen();
	void generateIntermCode(); 
}


extern char* yytext;
extern int yylineno;

void yyerror(char*);

/*********************************************************************/

%}
%start programa
%token IF  1
%token INT 2
%token RETURN 3
%token VOID 4
%token WHILE 5
%token ID 6
%token NUMERO 7 
%token ADD 8
%token SUB 9
%token MULT 10
%token DIV 11
%token LESS 12
%token LESSEQ 13
%token GREAT 14
%token GREATEQ 15
%token EQUAL 16
%token NEQUAL 17
%token ASSIGN 18
%token SEMICOLON 19
%token COMMA 20
%token LPARENTS 21
%token RPARENTS 22
%token LSQRBRA 23
%token RSQRBRA 24
%token LCURBRA 25
%token RCURBRA 26
%token ERROR 27

%nonassoc ELSE
%% /* Grammar for TINY */

programa: declaracao_lista 
				{ 
				if (productionFeedBack) printf("programa-> declaracao_lista .\n");
				savedTree = $1;
				}
			;
declaracao_lista: declaracao_lista declaracao 
				{
					if (productionFeedBack) printf("declaracao_lista-> declaracao_lista declaracao .\n");
					YYSTYPE t = $1;
					if (t!=NULL){
						while(t->sibling != NULL) t = t->sibling;
						t->sibling = $2;
						$$ = $1;
					}else{
						$$ = $2;
					}
				}
			|	declaracao
				{
					if (productionFeedBack) printf("declaracao_lista-> declaracao .\n");
					$$ = $1;
				}
			;
declaracao: var_declaracao
				{
					if (productionFeedBack) printf("declaracao-> var_declaracao .\n");
					$$ = $1;
				}
			| fun_declaracao
				{
					if (productionFeedBack) printf("declaracao-> fun_declaracao .\n");
					$$ = $1;
					savedFunction = "Global";
				}
			;
var_declaracao: tipo_especificador ID {savedName = copyString(ids);savedLineNo = yylineno;} SEMICOLON
				{
					if (productionFeedBack) printf("var_declaracao-> tipo_especificador ID ;.\n");
					YYSTYPE t;
					t = newExpNode(IdK); /*cria um  nó do tipo Exp e manda o tipo IdK para simbolizar que é um id*/
					t->attr.name = savedName; /*copia a string da ID para o campo nome do nó*/
					t->lineno = savedLineNo; /*copia o numero da linha da ID para o campo line no do nó*/
					
					t->sibling = $$->sibling;
					t->child[0] = $$->child[0];
					t->child[1] = $$->child[1];
					t->child[2] = $$->child[2];					
					$$ = $1;
					$$->sibling = NULL;
					$$->child[0] = t;
					$$->child[1] = NULL;
					$$->child[2] = NULL;
					$$->id_type = VarDecl;
					$$->child[0]->id_type = VarDecl;
					$$->scope = savedFunction;
					$$->child[0]->type = $$->type;
				}
			|	tipo_especificador ID{savedName = copyString(ids);savedLineNo = yylineno;} LSQRBRA NUMERO {savedVal = atoi(ids);} RSQRBRA SEMICOLON
				{
					if (productionFeedBack) printf("var_declaracao-> tipo_especificador ID [ NUMERO ];.\n");
					YYSTYPE t;
					YYSTYPE r;
					t = newExpNode(IdK);     /*cria um  nó do tipo Exp e manda o tipo IdK para simbolizar que é um id*/
					t->attr.name = savedName; /*copia a string da ID para o campo nome do nó*/
					t->lineno = savedLineNo; /*copia o numero da linha da ID para o campo line no do nó*/
					r = newExpNode(MemVarK);
					r->attr.val = savedVal;
					r->lineno = savedLineNo;
					
					t->sibling = $$->sibling;
					t->child[0] = r;
					t->child[1] = NULL;
					t->child[2] = NULL;
					r->child[0] = $$->child[0];
					r->child[1] = $$->child[1];
					r->child[2] = $$->child[2];					
					$$ = $1;
					$$->sibling = NULL;
					$$->child[0] = t;
					$$->child[1] = NULL;
					$$->child[2] = NULL;
					$$->id_type = VectorDecl;
					$$->child[0]->id_type = VectorDecl;
					$$->scope = savedFunction;
					$$->child[0]->type = $$->type;					
				}
			;
tipo_especificador: INT
				{
					if (productionFeedBack) printf("tipo_especificador-> int .\n");
					$$ = newExpNode(DeclTypeK);
					$$->type = Integer;
				}
			|	VOID
				{
					if (productionFeedBack) printf("tipo_especificador-> void .\n");
					$$ = newExpNode(DeclTypeK);
					$$->type = Void;
				}
			
			;
fun_declaracao: tipo_especificador ID {savedName = copyString(ids);savedLineNo = yylineno; savedFunction = savedName;} LPARENTS params RPARENTS composto_decl
				{
					
					if (productionFeedBack) printf("fun_declaracao-> tipo_especificador ID ( params ) composto_decl.\n");
					YYSTYPE t;
					t = newExpNode(IdK);     /*cria um  nó do tipo Exp e manda o tipo IdK para simbolizar que é um id*/
					t->attr.name = savedFunction; /*copia a string da ID para o campo nome do nó*/
					t->lineno = savedLineNo; /*copia o numero da linha da ID para o campo line no do nó*/
					
					t->sibling = $$->sibling;
					t->child[0] = $5;
					t->child[1] = $7;
					t->child[2] = NULL;					
					$$ = $1;
					$$->sibling = NULL;
					$$->child[0] = t;
					$$->child[1] = NULL;
					$$->child[2] = NULL;
					$$->id_type = FuncDecl;
					$$->child[0]->id_type = FuncDecl;
					$$->child[0]->type = $$->type;
					
				}			
			;
params: param_lista
				{
					if (productionFeedBack) printf("params-> param_lista .\n");
					$$ = $1;
				}
			|	VOID
				{
					if (productionFeedBack) printf("params-> VOID .\n");
					$$ = NULL;
				}
			;
param_lista: param_lista COMMA param
				{
					if (productionFeedBack) printf("param_lista-> param_lista , param .\n");
					YYSTYPE t = $1;
					if (t!=NULL){
						while(t->sibling != NULL) t = t->sibling;
						t->sibling = $3;
						$$ = $1;
					}else{
						$$ = $3;
					}
				}
			|	param
				{
					if (productionFeedBack) printf("param_lista-> param .\n");
					$$ = $1;
				}
			;
param: tipo_especificador id                              /*(tipo_especificador)->child[0](ID)*/
				{
					if (productionFeedBack) printf("param-> tipo_especificador ID .\n");
					$$ = $1;
					$$->child[0] = newExpNode(IdK);     /*cria um  nó do tipo Exp e manda o tipo IdK para simbolizar que é um id*/
					$$->child[0]->attr.name = $2->attr.name; /*copia a string da ID para o campo nome do nó*/				
					$$->child[0]->lineno = $2->lineno;
					$$->id_type = FuncAttrVar;
					$$->child[0]->id_type = FuncAttrVar;
					$$->scope = savedFunction;
					$$->child[0]->type = $$->type;
				}
			|	tipo_especificador id {savedName = copyString(ids);} LSQRBRA RSQRBRA
				{
					if (productionFeedBack) printf("param-> tipo_especificador ID [ ] .\n");
					//YYSTYPE t;
					//t = newExpNode(IdK);     /*cria um  nó do tipo Exp e manda o tipo IdK para simbolizar que é um id*/
					//t->attr.name = savedName; /*copia a string da ID para o campo nome do nó*/
					//t->lineno = $1->lineno; /*copia o numero da linha da ID para o campo line no do nó*/
					$$ = $1;
					$$->child[0] = $2;
					$$->id_type = FuncAttrVector;
					$$->child[0]->id_type = FuncAttrVector;
					$$->scope = savedFunction;
					$$->child[0]->type = $$->type;
				}
			;
composto_decl: LCURBRA local_declaracoes statement_lista RCURBRA
				{
					if (productionFeedBack) printf("composto_decl-> { local_declaracoes statement_lista } .\n");
					YYSTYPE t = $2;
					if (t!=NULL){
						while(t->sibling != NULL) t = t->sibling;
						t->sibling = $3;
						$$ = $2;
					}else{
						$$ = $3;
					}			
				}
			;	
local_declaracoes: local_declaracoes var_declaracao
				{
					if (productionFeedBack) printf("local_declaracoes-> local_declaracoes var_declaracao .\n");
					YYSTYPE t = $1;
					if (t!=NULL){
						while(t->sibling != NULL) t = t->sibling;
						t->sibling = $2;
						$$ = $1;
					}else{
						$$ = $2;
					}				
				}
			|	/* empty */
				{
					if (productionFeedBack) printf("local_declaracoes-> vazio .\n");
					$$ = NULL;
				}
			;			
statement_lista: statement_lista statement
				{
					if (productionFeedBack) printf("statement_lista-> statement_lista statement .\n");
					
					YYSTYPE t = $1;
					if (t!=NULL){
						while(t->sibling != NULL) t = t->sibling;
						t->sibling = $2;
						$$ = $1;
					}else{
						$$ = $2;
					}				
				}
			|	/* empty */
				{
					if (productionFeedBack) printf("statement_lista-> vazio .\n");
					$$ = NULL;
				}
			;
statement: expressao_decl 
				{
					if (productionFeedBack) printf("statement-> expressao_decl .\n");
					$$ = $1;			
				}
			|	composto_decl 
				{
					if (productionFeedBack) printf("statement-> composto_decl .\n");
					$$ = $1;			
				}
			|	selecao_decl
				{
					if (productionFeedBack) printf("statement-> selecao_decl .\n");
					$$ = $1;			
				}
			|	iteracao_decl
				{
					if (productionFeedBack) printf("statement-> iteracao_decl .\n");
					$$ = $1;				
				}
			|	retorno_decl
				{
					if (productionFeedBack) printf("statement-> retorno_decl .\n");
					$$ = $1;			
				}
			;
expressao_decl: expressao SEMICOLON
				{
					if (productionFeedBack) printf("expressao_decl-> expressao ; .\n");
					$$ = $1;			
				}
			|	SEMICOLON 
				{
					if (productionFeedBack) printf("expressao_decl-> ;.\n");
					$$ = $1;			
				}
			;
selecao_decl:  IF LPARENTS expressao RPARENTS statement        
				{
					if (productionFeedBack) printf("selecao_decl-> if ( expressao ) statement.\n");
					$$ = newStmtNode(IfK);
					$$->child[0] = $3;
					$$->child[1] = $5;
				}
			|	IF LPARENTS expressao RPARENTS statement ELSE statement
				{
					if (productionFeedBack) printf("selecao_decl-> if ( expressao ) statement else statement.\n");
					$$ = newStmtNode(IfK);
					$$->child[0] = $3;
					$$->child[1] = $5;
					$$->child[2] = $7;
				}
			;			
iteracao_decl: WHILE LPARENTS expressao RPARENTS statement
				{
					if (productionFeedBack) printf("iteracao_decl-> while ( expressao ) statement.\n");
					$$ = newStmtNode(WhileK);
					$$->child[0] = $3;
					$$->child[1] = $5;
				}
			;
retorno_decl: RETURN SEMICOLON
				{
					if (productionFeedBack) printf("retorno_decl-> return ;.\n");
					$$ = newStmtNode(ReturnK);
					$$->child[0] = NULL;
				}
			|	RETURN expressao SEMICOLON
				{
					if (productionFeedBack) printf("retorno_decl-> return expressao ;.\n");
					$$ = newStmtNode(ReturnK);
					$$->child[0] = $2;
				}
			;
expressao: var ASSIGN expressao
				{
					if (productionFeedBack) printf("expressao-> var = expressao.\n");
					$$ = newStmtNode(AssignK);
					$$->child[0] = $1;
					$$->child[1] = $3;
					$$->type = $1->type;
				}
			|	simples_expressao
				{
					if (productionFeedBack) printf("expressao-> simples_expressao.\n");
					$$ = $1;
				}
			;
var: ID
				{
					if (productionFeedBack) printf("var-> ID.\n");
					$$ = newExpNode(IdK);
					$$->attr.name = copyString(ids);
					$$->id_type = Var;					
				}
			|	ID {savedName = copyString(ids);savedLineNo = yylineno;} LSQRBRA expressao RSQRBRA
				{
					if (productionFeedBack) printf("var-> ID [ expressao ].\n");
					$$ = newExpNode(IdK);
					$$->attr.name = savedName;
					$$->lineno = savedLineNo;
					$$->child[0] = $4;
					$$->id_type = VectorPos;
				}
			;
simples_expressao: soma_expressao relacional soma_expressao
				{
					if (productionFeedBack) printf("simples_expressao-> soma_expressao relacional soma_expressao.\n");
					$$ = newExpNode(OpK);
					$$->attr.op = $2->attr.op;
					$$->child[0] = $1;
					$$->child[1] = $3;
				}
			|	soma_expressao
				{
					if (productionFeedBack) printf("simples_expressao-> soma_expressao.\n");
					$$ = $1;
				}
			;
relacional: LESSEQ 
				{
					if (productionFeedBack) printf("relacional-> <=.\n");
					$$ = newExpNode(OpK);
					$$->attr.op = LESSEQ;
				}
			|	LESS 
				{
					if (productionFeedBack) printf("relacional-> <.\n");
					$$ = newExpNode(OpK);
					$$->attr.op = LESS;
				}
			|	GREAT
				{
					if (productionFeedBack) printf("relacional-> >.\n");
					$$ = newExpNode(OpK);
					$$->attr.op = GREAT;
				}
			|	GREATEQ
				{
					if (productionFeedBack) printf("relacional-> >=.\n");
					$$ = newExpNode(OpK);
					$$->attr.op = GREATEQ;				
				}
			|	EQUAL
				{
					if (productionFeedBack) printf("relacional-> ==.\n");
					$$ = newExpNode(OpK);
					$$->attr.op = EQUAL;
				}
			|	NEQUAL
				{
					if (productionFeedBack) printf("relacional-> !=.\n");
					$$ = newExpNode(OpK);
					$$->attr.op = NEQUAL;
				}
			;
soma_expressao: soma_expressao soma termo
				{
					if (productionFeedBack) printf("soma_expressao-> soma_expressao soma termo.\n");
					$$ = $2;
					if ($1->type == Integer && $3->type == Integer){
						$2->type = Integer;
					}
					$$->child[0] = $1;
					$$->child[1] = $3;
				}
			|	termo
				{
					if (productionFeedBack) printf("soma_expressao-> termo.\n");
					$$ = $1;
				}
			;
soma: ADD 
				{
					if (productionFeedBack) printf("soma-> +.\n");
					$$ = newExpNode(OpK);
					$$->attr.op = ADD;
				}
			|	SUB 
				{
					if (productionFeedBack) printf("soma-> - .\n");
					$$ = newExpNode(OpK);
					$$->attr.op = SUB;				
				}
			;		
termo: termo mult fator
				{
					if (productionFeedBack) printf("termo-> termo mult fator.\n");
					$$ = $2;
					if ($1->type == Integer && $3->type == Integer){
						$2->type = Integer;
					}
					$$->child[0] = $1;
					$$->child[1] = $3;
				}
			|	fator
				{
					if (productionFeedBack) printf("termo-> fator.\n");
					$$ = $1;
				}
			;		
mult: MULT 
				{
					if (productionFeedBack) printf("mult-> *.\n");
					$$ = newExpNode(OpK);
					$$->attr.op = MULT;
				}
			|	DIV 
				{
					if (productionFeedBack) printf("mult-> /.\n");
					$$ = newExpNode(OpK);
					$$->attr.op = DIV;
				}
			;
fator: LPARENTS expressao RPARENTS
				{
					if (productionFeedBack) printf("fator-> ( expressao ).\n");
					$$ = $2;
				}
			|	var
				{
					if (productionFeedBack) printf("fator-> var.\n");
					$$ = $1;
				}
			|	ativacao
				{
					if (productionFeedBack) printf("fator-> ativacao.\n");
					$$ = $1;
				}
			|	NUMERO
				{
					if (productionFeedBack) printf("fator-> NUMERO.\n");
					$$ = newExpNode(NumK);
					$$->type = Integer;
					$$->attr.val = atoi(ids);
				}
			;
ativacao: id LPARENTS args RPARENTS
				{
					if (productionFeedBack) printf("ativacao->ID ( args ).\n");
					$$ = newExpNode(IdK);
					$$->attr.name = $1->attr.name;
					$$->lineno = $1->lineno;
					$$->child[0] = $3;
					$$->id_type = Call;
				}
			;
id: ID			
				{
					$$ = newExpNode(IdK);
					$$->attr.name = copyString(ids);
					savedName = copyString(ids);
					$$->lineno = yylineno;
				}
			;
args: arg_lista
				{
					if (productionFeedBack) printf("args->arg_lista.\n");
					$$ = $1;
				}
			|	/* empty */
				{
					if (productionFeedBack) printf("args->vazio.\n");
					$$ = NULL;
				}
			;
arg_lista: arg_lista COMMA expressao
				{
					if (productionFeedBack) printf("arg_lista->arg_lista , expressao.\n");
					YYSTYPE t = $1;
					if (t!=NULL){
						while(t->sibling != NULL) t = t->sibling;
						t->sibling = $3;
						$$ = $1;
					}else{
						$$ = $3;
					}
				}
			|	expressao
				{
					if (productionFeedBack) printf("arg_lista->expressao.\n");
					$$ = $1;
				}
			;

%%

/*************************************************************/
/************* Arvore de Analise Sintática *******************/
/*************************************************************/

char * returnType(ExpType type){
	switch(type){
		case Void: return "Void"; break;
		case Integer: return "Integer"; break;
	}
}

char * returnIDType(IDType type){
	switch(type){
		case Call: return "cham func"; break;
		case VarDecl: return "decl var"; break;
		case FuncDecl: return "decl funcao"; break;
		case Var: return "variavel"; break;
		case VectorDecl: return "decl vetor"; break;
		case VectorPos: return "vetor"; break;
		case FuncAttrVar: return "param func var"; break;
		case FuncAttrVector: return "param func vet"; break;
	}
}

char * returnOp(int op){
	switch(op){
		case ADD: return "+"; break;
		case MULT: return "*"; break;
		case SUB: return "-"; break;
		case DIV: return "/"; break;
		case EQUAL: return "=="; break;
		case NEQUAL: return "!="; break;
		case LESS: return "<"; break;
		case LESSEQ: return "<="; break;
		case GREAT: return ">"; break;
		case GREATEQ: return ">="; break;
	}
}

TreeNode * newStmtNode(StmtKind kind)
{ TreeNode * t = (TreeNode *) malloc(sizeof(TreeNode));
  int i;
  if (t==NULL){
    printf("Out of memory error at line %d\n",yylineno);
	}
  else {
    for (i=0;i<MAXCHILDREN;i++) t->child[i] = NULL;
    t->sibling = NULL;
    t->nodekind = StmtK;
    t->kind.stmt = kind;
    t->lineno = yylineno;
  }
  return t;
}

/* Function newExpNode creates a new expression 
 * node for syntax tree construction
 */
TreeNode * newExpNode(ExpKind kind)
{ TreeNode * t = (TreeNode *) malloc(sizeof(TreeNode));
  int i;
  if (t==NULL)
  {
	printf("Out of memory error at line %d\n",yylineno);
	}
  else {
    for (i=0;i<MAXCHILDREN;i++) t->child[i] = NULL;
    t->sibling = NULL;
    t->nodekind = ExpK;
    t->kind.exp = kind;
    t->lineno = yylineno;
  }
  return t;
}

/* Function copyString allocates and makes a new
 * copy of an existing string
 */
char * copyString(char * s)
{ int n;
  char * t;
  if (s==NULL) return NULL;
  n = strlen(s)+1;
  t = (char *)malloc(n);
  if (t==NULL){
    printf("Out of memory error at line %d\n",yylineno);
	}
  else strcpy(t,s);
  return t;
}

/* Procedure printToken prints a token 
 * and its lexeme to the listing file
 */
void printToken( int token, const char* tokenString )
{ switch (token)
  { case IF:
    case WHILE:
    case RETURN:
      fprintf(listing,
         "Reserved Word: %s\n",tokenString);
      break;
	case VOID:
		fprintf(listing,"Identifier Type: void\n");
		break;
	case INT:
      fprintf(listing,"Identifier Type: int\n");
	  break;
    case ASSIGN: fprintf(listing,"=\n"); break;
    case EQUAL: fprintf(listing,"==\n"); break;
    case NEQUAL: fprintf(listing,"!=\n"); break;
    case LESS: fprintf(listing,"<\n"); break;
    case LESSEQ: fprintf(listing,"<=\n"); break;
    case GREAT: fprintf(listing,">\n"); break;
    case GREATEQ: fprintf(listing,">=\n"); break;
    case ADD: fprintf(listing,"+\n"); break;
    case SUB: fprintf(listing,"-\n"); break;
    case MULT: fprintf(listing,"*\n"); break;
	case DIV: fprintf(listing,"/\n"); break;
	case LPARENTS: fprintf(listing,"(\n"); break;
	case RPARENTS: fprintf(listing,")\n"); break;
	case SEMICOLON: fprintf(listing,";\n"); break;
	case COMMA: fprintf(listing,",\n"); break;
	case LSQRBRA: fprintf(listing,"[\n"); break;
	case RSQRBRA: fprintf(listing,"]\n"); break;
	case LCURBRA: fprintf(listing,"{\n"); break;
	case RCURBRA: fprintf(listing,"}\n"); break;
    case NUMERO:
      fprintf(listing,
          "NUMERO, val= %s\n",tokenString);
      break;
    case ID:
      fprintf(listing,
          "ID, name= %s\n",tokenString);
      break;
    case ERROR:
      fprintf(listing,
          "ERROR: %s\n",tokenString);
      break;
    default: /* should never happen */
      fprintf(listing,"Unknown token: %d\n",token);
  }
}

/* printSpaces indents by printing spaces */
static void printSpaces(void)
{ int i;
  for (i=0;i<indentNo;i++)
    fprintf(listing," ");
}

/* procedure printTree prints a syntax tree to the 
 * listing file using indentation to indicate subtrees
 */
void printTree( TreeNode * tree )
{ int i;
  INDENT;
  while (tree != NULL) {
	printSpaces();
	if (tree->nodekind==StmtK)
    { switch (tree->kind.stmt) {
        case IfK:
          fprintf(listing,"if \n");
          break;
        case WhileK:
          fprintf(listing,"while \n");
          break;
        case AssignK:
          fprintf(listing," = \n");
          break;
        case ReturnK:
          fprintf(listing,"return \n");
          break;
        default:
          fprintf(listing,"Unknown StmtNode kind \n");
          break;
      }
    }
    else if (tree->nodekind==ExpK)
    { switch (tree->kind.exp) {
        case OpK:
          fprintf(listing,"Op: ");
          printToken(tree->attr.op,"\0");
          break;
        case NumK:
          fprintf(listing,"Numero: %d\n",tree->attr.val);
          break;
        case IdK:
          fprintf(listing,"Id: %s do escopo ",tree->attr.name);
          fprintf(listing,"%s do tipo ",tree->scope);
		  fprintf(listing,"%s. \n",returnIDType(tree->id_type));
		  break;
		case DeclTypeK:
          switch (tree->type){
		  case Void:
			fprintf(listing,"Tipo de ID: void\n");
			break;
		  case Integer:
			fprintf(listing,"Tipo de ID: int\n");
			break;
		  }
          break;
		case MemVarK:
          fprintf(listing,"Size or position: %d\n",tree->attr.val);
          break;
        default:
          fprintf(listing,"Unknown ExpNode kind\n");
          break;
      }
    }
    else fprintf(listing,"Unknown node kind\n");
    for (i=0;i<MAXCHILDREN;i++)
         printTree(tree->child[i]);
    tree = tree->sibling;
  }
  UNINDENT;
}

char* concat(const char *s1, const char *s2)
{
    char *result = (char *)malloc(strlen(s1)+strlen(s2)+1);//+1 for the zero-terminator
    //in real code you would check for errors in malloc here
    strcpy(result, s1);
    strcat(result, s2);
    return result;
}

TreeNode* verify_main(TreeNode * tree){
	if(tree!=NULL){
		if (tree->id_type == FuncDecl){	
			if(tree->child[0]!=NULL){			
				if (!strcmp(tree->child[0]->attr.name,"main")){
					return tree->child[0];
				}
			}	
		}
		if (verify_main(tree->sibling)!=NULL){
			return verify_main(tree->sibling);
		}else{
			return NULL;
		}
	}else{
		return NULL;
	}
}

TreeNode* return_Func_Decl(TreeNode * tree, int scope_number){
	if(tree!=NULL){
		if (tree->id_type == FuncDecl){	
			if(tree->child[0]!=NULL){			
				if (tree->child[0]->id_type == FuncDecl){
					tree->child[0]->lineno = tree->lineno;
					if(tree->child[0]->child[1]!=NULL){
						if (tree->child[0]->child[1]->scope_number == scope_number){
							return tree->child[0];
						}
					}
				}
			}	
		}
		if (return_Func_Decl(tree->sibling,scope_number)!=NULL){
			return return_Func_Decl(tree->sibling,scope_number);
		}else{
			return NULL;
		}
	}else{
		return NULL;
	}
}

TreeNode* return_node_root(TreeNode * tree, TreeNode * node){//procurar o nó e retornar o pai
	if (tree!=NULL){
		if((tree->child[0])!=NULL){
			if (tree->child[0]->kind.exp == IdK){
				if (!strcmp(tree->child[0]->attr.name,node->attr.name)){
					if(tree->child[0]->scope_number == node->scope_number){
						if(tree->child[0]->id_type == node->id_type){
							return tree;
							
						}
					}
				}
			}
			if (return_node_root(tree->child[0],node) !=NULL){
				return tree->child[0];
			}else{
				if(return_node_root(tree->child[1],node)!=NULL){
					return tree->child[1];
				}else{
					if(return_node_root(tree->child[2],node)!=NULL){
						return tree->child[2];
					}else{
						if(return_node_root(tree->sibling,node)!=NULL){
							return tree->sibling;
						}else{
							return NULL;
						}
					}
				}
			}
		}else{
			if((tree->child[1])!=NULL){
				if (tree->child[1]->kind.exp == IdK){
					if (!strcmp(tree->child[1]->attr.name,node->attr.name)){
						if(tree->child[1]->scope_number == node->scope_number){
							if(tree->child[1]->id_type == node->id_type){
								return tree;
							}
						}
					}
				}				
				if (return_node_root(tree->child[0],node) !=NULL){
					return tree->child[0];
				}else{
					if(return_node_root(tree->child[1],node)!=NULL){
						return tree->child[1];
					}else{
						if(return_node_root(tree->child[2],node)!=NULL){
							return tree->child[2];
						}else{
							if(return_node_root(tree->sibling,node)!=NULL){
								return tree->sibling;
							}else{
								return NULL;
							}
						}
					}
				}		
			}
		}
	}else{
		return NULL;
	}
	
}

/////////////////////////AQUIIIIIIIIIIII
TreeNode* change_type_Call(TreeNode * tree, char * name, char * scope, int lineno, ExpType type){
	if(tree!=NULL){
		if (tree->nodekind == ExpK){
			if (tree->kind.exp == IdK){
				if (tree->id_type == Call){
					if (!strcmp(name,tree->attr.name)){
						tree->type = type;
					}
				}
			}
		}
		tree->child[0] = change_type_Call(tree->child[0],name,scope,lineno,type);
		tree->child[1] = change_type_Call(tree->child[1],name,scope,lineno,type);
		tree->child[2] = change_type_Call(tree->child[2],name,scope,lineno,type);
		tree->sibling = change_type_Call(tree->sibling,name,scope,lineno,type);
		return tree;
	}else{
		return NULL;
	}
}



TreeNode * update_scope(TreeNode * tree, int* contador, int * limite, char * scope){
	char* cont;
	char * s;	
	cont = (char*)malloc(6*sizeof(char));
	if (tree == NULL){
		return NULL;
	}else{
		if(tree->nodekind == ExpK){
			if (tree->kind.exp == IdK){
				switch(tree->id_type){
					case FuncDecl:
						(*contador) = (*limite) + 200;
						(*limite) = (*limite) + 200;
						tree->scope_number = 0;
						tree->scope = "Global";
						
						scope = tree->attr.name;
						tree->child[0] = update_scope(tree->child[0], contador, limite, scope);
						scope = tree->attr.name;
						tree->child[1] = update_scope(tree->child[1], contador, limite, scope);
						scope = tree->attr.name;
						tree->child[2] = update_scope(tree->child[2], contador, limite, scope);
						scope = tree->attr.name;
						tree->sibling = update_scope(tree->sibling, contador, limite, scope);
						return tree;
						break;
					default:
						tree->scope_number = (*contador);
						tree->scope = scope;
						tree->child[0] = update_scope(tree->child[0], contador, limite, scope);
						scope = tree->scope;
						tree->child[1] = update_scope(tree->child[1], contador, limite, scope);
						scope = tree->scope;
						tree->child[2] = update_scope(tree->child[2], contador, limite, scope);
						scope = tree->scope;
						tree->sibling = update_scope(tree->sibling, contador, limite, scope);
						return tree;
						break;
				}
			}else{
				tree->scope_number = (*contador);
				tree->scope = scope;
				tree->child[0] = update_scope(tree->child[0], contador, limite, scope);
				scope = tree->scope;
				tree->child[1] = update_scope(tree->child[1], contador, limite, scope);
				scope = tree->scope;
				tree->child[2] = update_scope(tree->child[2], contador, limite, scope);
				scope = tree->scope;
				tree->sibling = update_scope(tree->sibling, contador, limite, scope);
				return tree;
			}
		}else{
			if (tree->kind.stmt == IfK){
				tree->scope = scope;
				tree->scope_number = (*contador);
				sprintf(cont, "%d", (*contador)%200);
				tree->child[0] = update_scope(tree->child[0], contador, limite, scope);
				s = scope;
				
				scope = concat(s,concat("->if",cont));
				(*contador)++;
				
				tree->child[1] = update_scope(tree->child[1], contador, limite, scope);
				
				scope = concat(s,concat("->else",cont));
				(*contador)++;
				
				tree->child[2] = update_scope(tree->child[2], contador, limite, scope);
				scope = s;
				tree->sibling = update_scope(tree->sibling, contador, limite, scope);
				return tree;
			}else{
				if (tree->kind.stmt == WhileK){
					s = scope;
					tree->child[0] = update_scope(tree->child[0], contador, limite, scope);					
					tree->scope_number = (*contador);
					tree->scope = scope;
					scope = concat(s,concat("->while",cont));
					(*contador)++;
					tree->child[1] = update_scope(tree->child[1], contador, limite, scope);
					tree->child[2] = update_scope(tree->child[2], contador, limite, scope);
					scope = s;
					tree->sibling = update_scope(tree->sibling, contador, limite, scope);
					return tree;
				}else{
					tree->scope_number = (*contador);
					tree->scope = scope;
					tree->child[0] = update_scope(tree->child[0], contador, limite, scope);
					scope = tree->scope;
					tree->child[1] = update_scope(tree->child[1], contador, limite, scope);
					scope = tree->scope;
					tree->child[2] = update_scope(tree->child[2], contador, limite, scope);
					scope = tree->scope;
					tree->sibling = update_scope(tree->sibling, contador, limite, scope);
					return tree;
				}
			}
		}
	}
}

TreeNode * update_type(TreeNode * tree){
	if (tree == NULL){
		return NULL;
	}else{
		if(tree->nodekind == ExpK){
			if (tree->kind.exp == DeclTypeK){
				tree->child[0]->type = tree->type;
			}
		}
		tree->child[0] = update_type(tree->child[0]);
		tree->child[1] = update_type(tree->child[1]);
		tree->child[2] = update_type(tree->child[2]);
		tree->sibling = update_type(tree->sibling);
		return tree;
	}
}

void printSyntaxTree() {
	int* contador;
	int* limite;
	char* scope;
	contador = (int *)malloc(sizeof(int));
	limite = (int *)malloc(sizeof(int));
	(*contador) = 0;
	(*limite) = 0;

	scope = "Global";
	savedTree = update_type(savedTree);
	savedTree = update_scope(savedTree,contador,limite,scope);
	TreeNode* t = savedTree;
	while(t!=NULL){
		savedTree = change_type_Call(savedTree,t->child[0]->attr.name,t->child[0]->scope,t->child[0]->lineno,t->child[0]->type);	
		t=t->sibling;
	}
	printTree(savedTree);
}

void yyerror(char * message)
{ fprintf(listing,"Syntax error at line %d: %s\n",yylineno,message);
  fprintf(listing,"Current token: ");
  printToken(yychar,ids);
}

/************************************************************************/
/************************************************************************/
/************************************************************************/
/************************************************************************/
/************************************************************************/
/************* Tabela de Símbolos e Analisador Semântico ****************/
/************************************************************************/
/************************************************************************/
/************************************************************************/
/************************************************************************/

void hash_vector_init() {
	int i;
	for(i = 0; i < hash_size; i++) {
		HashVec[i].begin == NULL;
	}
}

// Hash com deslocamento de bits
int hash_calc(char *nameID) {
	int key = 0;
	int i;
	for(i = 0; i < strlen(nameID)+1; i++) {
		key = ((key << 4) + nameID[i])%hash_size;	
	}
	if(TabGenFeedBack) printf("Chave calculada: %d - %s\n",key,nameID);
	return key;
}


int search_symbol(char *name, char *scope, int pos, IDType type) {
	Symbol *p = HashVec[pos].begin;
	Symbol *q = NULL;
	if(TabGenFeedBack) printf("search_symbol() says: Buscando id %s no escopo %s na posição %d\n",name,scope,pos);		
	if(p == NULL) {
		if(TabGenFeedBack) printf("search_symbol() says: id não encontrado\n");		
		return 0;
	}	
	do {								
		if(!strcmp(p->ID,name) && !strcmp(p->scope,scope)) {
			if (p->id_type == type){
				if(TabGenFeedBack) printf("search_symbol() says: id encontrado\n");
				return 1;
			}
		}
		p = p->nxt;
	} while(p != NULL);
	if(TabGenFeedBack) printf("search_symbol() says: id não encontrado\n");	
	return 0;
}

int search_symbol_decl(char *name, int pos, IDType id_type, char* scope) {
	Symbol *p = HashVec[pos].begin;
	Symbol *q = NULL;
	if(TabGenFeedBack) printf("search_symbol_decl() says: Buscando id %s no escopo %s na posição %d\n",name,scope,pos);		
	if(p == NULL) {
		if(TabGenFeedBack) printf("search_symbol_decl() says: id não encontrado\n");		
		return 0;
	}	
	do {
		
		if(!strcmp(p->ID,name) && ((p->id_type == FuncDecl)||(p->id_type == VarDecl)||(p->id_type == VectorDecl)||(p->id_type == FuncAttrVar) || (p->id_type == FuncAttrVar))) {
			if (!strcmp(p->scope,scope)){//verifica se a declaracao ocorreu dentro de um mesmo escopo
				if(TabGenFeedBack) printf("search_symbol_decl() says: id encontrado\n");
				return 1;		
			}else{
				if (!strcmp(p->scope,"Global") || !strcmp(scope,"Global")){//verifica se a declaracao esta no global ai da erro pq o global serve para todas as funcoes
					if(TabGenFeedBack) printf("search_symbol_decl() says: id encontrado\n");
					return 1;
				}
			}		
		}
		p = p->nxt;
	} while(p != NULL);
	if(TabGenFeedBack) printf("search_symbol_decl() says: id não encontrado\n");	
	return 0;
}

int verify_hierarchy_scope(TreeNode* tree, int scope, IDType id_type, char * name){//Verificação De escopo hierarquia
	if (tree!=NULL){
		if (tree->nodekind==ExpK){
			if (tree->kind.exp == IdK){
				if (!strcmp(tree->attr.name,name)){
					if(tree->scope_number == scope){
						if(tree->id_type == id_type){
							return 1;
						}
					}
				}
			}
		}
		if (verify_hierarchy_scope(tree->child[0],scope, id_type ,name)){
			return 1;
		}else{
			if (verify_hierarchy_scope(tree->child[1],scope, id_type ,name)){
				return 1;
			}else{
				if (verify_hierarchy_scope(tree->child[2],scope, id_type ,name)){
					return 1;
				}else{
					if (verify_hierarchy_scope(tree->sibling,scope, id_type ,name)){
						return 1;
					}else{
						return 0;
					}
				}
			}
		}
	}else{
		return 0;
	}
}

int search_symbol_var_decl(char *name, int pos, IDType id_type, char* scope, int number_scope) {//verificação se existe declaração igual
	int flag_same_function = 0;
	Symbol *p = HashVec[pos].begin;
	Symbol *q = NULL;
	Symbol* backup;
	if(p == NULL) {
		return 0;
	}	
	do {
		if(!strcmp(p->ID,name) && ((p->id_type == VarDecl)||(p->id_type == VectorDecl)||(p->id_type == FuncAttrVar) || (p->id_type == FuncAttrVar))) {
			if (!strcmp(p->scope,scope)){//verifica se a declaracao ocorreu dentro de um mesmo escopo
				return 1;
			}else{
				if (!strcmp(p->scope,"Global")){//verifica se a declaracao esta no global
					return 1;
				}else{
					if(floor(p->node->scope_number/200) == floor(number_scope/200)){//verifica se esta na mesma funcao
						if ((p->id_type == FuncAttrVar) || (p->id_type == FuncAttrVector)){//verifica se esta como atributo da funcao
							flag_same_function = 1;
							backup = p;
						}else{
							TreeNode* root = savedTree;
							TreeNode* tree = return_node_root(root,p->node);
							if(verify_hierarchy_scope(tree,number_scope, id_type ,name)){//verifica se a variavel é alcançavel a partir da declaração.
								flag_same_function = 1;
								backup = p;
							}
						}
					}
				}
			}		
		}
		p = p->nxt;
	} while(p != NULL);	
	if (flag_same_function == 1){
		return 1;
	}
	return 0;
}

TreeNode* return_node_search_symbol_var_decl(char *name, int pos, IDType id_type, char* scope, int number_scope) {
	int flag_same_function = 0;
	Symbol *p = HashVec[pos].begin;
	Symbol *q = NULL;
	Symbol* backup;
	if(p == NULL) {
		return NULL;
	}	
	do {
		if(!strcmp(p->ID,name) && ((p->id_type == VarDecl)||(p->id_type == VectorDecl)||(p->id_type == FuncAttrVar) || (p->id_type == FuncAttrVar))) {
			if (!strcmp(p->scope,scope)){//verifica se a declaracao ocorreu dentro de um mesmo escopo
				return p->node;
			}else{
				if (!strcmp(p->scope,"Global")){//verifica se a declaracao esta no global
					return p->node;
				}else{
					if(floor(p->node->scope_number/200) == floor(number_scope/200)){//verifica se esta na mesma funcao
						if ((p->id_type == FuncAttrVar) || (p->id_type == FuncAttrVector)){//verifica se esta como atributo da funcao
							flag_same_function = 1;
							backup = p;
						}else{
							TreeNode* root = savedTree;
							TreeNode* tree = return_node_root(root,p->node);
							if(verify_hierarchy_scope(tree,number_scope, id_type ,name)){//verifica se a variavel é alcançavel a partir da declaração.
								flag_same_function = 1;
								backup = p;
							}
						}
					}else{
						if (flag_same_function == 1){
							return backup->node;
						}
					}
				}
			}		
		}
		p = p->nxt;
	} while(p != NULL);	
	if (flag_same_function == 1){
		return backup->node;
	}
}

TreeNode* return_node_symbol(char *name, char *scope, int pos, IDType type) {
	Symbol *p = HashVec[pos].begin;
	Symbol *q = NULL;
	if(TabGenFeedBack) printf("return_node_symbol() says: Buscando id %s no escopo %s na posição %d\n",name,scope,pos);		
	if(p == NULL) {
		if(TabGenFeedBack) printf("return_node_symbol() says: id não encontrado\n");		
		return NULL;
	}	
	do {								
		if(!strcmp(p->ID,name) && !strcmp(p->scope,scope)) {
			if (p->id_type == type){
				if(TabGenFeedBack) printf("return_node_symbol() says: id encontrado\n");
				return p->node;
			}
		}
		p = p->nxt;
	} while(p != NULL);
	if(TabGenFeedBack) printf("return_node_symbol() says: id não encontrado\n");	
	return NULL;
}

Symbol* return_symbol(char *name, char *scope, int pos, IDType type) {
	Symbol *p = HashVec[pos].begin;
	Symbol *q = NULL;
	if(TabGenFeedBack) printf("return_node_symbol() says: Buscando id %s no escopo %s na posição %d\n",name,scope,pos);		
	if(p == NULL) {
		if(TabGenFeedBack) printf("return_node_symbol() says: id não encontrado\n");		
		return NULL;
	}	
	do {								
		if(!strcmp(p->ID,name) && !strcmp(p->scope,scope)) {
			if (p->id_type == type){
				if(TabGenFeedBack) printf("return_node_symbol() says: id encontrado\n");
				return p;
			}
		}
		p = p->nxt;
	} while(p != NULL);
	if(TabGenFeedBack) printf("return_node_symbol() says: id não encontrado\n");	
	return NULL;
}

Symbol* return_symbol_decl(char *name, int pos, IDType id_type, char* scope, int number_scope) {
	int flag_same_function = 0;
	Symbol *p = HashVec[pos].begin;
	Symbol *q = NULL;
	Symbol* backup;
	if(TabGenFeedBack) printf("return_node_symbol_decl() says: Buscando id %s no escopo %s na posição %d\n",name,scope,pos);		
	if(p == NULL) {
		if(TabGenFeedBack) printf("return_node_symbol_decl() says: id não encontrado\n");		
		return NULL;
	}	
	do {								
		if(!strcmp(p->ID,name) && ((p->id_type == FuncDecl)||(p->id_type == VarDecl)||(p->id_type == VectorDecl)||(p->id_type == FuncAttrVar) || (p->id_type == FuncAttrVar))){
			if (!strcmp(p->scope,scope)){//verifica se a declaracao ocorreu dentro de um mesmo escopo
				return p;
			}else{
				if (!strcmp(p->scope,"Global")){//verifica se a declaracao esta no global
					return p;
				}else{
					if(floor(p->node->scope_number/200) == floor(number_scope/200)){//verifica se esta na mesma funcao
						if ((p->id_type == FuncAttrVar) || (p->id_type == FuncAttrVector)){//verifica se esta como atributo da funcao
							flag_same_function = 1;
							backup = p;
						}else{
							TreeNode* root = savedTree;
							TreeNode* tree = return_node_root(root,p->node);
							if(verify_hierarchy_scope(tree,number_scope, id_type ,name)){//verifica se a variavel é alcançavel a partir da declaração.
								flag_same_function = 1;
								backup = p;
							}
						}
					}else{
						if (flag_same_function == 1){
							return backup;
						}
					}
				}
			}	
		}
		p = p->nxt;
	} while(p != NULL);
	if(TabGenFeedBack) printf("return_node_symbol_decl() says: id não encontrado\n");	
	if (flag_same_function == 1){
		return backup;
	}
	return NULL;
}

TreeNode* return_node_symbol_decl(char *name, int pos, IDType id_type, char* scope, int number_scope) {
	int flag_same_function = 0;
	Symbol *p = HashVec[pos].begin;
	Symbol *q = NULL;
	Symbol* backup;
	if(TabGenFeedBack) printf("return_node_symbol_decl() says: Buscando id %s no escopo %s na posição %d\n",name,scope,pos);		
	if(p == NULL) {
		if(TabGenFeedBack) printf("return_node_symbol_decl() says: id não encontrado\n");		
		return NULL;
	}	
	do {								
		if(!strcmp(p->ID,name) && ((p->id_type == FuncDecl)||(p->id_type == VarDecl)||(p->id_type == VectorDecl)||(p->id_type == FuncAttrVar) || (p->id_type == FuncAttrVar))){
			if (!strcmp(p->scope,scope)){//verifica se a declaracao ocorreu dentro de um mesmo escopo
				return p->node;
			}else{
				if (!strcmp(p->scope,"Global")){//verifica se a declaracao esta no global
					return p->node;
				}else{
					if(floor(p->node->scope_number/200) == floor(number_scope/200)){//verifica se esta na mesma funcao
						if ((p->id_type == FuncAttrVar) || (p->id_type == FuncAttrVector)){//verifica se esta como atributo da funcao
							flag_same_function = 1;
							backup = p;
						}else{
							TreeNode* root = savedTree;
							TreeNode* tree = return_node_root(root,p->node);
							if(verify_hierarchy_scope(tree,number_scope, id_type ,name)){//verifica se a variavel é alcançavel a partir da declaração.
								flag_same_function = 1;
								backup = p;
							}
						}
					}else{
						if (flag_same_function == 1){
							return backup->node;
						}
					}
				}
			}	
		}
		p = p->nxt;
	} while(p != NULL);
	if(TabGenFeedBack) printf("return_node_symbol_decl() says: id não encontrado\n");	
	if (flag_same_function == 1){
		return backup->node;
	}
	return NULL;
}


void insert_symbol(Symbol *sym, int key) {
	int flag_finished = 0;
	Symbol *p = HashVec[key].begin;
	if(p == NULL) {
		if(TabGenFeedBack) printf("Inserção de símbolo em lista vazia...\n");
		HashVec[key].begin = sym;
		if(TabGenFeedBack) printf("Símbolo <%s> inserido com sucesso em [%d]!\n\n",sym->ID,key);
	} else {
		if(TabGenFeedBack) printf("Colisão, encadeando símbolo\n");
		
		if(!strcmp(p->ID,sym->ID) && !strcmp(p->scope,sym->scope)) {
			if (p->id_type == sym->id_type){
				flag_finished = 1;
				p->lines[p->top] = sym->lines[0];
				p->top++;
			}
		}
		while(p->nxt != NULL) {
			if(!strcmp(p->nxt->ID,sym->ID) && !strcmp(p->nxt->scope,sym->scope)) {
				if (p->nxt->id_type == sym->id_type){
					flag_finished = 1;
					p->nxt->lines[p->nxt->top] = sym->lines[0];
					p->nxt->top++;
				}
			}
			p = p->nxt; 
		}
		if (flag_finished == 0){
			p->nxt = sym;
		}
	}
}

void line_upgrade(int newLine, Symbol *sym) {
	if(sym->lines[sym->top-1] != newLine) { 	// Evitar repetição de linhas iguais
		sym->lines[sym->top] = newLine;
		sym->top++;
		if(TabGenFeedBack) printf("Número de linhas atualizado\n");
	}
}

Symbol *allocateSymbol(char *id, IDType id_kind, char *data_type, char *scope, int size, int line, TreeNode *node) {
	int i;	
	Symbol *newSymbol = (Symbol*)malloc(sizeof(Symbol));
	newSymbol->ID = id;
	newSymbol->id_type = id_kind;
	newSymbol->data_type = data_type;
	newSymbol->scope = scope;
	newSymbol->size = size;
	for(i = 0; i < 50; i++) {
		newSymbol->lines[i] = 0;	
	}
	newSymbol->lines[0] = line;
	newSymbol->top = 1;
	newSymbol->im_add = -1;
	newSymbol->node = node;
	newSymbol->nxt = NULL;
	if(TabGenFeedBack) {
		printf("---------------------------------\n");		
		printf("ID: %s\n",newSymbol->ID);
		//printf("Classe: %s\n",newSymbol->id_kind);
		printf("Tipo de Dados: %s\n",newSymbol->data_type);
		printf("Escopo: %s\n",newSymbol->scope);
		printf("Tamanho: %d\n",newSymbol->size);
		printf("Linha: %d\n",newSymbol->lines[0]);
		printf("Tree Address: %p\n",newSymbol->node);
		printf("---------------------------------\n");	
	}
	return(newSymbol);
}

void printHash() {
	int i;
	Symbol *s = NULL; 	
	for(i = 0; i < hash_size; i++) {
		s = HashVec[i].begin;
		if(s != NULL) {
			printf("[%d] ",i);
			while(s != NULL) {
				printf("%s->", s->ID);
				s = s->nxt;
			}
			printf("\n");
		}
	}
		printf("\n");		
}

void TabGen(TreeNode *tree) {
	Symbol *newSymbol = NULL;
	Symbol *p = NULL;
	TreeNode *temp;
	int key;
	if(tree != NULL){
		// printf("LINHA: %d\n",tree->lineno);
		switch(tree->nodekind){
			case ExpK:
				switch(tree->kind.exp){
					case IdK:
					key = hash_calc(tree->attr.name);
					// printf("ID: %s do tipo ",tree->attr.name);
					// printf("%s.\n",returnIDType(tree->id_type));
						switch(tree->id_type){
							case Call: //caso seja id de chamada de funcao
								if (!strcmp(tree->attr.name,"main")){
									if(ShowSemanticalErrors) printf("Erro Semântico na linha %d: a 'main' nao pode ser chamada recursivamente. \n",tree->lineno);
									semantical_error = 1;
								}else{
									if (search_symbol(tree->attr.name,"Global",key,FuncDecl) == 0){//verifica se ja foi declarada, a gramatica so permite funcoes declaradas com escopo global
										if(ShowSemanticalErrors) printf("Erro Semântico na linha %d: funcao ",tree->lineno);
										if(ShowSemanticalErrors) printf("'%s' nao declarada.\n",tree->attr.name);
										semantical_error = 1;
										//função foi chamada mas nunca foi declarada
									}else{
										temp = return_node_symbol(tree->attr.name,"Global",key,FuncDecl);
										TreeNode* t = temp->child[0];
										TreeNode* r = tree->child[0];
										while(t!=NULL){
											if (r!=NULL){
												/*as variaveis por default recebem void, essa verificacao eh realizada quando for analisar a variavel la em baixo
												if (t->child[0]->type == r->type){
													/* DO NOTHING, EXPECTED RESULT
												}else{
													if(ShowSemanticalErrors) printf("Erro Semântico na linha %d: Atributo ",tree->lineno);
													if(ShowSemanticalErrors) printf("'%s' do tipo ",r->attr.name);
													if(ShowSemanticalErrors) printf("%s na chamada ",returnType(r->type));
													if(ShowSemanticalErrors) printf("'%s' deveria ser do tipo ",tree->attr.name);
													if(ShowSemanticalErrors) printf("%s .\n",returnType(t->child[0]->type));
													break;  //Erro semantico de tipos diferentes entre a declaracao e chamada.
												}*/
											}else{
												if(ShowSemanticalErrors) printf("Erro Semântico na linha %d: Falta o atributo ",tree->lineno);
												if(ShowSemanticalErrors) printf("'%s' do tipo ",t->child[0]->attr.name);
												if(ShowSemanticalErrors) printf("%s na chamada ",returnType(t->child[0]->type));
												if(ShowSemanticalErrors) printf("'%s' .\n",tree->attr.name);
												semantical_error = 1;
												break;    //Erro semantico de falta de atributo
											}
											r = r->sibling;
											t = t->sibling;
										}
										if (r==NULL){
											newSymbol = allocateSymbol(tree->attr.name,tree->id_type,returnType(tree->type),tree->scope,1,tree->lineno,tree);
											insert_symbol(newSymbol,key);
											//Aloca um simbolo, nao existe erro.
										}else{
											if(ShowSemanticalErrors) printf("Erro Semântico na linha %d: Excesso do atributo ",tree->lineno);
											if(ShowSemanticalErrors) printf("'%s' do tipo ",t->child[0]->attr.name);
											if(ShowSemanticalErrors) printf("%s na chamada ",returnType(t->child[0]->type));
											if(ShowSemanticalErrors) printf("'%s' .\n",tree->attr.name);
											semantical_error = 1;
											//Erro semantico de excesso de parametros.
										}
									}
								}
								break;
							case FuncAttrVar:
							case FuncAttrVector:
							case VarDecl:
								if (tree->type == Void){
									if(ShowSemanticalErrors) printf("Erro Semântico na linha %d: Existe um(a) ",tree->lineno);
									if(ShowSemanticalErrors) printf("%s ",returnIDType(tree->id_type));
									if(ShowSemanticalErrors) printf("'%s' declarada como Void.\n",tree->attr.name);
									semantical_error = 1;
								}else{
									if (search_symbol_decl(tree->attr.name,key, tree->id_type ,tree->scope) != 0){
										temp = return_node_symbol_decl(tree->attr.name,key,tree->id_type ,tree->scope, tree->scope_number);
										if(ShowSemanticalErrors) printf("Erro Semântico na linha %d: Existe um(a) ",tree->lineno);
										if(ShowSemanticalErrors) printf("'%s' que ja foi declarada com mesmo nome ",returnIDType(temp->id_type));
										if(ShowSemanticalErrors) printf("'%s' na linha ",tree->attr.name);
										if(ShowSemanticalErrors) printf("%d . \n",temp->lineno);
										semantical_error = 1;
										//ja existe outra declaracao no mesmo escopo
									}else{
										newSymbol = allocateSymbol(tree->attr.name,tree->id_type,returnType(tree->type),tree->scope,1,tree->lineno,tree);
										insert_symbol(newSymbol,key);									
									}
								}
								break;
							case VectorDecl:
								if (tree->type == Void){
									if(ShowSemanticalErrors) printf("Erro Semântico na linha %d: Existe um(a) ",tree->lineno);
									if(ShowSemanticalErrors) printf("%s ",returnIDType(tree->id_type));
									if(ShowSemanticalErrors) printf("'%s' declarada como Void.\n",tree->attr.name);
									semantical_error = 1;
								}else{
									if (search_symbol_decl(tree->attr.name,key, tree->id_type ,tree->scope) != 0){
										temp = return_node_symbol_decl(tree->attr.name,key,tree->id_type ,tree->scope, tree->scope_number);
										if(ShowSemanticalErrors) printf("Erro Semântico na linha %d: Existe um(a) ",tree->lineno);
										if(ShowSemanticalErrors) printf("'%s' que ja foi declarada com mesmo nome ",returnIDType(temp->id_type));
										if(ShowSemanticalErrors) printf("'%s' na linha ",tree->attr.name);
										if(ShowSemanticalErrors) printf("%d . \n",temp->lineno);
										semantical_error = 1;
										//ja existe outra declaracao no mesmo escopo
									}else{
										newSymbol = allocateSymbol(tree->attr.name,tree->id_type,returnType(tree->type),tree->scope,1,tree->lineno,tree);
										insert_symbol(newSymbol,key);									
									}
								}
								break;
							case FuncDecl:
								if (search_symbol_decl(tree->attr.name,key, tree->id_type ,tree->scope) != 0){
									temp = return_node_symbol_decl(tree->attr.name,key,tree->id_type ,tree->scope, tree->scope_number);
									if(ShowSemanticalErrors) printf("Erro Semântico na linha %d: Existe uma ",tree->lineno);
									if(ShowSemanticalErrors) printf("'%s' que ja foi declarada com mesmo nome na linha ",returnIDType(tree->id_type));
									if(ShowSemanticalErrors) printf("%d . \n",temp->lineno);
									semantical_error = 1;
									//ja existe outra declaracao no mesmo escopo
								}else{
									newSymbol = allocateSymbol(tree->attr.name,tree->id_type,returnType(tree->type),tree->scope,1,tree->lineno,tree);
									insert_symbol(newSymbol,key);									
								}
								break;
							case VectorPos:
								if (search_symbol_var_decl(tree->attr.name,key,tree->id_type,tree->scope,tree->scope_number) == 0){
									if(ShowSemanticalErrors) printf("Erro Semântico na linha %d: O ",tree->lineno);
									if(ShowSemanticalErrors) printf("%s ",returnIDType(tree->id_type));
									if(ShowSemanticalErrors) printf("'%s' esta sendo utilizado porem nao foi declarado. \n",tree->attr.name);
									semantical_error = 1;
								}else{
									temp = return_node_search_symbol_var_decl(tree->attr.name,key,tree->id_type,tree->scope,tree->scope_number);
									if(temp->id_type == VarDecl){
										if(ShowSemanticalErrors) printf("Erro Semântico na linha %d: O ",tree->lineno);
										if(ShowSemanticalErrors) printf("%s ",returnIDType(tree->id_type));
										if(ShowSemanticalErrors) printf("'%s' eh vetor quando era para ser variável de acordo com a linha ",tree->attr.name);
										if(ShowSemanticalErrors) printf("%d .\n",temp->lineno);
										semantical_error = 1;
									}else{
										if (temp->id_type == FuncAttrVar){
											if(ShowSemanticalErrors) printf("Erro Semântico na linha %d: O ",tree->lineno);
											if(ShowSemanticalErrors) printf("%s ",returnIDType(tree->id_type));
											if(ShowSemanticalErrors) printf("'%s' eh vetor quando era para ser variável de acordo com a linha  ",tree->attr.name);
											if(ShowSemanticalErrors) printf("%d .\n",temp->lineno);
											semantical_error = 1;
										}else{
											if (tree->child[0]->kind.exp == NumK){
												if (temp->child[0]->attr.val<(tree->child[0]->attr.val+1)){
													if(ShowSemanticalErrors) printf("Erro Semântico na linha %d: O ",tree->lineno);
													if(ShowSemanticalErrors) printf("%s ",returnIDType(tree->id_type));
													if(ShowSemanticalErrors) printf("'%s' esta sendo acessado uma posicao maior que a declarada. \n",tree->attr.name);
													semantical_error = 1;
												}else{
													newSymbol = allocateSymbol(tree->attr.name,tree->id_type,returnType(temp->type),tree->scope,1,tree->lineno,tree);
													insert_symbol(newSymbol,key);
												}
											}else{
												newSymbol = allocateSymbol(tree->attr.name,tree->id_type,returnType(temp->type),tree->scope,1,tree->lineno,tree);
												insert_symbol(newSymbol,key);
											}
										}										
									}
								}
								break;
							case Var:
								if (search_symbol_var_decl(tree->attr.name,key,tree->id_type,tree->scope,tree->scope_number) == 0){
									if(ShowSemanticalErrors) printf("Erro Semântico na linha %d: A ",tree->lineno);
									if(ShowSemanticalErrors) printf("%s ",returnIDType(tree->id_type));
									if(ShowSemanticalErrors) printf("'%s' esta sendo utilizado porem nao foi declarada. \n",tree->attr.name);
									semantical_error = 1;
								}else{
									temp = return_node_search_symbol_var_decl(tree->attr.name,key,tree->id_type,tree->scope,tree->scope_number);
									
									if((temp->id_type == VarDecl)||(temp->id_type == FuncAttrVar)){
										newSymbol = allocateSymbol(tree->attr.name,tree->id_type,returnType(temp->type),tree->scope,1,tree->lineno,tree);
										insert_symbol(newSymbol,key);										
									}else{
										if(ShowSemanticalErrors) printf("Erro Semântico na linha %d: A ",tree->lineno);
										if(ShowSemanticalErrors) printf("%s ",returnIDType(tree->id_type));
										if(ShowSemanticalErrors) printf("'%s' eh variavel quando era para ser vetor de acordo com a linha ",tree->attr.name);
										if(ShowSemanticalErrors) printf("%d .\n",temp->lineno);
										semantical_error = 1;
									}
								}
								break;
						}					
						break;
				}
				break;	
			case StmtK:
				switch(tree->kind.stmt){
					case IfK:
						break;
					case WhileK:
						break;
					case AssignK:
						break;
					case ReturnK:
						break;
				}
				break;
		}
		if (semantical_error == 0) TabGen(tree->child[0]);
		if (semantical_error == 0) TabGen(tree->child[1]);
		if (semantical_error == 0) TabGen(tree->child[2]);
		if (semantical_error == 0) TabGen(tree->sibling);
	}
}

char* verify_Op(TreeNode *tree){
	TreeNode *temp;
	int key;					
							char* type_1;
							char* type_2;
							if (tree->child[0]->kind.exp == OpK){
								type_1 = verify_Op(tree->child[0]);
							}else{
								if (tree->child[0]->kind.exp == NumK){
									type_1 = returnType(tree->child[0]->type);
								}else{
									key = hash_calc(tree->child[0]->attr.name);
									Symbol* temp = return_symbol_decl(tree->child[0]->attr.name, key, tree->child[0]->id_type, tree->child[0]->scope,tree->child[0]->scope_number);
									if (temp == NULL){
										type_1 = "Integer";
									}else type_1 = temp->data_type;
								}
							}
							if (tree->child[1]->kind.exp == OpK){
								type_2 = verify_Op(tree->child[1]);
							}else{
								if (tree->child[1]->kind.exp == NumK){
									type_2 = returnType(tree->child[1]->type);
								}else{
									key = hash_calc(tree->child[1]->attr.name);
									Symbol* temp = return_symbol_decl(tree->child[1]->attr.name, key, tree->child[1]->id_type, tree->child[1]->scope,tree->child[1]->scope_number);
									if (temp == NULL){
										type_2 = "Integer";
									}else type_2 = temp->data_type;
								}
							}
							//aqui verifica os tipos de variaveis
							if(!strcmp(type_1, type_2)){
								return type_1;
							}else{
								return "Integer";//retorna inteiro
							}
													
}

void TabGen_verify(TreeNode *tree) {
	Symbol *newSymbol = NULL;
	Symbol *p = NULL;
	int key;
	if(tree != NULL){
		switch(tree->nodekind){
			case ExpK:
				switch(tree->kind.exp){	
					case OpK:
							char* type_1;
							char* type_2;
							
							if (tree->child[0]->kind.exp == OpK){
								type_1 = verify_Op(tree->child[0]);
							}else{
								if (tree->child[0]->kind.exp == NumK){
									type_1 = returnType(tree->child[0]->type);
								}else{
									key = hash_calc(tree->child[0]->attr.name);
									Symbol* temp = return_symbol_decl(tree->child[0]->attr.name, key, tree->child[0]->id_type, tree->child[0]->scope,tree->child[0]->scope_number);
									if (temp == NULL){
										type_1 = "Integer";
									}else type_1 = temp->data_type;
								}
							}
							
							if (tree->child[1]->kind.exp == OpK){
								type_2 = verify_Op(tree->child[1]);
							}else{
								if (tree->child[1]->kind.exp == NumK){
									type_2 = returnType(tree->child[1]->type);
								}else{
									key = hash_calc(tree->child[1]->attr.name);
									Symbol* temp = return_symbol_decl(tree->child[1]->attr.name, key, tree->child[1]->id_type, tree->child[1]->scope,tree->child[1]->scope_number);
									if (temp == NULL){
										type_2 = "Integer";
									}else type_2 = temp->data_type;
								}
							}
							
							if(!strcmp(type_1, type_2)){
								
							}else{
								if(ShowSemanticalErrors) printf("Erro Semântico na linha %d: A operacao",tree->lineno);
								if(ShowSemanticalErrors) printf("%s esta sendo realizada entre dois operandos de tipos de dados diferentes.",returnOp(tree->attr.op));
								if(ShowSemanticalErrors) printf("'%s' com ",type_1);
								if(ShowSemanticalErrors) printf("%s .\n",type_2);
								semantical_error = 1;
							}
						break;
				}
				break;
		}
		if (semantical_error == 0) TabGen_verify(tree->child[0]);
		if (semantical_error == 0) TabGen_verify(tree->child[1]);
		if (semantical_error == 0) TabGen_verify(tree->child[2]);
		if (semantical_error == 0) TabGen_verify(tree->sibling);
	}
}

void TabGen_statement(TreeNode *tree) {//
	Symbol *newSymbol = NULL;
	Symbol *p = NULL;
	TreeNode* temp;
	int key;
	if(tree != NULL){
		// printf("LINHA statement: %d\n",tree->lineno);
		switch(tree->nodekind){
			case StmtK:{
				switch(tree->kind.stmt){
					case IfK:{
						if (tree->child[1]!=NULL){
							if(tree->child[1]->kind.exp == IdK){
								if(!strcmp(tree->child[1]->attr.name,"break")){
									if(ShowSemanticalErrors) printf("Erro Semântico na linha %d: break nao esta contido em um loop ou switch.\n",tree->child[0]->lineno);
									semantical_error = 1;
								}else{
									if(!strcmp(tree->child[1]->attr.name,"continue")){
										if(ShowSemanticalErrors) printf("Erro Semântico na linha %d: break nao esta contido em um loop ou switch.\n",tree->child[0]->lineno);
										semantical_error = 1;
									}
								}
							}
						}
						if (tree->child[2]!=NULL){	
							if(tree->child[1]->kind.exp == IdK){
								if(!strcmp(tree->child[2]->attr.name,"break")){
									if(ShowSemanticalErrors) printf("Erro Semântico na linha %d: break nao esta contido em um loop ou switch.\n",tree->child[1]->lineno);
									semantical_error = 1;
								}else{
									if(!strcmp(tree->child[2]->attr.name,"continue")){
										if(ShowSemanticalErrors) printf("Erro Semântico na linha %d: break nao esta contido em um loop ou switch.\n",tree->child[1]->lineno);
										semantical_error = 1;
									}
								}
							}
						}
						break;
					}
					
					case AssignK:{
						Symbol *temp_symbol;
						key = hash_calc(tree->child[0]->attr.name);
						temp_symbol = return_symbol_decl(tree->child[0]->attr.name, key, tree->child[0]->id_type, tree->child[0]->scope,tree->child[0]->scope_number);
						char* type_var = temp_symbol->data_type;
						char* type;
						int i = 0;
						if (tree->child[1]->kind.exp == OpK){
							type = verify_Op(tree->child[1]);
						}else{
							if (tree->child[1]->kind.exp == NumK){
								type = returnType(tree->child[1]->type);
							}else{
								key = hash_calc(tree->child[1]->attr.name);
								switch(tree->child[1]->id_type){
									case Call:{
										temp_symbol = return_symbol(tree->child[1]->attr.name, "Global", key, FuncDecl);
										break;
									}
									case Var:{
										temp_symbol = return_symbol_decl(tree->child[1]->attr.name, key, tree->child[1]->id_type, tree->child[1]->scope,tree->child[1]->scope_number);
										break;
									}
								}
								if (temp_symbol == NULL){
									type = "Integer";
								}else type = temp_symbol->data_type;
								i =  1;
							}
						}
						if(strcmp(type_var,type)){
							if(i){
								if (!strcmp(type,"Void")){
									if(ShowSemanticalErrors) printf("Erro Semântico na linha %d: Esta associando uma funcao que retorna 'void' para uma variavel.\n",tree->child[0]->lineno); 
									semantical_error = 1;
								}else{
									if(ShowSemanticalErrors) printf("Erro Semântico na linha %d: O valor retornado sera truncado (tipos diferentes de dados).\n",tree->child[0]->lineno); 
									semantical_error = 1;
								}
							}else{
								if(ShowSemanticalErrors) printf("Erro Semântico na linha %d: O valor retornado sera truncado (tipos diferentes de dados).\n",tree->child[0]->lineno); 
								semantical_error = 1;
							}
						}
						break;
					}
					
					case ReturnK:  
						int function_scope_number = (floor(tree->scope_number/200))*200;		
						temp = return_Func_Decl(savedTree,function_scope_number);
						 
						if(temp->type == Void){
							if (tree->child[0]){
								if(ShowSemanticalErrors) printf("Erro Semântico na linha %d: Nao deveria existir return para a funcao do tipo void.\n",tree->lineno);
								semantical_error = 1;
							}
						}else{
							char* type;
							if (tree->child[0]->kind.exp == OpK){
								type = verify_Op(tree->child[0]);
							}else{
								if (tree->child[0]->kind.exp == NumK){
									type = returnType(tree->child[0]->type);
								}else{
									key = hash_calc(tree->child[0]->attr.name);
									Symbol* temp = return_symbol_decl(tree->child[0]->attr.name, key, tree->child[0]->id_type, tree->child[0]->scope,tree->child[0]->scope_number);
									type = temp->data_type;
								}
							}
							if(strcmp(returnType(temp->type),type)){
								if(ShowSemanticalErrors) printf("Erro Semântico na linha %d: O valor retornado sera truncado (tipos diferentes de dados).\n",tree->child[0]->lineno); 
								semantical_error = 1;
							}
						}
						break;
				}
				break;
			}		
		}
		if (semantical_error == 0) TabGen_statement(tree->child[0]);
		if (semantical_error == 0) TabGen_statement(tree->child[1]);
		if (semantical_error == 0) TabGen_statement(tree->child[2]);
		if (semantical_error == 0) TabGen_statement(tree->sibling);
	}
}

void TabGen_verify_main(TreeNode *tree) {
	TreeNode* temp = verify_main(tree);
	if (temp == NULL) {
		if(ShowSemanticalErrors) printf("Erro Semântico no codigo: Não existe uma funcao 'main'.\n"); 
		semantical_error = 1;
	}
}

void printWTable(int index) {
  int i;
  Symbol *p = HashVec[index].begin;
  while(p!=NULL){
      i = 0;
	  if(p->lines[0] != 0) {
		 fprintf(listing,"%-16d  %-16s %-16s %-19s %-12s ", index, p->ID, returnIDType(p->id_type), p->data_type, p->scope);
				//if(p->id_type!=FuncDecl)  fprintf(listing,"\t%d (IM)\t\t",p->im_add);
				//else  fprintf(listing,"\t%d (GDM)\t\t",p->mem_add);
        while(p->lines[i]!=0){
		  fprintf(listing,"%d", p->lines[i]);
		  if(i < p->top-1) fprintf(listing,", ");
		  i++;
        }			
         fprintf(listing,"\n");
      }
        p = p->nxt;
  }
}

void printTable() {
	fprintf(listing,"\n***********************************************************************************************************************\n");
	fprintf(listing,"*************************************************************************************************************************\n");
	fprintf(listing,"****************************************  TABELA DE SIMBOLOS  ***********************************************************\n");
	fprintf(listing,"*************************************************************************************************************************\n");
	fprintf(listing,"*************************************************************************************************************************\n\n");
	fprintf(listing,"|-----------------------------------------------------------------------------------------------------------------------|\n");
	fprintf(listing,"| Entrada   +   Nome do ID   +   Tipo de ID   +   Tipo de Dados   +     Escopo   +   Linhas   |\n");
	fprintf(listing,"|-----------------------------------------------------------------------------------------------------------------------|\n");	
	int i;	
	for(i = 0;i<211;i++){
    if(&HashVec[i] != NULL)
    printWTable(i);
	}
}

void SymTabGen() {
	TabGen_verify_main(savedTree);
	TabGen(savedTree);
	TabGen_verify(savedTree);
	TabGen_statement(savedTree);
}

/************************************************************************/
/************************************************************************/
/************************************************************************/
/************************************************************************/
/************************************************************************/
/****************** Gerador de Codigo Intermediario *********************/
/************************************************************************/
/************************************************************************/
/************************************************************************/
/************************************************************************/

typedef enum {LD, ST, COND_IF, COND_IF_F, LOOP_WHILE, LOOP_WHILE_F, INTCODE_ADD, INTCODE_SUB, INTCODE_MUL, INTCODE_DIV, INTCODE_LT, INTCODE_LEQ, INTCODE_GT, INTCODE_GEQ, INTCODE_EQ, INTCODE_NEQ, INTCODE_ASSIGN, INTCODE_RET} OpKind;

typedef enum {Vazio, ConstInt, String} AddrKind; //diz qual o tipo de dado que esta no no da lista. Serve para alocar a quantidade correta de bits para o dado.

typedef struct 
{
	AddrKind kind;
	union 
	{
		int val;
		char *nome;
	}contents;
}Address;


typedef struct quad_addr
{
	OpKind op;
	Address val1, val2, res;
}Quad_Cell;

typedef struct quad_addr_lista
{
	Quad_Cell quad;
	quad_addr_lista* next,* prev;
}Quad_List;

Quad_List * AlocaQuad(OpKind op, Address val1, Address val2, Address res)
{
	Quad_List* aux = (Quad_List*) malloc(sizeof(Quad_List));
	Quad_Cell q;
	q.op = op;
	q.val1 = val1;
	q.val2 = val2;
	q.res = res;
	aux->quad = q;
	aux->next = NULL;
	aux->prev = NULL;
	return aux;
}

Quad_List * codigo_inter;

void insereBloco(OpKind op, Address val1, Address val2, Address res)
{
	
	if(codigo_inter == NULL)
		{
			codigo_inter = AlocaQuad(op, val1, val2, res);
		}
		else{
			Quad_List* aux, *aux2;
			aux = codigo_inter;
			while(aux->next!=NULL) aux = aux->next;
			aux2 = AlocaQuad(op, val1, val2, res);
			aux->next = aux2;
		}
}


int tempVariableCounter = 0;
char str[50];
char str_array[50];

FILE *fp = fopen("IntermediateCode.txt", "w+");

int ehFolhaInterm(TreeNode* root)
{
	int folhaFlag = 0;
	for(int i = 0; i<MAXCHILDREN;i++)
	{
		if(root->child[i]==NULL) folhaFlag = 1;
		else return 0;
		//printf("FOR: folhaFlag(filho)%d\n", folhaFlag);
	}
	return folhaFlag;
}
int paiDeFolhas(TreeNode* root) //precisa atualizar pra IF e pra While
{
	int folhaFlag = 0;
	if(root->kind.exp == OpK){
		for	(int i = 0; i<2;i++)
		{
			if(ehFolhaInterm(root->child[i])) folhaFlag = 1;
			else return 0;
			//printf("FOR: folhaFlag(pai)%d\n", folhaFlag);
		}
	}
	//printf("folhaFlag(pai)%d\n", folhaFlag);
	return folhaFlag;
}

char* returnToken(OpKind op)
{
	switch(op){
		case INTCODE_ADD: 		{return "ADD"		;break;}
		case INTCODE_SUB: 		{return "SUB"		;break;}
		case INTCODE_MUL: 		{return "MULT"		;break;}
		case INTCODE_DIV: 		{return "DIV"		;break;}
		case INTCODE_EQ:	 	{return "EQUAL"		;break;}
		case INTCODE_NEQ:	 	{return "NEQUAL"	 	;break;}
		case INTCODE_GEQ:		{return "GREATEQ" 	;break;}
		case INTCODE_GT: 		{return "GREAT"		;break;}
		case INTCODE_LT: 		{return "LESS"	 	;break;}
		case INTCODE_LEQ: 		{return "LESSEQ" 	;break;}
		case INTCODE_ASSIGN: 	{return "LOAD"		;break;}
	}
}


int labelCounter = 0;

int tempVarCounter = 0;

char toFile[100];

char tempVar[50];

char labels[10]; 

void CodeGen(TreeNode* root);

char jump[] = "GOTO";

int FUNCTION_SEARCH = 0;


Address processExp(TreeNode* root);

//Args eh um ponteiro de address que vai indicar o comeco do array de argumentos
//retorna um int indicando quantos argumentos tem
void genArguments(TreeNode* root) //funcao retorna um array de 
{
	Address arg;
	TreeNode* aux;
	aux = root;
	while(aux != NULL)
	{
		if(aux->codeGen!=1)
		{
			arg = processExp(aux);
			if(arg.kind == String)fprintf(fp, "(%s,%s,_,_)\n", "ARGUMENT",arg.contents.nome );
			if(arg.kind == ConstInt) fprintf(fp, "(%s,%d,_,_)\n", "ARGUMENT",arg.contents.val );
			aux->codeGen = 1;
		}
		aux = aux->sibling;
	}
}


char* FUNCTION_RETURN;

int findFuncRetVal(char* nome)
{
	char stream[50], *ret;
	fseek(fp, 0, SEEK_SET);
	while(feof(fp) == 0)
	{
		
		ret = fgets(stream, 50, fp);
		ret = strstr(stream, nome);
		if(ret != NULL )
		{
			while(1)
			{
				ret = fgets(stream, 50, fp);
				if(ret == NULL)
				{
					//fseek(fp, 0, SEEK_END);
					break;
				}
				else
				{
					ret = strstr(stream, "ret");
					if(ret!=NULL)
					{
						//achou o argumento de retorno da funcao Nome
						FUNCTION_RETURN = strtok(stream, "(ret,");
						if(FUNCTION_RETURN!=NULL) 
						{
							FUNCTION_SEARCH = 1;
							fseek(fp, 0, SEEK_END);
							//fflush(fp);
							return 1;
						}
					}
				}
			}
		}
	}
	FUNCTION_SEARCH = 0;
	fseek(fp, 0, SEEK_END);
	return 0;
}

Address processExp(TreeNode* root)
{
	if(root!=NULL)
	{
		switch(root->nodekind)
		{
			
			case ExpK:
			{
				///operacoes matematicas e logicas em pos-ordemmake
				///primeiro trata os dois filhos, depois trata a raiz
				
				switch(root->kind.exp)
				{
					case OpK:
					{
						Address *temp;
						Address op1, op2;
						char charOp1[50], charOp2[50];
						//if abaixo trata arrays. Nao muda se nao buga.
						if(root->child[0]->id_type == VectorPos && root->child[1]->id_type == VectorPos) 
						{
							op1 = processExp(root->child[0]);
							if(op1.kind == String)sprintf(charOp1, "%s", op1.contents.nome);
							if(op1.kind == ConstInt)sprintf(charOp1, "%d", op1.contents.val);
							op1.contents.nome = charOp1;
							op2 = processExp(root->child[1]);
							if(op2.kind == String)sprintf(charOp2, "%s", op2.contents.nome);
							if(op2.kind == ConstInt)sprintf(charOp2, "%d", op2.contents.val);
							op2.contents.nome = charOp2;
							
						}
						else 
						{
							op1 = processExp(root->child[0]);///filho esquerdo tratado
							switch(op1.kind)
							{
								case ConstInt:
								{
									break;
								}
								case String:
								{
									if(op1.contents.nome == NULL)
									{
										///indica que os filho da direita eh um operador.
										///como resgatar o temporario antigo.
										op1.contents.nome = temp->contents.nome;
									}
									break;
								}
								case Vazio:
								{
								}
							}
							op2 = processExp(root->child[1]);///filho direito tratado
							//if(root->child[1]->id_type ==  VectorPos) printf("RETORNO DO processExp(): %s\n", op2.contents.nome);
							switch(op2.kind)
							{
								case ConstInt:
								{
									//printf("OP2 EH INT\n");
									break;
								}
								case String:
								{
									//printf("OP2 EH STRING\n");
									if(op2.contents.nome == NULL)
									{
										///indica que os filho da direita eh um operador.
										///como resgatar o temporario antigo.
										op2.contents.nome = temp->contents.nome;
									}
									break;
								}
								case Vazio:
								{
									//printf("OP2 EH VAZIO\n");
									break;
								}
							}
						}
						if(root->child[0]->id_type == VectorPos && root->child[1]->id_type == VectorPos) 
						{
							if(op1.kind!=Vazio && op2.kind!=Vazio)
							{
								//printf("nome: %s\n", op1.contents.nome);
								//printf("nome: %s\n", op2.contents.nome);
							}
						}
						//if(op2.kind == ConstInt)printf("num: %d\n", op2.contents.val);
						if(op1.kind == Vazio) break;
						if(op2.kind == Vazio) break;
						OpKind op;///tratamento de raiz
						switch (root->attr.op) ///descobre o operando
						{
							case ADD: 		{op = INTCODE_ADD;		break;}
							case SUB: 	{op = INTCODE_SUB;		break;}
							case MULT: 		{op = INTCODE_MUL;		break;}
							case DIV: 		{op = INTCODE_DIV;		break;}
							case EQUAL:	 	{op = INTCODE_EQ;		break;}
							case NEQUAL:	 	{op = INTCODE_NEQ;		break;}
							case GREATEQ:	{op = INTCODE_GEQ;		break;}
							case GREAT: 	{op = INTCODE_GT;		break;}
							case LESS: 		{op = INTCODE_LT;		break;}
							case LESSEQ: 	{op = INTCODE_LEQ;		break;}
							default:
							{
								exit(1);
							}
						}
						///gera um temporario pra armazenar o resultado;
						sprintf(tempVar, "TEMP%d", tempVarCounter);
						tempVarCounter++;
						char *local_tempVar = (char*)malloc(sizeof(char)*50);
						for(int i = 0; i<50; i++)
						{
							local_tempVar[i] = tempVar[i];
						}
						
						if(op1.kind == String && op2.kind == String)sprintf(toFile, "(%s,%s,%s,%s)\n", returnToken(op), op1.contents.nome, op2.contents.nome, tempVar);
						if(op1.kind == ConstInt && op2.kind == String)sprintf(toFile, "(%s,%d,%s,%s)\n", returnToken(op), op1.contents.val, op2.contents.nome, tempVar);
						if(op1.kind == String && op2.kind == ConstInt)sprintf(toFile, "(%s,%s,%d,%s)\n", returnToken(op), op1.contents.nome, op2.contents.val, tempVar);
						if(op1.kind == ConstInt && op2.kind == ConstInt)sprintf(toFile, "(%s,%d,%d,%s)\n", returnToken(op), op1.contents.val, op2.contents.val, tempVar);
						fprintf(fp, "%s", toFile);
						Address retVal;
						retVal.contents.nome = local_tempVar;
						retVal.kind = String;
						root->codeGen = 1;
						return retVal;
						break;
					}
					case NumK:
					{
						Address returnVal;
						if(root->codeGen != 1){
							Address returnVal;
							returnVal.contents.val = root->attr.val;
							returnVal.kind = ConstInt;
							root->codeGen = 1;
							return returnVal;
						}
						returnVal.kind = Vazio;
						return returnVal;
						break;
					}
					case IdK:
					{
						if(root->id_type == FuncDecl)
						{
							if(root->codeGen != 1)
							{
								char * entrada = "FUNCTION_DEF";
								fprintf(fp, "(%s,%s,_,_)\n", entrada, root->attr.name);
								if(root->child[1]!=NULL)CodeGen(root->child[1]); //primeiro filho da funcao tem parametros, segundo tem codigo
								// else fprintf(fp, "(nop,_,_,_)\n");
								//root->codeGen = 1;
							}
						}
						else if(root->id_type == Call)
						{
							Address returnVal;
							if(root->codeGen != 1)
							{
								TreeNode* aux;
								char * entrada = "FUNCTION_CALL";
								if(root->child[0]!=NULL)fprintf(fp, "(BEGIN_ARGS,_,_,_)\n");//funcao sem argumentos
								if(root->child[0]!=NULL && root->child[0]->nodekind == ExpK)
								{///indica que o argumento da funcao eh outra funcao.
								 ///precisa armazenar o temporario que vai servir de retorno para a avaliacao da funcaoArgumento
									sprintf(tempVar, "TEMP%d", tempVarCounter);
									tempVarCounter++;
								}
								genArguments(root->child[0]); //primeiro filho da funcao tem parametros, segundo tem codigo
								///pra gerar o codigo de return, eu preciso descobrir o que a funcao retorna. Como?
								///da pra percorrer a arvores e achar o no de retorno da funcao.
								fprintf(fp, "(%s,%s,_,_)\n", entrada, root->attr.name);
								//printf("procurando funcao:%s\n", root->attr.name);
								int t = findFuncRetVal(root->attr.name);
								if(t)
								{
									returnVal.kind = String;
									returnVal.contents.nome = FUNCTION_RETURN;
									//FUNCTION_RETURN = NULL;
								}
								root->codeGen = 1;
								return returnVal;
							}
							returnVal.kind = Vazio;
							return returnVal;
						}
						else if(root->id_type == VectorPos)
						{
							Address returnVal;
							if(root->codeGen != 1)
							{
								
								returnVal = processExp(root->child[0]);
								if(returnVal.kind == ConstInt){
									sprintf(str_array,"%s[%d]", root->attr.name,returnVal.contents.val);
									returnVal.contents.nome = str_array;
									returnVal.kind = String;
								}
								else
								{
									sprintf(str_array,"%s[%s]", root->attr.name,returnVal.contents.nome);
									returnVal.contents.nome = str_array;
								}
								root->codeGen = 1;
								return returnVal;
							}
							returnVal.kind = Vazio;
							return returnVal;
						}else
						{
							Address returnVal;
							if(root->codeGen != 1)
							{
								Address returnVal;
								returnVal.contents.nome = root->attr.name;
								returnVal.kind = String;
								root->codeGen = 1;
								return returnVal;
							}
							returnVal.kind = Vazio;
							return returnVal;
						}
						break;
					}
					case DeclTypeK:
					{
						break;
					}
					case MemVarK:
					{
						break;
					}
					default:
					{
						exit(1);
					}
				}
				break;
			}
			default: 
			{
				exit(1);
			}
		}
	}
}


Address processStmt(treeNode* root)
{
	switch(root->kind.stmt)
	{
		case AssignK:
		{
			if(root->codeGen!=1){
				Address tempEsq, tempDir;
				char charOp1[50], charOp2[50];
				///lado esquerdo so pode ser variavel ou veotr. Trivial.
				///lado direito pode ser expressao, variavel ou inteiro.
				///se chamar processExp deve funcionar de prima.
				///precisa armazenar o temporario que vai salvar a expressao do lado direito.
				if(root->child[0]->id_type == VectorPos && root->child[1]->id_type == VectorPos) 
				{
					tempEsq = processExp(root->child[0]);
					if(tempEsq.kind == String)sprintf(charOp1, "%s", tempEsq.contents.nome);
					if(tempEsq.kind == ConstInt)sprintf(charOp1, "%d", tempEsq.contents.val);
					tempEsq.contents.nome = charOp1;
					tempDir = processExp(root->child[1]);
					if(tempDir.kind == String)sprintf(charOp2, "%s", tempDir.contents.nome);
					if(tempDir.kind == ConstInt)sprintf(charOp2, "%d", tempDir.contents.val);
					//if(tempDir.kind != Vazio)printf("nome: %s\n", charOp2);
					tempDir.contents.nome = charOp2;
					
				}
				else
				{
					tempEsq = processExp(root->child[0]);
					tempDir = processExp(root->child[1]);
				}
				if(FUNCTION_SEARCH)
				{
					sprintf(charOp1, "%s", FUNCTION_RETURN);
					tempDir.contents.nome = charOp1;
					tempDir.kind = String;
					FUNCTION_SEARCH = 0;
				}
				if(tempEsq.kind == String && tempDir.kind == String)sprintf(toFile, "(%s,%s,%s,_)\n", "LOAD", tempEsq.contents.nome, tempDir.contents.nome);
				if(tempEsq.kind == ConstInt && tempDir.kind == String)sprintf(toFile, "(%s,%d,%s,_)\n", "LOAD", tempEsq.contents.val, tempDir.contents.nome);
				if(tempEsq.kind == String && tempDir.kind == ConstInt)sprintf(toFile, "(%s,%s,%d,_)\n", "LOAD", tempEsq.contents.nome, tempDir.contents.val);
				if(tempEsq.kind == ConstInt && tempDir.kind == ConstInt)sprintf(toFile, "(%s,%d,%d,_)\n", "LOAD", tempEsq.contents.val, tempDir.contents.val);
				fprintf(fp, "%s", toFile);
				
				root->codeGen = 1;
				
			}
			break;
		}
		case IfK:
		{
			if(root->codeGen!=1){
				Address ifCond;
				char labelTrue[10];
				char labelFalse[10];
				
				sprintf(labelFalse,"L%d", labelCounter);
				labelCounter++;
				sprintf(labelTrue,"L%d", labelCounter);
				labelCounter++;
				
				//Avalia Condicao
				ifCond = processExp(root->child[0]); ///pela definicao da gramatica so pode ter expressao na condicao do if.
				//if_false t1 goto l0
				fprintf(fp,"(IF_FALSE,%s,%s,_)\n", ifCond.contents.nome, labelFalse); //
				CodeGen(root->child[1]);//codigo para TRUE
				
				if(root->child[2]!=NULL)
				{
					fprintf(fp,"(%s,%s,_, _)\n", jump, labelTrue);//goto l1
					fprintf(fp,"(LABEL,%s,_,_)\n", labelFalse);//label
					CodeGen(root->child[2]);
					fprintf(fp,"(LABEL,%s,_,_)\n", labelTrue);
				}else
				{
					fprintf(fp,"(LABEL,%s,_,_) \n", labelFalse);
				}
				root->codeGen= 1;
			}
			
			break;
		}
		case WhileK:
		{
			if(root->codeGen!=1){
				Address whileCond;
				char labelContinue[10];
				char labelBreak[10];
				sprintf(labelContinue,"L%d", labelCounter);
				labelCounter++;
				sprintf(labelBreak,"L%d", labelCounter);
				labelCounter++;
				fprintf(fp,"(LABEL,%s,_,_)\n", labelContinue);
				whileCond = processExp(root->child[0]);
				fprintf(fp,"(IF_FALSE,%s,%s,_)\n", whileCond.contents.nome, labelBreak);
				CodeGen(root->child[1]);
				fprintf(fp,"(%s,%s,_,_)\n", jump, labelContinue);
				fprintf(fp,"(LABEL,%s,_,_)\n", labelBreak);
				root->codeGen= 1;
			}
			break;
		}
		case ReturnK:
		{
			if(root->codeGen!=1){
				if (root->child[0] != NULL){
					Address retVal;
					if(root->child[0]->id_type == Var || root->child[0]->id_type == VectorPos)
					{//indica que no return tem uma variavel ou um vetor. Precisa armazenar num temp
						sprintf(tempVar, "TEMP%d", tempVarCounter);
						tempVarCounter++;
						retVal.contents.nome = tempVar;
						retVal.kind = String;
						fprintf(fp,"(LOAD,%s,%s,_)\n", retVal.contents.nome, root->child[0]->attr.name);
					}	
					else
					{
						retVal = processExp(root->child[0]);
					}
					if(retVal.contents.nome == NULL)
						fprintf(fp,"(ret,_,_,_)\n");
					else 
					{
						if(retVal.kind == String)fprintf(fp,"(ret,%s,_,_)\n", retVal.contents.nome);
						if(retVal.kind == ConstInt)fprintf(fp,"(ret,%d,_,_)\n", retVal.contents.val);
					}
					root->codeGen= 1;
				}else{
					fprintf(fp,"(ret,_,_,_)\n");
					root->codeGen = 1;
				}
			}
			break;
		}
	}
}

void CodeGen(TreeNode* root)
{
	//processa
	if(root != NULL)
	{
		switch(root->nodekind)
		{
			
			case StmtK:
			{
				processStmt(root);
				break;
			}
			case ExpK:
			{
				///operacoes matematicas e logias em pos-ordem. Talvez usar notacao polonesa?
				///primeiro trata os dois filhos, depois trata a raiz
				///ExpK tambem pode ser declaracao de funcao. Se for IdK e id_type for FuncDecl eh declaracao de funcao. Tratado dentro do processExp();
				processExp(root);
				break;
			}
			default: 
			{
				exit(1);
			}
			
		}
		
		//caminha
		if(root->child[0] != NULL )CodeGen(root->child[0]);
		if(root->child[1] != NULL )CodeGen(root->child[1]);
		if(root->child[2] != NULL )CodeGen(root->child[2]);
		CodeGen(root->sibling);
	}
}


void generateIntermCode()
{
	CodeGen(savedTree);
	fprintf(fp,"(halt,_,_,_)\n");
}