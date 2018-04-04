/****************************************************/
/* File: analex2.l                                  */
/* The C- Yacc/Bison specification file             */
/*                                                  */
/* Lucas Vecchete                                   */
/****************************************************/

%{
#include "anasint2.tab.h"
#include <time.h>
char ids[30];
void abrirArq();
int lineno = 1;
#define verTypesPrint 0
#define printTreeEnable 1
#define ScannerFeedback 0

extern FILE* listing;

%}

digito [0-9]
number {digito}+
letra [a-zA-Z]
ID {letra}+({letra}|{digito})*
newline \n
carriage \r
whitespace [ \t]+
other	[^0-9a-zA-Z;/=\-"+""*""("")""\n"\[\]\,\{\}\<\>|!=\==\<=\>=]
%option yylineno
%option noyywrap
%%

"if"            {if(ScannerFeedback) printf("IF\n");return IF;}
"else"          {if(ScannerFeedback) printf("ELSE\n");return ELSE;}
"int"			{if(ScannerFeedback) printf("INT\n");return INT;}
"return"		{if(ScannerFeedback) printf("RETURN\n");return RETURN;}
"void"			{if(ScannerFeedback) printf("VOID\n");return VOID;}
"while"			{if(ScannerFeedback) printf("WHILE\n");return WHILE;}
"="             {if(ScannerFeedback) printf("ASSIGN\n");return ASSIGN;}
"=="            {if(ScannerFeedback) printf("EQUAL\n");return EQUAL;}
"!="			{if(ScannerFeedback) printf("NEQUAL\n");return NEQUAL;}
"<"             {if(ScannerFeedback) printf("LESS\n");return LESS;}
"<="			{if(ScannerFeedback) printf("LESSEQ\n");return LESSEQ;}
">"				{if(ScannerFeedback) printf("GREAT\n");return GREAT;}
">="			{if(ScannerFeedback) printf("GREATEQ\n");return GREATEQ;}
"+"             {if(ScannerFeedback) printf("ADD\n");return ADD;}
"-"             {if(ScannerFeedback) printf("SUB\n");return SUB;}
"*"             {if(ScannerFeedback) printf("MULT\n");return MULT;}
"/"             {if(ScannerFeedback) printf("DIV\n");return DIV;}
"("             {if(ScannerFeedback) printf("LPARENTS\n");return LPARENTS;}
")"             {if(ScannerFeedback) printf("RPARENTS\n");return RPARENTS;}
";"             {if(ScannerFeedback) printf("SEMICOLON\n");return SEMICOLON;}
","				{if(ScannerFeedback) printf("COMMA\n");return COMMA;}
"["				{if(ScannerFeedback) printf("LSQRBRA\n");return LSQRBRA;}
"]"				{if(ScannerFeedback) printf("RSQRBRA\n");return RSQRBRA;}
"{"				{if(ScannerFeedback) printf("LCURBRA\n");return LCURBRA;}
"}"				{if(ScannerFeedback) printf("RCURBRA\n");return RCURBRA;}
{number}        {if(ScannerFeedback) printf("NUMERO \n"); strcpy(ids,yytext);return NUMERO;}
{ID}	    	{if(ScannerFeedback) printf("ID\n"); strcpy(ids,yytext); return ID;}
{whitespace}    {/*tava dando problema no newline*/}
{newline}		{ lineno++; if(ScannerFeedback) printf("\t%d\n", yylineno);}
{carriage}		{ }
"/*"            { 	char c, d;
                        c = input();
                        do
                        { 	if (c == EOF) break;
                                d = input();
                                if (c == '\n')
                                	 lineno++;
                                if (c == '*' && d == '/') break;
                                c = d;
                  } while (1);
                }
{other}               {printf("Lexical error on line: %d\n", yylineno); return ERROR;}
<<EOF>> 	return(0);
%%

void abrirArq() {
  yyin = fopen("entrada.c", "r");
}

int main() {
	int tmili;
	clock_t start, end;
 	struct timeval inicio, final2;
	start = clock();
	gettimeofday(&inicio, NULL);
	
	listing = fopen("output.txt", "w+");
	
	if(ScannerFeedback) {
		abrirArq();
		printf("executando...\n");
		int token;
	}
	abrirArq();
	if (yyparse()!=0){
		printf("\nO programa contém erro de sintaxe\n");
	}
	else {
		printSyntaxTree();
		SymTabGen();
	}
	
	gettimeofday(&final2, NULL);
	tmili = (int) (1000 * (final2.tv_sec - inicio.tv_sec) + (final2.tv_usec - inicio.tv_usec) / 1000);
	printf("\n\nCompilação finalizada em %d ms \n\n",tmili);
	//fclose(listing);
	return 0;
}
