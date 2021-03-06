/* A Bison parser, made by GNU Bison 3.0.2.  */

/* Bison implementation for Yacc-like parsers in C

   Copyright (C) 1984, 1989-1990, 2000-2013 Free Software Foundation, Inc.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.  */

/* As a special exception, you may create a larger work that contains
   part or all of the Bison parser skeleton and distribute that work
   under terms of your choice, so long as that work isn't itself a
   parser generator using the skeleton or a modified version thereof
   as a parser skeleton.  Alternatively, if you modify or redistribute
   the parser skeleton itself, you may (at your option) remove this
   special exception, which will cause the skeleton and the resulting
   Bison output files to be licensed under the GNU General Public
   License without this special exception.

   This special exception was added by the Free Software Foundation in
   version 2.2 of Bison.  */

/* C LALR(1) parser skeleton written by Richard Stallman, by
   simplifying the original so-called "semantic" parser.  */

/* All symbols defined below should begin with yy or YY, to avoid
   infringing on user name space.  This should be done even for local
   variables, as they might otherwise be expanded by user macros.
   There are some unavoidable exceptions within include files to
   define necessary library symbols; they are noted "INFRINGES ON
   USER NAME SPACE" below.  */

/* Identify Bison output.  */
#define YYBISON 1

/* Bison version.  */
#define YYBISON_VERSION "3.0.2"

/* Skeleton name.  */
#define YYSKELETON_NAME "yacc.c"

/* Pure parsers.  */
#define YYPURE 0

/* Push parsers.  */
#define YYPUSH 0

/* Pull parsers.  */
#define YYPULL 1




/* Copy the first part of user declarations.  */
#line 7 "anasint2.y" /* yacc.c:339  */

#define YYPARSER /* distinguishes Yacc output from other code files */

#include <iostream>
#include <fstream>
#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>
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
#define CompileSteps 1
#define TabGenFeedBack 0
#define TabGenDebug 0

#define SintaxTreeDebug 0
#define IntermCodeGenDebug 1
#define ScopeDebug 0
#define InstMemGenDebug 1

FILE* listing; /* listing output text file */

/*******************************************************/
/*******************************************************/
/*******************************************************/
/********** Árvore de Análise Sintática ****************/
/*******************************************************/
/*******************************************************/
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
             char * name;} attr;//tipo de atributo do no se eh nome, um token ou valor
    ExpType type; /* for type checking of exps */ //preenche so quando DeclType
	IDType id_type;
	char * scope;
	int scope_number;
   } TreeNode;

static char * savedName; /* for use in assignments */
static int savedLineNo;  /* ditto */
static int savedVal;  /* ditto */
static char * savedFunction = "Global";

static int dataMemVarLoc = 0;
static int instMemLoc = 0;

TreeNode * savedTree = NULL;// Declaração da árvore

TreeNode * newExpNode(ExpKind kind);
TreeNode * newStmtNode(StmtKind kind);
void printTree(TreeNode * tree);
void printToken(int token, const char* tokenString );

/************************************************************************/
/************* Tabela de Símbolos e Analisador Semântico ****************/
/************************************************************************/

#define hash_size 211
#define size_lines 10000

int semantical_error = 0;

typedef struct symbol{
	char *ID;
	IDType id_type;
	char *data_type;
	int index;
	char *scope;
	int lines[size_lines];
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


#line 220 "anasint2.tab.c" /* yacc.c:339  */

# ifndef YY_NULLPTR
#  if defined __cplusplus && 201103L <= __cplusplus
#   define YY_NULLPTR nullptr
#  else
#   define YY_NULLPTR 0
#  endif
# endif

/* Enabling verbose error messages.  */
#ifdef YYERROR_VERBOSE
# undef YYERROR_VERBOSE
# define YYERROR_VERBOSE 1
#else
# define YYERROR_VERBOSE 0
#endif

/* In a future release of Bison, this section will be replaced
   by #include "anasint2.tab.h".  */
#ifndef YY_YY_ANASINT2_TAB_H_INCLUDED
# define YY_YY_ANASINT2_TAB_H_INCLUDED
/* Debug traces.  */
#ifndef YYDEBUG
# define YYDEBUG 0
#endif
#if YYDEBUG
extern int yydebug;
#endif

/* Token type.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
  enum yytokentype
  {
    IF = 1,
    INT = 2,
    RETURN = 3,
    VOID = 4,
    WHILE = 5,
    ID = 6,
    NUMERO = 7,
    ADD = 8,
    SUB = 9,
    MULT = 10,
    DIV = 11,
    LESS = 12,
    LESSEQ = 13,
    GREAT = 14,
    GREATEQ = 15,
    EQUAL = 16,
    NEQUAL = 17,
    ASSIGN = 18,
    SEMICOLON = 19,
    COMMA = 20,
    LPARENTS = 21,
    RPARENTS = 22,
    LSQRBRA = 23,
    RSQRBRA = 24,
    LCURBRA = 25,
    RCURBRA = 26,
    ERROR = 27,
    ELSE = 258
  };
#endif

/* Value type.  */
#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED
typedef int YYSTYPE;
# define YYSTYPE_IS_TRIVIAL 1
# define YYSTYPE_IS_DECLARED 1
#endif


extern YYSTYPE yylval;

int yyparse (void);

#endif /* !YY_YY_ANASINT2_TAB_H_INCLUDED  */

/* Copy the second part of user declarations.  */

#line 302 "anasint2.tab.c" /* yacc.c:358  */

#ifdef short
# undef short
#endif

#ifdef YYTYPE_UINT8
typedef YYTYPE_UINT8 yytype_uint8;
#else
typedef unsigned char yytype_uint8;
#endif

#ifdef YYTYPE_INT8
typedef YYTYPE_INT8 yytype_int8;
#else
typedef signed char yytype_int8;
#endif

#ifdef YYTYPE_UINT16
typedef YYTYPE_UINT16 yytype_uint16;
#else
typedef unsigned short int yytype_uint16;
#endif

#ifdef YYTYPE_INT16
typedef YYTYPE_INT16 yytype_int16;
#else
typedef short int yytype_int16;
#endif

#ifndef YYSIZE_T
# ifdef __SIZE_TYPE__
#  define YYSIZE_T __SIZE_TYPE__
# elif defined size_t
#  define YYSIZE_T size_t
# elif ! defined YYSIZE_T
#  include <stddef.h> /* INFRINGES ON USER NAME SPACE */
#  define YYSIZE_T size_t
# else
#  define YYSIZE_T unsigned int
# endif
#endif

#define YYSIZE_MAXIMUM ((YYSIZE_T) -1)

#ifndef YY_
# if defined YYENABLE_NLS && YYENABLE_NLS
#  if ENABLE_NLS
#   include <libintl.h> /* INFRINGES ON USER NAME SPACE */
#   define YY_(Msgid) dgettext ("bison-runtime", Msgid)
#  endif
# endif
# ifndef YY_
#  define YY_(Msgid) Msgid
# endif
#endif

#ifndef YY_ATTRIBUTE
# if (defined __GNUC__                                               \
      && (2 < __GNUC__ || (__GNUC__ == 2 && 96 <= __GNUC_MINOR__)))  \
     || defined __SUNPRO_C && 0x5110 <= __SUNPRO_C
#  define YY_ATTRIBUTE(Spec) __attribute__(Spec)
# else
#  define YY_ATTRIBUTE(Spec) /* empty */
# endif
#endif

#ifndef YY_ATTRIBUTE_PURE
# define YY_ATTRIBUTE_PURE   YY_ATTRIBUTE ((__pure__))
#endif

#ifndef YY_ATTRIBUTE_UNUSED
# define YY_ATTRIBUTE_UNUSED YY_ATTRIBUTE ((__unused__))
#endif

#if !defined _Noreturn \
     && (!defined __STDC_VERSION__ || __STDC_VERSION__ < 201112)
# if defined _MSC_VER && 1200 <= _MSC_VER
#  define _Noreturn __declspec (noreturn)
# else
#  define _Noreturn YY_ATTRIBUTE ((__noreturn__))
# endif
#endif

/* Suppress unused-variable warnings by "using" E.  */
#if ! defined lint || defined __GNUC__
# define YYUSE(E) ((void) (E))
#else
# define YYUSE(E) /* empty */
#endif

#if defined __GNUC__ && 407 <= __GNUC__ * 100 + __GNUC_MINOR__
/* Suppress an incorrect diagnostic about yylval being uninitialized.  */
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN \
    _Pragma ("GCC diagnostic push") \
    _Pragma ("GCC diagnostic ignored \"-Wuninitialized\"")\
    _Pragma ("GCC diagnostic ignored \"-Wmaybe-uninitialized\"")
# define YY_IGNORE_MAYBE_UNINITIALIZED_END \
    _Pragma ("GCC diagnostic pop")
#else
# define YY_INITIAL_VALUE(Value) Value
#endif
#ifndef YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_END
#endif
#ifndef YY_INITIAL_VALUE
# define YY_INITIAL_VALUE(Value) /* Nothing. */
#endif


#if ! defined yyoverflow || YYERROR_VERBOSE

/* The parser invokes alloca or malloc; define the necessary symbols.  */

# ifdef YYSTACK_USE_ALLOCA
#  if YYSTACK_USE_ALLOCA
#   ifdef __GNUC__
#    define YYSTACK_ALLOC __builtin_alloca
#   elif defined __BUILTIN_VA_ARG_INCR
#    include <alloca.h> /* INFRINGES ON USER NAME SPACE */
#   elif defined _AIX
#    define YYSTACK_ALLOC __alloca
#   elif defined _MSC_VER
#    include <malloc.h> /* INFRINGES ON USER NAME SPACE */
#    define alloca _alloca
#   else
#    define YYSTACK_ALLOC alloca
#    if ! defined _ALLOCA_H && ! defined EXIT_SUCCESS
#     include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
      /* Use EXIT_SUCCESS as a witness for stdlib.h.  */
#     ifndef EXIT_SUCCESS
#      define EXIT_SUCCESS 0
#     endif
#    endif
#   endif
#  endif
# endif

# ifdef YYSTACK_ALLOC
   /* Pacify GCC's 'empty if-body' warning.  */
#  define YYSTACK_FREE(Ptr) do { /* empty */; } while (0)
#  ifndef YYSTACK_ALLOC_MAXIMUM
    /* The OS might guarantee only one guard page at the bottom of the stack,
       and a page size can be as small as 4096 bytes.  So we cannot safely
       invoke alloca (N) if N exceeds 4096.  Use a slightly smaller number
       to allow for a few compiler-allocated temporary stack slots.  */
#   define YYSTACK_ALLOC_MAXIMUM 4032 /* reasonable circa 2006 */
#  endif
# else
#  define YYSTACK_ALLOC YYMALLOC
#  define YYSTACK_FREE YYFREE
#  ifndef YYSTACK_ALLOC_MAXIMUM
#   define YYSTACK_ALLOC_MAXIMUM YYSIZE_MAXIMUM
#  endif
#  if (defined __cplusplus && ! defined EXIT_SUCCESS \
       && ! ((defined YYMALLOC || defined malloc) \
             && (defined YYFREE || defined free)))
#   include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
#   ifndef EXIT_SUCCESS
#    define EXIT_SUCCESS 0
#   endif
#  endif
#  ifndef YYMALLOC
#   define YYMALLOC malloc
#   if ! defined malloc && ! defined EXIT_SUCCESS
void *malloc (YYSIZE_T); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
#  ifndef YYFREE
#   define YYFREE free
#   if ! defined free && ! defined EXIT_SUCCESS
void free (void *); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
# endif
#endif /* ! defined yyoverflow || YYERROR_VERBOSE */


#if (! defined yyoverflow \
     && (! defined __cplusplus \
         || (defined YYSTYPE_IS_TRIVIAL && YYSTYPE_IS_TRIVIAL)))

/* A type that is properly aligned for any stack member.  */
union yyalloc
{
  yytype_int16 yyss_alloc;
  YYSTYPE yyvs_alloc;
};

/* The size of the maximum gap between one aligned stack and the next.  */
# define YYSTACK_GAP_MAXIMUM (sizeof (union yyalloc) - 1)

/* The size of an array large to enough to hold all stacks, each with
   N elements.  */
# define YYSTACK_BYTES(N) \
     ((N) * (sizeof (yytype_int16) + sizeof (YYSTYPE)) \
      + YYSTACK_GAP_MAXIMUM)

# define YYCOPY_NEEDED 1

/* Relocate STACK from its old location to the new one.  The
   local variables YYSIZE and YYSTACKSIZE give the old and new number of
   elements in the stack, and YYPTR gives the new location of the
   stack.  Advance YYPTR to a properly aligned location for the next
   stack.  */
# define YYSTACK_RELOCATE(Stack_alloc, Stack)                           \
    do                                                                  \
      {                                                                 \
        YYSIZE_T yynewbytes;                                            \
        YYCOPY (&yyptr->Stack_alloc, Stack, yysize);                    \
        Stack = &yyptr->Stack_alloc;                                    \
        yynewbytes = yystacksize * sizeof (*Stack) + YYSTACK_GAP_MAXIMUM; \
        yyptr += yynewbytes / sizeof (*yyptr);                          \
      }                                                                 \
    while (0)

#endif

#if defined YYCOPY_NEEDED && YYCOPY_NEEDED
/* Copy COUNT objects from SRC to DST.  The source and destination do
   not overlap.  */
# ifndef YYCOPY
#  if defined __GNUC__ && 1 < __GNUC__
#   define YYCOPY(Dst, Src, Count) \
      __builtin_memcpy (Dst, Src, (Count) * sizeof (*(Src)))
#  else
#   define YYCOPY(Dst, Src, Count)              \
      do                                        \
        {                                       \
          YYSIZE_T yyi;                         \
          for (yyi = 0; yyi < (Count); yyi++)   \
            (Dst)[yyi] = (Src)[yyi];            \
        }                                       \
      while (0)
#  endif
# endif
#endif /* !YYCOPY_NEEDED */

/* YYFINAL -- State number of the termination state.  */
#define YYFINAL  9
/* YYLAST -- Last index in YYTABLE.  */
#define YYLAST   108

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  31
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  37
/* YYNRULES -- Number of rules.  */
#define YYNRULES  70
/* YYNSTATES -- Number of states.  */
#define YYNSTATES  110

/* YYTRANSLATE[YYX] -- Symbol number corresponding to YYX as returned
   by yylex, with out-of-bounds checking.  */
#define YYUNDEFTOK  2
#define YYMAXUTOK   258

#define YYTRANSLATE(YYX)                                                \
  ((unsigned int) (YYX) <= YYMAXUTOK ? yytranslate[YYX] : YYUNDEFTOK)

/* YYTRANSLATE[TOKEN-NUM] -- Symbol number corresponding to TOKEN-NUM
   as returned by yylex, without out-of-bounds checking.  */
static const yytype_uint8 yytranslate[] =
{
       0,     3,     4,     5,     6,     7,     8,     9,    10,    11,
      12,    13,    14,    15,    16,    17,    18,    19,    20,    21,
      22,    23,    24,    25,    26,    27,    28,    29,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     1,     2,    30
};

#if YYDEBUG
  /* YYRLINE[YYN] -- Source line where rule number YYN was defined.  */
static const yytype_uint16 yyrline[] =
{
       0,   192,   192,   198,   210,   216,   221,   228,   228,   250,
     250,   250,   280,   286,   294,   294,   318,   323,   329,   341,
     347,   359,   359,   374,   387,   400,   405,   419,   424,   429,
     434,   439,   444,   450,   455,   461,   468,   477,   485,   491,
     498,   506,   512,   519,   519,   529,   537,   543,   549,   555,
     561,   567,   573,   580,   590,   596,   602,   609,   619,   625,
     631,   638,   643,   648,   653,   661,   671,   679,   685,   690,
     702
};
#endif

#if YYDEBUG || YYERROR_VERBOSE || 0
/* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals.  */
static const char *const yytname[] =
{
  "$end", "error", "$undefined", "IF", "INT", "RETURN", "VOID", "WHILE",
  "ID", "NUMERO", "ADD", "SUB", "MULT", "DIV", "LESS", "LESSEQ", "GREAT",
  "GREATEQ", "EQUAL", "NEQUAL", "ASSIGN", "SEMICOLON", "COMMA", "LPARENTS",
  "RPARENTS", "LSQRBRA", "RSQRBRA", "LCURBRA", "RCURBRA", "ERROR", "ELSE",
  "$accept", "programa", "declaracao_lista", "declaracao",
  "var_declaracao", "$@1", "$@2", "$@3", "tipo_especificador",
  "fun_declaracao", "$@4", "params", "param_lista", "param", "$@5",
  "composto_decl", "local_declaracoes", "statement_lista", "statement",
  "expressao_decl", "selecao_decl", "iteracao_decl", "retorno_decl",
  "expressao", "var", "$@6", "simples_expressao", "relacional",
  "soma_expressao", "soma", "termo", "mult", "fator", "ativacao", "id",
  "args", "arg_lista", YY_NULLPTR
};
#endif

# ifdef YYPRINT
/* YYTOKNUM[NUM] -- (External) token number corresponding to the
   (internal) symbol number NUM (which must be that of a token).  */
static const yytype_uint16 yytoknum[] =
{
       0,   256,   257,     1,     2,     3,     4,     5,     6,     7,
       8,     9,    10,    11,    12,    13,    14,    15,    16,    17,
      18,    19,    20,    21,    22,    23,    24,    25,    26,    27,
     258
};
# endif

#define YYPACT_NINF -91

#define yypact_value_is_default(Yystate) \
  (!!((Yystate) == (-91)))

#define YYTABLE_NINF -67

#define yytable_value_is_error(Yytable_value) \
  0

  /* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
     STATE-NUM.  */
static const yytype_int8 yypact[] =
{
      26,   -91,   -91,    12,    26,   -91,   -91,    11,   -91,   -91,
     -91,   -22,     2,     9,    24,   -91,    43,    39,   -91,    32,
      51,    45,    48,   -91,    46,   -91,    49,    44,    26,    52,
      50,   -91,   -91,   -91,   -91,    53,    26,   -91,   -91,    68,
      -1,    55,    54,    28,    58,    25,   -91,   -91,    30,   -91,
     -91,   -91,   -91,   -91,   -91,   -91,    61,    63,   -91,    47,
      42,   -91,   -91,    62,    30,   -91,    65,    30,    59,    64,
     -91,    30,   -91,   -91,   -91,   -91,   -91,   -91,   -91,   -91,
      30,    30,   -91,   -91,    30,    30,    66,   -91,    67,    30,
     -91,   -91,   -91,    57,    42,   -91,   -91,    69,    56,     8,
       8,    70,   -91,    30,    71,   -91,   -91,   -91,     8,   -91
};

  /* YYDEFACT[STATE-NUM] -- Default reduction number in state STATE-NUM.
     Performed when YYTABLE does not specify something else to do.  Zero
     means the default is an error.  */
static const yytype_uint8 yydefact[] =
{
       0,    12,    13,     0,     2,     4,     5,     0,     6,     1,
       3,     7,     0,     0,     0,     8,     0,     0,    10,    13,
       0,     0,    16,    19,     0,    66,    20,     0,     0,     0,
       0,    25,    15,    18,    11,     0,    27,    22,    24,     0,
       0,     7,     0,     0,     0,    42,    64,    34,     0,    23,
      29,    26,    28,    30,    31,    32,     0,    62,    41,    46,
      54,    58,    63,     0,     0,    38,     0,     0,     0,     0,
      33,     0,    55,    56,    48,    47,    49,    50,    51,    52,
       0,     0,    59,    60,     0,    68,     0,    39,     0,     0,
      61,    40,    62,    45,    53,    57,    70,     0,    67,     0,
       0,     0,    65,     0,    35,    37,    44,    69,     0,    36
};

  /* YYPGOTO[NTERM-NUM].  */
static const yytype_int8 yypgoto[] =
{
     -91,   -91,   -91,    83,    72,   -91,   -91,   -91,    -3,   -91,
     -91,   -91,   -91,    74,   -91,    73,   -91,   -91,   -90,   -91,
     -91,   -91,   -91,   -43,   -40,   -91,   -91,   -91,    14,   -91,
      16,   -91,     5,   -91,    75,   -91,   -91
};

  /* YYDEFGOTO[NTERM-NUM].  */
static const yytype_int8 yydefgoto[] =
{
      -1,     3,     4,     5,     6,    12,    13,    24,     7,     8,
      14,    21,    22,    23,    30,    50,    36,    40,    51,    52,
      53,    54,    55,    56,    57,    68,    58,    80,    59,    81,
      60,    84,    61,    62,    63,    97,    98
};

  /* YYTABLE[YYPACT[STATE-NUM]] -- What to do in state STATE-NUM.  If
     positive, shift that token.  If negative, reduce the rule whose
     number is the opposite.  If YYTABLE_NINF, syntax error.  */
static const yytype_int8 yytable[] =
{
      66,   -14,    42,    -9,    43,    69,    44,    45,    46,   104,
     105,    42,     9,    43,    20,    44,    45,    46,   109,    11,
      47,    86,    48,    15,    88,    20,    31,    49,    91,    47,
       1,    48,     2,    39,    16,    31,    45,    46,    45,    46,
      92,    92,    96,     1,    92,    19,   101,    17,   -66,    65,
     -43,    48,    18,    48,    82,    83,   -17,    72,    73,    25,
     107,    74,    75,    76,    77,    78,    79,    72,    73,    27,
      28,    31,    29,    34,   -21,    35,    41,    64,   103,    37,
      -9,    67,    70,    71,    89,    85,    87,    10,    90,    95,
      99,   100,     0,   102,    93,    26,   106,    94,     0,     0,
      32,   108,    33,     0,     0,     0,     0,     0,    38
};

static const yytype_int8 yycheck[] =
{
      43,    23,     3,    25,     5,    48,     7,     8,     9,    99,
     100,     3,     0,     5,    17,     7,     8,     9,   108,     8,
      21,    64,    23,    21,    67,    28,    27,    28,    71,    21,
       4,    23,     6,    36,    25,    27,     8,     9,     8,     9,
      80,    81,    85,     4,    84,     6,    89,    23,    23,    21,
      25,    23,     9,    23,    12,    13,    24,    10,    11,     8,
     103,    14,    15,    16,    17,    18,    19,    10,    11,    24,
      22,    27,    26,    21,    25,    25,     8,    23,    22,    26,
      25,    23,    21,    20,    25,    23,    21,     4,    24,    84,
      24,    24,    -1,    24,    80,    20,    26,    81,    -1,    -1,
      27,    30,    28,    -1,    -1,    -1,    -1,    -1,    36
};

  /* YYSTOS[STATE-NUM] -- The (internal number of the) accessing
     symbol of state STATE-NUM.  */
static const yytype_uint8 yystos[] =
{
       0,     4,     6,    32,    33,    34,    35,    39,    40,     0,
      34,     8,    36,    37,    41,    21,    25,    23,     9,     6,
      39,    42,    43,    44,    38,     8,    65,    24,    22,    26,
      45,    27,    46,    44,    21,    25,    47,    26,    35,    39,
      48,     8,     3,     5,     7,     8,     9,    21,    23,    28,
      46,    49,    50,    51,    52,    53,    54,    55,    57,    59,
      61,    63,    64,    65,    23,    21,    54,    23,    56,    54,
      21,    20,    10,    11,    14,    15,    16,    17,    18,    19,
      58,    60,    12,    13,    62,    23,    54,    21,    54,    25,
      24,    54,    55,    59,    61,    63,    54,    66,    67,    24,
      24,    54,    24,    22,    49,    49,    26,    54,    30,    49
};

  /* YYR1[YYN] -- Symbol number of symbol that rule YYN derives.  */
static const yytype_uint8 yyr1[] =
{
       0,    31,    32,    33,    33,    34,    34,    36,    35,    37,
      38,    35,    39,    39,    41,    40,    42,    42,    43,    43,
      44,    45,    44,    46,    47,    47,    48,    48,    49,    49,
      49,    49,    49,    50,    50,    51,    51,    52,    53,    53,
      54,    54,    55,    56,    55,    57,    57,    58,    58,    58,
      58,    58,    58,    59,    59,    60,    60,    61,    61,    62,
      62,    63,    63,    63,    63,    64,    65,    66,    66,    67,
      67
};

  /* YYR2[YYN] -- Number of symbols on the right hand side of rule YYN.  */
static const yytype_uint8 yyr2[] =
{
       0,     2,     1,     2,     1,     1,     1,     0,     4,     0,
       0,     8,     1,     1,     0,     7,     1,     1,     3,     1,
       2,     0,     5,     4,     2,     0,     2,     0,     1,     1,
       1,     1,     1,     2,     1,     5,     7,     5,     2,     3,
       3,     1,     1,     0,     5,     3,     1,     1,     1,     1,
       1,     1,     1,     3,     1,     1,     1,     3,     1,     1,
       1,     3,     1,     1,     1,     4,     1,     1,     0,     3,
       1
};


#define yyerrok         (yyerrstatus = 0)
#define yyclearin       (yychar = YYEMPTY)
#define YYEMPTY         (-2)
#define YYEOF           0

#define YYACCEPT        goto yyacceptlab
#define YYABORT         goto yyabortlab
#define YYERROR         goto yyerrorlab


#define YYRECOVERING()  (!!yyerrstatus)

#define YYBACKUP(Token, Value)                                  \
do                                                              \
  if (yychar == YYEMPTY)                                        \
    {                                                           \
      yychar = (Token);                                         \
      yylval = (Value);                                         \
      YYPOPSTACK (yylen);                                       \
      yystate = *yyssp;                                         \
      goto yybackup;                                            \
    }                                                           \
  else                                                          \
    {                                                           \
      yyerror (YY_("syntax error: cannot back up")); \
      YYERROR;                                                  \
    }                                                           \
while (0)

/* Error token number */
#define YYTERROR        1
#define YYERRCODE       256



/* Enable debugging if requested.  */
#if YYDEBUG

# ifndef YYFPRINTF
#  include <stdio.h> /* INFRINGES ON USER NAME SPACE */
#  define YYFPRINTF fprintf
# endif

# define YYDPRINTF(Args)                        \
do {                                            \
  if (yydebug)                                  \
    YYFPRINTF Args;                             \
} while (0)

/* This macro is provided for backward compatibility. */
#ifndef YY_LOCATION_PRINT
# define YY_LOCATION_PRINT(File, Loc) ((void) 0)
#endif


# define YY_SYMBOL_PRINT(Title, Type, Value, Location)                    \
do {                                                                      \
  if (yydebug)                                                            \
    {                                                                     \
      YYFPRINTF (stderr, "%s ", Title);                                   \
      yy_symbol_print (stderr,                                            \
                  Type, Value); \
      YYFPRINTF (stderr, "\n");                                           \
    }                                                                     \
} while (0)


/*----------------------------------------.
| Print this symbol's value on YYOUTPUT.  |
`----------------------------------------*/

static void
yy_symbol_value_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep)
{
  FILE *yyo = yyoutput;
  YYUSE (yyo);
  if (!yyvaluep)
    return;
# ifdef YYPRINT
  if (yytype < YYNTOKENS)
    YYPRINT (yyoutput, yytoknum[yytype], *yyvaluep);
# endif
  YYUSE (yytype);
}


/*--------------------------------.
| Print this symbol on YYOUTPUT.  |
`--------------------------------*/

static void
yy_symbol_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep)
{
  YYFPRINTF (yyoutput, "%s %s (",
             yytype < YYNTOKENS ? "token" : "nterm", yytname[yytype]);

  yy_symbol_value_print (yyoutput, yytype, yyvaluep);
  YYFPRINTF (yyoutput, ")");
}

/*------------------------------------------------------------------.
| yy_stack_print -- Print the state stack from its BOTTOM up to its |
| TOP (included).                                                   |
`------------------------------------------------------------------*/

static void
yy_stack_print (yytype_int16 *yybottom, yytype_int16 *yytop)
{
  YYFPRINTF (stderr, "Stack now");
  for (; yybottom <= yytop; yybottom++)
    {
      int yybot = *yybottom;
      YYFPRINTF (stderr, " %d", yybot);
    }
  YYFPRINTF (stderr, "\n");
}

# define YY_STACK_PRINT(Bottom, Top)                            \
do {                                                            \
  if (yydebug)                                                  \
    yy_stack_print ((Bottom), (Top));                           \
} while (0)


/*------------------------------------------------.
| Report that the YYRULE is going to be reduced.  |
`------------------------------------------------*/

static void
yy_reduce_print (yytype_int16 *yyssp, YYSTYPE *yyvsp, int yyrule)
{
  unsigned long int yylno = yyrline[yyrule];
  int yynrhs = yyr2[yyrule];
  int yyi;
  YYFPRINTF (stderr, "Reducing stack by rule %d (line %lu):\n",
             yyrule - 1, yylno);
  /* The symbols being reduced.  */
  for (yyi = 0; yyi < yynrhs; yyi++)
    {
      YYFPRINTF (stderr, "   $%d = ", yyi + 1);
      yy_symbol_print (stderr,
                       yystos[yyssp[yyi + 1 - yynrhs]],
                       &(yyvsp[(yyi + 1) - (yynrhs)])
                                              );
      YYFPRINTF (stderr, "\n");
    }
}

# define YY_REDUCE_PRINT(Rule)          \
do {                                    \
  if (yydebug)                          \
    yy_reduce_print (yyssp, yyvsp, Rule); \
} while (0)

/* Nonzero means print parse trace.  It is left uninitialized so that
   multiple parsers can coexist.  */
int yydebug;
#else /* !YYDEBUG */
# define YYDPRINTF(Args)
# define YY_SYMBOL_PRINT(Title, Type, Value, Location)
# define YY_STACK_PRINT(Bottom, Top)
# define YY_REDUCE_PRINT(Rule)
#endif /* !YYDEBUG */


/* YYINITDEPTH -- initial size of the parser's stacks.  */
#ifndef YYINITDEPTH
# define YYINITDEPTH 200
#endif

/* YYMAXDEPTH -- maximum size the stacks can grow to (effective only
   if the built-in stack extension method is used).

   Do not make this value too large; the results are undefined if
   YYSTACK_ALLOC_MAXIMUM < YYSTACK_BYTES (YYMAXDEPTH)
   evaluated with infinite-precision integer arithmetic.  */

#ifndef YYMAXDEPTH
# define YYMAXDEPTH 10000
#endif


#if YYERROR_VERBOSE

# ifndef yystrlen
#  if defined __GLIBC__ && defined _STRING_H
#   define yystrlen strlen
#  else
/* Return the length of YYSTR.  */
static YYSIZE_T
yystrlen (const char *yystr)
{
  YYSIZE_T yylen;
  for (yylen = 0; yystr[yylen]; yylen++)
    continue;
  return yylen;
}
#  endif
# endif

# ifndef yystpcpy
#  if defined __GLIBC__ && defined _STRING_H && defined _GNU_SOURCE
#   define yystpcpy stpcpy
#  else
/* Copy YYSRC to YYDEST, returning the address of the terminating '\0' in
   YYDEST.  */
static char *
yystpcpy (char *yydest, const char *yysrc)
{
  char *yyd = yydest;
  const char *yys = yysrc;

  while ((*yyd++ = *yys++) != '\0')
    continue;

  return yyd - 1;
}
#  endif
# endif

# ifndef yytnamerr
/* Copy to YYRES the contents of YYSTR after stripping away unnecessary
   quotes and backslashes, so that it's suitable for yyerror.  The
   heuristic is that double-quoting is unnecessary unless the string
   contains an apostrophe, a comma, or backslash (other than
   backslash-backslash).  YYSTR is taken from yytname.  If YYRES is
   null, do not copy; instead, return the length of what the result
   would have been.  */
static YYSIZE_T
yytnamerr (char *yyres, const char *yystr)
{
  if (*yystr == '"')
    {
      YYSIZE_T yyn = 0;
      char const *yyp = yystr;

      for (;;)
        switch (*++yyp)
          {
          case '\'':
          case ',':
            goto do_not_strip_quotes;

          case '\\':
            if (*++yyp != '\\')
              goto do_not_strip_quotes;
            /* Fall through.  */
          default:
            if (yyres)
              yyres[yyn] = *yyp;
            yyn++;
            break;

          case '"':
            if (yyres)
              yyres[yyn] = '\0';
            return yyn;
          }
    do_not_strip_quotes: ;
    }

  if (! yyres)
    return yystrlen (yystr);

  return yystpcpy (yyres, yystr) - yyres;
}
# endif

/* Copy into *YYMSG, which is of size *YYMSG_ALLOC, an error message
   about the unexpected token YYTOKEN for the state stack whose top is
   YYSSP.

   Return 0 if *YYMSG was successfully written.  Return 1 if *YYMSG is
   not large enough to hold the message.  In that case, also set
   *YYMSG_ALLOC to the required number of bytes.  Return 2 if the
   required number of bytes is too large to store.  */
static int
yysyntax_error (YYSIZE_T *yymsg_alloc, char **yymsg,
                yytype_int16 *yyssp, int yytoken)
{
  YYSIZE_T yysize0 = yytnamerr (YY_NULLPTR, yytname[yytoken]);
  YYSIZE_T yysize = yysize0;
  enum { YYERROR_VERBOSE_ARGS_MAXIMUM = 5 };
  /* Internationalized format string. */
  const char *yyformat = YY_NULLPTR;
  /* Arguments of yyformat. */
  char const *yyarg[YYERROR_VERBOSE_ARGS_MAXIMUM];
  /* Number of reported tokens (one for the "unexpected", one per
     "expected"). */
  int yycount = 0;

  /* There are many possibilities here to consider:
     - If this state is a consistent state with a default action, then
       the only way this function was invoked is if the default action
       is an error action.  In that case, don't check for expected
       tokens because there are none.
     - The only way there can be no lookahead present (in yychar) is if
       this state is a consistent state with a default action.  Thus,
       detecting the absence of a lookahead is sufficient to determine
       that there is no unexpected or expected token to report.  In that
       case, just report a simple "syntax error".
     - Don't assume there isn't a lookahead just because this state is a
       consistent state with a default action.  There might have been a
       previous inconsistent state, consistent state with a non-default
       action, or user semantic action that manipulated yychar.
     - Of course, the expected token list depends on states to have
       correct lookahead information, and it depends on the parser not
       to perform extra reductions after fetching a lookahead from the
       scanner and before detecting a syntax error.  Thus, state merging
       (from LALR or IELR) and default reductions corrupt the expected
       token list.  However, the list is correct for canonical LR with
       one exception: it will still contain any token that will not be
       accepted due to an error action in a later state.
  */
  if (yytoken != YYEMPTY)
    {
      int yyn = yypact[*yyssp];
      yyarg[yycount++] = yytname[yytoken];
      if (!yypact_value_is_default (yyn))
        {
          /* Start YYX at -YYN if negative to avoid negative indexes in
             YYCHECK.  In other words, skip the first -YYN actions for
             this state because they are default actions.  */
          int yyxbegin = yyn < 0 ? -yyn : 0;
          /* Stay within bounds of both yycheck and yytname.  */
          int yychecklim = YYLAST - yyn + 1;
          int yyxend = yychecklim < YYNTOKENS ? yychecklim : YYNTOKENS;
          int yyx;

          for (yyx = yyxbegin; yyx < yyxend; ++yyx)
            if (yycheck[yyx + yyn] == yyx && yyx != YYTERROR
                && !yytable_value_is_error (yytable[yyx + yyn]))
              {
                if (yycount == YYERROR_VERBOSE_ARGS_MAXIMUM)
                  {
                    yycount = 1;
                    yysize = yysize0;
                    break;
                  }
                yyarg[yycount++] = yytname[yyx];
                {
                  YYSIZE_T yysize1 = yysize + yytnamerr (YY_NULLPTR, yytname[yyx]);
                  if (! (yysize <= yysize1
                         && yysize1 <= YYSTACK_ALLOC_MAXIMUM))
                    return 2;
                  yysize = yysize1;
                }
              }
        }
    }

  switch (yycount)
    {
# define YYCASE_(N, S)                      \
      case N:                               \
        yyformat = S;                       \
      break
      YYCASE_(0, YY_("syntax error"));
      YYCASE_(1, YY_("syntax error, unexpected %s"));
      YYCASE_(2, YY_("syntax error, unexpected %s, expecting %s"));
      YYCASE_(3, YY_("syntax error, unexpected %s, expecting %s or %s"));
      YYCASE_(4, YY_("syntax error, unexpected %s, expecting %s or %s or %s"));
      YYCASE_(5, YY_("syntax error, unexpected %s, expecting %s or %s or %s or %s"));
# undef YYCASE_
    }

  {
    YYSIZE_T yysize1 = yysize + yystrlen (yyformat);
    if (! (yysize <= yysize1 && yysize1 <= YYSTACK_ALLOC_MAXIMUM))
      return 2;
    yysize = yysize1;
  }

  if (*yymsg_alloc < yysize)
    {
      *yymsg_alloc = 2 * yysize;
      if (! (yysize <= *yymsg_alloc
             && *yymsg_alloc <= YYSTACK_ALLOC_MAXIMUM))
        *yymsg_alloc = YYSTACK_ALLOC_MAXIMUM;
      return 1;
    }

  /* Avoid sprintf, as that infringes on the user's name space.
     Don't have undefined behavior even if the translation
     produced a string with the wrong number of "%s"s.  */
  {
    char *yyp = *yymsg;
    int yyi = 0;
    while ((*yyp = *yyformat) != '\0')
      if (*yyp == '%' && yyformat[1] == 's' && yyi < yycount)
        {
          yyp += yytnamerr (yyp, yyarg[yyi++]);
          yyformat += 2;
        }
      else
        {
          yyp++;
          yyformat++;
        }
  }
  return 0;
}
#endif /* YYERROR_VERBOSE */

/*-----------------------------------------------.
| Release the memory associated to this symbol.  |
`-----------------------------------------------*/

static void
yydestruct (const char *yymsg, int yytype, YYSTYPE *yyvaluep)
{
  YYUSE (yyvaluep);
  if (!yymsg)
    yymsg = "Deleting";
  YY_SYMBOL_PRINT (yymsg, yytype, yyvaluep, yylocationp);

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  YYUSE (yytype);
  YY_IGNORE_MAYBE_UNINITIALIZED_END
}




/* The lookahead symbol.  */
int yychar;

/* The semantic value of the lookahead symbol.  */
YYSTYPE yylval;
/* Number of syntax errors so far.  */
int yynerrs;


/*----------.
| yyparse.  |
`----------*/

int
yyparse (void)
{
    int yystate;
    /* Number of tokens to shift before error messages enabled.  */
    int yyerrstatus;

    /* The stacks and their tools:
       'yyss': related to states.
       'yyvs': related to semantic values.

       Refer to the stacks through separate pointers, to allow yyoverflow
       to reallocate them elsewhere.  */

    /* The state stack.  */
    yytype_int16 yyssa[YYINITDEPTH];
    yytype_int16 *yyss;
    yytype_int16 *yyssp;

    /* The semantic value stack.  */
    YYSTYPE yyvsa[YYINITDEPTH];
    YYSTYPE *yyvs;
    YYSTYPE *yyvsp;

    YYSIZE_T yystacksize;

  int yyn;
  int yyresult;
  /* Lookahead token as an internal (translated) token number.  */
  int yytoken = 0;
  /* The variables used to return semantic value and location from the
     action routines.  */
  YYSTYPE yyval;

#if YYERROR_VERBOSE
  /* Buffer for error messages, and its allocated size.  */
  char yymsgbuf[128];
  char *yymsg = yymsgbuf;
  YYSIZE_T yymsg_alloc = sizeof yymsgbuf;
#endif

#define YYPOPSTACK(N)   (yyvsp -= (N), yyssp -= (N))

  /* The number of symbols on the RHS of the reduced rule.
     Keep to zero when no symbol should be popped.  */
  int yylen = 0;

  yyssp = yyss = yyssa;
  yyvsp = yyvs = yyvsa;
  yystacksize = YYINITDEPTH;

  YYDPRINTF ((stderr, "Starting parse\n"));

  yystate = 0;
  yyerrstatus = 0;
  yynerrs = 0;
  yychar = YYEMPTY; /* Cause a token to be read.  */
  goto yysetstate;

/*------------------------------------------------------------.
| yynewstate -- Push a new state, which is found in yystate.  |
`------------------------------------------------------------*/
 yynewstate:
  /* In all cases, when you get here, the value and location stacks
     have just been pushed.  So pushing a state here evens the stacks.  */
  yyssp++;

 yysetstate:
  *yyssp = yystate;

  if (yyss + yystacksize - 1 <= yyssp)
    {
      /* Get the current used size of the three stacks, in elements.  */
      YYSIZE_T yysize = yyssp - yyss + 1;

#ifdef yyoverflow
      {
        /* Give user a chance to reallocate the stack.  Use copies of
           these so that the &'s don't force the real ones into
           memory.  */
        YYSTYPE *yyvs1 = yyvs;
        yytype_int16 *yyss1 = yyss;

        /* Each stack pointer address is followed by the size of the
           data in use in that stack, in bytes.  This used to be a
           conditional around just the two extra args, but that might
           be undefined if yyoverflow is a macro.  */
        yyoverflow (YY_("memory exhausted"),
                    &yyss1, yysize * sizeof (*yyssp),
                    &yyvs1, yysize * sizeof (*yyvsp),
                    &yystacksize);

        yyss = yyss1;
        yyvs = yyvs1;
      }
#else /* no yyoverflow */
# ifndef YYSTACK_RELOCATE
      goto yyexhaustedlab;
# else
      /* Extend the stack our own way.  */
      if (YYMAXDEPTH <= yystacksize)
        goto yyexhaustedlab;
      yystacksize *= 2;
      if (YYMAXDEPTH < yystacksize)
        yystacksize = YYMAXDEPTH;

      {
        yytype_int16 *yyss1 = yyss;
        union yyalloc *yyptr =
          (union yyalloc *) YYSTACK_ALLOC (YYSTACK_BYTES (yystacksize));
        if (! yyptr)
          goto yyexhaustedlab;
        YYSTACK_RELOCATE (yyss_alloc, yyss);
        YYSTACK_RELOCATE (yyvs_alloc, yyvs);
#  undef YYSTACK_RELOCATE
        if (yyss1 != yyssa)
          YYSTACK_FREE (yyss1);
      }
# endif
#endif /* no yyoverflow */

      yyssp = yyss + yysize - 1;
      yyvsp = yyvs + yysize - 1;

      YYDPRINTF ((stderr, "Stack size increased to %lu\n",
                  (unsigned long int) yystacksize));

      if (yyss + yystacksize - 1 <= yyssp)
        YYABORT;
    }

  YYDPRINTF ((stderr, "Entering state %d\n", yystate));

  if (yystate == YYFINAL)
    YYACCEPT;

  goto yybackup;

/*-----------.
| yybackup.  |
`-----------*/
yybackup:

  /* Do appropriate processing given the current state.  Read a
     lookahead token if we need one and don't already have one.  */

  /* First try to decide what to do without reference to lookahead token.  */
  yyn = yypact[yystate];
  if (yypact_value_is_default (yyn))
    goto yydefault;

  /* Not known => get a lookahead token if don't already have one.  */

  /* YYCHAR is either YYEMPTY or YYEOF or a valid lookahead symbol.  */
  if (yychar == YYEMPTY)
    {
      YYDPRINTF ((stderr, "Reading a token: "));
      yychar = yylex ();
    }

  if (yychar <= YYEOF)
    {
      yychar = yytoken = YYEOF;
      YYDPRINTF ((stderr, "Now at end of input.\n"));
    }
  else
    {
      yytoken = YYTRANSLATE (yychar);
      YY_SYMBOL_PRINT ("Next token is", yytoken, &yylval, &yylloc);
    }

  /* If the proper action on seeing token YYTOKEN is to reduce or to
     detect an error, take that action.  */
  yyn += yytoken;
  if (yyn < 0 || YYLAST < yyn || yycheck[yyn] != yytoken)
    goto yydefault;
  yyn = yytable[yyn];
  if (yyn <= 0)
    {
      if (yytable_value_is_error (yyn))
        goto yyerrlab;
      yyn = -yyn;
      goto yyreduce;
    }

  /* Count tokens shifted since error; after three, turn off error
     status.  */
  if (yyerrstatus)
    yyerrstatus--;

  /* Shift the lookahead token.  */
  YY_SYMBOL_PRINT ("Shifting", yytoken, &yylval, &yylloc);

  /* Discard the shifted token.  */
  yychar = YYEMPTY;

  yystate = yyn;
  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END

  goto yynewstate;


/*-----------------------------------------------------------.
| yydefault -- do the default action for the current state.  |
`-----------------------------------------------------------*/
yydefault:
  yyn = yydefact[yystate];
  if (yyn == 0)
    goto yyerrlab;
  goto yyreduce;


/*-----------------------------.
| yyreduce -- Do a reduction.  |
`-----------------------------*/
yyreduce:
  /* yyn is the number of a rule to reduce with.  */
  yylen = yyr2[yyn];

  /* If YYLEN is nonzero, implement the default value of the action:
     '$$ = $1'.

     Otherwise, the following line sets YYVAL to garbage.
     This behavior is undocumented and Bison
     users should not rely upon it.  Assigning to YYVAL
     unconditionally makes the parser a bit smaller, and it avoids a
     GCC warning that YYVAL may be used uninitialized.  */
  yyval = yyvsp[1-yylen];


  YY_REDUCE_PRINT (yyn);
  switch (yyn)
    {
        case 2:
#line 193 "anasint2.y" /* yacc.c:1646  */
    { 
				if (productionFeedBack) printf("programa-> declaracao_lista .\n");
				savedTree = (yyvsp[0]);
				}
#line 1460 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 3:
#line 199 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("declaracao_lista-> declaracao_lista declaracao .\n");
					YYSTYPE t = (yyvsp[-1]);
					if (t!=NULL){
						while(t->sibling != NULL) t = t->sibling;
						t->sibling = (yyvsp[0]);
						(yyval) = (yyvsp[-1]);
					}else{
						(yyval) = (yyvsp[0]);
					}
				}
#line 1476 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 4:
#line 211 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("declaracao_lista-> declaracao .\n");
					(yyval) = (yyvsp[0]);
				}
#line 1485 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 5:
#line 217 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("declaracao-> var_declaracao .\n");
					(yyval) = (yyvsp[0]);
				}
#line 1494 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 6:
#line 222 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("declaracao-> fun_declaracao .\n");
					(yyval) = (yyvsp[0]);
					savedFunction = "Global";
				}
#line 1504 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 7:
#line 228 "anasint2.y" /* yacc.c:1646  */
    {savedName = copyString(ids);savedLineNo = yylineno;}
#line 1510 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 8:
#line 229 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("var_declaracao-> tipo_especificador ID ;.\n");
					YYSTYPE t;
					t = newExpNode(IdK); /*cria um  nó do tipo Exp e manda o tipo IdK para simbolizar que é um id*/
					t->attr.name = savedName; /*copia a string da ID para o campo nome do nó*/
					t->lineno = savedLineNo; /*copia o numero da linha da ID para o campo line no do nó*/
					
					t->sibling = (yyval)->sibling;
					t->child[0] = (yyval)->child[0];
					t->child[1] = (yyval)->child[1];
					t->child[2] = (yyval)->child[2];					
					(yyval) = (yyvsp[-3]);
					(yyval)->sibling = NULL;
					(yyval)->child[0] = t;
					(yyval)->child[1] = NULL;
					(yyval)->child[2] = NULL;
					(yyval)->id_type = VarDecl;
					(yyval)->child[0]->id_type = VarDecl;
					(yyval)->scope = savedFunction;
					(yyval)->child[0]->type = (yyval)->type;
				}
#line 1536 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 9:
#line 250 "anasint2.y" /* yacc.c:1646  */
    {savedName = copyString(ids);savedLineNo = yylineno;}
#line 1542 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 10:
#line 250 "anasint2.y" /* yacc.c:1646  */
    {savedVal = atoi(ids);}
#line 1548 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 11:
#line 251 "anasint2.y" /* yacc.c:1646  */
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
					
					t->sibling = (yyval)->sibling;
					t->child[0] = r;
					t->child[1] = NULL;
					t->child[2] = NULL;
					r->child[0] = (yyval)->child[0];
					r->child[1] = (yyval)->child[1];
					r->child[2] = (yyval)->child[2];					
					(yyval) = (yyvsp[-7]);
					(yyval)->sibling = NULL;
					(yyval)->child[0] = t;
					(yyval)->child[1] = NULL;
					(yyval)->child[2] = NULL;
					(yyval)->id_type = VectorDecl;
					(yyval)->child[0]->id_type = VectorDecl;
					(yyval)->scope = savedFunction;
					(yyval)->child[0]->type = (yyval)->type;					
				}
#line 1581 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 12:
#line 281 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("tipo_especificador-> int .\n");
					(yyval) = newExpNode(DeclTypeK);
					(yyval)->type = Integer;
				}
#line 1591 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 13:
#line 287 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("tipo_especificador-> void .\n");
					(yyval) = newExpNode(DeclTypeK);
					(yyval)->type = Void;
				}
#line 1601 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 14:
#line 294 "anasint2.y" /* yacc.c:1646  */
    {savedName = copyString(ids);savedLineNo = yylineno; savedFunction = savedName;}
#line 1607 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 15:
#line 295 "anasint2.y" /* yacc.c:1646  */
    {
					
					if (productionFeedBack) printf("fun_declaracao-> tipo_especificador ID ( params ) composto_decl.\n");
					YYSTYPE t;
					t = newExpNode(IdK);     /*cria um  nó do tipo Exp e manda o tipo IdK para simbolizar que é um id*/
					t->attr.name = savedFunction; /*copia a string da ID para o campo nome do nó*/
					t->lineno = savedLineNo; /*copia o numero da linha da ID para o campo line no do nó*/
					
					t->sibling = (yyval)->sibling;
					t->child[0] = (yyvsp[-2]);
					t->child[1] = (yyvsp[0]);
					t->child[2] = NULL;					
					(yyval) = (yyvsp[-6]);
					(yyval)->sibling = NULL;
					(yyval)->child[0] = t;
					(yyval)->child[1] = NULL;
					(yyval)->child[2] = NULL;
					(yyval)->id_type = FuncDecl;
					(yyval)->child[0]->id_type = FuncDecl;
					(yyval)->child[0]->type = (yyval)->type;
					
				}
#line 1634 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 16:
#line 319 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("params-> param_lista .\n");
					(yyval) = (yyvsp[0]);
				}
#line 1643 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 17:
#line 324 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("params-> VOID .\n");
					(yyval) = NULL;
				}
#line 1652 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 18:
#line 330 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("param_lista-> param_lista , param .\n");
					YYSTYPE t = (yyvsp[-2]);
					if (t!=NULL){
						while(t->sibling != NULL) t = t->sibling;
						t->sibling = (yyvsp[0]);
						(yyval) = (yyvsp[-2]);
					}else{
						(yyval) = (yyvsp[0]);
					}
				}
#line 1668 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 19:
#line 342 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("param_lista-> param .\n");
					(yyval) = (yyvsp[0]);
				}
#line 1677 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 20:
#line 348 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("param-> tipo_especificador ID .\n");
					(yyval) = (yyvsp[-1]);
					(yyval)->child[0] = newExpNode(IdK);     /*cria um  nó do tipo Exp e manda o tipo IdK para simbolizar que é um id*/
					(yyval)->child[0]->attr.name = (yyvsp[0])->attr.name; /*copia a string da ID para o campo nome do nó*/				
					(yyval)->child[0]->lineno = (yyvsp[0])->lineno;
					(yyval)->id_type = FuncAttrVar;
					(yyval)->child[0]->id_type = FuncAttrVar;
					(yyval)->scope = savedFunction;
					(yyval)->child[0]->type = (yyval)->type;
				}
#line 1693 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 21:
#line 359 "anasint2.y" /* yacc.c:1646  */
    {savedName = copyString(ids);}
#line 1699 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 22:
#line 360 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("param-> tipo_especificador ID [ ] .\n");
					//YYSTYPE t;
					//t = newExpNode(IdK);     /*cria um  nó do tipo Exp e manda o tipo IdK para simbolizar que é um id*/
					//t->attr.name = savedName; /*copia a string da ID para o campo nome do nó*/
					//t->lineno = $1->lineno; /*copia o numero da linha da ID para o campo line no do nó*/
					(yyval) = (yyvsp[-4]);
					(yyval)->child[0] = (yyvsp[-3]);
					(yyval)->id_type = FuncAttrVector;
					(yyval)->child[0]->id_type = FuncAttrVector;
					(yyval)->scope = savedFunction;
					(yyval)->child[0]->type = (yyval)->type;
				}
#line 1717 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 23:
#line 375 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("composto_decl-> { local_declaracoes statement_lista } .\n");
					YYSTYPE t = (yyvsp[-2]);
					if (t!=NULL){
						while(t->sibling != NULL) t = t->sibling;
						t->sibling = (yyvsp[-1]);
						(yyval) = (yyvsp[-2]);
					}else{
						(yyval) = (yyvsp[-1]);
					}			
				}
#line 1733 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 24:
#line 388 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("local_declaracoes-> local_declaracoes var_declaracao .\n");
					YYSTYPE t = (yyvsp[-1]);
					if (t!=NULL){
						while(t->sibling != NULL) t = t->sibling;
						t->sibling = (yyvsp[0]);
						(yyval) = (yyvsp[-1]);
					}else{
						(yyval) = (yyvsp[0]);
					}				
				}
#line 1749 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 25:
#line 400 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("local_declaracoes-> vazio .\n");
					(yyval) = NULL;
				}
#line 1758 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 26:
#line 406 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("statement_lista-> statement_lista statement .\n");
					
					YYSTYPE t = (yyvsp[-1]);
					if (t!=NULL){
						while(t->sibling != NULL) t = t->sibling;
						t->sibling = (yyvsp[0]);
						(yyval) = (yyvsp[-1]);
					}else{
						(yyval) = (yyvsp[0]);
					}				
				}
#line 1775 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 27:
#line 419 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("statement_lista-> vazio .\n");
					(yyval) = NULL;
				}
#line 1784 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 28:
#line 425 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("statement-> expressao_decl .\n");
					(yyval) = (yyvsp[0]);			
				}
#line 1793 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 29:
#line 430 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("statement-> composto_decl .\n");
					(yyval) = (yyvsp[0]);			
				}
#line 1802 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 30:
#line 435 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("statement-> selecao_decl .\n");
					(yyval) = (yyvsp[0]);			
				}
#line 1811 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 31:
#line 440 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("statement-> iteracao_decl .\n");
					(yyval) = (yyvsp[0]);				
				}
#line 1820 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 32:
#line 445 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("statement-> retorno_decl .\n");
					(yyval) = (yyvsp[0]);			
				}
#line 1829 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 33:
#line 451 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("expressao_decl-> expressao ; .\n");
					(yyval) = (yyvsp[-1]);			
				}
#line 1838 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 34:
#line 456 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("expressao_decl-> ;.\n");
					(yyval) = (yyvsp[0]);			
				}
#line 1847 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 35:
#line 462 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("selecao_decl-> if ( expressao ) statement.\n");
					(yyval) = newStmtNode(IfK);
					(yyval)->child[0] = (yyvsp[-2]);
					(yyval)->child[1] = (yyvsp[0]);
				}
#line 1858 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 36:
#line 469 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("selecao_decl-> if ( expressao ) statement else statement.\n");
					(yyval) = newStmtNode(IfK);
					(yyval)->child[0] = (yyvsp[-4]);
					(yyval)->child[1] = (yyvsp[-2]);
					(yyval)->child[2] = (yyvsp[0]);
				}
#line 1870 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 37:
#line 478 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("iteracao_decl-> while ( expressao ) statement.\n");
					(yyval) = newStmtNode(WhileK);
					(yyval)->child[0] = (yyvsp[-2]);
					(yyval)->child[1] = (yyvsp[0]);
				}
#line 1881 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 38:
#line 486 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("retorno_decl-> return ;.\n");
					(yyval) = newStmtNode(ReturnK);
					(yyval)->child[0] = NULL;
				}
#line 1891 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 39:
#line 492 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("retorno_decl-> return expressao ;.\n");
					(yyval) = newStmtNode(ReturnK);
					(yyval)->child[0] = (yyvsp[-1]);
				}
#line 1901 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 40:
#line 499 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("expressao-> var = expressao.\n");
					(yyval) = newStmtNode(AssignK);
					(yyval)->child[0] = (yyvsp[-2]);
					(yyval)->child[1] = (yyvsp[0]);
					(yyval)->type = (yyvsp[-2])->type;
				}
#line 1913 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 41:
#line 507 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("expressao-> simples_expressao.\n");
					(yyval) = (yyvsp[0]);
				}
#line 1922 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 42:
#line 513 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("var-> ID.\n");
					(yyval) = newExpNode(IdK);
					(yyval)->attr.name = copyString(ids);
					(yyval)->id_type = Var;					
				}
#line 1933 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 43:
#line 519 "anasint2.y" /* yacc.c:1646  */
    {savedName = copyString(ids);savedLineNo = yylineno;}
#line 1939 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 44:
#line 520 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("var-> ID [ expressao ].\n");
					(yyval) = newExpNode(IdK);
					(yyval)->attr.name = savedName;
					(yyval)->lineno = savedLineNo;
					(yyval)->child[0] = (yyvsp[-1]);
					(yyval)->id_type = VectorPos;
				}
#line 1952 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 45:
#line 530 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("simples_expressao-> soma_expressao relacional soma_expressao.\n");
					(yyval) = newExpNode(OpK);
					(yyval)->attr.op = (yyvsp[-1])->attr.op;
					(yyval)->child[0] = (yyvsp[-2]);
					(yyval)->child[1] = (yyvsp[0]);
				}
#line 1964 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 46:
#line 538 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("simples_expressao-> soma_expressao.\n");
					(yyval) = (yyvsp[0]);
				}
#line 1973 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 47:
#line 544 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("relacional-> <=.\n");
					(yyval) = newExpNode(OpK);
					(yyval)->attr.op = LESSEQ;
				}
#line 1983 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 48:
#line 550 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("relacional-> <.\n");
					(yyval) = newExpNode(OpK);
					(yyval)->attr.op = LESS;
				}
#line 1993 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 49:
#line 556 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("relacional-> >.\n");
					(yyval) = newExpNode(OpK);
					(yyval)->attr.op = GREAT;
				}
#line 2003 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 50:
#line 562 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("relacional-> >=.\n");
					(yyval) = newExpNode(OpK);
					(yyval)->attr.op = GREATEQ;				
				}
#line 2013 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 51:
#line 568 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("relacional-> ==.\n");
					(yyval) = newExpNode(OpK);
					(yyval)->attr.op = EQUAL;
				}
#line 2023 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 52:
#line 574 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("relacional-> !=.\n");
					(yyval) = newExpNode(OpK);
					(yyval)->attr.op = NEQUAL;
				}
#line 2033 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 53:
#line 581 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("soma_expressao-> soma_expressao soma termo.\n");
					(yyval) = (yyvsp[-1]);
					if ((yyvsp[-2])->type == Integer && (yyvsp[0])->type == Integer){
						(yyvsp[-1])->type = Integer;
					}
					(yyval)->child[0] = (yyvsp[-2]);
					(yyval)->child[1] = (yyvsp[0]);
				}
#line 2047 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 54:
#line 591 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("soma_expressao-> termo.\n");
					(yyval) = (yyvsp[0]);
				}
#line 2056 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 55:
#line 597 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("soma-> +.\n");
					(yyval) = newExpNode(OpK);
					(yyval)->attr.op = ADD;
				}
#line 2066 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 56:
#line 603 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("soma-> - .\n");
					(yyval) = newExpNode(OpK);
					(yyval)->attr.op = SUB;				
				}
#line 2076 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 57:
#line 610 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("termo-> termo mult fator.\n");
					(yyval) = (yyvsp[-1]);
					if ((yyvsp[-2])->type == Integer && (yyvsp[0])->type == Integer){
						(yyvsp[-1])->type = Integer;
					}
					(yyval)->child[0] = (yyvsp[-2]);
					(yyval)->child[1] = (yyvsp[0]);
				}
#line 2090 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 58:
#line 620 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("termo-> fator.\n");
					(yyval) = (yyvsp[0]);
				}
#line 2099 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 59:
#line 626 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("mult-> *.\n");
					(yyval) = newExpNode(OpK);
					(yyval)->attr.op = MULT;
				}
#line 2109 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 60:
#line 632 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("mult-> /.\n");
					(yyval) = newExpNode(OpK);
					(yyval)->attr.op = DIV;
				}
#line 2119 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 61:
#line 639 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("fator-> ( expressao ).\n");
					(yyval) = (yyvsp[-1]);
				}
#line 2128 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 62:
#line 644 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("fator-> var.\n");
					(yyval) = (yyvsp[0]);
				}
#line 2137 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 63:
#line 649 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("fator-> ativacao.\n");
					(yyval) = (yyvsp[0]);
				}
#line 2146 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 64:
#line 654 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("fator-> NUMERO.\n");
					(yyval) = newExpNode(NumK);
					(yyval)->type = Integer;
					(yyval)->attr.val = atoi(ids);
				}
#line 2157 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 65:
#line 662 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("ativacao->ID ( args ).\n");
					(yyval) = newExpNode(IdK);
					(yyval)->attr.name = (yyvsp[-3])->attr.name;
					(yyval)->lineno = (yyvsp[-3])->lineno;
					(yyval)->child[0] = (yyvsp[-1]);
					(yyval)->id_type = Call;
				}
#line 2170 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 66:
#line 672 "anasint2.y" /* yacc.c:1646  */
    {
					(yyval) = newExpNode(IdK);
					(yyval)->attr.name = copyString(ids);
					savedName = copyString(ids);
					(yyval)->lineno = yylineno;
				}
#line 2181 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 67:
#line 680 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("args->arg_lista.\n");
					(yyval) = (yyvsp[0]);
				}
#line 2190 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 68:
#line 685 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("args->vazio.\n");
					(yyval) = NULL;
				}
#line 2199 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 69:
#line 691 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("arg_lista->arg_lista , expressao.\n");
					YYSTYPE t = (yyvsp[-2]);
					if (t!=NULL){
						while(t->sibling != NULL) t = t->sibling;
						t->sibling = (yyvsp[0]);
						(yyval) = (yyvsp[-2]);
					}else{
						(yyval) = (yyvsp[0]);
					}
				}
#line 2215 "anasint2.tab.c" /* yacc.c:1646  */
    break;

  case 70:
#line 703 "anasint2.y" /* yacc.c:1646  */
    {
					if (productionFeedBack) printf("arg_lista->expressao.\n");
					(yyval) = (yyvsp[0]);
				}
#line 2224 "anasint2.tab.c" /* yacc.c:1646  */
    break;


#line 2228 "anasint2.tab.c" /* yacc.c:1646  */
      default: break;
    }
  /* User semantic actions sometimes alter yychar, and that requires
     that yytoken be updated with the new translation.  We take the
     approach of translating immediately before every use of yytoken.
     One alternative is translating here after every semantic action,
     but that translation would be missed if the semantic action invokes
     YYABORT, YYACCEPT, or YYERROR immediately after altering yychar or
     if it invokes YYBACKUP.  In the case of YYABORT or YYACCEPT, an
     incorrect destructor might then be invoked immediately.  In the
     case of YYERROR or YYBACKUP, subsequent parser actions might lead
     to an incorrect destructor call or verbose syntax error message
     before the lookahead is translated.  */
  YY_SYMBOL_PRINT ("-> $$ =", yyr1[yyn], &yyval, &yyloc);

  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);

  *++yyvsp = yyval;

  /* Now 'shift' the result of the reduction.  Determine what state
     that goes to, based on the state we popped back to and the rule
     number reduced by.  */

  yyn = yyr1[yyn];

  yystate = yypgoto[yyn - YYNTOKENS] + *yyssp;
  if (0 <= yystate && yystate <= YYLAST && yycheck[yystate] == *yyssp)
    yystate = yytable[yystate];
  else
    yystate = yydefgoto[yyn - YYNTOKENS];

  goto yynewstate;


/*--------------------------------------.
| yyerrlab -- here on detecting error.  |
`--------------------------------------*/
yyerrlab:
  /* Make sure we have latest lookahead translation.  See comments at
     user semantic actions for why this is necessary.  */
  yytoken = yychar == YYEMPTY ? YYEMPTY : YYTRANSLATE (yychar);

  /* If not already recovering from an error, report this error.  */
  if (!yyerrstatus)
    {
      ++yynerrs;
#if ! YYERROR_VERBOSE
      yyerror (YY_("syntax error"));
#else
# define YYSYNTAX_ERROR yysyntax_error (&yymsg_alloc, &yymsg, \
                                        yyssp, yytoken)
      {
        char const *yymsgp = YY_("syntax error");
        int yysyntax_error_status;
        yysyntax_error_status = YYSYNTAX_ERROR;
        if (yysyntax_error_status == 0)
          yymsgp = yymsg;
        else if (yysyntax_error_status == 1)
          {
            if (yymsg != yymsgbuf)
              YYSTACK_FREE (yymsg);
            yymsg = (char *) YYSTACK_ALLOC (yymsg_alloc);
            if (!yymsg)
              {
                yymsg = yymsgbuf;
                yymsg_alloc = sizeof yymsgbuf;
                yysyntax_error_status = 2;
              }
            else
              {
                yysyntax_error_status = YYSYNTAX_ERROR;
                yymsgp = yymsg;
              }
          }
        yyerror (yymsgp);
        if (yysyntax_error_status == 2)
          goto yyexhaustedlab;
      }
# undef YYSYNTAX_ERROR
#endif
    }



  if (yyerrstatus == 3)
    {
      /* If just tried and failed to reuse lookahead token after an
         error, discard it.  */

      if (yychar <= YYEOF)
        {
          /* Return failure if at end of input.  */
          if (yychar == YYEOF)
            YYABORT;
        }
      else
        {
          yydestruct ("Error: discarding",
                      yytoken, &yylval);
          yychar = YYEMPTY;
        }
    }

  /* Else will try to reuse lookahead token after shifting the error
     token.  */
  goto yyerrlab1;


/*---------------------------------------------------.
| yyerrorlab -- error raised explicitly by YYERROR.  |
`---------------------------------------------------*/
yyerrorlab:

  /* Pacify compilers like GCC when the user code never invokes
     YYERROR and the label yyerrorlab therefore never appears in user
     code.  */
  if (/*CONSTCOND*/ 0)
     goto yyerrorlab;

  /* Do not reclaim the symbols of the rule whose action triggered
     this YYERROR.  */
  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);
  yystate = *yyssp;
  goto yyerrlab1;


/*-------------------------------------------------------------.
| yyerrlab1 -- common code for both syntax error and YYERROR.  |
`-------------------------------------------------------------*/
yyerrlab1:
  yyerrstatus = 3;      /* Each real token shifted decrements this.  */

  for (;;)
    {
      yyn = yypact[yystate];
      if (!yypact_value_is_default (yyn))
        {
          yyn += YYTERROR;
          if (0 <= yyn && yyn <= YYLAST && yycheck[yyn] == YYTERROR)
            {
              yyn = yytable[yyn];
              if (0 < yyn)
                break;
            }
        }

      /* Pop the current state because it cannot handle the error token.  */
      if (yyssp == yyss)
        YYABORT;


      yydestruct ("Error: popping",
                  yystos[yystate], yyvsp);
      YYPOPSTACK (1);
      yystate = *yyssp;
      YY_STACK_PRINT (yyss, yyssp);
    }

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END


  /* Shift the error token.  */
  YY_SYMBOL_PRINT ("Shifting", yystos[yyn], yyvsp, yylsp);

  yystate = yyn;
  goto yynewstate;


/*-------------------------------------.
| yyacceptlab -- YYACCEPT comes here.  |
`-------------------------------------*/
yyacceptlab:
  yyresult = 0;
  goto yyreturn;

/*-----------------------------------.
| yyabortlab -- YYABORT comes here.  |
`-----------------------------------*/
yyabortlab:
  yyresult = 1;
  goto yyreturn;

#if !defined yyoverflow || YYERROR_VERBOSE
/*-------------------------------------------------.
| yyexhaustedlab -- memory exhaustion comes here.  |
`-------------------------------------------------*/
yyexhaustedlab:
  yyerror (YY_("memory exhausted"));
  yyresult = 2;
  /* Fall through.  */
#endif

yyreturn:
  if (yychar != YYEMPTY)
    {
      /* Make sure we have latest lookahead translation.  See comments at
         user semantic actions for why this is necessary.  */
      yytoken = YYTRANSLATE (yychar);
      yydestruct ("Cleanup: discarding lookahead",
                  yytoken, &yylval);
    }
  /* Do not reclaim the symbols of the rule whose action triggered
     this YYABORT or YYACCEPT.  */
  YYPOPSTACK (yylen);
  YY_STACK_PRINT (yyss, yyssp);
  while (yyssp != yyss)
    {
      yydestruct ("Cleanup: popping",
                  yystos[*yyssp], yyvsp);
      YYPOPSTACK (1);
    }
#ifndef yyoverflow
  if (yyss != yyssa)
    YYSTACK_FREE (yyss);
#endif
#if YYERROR_VERBOSE
  if (yymsg != yymsgbuf)
    YYSTACK_FREE (yymsg);
#endif
  return yyresult;
}
#line 709 "anasint2.y" /* yacc.c:1906  */


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

TreeNode* return_Func_Decl_scope(TreeNode * tree, char* scope){
	if(tree!=NULL){
		if (tree->id_type == FuncDecl){	
			if(tree->child[0]!=NULL){			
				if (tree->child[0]->id_type == FuncDecl){
					if (strcmp(tree->child[0]->attr.name,scope)==0){
						return tree->child[0]->child[0];
					}
				}
			}	
		}
		if (return_Func_Decl_scope(tree->sibling,scope)!=NULL){
			return return_Func_Decl_scope(tree->sibling,scope);
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
	// char* cont;
	char * s;	
	// cont = (char*)malloc(6*sizeof(char));
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
				// sprintf(cont, "%d", (*contador)%200);
				tree->child[0] = update_scope(tree->child[0], contador, limite, scope);
				// s = scope;
				
				// scope = concat(s,concat("->if",cont));
				// (*contador)++;
				
				tree->child[1] = update_scope(tree->child[1], contador, limite, scope);
				
				// scope = concat(s,concat("->else",cont));
				// (*contador)++;
				
				tree->child[2] = update_scope(tree->child[2], contador, limite, scope);
				// scope = s;
				tree->sibling = update_scope(tree->sibling, contador, limite, scope);
				return tree;
			}else{
				if (tree->kind.stmt == WhileK){
					// s = scope;
					tree->child[0] = update_scope(tree->child[0], contador, limite, scope);					
					tree->scope_number = (*contador);
					tree->scope = scope;
					// scope = concat(s,concat("->while",cont));
					// (*contador)++;
					tree->child[1] = update_scope(tree->child[1], contador, limite, scope);
					tree->child[2] = update_scope(tree->child[2], contador, limite, scope);
					// scope = s;
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
// int hash_calc(char *nameID) {
	// int key = 0;
	// int i;
	// for(i = 0; i < strlen(nameID)+1; i++) {
		// key = (key + nameID[i])%hash_size;	
	// }
	// if(TabGenFeedBack) printf("Chave calculada: %d - %s\n",key,nameID);
	// return key;
// }

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
		if(!strcmp(p->ID,name) && ((p->id_type == VarDecl)||(p->id_type == VectorDecl)||(p->id_type == FuncAttrVar) || (p->id_type == FuncAttrVector))) {
			
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
		if(!strcmp(p->ID,name) && ((p->id_type == VarDecl)||(p->id_type == VectorDecl)||(p->id_type == FuncAttrVar) || (p->id_type == FuncAttrVector))) {
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
				if(TabGenFeedBack) printf("return_node_symbol_decl() says: id encontrada\n\n");		
				return p;
			}else{
				if (!strcmp(p->scope,"Global")){//verifica se a declaracao esta no global
					if(TabGenFeedBack) printf("return_node_symbol_decl() says: id encontrada\n\n");
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
		if (key == 108){
			if(TabGenDebug) printf("\n\n*****************\n");
			if(TabGenDebug) printf("NOME DA VARIAVEL: %s\n", HashVec[key].begin->ID);
			if(TabGenDebug) printf("LINHA DA VARIAVEL: %d\n", sym->lines[0]);
			 if(TabGenDebug) printf("ENDERECO DA VARIAVEL: %p\n", (void*)(HashVec[key].begin->ID));
			if(TabGenDebug) printf("*****************\n\n");
		}
		
		if(TabGenFeedBack) printf("Símbolo <%s> inserido com sucesso em [%d]!\n\n",sym->ID,key);
	
	} else {
		if(TabGenFeedBack) printf("Colisão, encadeando símbolo\n");
		
		if(!strcmp(p->ID,sym->ID) && !strcmp(p->scope,sym->scope)) {
			if (p->id_type == sym->id_type){
				if(TabGenFeedBack) printf("Atualização de linha <%s> inserida com sucesso em [%d]!\n\n",sym->ID,key);
				if (key == 108){
					if(TabGenDebug) printf("\n\n*****************\n");
					if(TabGenDebug) printf("NOME DA VARIAVEL: %s\n", p->ID);
					if(TabGenDebug) printf("LINHA DA VARIAVEL: %d\n", sym->lines[0]);
					if(TabGenDebug) printf("ENDERECO DA VARIAVEL: %p\n", (void*)(p->ID));
					if(TabGenDebug) printf("*****************\n\n");
				}
				flag_finished = 1;
				p->lines[p->top] = sym->lines[0];
				p->top++;
			}
		}
		while(p->nxt != NULL) {
			if(!strcmp(p->nxt->ID,sym->ID)) {
				if (!strcmp(p->nxt->scope,sym->scope)){
					if (p->nxt->id_type == sym->id_type){
						if(TabGenFeedBack) printf("Atualização de linha <%s> inserida com sucesso em [%d]!\n\n",sym->ID,key);
				
						if (key == 108){
							if(TabGenDebug) printf("\n\n*****************\n");
							if(TabGenDebug) printf("NOME DA VARIAVEL: %s\n", p->nxt->ID);
							if(TabGenDebug) printf("LINHA DA VARIAVEL: %d\n", sym->lines[0]);
							if(TabGenDebug) printf("ENDERECO DA VARIAVEL: %p\n", (void*)(p->nxt->ID));
							if(TabGenDebug) printf("*****************\n\n");
						}
						flag_finished = 1;
						p->nxt->lines[p->nxt->top] = sym->lines[0];
						p->nxt->top++;
					}
				}
			}
			p = p->nxt; 
			
		}
		if (flag_finished == 0){
			p->nxt = sym;
			if (key == 108){
				if(TabGenDebug) printf("\n\n*****************\n");
				if(TabGenDebug) printf("NOME DA VARIAVEL: %s\n", p->nxt->ID);
				if(TabGenDebug) printf("LINHA DA VARIAVEL: %d\n", sym->lines[0]);
				if(TabGenDebug) printf("ENDERECO DA VARIAVEL: %p\n", (void*)(p->nxt->ID));
				if(TabGenDebug) printf("*****************\n\n");
			}
			if(TabGenFeedBack) printf("Símbolo <%s> inserido com sucesso em [%d]!\n\n",sym->ID,key);
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
	for(i = 0; i < size_lines; i++) {
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

int flag_call = 0;

void TabGen(TreeNode *tree) {
	Symbol *newSymbol = NULL;
	Symbol *p = NULL;
	TreeNode *temp;
	int key;
	if(tree != NULL){
		switch(tree->nodekind){
			case ExpK:
				switch(tree->kind.exp){
					case IdK:
					// if(TabGenDebug) printf("NOMEEEEEEE: %s\n", tree->attr.name);
					// if(TabGenDebug) printf("do ID_Type: %s\n", returnIDType(tree->id_type));
					// if(TabGenDebug) printf("flag_call: %d\n", flag_call);
					// if(TabGenDebug) printf("linha: %d\n", tree->lineno);
					key = hash_calc(tree->attr.name);
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
											flag_call = 1;
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
								if(flag_call == 1) flag_call = 0;
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
								if(flag_call == 1) flag_call = 0;
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
										newSymbol = allocateSymbol(tree->attr.name,tree->id_type,returnType(tree->type),tree->scope,tree->child[0]->attr.val,tree->lineno,tree);
										insert_symbol(newSymbol,key);									
									}
								}
								break;
							case FuncDecl:
								if(flag_call == 1) flag_call = 0;
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
										
										newSymbol = allocateSymbol(tree->attr.name,tree->id_type,returnType(Integer),tree->scope,1,tree->lineno,tree);
										
										// if(TabGenDebug) printf("ESCOPO DA VARIAVEL: %s\n", newSymbol->scope);
										insert_symbol(newSymbol,key);
																			
									}else{
										if(flag_call == 1){
											if(tree->child[0] != NULL) printf("AQUIIIIIIIIII %s\n",returnIDType(tree->child[0]->id_type));
											newSymbol = allocateSymbol(tree->attr.name,VectorPos,returnType(Integer),tree->scope,1,tree->lineno,tree);
											insert_symbol(newSymbol,key);		
										}else{
											if(ShowSemanticalErrors) printf("Erro Semântico na linha %d: A ",tree->lineno);
											if(ShowSemanticalErrors) printf("%s ",returnIDType(tree->id_type));
											if(ShowSemanticalErrors) printf("'%s' eh variavel quando era para ser vetor de acordo com a linha ",tree->attr.name);
											if(ShowSemanticalErrors) printf("%d .\n",temp->lineno);
											semantical_error = 1;
										}
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
						if(flag_call == 1) flag_call = 0;
						break;
					case WhileK:
						if(flag_call == 1) flag_call = 0;
						break;
					case AssignK:
						if(flag_call == 1) flag_call = 0;
						break;
					case ReturnK:
						if(flag_call == 1) flag_call = 0;
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
		 printf("LINHA statement: %d\n",tree->lineno);
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
									}else{
										
									}
								}
							}
						}
						
						if (tree->child[2]!=NULL){	
							if(tree->child[2]->kind.exp == IdK){
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
						printf("Verify_stetment eh AssignK: \n");
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
						printf("Verify_stetment eh ReturnK: \n");
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

void changeTable_scope(int index) {
  int i;
  Symbol *p = HashVec[index].begin;
	while(p!=NULL){
		if (p->ID !=NULL){
			char* s;
			s = (char*)malloc(256*sizeof(char));
			strcpy(s, p->ID);
		}
	  if(strstr(p->scope,"->")!= NULL){
		char* temp = strtok(p->scope,"->");
		if (temp!= NULL) p->scope = temp;
	  }
      p = p->nxt;
	}
	
}

void changeTable_merge(int index) {
  int i;
  Symbol *p = HashVec[index].begin;
  while(p!=NULL){
	  if(p->nxt != NULL){
		if(strcmp(p->scope,p->nxt->scope) == 0){
			if(strcmp(p->ID,p->nxt->ID) == 0){
				if(p->id_type == p->nxt->id_type){
					for (i =0;i<p->nxt->top;i++){
						p->lines[p->top+i] = p->nxt->lines[i];
					}
					p->top = p->top + p->nxt->top;
					p->nxt = p->nxt->nxt;
				}
			}
		}
	  }
      p = p->nxt;
  }
}

void printWTable(int index) {
  int i;
  Symbol *p = HashVec[index].begin;
  while(p!=NULL){
      i = 0;
	  if(p->lines[0] != 0) {
		if(TabGenFeedBack)printf("%-16d  %-16s %-16s %-19s %-12s %-14d %-14d", index, p->ID, returnIDType(p->id_type), p->data_type, p->scope, p->size, p->top);
		 fprintf(listing,"%-16d  %-16s %-16s %-19s %-12s %-14d %-14d", index, p->ID, returnIDType(p->id_type), p->data_type, p->scope, p->size, p->top);
        while(p->lines[i]!=0){
			if(TabGenFeedBack)printf("%d", p->lines[i]);
		  fprintf(listing,"%d", p->lines[i]);
		  if(TabGenFeedBack){
			  if(i < p->top-1) printf(", ");
		  }
		  if(i < p->top-1) fprintf(listing,", ");
		  i++;
        }		
			if(TabGenFeedBack)printf("\n");
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
	fprintf(listing,"| Entrada   +   Nome do ID   +   Tipo de ID   +   Tipo de Dados   +     Escopo   +   SIZE   +   N. Ocorrencias   +    Linhas   |\n");
	fprintf(listing,"|-----------------------------------------------------------------------------------------------------------------------|\n");	
	int i;	
	for(i = 0;i<211;i++){
    if(&HashVec[i] != NULL)
    printWTable(i);
	}
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


typedef enum {LD, ST, COND_IF, COND_IF_F, LOOP_WHILE, LOOP_WHILE_F, INTCODE_ADD, INTCODE_SUB, INTCODE_MUL, INTCODE_DIV, INTCODE_LT, INTCODE_LEQ, INTCODE_GT, INTCODE_GEQ, INTCODE_EQ, INTCODE_NEQ, INTCODE_ASSIGN, INTCODE_RET, ARG, FUNDEF, FUNCAL, BEGIN_ARGS, JMP, LABEL} OpKind;

typedef enum {Vazio, ConstInt, String, Label} AddrKind; //diz qual o tipo de dado que esta no no da lista. Serve para alocar a quantidade correta de bits para o dado.

typedef enum {StringArr, NumberArr} ArrayPosType;


typedef struct t_contents
{
	
	int val;
	char nome[30] = "";
	char label[10] = "";
} content;

typedef struct 
{
	AddrKind kind;
	content contents;
	char* escopo;
	
}Address;


typedef struct quad_addr
{
	OpKind op;
	Address addr_01, addr_02, addr_03;
}Quad_Cell;

///ponteiro pra lista: Quad_List* aux;
///aux->quad.addr_01.contents.nome


typedef struct quad_addr_lista
{
	Quad_Cell quad;
	quad_addr_lista* next;
}Quad_List;

Quad_List * AlocaQuad(OpKind op, Address val1, Address val2, Address res)
{
	Quad_List* aux = (Quad_List*) malloc(sizeof(Quad_List));
	Quad_Cell q;
	q.op = op;
	q.addr_01 = val1;
	q.addr_01.kind = val1.kind;
	q.addr_02 = val2;
	q.addr_02.kind = val2.kind;
	q.addr_03 = res;
	q.addr_03.kind = res.kind;
	aux->quad = q;
	aux->next = NULL;
	return aux;
}

Quad_List * codigo_inter = NULL;

char * EMPTY_STRING = "";

void insereBloco(OpKind op, Address val1, Address val2, Address res);

void clearAddr(Address* addr)
{
	addr->kind = Vazio;
	//addr->contents.nome = NULL;
	addr->escopo = EMPTY_STRING;
}

char* returnToken(OpKind op)
{
	switch(op){
		case INTCODE_ADD: 		{return "add"		; break;}
		case INTCODE_SUB: 		{return "sub"		; break;}
		case INTCODE_MUL: 		{return "mul"		; break;}
		case INTCODE_DIV: 		{return "div"		; break;}
		case INTCODE_EQ:	 	{return "eq"		; break;}
		case INTCODE_NEQ:	 	{return "neq"	 	; break;}
		case INTCODE_GEQ:		{return "geq" 		; break;}
		case INTCODE_GT: 		{return "gt"		; break;}
		case INTCODE_LT: 		{return "lt"	 	; break;}
		case INTCODE_LEQ: 		{return "leq" 		; break;}
		case INTCODE_ASSIGN: 	{return "st"		; break;}
		case LD: 				{return "ld"		; break;}
		case ST:				{return "store"		; break;}
		case COND_IF: 			{return "if_true"	; break;}
		case COND_IF_F: 		{return "if_false"	; break;}
		case LOOP_WHILE: 		{return "if_true"	; break;}
		case LOOP_WHILE_F: 		{return "if_false"	; break;}
		case INTCODE_RET: 		{return "ret"		; break;}
		case ARG: 				{return "arg"		; break;}
		case FUNDEF: 			{return "fundef"	; break;}
		case FUNCAL: 			{return "funcal"	; break;}
		case BEGIN_ARGS: 		{return "begin_args"; break;}
		case JMP: 				{return "jmp"		; break;}
		case LABEL:				{return "label"		; break;}
		default:				{return "fodeu"		; break;}
	}
}

void imprimeAddr(Address addr)
{
	switch(addr.kind)
	{
		case Vazio:
		{
			printf("%s\n", "_");
			break;
		}
		case ConstInt:
		{
			printf("%d\n", addr.contents.val);
			break;
		}
		case String:
		{
			printf("%s\n", addr.contents.nome);
			break;
		}
		case Label:
		{
			printf("%s\n", addr.contents.label);
			break;
		}
		default:
		{
			
		}
	}
}

void imprimeQuad(Quad_Cell quad)
{
	char linha[120];
	char* operando;
	char op1[30] = "";
	char op2[30] = "";
	char op3[30] = "";
	operando = returnToken(quad.op);
	switch(quad.addr_01.kind)
	{
		case Vazio:
		{
			sprintf(op1, "%s", "_");
			break;
		}
		case ConstInt:
		{
			sprintf(op1, "%d", quad.addr_01.contents.val);
			break;
		}
		case String:
		{
			sprintf(op1, "%s", quad.addr_01.contents.nome);
			break;
		}
		case Label:
		{
			sprintf(op1, "%s",quad.addr_01.contents.label);
			break;
		}
		default:
		{
			sprintf(op1, "%s", quad.addr_01.contents.nome);
		}
	}
	switch(quad.addr_02.kind)
	{
		case Vazio:
		{
			sprintf(op2, "%s", "_");
			break;
		}
		case ConstInt:
		{
			sprintf(op2, "%d", quad.addr_02.contents.val);
			break;
		}
		case String:
		{
			sprintf(op2, "%s", quad.addr_02.contents.nome);
			break;
		}
		case Label:
		{
			sprintf(op2, "%s", quad.addr_02.contents.label);
			break;
		}
		default:
		{
			sprintf(op2, "%s", quad.addr_02.contents.nome);
		}
	}
	switch(quad.addr_03.kind)
	{
		case Vazio:
		{
			sprintf(op3, "%s", "_");
			break;
		}
		case ConstInt:
		{
			sprintf(op3, "%d", quad.addr_03.contents.val);
			break;
		}
		case String:
		{
			sprintf(op3, "%s", quad.addr_03.contents.nome);
			break;
		}
		case Label:
		{
			sprintf(op3, "%s", quad.addr_03.contents.label);
			break;
		}
		default:
		{
			sprintf(op3, "%s", quad.addr_03.contents.nome);
		}
	}
	// printf("(%s,%s,%s,%s)\n", operando,op1,op2,op3);
}

int CONTADOR_DE_BUGS = 0;

void printFromBegining()
{
	Quad_List* aux;
	aux = codigo_inter;
	CONTADOR_DE_BUGS++;
	printf("IMPRESSAO: %d -----------------\n", CONTADOR_DE_BUGS);
	while(aux!=NULL)
	{
		imprimeQuad(aux->quad);
		aux = aux->next;
	}
}


void insereBloco(OpKind op, Address val1, Address val2, Address res)
{
	// printf("CONTADOR DE IMPRESSAO:%d\n", CONTADOR_DE_BUGS++);
	if(codigo_inter == NULL)
		{
			codigo_inter = AlocaQuad(op, val1, val2, res);
		}
		else{
			Quad_List* aux, *aux2;
			aux = codigo_inter;
			while(aux->next!=NULL) 
			{
				aux = aux->next;
			}
			aux2 = AlocaQuad(op, val1, val2, res);
			aux->next = aux2;
		}
}


int tempVariableCounter = 0;
char str[50];
char str_array[50];

FILE *fp = fopen("IntermCode.txt", "w+");
FILE *intermCode = fopen("CodigoIntermediario.txt", "w+");
FILE *asmCode = fopen("AsmCode.txt", "w+");

void imprimeIntermedCode()
{
	printf("Imprimindo Codigo Intermediario...\n");
	char* operando;
	char op1[30] = "";
	char op2[30] = "";
	char op3[30] = "";
	int counter = 0;
	Quad_List* start;
	start = codigo_inter;
	while(codigo_inter!=NULL)
	{
		operando = returnToken(codigo_inter->quad.op);
		switch(codigo_inter->quad.addr_01.kind)
		{
			case Vazio:
			{
				sprintf(op1, "%s", "_");
				break;
			}
			case ConstInt:
			{
				sprintf(op1, "%d", codigo_inter->quad.addr_01.contents.val);
				// printf("ACHOU INTEIRO");
				break;
			}
			case String:
			{
				sprintf(op1, "%s", codigo_inter->quad.addr_01.contents.nome);
				break;
			}
			case Label:
			{
				sprintf(op1, "%s",codigo_inter->quad.addr_01.contents.label);
				break;
			}
			default:
			{
				sprintf(op1, "%s", codigo_inter->quad.addr_01.contents.nome);
			}
		}
		switch(codigo_inter->quad.addr_02.kind)
		{
			case Vazio:
			{
				sprintf(op2, "%s", "_");
				break;
			}
			case ConstInt:
			{
				sprintf(op2, "%d", codigo_inter->quad.addr_02.contents.val);
				// printf("ACHOU INTEIRO");
				break;
			}
			case String:
			{
				sprintf(op2, "%s", codigo_inter->quad.addr_02.contents.nome);
				break;
			}
			case Label:
			{
				sprintf(op2, "%s", codigo_inter->quad.addr_02.contents.label);
				break;
			}
			default:
			{
				sprintf(op2, "%s", codigo_inter->quad.addr_02.contents.nome);
			}
		}
		switch(codigo_inter->quad.addr_03.kind)
		{
			case Vazio:
			{
				sprintf(op3, "%s", "_");
				break;
			}
			case ConstInt:
			{
				sprintf(op3, "%d", codigo_inter->quad.addr_03.contents.val);
				// printf("ACHOU INTEIRO");
				break;
			}
			case String:
			{
				sprintf(op3, "%s", codigo_inter->quad.addr_03.contents.nome);
				break;
			}
			case Label:
			{
				sprintf(op3, "%s", codigo_inter->quad.addr_03.contents.label);
				break;
			}
			default:
			{
				sprintf(op3, "%s", codigo_inter->quad.addr_03.contents.nome);
			}
		}
		fprintf(intermCode, "%*d: (%s,%s,%s,%s)\n", 5, counter, operando, op1, op2, op3);
		counter++;
		imprimeQuad(codigo_inter->quad);
		codigo_inter = codigo_inter->next;
	}
	codigo_inter = start;
	fclose(intermCode);
}


int labelCounter = 0;

int tempVarCounter = 0;

char toFile[100];

char tempVar[50];

char labels[10]; 

void CodeGen(TreeNode* root);

char jump[] = "goto";

int FUNCTION_SEARCH = 0;


Address processExp(TreeNode* root);

//Args eh um ponteiro de address que vai indicar o comeco do array de argumentos
//retorna um int indicando quantos argumentos tem
void genArguments(TreeNode* root) //funcao retorna um array de 
{
	Address arg;
	Address nil;
	clearAddr(&arg);
	clearAddr(&nil);
	OpKind op = ARG;
	TreeNode* aux;
	aux = root;
	// printf("entrou aqui. Gen Arguments\n");
	while(aux != NULL)
	{
		if(aux->codeGen!=1)
		{
			arg = processExp(aux);
			arg.escopo = root->scope;
			if(arg.kind == String) fprintf(fp, "(%s,%s,_,_)\n", "arg",arg.contents.nome ); 
			if(arg.kind == ConstInt) fprintf(fp, "(%s,%d,_,_)\n", "arg",arg.contents.val );
			insereBloco(op, arg, nil, nil);
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
		//printf("procurando funcao %s. Analizando: %s \n", nome, ret);
		ret = strstr(stream, nome);
		if(ret != NULL )
		{
			//printf("achou funcao %s no arquivo\n", ret);
			while(1)
			{
				//printf("%s esta dentro do while\n", ret);
				ret = fgets(stream, 50, fp);
				// printf("Esta dentro do while: %s", ret);
				if(ret == NULL)
				{
					// printf("NULL\n");
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
							// printf("Temp de retorno : %s\n", FUNCTION_RETURN);
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

char actualFuncion[1000] = "";
char lastFuncion[1000] = "";
char numOfRets = 0;
int FLAG_newFunction = 0;

Address processExp(TreeNode* root)
{
	if(root!=NULL)
	{
		switch(root->nodekind)
		{
			
			case ExpK:
			{
				///operacoes matematicas e logicas em pos-ordem
				///primeiro trata os dois filhos, depois trata a raiz
				
				switch(root->kind.exp)
				{
					case OpK:
					{
						Address *temp;
						Address op1, op2;
						clearAddr(&op1);
						clearAddr(&op2);
						
						char charOp1[50], charOp2[50];
						//if abaixo trata arrays. Nao muda se nao buga.
						if(root->child[0]->id_type == VectorPos)  
						{
							clearAddr(&op1);
							op1 = processExp(root->child[0]);
							if(op1.kind!= Vazio){
								if(op1.kind == String)sprintf(op1.contents.nome, "%s", op1.contents.nome);
								if(op1.kind == ConstInt)sprintf(op1.contents.nome, "%d", op1.contents.val);
								// op1.contents.nome = charOp1;
								// printf("CharOp1:%s\n", charOp1);
								// printf("op1.contents.nome:%s\n", op1.contents.nome);
								op1.escopo = root->scope;
								op1.kind = String;
								//printf("opreando 1 eh vetor: %s\n", op1.contents.nome);
								root->child[0]->codeGen = 1;
							}
						}
						else 
						{
							clearAddr(&op1);
							op1 = processExp(root->child[0]);///filho esquerdo tratado
							op1.escopo = root->scope;
							root->child[0]->codeGen = 1;
						}
						if(root->child[1]->id_type == VectorPos)
						{
							clearAddr(&op2);
							op2 = processExp(root->child[1]);
							if(op2.kind!=Vazio) {
								if(op2.kind == String)sprintf(op2.contents.nome, "%s", op2.contents.nome);
								if(op2.kind == ConstInt)sprintf(op2.contents.nome, "%d", op2.contents.val);
								// op2.contents.nome = charOp2;
								// printf("CharOp2:%s\n", charOp2);
								// printf("op2.contents.nome:%s\n", op2.contents.nome);
								op2.kind = String;
								op2.escopo = root->scope;
								// printf("opreando 2 eh vetor: %s\n", op2.contents.nome);
								root->child[1]->codeGen = 1;
							}
						}
						else
						{
							clearAddr(&op2);
							op2 = processExp(root->child[1]);///filho direito tratado
							op2.escopo = root->scope;
							root->child[1]->codeGen = 1;
							
						}
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
								printf("Operando nao reconhecido \n");
								exit(1);
							}
						}
						///gera um temporario pra armazenar o resultado;
						sprintf(tempVar, "_TEMP%d_", tempVarCounter);
						tempVarCounter++;
						char *local_tempVar = (char*)malloc(sizeof(char)*50);
						for(int i = 0; i<50; i++)
						{
							local_tempVar[i] = tempVar[i];
						}
						
						//printf("local_tempVar: %s\n", local_tempVar);
						if(op1.kind == String && op2.kind == String)sprintf(toFile, "(%s,%s,%s,%s)\n", returnToken(op), op1.contents.nome, op2.contents.nome, tempVar);
						if(op1.kind == ConstInt && op2.kind == String)sprintf(toFile, "(%s,%d,%s,%s)\n", returnToken(op), op1.contents.val, op2.contents.nome, tempVar);
						if(op1.kind == String && op2.kind == ConstInt)sprintf(toFile, "(%s,%s,%d,%s)\n", returnToken(op), op1.contents.nome, op2.contents.val, tempVar);
						if(op1.kind == ConstInt && op2.kind == ConstInt)sprintf(toFile, "(%s,%d,%d,%s)\n", returnToken(op), op1.contents.val, op2.contents.val, tempVar);
						fprintf(fp, "%s", toFile);
						Address retVal;
						sprintf(retVal.contents.nome, "%s", local_tempVar);
						retVal.kind = String;
						root->codeGen = 1;
						insereBloco(op, op1, op2, retVal);
						return retVal;
						break;
					}
					case NumK:
					{
						Address returnVal;
						if(root->codeGen != 1){
							//printf("NumK (processExp)\n");
							Address returnVal;
							clearAddr(&returnVal);
							returnVal.contents.val = root->attr.val;
							returnVal.kind = ConstInt;
							returnVal.escopo = root->scope;
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
								// if(strcmp(actualFuncion, "") == 0 && strcmp(lastFuncion, "") == 0)
								// {
									// strcpy(actualFuncion, root->attr.name);
									// strcpy(lastFuncion, root->attr.name);
								// }else
								// {	
									// strcpy(lastFuncion, actualFuncion);
									// strcpy(actualFuncion, root->attr.name);
									// if(strcmp(lastFuncion, actualFuncion)!= 0)FLAG_newFunction = 1;
								// }
								// printf("----------------- %s ----------------\n", actualFuncion);
								Address ad1, ad2, ad3;
								clearAddr(&ad1);
								clearAddr(&ad2);
								clearAddr(&ad3);
								OpKind operation;
								char * entrada = "fundef";
								sprintf(ad1.contents.nome, "%s", root->attr.name);
								ad1.escopo = root->scope;
								ad1.kind = String;
								ad2.kind = Vazio;
								ad3.kind = Vazio;
								insereBloco(FUNDEF, ad1, ad2, ad3);
								fprintf(fp, "(%s,%s,_,_)\n", entrada, root->attr.name);
								if(root->child[1]!=NULL)CodeGen(root->child[1]); //primeiro filho da funcao tem parametros, segundo tem codigo
								else fprintf(fp, "(nop,_,_,_)\n");
								//root->codeGen = 1;
							}
						}
						else if(root->id_type == Call)
						{
							Address returnVal;
							clearAddr(&returnVal);
							if(root->codeGen != 1)
							{
								//printf("root == Call\n");
								Address ad1,ad2,ad3;
								clearAddr(&ad1);
								clearAddr(&ad2);
								clearAddr(&ad3);
								OpKind operation;
								TreeNode* aux;
								char * entrada = "funcal";
								sprintf(ad1.contents.nome, "%s", root->attr.name);
								ad1.escopo = root->scope;
								ad1.kind = String;
								ad2.kind = Vazio;
								ad3.kind = Vazio;
								operation = BEGIN_ARGS;
								if(root->child[0]!=NULL)
								{
									fprintf(fp, "(begin_args,_,_,_)\n");//funcao com argumentos
									insereBloco(operation, ad2, ad2, ad3);
								}
								// if(root->child[0]!=NULL && root->child[0]->nodekind == ExpK)
								// {///indica que o argumento da funcao eh outra funcao.
								//precisa armazenar o temporario que vai servir de retorno para a avaliacao da funcaoArgumento
									// sprintf(tempVar, "_TEMP%d_", tempVarCounter);
									// tempVarCounter++;
								// }
								// printf("chegou aqui\n");
								genArguments(root->child[0]); //primeiro filho da funcao tem parametros, segundo tem codigo
								///pra gerar o codigo de return, eu preciso descobrir o que a funcao retorna. Como?
								///da pra percorrer a arvores e achar o no de retorno da funcao.
								operation = FUNCAL;
								insereBloco(operation, ad1, ad2, ad3);
								fprintf(fp, "(%s,%s,_,_)\n", entrada, root->attr.name);
								//printf("procurando funcao:%s\n", root->attr.name);
								int t = findFuncRetVal(root->attr.name);
								// printf("retorno FindFuncRetVal: %d\n", t);
								if(t)
								{
									//printf("Entrou aqui. If(t)\n");
									returnVal.kind = String;
									//sprintf(returnVal.contents.nome,"%s", FUNCTION_RETURN);
									sprintf(returnVal.contents.nome,"%s", "_RET_");
									returnVal.escopo = root->scope;
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
							clearAddr(&returnVal);
							if(root->codeGen != 1)
							{
								
								returnVal = processExp(root->child[0]);
								if(returnVal.kind == ConstInt){
									sprintf(str_array,"%s[%d]", root->attr.name, returnVal.contents.val);
									sprintf(returnVal.contents.nome,"%s", str_array);
									returnVal.escopo = root->scope;
									returnVal.kind = String;
								}
								else
								{
									sprintf(str_array,"%s[%s]", root->attr.name,returnVal.contents.nome);
									returnVal.escopo = root->scope;
									sprintf(returnVal.contents.nome,"%s", str_array);
									returnVal.kind = String;
								}
								//printf("retval: %s\n", returnVal.contents.nome);
								root->codeGen = 1;
								return returnVal;
							}
							returnVal.kind = Vazio;
							return returnVal;
						}else if(root->id_type == Var)
						{
							Address returnVal;
							clearAddr(&returnVal);
							if(root->codeGen != 1)
							{
								//printf("IdK (processExp): ");
								sprintf(returnVal.contents.nome,"%s", root->attr.name);
								returnVal.kind = String;
								//printf("%s\n", root->attr.name);
								root->codeGen = 1;
								return returnVal;
							}
							returnVal.kind = Vazio;
							return returnVal;
						}
						else
						{
							Address returnVal;
							clearAddr(&returnVal);
							if(root->codeGen != 1)
							{
								//printf("IdK (processExp): ");
								sprintf(returnVal.contents.nome,"%s", root->attr.name);
								returnVal.kind = String;
								//printf("%s\n", root->attr.name);
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
						printf("Erro nao conhecido\n");
						exit(1);
					}
				}
				break;
			}
			default: 
			{
				printf("Erro nao conhecido.\n");
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
				clearAddr(&tempEsq);
				clearAddr(&tempDir);
				Address ad3;
				clearAddr(&ad3);
				OpKind operation = INTCODE_ASSIGN;
				char charOp1[50], charOp2[50];
				///lado esquerdo so pode ser variavel ou veotr. Trivial.
				///lado direito pode ser expressao, variavel ou inteiro.
				///se chamar processExp deve funcionar de prima.
				///precisa armazenar o temporario que vai salvar a expressao do lado direito.
				///se o lado direito eh uma funcao, o temp do return vai virar um _RET_.
				if(root->child[0]->id_type == VectorPos) 
				{
					// printf("array\n");
					clearAddr(&tempEsq);
					tempEsq = processExp(root->child[0]);
					if(tempEsq.kind != Vazio)
					{
						if(tempEsq.kind == String)sprintf(tempEsq.contents.nome, "%s", tempEsq.contents.nome);
						if(tempEsq.kind == ConstInt)sprintf(tempEsq.contents.nome, "%d", tempEsq.contents.val);
						
						tempEsq.kind = String;
					}	
				}
				else
				{
					// printf("\n");
					clearAddr(&tempEsq);
					tempEsq = processExp(root->child[0]);
				}
				if(root->child[1]->id_type == VectorPos)
				{
					clearAddr(&tempDir);
					tempDir = processExp(root->child[1]);
					if(tempDir.kind != Vazio)
					{
						if(tempDir.kind == String)sprintf(tempDir.contents.nome, "%s", tempDir.contents.nome);
						if(tempDir.kind == ConstInt)sprintf(tempDir.contents.nome, "%d", tempDir.contents.val);
						tempDir.kind = String;
					}
					
				}
				else
				{
					// printf("\n");
					clearAddr(&tempDir);
					tempDir = processExp(root->child[1]);
				}
				if(FUNCTION_SEARCH)
				{
					//printf("retval: %s\n", FUNCTION_RETURN);
					sprintf(tempDir.contents.nome , "%s", FUNCTION_RETURN);
					tempDir.kind = String;
					// printf("retval : %s\n", tempDir.contents.nome);
					FUNCTION_SEARCH = 0;
				}
				if(tempEsq.kind == String && tempDir.kind == String)sprintf(toFile, "(%s,%s,%s,_)\n", "st", tempEsq.contents.nome, tempDir.contents.nome);
				if(tempEsq.kind == ConstInt && tempDir.kind == String)sprintf(toFile, "(%s,%d,%s,_)\n", "st", tempEsq.contents.val, tempDir.contents.nome);
				if(tempEsq.kind == String && tempDir.kind == ConstInt)sprintf(toFile, "(%s,%s,%d,_)\n", "st", tempEsq.contents.nome, tempDir.contents.val);
				if(tempEsq.kind == ConstInt && tempDir.kind == ConstInt)sprintf(toFile, "(%s,%d,%d,_)\n", "st", tempEsq.contents.val, tempDir.contents.val);
			
				if(root->child[1]->id_type == Call && root->child[1]->kind.exp ==  IdK)
				{
					//printf("******************* ACHO FUNCAO NO LADO DIREITO\n");
					clearAddr(&tempDir);
					sprintf(tempDir.contents.nome, "_RET_");
					tempDir.kind = String;
				}
				operation = INTCODE_ASSIGN;
				ad3.kind = Vazio;
				//printf("tempEsq.contents.nome:%s\n", tempEsq.contents.nome);
				//printf("tempDir.contents.nome:%s\n", tempDir.contents.nome);
				
				insereBloco(operation, tempEsq, tempDir, ad3);
				fprintf(fp, "%s", toFile);
				root->codeGen = 1;
				
			}
			break;
		}
		case IfK:
		{
			if(root->codeGen!=1){
				Address labelF, labelT, ifCond, ad2, ad3;
				clearAddr(&labelF);
				clearAddr(&labelT);
				clearAddr(&ifCond);
				clearAddr(&ad2);
				clearAddr(&ad3);
				OpKind ifFalse, jumpOp, label;
				ifFalse = COND_IF_F;
				jumpOp = JMP;
				label = LABEL;
				
				
				labelF.kind = Label;
				labelT.kind = Label;
				ad2.kind = Vazio;
				ad3.kind = Vazio;
				
				char labelTrue[10];
				char labelFalse[10];
				
				sprintf(labelFalse,"L%d", labelCounter);
				sprintf(labelF.contents.label,"L%d", labelCounter);
				//printf("labelF.contents.label: %s\n", labelF.contents.label);
				labelCounter++;
				sprintf(labelTrue,"L%d", labelCounter);
				sprintf(labelT.contents.label ,"L%d", labelCounter);
				labelCounter++;
				
				
				//Avalia Condicao
				ifCond = processExp(root->child[0]); ///pela definicao da gramatica so pode ter expressao na condicao do if.
				//if_false t1 goto l0
				fprintf(fp,"(if_false,%s,%s,_) -->jump condicional\n", ifCond.contents.nome, labelFalse); //
				insereBloco(ifFalse, ifCond, labelF, ad3);
				CodeGen(root->child[1]);//codigo para TRUE
				
				if(root->child[2]!=NULL)
				{
					insereBloco(jumpOp, labelT, ad2, ad3);
					fprintf(fp,"(%s,%s,_, _) -->jump para o fim\n", jump, labelTrue);//goto l1
					insereBloco(label, labelF, ad2, ad3);
					fprintf(fp,"(label,%s,_,_) -->label false\n", labelFalse);//label
					CodeGen(root->child[2]);
					insereBloco(label, labelT, ad2, ad3);
					fprintf(fp,"(label,%s,_,_) -->label do fim\n", labelTrue);
				}else
				{
					insereBloco(label, labelF, ad2, ad3);
					fprintf(fp,"(label,%s,_,_) -->label do fim\n", labelFalse);
				}
				root->codeGen= 1;
			}
			
			break;
		}
		case WhileK:
		{
			if(root->codeGen!=1){
				Address whileCond;
				Address nil, labelC, labelB;
				clearAddr(&labelC);
				clearAddr(&labelB);
				clearAddr(&nil);
				clearAddr(&whileCond);
				OpKind whileB, jumpOp, label;
				
				label = LABEL;
				whileB = LOOP_WHILE_F;
				jumpOp = JMP;
				
				labelC.kind = Label;
				labelB.kind = Label;
				
				nil.kind = Vazio;
				
				char labelContinue[10];
				char labelBreak[10];
				
				
				sprintf(labelContinue,"L%d", labelCounter);
				sprintf(labelC.contents.label,"L%d", labelCounter);
				labelCounter++;
				sprintf(labelBreak,"L%d", labelCounter);
				sprintf(labelB.contents.label,"L%d", labelCounter);
				labelCounter++;
				
				
				
				fprintf(fp,"(label,%s,_,_)\n", labelContinue);
				insereBloco(label, labelC, nil, nil);
				whileCond = processExp(root->child[0]);
				fprintf(fp,"(if_false,%s,%s,_)\n", whileCond.contents.nome, labelBreak);
				insereBloco(whileB, whileCond, labelB, nil);
				CodeGen(root->child[1]);
				fprintf(fp,"(%s,%s,_,_)\n", jump, labelContinue);
				insereBloco(jumpOp, labelC, nil, nil);
				fprintf(fp,"(label,%s,_,_)\n", labelBreak);
				insereBloco(label, labelB, nil, nil);
				root->codeGen= 1;
			}
			break;
		}
		case ReturnK:
		{
			if(root->codeGen!=1){
				if(root->child[0]!=NULL){
					Address retVal;
					clearAddr(&retVal);
					// if(root->child[0]->kind.exp == IdK && root->child[0]->id_type == Call)
					// {
						// printf("ENTROU AQUI\n");
						// OpKind opCode;
						// opCode = INTCODE_ASSIGN;
						// Address ad1, nil;
						// clearAddr(&nil);
						// clearAddr(&ad1);
						// nil.kind = Vazio;
						// sprintf(tempVar, "REC_REG");
						// sprintf(retVal.contents.nome, "%s", tempVar);
						// retVal.kind = String;
						// fprintf(fp,"(ld,%s,%s,_)\n", retVal.contents.nome, root->child[0]->attr.name);
						// ad1.kind = String;
						// sprintf(ad1.contents.nome, "%s", root->child[0]->attr.name);
						// insereBloco(opCode, retVal, ad1, nil);
					// }
					// else
					// if(root->child[0]->id_type == Var || root->child[0]->id_type == VectorPos || root->child[0]->id_type == NumK)
					// {//indica que no return tem uma variavel ou um vetor. Precisa armazenar num temp
						// OpKind opCode;
						// opCode = INTCODE_ASSIGN;
						// Address ad1, nil;
						// clearAddr(&nil);
						// clearAddr(&ad1);
						// nil.kind = Vazio;
						// sprintf(tempVar, "_TEMP%d_", tempVarCounter);
						// tempVarCounter++;
						// sprintf(retVal.contents.nome, "%s", tempVar);
						// retVal.kind = String;
						// fprintf(fp,"(ld,%s,%s,_)\n", retVal.contents.nome, root->child[0]->attr.name);
						// ad1.kind = String;
						// if(root->child[0]->id_type != NumK)sprintf(ad1.contents.nome, "%s", root->child[0]->attr.name);
						// else sprintf(ad1.contents.nome, "%d", root->child[0]->attr.val);
						// insereBloco(opCode, retVal, ad1, nil);
					// }	
					// else 
					{
						clearAddr(&retVal);
						retVal = processExp(root->child[0]);
					}
					if(retVal.contents.nome == NULL)
					{
						OpKind opCode = INTCODE_RET;
						Address nil;
						clearAddr(&nil);
						nil.kind = Vazio;
						fprintf(fp,"(ret,_,_,_)\n");
						insereBloco(opCode, nil, nil, nil);
					}
					else 
					{
						OpKind opCode = INTCODE_RET;
						Address nil;
						clearAddr(&nil);
						nil.kind = Vazio;
						if(retVal.kind == String)fprintf(fp,"(ret,%s,_,_)\n", retVal.contents.nome);
						if(retVal.kind == ConstInt)fprintf(fp,"(ret,%d,_,_)\n", retVal.contents.val);
						insereBloco(opCode, retVal, nil, nil);
					}
					root->codeGen= 1;
				} else 
				{
					OpKind opCode = INTCODE_RET;
					Address nil;
					clearAddr(&nil);
					nil.kind = Vazio;
					fprintf(fp,"(ret,_,_,_)\n");
					insereBloco(opCode, nil, nil, nil);
					root->codeGen= 1;
				}
				break;
			}
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
				printf("Erro nao conhecido.\n");
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

void CodeGenNotRecursive(TreeNode* root)
{
	printf("Gerando Codigo Intermediario ...\n");
	CodeGen(root);
	fprintf(fp,"(halt,_,_,_)\n");
	printf("Codigo Intermediario Gerado com Sucesso\n");
}




/*
retorna o numero de linhas de um arquivo.
o ponteiro ARQUIVO precisa estar aberto, senao retorna -1
*/

int numberOfLinesInFile(FILE* ARQUIVO)
{
	fseek(ARQUIVO, 0, SEEK_SET);
	int fgetcRetVal = 1;
	int numLines = 0;
	if(ARQUIVO != NULL)
	{
		while(fgetcRetVal>0)
		{
			fgetcRetVal = fgetc(ARQUIVO);
			if(fgetcRetVal == '\n')numLines++;
			//printf("numLines: %d\n", numLines);
		}	
	}
	return numLines;
}



/*

Gera numeracao das instrucoes da memoria de instrucoes
necessário para poder fazer o jump entre as funcoes.

*/
void instMemGen()
{
	///precisa substituir nome de variaveis por enderecos de memoria. Procurar na tabela.
	///Sempre que houver ld procura o primeiro e o segundo argumento na tabela, 
	///substitui ambos por endereco de memoria
	///pra isso, carrega todo o arquivo de codigo intermediario na memoria pra ficar facil de manipular.
	///Nao espera-se um arquivo com mais de 1Gb.
	printf("Gerando a Memoria de Instrucoes");
	int memPos = 0;
	int numLines = 0;
	int codeSize;
	int fgetcRetVal = 1;
	char stream[50];
	char *res;
	char *var;
	int pos;
	char funMain[] = "main";
	char ch;
	
	
	numLines = numberOfLinesInFile(fp);	
	char INSTR_FILE[numLines][50];
	char AUXILIAR[numLines][50];
	
	numLines = 0;
	fseek(fp, 0, SEEK_SET); //retorna o FILE* para o comeco do arquivo
	do
	{
		fgets (INSTR_FILE[numLines++], sizeof(stream), fp);
	}while(feof(fp)==0);
	
	///a partir daqui, ARQUIVO contem todas as instrucoes do programa.
	//printf de debug;
	//for(int l=0; l<numLines-1;l++) printf("INSTR_FILE 1: linha %-2d: %s", l, &INSTR_FILE[l]);
		
	///precisa achar o (fundef,main,_,_) no arquivo e jogar ele na primeira posicao.
	fseek(fp, 0, SEEK_SET);
	int k = 0;
	int i = 0;
	for(i; i<numLines-1; i++)
	{
		res = strstr(INSTR_FILE[i], funMain);
		if(res!=NULL)
		{
			strcpy(AUXILIAR[k], INSTR_FILE[i]);k++;i++;
			while(strstr(INSTR_FILE[i], "halt") == NULL)
			{
				strcpy(AUXILIAR[k], INSTR_FILE[i]);k++;i++;
			}
		}
	}
	k++;///precisa disso para acertar a linha de inicio do AUXILIAR;
	///main ja esta no inicio do arquivo.
	///agora comeca de onde parou (k) e continua copiando o conteudo de INSTR_FILE em AUXILIAR
	for(i = 0; k<numLines; i++)
	{
		strcpy(AUXILIAR[k++], INSTR_FILE[i]);
	}
	for (i = 0; i<numLines; i++)
	{
		strcpy(INSTR_FILE[i], AUXILIAR[i]);
	}
	///INSTR_FILE contem as instrucoes do programa na ordem correta.
	if(InstMemGenDebug)printf("INSTR_FILE contem todas as instrucoes.\n");
	codeSize = numLines;
	
	///Precisa ler linha por linha do arquivo.
	///sempre que achar uma variavel, procura na tabela de simbolos usando o nome
	
	
	
	
	
}

void generateIntermCode()
{
	CodeGenNotRecursive(savedTree);
	imprimeIntermedCode();
	instMemGen();
}

/************************************************************************/
/************************************************************************/
/************************************************************************/
/************************************************************************/
/************************************************************************/
/****************** Gerador de Codigo de Máquina *********************/
/************************************************************************/
/************************************************************************/
/************************************************************************/
/************************************************************************/
#define MAX_INSTRUCTIONS 27

/*Estrutura de Lista do Assembly*/
int contador = 0;//numero da linha


typedef enum {I_NOP, I_JMP, I_JPE, I_JMPNE, I_JPL, I_JPLE, I_JPG, I_JPGE, I_SRVALUE, I_LOAD, I_STORE, I_REGCOPY, I_OR, I_AND, I_NOR, I_NAND, I_XOR, I_ADD, I_SUB, I_MUL, I_DIV, I_SHR, I_SHL, I_PUSH_R, I_POP_R, I_PUSH_PC, I_POP_PC,I_LABEL} Instruction_Assembly;

typedef enum {REG, NUM, MEM, LAB,NADA} Op_Type; //diz qual o tipo de dado que esta no no da lista. Serve para alocar a quantidade correta de bits para o dado.

typedef struct 
{
	Op_Type type;
	int size_bits;
	int value;
}Operand;

typedef struct assembly_lista
{
	Instruction_Assembly opcode;
	Operand op1, op2, op3;
	int line;
	assembly_lista* next,* prev;
}Assembly;

int flag_first_instruction = 1;

Assembly* Codigo_Maquina = (Assembly*)malloc(sizeof(Assembly));


Operand * AlocaOperand(Op_Type type, int size_bits, int value){
	Operand* aux = (Operand*) malloc(sizeof(Operand));
	aux->type = type;
	aux->size_bits = size_bits;
	aux->value = value;
	return aux;
}

Assembly * AlocaAssembly(Instruction_Assembly opcode, Operand* val1, Operand* val2, Operand* val3)
{
	Assembly* aux = (Assembly*) malloc(sizeof(Assembly));
	aux->opcode = opcode;
	aux->op1.type = NADA;
	aux->op2.type = NADA;
	aux->op3.type = NADA;
	if (val1 != NULL) aux->op1 = (*val1);
	if (val2 != NULL) aux->op2 = (*val2);
	if (val3 != NULL) aux->op3 = (*val3);
	aux->line = contador;
	aux->next = NULL;
	aux->prev = NULL;
	return aux;
}

void InsereAssembly(Instruction_Assembly opcode, Operand* val1, Operand* val2, Operand* val3)
{
	Assembly* aux = AlocaAssembly(opcode,val1,val2,val3);
	Assembly * p;
	p = Codigo_Maquina;
	if(p == NULL){
		p = aux;
		aux->prev = NULL;
		
	}else{
		// if (flag_first_instruction == 1){
			// flag_first_instruction = 0;
			// p = aux;
		// }else{
			while(p->next!= NULL){
				p = p->next;
			}
		p->next = aux;
		aux->prev = p;
		// }
	}
	
	if(opcode != I_LABEL) contador++;
}

int RemoveAssembly(Instruction_Assembly opcode, Operand val1, Operand val2, Operand val3)
{
	Assembly * p;
	Assembly * q = NULL;
	p = Codigo_Maquina;
	int flag_stop = 0;
	int line;
	while(p != NULL){
		if(p->opcode == opcode){
			if(p->op1.type == val1.type){
				if(p->op1.value == val1.value){
					line = p->next->line;
					q = p->prev;
					q->next = p->next;
					p->next->prev = q;
					free(p);
					flag_stop = 1;
					return line;
				}
			}
		}
		p = p->next;
	}
}


/*Pilha de Registradores Livres*/
typedef struct stack
{
	int reg;
	stack * next;
}Stack;

Stack* Free_Reg = NULL;

Stack * AlocaStack(int reg)//aloca o nó da pilha
{
	Stack* aux = (Stack*) malloc(sizeof(Stack));
	aux->reg = reg;
	aux->next = NULL;
	return aux;
}

void Push_Stack(int reg)//empilha
{
	Stack* aux = AlocaStack(reg);
	Stack * p;
	p = Free_Reg;
	if(p == NULL){
		p = aux;
	}else{
		while(p->next!= NULL){
			p = p->next;
		}
		p->next = aux;
	}
}

int Verifica_Stack()//verifica se está vazia
{
	Stack * p;
	p = Free_Reg;
	if(p == NULL){
		return 55; //valor arbitrario maior que 39(numero maximo de registradores) que indica que a pilha ta vazia.
	}
}

int Pop_Stack()//desempilha
{
	int temp;
	Stack * p;
	p = Free_Reg;
	if(p == NULL){
		return 55; //valor arbitrario maior que 39(numero maximo de registradores) que indica que a pilha ta vazia.
	}else{
		while(p->next!= NULL){
			p = p->next;
		}
		temp = p->reg;
		p = NULL;
		return temp;
	}
}

void Clear_Stack()//limpa a pilha
{
	Free_Reg = NULL;
}

/*Tabela de Registradores*/
typedef struct t_tabela_registradores
{
	int var;
	int flag_utilizado;
}Registradores;

Registradores tabela_registradores[40];
int register_cont = 8;

void Clean_Reg_Table_GP(){
	register_cont = 8;
	for(int i = 8; i<40;i++){
		tabela_registradores[i].var = 0;
		tabela_registradores[i].flag_utilizado = 0;
	}
	Clear_Stack();
}

void Clean_Reg_Table_RE(){
	for(int i = 0; i<8;i++){
		tabela_registradores[i].var = 0;
		tabela_registradores[i].flag_utilizado = 0;
	}
}

void Clean_Reg_Table(){
	register_cont = 8;
	for(int i = 0; i<40;i++){
		tabela_registradores[i].var = 0;
		tabela_registradores[i].flag_utilizado = 0;
	}
	Clear_Stack();
}

void Ini_Reg_Table(){
	Clean_Reg_Table_GP();
}


/*Tabela de Memoria*/

typedef struct t_tabela_memoria
{
	char* var;
	int occurs;
	int reg;
	int size;
	int first_line;
}Memoria;

int max_array_size = 1;
int escopo_contador;
int global_contador;
int variavel_contador;
int reserved_mem_total;
int reserved_mem_global;

int contador_parametros_decl;//Usado para Constroi_Tabela_Scope


Memoria* tabela_memoria_escopo = NULL;
Memoria* tabela_memoria = NULL;
Memoria* tabela_memoria_global = NULL;


void Insere_Mem_Table(Memoria temp){
	variavel_contador++;
	tabela_memoria = (Memoria*)realloc(tabela_memoria, variavel_contador*sizeof(Memoria));
	tabela_memoria[variavel_contador-1] = temp;
}

void Ini_Mem_Table(){
	variavel_contador = 0;
	tabela_memoria = (Memoria*)realloc(tabela_memoria, variavel_contador*sizeof(Memoria));
	tabela_memoria = NULL;
}

void Clean_Mem_Table(){
	variavel_contador = 0;
	tabela_memoria = (Memoria*)realloc(tabela_memoria, variavel_contador*sizeof(Memoria));
	tabela_memoria = NULL;
}

void Insere_Mem_Table_Scope(char* var,int occurs, int reg, int size,int first_line){
	escopo_contador++;
	tabela_memoria_escopo = (Memoria*)realloc(tabela_memoria_escopo, escopo_contador*sizeof(Memoria));
	tabela_memoria_escopo[escopo_contador-1].var = var;
	tabela_memoria_escopo[escopo_contador-1].occurs = occurs;
	tabela_memoria_escopo[escopo_contador-1].reg = reg;
	tabela_memoria_escopo[escopo_contador-1].size = size;
	tabela_memoria_escopo[escopo_contador-1].first_line = first_line;
}

void Ini_Mem_Table_Scope(){
	escopo_contador = 0;
	tabela_memoria_escopo = (Memoria*)realloc(tabela_memoria_escopo, escopo_contador*sizeof(Memoria));
	tabela_memoria_escopo = NULL;
}

void Clean_Mem_Table_Scope(){
	escopo_contador = 0;
	tabela_memoria_escopo = (Memoria*)realloc(tabela_memoria_escopo, escopo_contador*sizeof(Memoria));
	tabela_memoria_escopo = NULL;
}

void Sort_Mem_Table_Scope(){
	Memoria aux;
	for(int i = contador_parametros_decl+1;i<escopo_contador;i++){
		aux = tabela_memoria_escopo[i];
		int flag_sort_j = 0;
		int j = i-1;
		while(flag_sort_j == 0){
			if (j>=contador_parametros_decl){
				if(aux.first_line < tabela_memoria_escopo[j].first_line){
					tabela_memoria_escopo[j+1] = tabela_memoria_escopo[j];
					j--;
				}else{
					flag_sort_j = 1;
				}
			}else{
				flag_sort_j = 1;
			}
		}
		tabela_memoria_escopo[j+1] = aux;
	}
}

void Insere_Mem_Table_Global(char* var,int occurs, int reg, int size,int first_line){
	global_contador++;
	tabela_memoria_global = (Memoria*)realloc(tabela_memoria_global, global_contador*sizeof(Memoria));
	tabela_memoria_global[global_contador-1].var = var;
	tabela_memoria_global[global_contador-1].occurs = occurs;
	tabela_memoria_global[global_contador-1].reg = reg;
	tabela_memoria_global[global_contador-1].size = size;
	tabela_memoria_global[global_contador-1].first_line = first_line;
}

void Ini_Mem_Table_Global(){
	global_contador = 0;
	tabela_memoria_global = (Memoria*)realloc(tabela_memoria_global, global_contador*sizeof(Memoria));
	tabela_memoria_global = NULL;
}

void Clean_Mem_Table_Global(){
	global_contador = 0;
	tabela_memoria_global = (Memoria*)realloc(tabela_memoria_global, global_contador*sizeof(Memoria));
	tabela_memoria_global = NULL;
}

void Sort_Mem_Table_Global(){
	Memoria aux;
	for(int i = 1;i<global_contador;i++){
		aux = tabela_memoria_global[i];
		int flag_sort_j = 0;
		int j = i-1;
		while(flag_sort_j == 0){
			if (j>=0){
				if(aux.first_line < tabela_memoria_global[j].first_line){
					tabela_memoria_global[j+1] = tabela_memoria_global[j];
					j--;
				}else{
					flag_sort_j = 1;
				}
			}else{
				flag_sort_j = 1;
			}
		}
		tabela_memoria_global[j+1] = aux;
	}
}

void Get_Maximum_Array_Size(){
	max_array_size = 1;
	for(int i = 0;i<211;i++){
		if(&HashVec[i] != NULL) {
			Symbol *table = HashVec[i].begin;
			while(table!=NULL){
				if (table->id_type == VectorDecl){
					if (table->size > max_array_size){
						max_array_size = table->size;
					}
				}
				table = table->nxt;
			}
		}
	}
}

void getReservedMemory_Global(){
	int soma = 0;
	for(int i = 0;i<global_contador;i++){
		soma = soma + tabela_memoria_global[i].size;
	}
	reserved_mem_global = soma;
}

void Constroi_Tabela_Global(){
	Ini_Mem_Table_Global();
	for(int i = 0;i<211;i++){
		if(&HashVec[i] != NULL) {
			Symbol *table = HashVec[i].begin;
			while(table!=NULL){
				if (strcmp(table->scope,"Global") == 0){
					if ((table->id_type == VarDecl) || (table->id_type == VectorDecl)){
						Insere_Mem_Table_Global(table->ID, table->top, 0, table->size, table->lines[0]);
					}
				}
				table = table->nxt;
			}
		}
	}
	Sort_Mem_Table_Global();
	Get_Maximum_Array_Size();
	getReservedMemory_Global();
}

void Constroi_Tabela_Scope(char* scope){
	Ini_Mem_Table_Scope();
	int flag_out_busca = 0;
	int flag_achou = 0;
	contador_parametros_decl = 0;
	for(int i = 0;i<211;i++){
		if(&HashVec[i] != NULL) {
			Symbol *table = HashVec[i].begin;
			while(table!=NULL){
				if (strcmp(table->scope,scope) == 0){
					if ((table->id_type == FuncAttrVar) || (table->id_type == FuncAttrVector)){
						flag_achou = 1;
						break;
					}
				}
				table = table->nxt;
			}
		}
	}
	if(flag_achou){
		TreeNode* declaracao_func = return_Func_Decl_scope(savedTree,scope);
		while(declaracao_func!=NULL){
			for(int i = 0;i<211;i++){
				if(&HashVec[i] != NULL) {
					Symbol *table = HashVec[i].begin;
					while(table!=NULL){
						if (strcmp(table->scope,scope) == 0){
							if ((table->id_type == FuncAttrVar) || (table->id_type == FuncAttrVector)){
								if(strcmp(table->ID,declaracao_func->child[0]->attr.name)==0){
									if(table->id_type == FuncAttrVector){
										Insere_Mem_Table_Scope(table->ID, table->top, 0, max_array_size, table->lines[0]);
										contador_parametros_decl++;
									}else{
										Insere_Mem_Table_Scope(table->ID, table->top, 0, table->size, table->lines[0]);
										contador_parametros_decl++;
									}					
								}
							}
						}
						table = table->nxt;
					}
				}
			}
			declaracao_func = declaracao_func->sibling;
		}
	}
	for(int i = 0;i<211;i++){
		if(&HashVec[i] != NULL) {
			Symbol *table = HashVec[i].begin;
			while(table!=NULL){
				if (strcmp(table->scope,scope) == 0){
					if ((table->id_type == VarDecl) || (table->id_type == VectorDecl)){
						Insere_Mem_Table_Scope(table->ID, table->top, 0, table->size, table->lines[0]);
					}
				}
				table = table->nxt;
			}
		}
	}
	Sort_Mem_Table_Scope();
}

int return_occurs(char* var, char* scope){
	for(int i = 0;i<211;i++){
		if(&HashVec[i] != NULL) {
			Symbol *table = HashVec[i].begin;
			while(table!=NULL){
				if (strcmp(table->scope,scope) == 0){
					if ((table->id_type == Var)||(table->id_type == VectorPos)){
						if(strcmp(table->ID,var)==0){
							return table->top;
						}
					}
				}
				table = table->nxt;
			}
		}
	}
	return 0;
}

void update_occurs_Mem_Table(char* scope){
	for(int i = 0;i<variavel_contador;i++){
		tabela_memoria[i].occurs = return_occurs(tabela_memoria[i].var,scope);
	}
}

void getReservedMemory_Mem_Table(){
	int soma = 0;
	for(int i = 0;i<variavel_contador;i++){
		soma = soma + tabela_memoria[i].size;
	}
	reserved_mem_total = soma;
}

void Create_Mem_Table(char* scope){
	Constroi_Tabela_Scope(scope);
	Ini_Mem_Table();
	for(int i = 0;i<global_contador;i++){
		Insere_Mem_Table(tabela_memoria_global[i]);
	}
	for(int i = 0;i<escopo_contador;i++){
		Insere_Mem_Table(tabela_memoria_escopo[i]);
	}
	update_occurs_Mem_Table(scope);
	getReservedMemory_Mem_Table();
}

//pega valor de memoria relativo para a "posição de memória" localizada no registrador.

int SearchTemp(int temp){
	if(tabela_registradores[4].var == temp){
		return 4;
	}else{
		if(tabela_registradores[5].var == temp){
			return 5;
		}
	}
}

int returnFree_Temp(){
	if(tabela_registradores[4].flag_utilizado == 0){
		return 4;
	}else{
		if(tabela_registradores[5].flag_utilizado == 0){
			return 5;
		}
	}
}

int Get_Mem_Adress_REG(int pos_table){
	int soma = 0;
	if (pos_table == 0){
		return 0;
	}else{
		for(int i = 0;i<pos_table;i++){
			soma = soma + tabela_memoria[i].size;
		}
		return soma;
	}
}

int Get_Mem_Adress_REG_Param(int* tabela_memoria_parametro,int pos_table){
	int soma = 0;
	if (pos_table == 0){
		return 0;
	}else{
		for(int i = 0;i<pos_table;i++){
			soma = soma + tabela_memoria_parametro[i];
		}
		return soma;
	}
}

int Get_Mem_Adress(char* var){
	int j = 0;
	while(strcmp(tabela_memoria[j].var, var)!=0){
		j++;
	}
	int soma = 0;
	if (j == 0){
		return 0;
	}else{
		for(int i = 0;i<j;i++){
			soma = soma + tabela_memoria[i].size;
		}
		return soma;
	}
}

int returnPosition(char* var){
	int position_mem = 0;
	while(strcmp(tabela_memoria[position_mem].var, var)!=0){
		position_mem++;
	}
	return position_mem;
}

void Remove_Reg_Table(int reg){
	tabela_registradores[reg].flag_utilizado = 0;
	tabela_registradores[reg].var = 0;
	if(reg>7){
		if(reg != register_cont){
			Push_Stack(reg);
		}
	}
}

void load_reg_to_mem(int reg){ 
	int mem_addr;
	if (tabela_registradores[reg].flag_utilizado == 1){//registrador está sendo usado de fato;
		mem_addr = Get_Mem_Adress_REG(tabela_registradores[reg].var);
		Operand * Op1 = AlocaOperand(REG,8, reg);
		Operand * Op2 = AlocaOperand(MEM,16, mem_addr);
		Operand * Op3 = NULL;
		InsereAssembly(I_STORE,Op1,Op2,Op3);//STORE $reg mem_addr
		printf("STORE $%d %d \n", reg, mem_addr);
		tabela_memoria[tabela_registradores[reg].var].reg = 0;
		Remove_Reg_Table(reg);
	}
}

void load_reg_to_mem_addr(int reg,int adress){ 
	if (tabela_registradores[reg].flag_utilizado == 1){//registrador está sendo usado de fato;
		Operand * Op1 = AlocaOperand(REG,8, reg);
		Operand * Op2 = AlocaOperand(MEM,16, adress);
		Operand * Op3 = NULL;
		InsereAssembly(I_STORE,Op1,Op2,Op3);
		printf("STORE $%d %d\n", reg, adress);
		Remove_Reg_Table(reg);
	}
}

int Insere_Reg_Table(int mem_addr){//retorna o registrador que inseriu
	int free_reg;
	if(Verifica_Stack()==55){
		load_reg_to_mem(register_cont);
		tabela_registradores[register_cont].var = mem_addr;
		tabela_registradores[register_cont].flag_utilizado = 1;
		if (register_cont == 39){
			register_cont = 8;
			return 39;
		}else{
			register_cont++;
			return register_cont-1;
		}
	}else{
		free_reg = Pop_Stack();
		tabela_registradores[free_reg].var = mem_addr;
		tabela_registradores[free_reg].flag_utilizado = 1;
		return free_reg;
	}
}

int Insere_Reg_Table_initial(int mem_addr){//retorna o registrador que inseriu
	int free_reg;
	tabela_registradores[register_cont].var = mem_addr;
	tabela_registradores[register_cont].flag_utilizado = 1;
	if (register_cont == 39){
		register_cont = 8;
		return 39;
	}else{
		register_cont++;
		return register_cont-1;
	}

}

void load_mem_to_reg(char* var){ //retorna o registrador, e 0 se ja estiver
	int reg;
	int mem_addr;
	int position_mem = returnPosition(var);
	if(tabela_memoria[position_mem].reg == 0){//não está na matriz de registradores
		reg = Insere_Reg_Table(position_mem);
		mem_addr = Get_Mem_Adress(var);
		Operand * Op2 = AlocaOperand(REG,8, reg);
		Operand * Op1 = AlocaOperand(MEM,16, mem_addr);
		Operand * Op3 = NULL;
		InsereAssembly(I_LOAD,Op1,Op2,Op3);
		printf("LOAD %d $%d\n",mem_addr, reg);
		tabela_memoria[position_mem].reg = reg;
	}	
	if(tabela_memoria[position_mem].occurs > 0) tabela_memoria[position_mem].occurs--;
}

void load_mem_to_reg_withoutoccur(char* var){ //retorna o registrador, e 0 se ja estiver
	int reg;
	int mem_addr;
	int position_mem = returnPosition(var);
	if(tabela_memoria[position_mem].reg == 0){//não está na matriz de registradores
		reg = Insere_Reg_Table(position_mem);
		mem_addr = Get_Mem_Adress(var);
		Operand * Op2 = AlocaOperand(REG,8, reg);
		Operand * Op1 = AlocaOperand(MEM,16, mem_addr);
		Operand * Op3 = NULL;
		InsereAssembly(I_LOAD,Op1,Op2,Op3);
		printf("LOAD %d $%d\n", mem_addr, reg);
		tabela_memoria[position_mem].reg = reg;
	}	
}

void load_mem_to_reg_RE(int mem_addr, int reg){ //retorna o registrador, e 0 se ja estiver
	if(tabela_registradores[reg].flag_utilizado == 0){
		Operand * Op2 = AlocaOperand(REG,8, reg);
		Operand * Op1 = AlocaOperand(MEM,16, mem_addr);
		Operand * Op3 = NULL;
		InsereAssembly(I_LOAD,Op1,Op2,Op3);
		printf("LOAD %d $%d\n",mem_addr,reg);
		tabela_registradores[reg].flag_utilizado = 1;
	}
}

void initial_load_to_reg(){//TAD
	Ini_Reg_Table();
	int reg;
	int flag_out = 0;
	int i = 0;
	while(flag_out == 0){
		if (register_cont<=39){
			if(i<variavel_contador){
				if (tabela_memoria[i].occurs > 0){
					if(tabela_memoria[i].size == 1){
						reg = Insere_Reg_Table_initial(i);
						tabela_memoria[i].reg = reg;
					}
				}
				i++;
			}else{
				flag_out = 1;
			}
		}else{
			flag_out = 1;
		}
	}
}


void Store_ALL_Reg_Table(){//TAD
	for (int i = 8;i<40;i++){
		load_reg_to_mem(i);
	}
	Ini_Reg_Table();
}

void Load_ALL_Mem_Table(){//TAD
	Ini_Reg_Table();
	int reg;
	int flag_out = 0;
	int i = 0;
	while(flag_out == 0){
		if (register_cont<=39){
			if(i<variavel_contador){
				if (tabela_memoria[i].occurs > 0){
					if (tabela_memoria[i].size == 1){
						load_mem_to_reg_withoutoccur(tabela_memoria[i].var);
					}
				}
				i++;
			}else{
				flag_out = 1;
			}
		}else{
			flag_out = 1;
		}
	}

}

/**
 * FUNCAO CARACTERIZA SE O ARGUMENTO DO VETOR EH OUTRO VETOR
 * @param k 
 * @return 1 se for vetor, 0 se nao for
 */
int verificaVetor(char* k)
{
    char* aux;
    char copia[sizeof(k)];
    int flag_vetor = 0;
    aux = strtok(copia, "[]");
    while(aux!=NULL)
    {
        aux = strtok(NULL, "[]");
        flag_vetor++;
        // printf("flag_vetor: %d\n", flag_vetor);
    }
    // printf("flag_vetor (saiu): %d\n", flag_vetor);
    if(flag_vetor <=2)return 0;
    else return 1;
}

typedef enum{VARIAVEL, TEMPORARIO, IMEDIATO, VETOR, REG_RECT, L_LABEL}tipo_operando;//registrador nesse caso é temporario
typedef enum{D_VARIAVEL, D_TEMPORARIO, D_IMEDIATO, D_REG_RECT, NULO}tipo_deslocamento;

typedef struct t_compoente
{
	tipo_operando type;
	tipo_deslocamento type_d;
	int value;//valor caso seja TEMPORARIO(_TEMP_X_) sendo X o valor,caso seja IMEDIATO
	int deslocamento;//valor caso deslocamento seja D_TEMPORARIO ou  D_IMEDIATO.
	char* var;//valor caso seja VARIAVEL ou VETOR
	char* desl;//valor caso deslocamento seja D_VARIAVEL.
}Componente;

Componente* c = (Componente*) malloc(sizeof(Componente));

void AlocaComponente(tipo_operando type, tipo_deslocamento type_d, int value, int deslocamento, char* var, char* desl){
	//Componente* aux = (Componente*) malloc(sizeof(Componente));
	c->type = type;
	c->type_d = type_d;
	c->value = value;
	c->deslocamento = deslocamento;
	c->var = var;
	c->desl = desl;
	
	// printf("type: %d - %d\n", c->type, type);
	// printf("type_d: %d - %d\n", c->type_d, type_d);
	// printf("value: %d - %d\n", c->value, value);
	// printf("desloc: %d - %d\n", c->deslocamento, deslocamento);
	// printf("var: %s - %s\n", c->var, var);
	// printf("desl: %s - %s\n", c->desl, desl);
}

Quad_List* return_func_def(char* name)//retorna o ponteiro de QuadList quando achar um func_def com o nome "name", se não existir retorna NULL
{
	Quad_List* aux = codigo_inter;
	while(aux!=NULL)
	{
		if(aux->quad.op == FUNDEF)
		{
			if(strcmp(aux->quad.addr_01.contents.nome,name) == 0) return aux;
		}
		aux = aux->next;
	}
	return NULL;
	
}
//Processa o Addr numero "numero_endereco", retornando um ponteiro de componente, 
//com os campos especificados acima, Por exemplo, returnComponente(q, 1), ira processar o Addr1 do "q".
void returnComponente(Quad_Cell q, int numero_endereco)
{
	int valor, auxiliarInt;
	char* auxiliar;
	char* nomeVar;
	//sprintf(numEnderec,"%d", numero_endereco);
	switch(numero_endereco)
	{
		case 1:
		{
			if(q.addr_01.kind == String) //pode ser vetor, variavel, temp, ret
			{	
				if(strstr(q.addr_01.contents.nome,"TEMP")) //q.addr_01 --> temporario
				{
					
					int valor;
					char copia[sizeof(q.addr_01.contents.nome)];
					strcpy(copia, q.addr_01.contents.nome);
					auxiliar = strtok(copia, "_TEMP"); //auxiliar contem o valor do indice do temporario.
					auxiliarInt = atoi(auxiliar);
					AlocaComponente(TEMPORARIO, NULO, auxiliarInt, -1, NULL, NULL);
				}
				else if(strstr(q.addr_01.contents.nome, "[")) //eh um vetor por que tem o caracter "[" no nome
				{
					char copia[sizeof(q.addr_01.contents.nome)];
					strcpy(copia, q.addr_01.contents.nome);
					auxiliar = strtok(copia, "["); //auxiliar contem o nome do vetor.
					nomeVar = (char*)malloc(sizeof(auxiliar)*sizeof(char));
					strcpy(nomeVar, auxiliar); //copia o auxiliar pro nomeVar.
					
					auxiliar = strtok(NULL, "]");//auxiliar contem o valor da posicao do vetor. Verificar se eh String ou Integer.
					if(isdigit ((unsigned char)*auxiliar)) //conversao necessaria pela implementacao da funcao isdigit()
					{
						//auxiliar contem um imediato. caso trivial.
						auxiliarInt = atoi(auxiliar); //auxiliar contem o deslocamento.
						AlocaComponente(VETOR, D_IMEDIATO, -1, auxiliarInt, nomeVar, NULL); //colocar o nome do vetor
					}
					else 
					{
						//auxiliar contem algo que nao eh digito. precisa ver se eh temp, var, ou vetor(*******TO DO********)
						strcpy(copia, q.addr_01.contents.nome);
						if(strstr(copia, "_TEMP_")) //argumento eh um temp. Separar indice
						{
							auxiliar = strtok(copia, "[");
							auxiliar = strtok(NULL, "]");
							auxiliar = strtok(auxiliar, "_TEMP");
							auxiliarInt = atoi(auxiliar); //auxiliar ja contem o indice. eh o deslocamento do vetor.
							 AlocaComponente(VETOR, D_TEMPORARIO, -1, auxiliarInt, nomeVar, NULL);
						} else if(strstr(copia, "_RET_"))
						{
							auxiliar = strtok(copia, "[");
							auxiliar = strtok(NULL, "]"); //auxiliar contem RET
							 AlocaComponente(VETOR, D_REG_RECT, -1, -1, nomeVar, NULL);
						} else if(verificaVetor(copia) == 0) //nao eh vetor. eh var
						{
							auxiliar = strtok(copia, "[");
							auxiliar = strtok(NULL, "]");
							AlocaComponente(VETOR, D_VARIAVEL, -1, -1, nomeVar, auxiliar);
						} else
						{//eh vetor. precisa implementar
							
						}
					}
				}
				else if(strstr(q.addr_01.contents.nome, "RET"))
				{
					char copia[sizeof(q.addr_01.contents.nome)];
					strcpy(copia, q.addr_01.contents.nome);
					auxiliar = strtok(copia, "[");
					auxiliar = strtok(NULL, "]"); //auxiliar contem RET
					AlocaComponente(REG_RECT, NULO, -1, -1, NULL, NULL);
				}else//q.addr_01 --> variavel
				{
					//trivial
					AlocaComponente(VARIAVEL, NULO, -1, -1, q.addr_01.contents.nome, NULL);
				}
			}
			else if(q.addr_01.kind == Integer) //com certeza eh imediato
			{
				AlocaComponente(IMEDIATO, NULO, q.addr_01.contents.val, -1, NULL, NULL);
			}
			else if(q.addr_01.kind == Label)
			{
				//famosa gambiarra
				int i = 1;
				char copia[sizeof(q.addr_01.contents.label)-1];
				for(i; i<sizeof(copia)+1; i++)
				{
					copia[i-1] = q.addr_01.contents.label[i];
				}
				copia[sizeof(copia)] = '\0';
				int kkk_eae_men = atoi(copia);
				AlocaComponente(L_LABEL, NULO, kkk_eae_men, -1, NULL, NULL);
			}
			break;
		}
		case 2:
		{
			if(q.addr_02.kind == String) //pode ser vetor, variavel, temp, ret
			{	
				if(strstr(q.addr_02.contents.nome,"TEMP")) //q.addr_02 --> temporario
				{
					int valor;
					char copia[sizeof(q.addr_02.contents.nome)];
					strcpy(copia, q.addr_02.contents.nome);;
					auxiliar = strtok(copia, "_TEMP"); //auxiliar contem o valor do indice do temporario.
					auxiliarInt = atoi(auxiliar);

					 AlocaComponente(TEMPORARIO, NULO, auxiliarInt, -1, NULL, NULL);
				}
				else if(strstr(q.addr_02.contents.nome, "[")) //eh um vetor por que tem o caracter "[" no nome
				{
					char copia[sizeof(q.addr_02.contents.nome)];
					strcpy(copia, q.addr_02.contents.nome);
					auxiliar = strtok(copia, "["); //auxiliar contem o nome do vetor.
					nomeVar = (char*)malloc(sizeof(char*)*sizeof(auxiliar));
					strcpy(nomeVar, auxiliar); //copia o auxiliar pro nomeVar.
					
					
					auxiliar = strtok(NULL, "]");//auxiliar contem o valor da posicao do vetor. Verificar se eh String ou Integer.
						
					if(isdigit((unsigned char)*auxiliar)) //conversao necessaria pela implementacao da funcao isdigit()
					{
						//auxiliar contem um imediato. caso trivial.
						auxiliarInt = atoi(auxiliar); //auxiliar contem o deslocamento.
						
						 AlocaComponente(VETOR, D_IMEDIATO, -1, auxiliarInt, nomeVar, NULL); //colocar o nome do vetor
					}
					else 
					{
						//auxiliar contem algo que nao eh digito. precisa ver se eh temp, var, ou vetor(*******TO DO********)
						strcpy(copia, q.addr_02.contents.nome);
						if(strstr(copia, "_TEMP_")) //argumento eh um temp. Separar indice
						{
							
							auxiliar = strtok(copia, "[");
							auxiliar = strtok(NULL, "]");
							auxiliar = strtok(auxiliar, "_TEMP");
							auxiliarInt = atoi(auxiliar); //auxiliar ja contem o indice. eh o deslocamento do vetor.
							
							 AlocaComponente(VETOR, D_TEMPORARIO, -1, auxiliarInt, nomeVar, NULL);
						} else if(strstr(copia, "_RET_"))
						{
							
							auxiliar = strtok(copia, "[");
							auxiliar = strtok(NULL, "]"); //auxiliar contem RET
							
							 AlocaComponente(VETOR, D_REG_RECT, -1, -1, nomeVar, NULL);
						} else if(verificaVetor(copia) == 0) //nao eh vetor. eh var
						{
							auxiliar = strtok(copia, "[");
							auxiliar = strtok(NULL, "]");
							
							 AlocaComponente(VETOR, D_VARIAVEL, -1, -1, nomeVar, auxiliar);
						} else
						{//eh vetor. precisa implementar
							
						}
					}
				}
				else if(strstr(q.addr_02.contents.nome, "RET"))
				{
					char copia[sizeof(q.addr_02.contents.nome)];
					strcpy(copia, q.addr_02.contents.nome);
					auxiliar = strtok(copia, "[");
					auxiliar = strtok(NULL, "]"); //auxiliar contem RET
					 AlocaComponente(REG_RECT, NULO, -1, -1, NULL, NULL);
				}else //q.addr_02 --> variavel
				{
					//trivial
					AlocaComponente(VARIAVEL, NULO, -1, -1, q.addr_02.contents.nome, NULL);
				}
			}
			else if(q.addr_02.kind == Integer) //com certeza eh imediato
			{
				 AlocaComponente(IMEDIATO, NULO, q.addr_02.contents.val, -1, NULL, NULL);
			}
			else if(q.addr_02.kind == Label)
			{
				//famosa gambiarra
				int i = 1;
				char copia[sizeof(q.addr_02.contents.label)-1];
				for(i; i<sizeof(copia)+1; i++)
				{
					copia[i-1] = q.addr_02.contents.label[i];
				}
				copia[sizeof(copia)] = '\0';
				int kkk_eae_men = atoi(copia);
				AlocaComponente(L_LABEL, NULO, kkk_eae_men, -1, NULL, NULL);
			}
			break;
		}
		case 3:
		{
			
			if(q.addr_03.kind == String) //pode ser vetor, variavel, temp, ret
			{	
				if(strstr(q.addr_03.contents.nome,"TEMP")) //q.addr_03 --> temporario
				{
					int valor;
					char copia[sizeof(q.addr_03.contents.nome)];
					strcpy(copia, q.addr_03.contents.nome);
					auxiliar = strtok(copia, "_TEMP"); //auxiliar contem o valor do indice do temporario.
					auxiliarInt = atoi(auxiliar);
					 AlocaComponente(TEMPORARIO, NULO, auxiliarInt, -1, NULL, NULL);
				}
				else if(strstr(q.addr_03.contents.nome, "[")) //eh um vetor por que tem o caracter "[" no nome
				{
					char copia[sizeof(q.addr_03.contents.nome)];
					strcpy(copia, q.addr_03.contents.nome);
					auxiliar = strtok(copia, "["); //auxiliar contem o nome do vetor.
					nomeVar = (char*)malloc(sizeof(auxiliar)*sizeof(char));
					strcpy(nomeVar, auxiliar); //copia o auxiliar pro nomeVar.
					auxiliar = strtok(NULL, "]");//auxiliar contem o valor da posicao do vetor. Verificar se eh String ou Integer.
					if(isdigit((unsigned char)*auxiliar)) //conversao necessaria pela implementacao da funcao isdigit()
					{
						//auxiliar contem um imediato. caso trivial.
						auxiliarInt = atoi(auxiliar); //auxiliar contem o deslocamento.
						 AlocaComponente(VETOR, D_IMEDIATO, -1, auxiliarInt, nomeVar, NULL); //colocar o nome do vetor
					}
					else 
					{
						//auxiliar contem algo que nao eh digito. precisa ver se eh temp, var, ou vetor(*******TO DO********)
						strcpy(copia, q.addr_03.contents.nome);
						if(strstr(copia, "_TEMP_")) //argumento eh um temp. Separar indice
						{
							auxiliar = strtok(copia, "[");
							auxiliar = strtok(NULL, "]");
							auxiliar = strtok(auxiliar, "_TEMP");
							auxiliarInt = atoi(auxiliar); //auxiliar ja contem o indice. eh o deslocamento do vetor.
							 AlocaComponente(VETOR, D_TEMPORARIO, -1, auxiliarInt, nomeVar, NULL);
						} else if(strstr(copia, "_RET_"))
						{
							auxiliar = strtok(copia, "[");
							auxiliar = strtok(NULL, "]"); //auxiliar contem RET
							 AlocaComponente(VETOR, D_REG_RECT, -1, -1, nomeVar, NULL);
						} else if(verificaVetor(copia) == 0) //nao eh vetor. eh var
						{
							auxiliar = strtok(copia, "[");
							auxiliar = strtok(NULL, "]");
							 AlocaComponente(VETOR, D_VARIAVEL, -1, -1, nomeVar, auxiliar);
						} else
						{//eh vetor. precisa implementar
							
						}
					}
				}
				else if(strstr(q.addr_03.contents.nome, "RET"))
				{
					char copia[sizeof(q.addr_03.contents.nome)];
					strcpy(copia, q.addr_03.contents.nome);
					auxiliar = strtok(copia, "[");
					auxiliar = strtok(NULL, "]"); //auxiliar contem RET
					 AlocaComponente(REG_RECT, NULO, -1, -1, NULL, NULL);
				}else //q.addr_03 --> variavel
				{
					//trivial
					AlocaComponente(VARIAVEL, NULO, -1, -1, q.addr_03.contents.nome, NULL);
				}
			}
			else if(q.addr_03.kind == Integer) //com certeza eh imediato
			{
				AlocaComponente(IMEDIATO, NULO, q.addr_03.contents.val, -1, NULL, NULL);
			}
			else if(q.addr_03.kind == Label)
			{
				//famosa gambiarra
				int i = 1;
				char copia[sizeof(q.addr_03.contents.label)-1];
				for(i; i<sizeof(copia)+1; i++)
				{
					copia[i-1] = q.addr_03.contents.label[i];
				}
				copia[sizeof(copia)] = '\0';
				int kkk_eae_men = atoi(copia);
				AlocaComponente(L_LABEL, NULO, kkk_eae_men, -1, NULL, NULL);
			}
			break;
		}
		default:
		{
			printf("funcao returnComponente(Quad_Cell q, int numero_enderço) deve ter  0 < numero_endereço < 4. Argumento recebido: %d\n", numero_endereco);
			break;
		}
	}
}

////////////////////////////////////////////////////

//TAD
void Load_Vetor_to_Reg(char* v, int position, char* desl, tipo_deslocamento type,int reg){//TAD
	int addr_mem;
	Operand * Op2;
	Operand * Op1;
	Operand * Op3;
	int addr_base;
	if(type==D_IMEDIATO){
		addr_mem = Get_Mem_Adress(v) + position;
		load_mem_to_reg_RE(addr_mem, reg);
	}else{
		if(type==D_VARIAVEL){
			addr_base = Get_Mem_Adress(v);
			load_mem_to_reg(desl);
			if(addr_base<256){
				Op1 = AlocaOperand(MEM,8, addr_base);
				Op2 = AlocaOperand(REG,8, tabela_memoria[returnPosition(desl)].reg);
				Op3 = AlocaOperand(REG,8, 1);
				InsereAssembly(I_ADD,Op1,Op2,Op3);//ADD addr_base $var $1
				printf("ADD %d $%d $1\n",addr_base, tabela_memoria[returnPosition(desl)].reg);
				tabela_registradores[1].flag_utilizado = 1;
				if(tabela_memoria[returnPosition(desl)].occurs == 0) load_reg_to_mem(tabela_memoria[returnPosition(desl)].reg);
			}else{
				if (addr_base<65536){
					Op1 = AlocaOperand(MEM,16, addr_base);
					Op2 = AlocaOperand(REG,8, 6);
					Op3 = NULL;
					InsereAssembly(I_SRVALUE,Op1,Op2,Op3);//SRVALUE addr_base $6
					printf("SRVALUE %d $6\n",addr_base);
					tabela_registradores[6].flag_utilizado = 1;
					
					Op1 = AlocaOperand(REG,8, 6);
					Op2 = AlocaOperand(REG,8, tabela_memoria[returnPosition(desl)].reg);
					Op3 = AlocaOperand(REG,8, 1);
					InsereAssembly(I_ADD,Op1,Op2,Op3);//ADD $6 $var $1
					printf("ADD $6 $%d $1\n", tabela_memoria[returnPosition(desl)].reg);
					tabela_registradores[6].flag_utilizado = 0;
					tabela_registradores[1].flag_utilizado = 1;
					if(tabela_memoria[returnPosition(desl)].occurs == 0) load_reg_to_mem(tabela_memoria[returnPosition(desl)].reg);
				}else{
					int addr_base_shifted;
					addr_base_shifted = (addr_base_shifted>>16);
					
					Op1 = AlocaOperand(MEM,16, addr_base_shifted);
					Op2 = AlocaOperand(REG,8, 1);
					Op3 = NULL;
					InsereAssembly(I_SRVALUE,Op1,Op2,Op3); //SRVALUE addr_base_shifted $1
					printf("SRVALUE %d $1\n", addr_base_shifted);
					tabela_registradores[1].flag_utilizado = 1;
					
					addr_base_shifted = (addr_base_shifted<<16);
					addr_base = addr_base - addr_base_shifted;
					
					Op1 = AlocaOperand(MEM,16, addr_base);
					Op2 = AlocaOperand(REG,8, 6);
					Op3 = NULL;
					InsereAssembly(I_SRVALUE,Op1,Op2,Op3);//SRVALUE addr_base $6
					printf("SRVALUE %d $6\n", addr_base);
					tabela_registradores[6].flag_utilizado = 1;
					
					Op1 = AlocaOperand(REG,8, 1);
					Op2 = AlocaOperand(MEM,8, 16);
					Op3 = AlocaOperand(REG,8, 1);
					InsereAssembly(I_SHL,Op1,Op2,Op3);//SHL $1 16 $1
					printf("SHL $1 16 $1\n");
					tabela_registradores[1].flag_utilizado = 0;
					tabela_registradores[1].flag_utilizado = 1;
					
					Op1 = AlocaOperand(REG,8, 1);
					Op2 = AlocaOperand(REG,8, 6);
					Op3 = AlocaOperand(REG,8, 6);
					InsereAssembly(I_ADD,Op1,Op2,Op3);//ADD $1 $6 $6
					printf("ADD $1 $6 $6\n");
					tabela_registradores[1].flag_utilizado = 0;
					tabela_registradores[6].flag_utilizado = 0;
					tabela_registradores[6].flag_utilizado = 1;
					
					Op1 = AlocaOperand(REG,8, 6);
					Op2 = AlocaOperand(REG,8, tabela_memoria[returnPosition(desl)].reg);
					Op3 = AlocaOperand(REG,8, 1);
					InsereAssembly(I_ADD,Op1,Op2,Op3);//ADD $6 $var $1
					printf("ADD $6 $%d $1\n", tabela_memoria[returnPosition(desl)].reg);
					tabela_registradores[6].flag_utilizado = 0;
					tabela_registradores[1].flag_utilizado = 1;
					if(tabela_memoria[returnPosition(desl)].occurs == 0) load_reg_to_mem(tabela_memoria[returnPosition(desl)].reg);
				}
			}
			Op1 = AlocaOperand(REG,16,1);
			Op2 = AlocaOperand(REG,8, reg);
			Op3 = NULL;
			InsereAssembly(I_LOAD,Op1,Op2,Op3);//LOAD $1 $reg
			printf("LOAD $1 $%d\n", reg);
			tabela_registradores[reg].flag_utilizado = 0;
			tabela_registradores[reg].flag_utilizado = 1;
		}else{
			if(type==D_TEMPORARIO){
				int temp_reg = SearchTemp(position);
				addr_base = Get_Mem_Adress(v);
				if(addr_base<256){
					Op1 = AlocaOperand(MEM,8, addr_base);
					Op2 = AlocaOperand(REG,8, temp_reg);
					Op3 = AlocaOperand(REG,8, 1);
					InsereAssembly(I_ADD,Op1,Op2,Op3);//ADD addr_base $temp_reg $1
					printf("ADD %d $%d $1\n", addr_base, temp_reg);
					tabela_registradores[1].flag_utilizado = 1;
					tabela_registradores[temp_reg].flag_utilizado = 0;
				}else{
					if (addr_base<65536){
						Op1 = AlocaOperand(MEM,16, addr_base);
						Op2 = AlocaOperand(REG,8, 6);
						Op3 = NULL;
						InsereAssembly(I_SRVALUE,Op1,Op2,Op3);//SRVALUE addr_base $6
						printf("SRVALUE %d $6\n", addr_base);
						tabela_registradores[6].flag_utilizado = 1;
						
						Op1 = AlocaOperand(REG,8, 6);
						Op2 = AlocaOperand(REG,8, temp_reg);
						Op3 = AlocaOperand(REG,8, 1);
						InsereAssembly(I_ADD,Op1,Op2,Op3);//ADD $6 $temp_reg $1
						printf("ADD $6 $%d $1\n", temp_reg);
						tabela_registradores[6].flag_utilizado = 0;
						tabela_registradores[temp_reg].flag_utilizado = 0;
						tabela_registradores[1].flag_utilizado = 1;
						
					}else{
						int addr_base_shifted;
						addr_base_shifted = (addr_base_shifted>>16);
						
						Op1 = AlocaOperand(MEM,16, addr_base_shifted);
						Op2 = AlocaOperand(REG,8, 1);
						Op3 = NULL;
						InsereAssembly(I_SRVALUE,Op1,Op2,Op3); //SRVALUE addr_base_shifted $1
						printf("SRVALUE %d $1\n", addr_base_shifted);
						tabela_registradores[1].flag_utilizado = 1;
						
						addr_base_shifted = (addr_base_shifted<<16);
						addr_base = addr_base - addr_base_shifted;
						
						Op1 = AlocaOperand(MEM,16, addr_base);
						Op2 = AlocaOperand(REG,8, 6);
						Op3 = NULL;
						InsereAssembly(I_SRVALUE,Op1,Op2,Op3);//SRVALUE addr_base $6
						printf("SRVALUE %d $6\n", addr_base);
						tabela_registradores[6].flag_utilizado = 1;
						
						Op1 = AlocaOperand(REG,8, 1);
						Op2 = AlocaOperand(MEM,8, 16);
						Op3 = AlocaOperand(REG,8, 1);
						InsereAssembly(I_SHL,Op1,Op2,Op3);//SHL $1 16 $1
						printf("SHL $1 16 $1\n");
						tabela_registradores[1].flag_utilizado = 0;
						tabela_registradores[1].flag_utilizado = 1;
						
						Op1 = AlocaOperand(REG,8, 1);
						Op2 = AlocaOperand(REG,8, 6);
						Op3 = AlocaOperand(REG,8, 6);
						InsereAssembly(I_ADD,Op1,Op2,Op3);//ADD $1 $6 $1
						printf("ADD $1 $6 $1\n");
						tabela_registradores[1].flag_utilizado = 0;
						tabela_registradores[6].flag_utilizado = 0;
						tabela_registradores[6].flag_utilizado = 1;
						
						Op1 = AlocaOperand(REG,8, 6);
						Op2 = AlocaOperand(REG,8, temp_reg);
						Op3 = AlocaOperand(REG,8, 1);
						InsereAssembly(I_ADD,Op1,Op2,Op3);//ADD $6 $temp_reg $1
						printf("ADD $6 $%d $1\n", temp_reg);
						tabela_registradores[6].flag_utilizado = 0;
						tabela_registradores[temp_reg].flag_utilizado = 0;
						tabela_registradores[1].flag_utilizado = 1;
					}
				}
				Op1 = AlocaOperand(REG,16,1);
				Op2 = AlocaOperand(REG,8, reg);
				Op3 = NULL;
				InsereAssembly(I_LOAD,Op1,Op2,Op3);//LOAD $1 $reg
				printf("LOAD $1 $%d\n", reg);
				tabela_registradores[1].flag_utilizado = 0;
				tabela_registradores[reg].flag_utilizado = 1;
			}else{
				if(type==D_REG_RECT){
					int temp_reg = 0;
					addr_base = Get_Mem_Adress(v);
					if(addr_base<256){
						Op1 = AlocaOperand(MEM,8, addr_base);
						Op2 = AlocaOperand(REG,8, temp_reg);
						Op3 = AlocaOperand(REG,8, 1);
						InsereAssembly(I_ADD,Op1,Op2,Op3);//ADD addr_base $temp_reg $1
						printf("ADD %d $%d $1\n", addr_base,temp_reg);
						tabela_registradores[1].flag_utilizado = 1;
						tabela_registradores[temp_reg].flag_utilizado = 0;
					}else{
						if (addr_base<65536){
							Op1 = AlocaOperand(MEM,16, addr_base);
							Op2 = AlocaOperand(REG,8, 6);
							Op3 = NULL;
							InsereAssembly(I_SRVALUE,Op1,Op2,Op3);//SRVALUE addr_base $6
							printf("SRVALUE %d $6\n", addr_base);
							tabela_registradores[6].flag_utilizado = 1;
							
							Op1 = AlocaOperand(REG,8, 6);
							Op2 = AlocaOperand(REG,8, temp_reg);
							Op3 = AlocaOperand(REG,8, 1);
							InsereAssembly(I_ADD,Op1,Op2,Op3);//ADD $6 $temp_reg $1
							printf("ADD $6 $%d $1\n", temp_reg);
							tabela_registradores[6].flag_utilizado = 0;
							tabela_registradores[temp_reg].flag_utilizado = 0;
							tabela_registradores[1].flag_utilizado = 1;
							
						}else{
							int addr_base_shifted;
							addr_base_shifted = (addr_base_shifted>>16);
							
							Op1 = AlocaOperand(MEM,16, addr_base_shifted);
							Op2 = AlocaOperand(REG,8, 1);
							Op3 = NULL;
							InsereAssembly(I_SRVALUE,Op1,Op2,Op3); //SRVALUE addr_base_shifted $1
							printf("SRVALUE %d $1\n", addr_base_shifted);
							tabela_registradores[1].flag_utilizado = 1;
							
							addr_base_shifted = (addr_base_shifted<<16);
							addr_base = addr_base - addr_base_shifted;
							
							Op1 = AlocaOperand(MEM,16, addr_base);
							Op2 = AlocaOperand(REG,8, 6);
							Op3 = NULL;
							InsereAssembly(I_SRVALUE,Op1,Op2,Op3);//SRVALUE addr_base $6
							printf("SRVALUE %d $6\n", addr_base);
							tabela_registradores[6].flag_utilizado = 1;
							
							Op1 = AlocaOperand(REG,8, 1);
							Op2 = AlocaOperand(MEM,8, 16);
							Op3 = AlocaOperand(REG,8, 1);
							InsereAssembly(I_SHL,Op1,Op2,Op3);//SHL $1 16 $1
							printf("SHL $1 16 $1\n");
							tabela_registradores[1].flag_utilizado = 0;
							tabela_registradores[1].flag_utilizado = 1;
							
							Op1 = AlocaOperand(REG,8, 1);
							Op2 = AlocaOperand(REG,8, 6);
							Op3 = AlocaOperand(REG,8, 6);
							InsereAssembly(I_ADD,Op1,Op2,Op3);//ADD $1 $6 $1
							printf("ADD $1 $6 $1\n");
							tabela_registradores[1].flag_utilizado = 0;
							tabela_registradores[6].flag_utilizado = 0;
							tabela_registradores[6].flag_utilizado = 1;
							
							Op1 = AlocaOperand(REG,8, 6);
							Op2 = AlocaOperand(REG,8, temp_reg);
							Op3 = AlocaOperand(REG,8, 1);
							InsereAssembly(I_ADD,Op1,Op2,Op3);//ADD $6 $temp_reg $1
							printf("ADD $6 $%d $1\n", temp_reg);
							tabela_registradores[6].flag_utilizado = 0;
							tabela_registradores[temp_reg].flag_utilizado = 0;
							tabela_registradores[1].flag_utilizado = 1;
						}
					}
					Op1 = AlocaOperand(REG,16,1);
					Op2 = AlocaOperand(REG,8, reg);
					Op3 = NULL;
					InsereAssembly(I_LOAD,Op1,Op2,Op3);//LOAD $1 $reg
					printf("LOAD $1 $%d\n", reg);
					tabela_registradores[reg].flag_utilizado = 0;
					tabela_registradores[reg].flag_utilizado = 1;
				}
			}
		}
	}
}


void Store_to_Vetor(char* v, int position, char* desl, tipo_deslocamento type,int reg){//TAD
	int addr_mem;
	Operand * Op2;
	Operand * Op1;
	Operand * Op3;
	int addr_base;
	if(type==D_IMEDIATO){
		addr_mem = Get_Mem_Adress(v) + position;
		Op1 = AlocaOperand(REG,8, reg);
		Op2 = AlocaOperand(MEM,16, addr_mem);
		Op3 = NULL;
		InsereAssembly(I_STORE,Op1,Op2,Op3);//STORE $reg addr_mem
		printf("STORE $%d %d\n", reg, addr_mem);
		tabela_registradores[reg].flag_utilizado = 0;
	}else{
		if(type==D_VARIAVEL){
			addr_base = Get_Mem_Adress(v);
			load_mem_to_reg(desl);
			if(addr_base<256){
				Op1 = AlocaOperand(MEM,8, addr_base);
				Op2 = AlocaOperand(REG,8, tabela_memoria[returnPosition(desl)].reg);
				Op3 = AlocaOperand(REG,8, 1);
				InsereAssembly(I_ADD,Op1,Op2,Op3);//ADD addr_base $var $1
				printf("ADD %d $%d $1\n", addr_base, tabela_memoria[returnPosition(desl)].reg);
				tabela_registradores[1].flag_utilizado = 1;
				if(tabela_memoria[returnPosition(desl)].occurs == 0) load_reg_to_mem(tabela_memoria[returnPosition(desl)].reg);
			}else{
				if (addr_base<65536){
					Op1 = AlocaOperand(MEM,16, addr_base);
					Op2 = AlocaOperand(REG,8, 6);
					Op3 = NULL;
					InsereAssembly(I_SRVALUE,Op1,Op2,Op3);//SRVALUE addr_base $6
					printf("SRVALUE %d $6\n", addr_base);
					tabela_registradores[6].flag_utilizado = 1;
					
					Op1 = AlocaOperand(REG,8, 6);
					Op2 = AlocaOperand(REG,8, tabela_memoria[returnPosition(desl)].reg);
					Op3 = AlocaOperand(REG,8, 1);
					InsereAssembly(I_ADD,Op1,Op2,Op3);//ADD $6 $var $1
					printf("ADD $6 $%d $1\n",tabela_memoria[returnPosition(desl)].reg);
					tabela_registradores[6].flag_utilizado = 0;
					tabela_registradores[1].flag_utilizado = 1;
					if(tabela_memoria[returnPosition(desl)].occurs == 0) load_reg_to_mem(tabela_memoria[returnPosition(desl)].reg);
				}else{
					int addr_base_shifted;
					addr_base_shifted = (addr_base_shifted>>16);
					
					Op1 = AlocaOperand(MEM,16, addr_base_shifted);
					Op2 = AlocaOperand(REG,8, 1);
					Op3 = NULL;
					InsereAssembly(I_SRVALUE,Op1,Op2,Op3); //SRVALUE addr_base_shifted $1
					printf("SRVALUE %d $1\n", addr_base_shifted);
					tabela_registradores[1].flag_utilizado = 1;
					
					addr_base_shifted = (addr_base_shifted<<16);
					addr_base = addr_base - addr_base_shifted;
					
					Op1 = AlocaOperand(MEM,16, addr_base);
					Op2 = AlocaOperand(REG,8, 6);
					Op3 = NULL;
					InsereAssembly(I_SRVALUE,Op1,Op2,Op3);//SRVALUE addr_base $6
					printf("SRVALUE %d $6\n", addr_base);
					tabela_registradores[6].flag_utilizado = 1;
					
					Op1 = AlocaOperand(REG,8, 1);
					Op2 = AlocaOperand(MEM,8, 16);
					Op3 = AlocaOperand(REG,8, 1);
					InsereAssembly(I_SHL,Op1,Op2,Op3);//SHL $1 16 $1
					printf("SHL $1 16 $1\n");
					tabela_registradores[1].flag_utilizado = 0;
					tabela_registradores[1].flag_utilizado = 1;
					
					Op1 = AlocaOperand(REG,8, 1);
					Op2 = AlocaOperand(REG,8, 6);
					Op3 = AlocaOperand(REG,8, 6);
					InsereAssembly(I_ADD,Op1,Op2,Op3);//ADD $1 $6 $6
					printf("ADD $1 $6 $6\n");
					tabela_registradores[1].flag_utilizado = 0;
					tabela_registradores[6].flag_utilizado = 0;
					tabela_registradores[6].flag_utilizado = 1;
					
					Op1 = AlocaOperand(REG,8, 6);
					Op2 = AlocaOperand(REG,8, tabela_memoria[returnPosition(desl)].reg);
					Op3 = AlocaOperand(REG,8, 1);
					InsereAssembly(I_ADD,Op1,Op2,Op3);//ADD $6 $var $1
					printf("ADD $6 $%d $1\n",tabela_memoria[returnPosition(desl)].reg);
					tabela_registradores[6].flag_utilizado = 0;
					tabela_registradores[1].flag_utilizado = 1;
					if(tabela_memoria[returnPosition(desl)].occurs == 0) load_reg_to_mem(tabela_memoria[returnPosition(desl)].reg);
				}
			}
			Op1 = AlocaOperand(REG,8, reg);
			Op2 = AlocaOperand(REG,16, 1);
			Op3 = NULL;
			InsereAssembly(I_STORE,Op1,Op2,Op3);//STORE $reg $1
			printf("STORE $%d $1\n", reg);
			tabela_registradores[reg].flag_utilizado = 0;
			tabela_registradores[1].flag_utilizado = 0;
			
		}else{
			if(type==D_TEMPORARIO){
				int temp_reg = SearchTemp(position);
				addr_base = Get_Mem_Adress(v);
				if(addr_base<256){
					Op1 = AlocaOperand(MEM,8, addr_base);
					Op2 = AlocaOperand(REG,8, temp_reg);
					Op3 = AlocaOperand(REG,8, 1);
					InsereAssembly(I_ADD,Op1,Op2,Op3);//ADD addr_base $temp_reg $1
					printf("ADD %d $%d $1\n", addr_base, temp_reg);
					tabela_registradores[1].flag_utilizado = 1;
					tabela_registradores[temp_reg].flag_utilizado = 0;
				}else{
					if (addr_base<65536){
						Op1 = AlocaOperand(MEM,16, addr_base);
						Op2 = AlocaOperand(REG,8, 6);
						Op3 = NULL;
						InsereAssembly(I_SRVALUE,Op1,Op2,Op3);//SRVALUE addr_base $6
						printf("SRVALUE %d $6\n", addr_base);
						tabela_registradores[6].flag_utilizado = 1;
						
						Op1 = AlocaOperand(REG,8, 6);
						Op2 = AlocaOperand(REG,8, temp_reg);
						Op3 = AlocaOperand(REG,8, 1);
						InsereAssembly(I_ADD,Op1,Op2,Op3);//ADD $6 $temp_reg $1
						printf("ADD $6 $%d $1\n", temp_reg);
						tabela_registradores[6].flag_utilizado = 0;
						tabela_registradores[temp_reg].flag_utilizado = 0;
						tabela_registradores[1].flag_utilizado = 1;
						
					}else{
						int addr_base_shifted;
						addr_base_shifted = (addr_base_shifted>>16);
						
						Op1 = AlocaOperand(MEM,16, addr_base_shifted);
						Op2 = AlocaOperand(REG,8, 1);
						Op3 = NULL;
						InsereAssembly(I_SRVALUE,Op1,Op2,Op3); //SRVALUE addr_base_shifted $1
						printf("SRVALUE %d $1\n", addr_base_shifted);
						tabela_registradores[1].flag_utilizado = 1;
						
						addr_base_shifted = (addr_base_shifted<<16);
						addr_base = addr_base - addr_base_shifted;
						
						Op1 = AlocaOperand(MEM,16, addr_base);
						Op2 = AlocaOperand(REG,8, 6);
						Op3 = NULL;
						InsereAssembly(I_SRVALUE,Op1,Op2,Op3);//SRVALUE addr_base $6
						printf("SRVALUE %d $6\n", addr_base);
						tabela_registradores[6].flag_utilizado = 1;
						
						Op1 = AlocaOperand(REG,8, 1);
						Op2 = AlocaOperand(MEM,8, 16);
						Op3 = AlocaOperand(REG,8, 1);
						InsereAssembly(I_SHL,Op1,Op2,Op3);//SHL $1 16 $1
						printf("SHL $1 16 $1\n");
						tabela_registradores[1].flag_utilizado = 0;
						tabela_registradores[1].flag_utilizado = 1;
						
						Op1 = AlocaOperand(REG,8, 1);
						Op2 = AlocaOperand(REG,8, 6);
						Op3 = AlocaOperand(REG,8, 6);
						InsereAssembly(I_ADD,Op1,Op2,Op3);//ADD $1 $6 $6
						printf("ADD $1 $6 $6\n");
						tabela_registradores[1].flag_utilizado = 0;
						tabela_registradores[6].flag_utilizado = 0;
						tabela_registradores[6].flag_utilizado = 1;
						
						Op1 = AlocaOperand(REG,8, 6);
						Op2 = AlocaOperand(REG,8, temp_reg);
						Op3 = AlocaOperand(REG,8, 1);
						InsereAssembly(I_ADD,Op1,Op2,Op3);//ADD $6 $temp_reg $1
						printf("ADD $6 $%d $1\n", temp_reg);
						tabela_registradores[6].flag_utilizado = 0;
						tabela_registradores[temp_reg].flag_utilizado = 0;
						tabela_registradores[1].flag_utilizado = 1;
					}
				}
				Op1 = AlocaOperand(REG,8, reg);
				Op2 = AlocaOperand(REG,16, 1);
				Op3 = NULL;
				InsereAssembly(I_STORE,Op1,Op2,Op3);//STORE $reg $1
				printf("STORE $%d $1\n",reg);
				tabela_registradores[reg].flag_utilizado = 0;
				tabela_registradores[1].flag_utilizado = 0;
			}else{
				if(type==D_REG_RECT){
					int temp_reg = 0;
					addr_base = Get_Mem_Adress(v);
					if(addr_base<256){
						Op1 = AlocaOperand(MEM,8, addr_base);
						Op2 = AlocaOperand(REG,8, temp_reg);
						Op3 = AlocaOperand(REG,8, 1);
						InsereAssembly(I_ADD,Op1,Op2,Op3);//ADD addr_base $temp_reg $1
						printf("ADD %d $%d $1\n", addr_base, temp_reg);
						tabela_registradores[1].flag_utilizado = 1;
						tabela_registradores[temp_reg].flag_utilizado = 0;
					}else{
						if (addr_base<65536){
							Op1 = AlocaOperand(MEM,16, addr_base);
							Op2 = AlocaOperand(REG,8, 6);
							Op3 = NULL;
							InsereAssembly(I_SRVALUE,Op1,Op2,Op3);//SRVALUE addr_base $6
							printf("SRVALUE %d $6\n", addr_base);
							tabela_registradores[6].flag_utilizado = 1;
							
							Op1 = AlocaOperand(REG,8, 6);
							Op2 = AlocaOperand(REG,8, temp_reg);
							Op3 = AlocaOperand(REG,8, 1);
							InsereAssembly(I_ADD,Op1,Op2,Op3);//ADD $6 $temp_reg $1
							printf("ADD $6 $%d $1\n", temp_reg);
							tabela_registradores[6].flag_utilizado = 0;
							tabela_registradores[temp_reg].flag_utilizado = 0;
							tabela_registradores[1].flag_utilizado = 1;
							
						}else{
							int addr_base_shifted;
							addr_base_shifted = (addr_base_shifted>>16);
							
							Op1 = AlocaOperand(MEM,16, addr_base_shifted);
							Op2 = AlocaOperand(REG,8, 1);
							Op3 = NULL;
							InsereAssembly(I_SRVALUE,Op1,Op2,Op3); //SRVALUE addr_base_shifted $1
							printf("SRVALUE %d $1\n", addr_base_shifted);
							tabela_registradores[1].flag_utilizado = 1;
							
							addr_base_shifted = (addr_base_shifted<<16);
							addr_base = addr_base - addr_base_shifted;
							
							Op1 = AlocaOperand(MEM,16, addr_base);
							Op2 = AlocaOperand(REG,8, 6);
							Op3 = NULL;
							InsereAssembly(I_SRVALUE,Op1,Op2,Op3);//SRVALUE addr_base $6
							printf("SRVALUE %d $6\n", addr_base);
							tabela_registradores[6].flag_utilizado = 1;
							
							Op1 = AlocaOperand(REG,8, 1);
							Op2 = AlocaOperand(MEM,8, 16);
							Op3 = AlocaOperand(REG,8, 1);
							InsereAssembly(I_SHL,Op1,Op2,Op3);//SHL $1 16 $1
							printf("SHL $1 16 $1\n");
							tabela_registradores[1].flag_utilizado = 0;
							tabela_registradores[1].flag_utilizado = 1;
							
							Op1 = AlocaOperand(REG,8, 1);
							Op2 = AlocaOperand(REG,8, 6);
							Op3 = AlocaOperand(REG,8, 6);
							InsereAssembly(I_ADD,Op1,Op2,Op3);//ADD $1 $6 $1
							printf("ADD $1 $6 $1\n");
							tabela_registradores[1].flag_utilizado = 0;
							tabela_registradores[6].flag_utilizado = 0;
							tabela_registradores[6].flag_utilizado = 1;
							
							Op1 = AlocaOperand(REG,8, 6);
							Op2 = AlocaOperand(REG,8, temp_reg);
							Op3 = AlocaOperand(REG,8, 1);
							InsereAssembly(I_ADD,Op1,Op2,Op3);//ADD $6 $temp_reg $1
							printf("ADD $6 $%d $1\n", temp_reg);
							tabela_registradores[6].flag_utilizado = 0;
							tabela_registradores[temp_reg].flag_utilizado = 0;
							tabela_registradores[1].flag_utilizado = 1;
						}
					}
					Op1 = AlocaOperand(REG,8, reg);
					Op2 = AlocaOperand(REG,16, 1);
					Op3 = NULL;
					InsereAssembly(I_STORE,Op1,Op2,Op3);//STORE $reg $1
					printf("STORE $%d $1\n", reg);
					tabela_registradores[reg].flag_utilizado = 0;
					tabela_registradores[1].flag_utilizado = 0;
				}
			}
		}
	}
}


void Load_Operand(Componente* field, int reg){//TAD
	Operand * Op1;
	Operand * Op2;
	Operand * Op3;
	if(field->type == VARIAVEL){
		if (tabela_memoria[returnPosition(field->var)].size==1){
			load_mem_to_reg(field->var);
			int reg_var = tabela_memoria[returnPosition(field->var)].reg;
			Op1 = AlocaOperand(REG,8, reg_var);
			Op2 = AlocaOperand(REG,16, reg);
			Op3 = NULL;
			InsereAssembly(I_REGCOPY,Op1,Op2,Op3);//REGCOPY $var $reg
			printf("REGCOPY $%d $%d\n", reg_var,reg);
			tabela_registradores[reg].flag_utilizado = 1;
			if(tabela_memoria[returnPosition(field->var)].occurs == 0) load_reg_to_mem(tabela_memoria[returnPosition(field->var)].reg);
		}
	}else{
		if(field->type == VETOR){
			Load_Vetor_to_Reg(field->var, field->deslocamento, field->desl, field->type_d, reg);
		}else{
			if(field->type == TEMPORARIO){
				int reg_temp = SearchTemp(field->value);
				
				Op1 = AlocaOperand(REG,8, reg_temp);
				Op2 = AlocaOperand(REG,16, reg);
				Op3 = NULL;
				InsereAssembly(I_REGCOPY,Op1,Op2,Op3);//REGCOPY $reg_temp $reg
				printf("REGCOPY $%d $%d\n", reg_temp,reg);
				tabela_registradores[reg_temp].flag_utilizado = 0;
				tabela_registradores[reg].flag_utilizado = 1;
			}else{
				if(field->type == IMEDIATO){
					if (field->value < 65536){
						Op1 = AlocaOperand(MEM,16, field->value);
						Op2 = AlocaOperand(REG,8, reg);
						Op3 = NULL;
						InsereAssembly(I_SRVALUE,Op1,Op2,Op3);//SRVALUE field->value $reg
						printf("SRVALUE %d $%d\n", field->value,reg);
						tabela_registradores[reg].flag_utilizado = 1;
					}else{
						int addr_base_shifted;
						int addr_base = field->value;
						addr_base_shifted = (addr_base_shifted>>16);
						
						Op1 = AlocaOperand(MEM,16, addr_base_shifted);
						Op2 = AlocaOperand(REG,8, 1);
						Op3 = NULL;
						InsereAssembly(I_SRVALUE,Op1,Op2,Op3); //SRVALUE addr_base_shifted $1
						printf("SRVALUE %d $1\n", addr_base_shifted);
						tabela_registradores[1].flag_utilizado = 1;
						
						addr_base_shifted = (addr_base_shifted<<16);
						addr_base = addr_base - addr_base_shifted;
						
						Op1 = AlocaOperand(MEM,16, addr_base);
						Op2 = AlocaOperand(REG,8, reg);
						Op3 = NULL;
						InsereAssembly(I_SRVALUE,Op1,Op2,Op3);//SRVALUE addr_base $reg
						printf("SRVALUE %d $%d\n", addr_base, reg);
						tabela_registradores[reg].flag_utilizado = 1;
						
						Op1 = AlocaOperand(REG,8, 1);
						Op2 = AlocaOperand(MEM,8, 16);
						Op3 = AlocaOperand(REG,8, 1);
						InsereAssembly(I_SHL,Op1,Op2,Op3);//SHL $1 16 $1
						printf("SHL $1 16 $1\n");
						tabela_registradores[1].flag_utilizado = 0;
						tabela_registradores[1].flag_utilizado = 1;
						
						Op1 = AlocaOperand(REG,8, 1);
						Op2 = AlocaOperand(REG,8, reg);
						Op3 = AlocaOperand(REG,8, reg);
						InsereAssembly(I_ADD,Op1,Op2,Op3);//ADD $1 $reg $reg
						printf("ADD $1 $%d $%d\n", reg, reg);
						tabela_registradores[1].flag_utilizado = 0;
						tabela_registradores[reg].flag_utilizado = 0;
						tabela_registradores[reg].flag_utilizado = 1;
					}
				}else{
					if(field->type == REG_RECT){
						int reg_temp = 0;
				
						Op1 = AlocaOperand(REG,8, reg_temp);
						Op2 = AlocaOperand(REG,16, reg);
						Op3 = NULL;
						InsereAssembly(I_REGCOPY,Op1,Op2,Op3);//REGCOPY $reg_temp $reg
						printf("REGCOPY $%d $%d\n", reg_temp, reg);
						tabela_registradores[reg_temp].flag_utilizado = 0;
						tabela_registradores[reg].flag_utilizado = 1;
					}
				}
			}
		}
	}
}


void Assign_Operand(Componente* field, int reg){//TAD
	Operand * Op1;
	Operand * Op2;
	Operand * Op3;
	if(field->type == VARIAVEL){
		if (tabela_memoria[returnPosition(field->var)].size==1){
			load_mem_to_reg(field->var);
			int reg_var = tabela_memoria[returnPosition(field->var)].reg;

			Op1 = AlocaOperand(REG,8, reg);
			Op2 = AlocaOperand(REG,16, reg_var);
			Op3 = NULL;
			InsereAssembly(I_REGCOPY,Op1,Op2,Op3);//REGCOPY $reg $var
			printf("REGCOPY $%d $%d\n", reg, reg_var);
			tabela_registradores[reg].flag_utilizado = 0;
			if(tabela_memoria[returnPosition(field->var)].occurs == 0) load_reg_to_mem(tabela_memoria[returnPosition(field->var)].reg);
		}
	}else{
		if(field->type == VETOR){
			Store_to_Vetor(field->var, field->deslocamento, field->desl, field->type_d, reg);
		}else{
			if(field->type == TEMPORARIO){
				int reg_temp = returnFree_Temp();
				
				Op1 = AlocaOperand(REG,8, reg);
				Op2 = AlocaOperand(REG,16, reg_temp);
				Op3 = NULL;
				InsereAssembly(I_REGCOPY,Op1,Op2,Op3);//REGCOPY $reg $reg_temp
				printf("REGCOPY $%d $%d\n", reg, reg_temp);
				tabela_registradores[reg_temp].flag_utilizado = 1;
				tabela_registradores[reg].flag_utilizado = 0;
				tabela_registradores[reg_temp].var = field->value;
			}else{
				if(field->type == REG_RECT){
					int reg_temp = 0;
					Op1 = AlocaOperand(REG,8, reg);
					Op2 = AlocaOperand(REG,16, reg_temp);
					Op3 = NULL;
					InsereAssembly(I_REGCOPY,Op1,Op2,Op3);//REGCOPY $reg $reg_temp
					printf("REGCOPY $%d $%d\n", reg, reg_temp);
					tabela_registradores[reg_temp].flag_utilizado = 1;
					tabela_registradores[reg].flag_utilizado = 0;
				}
			}
		}
	}
}

int convertString_to_label(char* str){
	int key = 65536;
	for(int i = 0; i < strlen(str)+1; i++) {
		key = key + str[i]*(i+1);	
	}
	return key;
}

void Store_Global_Reg_Table_nextScope(){//TAD
	int addr_mem;
	for (int j = 0;j<global_contador;j++){
		if(tabela_memoria_global[j].size == 1){//verifica se não é vetor
			addr_mem = Get_Mem_Adress(tabela_memoria_global[j].var);
			load_mem_to_reg_RE(addr_mem, 1);
			addr_mem = Get_Mem_Adress(tabela_memoria_global[j].var) + reserved_mem_total;
			load_reg_to_mem_addr(1,addr_mem);
		}else{
			for(int p = 0;p<tabela_memoria_global[j].size;p++){
				addr_mem = Get_Mem_Adress(tabela_memoria_global[j].var) + p;
				load_mem_to_reg_RE(addr_mem, 1);
				addr_mem = Get_Mem_Adress(tabela_memoria_global[j].var) + reserved_mem_total + p;
				load_reg_to_mem_addr(1,addr_mem);
			}
		}
	}	
}

void Store_Global_Reg_Table_prevScope(){//TAD
	int addr_mem;
	for (int j = 0;j<global_contador;j++){
		if(tabela_memoria_global[j].size == 1){//verifica se não é vetor
			addr_mem = Get_Mem_Adress(tabela_memoria_global[j].var) + reserved_mem_total;
			load_mem_to_reg_RE(addr_mem, 1);
			addr_mem = Get_Mem_Adress(tabela_memoria_global[j].var);
			load_reg_to_mem_addr(1,addr_mem);
		}else{
			for(int p = 0;p<tabela_memoria_global[j].size;p++){
				addr_mem = Get_Mem_Adress(tabela_memoria_global[j].var) + reserved_mem_total + p;
				load_mem_to_reg_RE(addr_mem, 1);
				addr_mem = Get_Mem_Adress(tabela_memoria_global[j].var) + p;
				load_reg_to_mem_addr(1,addr_mem);
			}
		}
	}
}


///////////////////////////////////////////////////

char* funcalString;

Quad_List* Generate_Assembly_for_ARGS(Quad_List* code_int){
	
	Operand * Op1;
	Operand * Op2;
	Operand * Op3;
	int reserved_mem_parametro;
	int parametro_contador;
	int* tabela_memoria_parametro;
	tabela_memoria_parametro = NULL;
	reserved_mem_parametro = 0;
	parametro_contador = 0;
	while(code_int->quad.op!=FUNCAL){
		Quad_Cell quad = code_int->quad;
		switch(quad.op){
		case BEGIN_ARGS:
			
			code_int = Generate_Assembly_for_ARGS(code_int->next);
			
			Store_ALL_Reg_Table();
			Store_Global_Reg_Table_nextScope();
			Op1 = AlocaOperand(MEM,16, reserved_mem_total);
			InsereAssembly(I_PUSH_R,Op1,NULL,NULL);//PUSH.R reserved_mem_total
			printf("PUSH.R %d\n", reserved_mem_total);
			Op1 = AlocaOperand(MEM,8, contador+2);
			InsereAssembly(I_PUSH_PC,Op1,NULL,NULL);//PUSH.PC contador+2
			printf("PUSH.PC %d \n", contador+2);

			Op1 = AlocaOperand(LAB,32, convertString_to_label(funcalString));
			InsereAssembly(I_JMP,Op1,NULL,NULL);//JMP value
			printf("JMP %d\n", convertString_to_label(funcalString));

			InsereAssembly(I_POP_R,NULL,NULL,NULL);//POP.R 
			printf("POP.R \n");
			Store_Global_Reg_Table_prevScope();
			Load_ALL_Mem_Table();

			
		break;
		case INTCODE_ADD:
			
			returnComponente(quad,1);
			Load_Operand(c,2);
			returnComponente(quad,2);
			Load_Operand(c,3);
			returnComponente(quad,3);
			if (c->type == TEMPORARIO){
				int reg_temp = returnFree_Temp();
				Op1 = AlocaOperand(REG,8, 2);
				Op2 = AlocaOperand(REG,8, 3);
				Op3 = AlocaOperand(REG,8, reg_temp);
				InsereAssembly(I_ADD,Op1,Op2,Op3);//ADD $2 $3 $temp
				printf("ADD $2 $3 $%d\n", reg_temp);
				tabela_registradores[2].flag_utilizado = 0;
				tabela_registradores[3].flag_utilizado = 0;
				tabela_registradores[reg_temp].flag_utilizado = 1;
				tabela_registradores[reg_temp].var = c->value;
			}
			
		break;
		case INTCODE_SUB:
			
			returnComponente(quad,1);
			Load_Operand(c,2);
			returnComponente(quad,2);
			Load_Operand(c,3);
			returnComponente(quad,3);
			if (c->type == TEMPORARIO){
				int reg_temp = returnFree_Temp();
				Op1 = AlocaOperand(REG,8, 2);
				Op2 = AlocaOperand(REG,8, 3);
				Op3 = AlocaOperand(REG,8, reg_temp);
				InsereAssembly(I_SUB,Op1,Op2,Op3);//SUB $2 $3 $temp
				printf("SUB $2 $3 $%d\n", reg_temp);
				tabela_registradores[2].flag_utilizado = 0;
				tabela_registradores[3].flag_utilizado = 0;
				tabela_registradores[reg_temp].flag_utilizado = 1;
				tabela_registradores[reg_temp].var = c->value;
			}
			
		break;
		case INTCODE_MUL:
			
			returnComponente(quad,1);
			Load_Operand(c,2);
			returnComponente(quad,2);
			Load_Operand(c,3);
			returnComponente(quad,3);
			if (c->type == TEMPORARIO){
				int reg_temp = returnFree_Temp();
				Op1 = AlocaOperand(REG,8, 2);
				Op2 = AlocaOperand(REG,8, 3);
				Op3 = AlocaOperand(REG,8, reg_temp);
				InsereAssembly(I_MUL,Op1,Op2,Op3);//MUL $2 $3 $temp
				printf("MUL $2 $3 $%d\n", reg_temp);
				tabela_registradores[2].flag_utilizado = 0;
				tabela_registradores[3].flag_utilizado = 0;
				tabela_registradores[reg_temp].flag_utilizado = 1;
				tabela_registradores[reg_temp].var = c->value;
			}
			
		break;
		case INTCODE_DIV:
			
			returnComponente(quad,1);
			Load_Operand(c,2);
			returnComponente(quad,2);
			Load_Operand(c,3);
			returnComponente(quad,3);
			if (c->type == TEMPORARIO){
				int reg_temp = returnFree_Temp();
				Op1 = AlocaOperand(REG,8, 2);
				Op2 = AlocaOperand(REG,8, 3);
				Op3 = AlocaOperand(REG,8, reg_temp);
				InsereAssembly(I_DIV,Op1,Op2,Op3);//DIV $2 $3 $temp
				printf("DIV $2 $3 $%d\n", reg_temp);
				tabela_registradores[2].flag_utilizado = 0;
				tabela_registradores[3].flag_utilizado = 0;
				tabela_registradores[reg_temp].flag_utilizado = 1;
				tabela_registradores[reg_temp].var = c->value;
			}
			
		break;
		case INTCODE_ASSIGN:
			
			returnComponente(quad,2);
			Load_Operand(c,3);
			returnComponente(quad,1);
			Assign_Operand(c,3);
			
		break;
		case INTCODE_RET:
			
			returnComponente(quad,1);
			Load_Operand(c,0);
			Store_ALL_Reg_Table();
			Op1 = AlocaOperand(MEM,0, 0);
			InsereAssembly(I_POP_PC,Op1,NULL,NULL);//POP.PC 
			printf("POP.PC \n");
			
		break;
		case ARG:
			
			returnComponente(quad,1);
			if (c->type == VARIAVEL){
				int position = returnPosition(c->var);
				if (tabela_memoria[position].size>1){
					for(int p = 0;p < tabela_memoria[position].size;p++){
						int addr_mem = Get_Mem_Adress(tabela_memoria[position].var) + p;
						load_mem_to_reg_RE(addr_mem, 1);
						addr_mem = Get_Mem_Adress_REG_Param(tabela_memoria_parametro,parametro_contador) + reserved_mem_total + reserved_mem_global + p;
						load_reg_to_mem_addr(1,addr_mem);
					}
					if(tabela_memoria[position].occurs > 0) tabela_memoria[position].occurs--;
					if(tabela_memoria[position].occurs == 0) load_reg_to_mem(tabela_memoria[position].reg);
					parametro_contador++;
					tabela_memoria_parametro = (int*)realloc(tabela_memoria_parametro,parametro_contador*(sizeof(int)));
					tabela_memoria_parametro[parametro_contador-1] = max_array_size;
					reserved_mem_parametro = reserved_mem_parametro + max_array_size;
				}else{
					Load_Operand(c,3);
					int addr_mem = Get_Mem_Adress_REG_Param(tabela_memoria_parametro,parametro_contador) + reserved_mem_total + reserved_mem_global;
					load_reg_to_mem_addr(3,addr_mem);
					parametro_contador++;
					tabela_memoria_parametro = (int*)realloc(tabela_memoria_parametro,parametro_contador*(sizeof(int)));
					tabela_memoria_parametro[parametro_contador-1] = tabela_memoria[position].size;
					reserved_mem_parametro = reserved_mem_parametro + tabela_memoria[position].size;
				}
			}else{
				Load_Operand(c,3);
				int addr_mem = Get_Mem_Adress_REG_Param(tabela_memoria_parametro,parametro_contador) + reserved_mem_total + reserved_mem_global;
				load_reg_to_mem_addr(3,addr_mem);
				parametro_contador++;
				tabela_memoria_parametro = (int*)realloc(tabela_memoria_parametro,parametro_contador*(sizeof(int)));
				tabela_memoria_parametro[parametro_contador-1] = 1;
				reserved_mem_parametro = reserved_mem_parametro + 1;
			}
			
		break;
		case JMP:
			
			Store_ALL_Reg_Table();
			returnComponente(quad,1);
			if(c->type == L_LABEL){
				Op1 = AlocaOperand(LAB,32, c->value);
				Op2 = NULL;
				Op3 = NULL;
				InsereAssembly(I_JMP,Op1,Op2,Op3);//JMP c->value
				printf("JMP %d\n", c->value);
			}
			Load_ALL_Mem_Table();
			
		break;
		case LABEL:
			
			Store_ALL_Reg_Table();
			returnComponente(quad,1);
			if(c->type == L_LABEL){
				Op1 = AlocaOperand(LAB,32, c->value);
				Op2 = NULL;
				Op3 = NULL;
				InsereAssembly(I_LABEL,Op1,Op2,Op3);//LB c->value
				printf("LB %d\n", c->value);
			}
			Load_ALL_Mem_Table();
			
		break;
		}
		code_int = code_int->next;
	}
	funcalString = (char*)malloc(sizeof(code_int->quad.addr_01.contents.nome)*sizeof(char));
	if (code_int->quad.addr_01.contents.nome != NULL) strcpy(funcalString, code_int->quad.addr_01.contents.nome);
	return code_int;
}

void Generate_Assembly(){
	Quad_List* code_int;
	Operand * Op1;
	Operand * Op2;
	Operand * Op3;
	int reserved_mem_parametro;
	int parametro_contador;
	int* tabela_memoria_parametro;
	tabela_memoria_parametro = NULL;
	reserved_mem_parametro = 0;
	parametro_contador = 0;
	
	code_int = return_func_def("main");
	Constroi_Tabela_Global();
	Create_Mem_Table("main");
	initial_load_to_reg();
	printf("PROCESSANDO MAIN\n");
	while(code_int!=NULL){
		Quad_Cell quad = code_int->quad;
		switch(quad.op){
		case BEGIN_ARGS:
			code_int = Generate_Assembly_for_ARGS(code_int->next);
			//FUNCAL
			Store_ALL_Reg_Table();
			Store_Global_Reg_Table_nextScope();
			Op1 = AlocaOperand(MEM,16, reserved_mem_total);
			InsereAssembly(I_PUSH_R,Op1,NULL,NULL);//PUSH.R reserved_mem_total
			printf("PUSH.R %d\n", reserved_mem_total);
			Op1 = AlocaOperand(MEM,8, contador+2);
			InsereAssembly(I_PUSH_PC,Op1,NULL,NULL);//PUSH.PC contador+2
			printf("PUSH.PC %d \n", contador+2);
			

			Op1 = AlocaOperand(LAB,32, convertString_to_label(funcalString));
			InsereAssembly(I_JMP,Op1,NULL,NULL);//JMP value
			printf("JMP %d\n", convertString_to_label(funcalString));

			InsereAssembly(I_POP_R,NULL,NULL,NULL);//POP.R 
			printf("POP.R \n");
			Store_Global_Reg_Table_prevScope();
			Load_ALL_Mem_Table();
			
		break;
		case INTCODE_ADD:
			
			returnComponente(quad,1);
			Load_Operand(c,2);
			returnComponente(quad,2);
			Load_Operand(c,3);
			returnComponente(quad,3);
			if (c->type == TEMPORARIO){
				int reg_temp = returnFree_Temp();
				Op1 = AlocaOperand(REG,8, 2);
				Op2 = AlocaOperand(REG,8, 3);
				Op3 = AlocaOperand(REG,8, reg_temp);
				InsereAssembly(I_ADD,Op1,Op2,Op3);//ADD $2 $3 $temp
				printf("ADD $2 $3 $%d\n", reg_temp);
				tabela_registradores[2].flag_utilizado = 0;
				tabela_registradores[3].flag_utilizado = 0;
				tabela_registradores[reg_temp].flag_utilizado = 1;
				tabela_registradores[reg_temp].var = c->value;
			}
			
		break;
		case INTCODE_SUB:
			
			returnComponente(quad,1);
			Load_Operand(c,2);
			returnComponente(quad,2);
			Load_Operand(c,3);
			returnComponente(quad,3);
			if (c->type == TEMPORARIO){
				int reg_temp = returnFree_Temp();
				Op1 = AlocaOperand(REG,8, 2);
				Op2 = AlocaOperand(REG,8, 3);
				Op3 = AlocaOperand(REG,8, reg_temp);
				InsereAssembly(I_SUB,Op1,Op2,Op3);//SUB $2 $3 $temp
				printf("SUB $2 $3 $%d\n", reg_temp);
				tabela_registradores[2].flag_utilizado = 0;
				tabela_registradores[3].flag_utilizado = 0;
				tabela_registradores[reg_temp].flag_utilizado = 1;
				tabela_registradores[reg_temp].var = c->value;
			}
			
		break;
		case INTCODE_MUL:
			
			returnComponente(quad,1);
			Load_Operand(c,2);
			returnComponente(quad,2);
			Load_Operand(c,3);
			returnComponente(quad,3);
			if (c->type == TEMPORARIO){
				int reg_temp = returnFree_Temp();
				Op1 = AlocaOperand(REG,8, 2);
				Op2 = AlocaOperand(REG,8, 3);
				Op3 = AlocaOperand(REG,8, reg_temp);
				InsereAssembly(I_MUL,Op1,Op2,Op3);//MUL $2 $3 $temp
				printf("MUL $2 $3 $%d\n", reg_temp);
				tabela_registradores[2].flag_utilizado = 0;
				tabela_registradores[3].flag_utilizado = 0;
				tabela_registradores[reg_temp].flag_utilizado = 1;
				tabela_registradores[reg_temp].var = c->value;
			}
			
		break;
		case INTCODE_DIV:
			
			returnComponente(quad,1);
			Load_Operand(c,2);
			returnComponente(quad,2);
			Load_Operand(c,3);
			returnComponente(quad,3);
			if (c->type == TEMPORARIO){
				int reg_temp = returnFree_Temp();
				Op1 = AlocaOperand(REG,8, 2);
				Op2 = AlocaOperand(REG,8, 3);
				Op3 = AlocaOperand(REG,8, reg_temp);
				InsereAssembly(I_DIV,Op1,Op2,Op3);//DIV $2 $3 $temp
				printf("DIV $2 $3 $%d\n", reg_temp);
				tabela_registradores[2].flag_utilizado = 0;
				tabela_registradores[3].flag_utilizado = 0;
				tabela_registradores[reg_temp].flag_utilizado = 1;
				tabela_registradores[reg_temp].var = c->value;
			}
			
		break;
		case INTCODE_LT:
			
			returnComponente(quad,1);
			Load_Operand(c,2);
			returnComponente(quad,2);
			Load_Operand(c,3);
			code_int = code_int->next;
			
			Store_ALL_Reg_Table();
			quad = code_int->quad;
			returnComponente(quad,2);
			if (c->type == L_LABEL){
				Op1 = AlocaOperand(REG,8, 2);
				Op2 = AlocaOperand(REG,8, 3);
				Op3 = AlocaOperand(LAB,8, c->value);
				InsereAssembly(I_JPGE,Op1,Op2,Op3);//JPG $2 3 c->value
				printf("JPGE $2 $3 %d\n", c->value);
				tabela_registradores[2].flag_utilizado = 0;
				tabela_registradores[3].flag_utilizado = 0;
			}
			
		break;
		case INTCODE_LEQ:
			
			returnComponente(quad,1);
			Load_Operand(c,2);
			returnComponente(quad,2);
			Load_Operand(c,3);
			code_int = code_int->next;
			
			Store_ALL_Reg_Table();
			quad = code_int->quad;
			returnComponente(quad,2);
			if (c->type == L_LABEL){
				Op1 = AlocaOperand(REG,8, 2);
				Op2 = AlocaOperand(REG,8, 3);
				Op3 = AlocaOperand(LAB,8, c->value);
				InsereAssembly(I_JPG,Op1,Op2,Op3);//JPGE $2 3 c->value
				printf("JPG $2 $3 %d\n", c->value);
				tabela_registradores[2].flag_utilizado = 0;
				tabela_registradores[3].flag_utilizado = 0;
			}
			
		break;
		case INTCODE_GT:
			
			returnComponente(quad,1);
			Load_Operand(c,2);
			returnComponente(quad,2);
			Load_Operand(c,3);
			code_int = code_int->next;
			
			Store_ALL_Reg_Table();
			quad = code_int->quad;
			returnComponente(quad,2);
			if (c->type == L_LABEL){
				Op1 = AlocaOperand(REG,8, 2);
				Op2 = AlocaOperand(REG,8, 3);
				Op3 = AlocaOperand(LAB,8, c->value);
				InsereAssembly(I_JPLE,Op1,Op2,Op3);//JPL $2 3 c->value
				printf("JPLE $2 $3 %d\n", c->value);
				tabela_registradores[2].flag_utilizado = 0;
				tabela_registradores[3].flag_utilizado = 0;
			}
			
		break;
		case INTCODE_GEQ:
			
			returnComponente(quad,1);
			Load_Operand(c,2);
			returnComponente(quad,2);
			Load_Operand(c,3);
			code_int = code_int->next;
			
			Store_ALL_Reg_Table();
			quad = code_int->quad;
			returnComponente(quad,2);
			if (c->type == L_LABEL){
				Op1 = AlocaOperand(REG,8, 2);
				Op2 = AlocaOperand(REG,8, 3);
				Op3 = AlocaOperand(LAB,8, c->value);
				InsereAssembly(I_JPL,Op1,Op2,Op3);//JPLE $2 3 c->value
				printf("JPL $2 $3 %d\n", c->value);
				tabela_registradores[2].flag_utilizado = 0;
				tabela_registradores[3].flag_utilizado = 0;
			}
			
		break;
		case INTCODE_EQ:
			returnComponente(quad,1);
			Load_Operand(c,2);
			returnComponente(quad,2);
			Load_Operand(c,3);
			code_int = code_int->next;
			
			Store_ALL_Reg_Table();
			quad = code_int->quad;
			returnComponente(quad,2);
			if (c->type == L_LABEL){
				Op1 = AlocaOperand(REG,8, 2);
				Op2 = AlocaOperand(REG,8, 3);
				Op3 = AlocaOperand(LAB,8, c->value);
				InsereAssembly(I_JMPNE,Op1,Op2,Op3);//JMPNE $2 3 c->value
				printf("JMPNE $2 $3 %d\n", c->value);
				tabela_registradores[2].flag_utilizado = 0;
				tabela_registradores[3].flag_utilizado = 0;
			}
			
		break;
		case INTCODE_NEQ:
			returnComponente(quad,1);
			Load_Operand(c,2);
			returnComponente(quad,2);
			Load_Operand(c,3);
			code_int = code_int->next;
			
			Store_ALL_Reg_Table();
			quad = code_int->quad;
			returnComponente(quad,2);
			if (c->type == L_LABEL){
				Op1 = AlocaOperand(REG,8, 2);
				Op2 = AlocaOperand(REG,8, 3);
				Op3 = AlocaOperand(LAB,8, c->value);
				InsereAssembly(I_JPE,Op1,Op2,Op3);//JPE $2 3 c->value
				printf("JPE $2 $3 %d\n", c->value);
				tabela_registradores[2].flag_utilizado = 0;
				tabela_registradores[3].flag_utilizado = 0;
			}
			
		break;
		case INTCODE_ASSIGN:
			returnComponente(quad,2);
			Load_Operand(c,3);
			returnComponente(quad,1);
			Assign_Operand(c,3);
			
		break;
		case INTCODE_RET:
			if (quad.addr_01.kind != Vazio){
				returnComponente(quad,1);
				Load_Operand(c,0);
				
				Store_ALL_Reg_Table();
				Op1 = AlocaOperand(LAB,32, -1);
				InsereAssembly(I_JMP,Op1,NULL,NULL);//JMP c->value
				printf("JMP %d\n", -1);
				
			}else{
				Store_ALL_Reg_Table();
				Op1 = AlocaOperand(LAB,32, -1);
				InsereAssembly(I_JMP,Op1,NULL,NULL);//JMP c->value
				printf("JMP %d\n", -1);
				
			}
		break;
		case JMP:
			
			Store_ALL_Reg_Table();
			returnComponente(quad,1);
			if(c->type == L_LABEL){
				Op1 = AlocaOperand(LAB,32, c->value);
				Op2 = NULL;
				Op3 = NULL;
				InsereAssembly(I_JMP,Op1,Op2,Op3);//JMP c->value
				printf("JMP %d\n", c->value);
			}
			Load_ALL_Mem_Table();
			
		break;
		case LABEL:
			
			Store_ALL_Reg_Table();
			returnComponente(quad,1);
			if(c->type == L_LABEL){
				Op1 = AlocaOperand(LAB,32, c->value);
				Op2 = NULL;
				Op3 = NULL;
				InsereAssembly(I_LABEL,Op1,Op2,Op3);//LB c->value
				printf("LB %d\n", c->value);
			}
			Load_ALL_Mem_Table();
			
		break;
		case FUNCAL:
			
			Store_ALL_Reg_Table();
			Store_Global_Reg_Table_nextScope();
			Op1 = AlocaOperand(MEM,16, reserved_mem_total);
			InsereAssembly(I_PUSH_R,Op1,NULL,NULL);//PUSH.R reserved_mem_total
			printf("PUSH.R %d\n", reserved_mem_total);
			Op1 = AlocaOperand(MEM,8, contador+2);
			InsereAssembly(I_PUSH_PC,Op1,NULL,NULL);//PUSH.PC contador+2
			printf("PUSH.PC %d \n", contador+2, contador);
			returnComponente(quad,1);
			if(c->type == VARIAVEL){
				Op1 = AlocaOperand(LAB,32, convertString_to_label(c->var));
				InsereAssembly(I_JMP,Op1,NULL,NULL);//JMP value
				printf("JMP %d\n", convertString_to_label(c->var));
			}
			InsereAssembly(I_POP_R,NULL,NULL,NULL);//POP.R 
			printf("POP.R \n");
			Store_Global_Reg_Table_prevScope();
			Load_ALL_Mem_Table();
			
		break;
		}
		code_int = code_int->next;
	}
	Store_ALL_Reg_Table();
	Op1 = AlocaOperand(LAB,32, -1);
	InsereAssembly(I_JMP,Op1,NULL,NULL);//JMP c->value
	printf("JMP %d\n", -1);
	
	int flag_out_assembly = 0;
	tabela_memoria_parametro = NULL;
	reserved_mem_parametro = 0;
	parametro_contador = 0;
	
	code_int = codigo_inter;
	while(code_int->quad.op!=FUNDEF){//verificar se não tem algo antes Global
		code_int = code_int->next;
	}
	if(strcmp(code_int->quad.addr_01.contents.nome,"main")!=0){
		returnComponente(code_int->quad,1);
		//LABEL c->var
		Op1 = AlocaOperand(LAB,32, convertString_to_label(c->var));
		Op2 = NULL;
		Op3 = NULL;
		InsereAssembly(I_LABEL,Op1,Op2,Op3);//LB c->value
		printf("LB %d\n", convertString_to_label(c->var));
		
		Create_Mem_Table(c->var);
		Load_ALL_Mem_Table();
		//initial_load_to_reg();
		printf("NOVA FUNCAO - %s\n",code_int->quad.addr_01.contents.nome);
		code_int = code_int->next;
		
		while(flag_out_assembly == 0){
			Quad_Cell quad = code_int->quad;
			switch(quad.op){
			case FUNDEF:
				//RETURN 
				printf("NOVA FUNCAO - %s\n",code_int->quad.addr_01.contents.nome);
				Store_ALL_Reg_Table();
				InsereAssembly(I_POP_PC,NULL,NULL,NULL);//POP.PC 
				printf("POP.PC \n");
				//LABEL c->var
				returnComponente(quad,1);

				Op1 = AlocaOperand(LAB,32, convertString_to_label(c->var));
				Op2 = NULL;
				Op3 = NULL;
				InsereAssembly(I_LABEL,Op1,Op2,Op3);//LB c->value
				printf("LB %d\n", convertString_to_label(c->var));
				
				Create_Mem_Table(c->var);
				Load_ALL_Mem_Table();
				// initial_load_to_reg();
				
			break;
			case BEGIN_ARGS:
				
				code_int = Generate_Assembly_for_ARGS(code_int->next);
				//FUNCAL
				
				Store_ALL_Reg_Table();
				Store_Global_Reg_Table_nextScope();
				Op1 = AlocaOperand(MEM,16, reserved_mem_total);
				InsereAssembly(I_PUSH_R,Op1,NULL,NULL);//PUSH.R reserved_mem_total
				printf("PUSH.R %d\n", reserved_mem_total);
				Op1 = AlocaOperand(MEM,8, contador+2);
				InsereAssembly(I_PUSH_PC,Op1,NULL,NULL);//PUSH.PC contador+2
				printf("PUSH.PC %d \n", contador+2);

				Op1 = AlocaOperand(LAB,32, convertString_to_label(funcalString));
				InsereAssembly(I_JMP,Op1,NULL,NULL);//JMP value
				printf("JMP %d\n", convertString_to_label(funcalString));

				InsereAssembly(I_POP_R,NULL,NULL,NULL);//POP.R 
				printf("POP.R \n");
				Store_Global_Reg_Table_prevScope();
				Load_ALL_Mem_Table();
				
			break;
			case INTCODE_ADD:
				
				returnComponente(quad,1);
				Load_Operand(c,2);
				returnComponente(quad,2);
				Load_Operand(c,3);
				returnComponente(quad,3);
				if (c->type == TEMPORARIO){
					int reg_temp = returnFree_Temp();
					Op1 = AlocaOperand(REG,8, 2);
					Op2 = AlocaOperand(REG,8, 3);
					Op3 = AlocaOperand(REG,8, reg_temp);
					InsereAssembly(I_ADD,Op1,Op2,Op3);//ADD $2 $3 $temp
					printf("ADD $2 $3 $%d\n", reg_temp);
					tabela_registradores[2].flag_utilizado = 0;
					tabela_registradores[3].flag_utilizado = 0;
					tabela_registradores[reg_temp].flag_utilizado = 1;
					tabela_registradores[reg_temp].var = c->value;
				}
				
			break;
			case INTCODE_SUB:
				
				returnComponente(quad,1);
				Load_Operand(c,2);
				returnComponente(quad,2);
				Load_Operand(c,3);
				returnComponente(quad,3);
				if (c->type == TEMPORARIO){
					int reg_temp = returnFree_Temp();
					Op1 = AlocaOperand(REG,8, 2);
					Op2 = AlocaOperand(REG,8, 3);
					Op3 = AlocaOperand(REG,8, reg_temp);
					InsereAssembly(I_SUB,Op1,Op2,Op3);//SUB $2 $3 $temp
					printf("SUB $2 $3 $%d\n", reg_temp);
					tabela_registradores[2].flag_utilizado = 0;
					tabela_registradores[3].flag_utilizado = 0;
					tabela_registradores[reg_temp].flag_utilizado = 1;
					tabela_registradores[reg_temp].var = c->value;
				}
				
			break;
			case INTCODE_MUL:
				
				returnComponente(quad,1);
				Load_Operand(c,2);
				returnComponente(quad,2);
				Load_Operand(c,3);
				returnComponente(quad,3);
				if (c->type == TEMPORARIO){
					int reg_temp = returnFree_Temp();
					Op1 = AlocaOperand(REG,8, 2);
					Op2 = AlocaOperand(REG,8, 3);
					Op3 = AlocaOperand(REG,8, reg_temp);
					InsereAssembly(I_MUL,Op1,Op2,Op3);//MUL $2 $3 $temp
					printf("MUL $2 $3 $%d\n", reg_temp);
					tabela_registradores[2].flag_utilizado = 0;
					tabela_registradores[3].flag_utilizado = 0;
					tabela_registradores[reg_temp].flag_utilizado = 1;
					tabela_registradores[reg_temp].var = c->value;
				}
				
			break;
			case INTCODE_DIV:
				
				returnComponente(quad,1);
				Load_Operand(c,2);
				returnComponente(quad,2);
				Load_Operand(c,3);
				returnComponente(quad,3);
				if (c->type == TEMPORARIO){
					int reg_temp = returnFree_Temp();
					Op1 = AlocaOperand(REG,8, 2);
					Op2 = AlocaOperand(REG,8, 3);
					Op3 = AlocaOperand(REG,8, reg_temp);
					InsereAssembly(I_DIV,Op1,Op2,Op3);//DIV $2 $3 $temp
					printf("DIV $2 $3 $%d\n", reg_temp);
					tabela_registradores[2].flag_utilizado = 0;
					tabela_registradores[3].flag_utilizado = 0;
					tabela_registradores[reg_temp].flag_utilizado = 1;
					tabela_registradores[reg_temp].var = c->value;
				}
				
			break;
			case INTCODE_LT:
				
				returnComponente(quad,1);
				Load_Operand(c,2);
				returnComponente(quad,2);
				Load_Operand(c,3);
				code_int = code_int->next;
				
				Store_ALL_Reg_Table();
				quad = code_int->quad;
				returnComponente(quad,2);
				if (c->type == L_LABEL){
					Op1 = AlocaOperand(REG,8, 2);
					Op2 = AlocaOperand(REG,8, 3);
					Op3 = AlocaOperand(LAB,8, c->value);
					InsereAssembly(I_JPGE,Op1,Op2,Op3);//JPG $2 3 c->value
					printf("JPGE $2 $3 %d\n", c->value);
					tabela_registradores[2].flag_utilizado = 0;
					tabela_registradores[3].flag_utilizado = 0;
				}
				
			break;
			case INTCODE_LEQ:
				
				returnComponente(quad,1);
				Load_Operand(c,2);
				returnComponente(quad,2);
				Load_Operand(c,3);
				code_int = code_int->next;
				
				Store_ALL_Reg_Table();
				quad = code_int->quad;
				returnComponente(quad,2);
				if (c->type == L_LABEL){
					Op1 = AlocaOperand(REG,8, 2);
					Op2 = AlocaOperand(REG,8, 3);
					Op3 = AlocaOperand(LAB,8, c->value);
					InsereAssembly(I_JPG,Op1,Op2,Op3);//JPGE $2 3 c->value
					printf("JPG $2 $3 %d\n", c->value);
					tabela_registradores[2].flag_utilizado = 0;
					tabela_registradores[3].flag_utilizado = 0;
				}
				
			break;
			case INTCODE_GT:
				
				returnComponente(quad,1);
				Load_Operand(c,2);
				returnComponente(quad,2);
				Load_Operand(c,3);
				code_int = code_int->next;
				
				Store_ALL_Reg_Table();
				quad = code_int->quad;
				returnComponente(quad,2);
				if (c->type == L_LABEL){
					Op1 = AlocaOperand(REG,8, 2);
					Op2 = AlocaOperand(REG,8, 3);
					Op3 = AlocaOperand(LAB,8, c->value);
					InsereAssembly(I_JPLE,Op1,Op2,Op3);//JPL $2 3 c->value
					printf("JPLE $2 $3 %d\n", c->value);
					tabela_registradores[2].flag_utilizado = 0;
					tabela_registradores[3].flag_utilizado = 0;
				}
				
			break;
			case INTCODE_GEQ:
				
				returnComponente(quad,1);
				Load_Operand(c,2);
				returnComponente(quad,2);
				Load_Operand(c,3);
				code_int = code_int->next;
				
				Store_ALL_Reg_Table();
				quad = code_int->quad;
				returnComponente(quad,2);
				if (c->type == L_LABEL){
					Op1 = AlocaOperand(REG,8, 2);
					Op2 = AlocaOperand(REG,8, 3);
					Op3 = AlocaOperand(LAB,8, c->value);
					InsereAssembly(I_JPL,Op1,Op2,Op3);//JPLE $2 3 c->value
					printf("JPL $2 $3 %d\n", c->value);
					tabela_registradores[2].flag_utilizado = 0;
					tabela_registradores[3].flag_utilizado = 0;
				}
				
			break;
			case INTCODE_EQ:
				
				returnComponente(quad,1);
				Load_Operand(c,2);
				returnComponente(quad,2);
				Load_Operand(c,3);
				code_int = code_int->next;
				
				Store_ALL_Reg_Table();
				quad = code_int->quad;
				returnComponente(quad,2);
				if (c->type == L_LABEL){
					Op1 = AlocaOperand(REG,8, 2);
					Op2 = AlocaOperand(REG,8, 3);
					Op3 = AlocaOperand(LAB,8, c->value);
					InsereAssembly(I_JMPNE,Op1,Op2,Op3);//JMPNE $2 3 c->value
					printf("JMPNE $2 $3 %d\n", c->value);
					tabela_registradores[2].flag_utilizado = 0;
					tabela_registradores[3].flag_utilizado = 0;
				}
				
			break;
			case INTCODE_NEQ:
				
				returnComponente(quad,1);
				Load_Operand(c,2);
				returnComponente(quad,2);
				Load_Operand(c,3);
				code_int = code_int->next;
				
				Store_ALL_Reg_Table();
				quad = code_int->quad;
				returnComponente(quad,2);
				if (c->type == L_LABEL){
					Op1 = AlocaOperand(REG,8, 2);
					Op2 = AlocaOperand(REG,8, 3);
					Op3 = AlocaOperand(LAB,8, c->value);
					InsereAssembly(I_JPE,Op1,Op2,Op3);//JPE $2 3 c->value
					printf("JPE $2 $3 %d\n", c->value);
					tabela_registradores[2].flag_utilizado = 0;
					tabela_registradores[3].flag_utilizado = 0;
				}
			break;
			case INTCODE_ASSIGN:
				returnComponente(quad,2);
				Load_Operand(c,3);
				returnComponente(quad,1);
				
				Assign_Operand(c,3);
				
			break;
			case INTCODE_RET:
				if (quad.addr_01.kind != Vazio){
					returnComponente(quad,1);
					Load_Operand(c,0);
					
					Store_ALL_Reg_Table();
					InsereAssembly(I_POP_PC,NULL,NULL,NULL);//POP.PC 
					printf("POP.PC \n");
					
				}else{
					Store_ALL_Reg_Table();
					InsereAssembly(I_POP_PC,NULL,NULL,NULL);//POP.PC 
					printf("POP.PC \n");
					
				}
				
			break;
			case JMP:
				
				Store_ALL_Reg_Table();
				returnComponente(quad,1);
				if(c->type == L_LABEL){
					Op1 = AlocaOperand(LAB,32, c->value);
					Op2 = NULL;
					Op3 = NULL;
					InsereAssembly(I_JMP,Op1,Op2,Op3);//JMP c->value
					printf("JMP %d\n", c->value);
				}
				Load_ALL_Mem_Table();
				
			break;
			case LABEL:
				Store_ALL_Reg_Table();
				returnComponente(quad,1);
				if(c->type == L_LABEL){
					Op1 = AlocaOperand(LAB,32, c->value);
					Op2 = NULL;
					Op3 = NULL;
					InsereAssembly(I_LABEL,Op1,Op2,Op3);//LB c->value
					printf("LB %d\n", c->value);
				}
				Load_ALL_Mem_Table();
				
			break;
			case FUNCAL:
				
				Store_ALL_Reg_Table();
				Store_Global_Reg_Table_nextScope();
				Op1 = AlocaOperand(MEM,16, reserved_mem_total);
				InsereAssembly(I_PUSH_R,Op1,NULL,NULL);//PUSH.R reserved_mem_total
				printf("PUSH.R %d\n", reserved_mem_total);
				Op1 = AlocaOperand(MEM,8, contador+2);
				InsereAssembly(I_PUSH_PC,Op1,NULL,NULL);//PUSH.PC contador+2
				printf("PUSH.PC %d \n", contador+2);
				returnComponente(quad,1);
				if(c->type == VARIAVEL){
					Op1 = AlocaOperand(LAB,32, convertString_to_label(c->var));
					InsereAssembly(I_JMP,Op1,NULL,NULL);//JMP value
					printf("JMP %d\n", convertString_to_label(c->var));
				}

				InsereAssembly(I_POP_R,NULL,NULL,NULL);//POP.R 
				printf("POP.R \n");
				Store_Global_Reg_Table_prevScope();
				Load_ALL_Mem_Table();
				
			break;
			}
			code_int = code_int->next;
			if(code_int->quad.op == FUNDEF){
				returnComponente(code_int->quad,1);
				if(strcmp(c->var,"main")==0){
					flag_out_assembly = 1;
				}
			}
		}
		
	}
	Store_ALL_Reg_Table();

	InsereAssembly(I_POP_PC,NULL,NULL,NULL);//POP.PC 
	printf("POP.PC \n");

	Op1 = AlocaOperand(LAB,32, -1);
	InsereAssembly(I_LABEL,Op1,NULL,NULL);//LB 9999999
	printf("LB %d\n", -1);
	
	InsereAssembly(I_NOP,NULL,NULL,NULL);//NOP
	printf("NOP\n");
	
}

void Remove_Labels(){
	Assembly* p = Codigo_Maquina;
	int label;
	int line;
	while(p != NULL){
		if(p->opcode == I_LABEL){
			label = p->op1.value;
			line = RemoveAssembly(p->opcode,p->op1,p->op2,p->op3);
			// printf("PROCESSANDO LABEL: %d, LINE ASSEMBLY:%d\n", label ,line);
			Assembly* q = Codigo_Maquina;
			
			while(q != NULL){
				switch(q->opcode){
				case I_JMP:
					if(q->op1.type == LAB){
						if(q->op1.value == label){
							q->op1.type = MEM;
							q->op1.value = line;
							// printf("ACHOU JUMP COM LABEL:%d, substituido por linha %d\n", label, q->op1.value);
						}
					}
				break;
				case I_JPE:
				case I_JMPNE:
				case I_JPL:
				case I_JPLE:
				case I_JPG:
				case I_JPGE:
					if(q->op3.type == LAB){
						if(q->op3.value == label){
							q->op3.type = MEM;
							q->op3.value = line;
							// printf("ACHOU JUMP COM LABEL:%d, substituido por linha %d\n", label, q->op3.value);
						}
					}
				break;
				}
				q = q->next;
			}
		}
		p = p->next;
	}
}


FILE* arquivo_assembly = fopen("assembly.txt","w+");
FILE* arquivo_machine_code = fopen("CodigoMaquina.txt","w+");


void Escreve_Arquivo_Assembly(){
	Assembly* p = Codigo_Maquina;
	if(p!=NULL){
		if(p->opcode==I_NOP){
			p = p->next;
		}
	}
	while(p != NULL){
		switch(p->opcode){
		case I_NOP: fprintf(arquivo_assembly,"NOP ");	break;
		case I_JMP:  fprintf(arquivo_assembly,"JMP ");	break;
		case I_JPE: fprintf(arquivo_assembly,"JPE ");	break;
		case I_JMPNE: fprintf(arquivo_assembly,"JMPNE ");	break;
		case I_JPL: fprintf(arquivo_assembly,"JPL ");	break;
		case I_JPG: fprintf(arquivo_assembly,"JPG ");	break;
		case I_JPLE: fprintf(arquivo_assembly,"JPLE ");	break;
		case I_JPGE: fprintf(arquivo_assembly,"JPGE ");	break;
		case I_SRVALUE: fprintf(arquivo_assembly,"SRVALUE ");	break;
		case I_LOAD: fprintf(arquivo_assembly,"LOAD ");	break;
		case I_STORE: fprintf(arquivo_assembly,"STORE ");	break;
		case I_REGCOPY: fprintf(arquivo_assembly,"REGCOPY ");	break;
		case I_ADD: fprintf(arquivo_assembly,"ADD ");	break;
		case I_SUB: fprintf(arquivo_assembly,"SUB ");	break;
		case I_MUL: fprintf(arquivo_assembly,"MUL ");	break;
		case I_DIV: fprintf(arquivo_assembly,"DIV ");	break;
		case I_SHR: fprintf(arquivo_assembly,"SHR ");	break;
		case I_SHL: fprintf(arquivo_assembly,"SHL ");	break;
		case I_PUSH_R: fprintf(arquivo_assembly,"PUSH_R ");	break;
		case I_POP_R: fprintf(arquivo_assembly,"POP_R ");	break;
		case I_PUSH_PC: fprintf(arquivo_assembly,"PUSH_PC ");	break;
		case I_POP_PC: fprintf(arquivo_assembly,"POP_PC ");	break;
		case I_LABEL: fprintf(arquivo_assembly,"LABEL ");	break;
		}
		switch(p->op1.type){
		case REG: 
			fprintf(arquivo_assembly,"$%d ",p->op1.value);
		break;
		case NUM:
		case NADA:
			fprintf(arquivo_assembly," ");
		break;
		case MEM:
		case LAB: 
			fprintf(arquivo_assembly,"%d ",p->op1.value);
		break;
		}
		switch(p->op2.type){
		case REG: 
			fprintf(arquivo_assembly,"$%d ",p->op2.value);
		break;
		case NUM:
		case NADA:
			fprintf(arquivo_assembly," ");
		break;
		case MEM:
		case LAB: 
			fprintf(arquivo_assembly,"%d ",p->op2.value);

		break;
		}
		switch(p->op3.type){
		case REG: 
			fprintf(arquivo_assembly,"$%d ",p->op3.value);
		break;
		case NUM:
		case NADA:
			fprintf(arquivo_assembly," ");
		break;
		case MEM:
		case LAB: 
			fprintf(arquivo_assembly,"%d ",p->op3.value);

		break;
		}
		fprintf(arquivo_assembly,"\n");
		p = p->next;
	}
	
}

void Generate_Machine_code(){
	Assembly* p = Codigo_Maquina;
	int tamanho = 0;
	int value;
	int binario[8];
	int aux_binario[16];
	int j;
	if(p!=NULL){
		if(p->opcode==I_NOP){
			p = p->next;
		}
	}
	while(p != NULL){
		fprintf(arquivo_machine_code,"I_mem[%d] = {8'b",p->line);
		//VERIFICA O TIPO
		switch(p->opcode){
		case I_NOP: fprintf(arquivo_machine_code,"00");	break;
		case I_JMP:  fprintf(arquivo_machine_code,"00");	break;
		case I_JPE: fprintf(arquivo_machine_code,"00");	break;
		case I_JMPNE: fprintf(arquivo_machine_code,"00");	break;
		case I_JPL: fprintf(arquivo_machine_code,"00");	break;
		case I_JPG: fprintf(arquivo_machine_code,"00");	break;
		case I_JPLE: fprintf(arquivo_machine_code,"00");	break;
		case I_JPGE: fprintf(arquivo_machine_code,"00");	break;
		case I_SRVALUE: fprintf(arquivo_machine_code,"01");	break;
		case I_LOAD: fprintf(arquivo_machine_code,"01");	break;
		case I_STORE: fprintf(arquivo_machine_code,"01");	break;
		case I_REGCOPY: fprintf(arquivo_machine_code,"01");	break;
		case I_ADD: fprintf(arquivo_machine_code,"10");	break;
		case I_SUB: fprintf(arquivo_machine_code,"10");	break;
		case I_MUL: fprintf(arquivo_machine_code,"10");	break;
		case I_DIV: fprintf(arquivo_machine_code,"10");	break;
		case I_SHR: fprintf(arquivo_machine_code,"10");	break;
		case I_SHL: fprintf(arquivo_machine_code,"10");	break;
		case I_PUSH_R: fprintf(arquivo_machine_code,"11");	break;
		case I_POP_R: fprintf(arquivo_machine_code,"11");	break;
		case I_PUSH_PC: fprintf(arquivo_machine_code,"11");	break;
		case I_POP_PC: fprintf(arquivo_machine_code,"11");	break;
		}
		//VERIFICA O MODO
		switch(p->opcode){
		case I_LOAD:
		case I_STORE:
		if(p->op1.type == REG) {
			if(p->op2.type == REG){
				fprintf(arquivo_machine_code,"11");
			}else{
				fprintf(arquivo_machine_code,"00");
			}			
		}else{
			fprintf(arquivo_machine_code,"00");
		}
		break;
		case I_NOP:
		case I_JMP:
		case I_SRVALUE:
		case I_REGCOPY: 
		case I_PUSH_R:
		case I_POP_R: 
		case I_PUSH_PC: 
		case I_POP_PC: 
			fprintf(arquivo_machine_code,"00");
		break;
		case I_ADD: 
		case I_SUB:
		case I_MUL: 
		case I_DIV: 
		case I_SHR: 
		case I_SHL: 
		case I_JPE: 
		case I_JMPNE: 
		case I_JPL: 
		case I_JPG: 
		case I_JPLE: 
		case I_JPGE: 
			if(p->op1.type == MEM) {
				fprintf(arquivo_machine_code,"1");
			}else{
				fprintf(arquivo_machine_code,"0");
			}
			if(p->op2.type == MEM){
				fprintf(arquivo_machine_code,"1");
			}else{
				fprintf(arquivo_machine_code,"0");
			}
		break;
		}
		//VERIFICA O OPCODE
		switch(p->opcode){
		case I_NOP: fprintf(arquivo_machine_code,"0000,");	break;
		case I_JMP:  fprintf(arquivo_machine_code,"0001,");	break;
		case I_JPE: fprintf(arquivo_machine_code,"0010,");	break;
		case I_JMPNE: fprintf(arquivo_machine_code,"0011,");	break;
		case I_JPL: fprintf(arquivo_machine_code,"0100,");	break;
		case I_JPG: fprintf(arquivo_machine_code,"0101,");	break;
		case I_JPLE: fprintf(arquivo_machine_code,"0110,");	break;
		case I_JPGE: fprintf(arquivo_machine_code,"0111,");	break;
		case I_SRVALUE: fprintf(arquivo_machine_code,"0000,");	break;
		case I_LOAD: fprintf(arquivo_machine_code,"0001,");	break;
		case I_STORE: fprintf(arquivo_machine_code,"0010,");	break;
		case I_REGCOPY: fprintf(arquivo_machine_code,"0011,");	break;
		case I_ADD: fprintf(arquivo_machine_code,"0101,");	break;
		case I_SUB: fprintf(arquivo_machine_code,"0110,");	break;
		case I_MUL: fprintf(arquivo_machine_code,"0111,");	break;
		case I_DIV: fprintf(arquivo_machine_code,"1000,");	break;
		case I_SHR: fprintf(arquivo_machine_code,"1001,");	break;
		case I_SHL: fprintf(arquivo_machine_code,"1010,");	break;
		case I_PUSH_R: fprintf(arquivo_machine_code,"0001,");	break;
		case I_POP_R: fprintf(arquivo_machine_code,"0010,");	break;
		case I_PUSH_PC: fprintf(arquivo_machine_code,"0011,");	break;
		case I_POP_PC: fprintf(arquivo_machine_code,"0100,");	break;
		}
		//verifica operandos
		switch(p->opcode){
		case I_POP_R:
		case I_POP_PC: 
		case I_NOP: 
		fprintf(arquivo_machine_code,"32'd0}");	
		break;
		case I_JMP:  
			fprintf(arquivo_machine_code,"16'd0,16'd%d}",p->op1.value);
		break;
		case I_PUSH_R: 
			fprintf(arquivo_machine_code,"16'd%d,16'd0}",p->op1.value);
		break;
		case I_PUSH_PC: 
			fprintf(arquivo_machine_code,"16'd%d,16'd0}",p->op1.value);
		break;
		case I_JPE: 
		case I_JMPNE: 
		case I_JPL: 
		case I_JPG: 
		case I_JPLE: 
		case I_JPGE:
			fprintf(arquivo_machine_code,"8'd%d,8'd%d,16'd%d}",p->op1.value,p->op2.value,p->op3.value);
		break;
		case I_ADD: 
		case I_SUB: 
		case I_MUL: 
		case I_DIV: 
		case I_SHR: 
		case I_SHL:
			//op1
			fprintf(arquivo_machine_code,"8'd%d,8'd%d,8'd%d,8'd0}",p->op1.value,p->op2.value,p->op3.value);
		break;
		case I_SRVALUE: 
			//op1
			fprintf(arquivo_machine_code,"16'd%d,8'd%d,8'd0}",p->op1.value,p->op2.value);
		break;
		case I_REGCOPY: 
			fprintf(arquivo_machine_code,"8'd%d,8'd0,8'd%d,8'd0}",p->op1.value,p->op2.value);
		break;
		case I_LOAD: 
			//op1
			fprintf(arquivo_machine_code,"16'd%d,8'd%d,8'd0}",p->op1.value,p->op2.value);
		break;
		case I_STORE: 
			if(p->op2.type == REG){
				fprintf(arquivo_machine_code,"8'd%d,8'd%d,8'd0,8'd0}",p->op1.value,p->op2.value);
			}else{
				fprintf(arquivo_machine_code,"8'd%d,16'd%d,8'd0}",p->op1.value,p->op2.value);
			}
		break;
		}
		fprintf(arquivo_machine_code,";\n");
		tamanho++;
		p = p->next;
	}
	fprintf(arquivo_machine_code,"limit_PC = %d;\n",tamanho);
}


void Gen_Ass(){
	Generate_Assembly();
	 Remove_Labels();
	 printf("*******************************************************\n");
	 Escreve_Arquivo_Assembly();
	 fclose(arquivo_assembly);
	 Generate_Machine_code();
	 fclose(arquivo_machine_code);
}

void SymTabGen() {
	TabGen_verify_main(savedTree);//verifica se existe uma main

	TabGen(savedTree);//todo o resto da analise semantica
	if(CompileSteps) printf("\n\n/*************TERMINOU TABGEN()**********/\n\n");
	
	TabGen_verify(savedTree);//verifica se vc esta operando IDs de tipos iguais
	if(CompileSteps) printf("\n\n/*************TERMINOU TabGen_verify()**********/\n\n");

	
	int i;
	for(i = 0;i<211;i++){
		if(&HashVec[i] != NULL) changeTable_scope(i);
	}
	if(CompileSteps) printf("\n\n/*************TERMINOU changeTable_scope()**********/\n\n");
	for(i = 0;i<211;i++){
		if(&HashVec[i] != NULL) changeTable_merge(i);
	}
	if(CompileSteps) printf("\n\n/*************TERMINOU changeTable_merge()**********/\n\n");
	
	// rodar mais uma vez, pq bruteforce é o que há!!!
	for(i = 0;i<211;i++){
		if(&HashVec[i] != NULL) changeTable_merge(i);
	}
	if(CompileSteps) printf("\n\n/*************TERMINOU changeTable_merge BRUTEFORCE()**********/\n\n");
	
	printTable();
	/*****/
	if(CompileSteps) printf("\n\n/*************TERMINOU printTable()**********/\n\n");
	fclose(listing);
	 if (semantical_error == 0){
		 generateIntermCode();
		 if(CompileSteps) printf("\n\n/*************TERMINOU generateIntermCode()**********/\n\n");
	 }
	 if (semantical_error == 0) {
		 Gen_Ass();
		 if(CompileSteps) printf("\n\n/*************TERMINOU Gen_Ass()**********/\n\n");
	 }
}
