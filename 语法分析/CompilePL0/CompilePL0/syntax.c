///////////
//syntax 语法分析
//1.添加了 block() constdeclaration() vardeclaration() enter() position() statement().. gen() test()
//2.修改了err_msg[]  宏定义（便于test()） 
//3 项目-属性-C/C++预处理器添加_CRT_SECURE_NO_WARNINGS  解决C4996 _s问题
//4.修改了 13061049_test不符合语法的部分
//@TODO
//kuro1.com
//github.com/CsterKuroi/Compile
//modified by kuro1 on 2015.11.22 
//////////

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

#define norw        14             // 保留字14个
#define txmax       100            // 符号表长度
#define nmax        14             // 数字位数
#define al          10             // 标识符长度
#define amax        2047           // 数字最大（addr）
#define levmax      3              // 嵌套层数
#define cxmax       200            // code[]长度
//symbol 32+1
#define elsesym     0x1
#define ident       0x2
#define number      0x4
#define plus        0x8
#define minus       0x10
#define times       0x20
#define slash       0x40
#define oddsym      0x80
#define eql         0x100
#define neq         0x200
#define lss         0x400
#define leq         0x800
#define gtr         0x1000
#define geq         0x2000
#define lparen      0x4000
#define rparen      0x8000
#define comma       0x10000
#define semicolon   0x20000
#define period      0x40000
#define becomes     0x80000
#define beginsym    0x100000
#define endsym      0x200000
#define ifsym       0x400000
#define thensym     0x800000
#define whilesym    0x1000000
#define dosym       0x2000000
#define callsym     0x4000000
#define constsym    0x8000000
#define varsym      0x10000000
#define procsym     0x20000000
#define readsym     0x40000000
#define writesym    0x80000000
#define nul         0x100000000 //0

enum object
{
	constant, variable, proc
};//符号表对象kind
enum fct
{
	lit, opr, lod, sto, cal, Int, jmp, jpc
};//TODO red wrt
typedef struct
{
	enum fct f;
	long l;
	long a;
} instruction;
char* err_msg[] =
{
	"错误0：",
	"错误1：需要’=’而不是’:=’！",
	"错误2：需要数字！",
	"错误3：需要等号/赋值号！",
	"错误4：需要标识符！",
	"错误5：需要分号’;’！",
	"错误6：过程说明末尾出现非法字符",
	"错误7：",
	"错误8：分程序结尾有非法字符",
	"错误9：需要句号’.’",
	"错误10：需要分号’;’！",
	"错误11：未定义的标识符！",
	"错误12：标识符不是变量！",
	"错误13：需要赋值号’:=’！",
	"错误14：call后跟的不是标识符！",
	"错误15：call后跟的不是过程名！",
	"错误16：if后没有then！",
	"错误17：需要end",
	"错误18：需要do",
	"错误19：语句末尾出现非法字符",
	"错误20：缺少二元逻辑运算符！",
	"错误21：错误使用标识符，标识符是过程名！",
	"错误22：需要右括号’)’！",
	"错误23：因子之间应该为'*'或'/'",
	"错误24：因子开头应该为标识符/数字/左括号",
	"错误25：",
	"错误26：",
	"错误27：",
	"错误28：",
	"错误29：",
	"错误30：数字太大！",
	"错误31：数字位数太长！",
	"错误32：嵌套层数大于最大允许的套层数！",
	"错误33：",
	"错误34：",
	"错误35：read()中应是声明过的变量名！",
	"错误36：read语句的标识符应该为变量！",
	"错误37：",
	"错误38：",
	"错误39：code[]过长",
	"错误40：需要左括号’(’"
};//TODO
char infilename[80];
FILE* infile;
char ch;
unsigned long sym;
char id[al + 1];
long num;
long cc;
long ll;
long kk,err;
long cx;
char line[81];
char a[al + 1];
instruction code[cxmax + 1];
char word[norw][al + 1];
unsigned long wsym[norw];
unsigned long ssym[256];
char mnemonic[8][3 + 1];
unsigned long declbegsys, statbegsys, facbegsys;
struct
{
	char name[al + 1];
	enum object kind;
	long val;
	long level;
	long addr;
}table[txmax + 1];
long dx;		// 数据段内存分配指针
long lev;		// 层次
long tx;		// 符号表位置
#define stacksize 500
long s[stacksize];

void error(long n) //错误处理
{
	printf("error=>");
	for (int i = 1; i <= cc - 1; i++)
	{
		printf(" ");
	}
	printf("|%s(%d)\n", err_msg[n], n);
	err++;
}//error1

void getch() //取字符
{
	if (cc == ll)
	{
		if (feof(infile))
		{
			printf("***************\n");
			printf("    end of file\n");
			printf("***************\n");
			error(0);
			exit(1);
		}
		ll = 0;
		cc = 0;
		while ((!feof(infile)) && ((ch = getc(infile)) != '\n')&& (ch != -1))
		{
			printf("%c", ch);
			line[++ll] = ch;
		}
		printf("\n");
		line[++ll] = ' ';
	}
	ch = line[++cc];
}//getchar1

void getsym() //取单词
{
	int i, j, k;
	while (ch == ' ' || ch == '\t')//空格TAB
	{
		getch();
	}
	if (isalpha(ch)) 	//如果是字母
	{
		k = 0;
		do
		{
			if (k < al)
			{
				a[k] = ch;
				k = k + 1;
			}
			getch();
		} while (isalpha(ch) || isdigit(ch));
		if (k >= kk)
		{
			kk = k;
		}
		else
		{
			do
			{
				kk = kk - 1;
				a[kk] = ' ';
			} while (k < kk);
		}
		strcpy(id, a);
		i = 0;
		j = norw - 1;
		do
		{
			k = (i + j) / 2;
			if (strcmp(id, word[k]) == 0) break;
			else if (strcmp(id, word[k])<0)
			{
				j = k - 1;
			}
			else if (strcmp(id, word[k])>0)
			{
				i = k + 1;
			}
		} while (i <= j);
		if (i>j)
		{
			sym = ident;
		}
		else
		{
			sym = wsym[k];
		}
	}
	else if (isdigit(ch)) //如果是数字
	{
		k = 0;
		num = 0;
		sym = number;
		do
		{
			num = num * 10 + (ch - '0');
			k++;
			getch();
		} while (isdigit(ch));
		if (k > nmax)
		{
			error(31);
		}
	}
	else if (ch == ':')//如果是冒号
	{
		getch();
		if (ch == '=')
		{
			sym = becomes;
			getch();
		}
		else
		{
			sym = nul;
		}
	}
	else if (ch == '>')//大于
	{
		getch();
		if (ch == '=')
		{
			sym = geq;
			getch();
		}
		else
		{
			sym = gtr;
		}
	}
	else if (ch == '<')//小于
	{
		getch();
		if (ch == '=')
		{
			sym = leq;
			getch();
		}
		else if (ch == '>')
		{
			sym = neq;
			getch();
		}
		else
		{
			sym = lss;
		}
	}
	else//其他字符
	{
		sym = ssym[(unsigned char)ch];
		getch();
	}
}//getsym1

void gen(enum fct x, long y, long z) //code生成
{
	if (cx > cxmax)
	{
		error(39);
		exit(1);
	}
	code[cx].f = x;
	code[cx].l = y;
	code[cx].a = z;
	cx++;
}//gen1

void test(unsigned long s1, unsigned long s2, long n) //单词合法性测试
{
	if (!(sym & s1))
	{
		error(n);
		s1 = s1 | s2;
		while (!(sym & s1))
		{
			getsym();
		}
	}
}//test1

void enter(enum object k) //登记符号表
{
	tx++;
	strcpy(table[tx].name, id);
	table[tx].kind = k;
	switch (k)
	{
		case constant:
			if (num > amax)
			{
				error(30);
				num = 0;
			}
			table[tx].val = num;
			break;
		case variable:
			table[tx].level = lev;
			table[tx].addr = dx;
			dx++;
			break;
		case proc:
			table[tx].level = lev;
			break;
	}
}//enter1

long position(char* id) //查找符号表
{
	long i;
	strcpy(table[0].name, id);
	i = tx;
	while (strcmp(table[i].name, id) != 0)
	{
		i--;
	}
	return i;
}//pos1

void constdeclaration() //常量定义
{
	if (sym == ident)
	{
		getsym();
		if (sym == eql || sym == becomes)
		{
			if (sym == becomes)
			{
				error(1);
			}
			getsym();
			if (sym == number)
			{
				enter(constant);
				getsym();
			}
			else
			{
				error(2);
			}
		}
		else
		{
			error(3);
		}
	}
	else
	{
		error(4);
	}
}//con1

void vardeclaration() //变量定义
{
	if (sym == ident)
	{
		enter(variable);
		getsym();
	}
	else
	{
		error(4);
	}
}//var1

void expression(unsigned long);

void factor(unsigned long fsys) //因子
{
	long i;
	test(facbegsys, fsys, 24);
	while (sym & facbegsys)
	{
		if (sym == ident)
		{
			i = position(id);
			if (i == 0)
			{
				error(11);
			}
			else
			{
				switch (table[i].kind)
				{
					case constant:
						gen(lit, 0, table[i].val);//如果这个标识符对应的是常量，值为val，生成lit指令，把val放到栈顶
						break;
					case variable:
						gen(lod, lev - table[i].level, table[i].addr); //TODO 如果标识符是变量名，生成lod指令，把位于距离当前层level的层的偏移地址为adr的变量放到栈顶
						break;
					case proc:
						error(21);
						break;
				}
			}
			getsym();
		}
		else if (sym == number)
		{
			if (num>amax)
			{
				error(30);
				num = 0;
			}
			gen(lit, 0, num);
			getsym();
		}
		else if (sym == lparen)
		{
			getsym();
			expression(rparen | fsys);//递归调用expression
			if (sym == rparen)
			{
				getsym();
			}
			else
			{
				error(22);
			}
		}
		//test(fsys, lparen, 23);
	}
}//fac1

void term(unsigned long fsys) //项
{
	unsigned long mulop;
	factor(fsys | times | slash);
	while (sym == times || sym == slash)
	{
		mulop = sym;
		getsym();
		factor(fsys | times | slash);
		if (mulop == times)
		{
			gen(opr, 0, 4);
		}
		else
		{
			gen(opr, 0, 5);
		}
	}
}//term1

void expression(unsigned long fsys) //表达式
{
	unsigned long addop;
	if (sym == plus || sym == minus)
	{
		addop = sym;
		getsym();
		term(fsys | plus | minus);
		if (addop == minus)
		{
			gen(opr, 0, 1);
		}
	}
	else
	{
		term(fsys | plus | minus);
	}
	while (sym == plus || sym == minus)
	{
		addop = sym;
		getsym();
		term(fsys | plus | minus);
		if (addop == plus)
		{
			gen(opr, 0, 2);
		}
		else
		{
			gen(opr, 0, 3);
		}
	}
}//exp1

void condition(unsigned long fsys) //条件处理
{
	unsigned long relop;
	if (sym == oddsym)
	{
		getsym();
		expression(fsys);
		gen(opr, 0, 6);
	}
	else
	{
		expression(fsys | eql | neq | lss | gtr | leq | geq);
		if (!(sym&(eql | neq | lss | gtr | leq | geq)))
		{
			error(20);
		}
		else
		{
			relop = sym;
			getsym();
			expression(fsys);
			switch (relop)
			{
				case eql:
					gen(opr, 0, 8);
					break;
				case neq:
					gen(opr, 0, 9);
					break;
				case lss:
					gen(opr, 0, 10);
					break;
				case geq:
					gen(opr, 0, 11);
					break;
				case gtr:
					gen(opr, 0, 12);
					break;
				case leq:
					gen(opr, 0, 13);
					break;
			}
		}
	}
}//con

void statement(unsigned long fsys) //语句
{
	long i, cx1, cx2;
	if (sym == ident)//赋值语句
	{
		i = position(id);
		if (i == 0)
		{
			error(11);
		}
		else if (table[i].kind != variable)
		{
			error(12);
			i = 0;
		}
		getsym();
		if (sym == becomes)
		{
			getsym();
		}
		else
		{
			error(13);
		}
		printf("<赋值语句>\n");
		expression(fsys);
		if (i != 0)
		{
			gen(sto, lev - table[i].level, table[i].addr);
		}
	}
	else if (sym == callsym)//过程调用
	{
		getsym();
		if (sym != ident)
		{
			error(14);
		}
		else
		{
			i = position(id);
			if (i == 0)
			{
				error(11);
			}
			else if (table[i].kind == proc)
			{
				printf("<过程调用语句>\n");
				gen(cal, lev - table[i].level, table[i].addr);
			}
			else
			{
				error(15);
			}
			getsym();
		}
	}
	else if (sym == ifsym)//条件语句
	{
		printf("<条件语句>\n");
		getsym();
		condition(fsys | thensym | dosym);
		if (sym == thensym)
		{
			getsym();
		}
		else
		{
			error(16);
		}
		cx1 = cx;
		gen(jpc, 0, 0);
		statement(fsys);
		code[cx1].a = cx;
		if (sym == elsesym)
		{
			getsym();
			statement(fsys);
		}//TODO 2		
	}
	else if (sym == beginsym)//复合语句
	{
		printf("<复合语句>\n");
		getsym();
		statement(fsys | semicolon | endsym);
		while (sym == semicolon || (sym&statbegsys))
		{
			if (sym == semicolon)
			{
				getsym();
			}
			else
			{
				error(10);
			}
			statement(fsys | semicolon | endsym);
		}
		if (sym == endsym)
		{
			getsym();
		}
		else
		{
			error(17);
		}
	}
	else if (sym == whilesym)//while循环
	{
		cx1 = cx;
		printf("<当循环语句>\n");
		getsym();
		condition(fsys | dosym);
		cx2 = cx;
		gen(jpc, 0, 0);
		if (sym == dosym)
		{
			getsym();
		}
		else
		{
			error(18);
		}
		statement(fsys);
		gen(jmp, 0, cx1);
		code[cx2].a = cx;
	}
	else if (sym == readsym)//read语句
	{
		getsym();
		if (sym != lparen)
		{
			error(40);
		}
		else
		{
			do {
				getsym();
				if (sym == ident)
				{
					i = position(id);
				}
				else
				{
					i = 0;
				}
				if (i == 0)
				{
					error(35);
				}
				else if (table[i].kind != variable)
				{
					error(36);
				}
				else
				{
					gen(opr, 0, 16); //TODO
					gen(sto, lev - table[i].level, table[i].addr);
				}
				getsym();
			} while (sym == comma); 
		}
		if (sym != rparen)
		{
			error(22);
		}
		else
		{
			getsym();
		}
		printf("<读语句>\n");
	}
	else if (sym == writesym)//write语句
	{
		getsym();
		if (sym != lparen)
		{
			error(40);
		}
		else
		{
			do {
				getsym();
				expression(fsys); 
				gen(opr, 0, 14);
			} while (sym == comma);
			if (sym != rparen)
			{
				error(22);//缺少右括号
			}
			else
			{
				printf("<写语句>\n");
				getsym();
			}
		}
		gen(opr, 0, 15);//换行符
	}
	else
		printf("<空语句>\n");
	test(fsys, 0, 19);
}//state1

void block(unsigned long fsys) //程序块
{
	long tx0;		// 层初始符号表指针
	long cx0; 		// 层初始code指针
	long tx1;		// 调用前保留现场
	long dx1;
	dx = 3;
	tx0 = tx;
	table[tx].addr = cx;
	gen(jmp, 0, 0);
	if (lev>levmax)
	{
		error(32);
	}
	do
	{
		if (sym == constsym)
		{
			getsym();
			constdeclaration();
			while (sym == comma)
			{
				getsym();
				constdeclaration();
			}
			if (sym == semicolon)
			{
				printf("<常量定义>\n");
				getsym();
			}
			else
			{
				error(5);
			}
		}
		if (sym == varsym)
		{
			getsym();
			vardeclaration();
			while (sym == comma)
			{
				getsym();
				vardeclaration();
			}
			if (sym == semicolon)
			{
				printf("<变量定义>\n");
				getsym();
			}
			else
			{
				error(5);
			}
		}

		while (sym == procsym)
		{
			getsym();
			if (sym == ident)
			{
				enter(proc);
				getsym();
			}
			else
			{
				error(4);
			}
			if (sym == semicolon)
			{
				printf("<过程首部>\n");
				getsym();
			}
			else
			{
				error(5);
			}
			lev = lev + 1;
			tx1 = tx;
			dx1 = dx;
			block(fsys | semicolon);
			lev = lev - 1;
			tx = tx1;
			dx = dx1;
			if (sym == semicolon)
			{
				printf("<过程说明>\n");
				getsym();
				test(statbegsys | ident | procsym, fsys, 6);
			}
			else
			{
				error(5);
			}
		}
		test(beginsym, declbegsys|ident|statbegsys, 7);//复合语句开头
	} while (sym&declbegsys);
	code[table[tx0].addr].a = cx;
	table[tx0].addr = cx;
	cx0 = cx;
	gen(Int, 0, dx);
	statement(fsys | semicolon | endsym);
	gen(opr, 0, 0); // return
	test(fsys, 0, 8);
//	listcode(cx0);
}

int main()
{
	for (int i = 0; i<256; i++)
	{
		ssym[i] = nul;
	}
	ssym['+'] = plus;
	ssym['-'] = minus;
	ssym['*'] = times;
	ssym['/'] = slash;
	ssym['('] = lparen;
	ssym[')'] = rparen;
	ssym['='] = eql;
	ssym[','] = comma;
	ssym['.'] = period;
	ssym[';'] = semicolon;

	strcpy(word[0], "begin     ");
	strcpy(word[1], "call      ");
	strcpy(word[2], "const     ");
	strcpy(word[3], "do        ");
	strcpy(word[4], "else      ");
	strcpy(word[5], "end       ");
	strcpy(word[6], "if        ");
	strcpy(word[7], "odd       ");
	strcpy(word[8], "procedure ");
	strcpy(word[9], "read      ");
	strcpy(word[10], "then      ");
	strcpy(word[11], "var       ");
	strcpy(word[12], "while     ");
	strcpy(word[13], "write     ");

	wsym[0] = beginsym;
	wsym[1] = callsym;
	wsym[2] = constsym;
	wsym[3] = dosym;
	wsym[4] = elsesym;
	wsym[5] = endsym;
	wsym[6] = ifsym;
	wsym[7] = oddsym;
	wsym[8] = procsym;
	wsym[9] = readsym;
	wsym[10] = thensym;
	wsym[11] = varsym;
	wsym[12] = whilesym;
	wsym[13] = writesym;

	strcpy(mnemonic[lit], "LIT");
	strcpy(mnemonic[opr], "OPR");
	strcpy(mnemonic[lod], "LOD");
	strcpy(mnemonic[sto], "STO");
	strcpy(mnemonic[cal], "CAL");
	strcpy(mnemonic[Int], "INT");
	strcpy(mnemonic[jmp], "JMP");
	strcpy(mnemonic[jpc], "JPC");

	declbegsys = constsym | varsym | procsym;
	statbegsys = beginsym | callsym | ifsym | whilesym| elsesym;
	facbegsys = ident | number | lparen;

	if ((infile = fopen("13061049_test.txt", "r")) == NULL)
	{
		printf("File %s can't be opened.\n", infilename);
		exit(1);
	}
	err = 0;
	cc = 0;
	cx = 0;
	ll = 0;
	ch = ' ';
	kk = al;
	getsym();
	lev = 0;
	tx = 0;
	block(declbegsys | statbegsys | period);
	if (sym != period)
	{
		error(9);
	}
	printf("<程序结束.>\n");
	if (err == 0)
	{
		// interpret();
	}
	else
	{
		printf("%d errors in pro\n",err);
	}
	fclose(infile);
	return 0;
}