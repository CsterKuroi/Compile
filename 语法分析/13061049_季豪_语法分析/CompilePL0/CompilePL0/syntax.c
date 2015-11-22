///////////
//syntax �﷨����
//1.����� block() constdeclaration() vardeclaration() enter() position() statement().. gen() test()
//2.�޸���err_msg[]  �궨�壨����test()�� 
//3 ��Ŀ-����-C/C++Ԥ���������_CRT_SECURE_NO_WARNINGS  ���C4996 _s����
//4.�޸��� 13061049_test�������﷨�Ĳ���
//@TODO
//kuro1.com
//github.com/CsterKuroi/Compile
//modified by kuro1 on 2015.11.22 
//////////

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

#define norw        14             // ������14��
#define txmax       100            // ���ű���
#define nmax        14             // ����λ��
#define al          10             // ��ʶ������
#define amax        2047           // �������addr��
#define levmax      3              // Ƕ�ײ���
#define cxmax       200            // code[]����
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
};//���ű����kind
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
	"����0��",
	"����1����Ҫ��=�������ǡ�:=����",
	"����2����Ҫ���֣�",
	"����3����Ҫ�Ⱥ�/��ֵ�ţ�",
	"����4����Ҫ��ʶ����",
	"����5����Ҫ�ֺš�;����",
	"����6������˵��ĩβ���ַǷ��ַ�",
	"����7��",
	"����8���ֳ����β�зǷ��ַ�",
	"����9����Ҫ��š�.��",
	"����10����Ҫ�ֺš�;����",
	"����11��δ����ı�ʶ����",
	"����12����ʶ�����Ǳ�����",
	"����13����Ҫ��ֵ�š�:=����",
	"����14��call����Ĳ��Ǳ�ʶ����",
	"����15��call����Ĳ��ǹ�������",
	"����16��if��û��then��",
	"����17����Ҫend",
	"����18����Ҫdo",
	"����19�����ĩβ���ַǷ��ַ�",
	"����20��ȱ�ٶ�Ԫ�߼��������",
	"����21������ʹ�ñ�ʶ������ʶ���ǹ�������",
	"����22����Ҫ�����š�)����",
	"����23������֮��Ӧ��Ϊ'*'��'/'",
	"����24�����ӿ�ͷӦ��Ϊ��ʶ��/����/������",
	"����25��",
	"����26��",
	"����27��",
	"����28��",
	"����29��",
	"����30������̫��",
	"����31������λ��̫����",
	"����32��Ƕ�ײ����������������ײ�����",
	"����33��",
	"����34��",
	"����35��read()��Ӧ���������ı�������",
	"����36��read���ı�ʶ��Ӧ��Ϊ������",
	"����37��",
	"����38��",
	"����39��code[]����",
	"����40����Ҫ�����š�(��"
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
long dx;		// ���ݶ��ڴ����ָ��
long lev;		// ���
long tx;		// ���ű�λ��
#define stacksize 500
long s[stacksize];

void error(long n) //������
{
	printf("error=>");
	for (int i = 1; i <= cc - 1; i++)
	{
		printf(" ");
	}
	printf("|%s(%d)\n", err_msg[n], n);
	err++;
}//error1

void getch() //ȡ�ַ�
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

void getsym() //ȡ����
{
	int i, j, k;
	while (ch == ' ' || ch == '\t')//�ո�TAB
	{
		getch();
	}
	if (isalpha(ch)) 	//�������ĸ
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
	else if (isdigit(ch)) //���������
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
	else if (ch == ':')//�����ð��
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
	else if (ch == '>')//����
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
	else if (ch == '<')//С��
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
	else//�����ַ�
	{
		sym = ssym[(unsigned char)ch];
		getch();
	}
}//getsym1

void gen(enum fct x, long y, long z) //code����
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

void test(unsigned long s1, unsigned long s2, long n) //���ʺϷ��Բ���
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

void enter(enum object k) //�ǼǷ��ű�
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

long position(char* id) //���ҷ��ű�
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

void constdeclaration() //��������
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

void vardeclaration() //��������
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

void factor(unsigned long fsys) //����
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
						gen(lit, 0, table[i].val);//��������ʶ����Ӧ���ǳ�����ֵΪval������litָ���val�ŵ�ջ��
						break;
					case variable:
						gen(lod, lev - table[i].level, table[i].addr); //TODO �����ʶ���Ǳ�����������lodָ���λ�ھ��뵱ǰ��level�Ĳ��ƫ�Ƶ�ַΪadr�ı����ŵ�ջ��
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
			expression(rparen | fsys);//�ݹ����expression
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

void term(unsigned long fsys) //��
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

void expression(unsigned long fsys) //���ʽ
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

void condition(unsigned long fsys) //��������
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

void statement(unsigned long fsys) //���
{
	long i, cx1, cx2;
	if (sym == ident)//��ֵ���
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
		printf("<��ֵ���>\n");
		expression(fsys);
		if (i != 0)
		{
			gen(sto, lev - table[i].level, table[i].addr);
		}
	}
	else if (sym == callsym)//���̵���
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
				printf("<���̵������>\n");
				gen(cal, lev - table[i].level, table[i].addr);
			}
			else
			{
				error(15);
			}
			getsym();
		}
	}
	else if (sym == ifsym)//�������
	{
		printf("<�������>\n");
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
	else if (sym == beginsym)//�������
	{
		printf("<�������>\n");
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
	else if (sym == whilesym)//whileѭ��
	{
		cx1 = cx;
		printf("<��ѭ�����>\n");
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
	else if (sym == readsym)//read���
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
		printf("<�����>\n");
	}
	else if (sym == writesym)//write���
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
				error(22);//ȱ��������
			}
			else
			{
				printf("<д���>\n");
				getsym();
			}
		}
		gen(opr, 0, 15);//���з�
	}
	else
		printf("<�����>\n");
	test(fsys, 0, 19);
}//state1

void block(unsigned long fsys) //�����
{
	long tx0;		// ���ʼ���ű�ָ��
	long cx0; 		// ���ʼcodeָ��
	long tx1;		// ����ǰ�����ֳ�
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
				printf("<��������>\n");
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
				printf("<��������>\n");
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
				printf("<�����ײ�>\n");
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
				printf("<����˵��>\n");
				getsym();
				test(statbegsys | ident | procsym, fsys, 6);
			}
			else
			{
				error(5);
			}
		}
		test(beginsym, declbegsys|ident|statbegsys, 7);//������俪ͷ
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
	printf("<�������.>\n");
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