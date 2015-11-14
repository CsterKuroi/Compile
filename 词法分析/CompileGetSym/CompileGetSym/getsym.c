#include<stdio.h>
#include<stdlib.h>
#include<ctype.h>
#include<string.h>

#define al 10						//al      ���ŵĳ���
#define norw 14						//norw    ����������
#define nmax 14						//nmax    numλ��
#define ident     "ident     "		//ident   ��ʶ������
#define number    "number    "		//number  ��������
#define becomes   "becomes   "		//��������
#define nul       "nul       "
#define geq       "geq       "
#define gtr       "gtr       "
#define leq       "leq       "
#define neq       "neq       "
#define lss       "lss       "
#define plus      "plus      "
#define minus     "minus     "
#define times     "times     "
#define slash     "slash     "
#define lparen    "lparen    "
#define rparen    "rparen    "
#define eql       "eql       "
#define comma     "comma     "
#define period    "period    "
#define semicolon "semicolon "

FILE* infile;						//Դ�ļ�
char infilename[80];				//Դ�ļ���
errno_t ferr;						//���ļ�����ֵ 0����
char line[81];						//�ļ���һ�У���1��ʼ��
char ch;							//��ȡ�����ַ�
int cc;								//line��ָ��
int ll;								//line����
char a[al + 1];						//��ɱ�ʶ��/������
char id[al + 1];					//��ʶ��/�����ֵĿ���
char sym[al+1];						//�ִ�����
int kk;								//�Ż�getsym
char word[norw][al + 1];			//�����ֱ�
char wsym[norw][al + 1];			//���������ͱ�
char ssym[256][al+1];				//�������ͱ�
int num;							//����

int error(int n)
{
	printf("error:%d\n", n);
	return 0;
}//error

int getch()
{
	if (cc == ll)
	{
		if (feof(infile))
		{
			printf("***********\n");
			printf("End of file\n");
			printf("***********\n");
			exit(1);
		}
		ll=0;
		cc=0;
		while ((!feof(infile)) && ((ch = getc(infile)) != '\n') && (ch!=-1))
			line[++ll] = ch;
		line[++ll] = ' ';
	}
	ch = line[++cc];
	return 0;
}//getchar

void getsym(void)
{
	int i,j,k;
	while (ch == ' ' || ch == '\t')
		getch();
	if (isalpha(ch))//�������ĸ
	{
		k = 0;
		do
		{
			if (k < al)
				a[k++] = ch;
			getch();
		} while (isalpha(ch) || isdigit(ch));
		if (k >= kk)
			kk = k;
		else do{
			kk = kk - 1;
			a[kk] = ' ';
		} while (k <kk);
		strcpy_s(id, al+1, a);
		i = 0;
		j = norw - 1;
		do
		{
			k = (i + j) / 2;
			if (strcmp(id, word[k])==0) break;
			else if (strcmp(id,word[k])<0)
			{
				j = k - 1;
			}
			else if (strcmp(id,word[k])>0)
			{
				i = k + 1;
			}
			
		} while (i <= j);

		if (i>j)
		{
			strcpy_s(sym,al+1,ident);
		}
		else
		{
			strcpy_s(sym, al+1, wsym[k]);
		}
	}
	else if (isdigit(ch))//���������
	{
		k = 0;
		num = 0;
		strcpy_s(sym, al+1, number);
		do
		{
			num = num * 10 + ch - '0';
			k++;
			getch();
		} while (isdigit(ch));
		if (k > nmax)
			error(3);
	}
	else if (ch == ':')//�����ð��
	{
		getch();
		if (ch == '=')
		{
			strcpy_s(sym, al+1, becomes);
			getch();
		}
		else
		{
			strcpy_s(sym, al+1, nul);
		}
	}

	else if (ch == '>')//����
	{
		getch();
		if (ch == '=')
		{
			strcpy_s(sym, al+1, geq);
			getch();
		}
		else
		{
			strcpy_s(sym, al+1, gtr);
		}
	}
	else if (ch == '<')//С��
	{
		getch();
		if (ch == '=')
		{
			strcpy_s(sym, al+1, leq);
			getch();
		}
		else if (ch == '>')
		{
			strcpy_s(sym, al+1, neq);
			getch();
		}
		else
		{
			strcpy_s(sym, al+1, lss);
		}
	}
	else
	{ 
		strcpy_s(sym, al+1, ssym[ch]);//�����ַ�
		getch();
	}
} //getsym

int main()
{
	//��ʼ�����ֱ���
	kk = al; 
	cc = 0;
	ll = 0;
	ch = ' ';
	//��ʼ���������ͱ�
	for(int i=0;i<256;i++)
		strcpy_s(ssym[i], al+1, nul);
	strcpy_s(ssym['+'], al+1, plus);
	strcpy_s(ssym['-'], al+1, minus);
	strcpy_s(ssym['*'], al+1, times);
	strcpy_s(ssym['/'], al+1, slash);
	strcpy_s(ssym['('], al+1, lparen);
	strcpy_s(ssym[')'], al+1, rparen);
	strcpy_s(ssym['='], al+1, eql);
	strcpy_s(ssym[','], al+1, comma);
	strcpy_s(ssym['.'], al+1, period);
	strcpy_s(ssym['<'], al+1, lss);
	strcpy_s(ssym['>'], al+1, gtr);
	strcpy_s(ssym[';'], al+1, semicolon);
	//��ʼ�������ֱ�
	strcpy_s(word[0], al+1, "begin     ");
	strcpy_s(word[1], al+1, "call      ");
	strcpy_s(word[2], al+1, "const     ");
	strcpy_s(word[3], al+1, "do        ");
	strcpy_s(word[4], al + 1, "else      ");
	strcpy_s(word[5], al+1, "end       ");
	strcpy_s(word[6], al+1, "if        ");
	strcpy_s(word[7], al+1, "odd       ");
	strcpy_s(word[8], al+1, "procedure ");
	strcpy_s(word[9], al+1, "read      ");
	strcpy_s(word[10], al+1, "then      ");
	strcpy_s(word[11], al+1, "var       ");
	strcpy_s(word[12], al+1, "while     ");
	strcpy_s(word[13], al+1, "write     ");
	//��ʼ�����������ͱ�
	strcpy_s(wsym[0], al+1, "beginsym  ");
	strcpy_s(wsym[1], al+1, "callsym   ");
	strcpy_s(wsym[2], al+1, "constsym  ");
	strcpy_s(wsym[3], al+1, "dosym     ");
	strcpy_s(wsym[4], al+1, "elsesym   ");
	strcpy_s(wsym[5], al+1, "endsym    ");
	strcpy_s(wsym[6], al+1, "ifsym     ");
	strcpy_s(wsym[7], al+1, "oddsym    ");
	strcpy_s(wsym[8], al+1, "prosym    ");
	strcpy_s(wsym[9], al+1, "readsym   ");
	strcpy_s(wsym[10], al+1, "thensym   ");
	strcpy_s(wsym[11], al+1, "varsym    ");
	strcpy_s(wsym[12], al+1, "whilesym  ");
	strcpy_s(wsym[13], al+1, "writesym  ");
	//��ȡ�ļ�
	printf("please input source program file name : \n");
	scanf_s("%s",infilename,80);
	if ((ferr = fopen_s(&infile, infilename, "r")) != 0)
	{
		error(1);
		exit(1);
	}
	//�ִ����{���,�ִ�����,����ֵ}(һ��һ��ĵ���ֵΪ��,������ֺͱ�ʶ����Ҫ�������ֵ)
	for (int i = 1;;i++){
		getsym();
		if (strcmp(sym, number)==0)
			printf("%d %s %d\n",i,sym,num);
		else if (strcmp(sym, ident) == 0)
			printf("%d %s %s\n", i, sym, id);
		else
			printf("%d %s\n", i, sym);
	}
	fclose(infile);
	return 0;
}