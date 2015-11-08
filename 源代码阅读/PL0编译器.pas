program pl0(input,output,fin) ;  
const norw = 13; {*保留字数量*}
      txmax = 100;        { length of identifier table }{*符号表最长*}
      nmax = 14;          { max. no. of digits in numbers }{*数字变量最多数量*}
      al = 10;            { length of identifiers }{*符号最长*}
      amax = 2047;        { maximum address }{*最大地址*}
      levmax = 3;         { maximum depth of block nesting }{*最大嵌套层数*}
      cxmax = 200;        { size of code array }{*？？目标代码数组长度*}
type  symbol =
      ( nul,ident,number,plus,minus,times,slash,oddsym,eql,neq,lss,
       leq,gtr,geq,lparen,rparen,comma,semicolon,period,becomes,
       beginsym,endsym,ifsym,thensym,whilesym,dosym,callsym,constsym,
       varsym,procsym,readsym,writesym );
     alfa = packed array[1..al] of char;
     objecttyp = (constant,variable,prosedure);
     symset = set of symbol; {* 集合类型，可用于存放一组symbol *}
     fct = ( lit,opr,lod,sto,cal,int,jmp,jpc,red,wrt ); { functions }{* 分别标识类PCODE的各条指令 *}
     instruction = packed record
                     f : fct;            { function code }
                     l : 0..levmax;      { level }
                     a : 0..amax;        { displacement address }
                   end;
                  {   lit 0, a : load constant a
                      opr 0, a : execute operation a
                      lod l, a : load variable l,a
                      sto l, a : store variable l,a
                      cal l, a : call procedure a at level l
                      int 0, a : increment t-register by a
                      jmp 0, a : jump to a
                      jpc 0, a : jump conditional to a
                      red l, a : read variable l,a
                      wrt 0, 0 : write stack-top
                  }
var  ch : char;  {* 词法分析存放最近一次读出的字符 *}
      sym: symbol;    { last symbol read }{* 最近一次识别出来的token类型 *}
      id : alfa;      { last identifier read } {* 最近一次识别出来的标识符的名字 *}
      num: integer;   { last number read }{* 最近一次识别出来的数字的值 *}
      cc : integer;   { character count }{* 行缓冲区指针 *} 
      ll : integer;   { line length }{* 行缓冲区长度 *}
      kk,err: integer;{* err出错总次数 *}
      cx : integer;   { code allocation index }
      line: array[1..81] of char;{* 行缓冲区，供词法分析获取单词时用 *}
      a : alfa;{* 词法分析器 临时存放正在分析的词 *}
      code : array[0..cxmax] of instruction;{* 类PCODE代码表*}
      word : array[1..norw] of alfa;{* 保留字表 *}
      wsym : array[1..norw] of symbol;{* 保留字对应的symbol类型 *}
      ssym : array[char] of symbol;{* 符号对应的symbol类型表 *}
      mnemonic : array[fct] of{* 类PCODE指令助记符表 *}
                   packed array[1..5] of char;
      declbegsys, statbegsys, facbegsys : symset;{* 声明开始、表达式开始和项开始符号集合 *}
      table : array[0..txmax] of{* 符号表 *}
                record{* 符号的名字 *}
                  name : alfa;
                  case kind: objecttyp of
                    constant : (val:integer );{* 如果是常量名 *}
                    variable,prosedure: (level,adr: integer ){* 如果是变量名或过程名 *}
                end;
      fin : text;     { source program file }{* 源程序文件 *}
      sfile: string;  { source program file name }{* 源程序文件的文件名 *}

{* 出错处理过程error *}
{* 参数：n:出错代码 *}
procedure error( n : integer );  { P384 }
  begin
    writeln( '****', ' ':cc-1, '^', n:2 );
    err := err+1{* 出错总次数加1 *}
  end; { error }
  

{* 词法分析过程getsym *}
procedure getsym;  { P384 }
  var i,j,k : integer;
  procedure getch; { P384 }{* 读取原程序中下一个字符过程getch *}
    begin
      if cc = ll  { get character to end of line }{* 如果行缓冲区指针指向行缓冲区最后一个字符就从文件读下一行 *}
      then begin { read next line }
             if eof(fin){* 如果到达文件末尾 *}
             then begin
                    writeln('program incomplete');{* 文件不完整，出错 *}
                    close(fin);
                    exit;
                  end;
             ll := 0;{* 行缓冲区长度置0 *}
             cc := 0;{* 行缓冲区指针置行首 *}
             write(cx:4,' ');  { print code address }{* 输出cx值，宽度为4 *}
             while not eoln(fin) do{* 当未到行末时 *}
               begin
                 ll := ll+1;
                 read(fin,ch);
                 write(ch);
                 line[ll] := ch
               end;
             writeln;
             readln(fin);
             ll := ll+1;{* 行缓冲区长度加1，end-line？？*}
             line[ll] := ' ' { process end-line }
           end;
      cc := cc+1;{* 行缓冲区指针加一，指向即将读到的字符 *}
      ch := line[cc]{* 读出字符，放入全局变量ch *}
    end; { getch }


   begin { procedure getsym;  P384 }
    while ch = ' ' do
      getch;
    if ch in ['a'..'z']{* 如果读出的字符是字母，说明是保留字或标识符 *}
    then begin  { identifier of reserved word }
           k := 0;
           repeat{* 读出字符构成标识符 *}
             if k < al
             then begin
                    k := k+1;
                    a[k] := ch
                  end;
             getch
           until not( ch in ['a'..'z','0'..'9']);{* 直到读出的不是字母或数字 *}
{* kk初值为al，即最大标识符长度，如果读到的标识符长度小于kk，就把a数组的后部空间用空格补足，kk的值就成为a数组前部非空格字符的个数。
以后再运行getsym时，如果读到的标识符长度大于等于kk，就把kk的值变成当前标识符的长度。这时就不必在后面填空格了，后面肯定是空格；如果最近读到的标识符长度小于kk，那就需要从kk位置向前，把超过当前标识长度的空间填满空格。*}
           if k >= kk        { kk : last identifier length }
           then kk := k
           else repeat
                  a[kk] := ' ';
                  kk := kk-1
                until kk = k;
           id := a;{* 最后读出标识符等于a *}
           i := 1;{* i指向第1个保留字 *}
           j := norw;   { binary search reserved word table }{* j指向第13个保留字 *}

{* 二分法查找 标识符是不是保留字 *}
           repeat
             k := (i+j) div 2;
             if id <= word[k]
             then j := k-1;
             if id >= word[k]
             then i := k+1
           until i > j;
           if i-1 > j{* 如果i - 1 > j表明在保留字表中找到相应的项，把sym置为相应的保留字值 *}
           then sym := wsym[k]
           else sym := ident{* 未找到保留字，把sym置为ident类型，表示是标识符 *}
         end

    else if ch in ['0'..'9']{* 如果读出字符是数字 *}
         then begin  { number }
                k := 0; {* 数字位数 *}
                num := 0;{* 数字置为0 *}
                sym := number;{* 置sym为number *}
                repeat{* 循环读出数字 *}
                  num := 10*num+(ord(ch)-ord('0'));
                  k := k+1;
                  getch
                until not( ch in ['0'..'9']);
                if k > nmax
                then error(30)
              end

         else if ch = ':' {* 冒号 *}
              then begin
                     getch;
                     if ch = '='{* 如果读到等号，构成赋值号 *}
                     then begin
                            sym := becomes;
                            getch
                          end
                     else sym := nul{* 如果不是读到等号 置为nul *}
                   end
              else if ch = '<'{* 如果读到小于号 *}
                   then begin
                          getch;
                          if ch = '='{* 如果读到等号是<= *}
                          then begin
                                 sym := leq;
                                 getch
                               end
                          else if ch = '>'{* 如果读到大于号是<> *}
                               then begin
                                      sym := neq;
                                      getch
                                    end
                               else sym := lss{}{* 单独的小于号 *}
                        end
                   else if ch = '>' {* 如果读到大于号 *}
                        then begin
                               getch;
                               if ch = '='{* 如果读到等号>= *}
                               then begin
                                      sym := geq;
                                      getch
                                    end
                               else sym := gtr{* 单独的大于号 *}
                             end
                        else begin
                               sym := ssym[ch];{*从符号表中查类型*}
                               getch
                             end
   end; { getsym }

{* 目标代码生成过程gen *}
{* 参数：x: 指令助记符 *}
{*   y, z:代码的两个操作数 *}
{* 把生成的目标代码写入code数组，供解释器解释执行 *}
procedure gen( x: fct; y,z : integer ); { P385 }
  begin
    if cx > cxmax{* 行号大于允许的最大代码行数 *}
    then begin
           writeln('program too long');
           close(fin);
           exit
         end;
    with code[cx] do{* 把指令写入code数组的当前cx所指位置 *}
      begin
        f := x;
        l := y;
        a := z
      end;
    cx := cx+1
  end; { gen }
  

{* 测试当前单词是否合法 过程test *}
{* 参数：s1:当语法分析进入或退出某一语法单元时当前单词符号应属于的集合 *}
{*   s2:在某一出错状态下，可恢复语法分析正常工作的补充单词集合 *}
{*   n:出错信息编号，当当前符号不属于合法的s1集合时发出的出错信息 *}
procedure test( s1,s2 :symset; n: integer );  { P386 }
  begin
    if not ( sym in s1 ){* 如果当前符号不在s1中 *}
    then begin
           error(n);{* n号错误 *}
           s1 := s1+s2;{* s2补充进s1集合 *}
           while not( sym in s1) do{* 找到下一个合法的符号恢复语法分析工作 *}
             getsym
           end
  end; { test }
  

{* 语法分析过程block *}
{* 参数：lev:这1次语法分析所在的层次 *}
{*   tx:符号表指针 *}
{*   fsys:用于出错恢复的单词集合 *}
procedure block( lev,tx : integer; fsys : symset ); { P386 }
  var  dx : integer;  { data allocation index }{* ？？数据段内存分配指针，指向下一个被分配空间在数据段中的偏移位置 *}
       tx0: integer;  { initial table index } {* 本层开始时 符号表位置 *}
       cx0: integer;  { initial code index }{* 本层开始时 代码段分配位置 *}

{* 登陆符号表过程enter *}
{* 参数：k:要登陆到符号表的符号类型 *}
  procedure enter( k : objecttyp ); { P386 }
    begin  { enter object into table }
      tx := tx+1;{* 符号表指针指向一个新的空位 *}
      with table[tx] do
        begin
          name := id;
          kind := k;	
          case k of{* 符号类型：常量、变量、过程名 *}
            constant : begin{* 常量 *}
                         if num > amax{* 常量大于允许的最大值报30号错误置0 *}
                         then begin
                                error(30);
                                num := 0
                              end;
                         val := num{* 合法的数值登陆到符号表 *}
                       end;
            variable : begin{* 变量 *}
                         level := lev;{* 变量所属层次号 *}
                         adr := dx; {* 变量在当前层中的偏移量 *}
                         dx := dx+1
                       end;
            prosedure: level := lev;{* 过程名，记录层次*}
          end
        end
    end; { enter }

{* 在符号表中查找指定符号所在位置的函数position *}
{* 参数：id:要找的符号 *}
{* 返回值：要找的符号在符号表中的位置，如果找不到就返回0 *}
  function position ( id : alfa ): integer; { P386 }
    var i : integer;
    begin
      table[0].name := id;{* 把id放入符号表0号位置 *}
      i := tx;{* 从符号表中当前位置也即最后一个符号开始找 *}
      while table[i].name <> id do
        i := i-1;
      position := i
    end;  { position }
    

{* 常量声明处理过程constdeclaration *}
  procedure constdeclaration; { P386 }
    begin
      if sym = ident{* 第一个符号应为标识符 *}
      then begin
             getsym; {* 获取下一个token *}
             if sym in [eql,becomes]
             then begin
                    if sym = becomes
                    then error(1);{* 赋值号 抛出1号错误 *}
{* 自动错误纠正 使编译继续进行 把赋值号当作等号处理 *}
                    getsym;{* 获取下一个token *}
                    if sym = number{* 如果是数字 把这个常量登陆到符号表 *}
                    then begin
                           enter(constant);
                           getsym
                         end
                    else error(2){* 如果不是数字 抛出2号错误 *}
                  end
             else error(3){* 如果不是等号、赋值 抛出3号错误 *}
           end
      else error(4){* 第一个符号不是标识符 抛出4号错误 *}
    end; { constdeclaration }
    

{* 变量声明过程vardeclaration *} 
  procedure vardeclaration; { P387 }
    begin
      if sym = ident{* 为标识符 则登陆符号表 *}
      then begin
             enter(variable);
             getsym
           end
      else error(4){* 不是标识符 抛出4号错误 *}
    end; { vardeclaration }
    

{* 列出当前一层 类PCODE目标代码 过程listcode *} 
  procedure listcode;  { P387 }
    var i : integer;
    begin

      for i := cx0 to cx-1 do{* 从当前层代码开始位置到当前代码位置-1处，即为本分程序块 *}
        with code[i] do
          writeln( i:4, mnemonic[f]:7,l:3, a:5) {* 显示出第i行代码的助记符和L与A操作数 *}
    end; { listcode }  

{* ！！语句处理过程statement *}
{* 参数说明：fsys: 如果出错可用来恢复语法分析的符号集合 *}
 procedure statement( fsys : symset ); { P387 }
  var i,cx1,cx2: integer;
{* 表达式处理过程expression *}
{* 参数说明：fsys: 如果出错可用来恢复语法分析的符号集合 *}
    procedure expression( fsys: symset); {P387 }
      var addop : symbol;
{* 项处理过程term *}
{* 参数说明：fsys: 如果出错可用来恢复语法分析的符号集合 *}
      procedure term( fsys : symset);  { P387 }
        var mulop: symbol ;
{* 因子处理过程factor *}
{* 参数说明：fsys: 如果出错可用来恢复语法分析的符号集合 *}
        procedure factor( fsys : symset ); { P387 }
          var i : integer;
          begin
            test( facbegsys, fsys, 24 );{* 因子处理前，先检查当前token是否在facbegsys集合中。 *}{* 如果不是合法的token，抛24号错误，并通过fsys集恢复使语法处理可以继续进行 *}   
            while sym in facbegsys do{* 循环处理因子 *}
              begin
                if sym = ident
                then begin
                       i := position(id);
                       if i= 0{* 查符号表返回为0，没有找到标识符，11号错误 *}
                       then error(11)
                       else{* 如果在符号表中找到了标识符，开始生成相应代码 *}
                         with table[i] do
                           case kind of
                             constant : gen(lit,0,val);{* 如果这个标识符对应的是常量，值为val，生成lit指令，把val放到栈顶 *}
                             variable : gen(lod,lev-level,adr);{* ？？如果标识符是变量名，生成lod指令，把位于距离当前层level的层的偏移地址为adr的变量放到栈顶 *}
                             prosedure: error(21){* 如果在因子处理中遇到的标识符是过程名，出错了，抛21号错 *}
                           end;
                       getsym
                     end
                else if sym = number{* 如果因子是数字 *}
                     then begin
                            if num > amax
                            then begin
                                   error(30);
                                   num := 0
                                 end;
                            gen(lit,0,num);{* lit指令，把数值字面常量放到栈顶 *}
                            getsym
                          end
                     else if sym = lparen{* 如果遇到左括号 *}
                          then begin
                                 getsym;
                                 expression([rparen]+fsys);{* 递归调用expression子程序分析一个子表达式 *}
                                 if sym = rparen{* 子表达式之后应遇到右括号 *}
                                 then getsym
                                 else error(22){* 没遇到抛出22号错误 *}
                               end;
                test(fsys,[lparen],23){* ？？一个因子处理完后token应在fsys集合中 *}
              end
          end; { factor }

        begin { procedure term( fsys : symset);   P388
                var mulop: symbol ;    }
          factor( fsys+[times,slash]);*项 由因子开始，调用factor子程序分析因子 *}
          while sym in [times,slash] do{* 一个因子后应当遇到乘号或除号 *}
            begin
              mulop := sym;{* 保存当前运算符 *}
              getsym;
              factor( fsys+[times,slash] );{* 运算符后应是一个因子，故调factor子程序分析因子 *}
              if mulop = times
              then gen( opr,0,4 ){* 生成4乘法指令 *}
              else gen( opr,0,5) {* 生成5除法指令 *}
            end
        end; { term }

      begin { procedure expression( fsys: symset);  P388
              var addop : symbol; }
        if sym in [plus, minus]{* 表达式可由加号或减号开始，表示正负号 *}
        then begin
               addop := sym;{* 把正号或负号保存起来，以便下面生成相应代码 *}
               getsym;
               term( fsys+[plus,minus]);{* 正负号后面是一个项，调term子程序分析 *}
               if addop = minus{* 负号，生成一条1号操作指令，取反运算 *}
               then gen(opr,0,1)
             end
        else term( fsys+[plus,minus]);{* 如果不是正负号开头，就是项开头 *}
        while sym in [plus,minus] do{* 项后应是加运算/减运算 *}
          begin
            addop := sym;{* 保存运算符 *}
            getsym;
            term( fsys+[plus,minus] );{* 加减运算符后应是一个项 *}
            if addop = plus
            then gen( opr,0,2){* 生成2号操作指令：加法 *}
            else gen( opr,0,3) {* 生成3号操作指令：减法 *}
          end
      end; { expression }
      
{* 条件处理过程condition *}
{* 参数说明：fsys: 如果出错可用来恢复语法分析的符号集合 *}
    procedure condition( fsys : symset ); { P388 }
      var relop : symbol;{* 用于临时记录token(一定是一个二元逻辑运算符)的内容 *}
      begin
        if sym = oddsym{* 如果是odd运算符(一元) *}
        then begin
               getsym;
               expression(fsys);{* 对odd的表达式进行处理计算 *}
               gen(opr,0,6){* 生成6号操作指令：奇偶判断 *}
             end
        else begin{* 二元逻辑运算符 *}
               expression( [eql,neq,lss,gtr,leq,geq]+fsys);{* 对表达式左部进行处理计算 *}
               if not( sym in [eql,neq,lss,leq,gtr,geq]){* 不是则抛出20号错误 *}
               then error(20)
               else begin
                      relop := sym;{* 记录下当前的逻辑运算符 *}
                      getsym;
                      expression(fsys);{* 对表达式右部进行处理计算 *}
                      case relop of
                        eql : gen(opr,0,8);{* 等号：产生8号判等指令 *}
                        neq : gen(opr,0,9);{* 不等号：产生9号判不等指令 *}
                        lss : gen(opr,0,10);{* 小于号：产生10号判小指令 *}
                        geq : gen(opr,0,11);{* 大于等号号：产生11号判不小于指令 *}
                        gtr : gen(opr,0,12);{* 大于号：产生12号判大于指令 *}
                        leq : gen(opr,0,13);{* 小于等于号：产生13号判不大于指令 *}
                      end
                    end
             end
      end; { condition }

    begin { procedure statement( fsys : symset );  P389
            var i,cx1,cx2: integer; }
      if sym = ident{* 可能是赋值语句，以标识符开头 *}
      then begin
             i := position(id);
             if i= 0
             then error(11){* 没找到，抛出11号错误 *}
             else if table[i].kind <> variable
                  then begin { giving value to non-variation }
                         error(12);{* 不是变量，抛出12号错误 *}
                         i := 0
                       end;
             getsym;
             if sym = becomes {* 如果的确为赋值号获取下一个taken *}
             then getsym
             else error(13);{* 所接不是赋值号，抛出13号错误 *}
             expression(fsys);{* 处理表达式 *}
             if i <> 0{* 如果不曾出错，i将不为0，为左部标识符在符号表中的位置 *}
             then
               with table[i] do
                 gen(sto,lev-level,adr){* ？？把表达式值写往指定内存的sto目标代码 *}
           end
      else if sym = callsym{* 如果是call语句 *}
      then begin
             getsym;
             if sym <> ident {* 如果call后跟的不是标识符，抛出14号错误 *}
             then error(14)
             else begin
                    i := position(id);
                    if i = 0
                    then error(11){* 没找到，抛出11号错误 *}
                    else
                      with table[i] do
                        if kind = prosedure
                        then gen(cal,lev-level,adr){* 生成cal目标代码，呼叫这个过程 *}
                        else error(15);{* 如果call后跟的不是过程名，抛出15号错误 *}
                    getsym
                  end
           end
      else if sym = ifsym
           then begin
                  getsym;
                  condition([thensym,dosym]+fsys);{* 对逻辑表达式进行分析计算，出错恢复集中加入then和do语句 *}
                  if sym = thensym{* 表达式后应遇到then语句 *}
                  then getsym
                  else error(16);{* 如果if后没有then，抛出16号错误 *}
                  cx1 := cx;{* 记下当前代码分配指针位置 *}
                  gen(jpc,0,0);{* 生成条件跳转指令，跳转位置暂时填0，分析完语句后再填写 *}
                  statement(fsys);
                  code[cx1].a := cx{* 上一行指令(cx1所指的)的跳转位置应为当前cx所指位置 *}
                end


           else if sym = beginsym{* 如果遇到begin *}
                then begin
                       getsym;
                       statement([semicolon,endsym]+fsys);{* 对begin与end之间的语句进行分析处理 *}
                       while sym in ([semicolon]+statbegsys) do{* 如果分析完一句后遇到分号或 语句开始符 循环分析下一句语句 *}
                         begin
                           if sym = semicolon{* 如果是分号（可能是空语句） *}
                           then getsym
                           else error(10);{* 如果语句与语句间没有分号，抛10号错 *}
                           statement([semicolon,endsym]+fsys){* 分析一个语句 *}
                         end;
                       if sym = endsym{* 如果语句全分析完了，应该遇到end *}
                       then getsym
                       else error(17){* 如果不是end，抛出17号错 *}
                     end
                else if sym = whilesym{* 如果遇到while语句 *}
                     then begin
                            cx1 := cx;{* 记下while循环的开始位置 *}
                            getsym;
                            condition([dosym]+fsys); {* 对逻辑表达式进行分析计算 *}
                            cx2 := cx;{* 记下while的do中的语句的开始位置 *}
                            gen(jpc,0,0); {* 生成条件跳转指令，跳转位置暂时填0 *}
                            if sym = dosym{* 逻辑表达式后应为do语句 *}
                            then getsym
                            else error(18);{* 否则，抛出18号错误 *}
                            statement(fsys);{* 分析do后的语句块 *}
                            gen(jmp,0,cx1);{* 生成语句：循环跳转到cx1位置，即再次进行逻辑判断 *}
                            code[cx2].a := cx{* 把刚才填0的跳转位置改成当前位置，完成while语句的处理 *}
                          end




                     else if sym = readsym {* 如果是read语句 *}
                          then begin
                                 getsym;
                                 if sym = lparen{* read语句后跟的应该是左括号 *}
                                 then
                                   repeat
                                     getsym;
                                     if sym = ident{* 如果为一个标识符 *} 
                                     then begin
                                            i := position(id);
                                            if i = 0
                                            then error(11){* 不存在，抛出11号错误 *}
                                            else if table[i].kind <> variable
                                                 then begin
                                                        error(12);{* 不是变量，抛出12号错误 *}
                                                        i := 0
                                                      end
                                                 else with table[i] do
                                                        gen(red,lev-level,adr){* 生成red操作指令 *}
                                          end
                                     else error(40);{* 不是左括号，抛出40号错误 *}
                                     getsym;
                                   until sym <> comma{* 不断生成代码直到read语句的参数表中的变量遍历完不是都好，应为右括号 *}
                                 else error(40);{* 如果不是左括号抛出40号错误 *}
                                 if sym <> rparen{* 如果不是右括号 *}
                                 then error(22);{* 抛出22号错误 *}
                                 getsym
                               end




                          else if sym = writesym
                               then begin
                                      getsym;
                                      if sym = lparen{* 应该是左括号 *}
                                      then begin
                                             repeat
                                               getsym;
{* 调用expression过程分析表达式，用于出错恢复的集合中加上右括号和逗号 *}
                                               expression([rparen,comma]+fsys);
                                               gen(wrt,0,0);{* 生成wrt指令：向屏幕输出 *}
                                             until sym <> comma;{* 循环直到遇到的不再是逗号，应是右括号 *}
                                             if sym <> rparen{* 如果不是右括号 *}
                                             then error(22);{* 抛出22号错误 *}
                                             getsym
                                           end
                                      else error(40){* 如果不是左括号抛出40号错误 *}
                                    end;
      test(fsys,[],19) {* 一个语句处理完成，遇到fsys集中的符号，否则抛19号错 *}
    end; { statement }

  begin  {   procedure block( lev,tx : integer; fsys : symset );    P390
                var  dx : integer;  /* data allocation index */
                     tx0: integer;  /*initial table index */
                     cx0: integer;  /* initial code index */              }
    dx := 3;{* 地址指示器给出每层局部量当前已分配到的相对位置。
  置初始值为3的原因是：每一层最开始的位置有三个空间用于存放静态链SL、动态链DL和返回地址RA *}
    tx0 := tx;{* 初始符号表指针指向当前层的符号在符号表中的开始位置 *}
    table[tx].adr := cx;{* 符号表当前位置记下当前层代码的开始位置 *}
    gen(jmp,0,0); { jump from declaration part to statement part }{* 产生一行跳转指令，跳转位置暂时未知填0 *}
    if lev > levmax {* 如果当前过程嵌套层数大于最大允许的套层数，抛出32号错误 *}
    then error(32);

    repeat{* 循环处理源程序中所有的声明部分 *}
      if sym = constsym{* 常量声明 *}
      then begin
             getsym;
             repeat
               constdeclaration;
               while sym = comma do
                 begin
                   getsym;
                   constdeclaration
                 end;
               if sym = semicolon {* 遇到分号，常量声明结束 *}
               then getsym
               else error(5){* 如果常量声明语句结束后没有遇到分号，抛出5号错误 *}
             until sym <> ident{* 如果遇到非标识符，则常量声明结束 *}
           end;
      if sym = varsym {* 变量声明 *}
      then begin
             getsym;
             repeat
               vardeclaration;
               while sym = comma do
                 begin
                   getsym;
                   vardeclaration
                 end;
               if sym = semicolon{* 遇到分号，变量声明结束 *}
               then getsym
               else error(5){* 如果变量声明语句结束后没有遇到分号，抛出5号错误 *}
             until sym <> ident;{* 如果遇到非标识符，则变量声明结束 *}
           end;
      while sym = procsym do{* 循环声明子过程 *}
        begin
          getsym;
          if sym = ident
          then begin
                 enter(prosedure);{* 把过程登录到符号表中 *}
                 getsym
               end
          else error(4);{* 如果不是标识符，抛出4号错误 *}
          if sym = semicolon{* 如果当前token为分号 *}
          then getsym
          else error(5);{* 不是分号，抛出5号错误 *}
          block(lev+1,tx,[semicolon]+fsys);{* 递归调用语法分析过程，当前层次加1，同时传递表头索引、合法单词符 *}
          if sym = semicolon{* 递归返回 最后一个end后的分号 *}
          then begin
                 getsym;
                 test( statbegsys+[ident,procsym],fsys,6){* 检查当前token是否合法，不合法则用fsys恢复语法分析同时抛6号错 *}
               end
          else error(5){* 不是分号，抛出5号错误 *}
        end;
      test( statbegsys+[ident],declbegsys,7){* 检查当前状态是否合法，不合法则用声明开始符号作出错恢复、抛7号错 *}
    until not ( sym in declbegsys );{* 直到声明性的源程序分析完毕，分析主程序 *}
    code[table[tx0].adr].a := cx;  { back enter statement code's start adr. }{* 把前面生成的跳转语句的跳转位置改成当前位置 *}
    with table[tx0] do
      begin
        adr := cx; { code's start address }{* 地址为当前代码分配地址 *}
      end;
    cx0 := cx;{* 记下当前代码分配位置 *}
    gen(int,0,dx); { topstack point to operation area }{* 生成分配空间指令，分配dx个空间 *}
    statement( [semicolon,endsym]+fsys);{* 处理当前遇到的语句或语句块 *}
    gen(opr,0,0); { return }{* ？？生成从子程序返回操作指令 *}
    test( fsys, [],8 );{* 用fsys检查当前状态是否合法，不合法则抛8号错 *}
    listcode;{* 列出本层的类PCODE代码 *}
  end { block };

{* 目标代码解释运行过程interpret *}
procedure interpret;  { P391 }
  const stacksize = 500;{* 常量定义假想有500个栈单元 *}
  var p,b,t: integer; { program-,base-,topstack-register }
{* p为程序指令指针，指向下一条要运行的代码 *}
{* b为基址指针，指向每个过程被调用时数据区中分配给它的局部变量数据段基址 *}
{* t为栈顶寄存器，这个变量记录这个计算机的当前栈顶位置 *}
      i : instruction;{ instruction register }{* i变量中存放当前在运行的指令 *}
      s : array[1..stacksize] of integer; { data store }{* s为栈式计算机的数据内存区 *}


{* 通过静态链求出数据区基地址的函数base *}
{* 参数说明：l：要求的数据区所在层与当前层的层差 *}
{* 返回值：要求的数据区基址 *}
  function base( l : integer ): integer;
    var b1 : integer;
    begin { find base l levels down }
      b1 := b;
      while l > 0 do
        begin
          b1 := s[b1];{* ？？用当前层数据区基址中的内容（正好是静态链SL数据，为上一层的基址）的作为新的当前层，即向上找了一层 *}
          l := l-1
        end;
      base := b1{* 把找到的要求的数据区基址返回 *}
  end; { base }


  begin  { P392 }
    writeln( 'START PL/0' );{* PL/0程序开始运行 *}
    t := 0;{* 程序开始运行时 栈顶寄存器置0 *}
    b := 1;{* ！！数据段基址为1 *}
    p := 0;{* 从0号代码开始执行程序 *}
    s[1] := 0;
    s[2] := 0;
    s[3] := 0;{* 数据内存中为SL,DL,RA三个单元均为0，标识为主程序 *}
    repeat
      i := code[p];
      p := p+1;
      with i do
        case f of {* 指令助记符，执行不同的功能 *}
          lit : begin{* 如果是lit指令 *}
                  t := t+1;{* 栈顶指针上移，在栈中分配了一个单元 *}
                  s[t]:= a;{* 该单元的内容存放i指令的a操作数，即实现了把常量值放到运行栈栈顶 *}
                end;
          opr : case a of { operator }{* 如果是opr指令 *}
                  0 : begin { return }{* 0号操作为从子过程返回操作 *}
                        t := b-1;{* ？？释放这段子过程占用的数据内存空间 *}
                        p := s[t+3];{* 把指令指针取到RA的值，指向的是返回地址 *}
                        b := s[t+2];{* 把数据段基址取到DL的值，指向调用前子过程的数据段基址 *}
                      end;
                  1 : s[t] := -s[t];{* 1号操作为栈顶数据取反操作 *}
                  2 : begin{* 2号操作为栈顶两个数据加法操作 *}
                        t := t-1;{* ！！栈顶指针下移，节约空间 *} 
                        s[t] := s[t]+s[t+1]
                      end;
                  3 : begin{* 3号操作为栈顶两个数据减法操作 *}
                        t := t-1;
                        s[t] := s[t]-s[t+1]
                      end;
                  4 : begin{* 4号操作为栈顶两个数据乘法操作 *}
                        t := t-1;
                        s[t] := s[t]*s[t+1]
                      end;
                  5 : begin{* 5号操作为栈顶两个数据除法操作 *}
                        t := t-1;
                        s[t] := s[t]div s[t+1]
                      end;
                  6 : s[t] := ord(odd(s[t]));{* 6号操作为判奇操作 *}{* 数据栈顶的值是奇数则把栈顶值置1，否则置0 *}
                  8 : begin{* 8号操作为栈顶两个数据判等操作 *}
                        t := t-1;
                        s[t] := ord(s[t]=s[t+1])
                      end;
                  9 : begin{* 9号操作为栈顶两个数据判不等操作 *}
                        t := t-1;
                        s[t] := ord(s[t]<>s[t+1])
                      end;
                  10: begin{* 10号操作为栈顶两个数据判小于操作 *}
                        t := t-1;
                        s[t] := ord(s[t]< s[t+1])
                      end;
                  11: begin{* 11号操作为栈顶两个数据判大于等于操作 *}
                        t := t-1;
                        s[t] := ord(s[t] >= s[t+1])
                      end;
                  12: begin{* 12号操作为栈顶两个数据判大于操作 *}
                        t := t-1;
                        s[t] := ord(s[t] > s[t+1])
                      end;
                  13: begin{* 13号操作为栈顶两个数据判小于等于操作 *}
                        t := t-1;
                        s[t] := ord(s[t] <= s[t+1])
                      end;
                end;
          lod : begin{* 如果是lod指令:将变量放到栈顶 *}
                  t := t+1;
                  s[t] := s[base(l)+a]
                end;
          sto : begin{* 如果是sto指令:把栈顶的值存入位置在数据区层差l偏移地址a的变量内存 *}
                  s[base(l)+a] := s[t];  { writeln(s[t]); }
                  t := t-1
                end;
          cal : begin  { generate new block mark }{* 如果是cal指令 *}
                  s[t+1] := base(l);{* 在栈顶压入静态链SL *}
                  s[t+2] := b;{* 压入当前数据区基址，作为动态链DL *}
                  s[t+3] := p;{* 压入当前的断点，作为返回地址RA *}
                  b := t+1;{* 把当前数据区基址指向SL所在位置 *}
                  p := a;{* 从a所指位置开始继续执行指令，实现程序执行的跳转 *}
                end;
          int : t := t+a;{* 如果是int指令,栈顶上移a个空间，即开辟a个新的内存单元 *}
          jmp : p := a;{* 把jmp指令操作数a的值作为下一次要执行的指令地址，实现无条件跳转 *}
          jpc : begin{* 如果是jpc指令 *}
                  if s[t] = 0
                  then p := a;{* 如果是0就跳转，否则不跳转 *}
                  t := t-1;
                end;
          red : begin{* ？？如果是red指令 *}
                  writeln('??:');
                  readln(s[base(l)+a]);
                end;
          wrt : begin{* 如果是wrt指令,输出栈顶值 *}
                  writeln(s[t]);
                  t := t+1
                end
        end { with,case }

    until p = 0;{* 主程序de子程序返回指令，也就是整个程序运行的结束 *}
    writeln('END PL/0');
  end; { interpret }

{* main 入口*}
begin { main }
  writeln('please input source program file name : ');
  readln(sfile);
  assign(fin,sfile);
  reset(fin);{*以只读的方式打开文件*}
  for ch := 'A' to ';' do{*这个循环把ssym数组填nul *}
  ssym[ch] := nul;
  {*初始化保留字表，空格填充？？，便于词法分析时以二分法来查找保留字*}
  word[1] := 'begin        '; word[2] := 'call         ';
  word[3] := 'const        '; word[4] := 'do           ';
  word[5] := 'end          '; word[6] := 'if           ';
  word[7] := 'odd          '; word[8] := 'procedure    ';
  word[9] := 'read         '; word[10]:= 'then         ';
  word[11]:= 'var          '; word[12]:= 'while        ';
  word[13]:= 'write        ';
  {* 保留字符号列表，相应位置保留字的类型 *}
  wsym[1] := beginsym;      wsym[2] := callsym;
  wsym[3] := constsym;      wsym[4] := dosym;
  wsym[5] := endsym;        wsym[6] := ifsym;
  wsym[7] := oddsym;        wsym[8] := procsym;
  wsym[9] := readsym;       wsym[10]:= thensym;
  wsym[11]:= varsym;        wsym[12]:= whilesym;
  wsym[13]:= writesym;
  {* 初始化符号表，把符号赋上相应的类型，其余符号类型均为nul *}
  ssym['+'] := plus;        ssym['-'] := minus;
  ssym['*'] := times;       ssym['/'] := slash;
  ssym['('] := lparen;      ssym[')'] := rparen;
  ssym['='] := eql;         ssym[','] := comma;
  ssym['.'] := period;
  ssym['<'] := lss;         ssym['>'] := gtr;
  ssym[';'] := semicolon;
  {* 初始化类PCODE助记符表，供输出类PCODE代码用 *}
  mnemonic[lit] := 'LIT  '; mnemonic[opr] := 'OPR  ';
  mnemonic[lod] := 'LOD  '; mnemonic[sto] := 'STO  ';
  mnemonic[cal] := 'CAL  '; mnemonic[int] := 'INT  ';
  mnemonic[jmp] := 'JMP  '; mnemonic[jpc] := 'JPC  ';
  mnemonic[red] := 'RED  '; mnemonic[wrt] := 'WRT  ';
  
  declbegsys := [ constsym, varsym, procsym ];
  statbegsys := [ beginsym, callsym, ifsym, whilesym];
  facbegsys := [ ident, number, lparen ];
  err := 0;{* 出错次数置0 *}
  cc := 0;{* 词法分析行缓冲区指针置0 *}
  cx := 0;{* 类PCODE代码表指针置0 *}
  ll := 0;{* 词法分析行缓冲区长度置0 *}
  ch := ' ';{* 词法分析当前字符为空格 *}
  kk := al;{* 置kk的值为允许的标识符的最长长度 *}
  getsym;{* 首次调用词法分析，获取第一个token *}
  block( 0,0,[period]+declbegsys+statbegsys );{* 主程序的语法分析，符号表暂时为空，符号表指针指0号位置*}
  if sym <> period{* 主程序分析结束，句号结束否则报9号错 *}
  then error(9);
  if err = 0{* 如果出错次数为0，解释执行编译产生的代码 *}
  then interpret
  else write('ERRORS IN PL/0 PROGRAM');{* 如果有错提示 *}
  writeln;
  close(fin){* 关闭源程序文件 *}
end.