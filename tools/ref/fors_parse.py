import sys,re,os
RES=set("module use pub fn struct enum trait impl const extern let var inout sink if else match for in while break continue return raise raises with parallel simd spawn comptime move consume discard as and or not true false iso imm secret dyn asm import recover type".split())
SUF=set("i8 i16 i32 i64 u8 u16 u32 u64 isize usize f32 f64".split())
ISUF=SUF-{"f32","f64"}
PUN=sorted("( ) [ ] { } , ; : . @ ? -> => = == != < > <= >= + - * / % & | ^ << >> ..< ..= += -= *= /= %= &= |= ^= <<= >>=".split(),key=len,reverse=True)
class E(Exception): pass
def lex(s):
    t=[];i=0;n=len(s);line=1
    def err(m): raise E("lex line %d: %s"%(line,m))
    while i<n:
        c=s[i]
        if c in " \t\r\n":
            if c=="\n": line+=1
            i+=1;continue
        if s.startswith("//",i):
            while i<n and s[i]!="\n": i+=1
            t.append(("cmt","",line)) ;continue
        if s.startswith("/*",i):
            d=1;i+=2
            while i<n and d:
                if s.startswith("/*",i): d+=1;i+=2
                elif s.startswith("*/",i): d-=1;i+=2
                else:
                    if s[i]=="\n": line+=1
                    i+=1
            if d: err("unterminated comment")
            t.append(("cmt","",line));continue
        if ord(c)>127: err("non-ascii")
        if c.isalpha() or c=="_":
            j=i
            while j<n and (s[j].isalnum() or s[j]=="_") and ord(s[j])<128: j+=1
            w=s[i:j];i=j
            t.append(("_" if w=="_" else "kw" if w in RES else "id",w,line));continue
        if c.isdigit():
            j=i;isf=False;radix=False
            def digs(j,ok):
                if j>=n or s[j] not in ok: err("digit expected")
                while j<n:
                    if s[j] in ok: j+=1
                    elif s[j]=="_" and j+1<n and s[j+1] in ok: j+=2
                    else: break
                return j
            D="0123456789"
            if s[i]=="0" and i+1<n and s[i+1] in "xob":
                radix=True
                j=digs(i+2,{"x":"0123456789abcdefABCDEF","o":"01234567","b":"01"}[s[i+1]])
            else:
                j=digs(i,D)
                if j+1<n and s[j]=="." and s[j+1] in D: isf=True;j=digs(j+1,D)
                if j<n and s[j] in "eE" and (j+1<n and (s[j+1] in D or (s[j+1] in "+-" and j+2<n and s[j+2] in D))):
                    isf=True;j+=1
                    if s[j] in "+-": j+=1
                    j=digs(j,D)
            k=j
            while k<n and (s[k].isalnum() or s[k]=="_"): k+=1
            suf=s[j:k]
            if suf:
                if suf not in SUF or (radix and suf not in ISUF) or (isf and suf not in("f32","f64")): err("bad suffix %r"%suf)
            t.append(("num",s[i:k],line));i=k;continue
        if c=='"':
            j=i+1
            while True:
                if j>=n or s[j]=="\n": err("unterminated string")
                if s[j]=="\\":
                    e=s[j+1]
                    if e in 'nrt0\\"': j+=2
                    elif e=="x" and re.match(r"[0-9a-fA-F]{2}",s[j+2:j+4]): j+=4
                    elif e=="u":
                        m=re.match(r"\{[0-9a-fA-F]+\}",s[j+2:])
                        if not m: err("bad \\u")
                        j+=2+m.end()
                    else: err("bad escape")
                elif s[j]=='"': break
                else: j+=1
            t.append(("str",s[i:j+1],line));i=j+1;continue
        if s.startswith("\\\\",i):
            while i<n and s[i]!="\n": i+=1
            if t and t[-1][0]=="mstr": pass
            else: t.append(("mstr","",line))
            continue
        if s.startswith("..",i) and not (s.startswith("..<",i) or s.startswith("..=",i)): err("'..' alone")
        for p in PUN:
            if s.startswith(p,i):
                t.append(("p",p,line));i+=len(p);break
        else: err("bad char %r"%c)
    # comments break mstr joins: handled since cmt token intervenes; now drop cmts
    t=[x for x in t if x[0]!="cmt"]
    t.append(("eof","",line));return t
CMP=["==","!=","<",">","<=",">="]
ASG=["=","+=","-=","*=","/=","%=","&=","|=","^=","<<=",">>="]
class P:
    def __init__(s,t): s.t=t;s.i=0
    def k(s,o=0): return s.t[min(s.i+o,len(s.t)-1)]
    def isp(s,x,o=0): a=s.k(o);return a[0] in("p","kw","_") and a[1]==x
    def isid(s,w=None,o=0): a=s.k(o);return a[0]=="id" and (w is None or a[1]==w)
    def err(s,m): a=s.k();raise E("parse line %d at %r: %s"%(a[2],a[1] or a[0],m))
    def eat(s,x):
        if not s.isp(x): s.err("expected %r"%x)
        s.i+=1
    def opt(s,x):
        if s.isp(x): s.i+=1;return True
        return False
    def ident(s):
        if not s.isid(): s.err("expected identifier")
        s.i+=1;return s.t[s.i-1][1]
    def clist(s,item,close,minn=0):
        c=0
        while not s.isp(close):
            item();c+=1
            if not s.opt(","): break
        if c<minn: s.err("expected at least %d item"%minn)
        s.eat(close)
    def path(s):
        p=[s.ident()]
        while s.isp(".") and s.isid(o=1): s.i+=1;p.append(s.ident())
        return p
    def needs_item(s):
        # closed single-segment sealed-capability vocabulary: "asm" is also
        # reserved (R2-4), so accept it bare as this one item.
        if s.isp("asm"): s.i+=1;return ["asm"]
        return s.path()
    def file(s):
        if s.opt("module"): s.path();s.eat(";")
        if s.isid("contracts"): s.i+=1;s.eat(":");s.eat(".");s.ident();s.eat(";")
        if s.isid("needs"): s.i+=1;s.eat("{");s.clist(s.needs_item,"}");s.eat(";")
        if s.isid("inputs"): s.i+=1;s.eat("{");s.clist(lambda:s.strlit(),"}");s.eat(";")
        while s.isp("use") or (s.isp("pub") and s.isp("use",1)):
            s.opt("pub");s.eat("use")
            def use_item():
                s.path()
                if s.opt("as"): s.ident()
            use_item()
            while s.opt(","): use_item()
            s.eat(";")
        while s.k()[0]!="eof": s.decl()
    def attr(s):
        s.eat("@");s.ident()
        if s.opt("("):
            def a():
                if s.isid() and s.isp(":",1): s.i+=2
                if s.isid(): s.path()
                elif not s.literal(): s.err("attr arg must be literal or path")
            s.clist(a,")")
    def literal(s):
        a=s.k()
        if a[0] in("num","str","mstr") or s.isp("true") or s.isp("false"): s.i+=1;return True
        if s.isp(".") and s.isid(o=1): s.i+=2;return True
        return False
    def strlit(s):
        if s.k()[0] not in("str","mstr"): s.err("expected a string")
        s.i+=1
    def decl(s):
        while s.isp("@"): s.attr()
        s.opt("pub")
        if s.isp("fn"): s.fnsig();s.block()
        elif s.opt("extern"):
            if s.k()[0]!="str": s.err("expected ABI string")
            s.i+=1;s.fnsig();s.eat(";")
        elif s.isp("struct") or (s.isid("soa") and s.isp("struct",1)):
            if s.isid(): s.i+=1
            s.eat("struct");s.ident()
            if s.isp("["): s.generics()
            while s.isid("invariant"): s.i+=1;s.expr(True)
            s.eat("{");s.clist(s.field,"}")
        elif s.opt("enum"):
            s.ident()
            if s.isp("["): s.generics()
            s.eat("{")
            def v():
                s.ident()
                if s.opt("("): s.clist(s.type,")",1)
                elif s.opt("{"): s.clist(s.field,"}",1)
            s.clist(v,"}",1)
        elif s.opt("trait"):
            s.ident()
            if s.isp("["): s.generics()
            s.eat("{")
            while not s.isp("}"):
                if s.isp("type"):
                    s.i+=1;s.ident()
                    if s.opt(":"):
                        s.type()
                        while s.opt("+"): s.type()
                    s.eat(";");continue
                while s.isp("@"): s.attr()
                s.fnsig()
                if not s.opt(";"): s.block()
            s.eat("}")
        elif s.opt("impl"):
            if s.isp("["): s.generics()
            s.type()
            if s.opt("for"): s.type()
            s.eat("{")
            while not s.isp("}"):
                if s.isp("type"):
                    s.i+=1;s.ident();s.eat("=");s.type();s.eat(";");continue
                while s.isp("@"): s.attr()
                s.opt("pub");s.fnsig();s.block()
            s.eat("}")
        elif s.opt("const"):
            s.ident();s.eat(":");s.type();s.eat("=");s.expr();s.eat(";")
        else: s.err("expected declaration")
    def field(s): s.opt("pub");s.ident();s.eat(":");s.type()
    def generics(s):
        s.eat("[")
        def g():
            s.ident()
            if s.opt("."):
                s.ident();s.eat(":")
                s.type()
                while s.opt("+"): s.type()
                return
            if s.opt(":"):
                if s.isid("brand"): s.i+=1
                else:
                    s.type()
                    while s.opt("+"): s.type()
        s.clist(g,"]",1)
    def conv(s):
        if s.isp("let") or s.isp("inout") or s.isp("sink") or s.isid("set"): s.i+=1
        else: s.err("expected convention (let/inout/sink/set)")
    def fnsig(s):
        s.eat("fn");s.ident()
        if s.isp("["): s.generics()
        s.eat("(")
        def p(): s.conv();s.ident();s.eat(":");s.type()
        s.clist(p,")")
        if s.opt("->"): s.rettype()
        if s.opt("raises"): s.type()
        while s.isid("pre") or s.isid("post") or s.isid("invariant"): s.i+=1;s.expr(True)
    # types
    def quals(s):
        while s.isp("iso") or s.isp("imm") or s.isp("secret"): s.i+=1
    def type(s):
        s.quals();return s.typecore()
    def typeapp(s):
        s.path();bare=True
        if s.opt("["): bare=False;s.clist(s.targ,"]",1)
        return bare
    def targ(s):
        a=s.k()
        if a[0] in("num","str") or s.isp("true") or s.isp("false") or s.isp("-"): s.addexpr(False);return
        bare=s.type()
        if bare is True:
            while any(s.isp(o) for o in "+-*/%"): s.i+=1;s.cast(False)
    def fntype(s):
        s.eat("fn");s.eat("(")
        def fp(): s.conv();s.type()
        s.clist(fp,")")
        if s.opt("->"): s.type()
        if s.opt("raises"): s.type()
    def typecore(s):
        if s.isid(): return s.typeapp()
        if s.opt("("): s.clist(s.type,")");return False
        if s.isp("fn"): s.fntype();return False
        if s.opt("dyn"): s.typeapp();return False
        s.err("expected type")
    def rettype(s):
        if s.isid("scoped") and s.isp("(",1): s.i+=2;s.ident();s.eat(")")
        s.quals()
        if s.isid(): s.typeapp()
        elif s.isp("fn"): s.fntype()
        elif s.opt("dyn"): s.typeapp()
        elif s.opt("("): s.clist(s.rettype,")")
        else: s.err("expected return type")
    # statements
    def block(s):
        s.eat("{")
        while not s.isp("}"): s.stmt()
        s.eat("}")
    def binding(s):
        if s.isid() or s.isp("_"): s.i+=1
        elif s.opt("("): s.clist(s.binding,")",1)
        else: s.err("expected binding name")
    def stmt(s):
        if s.isp("let") or s.isp("var"):
            s.i+=1;s.binding()
            if s.opt(":"): s.type()
            if s.opt("="): s.expr()
            s.eat(";")
        elif s.isp("if"): s.ifexpr()
        elif s.isp("match"): s.matchexpr()
        elif s.opt("comptime"): s.block()
        elif s.opt("for"): s.binding();s.eat("in");s.expr(True);s.block()
        elif s.opt("while"): s.expr(True);s.block()
        elif s.opt("break") or s.opt("continue"): s.eat(";")
        elif s.opt("return"):
            if not s.isp(";"): s.expr()
            s.eat(";")
        elif s.opt("raise"): s.expr();s.eat(";")
        elif s.opt("with"):
            if not (s.isid("arena") or s.isid("allocator")): s.err("expected arena/allocator")
            s.i+=1;s.ident();s.eat(":");s.type();s.block()
        elif s.opt("parallel"):
            if s.opt("for"):
                s.binding();s.eat("in");s.expr(True)
                if s.isid("grain"): s.i+=1;s.expr(True)
            s.block()
        elif s.opt("simd"): s.eat("for");s.binding();s.eat("in");s.expr(True);s.block()
        elif s.opt("spawn"): s.expr();s.eat(";")
        elif s.opt("consume") or s.opt("discard"): s.place();s.eat(";")
        elif s.isp("@"): s.attr();s.block()
        elif s.isp("{"): s.block()
        else:
            e=s.expr()
            if any(s.isp(a) for a in ASG):
                if not isplace(e): s.err("assignment target is not a place")
                s.i+=1;s.expr();s.eat(";")
            elif s.isp("}"): pass
            else: s.eat(";")
    def place(s):
        s.ident()
        while True:
            if s.isp(".") : s.i+=1;s.ident()
            elif s.isp("["): s.bracket()
            else: break
    # expressions
    def expr(s,ns=False):
        e=s.andexpr(ns)
        while s.opt("or"): s.andexpr(ns);e=("o",)
        return e
    def andexpr(s,ns):
        e=s.notexpr(ns)
        while s.opt("and"): s.notexpr(ns);e=("o",)
        return e
    def notexpr(s,ns):
        if s.opt("not"): s.notexpr(ns);return ("o",)
        return s.cmp(ns)
    def cmp(s,ns):
        e=s.cast(ns)
        for b in "&|^":
            if s.isp(b):
                while s.opt(b): s.cast(ns)
                return ("o",)
        if s.opt("<<") or s.opt(">>"): s.cast(ns);return ("o",)
        e=s.rangeexpr(ns,e)
        if any(s.isp(c) for c in CMP): s.i+=1;s.rangeexpr(ns,None);e=("o",)
        return e
    def rangeexpr(s,ns,seed):
        e=s.addexpr(ns,seed)
        if s.opt("..<") or s.opt("..="): s.addexpr(ns);e=("o",)
        return e
    def addexpr(s,ns,seed=None):
        e=s.mul(ns,seed)
        while s.isp("+") or s.isp("-"): s.i+=1;s.mul(ns,None);e=("o",)
        return e
    def mul(s,ns,seed):
        e=seed if seed is not None else s.cast(ns)
        while s.isp("*") or s.isp("/") or s.isp("%"): s.i+=1;s.cast(ns);e=("o",)
        return e
    def cast(s,ns):
        e=s.unary(ns)
        while s.opt("as"): s.type();e=("o",)
        return e
    def unary(s,ns):
        if s.opt("-") or s.opt("move"): s.unary(ns);return ("o",)
        return s.postfix(ns)
    def postfix(s,ns):
        e=s.primary(ns)
        while True:
            if s.opt("?"): e=("o",)
            elif s.isp("."):
                s.i+=1;s.ident();e=("pl",) if isplace(e) else ("o",)
            elif s.isp("("):
                s.i+=1;s.clist(s.arg,")");e=("o",)
                if s.isp("else") and s.isp("|",1):
                    s.i+=2;s.ident();s.eat("|");s.block()
            elif s.isp("["):
                s.bracket()
                if e[0]=="path" and not ns and s.isp("{"): s.structbody();e=("o",)
                else: e=("pl",) if isplace(e) else ("o",)
            else: return e
    def bracket(s):
        s.eat("[")
        def ba():
            if any(s.isp(x) for x in("iso","imm","secret","fn","dyn")): s.type()
            else: s.expr()
        s.clist(ba,"]")
    def structbody(s):
        s.eat("{")
        def fi(): s.ident();s.eat(":");s.expr()
        s.clist(fi,"}")
    def arg(s):
        if s.isid() and s.isp(":",1): s.i+=2
        nxt=lambda: s.isp(",",1) or s.isp(")",1)
        if s.isp("&"):
            if nxt(): s.i+=1;return
            s.i+=1
            if s.isid("out") and s.isid(o=1): s.i+=1
            s.place();return
        if (s.isp("-") or s.isp("|")) and nxt(): s.i+=1;return
        for b in ["+","*","/","%","^","<<",">>","and","or"]+CMP:
            if s.isp(b): s.i+=1;return
        s.expr()
    def primary(s,ns):
        a=s.k()
        if s.literal(): return ("o",)
        if a[0]=="id":
            s.path()
            if not ns and s.isp("{"): s.structbody();return ("o",)
            return ("path",)
        if s.opt("("): s.clist(s.expr,")");return ("o",)
        if s.opt("["):
            if not s.isp("]"):
                s.expr()
                if s.opt(";"): s.expr()
                else:
                    while s.opt(","):
                        if s.isp("]"): break
                        s.expr()
            s.eat("]");return ("o",)
        if s.opt("|"):
            def cp():
                if s.isp("let") or s.isp("inout") or s.isp("sink"): s.i+=1
                elif s.isid("set") and (s.isid(o=1) or s.isp("_",1)): s.i+=1
                if s.isid() or s.isp("_"): s.i+=1
                else: s.err("expected closure param")
                if s.opt(":"): s.type()
            s.clist(cp,"|")
            if s.isp("{"): s.block()
            else: s.expr(ns)
            return ("o",)
        if s.isp("if"): s.ifexpr();return ("o",)
        if s.isp("match"): s.matchexpr();return ("o",)
        if s.opt("comptime"): s.block();return ("o",)
        if s.opt("asm"): s.asmexpr();return ("o",)
        s.err("expected expression")
    def asmexpr(s):
        s.eat("(");s.ident();s.eat(")")
        s.eat("{")
        nstr=[0]
        def item():
            if s.k()[0] in("str","mstr"): s.i+=1;nstr[0]+=1;return
            if s.opt("in"):
                s.eat("(");s.ident();s.eat(")");s.eat("=");s.expr();return
            if s.isid("out"): s.i+=1;s.eat("(");s.ident();s.eat(")");return
            if s.isid("clobber"): s.i+=1;s.eat("(");s.clist(s.ident,")",1);return
            s.err("expected 'in', 'out', 'clobber', or a string")
        s.clist(item,"}",1)
        if nstr[0]<1: s.err("asm block requires at least one string instruction")
    def ifexpr(s):
        s.eat("if");s.expr(True);s.block()
        if s.opt("else"):
            if s.isp("if"): s.ifexpr()
            else: s.block()
    def matchexpr(s):
        s.eat("match");s.expr(True);s.eat("{")
        while not s.isp("}"):
            s.pattern();s.eat("=>")
            if s.isp("{"): s.block();s.opt(",")
            else:
                s.expr()
                if not s.opt(",") and not s.isp("}"): s.err("expected ',' after arm")
        s.eat("}")
    def pattern(s):
        a=s.k()
        if s.opt("let"): s.ident();return
        if s.opt("_") or s.opt("true") or s.opt("false"): return
        if a[0]=="str": s.i+=1;return
        if s.isp("-") and s.k(1)[0]=="num": s.i+=2;return
        if a[0]=="num": s.i+=1;return
        if s.isp(".") : s.i+=1;s.ident();s.payload();return
        if a[0]=="id": s.path();s.payload();return
        if s.opt("("): s.clist(s.pattern,")");return
        s.err("expected pattern")
    def payload(s):
        if s.opt("("): s.clist(s.pattern,")",1)
        elif s.opt("{"):
            def fp():
                if s.opt("let"): s.ident();return
                nm=s.ident()
                if s.opt(":"): s.pattern()
                else: s.err('write "let %s" to bind the field or "%s: pattern"'%(nm,nm))
            s.clist(fp,"}",1)
def isplace(e): return e[0] in("path","pl")
def check(src):
    try:
        p=P(lex(src));p.file();return None
    except E as e: return str(e)
if __name__=="__main__":
    root=sys.argv[1];bad=0
    for d,_,fs in sorted(os.walk(root)):
        for f in sorted(fs):
            if not f.endswith(".fors"): continue
            fp=os.path.join(d,f);src=open(fp).read()
            m=re.search(r"^//! expect: (\S+)",src,re.M)
            exp=m.group(1) if m else "(none)"
            r=check(src)
            rel=os.path.relpath(fp,root)
            if exp=="parse-error":
                print(("PE-OK  " if r else "PE-BAD ")+rel+" :: "+str(r))
                bad+= (r is None)
            elif r:
                print("BAD    %s [%s] :: %s"%(rel,exp,r));bad+=1
    print("bad:",bad)
