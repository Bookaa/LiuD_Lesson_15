# lesson 15

class Var:
    no = 0
    def __init__(self, name, typ):
        self.typ = typ
        self.name = name
        Var.no += 1
        self.no = Var.no
    def run(self, ctx):
        val = ctx.getvalue(self.no, self.name)
        if self.typ == type_unknown:
            return val
        if val.typ != self.typ:
            pass
        assert val.typ == self.typ
        return val

class SupportVar:
    def __init__(self, owner):
        self.vars = {}
        self.owner = owner
    def getvar(self, name):
        var = self.vars.get(name)
        if var:
            return var
        var = self.owner.getvar(name)
        assert var
        return var
    def addvar(self, name, typ):
        var = self.vars.get(name)
        if var is None:
            var = Var(name, typ)
            self.vars[name] = var
        else:
            assert var.typ == typ
        return var
class CodeBlock(SupportVar):
    def __init__(self, owner):
        SupportVar.__init__(self, owner)
        self.stmts = []
    def DefineOrAssign(self, name, val):
        var = self.addvar(name, val.typ)
        stmt = LiuL.newstmt_assign(var, val)
        self.stmts.append(stmt)
        return var
    def addstmt_SetDotMember(self, whos, name, val):
        stmt = LiuL.newstmt_setdotmember(whos, name, val)
        self.stmts.append(stmt)

    def FuncCall(self, fn, args):
        stmt = LiuL.newstmt_funccall(fn, args)
        self.stmts.append(stmt)

    def addstmt_Return(self, val):
        stmt = LiuL.newstmt_return(val)
        self.stmts.append(stmt)

    def run(self, ctx):
        ctx1 = RunContext(self.vars, ctx)
        for v in self.stmts:
            if isinstance(v, LiuL_stmt_return):
                return v.run(ctx1)
            v.run(ctx1)

class DefinedFunc(SupportVar):
    def __init__(self, funcname, args, owner):
        SupportVar.__init__(self, owner)
        self.name = funcname
        self.args = args
        self.block = CodeBlock(self)
        for name in args:
            self.addvar(name, type_unknown)
    def run(self, args, ctx0):
        ctx = RunContext(self.vars, ctx0)
        assert len(self.args) == len(args)
        for name, value in zip(self.args, args):
            var = self.vars.get(name)
            ctx.setvalue(var.no, name, value)
        result = self.block.run(ctx)
        return result

class Value:
    def __init__(self, typ, val):
        self.typ = typ
        self.val = val
    def run(self, ctx):
        return self

class Operate2:
    def __init__(self, op, val1, val2):
        typ1,typ2 = val1.typ, val2.typ
        if typ1 == typ2:
            self.typ = typ1
        elif type_unknown in (typ1, typ2):
            self.typ = type_unknown
        else:
            assert False
        self.op = op
        self.val1 = val1
        self.val2 = val2
    def run(self, ctx):
        v1 = self.val1.run(ctx)
        v2 = self.val2.run(ctx)
        if self.op == '+':
            v3 = v1.val + v2.val
            return Value(self.typ, v3)
        elif self.op == '*':
            v3 = v1.val * v2.val
            return Value(self.typ, v3)
        assert False

type_unknown = 'unknown'
type_int = 'int'

class OP_getdotmember:
    def __init__(self, whos, name):
        self.typ = type_unknown
        self.whos = whos
        self.name = name
    def run(self, ctx):
        vwho = self.whos.run(ctx)
        who = vwho.val
        if isinstance(who, DefinedInstance):
            ctx1 = who.ctx
            cls = who.cls
            var = cls.getvar(self.name)
            val = ctx1.getvalue(var.no, self.name)
            return val
        assert False

def GetValue(v, ctx):
    if isinstance(v, list):
        return [GetValue(v1, ctx) for v1 in v]
    if isinstance(v, str):
        v3 = v
    elif isinstance(v, Value):
        v3 = v
    else:
        assert False
    return v3

class OperateCall:
    def __init__(self, fn, args):
        self.fn = fn
        self.args = args
        self.typ = type_unknown
    def run(self, ctx):
        if isinstance(self.fn, DefinedFunc):
            valuelst = [v.run(ctx) for v in self.args]
            return self.fn.run(valuelst, ctx)
        if isinstance(self.fn, OperateCall):
            val_fn2 = self.fn.run(ctx)
            fn2 = val_fn2.val
            assert isinstance(fn2, DefinedFunc)
            valuelst = [v.run(ctx) for v in self.args]
            return fn2.run(valuelst, ctx)
        assert False

class Expr_CallLater:
    def __init__(self, fn, args):
        self.fn = fn
        self.args = args
        self.typ = type_unknown
    def run(self, ctx):
        lst = self.toval(self.args, ctx)
        result = self.fn(*lst)
        return Value(type_unknown, result)
    def toval(self, args, ctx):
        lst = []
        for v in args:
            if isinstance(v, Var):
                v3 = v.run(ctx)
                lst.append(v3.val)
                continue
            if isinstance(v, list):
                lst2 = self.toval(v, ctx)
                lst.append(lst2)
                continue
            lst.append(v)
        return lst

class LiuL_stmt_assign:
    def __init__(self, dest, src):
        self.dest = dest
        self.src = src
    def run(self, ctx):
        value = self.src.run(ctx)
        ctx.setvalue(self.dest.no, self.dest.name, value)

class LiuL_stmt_setdotmember:
    def __init__(self, whos, name, src):
        self.whos = whos
        self.name = name
        self.src = src
    def run(self, ctx):
        vsrc = self.src.run(ctx)
        vwhos = self.whos.run(ctx)
        who = vwhos.val
        if isinstance(who, DefinedInstance):
            ctx1 = who.ctx
            cls = who.cls
            var = cls.addvar(self.name, vsrc.typ)
            ctx1.noset.add(var.no)
            ctx1.setvalue(var.no, self.name, vsrc)
            return
        assert False

class LiuL_stmt_funccall:
    def __init__(self, fn, args):
        self.fn = fn
        self.args = args
    def run(self, ctx):
        argvalues = [v.run(ctx) for v in self.args]
        if isinstance(self.fn, GlobalFunc):
            return self.fn.run(argvalues)
        assert False

class LiuL_stmt_return:
    def __init__(self, val):
        self.val = val
    def run(self, ctx):
        value = self.val.run(ctx)
        return value

class GlobalFunc:
    def __init__(self, name):
        self.name = name
    def run(self, values):
        if self.name == 'print':
            lst = [v.val for v in values]
            print lst
            return
        assert False

class LiuL:
    def __init__(self):
        self.funcs = {}
        self.classes = {}
        self.global_funcs = {
            'print' : GlobalFunc('print')
        }
    def def_func(self, funcname, args):
        the = DefinedFunc(funcname, args, self)
        self.funcs[funcname] = the
        return the
    def def_class(self, name):
        the = DefinedClass(name, self)
        self.classes[name] = the
        return the
    def getvar(self, name):
        v = self.funcs.get(name)
        if v:
            return v
        v = self.classes.get(name)
        if v:
            return v
        return self.global_funcs.get(name)

    @staticmethod
    def ConstantInt(n):
        return Value(type_int, n)
    @staticmethod
    def op_Add(val1, val2):
        return Operate2('+', val1, val2)
    @staticmethod
    def op_Multi(val1, val2):
        return Operate2('*', val1, val2)
    @staticmethod
    def op_getdotmember(whos, name):
        return OP_getdotmember(whos, name)
    @staticmethod
    def op_FuncCall(fn, args):
        return OperateCall(fn, args)
    @staticmethod
    def op_CallLater(fn, args):
        return Expr_CallLater(fn, args)

    @staticmethod
    def newstmt_assign(dest, src):
        return LiuL_stmt_assign(dest, src)
    @staticmethod
    def newstmt_setdotmember(whos, name, src):
        return LiuL_stmt_setdotmember(whos, name, src)
    @staticmethod
    def newstmt_funccall(fn, args):
        return LiuL_stmt_funccall(fn, args)
    @staticmethod
    def newstmt_return(val):
        return LiuL_stmt_return(val)

class DefinedClass(LiuL, SupportVar):
    def __init__(self, name, owner):
        SupportVar.__init__(self, owner)
        LiuL.__init__(self)
        self.name = name
        self.addvar('self', 'classinstance')
    def newinstance(self, args, ctx0):
        ctx = RunContext(self.vars, ctx0)
        thein = DefinedInstance(ctx, self)
        selfv = Value('classinstance', thein)
        vself = self.vars.get('self')
        ctx.setvalue(vself.no, 'self', selfv)
        initfunc = self.funcs.get('__init__')
        if initfunc:
            initfunc.run([selfv] + args, ctx)
        return thein
    def def_init_func(self, args):
        return self.def_func('__init__', args)
    def getvar(self, name):
        var = SupportVar.getvar(self, name)
        if var:
            return var
        return LiuL.getvar(self, name)

class DefinedInstance:
    def __init__(self, ctx, cls):
        self.ctx = ctx
        self.cls = cls
    def getvar(self, name):
        fn = self.cls.funcs.get(name)
        if fn:
            return BundledFunc(self, fn)
        assert False

class BundledFunc:
    def __init__(self, theintance, fn):
        self.theinstance = theintance
        self.fn = fn
    def run(self, args, ctx_nouse):
        ctx = RunContext(self.fn.vars, self.theinstance.ctx)
        varself = self.theinstance.cls.getvar('self')
        valself = varself.run(self.theinstance.ctx)

        args = [valself] + args
        assert len(self.fn.args) == len(args)
        for name, value in zip(self.fn.args, args):
            var = self.fn.vars.get(name)
            ctx.setvalue(var.no, name, value)
        result = self.fn.block.run(ctx)
        return result

class RunContext:
    def __init__(self, vars, owner):
        self.owner = owner
        self.noset = set([])
        for a,b in vars.items():
            self.noset.add(b.no)
        self.values = {}
    def setvalue(self, no, name, val):
        assert isinstance(val, Value)
        if no in self.noset:
            self.values[no] = name, val
        elif self.owner:
            self.owner.setvalue(no, name, val)
        else:
            assert False
    def getvalue(self, no, name):
        v2 = self.values.get(no)
        if v2:
            name1, val = v2
            assert name1 == name
            return val
        if self.owner:
            return self.owner.getvalue(no, name)
        assert False

def call2_DefineOrAssign(block, name, val):
    return block.DefineOrAssign(name, val)

def call2_return(block, val):
    block.addstmt_Return(val)

def call2_funccall(block, fn, args):
    block.FuncCall(fn, args)

def call2_getvar(a, name):
    return a.getvar(name)

def call2_getdotmember(f, name):
    return getattr(f, name)

def call2_def_init_func(cls, args):
    return cls.def_init_func(args)

def call2_def_func(cls, name, args):
    return cls.def_func(name, args)

def call2_addstmt_SetDotMember(block, whos, name, val):
    block.addstmt_SetDotMember(whos, name, val)

# ----------------

def make_func1(liul):
    f = liul.def_func('func1', ['b1', 'b2'])

    a1 = LiuL.ConstantInt(3)
    i = f.block.DefineOrAssign('i', a1)

    a1 = LiuL.ConstantInt(2)
    a1 = LiuL.op_Add(i, a1)
    j = f.block.DefineOrAssign('j', a1)

    a1 = LiuL.ConstantInt(2)
    a1 = LiuL.op_Multi(j, a1)
    a1 = LiuL.op_Add(i, a1)

    b1 = f.block.getvar('b1')
    b2 = f.block.getvar('b2')
    a1 = LiuL.op_Add(a1, b1)
    a1 = LiuL.op_Add(a1, b2)

    fn = f.block.getvar('print')
    f.block.FuncCall(fn, [a1, b2])

    f.block.addstmt_Return(a1)

def make_func3(liul):
    f = liul.def_func('func3', [])

    f2 = liul.getvar('func2')
    genfn = LiuL.op_FuncCall(f2, [])

    a1 = LiuL.op_FuncCall(genfn, [LiuL.ConstantInt(8), LiuL.ConstantInt(9)])

    fn_print = f.block.getvar('print')
    f.block.FuncCall(fn_print, [a1])

    a2 = LiuL.op_FuncCall(genfn, [LiuL.ConstantInt(10), LiuL.ConstantInt(9)])

    f.block.addstmt_Return(a2)

def make_func2(liul):
    f = liul.def_func('func2', [])

    fn3 = LiuL.op_CallLater(liul.def_func, ['fn1',['b1','b2']])
    fn = f.block.DefineOrAssign('fn', fn3)

    tem1 = LiuL.op_CallLater(call2_getdotmember, [fn, 'block'])
    block = f.block.DefineOrAssign('block', tem1)

    val = LiuL.op_CallLater(call2_DefineOrAssign, [block, 'i', LiuL.ConstantInt(3)])
    i = f.block.DefineOrAssign('i', val)

    val = LiuL.op_CallLater(LiuL.op_Add, [i, LiuL.ConstantInt(2)])
    j = f.block.DefineOrAssign('j', val)

    val = LiuL.op_CallLater(LiuL.op_Multi, [j, LiuL.ConstantInt(2)])
    j2 = f.block.DefineOrAssign('j2', val)

    a1 = f.block.DefineOrAssign('a1', LiuL.op_CallLater(LiuL.op_Add, [i, j2]))

    b1 = f.block.DefineOrAssign('b1', LiuL.op_CallLater(call2_getvar, [block, 'b1']))
    b2 = f.block.DefineOrAssign('b2', LiuL.op_CallLater(call2_getvar, [block, 'b2']))

    a1 = f.block.DefineOrAssign('a1', LiuL.op_CallLater(LiuL.op_Add, [a1, b1]))
    a1 = f.block.DefineOrAssign('a1', LiuL.op_CallLater(LiuL.op_Add, [a1, b2]))

    val = LiuL.op_CallLater(call2_getvar, [block, 'print'])
    fprint = f.block.DefineOrAssign('fprint', val)

    val = LiuL.op_CallLater(call2_funccall, [block, fprint, [a1, b2]])
    f.block.DefineOrAssign('nouse2', val)

    fn_val = LiuL.op_CallLater(call2_return, [block, a1])
    f.block.DefineOrAssign('nouse', fn_val)

    f.block.addstmt_Return(fn)
    return f

def make_class1(liul):
    cls1 = liul.def_class('cls1')
    if True:
        f = cls1.def_init_func(['self', 'a1'])
        block = f.block
        a1 = block.getvar('a1')
        vself = block.getvar('self')
        block.addstmt_SetDotMember(vself, 'a', a1)
    if True:
        f = cls1.def_func('func5', ['self', 'a2'])
        block = f.block
        a2 = block.getvar('a2')
        vself = block.getvar('self')
        selfa = LiuL.op_getdotmember(vself, 'a')
        tem = LiuL.op_Add(selfa, a2)
        block.addstmt_Return(tem)

def make_func6(liul):
    f = liul.def_func('func6', [])
    f.block.addstmt_Return(LiuL.ConstantInt(23))
    return f

def make_func4(liul):
    f = liul.def_func('func4', [])

    cls1 = f.block.DefineOrAssign('cls1', LiuL.op_CallLater(liul.def_class, ['cls2']))

    if True:
        tem = LiuL.op_CallLater(call2_def_init_func, [cls1, ['self', 'a1']])
        f1 = f.block.DefineOrAssign('f1', tem)

        block = f.block.DefineOrAssign('block1', LiuL.op_CallLater(call2_getdotmember, [f1, 'block']))

        a1 = f.block.DefineOrAssign('a1', LiuL.op_CallLater(call2_getvar, [block, 'a1']))
        vself = f.block.DefineOrAssign('self', LiuL.op_CallLater(call2_getvar, [block, 'self']))

        tem = LiuL.op_CallLater(call2_addstmt_SetDotMember, [block, vself, 'a', a1])
        f.block.DefineOrAssign('nouse', tem)

    if True:
        tem = LiuL.op_CallLater(call2_def_func, [cls1, 'func5', ['self', 'a2']])
        f1 = f.block.DefineOrAssign('f1', tem)

        tem = LiuL.op_CallLater(call2_getdotmember, [f1, 'block'])
        block = f.block.DefineOrAssign('block2', tem)

        a2 = f.block.DefineOrAssign('a2', LiuL.op_CallLater(call2_getvar, [block, 'a2']))
        vself = f.block.DefineOrAssign('self', LiuL.op_CallLater(call2_getvar, [block, 'self']))

        selfa = f.block.DefineOrAssign('selfa', LiuL.op_CallLater(LiuL.op_getdotmember, [vself, 'a']))

        tem = f.block.DefineOrAssign('tem', LiuL.op_CallLater(LiuL.op_Add, [selfa, a2]))

        fn_val = LiuL.op_CallLater(call2_return, [block, tem])
        f.block.DefineOrAssign('nouse', fn_val)

    f.block.addstmt_Return(cls1)
    return f

'''
class cls1:
    def __init__(self, a1):
        self.a = a1
    def func5(self, a2):
        return self.a + a2

def func2():
    fn = dynamic create function fn just like func1
    return fn

def func3():
    fn3 = func2()
    print fn3(8,9)
    return fn3(10,9)

def func1(b1, b2):
    i = 3
    j = i + 2
    print i+j*2, b2
    return 55

def test():
    the = cls1(12)
    print the.func5(13)

    '''

import unittest
class Test(unittest.TestCase):
    def test2(self):
        liul = LiuL()
        make_func1(liul)

        ctx = RunContext({}, None)
        f = liul.getvar('func1')
        result = f.run([LiuL.ConstantInt(5), LiuL.ConstantInt(7)], ctx)
        self.assertEqual(result.val, 25)
    def test3(self):
        liul = LiuL()
        make_func2(liul)
        make_func3(liul)

        ctx = RunContext({}, None)
        f = liul.getvar('func3')
        result = f.run([], ctx)
        self.assertEqual(result.val, 32)
    def test4(self):
        liul = LiuL()
        make_class1(liul)

        ctx = RunContext({}, None)

        cls = liul.getvar('cls1')

        the = cls.newinstance([LiuL.ConstantInt(12)], ctx)
        func5 = the.getvar('func5')
        result = func5.run([LiuL.ConstantInt(13)], ctx)
        self.assertEqual(result.val, 25)
    def test5(self):
        liul = LiuL()
        make_func4(liul)

        ctx = RunContext({}, None)

        func4 = liul.getvar('func4')
        ret = func4.run([], ctx)
        cls2 = ret.val

        the = cls2.newinstance([LiuL.ConstantInt(12)], ctx)
        func5 = the.getvar('func5')
        result = func5.run([LiuL.ConstantInt(13)], ctx)
        self.assertEqual(result.val, 25)

    def test6(self):
        liul = LiuL()
        make_class1(liul)
        make_func6(liul)

        ctx = RunContext({}, None)

        func4 = liul.getvar('func6')
        ret = func4.run([], ctx)
        print ret.val

if __name__ == '__main__':
    the = Test(methodName='test5')
    the.test5()
    print 'good'