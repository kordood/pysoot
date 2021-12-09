# this file is executed exclusively in Jython

import sys
import os
import logging

l = logging.getLogger("pysoot.soot_manager")

self_dir = os.path.dirname(os.path.realpath(__file__))
self_dir = self_dir.replace("__pyclasspath__", "")  # needed because added by Jython

# soot-trunk.jar is a slightly modified version of soot.
# At some point I will upload the modifcations and the compilation script somewhere
sys.path.append(os.path.join(self_dir, "soot-trunk.jar"))
import java.util.Collections as Collections
import soot.Scene as Scene
import soot.Hierarchy as Hierarchy
import soot.G as G
import soot.options.Options as Options
import soot.PackManager as PackManager

# the import situation is pretty complicated
# from a pysoot prospective (running in Python, with a virtualenv with pysoot installed)
# SootClass is in pysoot.sootir.soot_class
# from Jython prospective, without countermeasures, SootClass is in sootir.soot_class
# (because Jython runs without virtualenv and from this folder, so it gets to sootir just following cwd).
# The problem is that when we pickle/unpickle there is a mismatch and Python cannot find sootir.soot_class.
# The solution is that I added a link in jython_bin/Lib to ../pysoot
# (basically simulating a virtualenv in Jython with pysoot installed).
# In this way, Jython can find SootClass by following jython_bin/Lib (which is by default in sys.path) and then
# from pysoot.sootir.soot_class import SootClass
from pysoot.sootir.soot_class import SootClass

import json
import sys
import subprocess
import soot.Modifier as Modifier
import soot.ArrayType as ArrayType
import soot.RefType as RefType
import soot.jimple.Jimple as Jimple
import soot.jimple.NullConstant as NullConstant
import soot.jimple.IntConstant as IntConstant
import soot.jimple.LongConstant as LongConstant
import soot.jimple.FloatConstant as FloatConstant
import soot.jimple.DoubleConstant as DoubleConstant
import soot.jimple.StringConstant as StringConstant
import soot.javaToJimple.LocalGenerator as LocalGenerator
import soot.SootClass as _SootClass


class SootManager(object):
    def __init__(self, config):
        G.reset()  # otherwise there are globals around even if a new instance of this class is created!
        # I think there cannot be more than one instance of SootManager around
        # otherwise the globals will conflict
        # it is not a big issue since there is going to be a SootManager instance per Jython process
        self._create_scene(config)

        self.apk_file = config["input_file"]
        self.sdk_path = config["android_sdk"]
        package_dir = os.path.dirname(__file__)
        self.jar_file =  os.path.join(package_dir, "DummyMain.jar")
        self.json_file = self.apk_file + ".dummy_main.json"
        self.method_json = None
        self.hash_table = dict()
        self.local_table = dict()
        self.run_jar()
        self.load_json()
        self.constants = {"null": NullConstant,
                          "int": IntConstant,
                          "long": LongConstant,
                          "float": FloatConstant,
                          "double": DoubleConstant,
                          "java.lang.String": StringConstant
                          }
        self.counter = 0
        self.tracker = []

    def _create_scene(self, config):
        Options.v().set_process_dir(Collections.singletonList(config["input_file"]))

        if config["input_format"] == "apk":
            Options.v().set_android_jars(config["android_sdk"])
            Options.v().set_process_multiple_dex(True)
            Options.v().set_src_prec(Options.src_prec_apk)
        elif config["input_format"] == "jar":
            Options.v().set_soot_classpath(config["soot_classpath"])
        else:
            raise Exception("invalid input type")

        if config["ir_format"] == "jimple":
            Options.v().set_output_format(Options.output_format_jimple)
        elif config["ir_format"] == "shimple":
            Options.v().set_output_format(Options.output_format_shimple)
        else:
            raise Exception("invalid ir format")

        Options.v().set_allow_phantom_refs(True)

        # this options may or may not work
        Options.v().setPhaseOption("cg", "all-reachable:true")
        Options.v().setPhaseOption("jb.dae", "enabled:false")
        Options.v().setPhaseOption("jb.uce", "enabled:false")
        Options.v().setPhaseOption("jj.dae", "enabled:false")
        Options.v().setPhaseOption("jj.uce", "enabled:false")

        # this avoids an exception in some apks
        Options.v().set_wrong_staticness(Options.wrong_staticness_ignore)

        Scene.v().loadNecessaryClasses()
        PackManager.v().runPacks()
        l.debug("Soot is done!")

        self.scene = Scene.v()
        self.raw_classes = self.scene.getClasses()
        self._init_class_hierarchy()
        l.debug("Soot init is done!")

    def _init_class_hierarchy(self):
        # all methods in Hierarchy.java that take as input one or more SootClass are exported
        # they are wrapped so that they take the name(s) of the classes (as strings)
        # and return a list of class names (as strings) or a boolean
        def make_function(method_name):
            def wrapper(*args):  # no kwargs in a Jython method
                converted_args = [self.raw_class_dict[a] for a in args]
                func = getattr(self.hierarchy, method_name)
                res = func(*converted_args)
                if type(res) == bool:
                    return res
                else:
                    return [c.name for c in res]

            return wrapper

        self.hierarchy = Hierarchy()
        self.raw_class_dict = {cc.name: cc for cc in self.raw_classes}
        exported_class_hierarchy_methods = [n for n in dir(self.hierarchy) if
                                            n not in ["getClass", "isVisible"] and
                                            (n.startswith("get") or n.startswith("is"))]
        for method_name in exported_class_hierarchy_methods:
            setattr(self, method_name, make_function(method_name))

    def get_classes(self):
        classes = {}
        l.debug("Start converting classes")
        for raw_class in self.raw_classes:
            l.debug("%s | class: %s" % (str(raw_class.isApplicationClass()), str(raw_class)))
            # TODO with this we only get classes for which we have all the code
            # soot also has classes with lower "resolving levels", but for those we may not have
            # the method list or the code, if we want them we cannot fully translate them
            if raw_class.isApplicationClass():
                l.debug("In progress!")
                soot_class = SootClass.from_ir(raw_class)
                l.debug("Done!")
                classes[soot_class.name] = soot_class
        return classes

    def run_jar(self):
        cmd = "java -jar %s %s %s" % (self.jar_file, self.apk_file, self.sdk_path)
        subprocess.call(cmd, shell=True)

    def load_json(self):
        self.method_json = json.load(open(self.json_file))

    def parse_json(self):
        if isinstance(self.method_json, dict):
            dummy_class = self.scene.makeSootClass("dummyMainClass")
            dummy_class.setResolvingLevel(_SootClass.BODIES)
            dummy_class.setModifiers(Modifier.PUBLIC)
            self.scene.addClass(dummy_class)
            dummy_class.setApplicationClass()
            self.raw_classes = self.scene.getClasses()
            _method_count = 0
            soot_methods = dict()

            for method_name, content in self.method_json.items():
                method = content['method']
                name = method['name']
                params = [self.scene.getType(param) for param in method['params']]
                ret = self.scene.getType(method['ret'])
                soot_method = self.scene.makeSootMethod(name, params, ret)
                soot_method.setModifiers(Modifier.PUBLIC + Modifier.STATIC)
                dummy_class.addMethod(soot_method)
                soot_methods[method_name] = soot_method

            _stmt_tracker = list()
            for method_name, content in self.method_json.items():
                self.local_table.clear()
                self.hash_table.clear()
                self.tracker = [self.method_json]

                soot_method = soot_methods[method_name]
                body = content['body']
                body_list = list()
                jimple_body = Jimple.v().newBody()
                jimple_body.setMethod(soot_method)
                local_generator = LocalGenerator(jimple_body)
                stmt_list = list()

                _counter = 0
                _testclass = self.scene.getSootClass("org.red.cute.window.SimpleWindow")
                self.tracker.append([str(method) for method in _testclass.getMethods()])

                self.tracker.append(method_name)

                for body_stmt in body:
                    stmt_type = body_stmt['type']
                    stmt = body_stmt['stmt']

                    _cond = _method_count > 10 and _counter == 5

                    if stmt_type == "assign":
                        new_stmt = self.parse_assign(stmt, local_generator, _cond)
                    elif stmt_type == "goto":
                        new_stmt = self.parse_goto(stmt)
                    elif stmt_type == "identity":
                        new_stmt = self.parse_identity(stmt, local_generator, soot_method)
                    elif stmt_type == "if":
                        new_stmt = self.parse_if(stmt)
                    elif stmt_type == "invoke":
                        new_stmt = self.parse_invoke(stmt)
                    elif stmt_type == "return":
                        new_stmt = self.parse_return(stmt)
                    elif stmt_type == "returnVoid":
                        new_stmt = self.parse_returnVoid(stmt, _method_count)
                    else:
                        # return [stmt_type]
                        continue

                    self.tracker.append("%s" % str(new_stmt))
                    self.tracker.append("%d" % self.counter)
                    _counter += 1

                    """
                    if _method_count > 19:
                        if _counter > self.counter:
                            self.counter = _counter
                            return self.tracker
                    """

                    if new_stmt is not None:
                        stmt_list.append(new_stmt)

                """
                unresolved_stmts = list()
                for index, new_stmt in enumerate(stmt_list):
                    if isinstance(new_stmt, list):
                        if len(new_stmt) > 2:
                            unresolved_stmts.append({index: new_stmt})
                """
                stmt_list = self.resolve_branch_stmts(stmt_list)
                for stmt in stmt_list:
                    _stmt_tracker.append("%s" % str(stmt))

                jimple_body.getUnits().addAll(stmt_list)
                soot_method.setActiveBody(jimple_body)

                _method_count += 1
                _stmt_tracker.append("==================")

            return _stmt_tracker

    def resolve_branch_stmts(self, stmt_list):
        for index, stmt in enumerate(stmt_list):
            if isinstance(stmt, list):
                stmt_info = stmt

                if len(stmt_info) == 3:
                    stmt_type = stmt_info[0]
                    if stmt_type == "if" or stmt_type == "goto":
                        stmt_hash = stmt_info[1]
                        new_stmt = self.hash_table.get(stmt_hash)

                        target_hash = stmt_info[2]
                        target = self.hash_table.get(target_hash)
                        new_stmt.setTarget(target)
                        stmt_list[index] = new_stmt
                        continue

                # Failed
                nop_stmt = Jimple.v().newNopStmt()
                stmt_list[index] = nop_stmt

        return stmt_list

    def parse_assign(self, stmt, local_generator, _cond):
        # Todo: how to know new stmt case by case
        """
        newAssignStmt(returnLocal, invokeExpr)
        newAssignStmt(local, newArrayExpr)
        newAssignStmt(tempLocal, NullConstant.v())
        newAssignStmt(applicationLocal,
					  Jimple.v().newStaticFieldRef(scApplicationHolder.getFieldByName("application").makeRef()))
        newAssignStmt(Jimple.v().newInstanceFieldRef(b.getThisLocal(), intentField.makeRef()), lcIntent)
        newAssignStmt(Jimple.v().newStaticFieldRef(fld.makeRef()), lc)
        final Local thisLocal = b.getThisLocal();
        final Local binderLocal = b.getParameterLocal(0);
        newAssignStmt(Jimple.v().newInstanceFieldRef(thisLocal, binderField.makeRef()), binderLocal))

        newAssignStmt(Local / FieldRef,
                      Expr / Constant / FieldRef / Local
                      )
        """

        left_op = stmt['leftOp']
        right_op = stmt['rightOp']
        self.tracker.append("parse assign")

        if left_op.get('name') is None:
            self.tracker.append("parse left op (name is None)")
            # field assign
            base = left_op.get('base')
            declaring_class = left_op['declaringClass']
            field_name = left_op['fieldName']
            field_type = left_op['fieldType']
            modifier = left_op['modifier']
            soot_class = self.scene.getSootClass(declaring_class)
            soot_field_type = self.scene.getType(field_type)

            self.tracker.append("%s: %s %s (%d)" % (str(soot_class), str(soot_field_type), str(field_name), modifier))
            if soot_class.declaresField(field_name, soot_field_type) == False:
                self.tracker.append("make soot field")
                field = self.scene.makeSootField(field_name, soot_field_type, modifier)
                soot_class.addField(field)
            else:
                self.tracker.append("get field")
                field = soot_class.getField(field_name, soot_field_type)
            """
            self.tracker.append([local for local in self.local_table.keys()])
            self.tracker.append([str(local)
                                 for local in self.local_table.values()])
            """
            base = self.local_table.get(base)
            if base is None:
                old_modifiers = field.getModifiers()
                modifiers = old_modifiers | Modifier.STATIC
                if old_modifiers != modifiers:
                    field.setModifiers(modifiers)
                field_ref = field.makeRef()
                assignee = Jimple.v().newStaticFieldRef(field_ref)
            else:
                old_modifiers = field.getModifiers()
                modifiers = old_modifiers & ~Modifier.STATIC
                if old_modifiers != modifiers:
                    field.setModifiers(modifiers)
                field_ref = field.makeRef()
                assignee = Jimple.v().newInstanceFieldRef(base, field_ref)
        else:
            self.tracker.append("parse left op (name exists)")
            name = left_op['name']
            if self.local_table.get(name) is None:
                self.tracker.append("make local")
                local_type = self.scene.getType(left_op['type'])
                # assignee = local_generator.generateLocal(local_type)
                assignee = Jimple.v().newLocal(name, local_type)
                self.local_table[name] = assignee
            else:
                self.tracker.append("load local")
                assignee = self.local_table[name]

        op_type = right_op['type']
        self.tracker.append("parse right op")
        if op_type == "local":
            self.tracker.append("assign from local")
            assigner = self.local_table[right_op['value']]
        elif op_type == "new":
            self.tracker.append("assign from new")
            assigner = Jimple.v().newNewExpr(RefType.v(self.scene.getSootClass(right_op['value'])))

            # fast return (prevent bug)
            new_stmt = Jimple.v().newAssignStmt(assignee, assigner)
            self.hash_table[stmt['hash']] = new_stmt
            return new_stmt
        elif op_type == "invoke":
            self.tracker.append("assign from invoke")
            expr_info = right_op['value']
            assigner = self.parse_invoke_expr(expr_info, _cond)
            if assigner is None:
                return None
        else:
            self.tracker.append("assign from constant")
            # Constant
            """
            IntConstant
            LongConstant
            DoubleConstant
            FloatConstant
            StringConstant
            NullConstant
            """
            if op_type == "null":
                self.tracker.append("const null")
                assigner = self.constants[op_type].v()
            else:
                if op_type == "int" or op_type == "long":
                    self.tracker.append("const int / long")
                    value = int(right_op['value'])
                elif op_type == "float" or op_type == "double":
                    self.tracker.append("const float / double")
                    value = float(right_op['value'])
                else:
                    self.tracker.append("const others")
                    value = right_op['value']
                assigner = self.constants[op_type].v(value)

        new_stmt = Jimple.v().newAssignStmt(assignee, assigner)
        self.hash_table[stmt['hash']] = new_stmt

        return new_stmt

    def parse_invoke(self, stmt):
        self.tracker.append("parse invoke")
        expr_info = stmt['expr']
        expr = self.parse_invoke_expr(expr_info)
        if expr is None:
            return None
        new_stmt = Jimple.v().newInvokeStmt(expr)
        self.hash_table[stmt['hash']] = new_stmt
        return new_stmt

    def parse_invoke_expr(self, expr_info, _cond=False):
        self.tracker.append("parse invoke expr")
        method_sig = expr_info['method']
        self.tracker.append("%s" % method_sig)

        method = self.scene.grabMethod(method_sig)

        if method is None:
            soot_class, method = self.grab_method(method_sig)
        else:
            soot_class = method.getDeclaringClass()

        self.tracker.append("%s : %s" % (str(soot_class), str(method)))

        args_info = expr_info['args']
        args = self.parse_args(args_info)

        invoke_type = expr_info['invokeType']
        self.tracker.append(str(invoke_type))
        invoke_expr_functions = {"JSpecialInvokeExpr": Jimple.v().newSpecialInvokeExpr,
                                 "JStaticInvokeExpr": Jimple.v().newStaticInvokeExpr,
                                 "JInterfaceInvokeExpr": Jimple.v().newInterfaceInvokeExpr,
                                 # "JDynamicInvokeExpr": Jimple.v().newDynamicInvokeExpr, # unsupported
                                 "JVirtualInvokeExpr": Jimple.v().newVirtualInvokeExpr
                                 }
        invoke_expr_func = invoke_expr_functions.get(invoke_type)
        if invoke_expr_func is None:
            return None

        self.tracker.append("invoke function is %s" % invoke_expr_func)

        if expr_info['base'] == "":
            self.tracker.append("get static method ref")
            method_ref = self.scene.makeMethodRef(soot_class, method.getName(),
                                                  method.getParameterTypes(), method.getReturnType(), True)

            if args is None or len(args) < 1:
                self.tracker.append("new static invoke no args")
                expr = invoke_expr_func(method_ref)
            else:
                self.tracker.append("new static invoke with args")
                expr = invoke_expr_func(method_ref, args)
        else:
            self.tracker.append("get instance method ref")
            method_ref = self.scene.makeMethodRef(soot_class, method.getName(),
                                                  method.getParameterTypes(), method.getReturnType(), False)
            base = self.local_table[expr_info['base']]

            if args is None or len(args) < 1:
                self.tracker.append("new instance invoke no args")
                expr = invoke_expr_func(base, method_ref)
            else:
                self.tracker.append("new instance invoke with args")
                expr = invoke_expr_func(base, method_ref, args)
        return expr

    def grab_method(self, method_sig):
        self.tracker.append("grab method")
        split_sig = method_sig.split(':')

        if len(split_sig) < 2:
            return None, None

        class_name = split_sig[0].lstrip('<')
        subsig = split_sig[1].strip().rstrip('>')

        self.tracker.append("%s & %s" % (class_name, subsig))
        soot_class = self.scene.getSootClassUnsafe(class_name)
        self.tracker.append("sc: %s" % str(soot_class))

        if soot_class is None:
            return None, None

        tmp_class = soot_class
        max_count = 50

        while True:
            if max_count < 0:
                break

            super_class = tmp_class.getSuperclass()
            self.tracker.append("sc: %s" % str(super_class))

            if super_class is None:
                break

            method = super_class.getMethodUnsafe(subsig)
            self.tracker.append("m: %s" % str(method))

            if method is None:
                tmp_class = super_class
            else:
                return soot_class, method

            max_count -= 1

        return None, None

    def parse_args(self, args_info):
        self.tracker.append("parse args")
        args = []
        for arg_info in args_info:
            for arg_type, arg_value in arg_info.items():
                """
                self.tracker.append("arg type %s" % arg_type)
                self.tracker.append("arg value %s" % arg_value)
                """
                if arg_type in self.constants:
                    self.tracker.append("other const arg")
                    if arg_type == "int" or arg_type == "long":
                        arg = self.constants[arg_type].v(int(arg_value))
                    elif arg_type == "float" or arg_type == "double":
                        arg = self.constants[arg_type].v(float(arg_value))
                    elif arg_type == "null":
                        arg = self.constants[arg_type].v()
                    else:
                        arg = self.constants[arg_type].v(arg_value)
                else:
                    self.tracker.append("force null const arg")
                    arg = self.constants["null"].v()
                args.append(arg)
        return args

    def parse_goto(self, stmt):
        """
        createIfStmt(endWhileStmt);
        """
        self.tracker.append("parse goto")
        label = self.hash_table.get(stmt['target'])

        if label is None:
            label = Jimple.v().newNopStmt()
            new_stmt = Jimple.v().newGotoStmt(label)
            return ["goto", stmt['hash'], stmt['target']]

        new_stmt = Jimple.v().newGotoStmt(label)
        self.hash_table[stmt['hash']] = new_stmt
        return new_stmt

    def parse_identity(self, stmt, local_generator, soot_method):
        """
        newIdentityStmt(thisLocal, Jimple.v().newThisRef(compSootClass.getType()))
        """
        self.tracker.append("parse identity")
        left_op = stmt['leftOp']
        right_op = stmt['rightOp']
        name = left_op['name']
        self.tracker.append("left op")
        self.tracker.append(name)
        if "$" in name:
            self.tracker.append("is local")
            local = self.local_table.get(name)
            if local is None:
                self.tracker.append("generate local")
                local_type = self.scene.getType(left_op['type'])
                # local = local_generator.generateLocal(local_type)
                local = Jimple.v().newLocal(name, local_type)
                self.local_table[name] = local
        else:
            self.tracker.append("is other")
            """
            l = jimple.newLocal("parameter" + i, t)
            """
            local_type = left_op['type']
            _type = self.scene.getSootClass(local_type).getType()
            local = Jimple.v().newLocal(name, _type)
            self.local_table[name] = local

        ref_type = right_op['refType']
        self.tracker.append("right op")
        if "@" in ref_type:
            self.tracker.append("is param")
            type_name, index = ref_type.split("@")
            param_type = self.scene.getType(type_name)
            # param_local = local_generator.generateLocal(param_type)
            param_local = Jimple.v().newLocal("parameter" + type_name, param_type)
            ref = Jimple.v().newParameterRef(param_type, int(index))
        else:
            self.tracker.append("is other")
            """
            newThisRef(sootMethod.getDeclaringClass().getType())
            """
            _type = self.scene.getSootClass(ref_type).getType()
            ref = Jimple.v().newThisRef()

        new_stmt = Jimple.v().newIdentityStmt(local, ref)
        self.hash_table[stmt['hash']] = new_stmt
        return new_stmt

    def parse_if(self, stmt):
        """
        newEqExpr(intCounter, IntConstant.v(conditionCounter++))
        newIfStmt(cond, target)
        """
        condition = stmt['condition']
        op1 = condition['op1']
        op2 = condition['op2']
        self.tracker.append("parse if")
        if "$" in op1 or "@" in op1:
            self.tracker.append("op1 is local or param")
            op1 = self.local_table[op1]

        if "$" in str(op2) or "@" in str(op2):
            self.tracker.append("op2 is local or param")
            op2 = self.local_table[op2]
        else:
            self.tracker.append("op2 is int constant")
            op2 = IntConstant.v(op2)

        expr = Jimple.v().newEqExpr(op1, op2)
        target = self.hash_table.get(stmt['target'])

        if target is None:
            self.tracker.append("target will solve later")
            label = Jimple.v().newNopStmt()
            new_stmt = Jimple.v().newIfStmt(expr, label)
            self.hash_table[stmt['hash']] = new_stmt
            return ["if", stmt['hash'], stmt['target']]

        new_stmt = Jimple.v().newIfStmt(expr, target)
        self.hash_table[stmt['hash']] = new_stmt
        return new_stmt

    def parse_return(self, stmt):
        """
        newReturnStmt(thisLocal)
        newReturnStmt(NullConstant.v())
        """
        self.tracker.append("parse return")
        local = self.local_table[stmt['value']]
        new_stmt = Jimple.v().newReturnStmt(local)
        self.hash_table[stmt['hash']] = new_stmt
        return new_stmt

    def parse_returnVoid(self, stmt, _method_count):
        """
        newReturnVoidStmt()
        """
        self.tracker.append("parse return void")
        new_stmt = Jimple.v().newReturnVoidStmt()
        self.hash_table[stmt['hash']] = new_stmt
        return new_stmt


if __name__ == "__main__":
    import sys

    config = dict()
    config['input_file'] = sys.argv[3]
    config['android_sdk'] = sys.argv[2]
    config['input_format'] = sys.argv[1]
    config["ir_format"] = "shimple"

    si = SootManager(config)
