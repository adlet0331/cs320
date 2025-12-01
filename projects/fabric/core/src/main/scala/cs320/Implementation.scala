package cs320

object Implementation extends Template {

  def typeCheck(e: Typed.Expr): Typed.Type = T.typeCheck(e)

  def interp(e: Untyped.Expr): Untyped.Value = U.interp(e)._1

  object T {
    import Typed._

    // Type entry can be simple or polymorphic
    sealed trait TypeEntry
    case class SimpleEntry(typ: Type, isMutable: Boolean) extends TypeEntry
    case class PolyEntry(tparams: List[String], paramTypes: List[Type], rtype: Type) extends TypeEntry
    
    // Type environment: variable name -> TypeEntry
    type TypeEnv = Map[String, TypeEntry]
    // Type definition environment: type name -> (type params, List of (variant name, param types))
    type TypeDefEnv = Map[String, (List[String], List[(String, List[Type])])]
    // Variant constructor environment: variant name -> (type name, type params, param types)
    type VarEnv = Map[String, (String, List[String], List[Type])]
    
    // Combined environment
    case class Env(
      tenv: TypeEnv,          // variable types
      tdefEnv: TypeDefEnv,    // type definitions
      varEnv: VarEnv,         // variant constructors
      tparams: Set[String]    // type parameters in scope
    )

    def checkIntOp(left: Expr, right: Expr, env: Env, resType: Type): Type = {
      val lt = typeCheck(left, env)
      val rt = typeCheck(right, env)
      (lt, rt) match {
        case (IntT, IntT) => resType
        case _ => error("type error in integer operation")
      }
    }
    
    // Check if a type is well-formed (no free type variables)
    def checkType(typ: Type, env: Env): Unit = typ match {
      case IntT | BooleanT | UnitT => ()
      case VarT(name) =>
        if (!env.tparams.contains(name)) error(s"free type variable: $name")
      case ArrowT(ptypes, rtype) =>
        ptypes.foreach(checkType(_, env))
        checkType(rtype, env)
      case AppT(name, targs) =>
        if (!env.tdefEnv.contains(name)) error(s"unknown type: $name")
        val (tps, _) = env.tdefEnv(name)
        if (targs.length != tps.length) error(s"wrong number of type arguments for $name")
        targs.foreach(checkType(_, env))
    }
    
    // Substitute type variables with actual types
    def substituteType(typ: Type, subst: Map[String, Type]): Type = typ match {
      case IntT | BooleanT | UnitT => typ
      case VarT(name) => subst.getOrElse(name, typ)
      case ArrowT(ptypes, rtype) =>
        ArrowT(ptypes.map(substituteType(_, subst)), substituteType(rtype, subst))
      case AppT(name, targs) =>
        AppT(name, targs.map(substituteType(_, subst)))
    }

    def typeCheck(expr: Expr): Type = {
      val initialEnv = Env(Map(), Map(), Map(), Set())
      typeCheck(expr, initialEnv)
    }
    
    def typeCheck(expr: Expr, env: Env): Type = expr match {
      case Id(name, targs) =>
        // Check in variant constructors first
        env.varEnv.get(name) match {
          case Some((typeName, tps, paramTypes)) =>
            // It's a variant constructor
            if (targs.isEmpty && tps.nonEmpty) error(s"type arguments required for $name")
            if (targs.length != tps.length) error(s"wrong number of type arguments for $name")
            targs.foreach(checkType(_, env))
            val subst = (tps zip targs).toMap
            val substParamTypes = paramTypes.map(substituteType(_, subst))
            val resultType = AppT(typeName, targs)
            if (paramTypes.isEmpty) resultType
            else ArrowT(substParamTypes, resultType)
          case None =>
            // Check in variable environment
            env.tenv.get(name) match {
              case Some(SimpleEntry(typ, _)) =>
                if (targs.nonEmpty) error(s"non-polymorphic $name cannot take type arguments")
                typ
              case Some(PolyEntry(tps, paramTypes, rtype)) =>
                // Polymorphic function
                if (targs.isEmpty) error(s"type arguments required for polymorphic function $name")
                if (targs.length != tps.length) error(s"wrong number of type arguments for $name")
                targs.foreach(checkType(_, env))
                val subst = (tps zip targs).toMap
                val substParamTypes = paramTypes.map(substituteType(_, subst))
                val substRtype = substituteType(rtype, subst)
                ArrowT(substParamTypes, substRtype)
              case None => error(s"free identifier: $name")
            }
        }
        
      case IntE(_) => IntT
      case BooleanE(_) => BooleanT
      case UnitE => UnitT
      
      case Add(left, right) => checkIntOp(left, right, env, IntT)
      case Mul(left, right) => checkIntOp(left, right, env, IntT)
      case Div(left, right) => checkIntOp(left, right, env, IntT)
      case Mod(left, right) => checkIntOp(left, right, env, IntT)
      case Eq(left, right) => checkIntOp(left, right, env, BooleanT)
      case Lt(left, right) => checkIntOp(left, right, env, BooleanT)
      
      case Sequence(left, right) =>
        typeCheck(left, env)
        typeCheck(right, env)
        
      case If(cond, texpr, fexpr) =>
        val ct = typeCheck(cond, env)
        val tt = typeCheck(texpr, env)
        val ft = typeCheck(fexpr, env)
        ct match {
          case BooleanT =>
            if (tt == ft) tt
            else error("branches of if have different types")
          case _ => error("condition of if is not a boolean")
        }
        
      case Val(mut, name, typOpt, expr, body) =>
        val exprType = typeCheck(expr, env)
        typOpt match {
          case Some(annotatedType) =>
            checkType(annotatedType, env)
            if (exprType != annotatedType) error("type annotation mismatch")
          case None => ()
        }
        val newEnv = env.copy(tenv = env.tenv + (name -> SimpleEntry(exprType, mut)))
        typeCheck(body, newEnv)
        
      case Fun(params, body) =>
        params.foreach { case (_, typ) => checkType(typ, env) }
        val paramEnv = params.foldLeft(env.tenv) {
          case (acc, (name, typ)) => acc + (name -> SimpleEntry(typ, false))
        }
        val bodyType = typeCheck(body, env.copy(tenv = paramEnv))
        ArrowT(params.map(_._2), bodyType)
        
      case Assign(name, expr) =>
        env.tenv.get(name) match {
          case Some(SimpleEntry(typ, true)) =>
            val exprType = typeCheck(expr, env)
            if (exprType != typ) error("assignment type mismatch")
            UnitT
          case Some(SimpleEntry(_, false)) => error("cannot assign to immutable variable")
          case Some(PolyEntry(_, _, _)) => error("cannot assign to function")
          case None => error(s"free identifier: $name")
        }
        
      case App(fun, args) =>
        val funType = typeCheck(fun, env)
        funType match {
          case ArrowT(paramTypes, rtype) =>
            if (args.length != paramTypes.length) error("wrong number of arguments")
            val argTypes = args.map(typeCheck(_, env))
            if (argTypes != paramTypes) error("argument type mismatch")
            rtype
          case _ => error("not a function")
        }
        
      case RecBinds(defs, body) =>
        // First pass: collect all type definitions and check for conflicts
        val typeDefsToAdd = defs.collect { case td: TypeDef => td }
        
        // Check for duplicate type names
        val typeNames = typeDefsToAdd.map(_.name)
        typeNames.foreach { tn =>
          if (env.tdefEnv.contains(tn)) error(s"duplicate type definition: $tn")
        }
        
        // Check for type parameter conflicts with outer scope
        typeDefsToAdd.foreach { td =>
          td.tparams.foreach { tp =>
            if (env.tparams.contains(tp)) error(s"type parameter shadows outer: $tp")
          }
        }
        
        // Build new type definition environment
        val newTdefEnv = typeDefsToAdd.foldLeft(env.tdefEnv) { (acc, td) =>
          acc + (td.name -> (td.tparams, td.variants.map(v => (v.name, v.params))))
        }
        
        // Build variant constructor environment
        val newVarEnv = typeDefsToAdd.foldLeft(env.varEnv) { (acc, td) =>
          td.variants.foldLeft(acc) { (acc2, v) =>
            acc2 + (v.name -> (td.name, td.tparams, v.params))
          }
        }
        
        // Now collect all recursive definitions (lazy, fun, typedefs)
        // Build their types before checking bodies
        val envWithTypes = env.copy(tdefEnv = newTdefEnv, varEnv = newVarEnv)
        
        // Check all variant param types are valid
        typeDefsToAdd.foreach { td =>
          val tparamsSet = td.tparams.toSet
          val checkEnv = envWithTypes.copy(tparams = env.tparams ++ tparamsSet)
          td.variants.foreach { v =>
            v.params.foreach { pt =>
              checkType(pt, checkEnv)
            }
          }
        }
        
        // Collect lazy and rec fun definitions for first pass
        val lazyDefs = defs.collect { case l: Lazy => l }
        val recFunDefs = defs.collect { case rf: RecFun => rf }
        
        // Check lazy types and recfun param/return types
        lazyDefs.foreach { l => checkType(l.typ, envWithTypes) }
        recFunDefs.foreach { rf =>
          rf.tparams.foreach { tp =>
            if (env.tparams.contains(tp)) error(s"type parameter shadows outer: $tp")
          }
          val checkEnv = envWithTypes.copy(tparams = env.tparams ++ rf.tparams.toSet)
          rf.params.foreach { case (_, pt) => checkType(pt, checkEnv) }
          checkType(rf.rtype, checkEnv)
        }
        
        // Build tenv with all definitions
        val newTenv = lazyDefs.foldLeft(envWithTypes.tenv) { (acc, l) =>
          acc + (l.name -> SimpleEntry(l.typ, false))
        }
        val newTenv2 = recFunDefs.foldLeft(newTenv) { (acc, rf) =>
          if (rf.tparams.isEmpty) {
            // Non-polymorphic function
            acc + (rf.name -> SimpleEntry(ArrowT(rf.params.map(_._2), rf.rtype), false))
          } else {
            // Polymorphic function
            acc + (rf.name -> PolyEntry(rf.tparams, rf.params.map(_._2), rf.rtype))
          }
        }
        
        val fullEnv = envWithTypes.copy(tenv = newTenv2)
        
        // Second pass: check bodies
        lazyDefs.foreach { l =>
          val bodyType = typeCheck(l.expr, fullEnv)
          if (bodyType != l.typ) error(s"lazy ${l.name} body type mismatch")
        }
        
        recFunDefs.foreach { rf =>
          val bodyEnv = fullEnv.copy(
            tparams = env.tparams ++ rf.tparams.toSet,
            tenv = fullEnv.tenv ++ rf.params.map { case (n, t) => n -> SimpleEntry(t, false) }
          )
          val bodyType = typeCheck(rf.body, bodyEnv)
          if (bodyType != rf.rtype) error(s"recfun ${rf.name} body type mismatch")
        }
        
        // Now check the body expression
        typeCheck(body, fullEnv)
        
      case Match(expr, cases) =>
        val exprType = typeCheck(expr, env)
        exprType match {
          case AppT(typeName, targs) =>
            env.tdefEnv.get(typeName) match {
              case Some((tparams, variants)) =>
                // Check all variants are covered exactly once
                val variantNames = variants.map(_._1).toSet
                val caseNames = cases.map(_.variant).toSet
                if (variantNames != caseNames) error("pattern matching not exhaustive or has duplicates")
                
                val subst = (tparams zip targs).toMap
                
                // Type check each case body
                val caseTypes = cases.map { c =>
                  val variantInfo = variants.find(_._1 == c.variant).get
                  val paramTypes = variantInfo._2.map(substituteType(_, subst))
                  if (c.names.length != paramTypes.length) error("wrong number of pattern variables")
                  val caseEnv = c.names.zip(paramTypes).foldLeft(env.tenv) {
                    case (acc, (name, typ)) => acc + (name -> SimpleEntry(typ, false))
                  }
                  typeCheck(c.body, env.copy(tenv = caseEnv))
                }
                
                // All case bodies must have the same type
                if (caseTypes.distinct.length != 1) error("case bodies have different types")
                caseTypes.head
                
              case None => error(s"unknown type: $typeName")
            }
          case _ => error("cannot match on non-algebraic type")
        }
    }
  }

  object U {
    import Untyped._
    type Sto = Map[Addr, Value]
    def malloc(sto: Sto): Addr = sto.foldLeft(0){
      case (max, (addr, _)) => Math.max(max, addr)
    } + 1

    def numVstoOp(left:Expr, right:Expr, sto:Sto, op: (BigInt, BigInt) => BigInt, env:Env): (Value, Sto) = {
      val (lv, ls) = interp(left, env, sto)
      val (rv, rs) = interp(right, env, ls)
      (numVop(op)(lv, rv), rs)
    }

    def numVstoBop(left:Expr, right:Expr, sto:Sto, op: (BigInt, BigInt) => Boolean, env:Env): (Value, Sto) = {
      val (lv, ls) = interp(left, env, sto)
      val (rv, rs) = interp(right, env, ls)
      (numVbop(op)(lv, rv), rs)
    }

    def numVop(op: (BigInt, BigInt) => BigInt): (Value, Value) => IntV = (_, _) match {
      case (IntV(x), IntV(y)) => IntV(op(x, y))
      case (x, y) => error(s"not both numbers")
    }

    def numVbop(op: (BigInt, BigInt) => Boolean): (Value, Value) => BooleanV = (_, _) match {
      case (IntV(x), IntV(y)) => BooleanV(op(x, y))
      case (x, y) => error(s"not both numbers")
    }

    val intAdd = numVop(_ + _)
    val intMul = numVop(_ * _)
    val intDiv = numVop { (x, y) =>
      if (y == 0) error("division by zero")
      else x / y
    }
    val intMod = numVop { (x, y) =>
      if (y == 0) error("modulo by zero")
      else x % y
    }

    def interp(expr: Expr): (Value, Sto) = interp(expr, Map(), Map())

    def interp(expr: Expr, env: Env, sto: Sto): (Value, Sto) = expr match {
      // Value cases
      case Id(name) => env.get(name) match {
        case Some(addr) => sto(addr) match{
          case ExprV(e, eenv) =>{
            val (ev, newSto) = interp(e, eenv, sto)
            (ev, newSto + (addr -> ev))
          }
          case v @ (IntV(_) | BooleanV(_) | UnitV | CloV(_, _, _) | ConstructorV(_) | VariantV(_, _)) => (v, sto)
        }
        case None => error("unbound variable")
      }
      case IntE(value) => (IntV(value), sto)
      case BooleanE(value) => (BooleanV(value), sto)
      case UnitE => (UnitV, sto)
      case Fun(params, body) => (CloV(params, body, env), sto)

      // Operations
      case Add(left, right) => numVstoOp(left, right, sto, _ + _, env)
      case Mul(left, right) => numVstoOp(left, right, sto, _ * _, env)
      case Div(left, right) => numVstoOp(left, right, sto, (x, y) => {
        if (y == 0) error("division by zero")
        else x / y
      }, env)
      case Mod(left, right) => numVstoOp(left, right, sto, (x, y) => {
        if (y == 0) error("modulo by zero")
        else x % y
      }, env)
      case Eq(left, right) => numVstoBop(left, right, sto, _ == _, env)
      case Lt(left, right) => numVstoBop(left, right, sto, _ < _, env)
      case Sequence(left, right) => {
        val (lv, ls) = interp(left, env, sto)
        interp(right, env, ls)
      }
      case If(cond, texpr, fexpr) => {
        val (cv, cs) = interp(cond, env, sto)
        cv match {
          case BooleanV(true) => interp(texpr, env, cs)
          case BooleanV(false) => interp(fexpr, env, cs)
          case _ => error("condition not a boolean")
        }
      }
      case Val(name, expr, body) => {
        val (ev, es) = interp(expr, env, sto)
        val addr = malloc(es)
        interp(body, env + (name -> addr), es + (addr -> ev))
      }
      case RecBinds(defs, body) => {
        // Allocate addresses for all definitions using fold to thread the store
        val (newEnv, _) = defs.foldLeft((env, sto)) {
          case ((accEnv, accSto), Lazy(name, _)) =>
            val addr = malloc(accSto)
            (accEnv + (name -> addr), accSto + (addr -> UnitV))
          case ((accEnv, accSto), RecFun(name, _, _)) =>
            val addr = malloc(accSto)
            (accEnv + (name -> addr), accSto + (addr -> UnitV))
          case ((accEnv, accSto), TypeDef(variants)) =>
            variants.foldLeft((accEnv, accSto)) { case ((e, s), Variant(vname, _)) =>
              val addr = malloc(s)
              (e + (vname -> addr), s + (addr -> UnitV))
            }
        }

        val newSto = defs.foldLeft(sto) {
          case (s, Lazy(name, expr)) =>
            val addr = newEnv(name)
            s + (addr -> ExprV(expr, newEnv))
          case (s, RecFun(name, params, expr)) =>
            val addr = newEnv(name)
            s + (addr -> CloV(params, expr, newEnv))
          case (s, TypeDef(variants)) =>
            variants.foldLeft(s) { case (s2, Variant(vname, isNullary)) =>
              val addr = newEnv(vname)
              // For nullary constructors (isNullary=true), store VariantV directly
              // For constructors with params (isNullary=false), store ConstructorV
              if (isNullary) s2 + (addr -> VariantV(vname, List()))
              else s2 + (addr -> ConstructorV(vname))
            }
        }
        interp(body, newEnv, newSto)
      }
      case Assign(name, expr) => {
        env.get(name) match {
          case Some(addr) => {
            val (ev, es) = interp(expr, env, sto)
            (UnitV, es + (addr -> ev))
          }
          case None => error("unbound variable")
        }
      }
      case App(fun, args) => {
        val (fv, fs) = interp(fun, env, sto)
        fv match {
          case CloV(params, body, fenv) => {
            if (params.length != args.length) error("argument length mismatch")
            val (argVals, as) = args.foldLeft((List[Value](), fs)){
              case ((vals, s), arg) => {
                val (av, ns) = interp(arg, env, s)
                (vals :+ av, ns)
              }
            }
            // Allocate addresses for all parameters
            val (newEnv, newSto) = (params zip argVals).foldLeft((fenv, as)) {
              case ((accEnv, accSto), (name, value)) =>
                val addr = malloc(accSto)
                (accEnv + (name -> addr), accSto + (addr -> value))
            }
            interp(body, newEnv, newSto)
          }
          case ConstructorV(name) => {
            // Constructor application - creates a VariantV
            val (argVals, as) = args.foldLeft((List[Value](), fs)){
              case ((vals, s), arg) => {
                val (av, ns) = interp(arg, env, s)
                (vals :+ av, ns)
              }
            }
            (VariantV(name, argVals), as)
          }
          case _ => error("not a function")
        }
      }
      case Match(expr, cases) => {
        val (ev, es) = interp(expr, env, sto)
        ev match {
          case VariantV(vname, values) => {
            val matchingCase = cases.find{
              case Case(cname, _, _) => cname == vname
            } match {
              case Some(cse) => cse
              case None => error("no matching case")
            }
            val Case(_, names, body) = matchingCase
            if (names.length != values.length) error("pattern length mismatch")
            val (newEnv, newSto) = (names zip values).foldLeft((env, es)) {
              case ((accEnv, accSto), (name, value)) =>
                val addr = malloc(accSto)
                (accEnv + (name -> addr), accSto + (addr -> value))
            }
            interp(body, newEnv, newSto)
          }
          case _ => error("not a variant value")
        }
      }
    }
  }
}